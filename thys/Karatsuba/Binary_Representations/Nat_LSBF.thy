theory Nat_LSBF
  imports Main "../Preliminaries/Karatsuba_Sum_Lemmas" Abstract_Representations "HOL-Library.Log_Nat"
begin

section "Representing @{type nat} in LSBF"

text "In this theory, a representation of @{type nat} is chosen and simple algorithms implemented
thereon."

lemma list_isolate_nth: "i < length xs \<Longrightarrow> \<exists>xs1 xs2. xs = xs1 @ (xs ! i) # xs2 \<and> length xs1 = i"
  using id_take_nth_drop by fastforce

lemma list_is_replicate_iff: "xs = replicate (length xs) x \<longleftrightarrow> (\<forall>i \<in> {0..<length xs}. xs ! i = x)"
proof
  assume 1: "xs = replicate (length xs) x"
  show "\<forall>i \<in> {0..<length xs}. xs ! i = x"
    using 1 nth_replicate[of _ "length xs" x] by auto
next
  assume "\<forall>i \<in> {0..<length xs}. xs ! i = x"
  then have "\<forall>i \<in> {0..<length xs}. xs ! i = (replicate (length xs) x) ! i"
    using nth_replicate by auto
  then show "xs = replicate (length xs) x"
    using nth_equalityI[of xs "replicate (length xs) x"] by simp
qed

lemma list_is_replicate_iff2: "xs = replicate (length xs) x \<longleftrightarrow> set xs = {x} \<or> xs = []"
  by (metis empty_replicate length_0_conv replicate_eqI set_replicate singleton_iff)

lemma set_bool_list: "set xs \<subseteq> {True, False}"
  by auto
lemma bool_list_is_replicate_if:
  assumes "a \<notin> set xs" shows "xs = replicate (length xs) (\<not> a)"
proof (intro iffD2[OF list_is_replicate_iff2])
  from assms set_bool_list have "set xs \<subseteq> {\<not> a}" by fastforce
  then have "set xs = {\<not> a} \<or> set xs = {}" by (meson subset_singletonD)
  then show "set xs = {\<not> a} \<or> xs = []" by simp
qed

lemma bit_strong_decomp_2: "\<exists>ys zs. xs = ys @ a # zs \<Longrightarrow> \<exists>ys' n. xs = ys' @ a # (replicate n (\<not> a))"
proof -
  assume "\<exists>ys zs. xs = ys @ a # zs"
  then have "a \<in> set xs" by auto
  from split_list_last[OF this] obtain ys zs where "xs = ys @ a # zs" "a \<notin> set zs" by blast
  from this(2) have "zs = replicate (length zs) (\<not>a)"
    by (intro bool_list_is_replicate_if)
  with \<open>xs = ys @ a # zs\<close> show ?thesis by blast
qed

lemma bit_strong_decomp_1: "\<exists>ys zs. xs = ys @ a # zs \<Longrightarrow> \<exists>ys' n. xs = (replicate n (\<not> a) @ a # ys')"
proof -
  assume "\<exists>ys zs. xs = ys @ a # zs"
  then obtain ys zs where "xs = ys @ a # zs" by blast
  then have "rev xs = rev zs @ [a] @ rev ys" by simp
  then obtain n ys' where "rev xs = ys' @ [a] @ replicate n (\<not> a)"
    using bit_strong_decomp_2[of "rev xs" a] by auto
  then have "xs = replicate n (\<not> a) @ [a] @ rev ys'"
    by (metis append_assoc rev_append rev_replicate rev_rev_ident rev_singleton_conv)
  thus ?thesis by auto
qed

subsection "Type definition"

type_synonym nat_lsbf = "bool list"

subsection "Conversions"

fun eval_bool :: "bool \<Rightarrow> nat" where
"eval_bool True = 1"
| "eval_bool False = 0"

lemma eval_bool_is_of_bool[simp]: "eval_bool = of_bool"
  by auto

lemma eval_bool_leq_1: "eval_bool a \<le> 1"
  by (cases a) simp_all

lemma eval_bool_inj: "eval_bool a = eval_bool b \<Longrightarrow> a = b"
  by (cases a; cases b) simp_all

fun to_nat :: "nat_lsbf \<Rightarrow> nat" where
"to_nat [] = 0"
| "to_nat (x#xs) = (eval_bool x) + 2 * to_nat xs"

fun from_nat :: "nat \<Rightarrow> nat_lsbf" where
"from_nat 0 = []"
| "from_nat x = (if x mod 2 = 0 then False else True)#(from_nat (x div 2))"

value "from_nat 103"
value "to_nat (from_nat 103)"

lemma to_nat_from_nat[simp]: "to_nat (from_nat x) = x"
proof (induction x rule: less_induct)
  case (less x)
  consider "x = 0" | "x > 0" by auto
  then show ?case
  proof (cases)
    case 1
    then show ?thesis by simp
  next
    case 2
    then have "to_nat (from_nat x) = eval_bool (if x mod 2 = 0 then False else True) + 2 * to_nat (from_nat (x div 2))"
      by (metis from_nat.elims nat_less_le to_nat.simps(2))
    also have "... = (x mod 2) + 2 * to_nat (from_nat (x div 2))"
      by simp
    also have "... = (x mod 2) + 2 * (x div 2)"
      using less 2 by simp
    also have "... = x" by simp
    finally show ?thesis .
  qed
qed

lemma to_nat_explicitly: "to_nat xs = (\<Sum>i \<leftarrow> [0..<length xs]. eval_bool (xs ! i) * 2 ^ i)"
proof (induction xs rule: to_nat.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs)
  let ?xs = "\<lambda>i. eval_bool ((x # xs) ! i)"
  have "(\<Sum>i\<leftarrow>[0..<length (x # xs)]. ?xs i * 2 ^ i)
    = ?xs 0 + (\<Sum>i\<leftarrow>[1..<length (x # xs)]. ?xs i * 2 ^ i)"
    by (simp add: upt_rec)
  also have "... = ?xs 0 + (\<Sum>i\<leftarrow>[0..<length xs]. ?xs (i + 1) * 2 ^ (i + 1))"
    using list_sum_index_shift[of _ "length xs" 0 "\<lambda>i. ?xs i * 2 ^ i"] by simp
  also have "... = ?xs 0 + 2 * (\<Sum>i\<leftarrow>[0..<length xs]. ?xs (i + 1) * 2 ^ i)"
    by (simp add: sum_list_const_mult mult.left_commute)
  also have "... = ?xs 0 + 2 * to_nat xs"
    using 2 by simp
  also have "... = to_nat (x # xs)" by simp
  finally show ?case by simp
qed

lemma to_nat_app: "to_nat (xs @ ys) = to_nat xs + (2 ^ length xs) * to_nat ys"
  by (induction xs) auto

lemma to_nat_length_upper_bound: "to_nat xs \<le> 2 ^ (length xs) - 1"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then have "to_nat (a # xs) = eval_bool a + 2 * to_nat xs" by simp
  also have "... \<le> eval_bool a + 2 * (2 ^ (length xs) - 1)" using Cons.IH by simp
  also have "... \<le> 1 + 2 * (2 ^ (length xs) - 1)" using eval_bool_leq_1[of a] by simp
  also have "... = 1 + (2 ^ (length xs + 1) - 1 - 1)" by simp
  also have "... = 2 ^ (length xs + 1) - 1"
    apply (intro add_diff_inverse_nat)
    using power_increasing[of 1 "length xs + 1" "2::nat"]
    by (simp add: add.commute)
  finally show ?case by simp
qed
lemma to_nat_length_bound: "to_nat xs < 2 ^ length xs"
  using to_nat_length_upper_bound[of xs]
  using le_eq_less_or_eq by fastforce
lemma to_nat_length_lower_bound: "to_nat (xs @ [True]) \<ge> 2 ^ length xs"
  by (induction xs) auto

lemma to_nat_replicate_false[simp]: "to_nat (replicate n False) = 0"
  by (induction n) simp_all

lemma to_nat_one_bit[simp]: "to_nat (replicate n False @ [True]) = 2 ^ n"
  by (simp add: to_nat_app)

lemma to_nat_replicate_true[simp]: "to_nat (replicate n True) = 2 ^ n - 1"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "2 ^ (Suc n) \<ge> (2 :: nat)" by simp
  hence 1: "2 ^ (Suc n) - 1 \<ge> (1 :: nat)" by linarith
  have "to_nat (replicate (Suc n) True) = 1 + 2 * to_nat (replicate n True)"
    by simp
  also have "... = 1 + 2 * (2 ^ n - 1)"
    using Suc.IH by simp
  also have "... = 2 ^ (Suc n) - 1"
    using le_add_diff_inverse[of 1 "2 ^ (Suc n) - 1"]
    using 1 by simp
  finally show ?case .
qed

lemma "to_nat xs = 0 \<longleftrightarrow> (\<exists>n. xs = replicate n False)"
proof
  show "to_nat xs = 0 \<Longrightarrow> \<exists>n. xs = replicate n False"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then have "a = False" "to_nat xs = 0" by auto
    then obtain n where "xs = replicate n False" using Cons.IH by auto
    hence "a # xs = replicate (Suc n) False" using \<open>a = False\<close> by simp
    then show ?case by blast
  qed
  show "\<exists>n. xs = replicate n False \<Longrightarrow> to_nat xs = 0"
    using to_nat_replicate_false by auto
qed

lemma to_nat_app_replicate[simp]: "to_nat (xs @ replicate n False) = to_nat xs"
  by (induction xs) auto

lemma change_bit_ineq: "length xs = length ys \<Longrightarrow> to_nat (xs @ False # zs) < to_nat (ys @ True # zs)"
proof -
  assume "length xs = length ys"
  have "to_nat (xs @ False # zs) = to_nat xs + 2 ^ (length xs + 1) * to_nat zs"
    using to_nat_app_replicate[of xs 1] to_nat_app by simp
  also have "... \<le> 2 ^ (length xs) - 1 + 2 ^ (length xs + 1) * to_nat zs"
    using to_nat_length_upper_bound[of xs] by linarith
  also have "... < 2 ^ (length xs) + 2 ^ (length xs + 1) * to_nat zs" by simp
  also have "... = 2 ^ (length ys) + 2 ^ (length ys + 1) * to_nat zs"
    using \<open>length xs = length ys\<close> by simp
  also have "... \<le> to_nat (ys @ [True]) + 2 ^ (length ys + 1) * to_nat zs"
    using to_nat_length_lower_bound[of ys] by simp
  also have "... = to_nat (ys @ True # zs)"
    using to_nat_app by simp
  finally show ?thesis .
qed

lemma to_nat_ineq_imp_False_bit: "to_nat xs < 2 ^ length xs - 1 \<Longrightarrow> \<exists>ys zs. xs = ys @ False # zs"
proof (rule ccontr)
  assume "\<nexists>ys zs. xs = ys @ False # zs"
  then have "\<forall>i\<in>{0..<length xs}. xs ! i = True"
    by (metis(full_types) atLeastLessThan_iff in_set_conv_decomp_first in_set_conv_nth)
  then have "xs = replicate (length xs) True" using list_is_replicate_iff by fast
  then have "to_nat xs = 2 ^ length xs - 1" using to_nat_replicate_true by metis
  thus "to_nat xs < 2 ^ length xs - 1 \<Longrightarrow> False" by simp
qed

lemma to_nat_bound_to_length_bound: "to_nat xs \<ge> 2 ^ n \<Longrightarrow> length xs \<ge> n + 1"
proof (rule ccontr)
  assume "to_nat xs \<ge> 2 ^ n"
  assume "\<not> n + 1 \<le> length xs"
  then have "n \<ge> length xs" by simp
  then have "to_nat xs \<ge> 2 ^ length xs" using \<open>to_nat xs \<ge> 2 ^ n\<close>
    using power_increasing le_trans one_le_numeral by meson
  then show False using to_nat_length_bound[of xs] by simp
qed

lemma to_nat_drop_take: "to_nat xs = to_nat (take k xs) + 2 ^ k * to_nat (drop k xs)"
proof -
  have "xs = take k xs @ drop k xs" by simp
  then have "to_nat xs = to_nat (take k xs) + 2 ^ (length (take k xs)) * to_nat (drop k xs)"
    using to_nat_app by metis
  also have "2 ^ (length (take k xs)) * to_nat (drop k xs) = 2 ^ k * to_nat (drop k xs)"
    by (cases "length xs < k") simp_all
  finally show ?thesis .
qed

lemma to_nat_take: "to_nat (take k xs) = to_nat xs mod 2 ^ k"
proof -
  have "to_nat xs = to_nat (take k xs) + 2 ^ k * to_nat (drop k xs)"
    by (simp add: to_nat_drop_take)
  then have "to_nat xs mod 2 ^ k = to_nat (take k xs) mod 2 ^ k" by simp
  moreover have "to_nat (take k xs) < 2 ^ k"
    using to_nat_length_bound[of "take k xs"] length_take[of k xs]
    by (metis add_leD1 leI min_absorb2 min_def to_nat_bound_to_length_bound)
  ultimately show ?thesis by simp
qed

lemma to_nat_drop: "to_nat (drop k xs) = to_nat xs div 2 ^ k"
proof -
  have "to_nat xs = to_nat xs mod 2 ^ k + 2 ^ k * to_nat (drop k xs)"
    using to_nat_drop_take[of xs k] to_nat_take[of k xs] by argo
  then have "to_nat xs div 2 ^ k = to_nat (drop k xs)"
    by (metis add.right_neutral bits_mod_div_trivial div_mult_self2 power_not_zero zero_neq_numeral)
  thus ?thesis by rule
qed

lemma to_nat_nth_True_bound:
  assumes "i < length xs"
  assumes "xs ! i = True"
  shows "to_nat xs \<ge> 2 ^ i"
proof -
  from assms have "xs = (take i xs @ [True]) @ drop (Suc i) xs"
    using id_take_nth_drop by fastforce
  then show "to_nat xs \<ge> 2 ^ i"
    using to_nat_app[of _ "drop (Suc i) xs"] to_nat_length_lower_bound[of "take i xs"] \<open>i < length xs\<close>
    by (metis append_eq_conv_conj le_add1 le_eq_less_or_eq list_isolate_nth trans_less_add1)
qed

subsection "Truncating and filling"

fun truncate_reversed :: "bool list \<Rightarrow> bool list" where
"truncate_reversed [] = []"
| "truncate_reversed (x#xs) = (if x then x#xs else truncate_reversed xs)"

definition truncate :: "nat_lsbf \<Rightarrow> nat_lsbf" where
"truncate xs = rev (truncate_reversed (rev xs))"

abbreviation truncated where "truncated x \<equiv> truncate x = x"

lemma truncate_reversed_eqI[simp]: "xs = (replicate n False) @ ys \<Longrightarrow> truncate_reversed xs = truncate_reversed ys"
  by (induction n arbitrary: xs ys) auto
corollary truncate_eqI[simp]: "xs = ys @ (replicate n False) \<Longrightarrow> truncate xs = truncate ys"
  by (simp add: truncate_def)

lemma replicate_truncate_reversed: "\<exists>n. (replicate n False) @ truncate_reversed xs = xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then obtain n where 1: "replicate n False @ truncate_reversed xs = xs" by blast
  hence "a # xs = a # replicate n False @ truncate_reversed xs" by simp
  show ?case
  proof (cases a)
    case True
    then have "truncate_reversed (a # xs) = a # xs" by simp
    also have "... = replicate 0 False @ a # xs" by simp
    finally show ?thesis by simp
  next
    case False
    then have "truncate_reversed (a # xs) = truncate_reversed xs" by simp
    hence "replicate (Suc n) False @ truncate_reversed (a # xs) = False # replicate n False @ truncate_reversed xs"
      by simp
    with 1 False have "replicate (Suc n) False @ truncate_reversed (a # xs) = a # xs" by simp
    then show ?thesis by blast
  qed
qed
corollary truncate_replicate: "\<exists>n. truncate xs @ (replicate n False) = xs"
proof -
  from replicate_truncate_reversed[of "rev xs"]
  obtain n where "replicate n False @ truncate_reversed (rev xs) = rev xs" by blast
  hence "rev (truncate_reversed (rev xs)) @ rev (replicate n False) = xs"
    using rev_append[symmetric, of "truncate_reversed (rev xs)" "replicate n False"]
    using rev_rev_ident[of xs]
    by simp
  hence "truncate xs @ replicate n False = xs" by (simp add: truncate_def)
  thus ?thesis by blast
qed
lemma decompose_trailing_zeros: "xs = truncate xs @ (replicate (length xs - length (truncate xs)) False)"
  using truncate_replicate[of xs]
  by (metis add_diff_cancel_left' length_append length_replicate)

lemma truncate_reversed_length_ineq: "length (truncate_reversed xs) \<le> length xs"
  by (induction xs) simp_all
lemma truncate_length_ineq: "length (truncate xs) \<le> length xs"
  by (metis Nat_LSBF.truncate_def length_rev truncate_reversed_length_ineq)

lemma truncate_reversed_fixed_point_iff: "truncate_reversed x = x \<longleftrightarrow> (x = [] \<or> hd x = True)"
proof (induction x)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then have "(a # x = [] \<or> hd (a # x) = True) = a" by simp
  moreover have "a \<Longrightarrow> truncate_reversed (a # x) = a # x" by simp
  moreover have "\<not> a \<Longrightarrow> truncate_reversed (a # x) = truncate_reversed x" by simp
  hence "\<not> a \<Longrightarrow> length (truncate_reversed (a # x)) \<le> length x"
    using truncate_reversed_length_ineq[of "x"] by simp
  hence "\<not> a \<Longrightarrow> truncate_reversed (a # x) \<noteq> (a # x)"
    using neq_if_length_neq[of "a#x" x] by force
  ultimately show ?case by simp
qed

lemma truncated_iff: "truncated x \<longleftrightarrow> (x = [] \<or> last x = True)"
proof -
  have "truncated x \<longleftrightarrow> truncate_reversed (rev x) = rev x"
    by (simp add: truncate_def rev_swap)
  also have "... \<longleftrightarrow> rev x = [] \<or> hd (rev x) = True"
    using truncate_reversed_fixed_point_iff[of "rev x"] .
  also have "... \<longleftrightarrow> x = [] \<or> last x = True"
    by (simp add: hd_rev)
  finally show ?thesis .
qed

lemma hd_truncate_reversed: "truncate_reversed xs \<noteq> [] \<Longrightarrow> hd (truncate_reversed xs) = True"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (rule ccontr)
    assume 1: "hd (truncate_reversed (a # xs)) \<noteq> True"
    then have "a = False" by auto
    with 1 have "hd (truncate_reversed xs) \<noteq> True" by simp
    hence "truncate_reversed xs = []" using Cons.IH by blast
    hence "truncate_reversed (a # xs) = []" using \<open>a = False\<close> by simp
    thus "False" using Cons.prems by simp
  qed
qed

lemma last_truncate: "truncate xs \<noteq> [] \<Longrightarrow> last (truncate xs) = True"
  using hd_truncate_reversed last_rev by (auto simp: truncate_def)

lemma truncate_truncate[simp]: "truncate (truncate xs) = truncate xs"
  using truncated_iff[of "truncate xs"] last_truncate by auto


lemma truncate_reversed_Nil_iff: "truncate_reversed xs = [] \<longleftrightarrow> (\<exists>n. xs = replicate n False)"
proof
  show "truncate_reversed xs = [] \<Longrightarrow> \<exists>n. xs = replicate n False"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then have "a = False" "truncate_reversed (a#xs) = truncate_reversed xs"
      by (auto split: if_splits)
    then obtain n where "xs = replicate n False" using Cons by auto
    hence "a # xs = replicate (Suc n) False" using \<open>a = False\<close> by simp
    thus ?case by blast
  qed
next
  show "\<exists>n. xs = replicate n False \<Longrightarrow> truncate_reversed xs = []"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by (metis Cons_replicate_eq truncate_reversed.simps(2))
  qed
qed

lemma truncate_Nil_iff: "truncate xs = [] \<longleftrightarrow> (\<exists>n. xs = replicate n False)"
  using truncate_reversed_Nil_iff[of "rev xs"]
  by (auto simp: truncate_def) (metis rev_replicate rev_rev_ident)

corollary truncate_neq_Nil: "truncate xs \<noteq> [] \<Longrightarrow> \<exists>ys zs. xs = ys @ True # zs"
  using truncate_Nil_iff[of xs]
  by (metis (full_types) hd_Cons_tl hd_truncate_reversed replicate_truncate_reversed truncate_reversed_Nil_iff)

lemma truncate_Cons: "truncate (a # xs) = (if \<not>a \<and> (truncate xs = []) then [] else a # truncate xs)"
proof (cases "truncate xs = []")
  case True
  then obtain n where "xs = replicate n False" using truncate_Nil_iff by blast
  then have "truncate (a # xs) = truncate [a]" by simp
  then show ?thesis using True by (simp add: truncate_def)
next
  case False
  then obtain ys n where "xs = ys @ True # (replicate n False)"
    using truncate_neq_Nil[of xs] bit_strong_decomp_2[of xs True] by auto
  then have "truncate xs = ys @ [True]" by (auto simp: truncate_def)
  moreover have "truncate (a # xs) = a # ys @ [True]"
    using \<open>xs = ys @ True # (replicate n False)\<close> by (auto simp: truncate_def)
  ultimately show ?thesis by simp
qed

lemma truncate_eq_Cons: "truncate xs = truncate ys \<Longrightarrow> truncate (a # xs) = truncate (a # ys)"
  using truncate_Cons by simp

lemma truncate_as_take: "\<And>xs. \<exists>n. truncate xs = take n xs"
  using truncate_replicate append_eq_conv_conj by blast

lemma to_nat_zero_iff: "to_nat xs = 0 \<longleftrightarrow> truncate xs = []"
proof (induction xs)
  case Nil
  then show ?case by (simp add: truncate_def)
next
  case (Cons a xs)
  have "to_nat (a # xs) = 0 \<longleftrightarrow> (eval_bool a = 0 \<and> to_nat xs = 0)" by simp
  also have "... \<longleftrightarrow> (a = False \<and> to_nat xs = 0)" using eval_bool_inj[of a "False"] by auto
  also have "... \<longleftrightarrow> (a = False \<and> truncate xs = [])" using Cons.IH by simp
  also have "... \<longleftrightarrow> (truncate (a # xs) = [])" using truncate_Cons by simp
  finally show ?case .
qed

lemma to_nat_eq_imp_truncate_eq: "to_nat xs = to_nat ys \<Longrightarrow> truncate xs = truncate ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case using to_nat_zero_iff by (simp add: truncate_def)
next
  case (Cons a xs)
  show ?case
  proof (cases "ys = []")
    case True
    then have "to_nat ys = 0" by simp
    hence "to_nat (a # xs) = 0" using Cons.prems by simp
    with \<open>to_nat ys = 0\<close> show "truncate (a # xs) = truncate ys"
      using to_nat_zero_iff[of "a # xs"] to_nat_zero_iff[of ys] by simp
  next
    case False
    then obtain b zs where "ys = b # zs" by (meson neq_Nil_conv)
    then have "to_nat (a # xs) = to_nat (b # zs)" using Cons.prems by simp
    then have 1: "eval_bool a + 2 * to_nat xs = eval_bool b + 2 * to_nat zs" by simp
    then have "eval_bool a = eval_bool b"
      by (metis add_cancel_right_left double_not_eq_Suc_double eval_bool.elims plus_1_eq_Suc)
    hence "a = b" using eval_bool_inj by simp
    from 1 have "to_nat xs = to_nat zs"
      using \<open>eval_bool a = eval_bool b\<close> by auto
    hence "truncate xs = truncate zs" using Cons.IH by simp
    hence "truncate (a # xs) = truncate (b # zs)" using \<open>a = b\<close>
      using truncate_eq_Cons[of xs zs a] by simp
    thus ?thesis using \<open>ys = b # zs\<close> by simp
  qed
qed

lemma truncate_from_nat[simp]: "truncate (from_nat x) = from_nat x"
  unfolding truncated_iff
  by (induction x rule: from_nat.induct) auto

lemma truncate_and_length_eq_imp_eq:
  assumes "truncate xs = truncate ys" "length xs = length ys"
  shows "xs = ys"
proof -
  obtain n where 1: "xs = truncate xs @ replicate n False"
    by (metis truncate_replicate)
  then have 2: "length xs = length (truncate xs) + n"
    by (metis length_append length_replicate)
  obtain m where 3: "ys = truncate ys @ replicate m False"
    by (metis truncate_replicate)
  then have "length ys = length (truncate ys) + m"
    by (metis length_append length_replicate)
  with 2 assms have "n = m" by simp
  with 1 3 assms show ?thesis by algebra
qed

lemma nat_lsbf_eqI:
  assumes "to_nat xs = to_nat ys"
  assumes "length xs = length ys"
  shows "xs = ys"
  using assms 
  using to_nat_eq_imp_truncate_eq truncate_and_length_eq_imp_eq by blast

interpretation nat_lsbf: abstract_representation from_nat to_nat truncate
proof
  show "to_nat \<circ> from_nat = id"
    using to_nat_from_nat comp_apply by fastforce
next
  show "from_nat \<circ> to_nat = truncate"
    using from_to_f_criterion[of to_nat from_nat truncate]
    using to_nat_from_nat truncate_from_nat to_nat_eq_imp_truncate_eq
    using comp_apply
    by fastforce
qed
    
lemma truncated_Cons_imp_truncated_tl: "truncated (x # xs) \<Longrightarrow> truncated xs"
  using truncated_iff by fastforce

(* ensures that the number has at least n bits *)
definition fill where "fill n xs = xs @ replicate (n - length xs) False"

lemma to_nat_fill[simp]: "to_nat (fill n xs) = to_nat xs"
  by (simp add: fill_def)

lemma length_fill[intro]: "length xs \<le> n \<Longrightarrow> length (fill n xs) = n"
  by (simp add: fill_def)

lemma take_id: "length xs = k \<Longrightarrow> take k xs = xs"
  by simp
lemma fill_id: "length xs \<ge> k \<Longrightarrow> fill k xs = xs"
  unfolding fill_def by simp

lemma length_fill': "length (fill n xs) = max n (length xs)"
  by (simp add: fill_def)

lemma length_fill_max[simp]:
  "length (fill (max (length xs) (length ys)) xs) = max (length xs) (length ys)"
  "length (fill (max (length xs) (length ys)) ys) = max (length xs) (length ys)"
  by (intro length_fill, simp)+


lemma truncate_fill: "truncate (fill k xs) = truncate xs"
  by (simp add: fill_def)

lemma fill_truncate: "length xs \<le> k \<Longrightarrow> fill k (truncate xs) = fill k xs"
proof -
  assume "length xs \<le> k"
  obtain n where n_def: "xs = truncate xs @ replicate n False"
    using truncate_replicate by metis
  then have "length xs = length (truncate xs) + n" by (metis length_append length_replicate)
  then have "length (truncate xs) + n \<le> k" using \<open>length xs \<le> k\<close> by simp
  from n_def have "fill k xs = (truncate xs @ replicate n False) @ replicate (k - length (truncate xs @ replicate n False)) False"
    using fill_def by presburger
  also have "... = truncate xs @ replicate (n + (k - length (truncate xs @ replicate n False))) False"
    by (simp add: replicate_add)
  also have "... = truncate xs @ replicate (n + (k - (length (truncate xs) + n))) False"
    by simp
  also have "... = truncate xs @ replicate (k - (length (truncate xs))) False"
    using \<open>length (truncate xs) + n \<le> k\<close> by simp
  also have "... = fill k (truncate xs)" by (simp add: fill_def)
  finally show ?thesis by simp
qed
  
lemma fill_take_com: "fill k (take k xs) = take k (fill k xs)"
  using fill_def by fastforce

lemma to_nat_length_lower_bound_truncated: "xs \<noteq> [] \<Longrightarrow> truncated xs \<Longrightarrow> to_nat xs \<ge> 2 ^ (length xs - 1)"
proof -
  assume "xs \<noteq> []" "truncated xs"
  then obtain xs' where "xs = xs' @ [True]"
    by (metis(full_types) append_butlast_last_id last_truncate)
  then show ?thesis using to_nat_length_lower_bound[of xs'] by simp
qed

lemma to_nat_length_bound_truncated: "truncated xs \<Longrightarrow> to_nat xs < 2 ^ n \<Longrightarrow> length xs \<le> n"
proof (rule ccontr)
  assume "truncated xs" "to_nat xs < 2 ^ n" "\<not> length xs \<le> n"
  show False
  proof (cases "xs = []")
    case True
    then show ?thesis using \<open>\<not> length xs \<le> n\<close> by simp
  next
    case False
    have "length xs \<ge> n + 1" using \<open>\<not> length xs \<le> n\<close> by simp
    then have "to_nat xs \<ge> 2 ^ n"
      using to_nat_length_lower_bound_truncated[of xs]
      using False \<open>truncated xs\<close>
      by (meson add_le_imp_le_diff dual_order.trans one_le_numeral power_increasing)
    then show ?thesis using \<open>to_nat xs < 2 ^ n\<close> by simp
  qed
qed

subsection "Right-shifts"

definition shift_right :: "nat \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf" where
  "shift_right n xs = (replicate n False) @ xs"

lemma to_nat_shift_right[simp]: "to_nat (shift_right n xs) = 2 ^ n * to_nat xs"
  unfolding shift_right_def using to_nat_app by simp

lemma length_shift_right[simp]: "length (shift_right n xs) = n + length xs"
  unfolding shift_right_def by simp

subsection "Subdividing lists"

subsubsection "Splitting a list in two blocks"

fun split_at :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list" where
  "split_at m xs = (take m xs, drop m xs)"

definition split :: "nat_lsbf \<Rightarrow> nat_lsbf \<times> nat_lsbf" where
  "split xs = (let n = length xs div (2::nat) in split_at n xs)"

lemma app_split: "split xs = (x0, x1) \<Longrightarrow> xs = x0 @ x1"
  unfolding split_def Let_def using append_take_drop_id[of "length xs div 2" xs] by simp

lemma length_split: "length xs mod 2 = 0 \<Longrightarrow> split xs = (x0, x1) \<Longrightarrow> length x0 = length xs div 2 \<and> length x1 = length xs div 2"
  unfolding split_def by fastforce

lemma length_split_le:
  assumes "split xs = (x0, x1)"
  shows "length x0 \<le> length xs" and "length x1 \<le> length xs"
  using app_split[OF assms] by simp_all

subsubsection "Splitting a list in multiple blocks"

text "@{term \<open>subdivide n xs\<close>} divides the list @{term xs} into blocks of size @{term n}."

fun subdivide :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
"subdivide 0 xs = undefined"
| "subdivide n [] = []"
| "subdivide n xs = take n xs # subdivide n (drop n xs)"

value "concat [[0..<2], [4..<7], [1..<5]]"

value "subdivide 2 [0..<6]"
value "subdivide 3 [0..<6]"
value "subdivide (2 ^ 2) [0..<2 ^ 6]"

lemma concat_subdivide: "n > 0 \<Longrightarrow> concat (subdivide n xs) = xs"
  by (induction n xs rule: subdivide.induct) simp_all

lemma subdivide_step:
  assumes "n > 0"
  assumes "xs \<noteq> []"
  assumes "length xs = n * k"
  obtains ys zs where "xs = ys @ zs" "length ys = n" "length zs = n * (k - 1)"
    "subdivide n xs = ys # subdivide n zs"
proof -
  from assms obtain a xs' where "xs = a # xs'" using list.exhaust by blast
  from assms have "k > 0"
    using zero_less_iff_neq_zero by fastforce
  then obtain k' where "k = Suc k'" using gr0_implies_Suc by auto
  then have "length xs = n + n * k'" using assms(3) by simp
  define ys zs where "ys = take n xs" "zs = drop n xs"
  with \<open>length xs = n + n * k'\<close> have "xs = ys @ zs" "length ys = n" "length zs = n * k'" by simp_all
  moreover have "subdivide n xs = ys # subdivide n zs" using ys_zs_def assms(1) assms(2) Suc_diff_1 subdivide.simps(3)
    \<open>xs = a # xs'\<close> by metis
  ultimately show "(\<And>ys zs.
        xs = ys @ zs \<Longrightarrow>
        length ys = n \<Longrightarrow>
        length zs = n * (k - 1) \<Longrightarrow>
        subdivide n xs = ys # subdivide n zs \<Longrightarrow> thesis) \<Longrightarrow>
    thesis"
    by (simp add: \<open>k = Suc k'\<close>)
qed

lemma subdivide_step':
  assumes "n > 0"
  assumes "xs \<noteq> []"
  shows "subdivide n xs = (take n xs) # subdivide n (drop n xs)"
  using assms
  by (cases n; cases xs; simp_all)

lemma subdivide_correct:
  assumes "n > 0"
  assumes "length xs = n * k"
  shows "length (subdivide n xs) = k \<and> (x \<in> set (subdivide n xs) \<longrightarrow> length x = n)"
  using assms
proof (induction k arbitrary: xs n x)
  case 0
  then have "subdivide n xs = []" using 0 gr0_conv_Suc by force
  then show ?case by simp
next
  case (Suc k)
  then have "xs \<noteq> []" by force
  from subdivide_step[OF \<open>n > 0\<close> this \<open>length xs = n * Suc k\<close>] obtain ys zs where ys_zs:
    "xs = ys @ zs"
    "length ys = n"
    "length zs = n * (Suc k - 1)"
    "subdivide n xs = ys # subdivide n zs"
    by blast
  then have "length zs = n * k" by simp
  note IH = Suc.IH[OF \<open>n > 0\<close> this]
  from IH show ?case using ys_zs by simp
qed

lemma nth_nth_subdivide:
  assumes "n > 0"
  assumes "length xs = n * k"
  assumes "i < k" "j < n"
  shows "subdivide n xs ! i ! j = xs ! (i * n + j)"
  using assms
proof (induction k arbitrary: xs i)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then have "xs \<noteq> []" by auto
  with Suc subdivide_step obtain ys zs where "xs = ys @ zs" "length ys = n" "length zs = n * (Suc k - 1)"
    "subdivide n xs = ys # subdivide n zs" by blast
  then have "length zs = n * k" by simp
  show ?case
  proof (cases i)
    case 0
    then have "subdivide n xs ! i ! j = ys ! (i * n + j)" using \<open>subdivide n xs = ys # subdivide n zs\<close> by simp
    then show ?thesis using \<open>xs = ys @ zs\<close> 0 \<open>j < n\<close> \<open>length ys = n\<close>
      by (simp add: nth_append)
  next
    case (Suc i')
    then have "subdivide n xs ! i ! j = subdivide n zs ! i' ! j"
      using \<open>subdivide n xs = ys # subdivide n zs\<close> by simp
    also have "... = zs ! (i' * n + j)"
      apply (intro Suc.IH[of zs i'])
      subgoal using \<open>n > 0\<close> .
      subgoal using \<open>length zs = n * k\<close> .
      subgoal using \<open>i < Suc k\<close> \<open>i = Suc i'\<close> by simp
      subgoal using \<open>j < n\<close> .
      done
    also have "... = xs ! (i * n + j)"
      using \<open>i = Suc i'\<close> \<open>xs = ys @ zs\<close> \<open>length ys = n\<close>
      by (metis ab_semigroup_add_class.add_ac(1) mult_Suc nth_append_length_plus)
    finally show ?thesis .
  qed
qed

lemma subdivide_concat:
  assumes "n > 0"
  assumes "\<And>i. i < length xs \<Longrightarrow> length (xs ! i) = n"
  shows "subdivide n (concat xs) = xs"
proof (intro iffD1[OF concat_eq_concat_iff])
  show "concat (subdivide n (concat xs)) = concat xs"
    using concat_subdivide[OF \<open>n > 0\<close>] .
  have "map length xs = replicate (length xs) n"
    apply (intro replicate_eqI)
    subgoal by simp
    subgoal using assms by (metis in_set_conv_nth length_map nth_map)
    done
  then have "length (concat xs) = length xs * n"
    by (simp add: length_concat sum_list_replicate)
  then show "length (subdivide n (concat xs)) = length xs"
    apply (intro conjunct1[OF subdivide_correct] \<open>n > 0\<close>) by simp
  show "\<forall>(x, y)\<in>set (zip (subdivide n (concat xs)) xs). length x = length y"
  proof
    fix z
    assume a: "z \<in> set (zip (subdivide n (concat xs)) xs)"
    then obtain x y where "z = (x, y)" by fastforce
    from a obtain i where "i < length xs" "z = zip (subdivide n (concat xs)) xs ! i"
      using \<open>length (subdivide n (concat xs)) = length xs\<close>
      by (metis (no_types, lifting) gen_length_def in_set_conv_nth length_code length_zip min_0R min_add_distrib_left)
    then have "subdivide n (concat xs) ! i = x" "xs ! i = y"
      using \<open>z = (x, y)\<close> \<open>length (subdivide n (concat xs)) = length xs\<close> by simp_all
    then have "length x = n" using \<open>i < length xs\<close> \<open>length (subdivide n (concat xs)) = length xs\<close>
      using \<open>length (concat xs) = length xs * n\<close>
      \<open>n > 0\<close> mult.commute[of n "length xs"]
      by (metis nth_mem subdivide_correct)
    moreover from \<open>xs ! i = y\<close> \<open>i < length xs\<close> have "length y = n" using assms by blast
    ultimately show "case z of (x, y) \<Rightarrow> length x = length y" using \<open>z = (x, y)\<close> by simp
  qed
qed

lemma to_nat_subdivide:
  assumes "n > 0"
  assumes "length xs = n * k"
  shows "to_nat xs = (\<Sum>i \<leftarrow> [0..<k]. to_nat (subdivide n xs ! i) * 2 ^ (i * n))"
  using assms
proof (induction k arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then have "length (take n xs) = n" "length (drop n xs) = n * k" by simp_all
  from Suc have "xs \<noteq> []" by auto
  have "(\<Sum>i \<leftarrow> [0..<Suc k]. to_nat (subdivide n xs ! i) * 2 ^ (i * n))
      = to_nat (subdivide n xs ! 0) * 2 ^ (0 * n) + (\<Sum>i \<leftarrow> [1..<Suc k]. to_nat (subdivide n xs ! i) * 2 ^ (i * n))"
    by (intro sum_list_split_0)
  also have "subdivide n xs ! 0 = take n xs"
    using Suc \<open>xs \<noteq> []\<close> subdivide_step'[OF \<open>0 < n\<close> \<open>xs \<noteq> []\<close>] by simp
  also have "(\<Sum>i \<leftarrow> [1..<Suc k]. to_nat (subdivide n xs ! i) * 2 ^ (i * n))
           = (\<Sum>i \<leftarrow> [0..<k]. to_nat (subdivide n xs ! (i + 1)) * 2 ^ ((i + 1) * n))"
    using sum_list_index_shift[of "\<lambda>i. to_nat (subdivide n xs ! i) * 2 ^ (i * n)" 1 0 k]
    by simp
  also have "... = (\<Sum>i \<leftarrow> [0..<k]. to_nat (subdivide n (drop n xs) ! i) * 2 ^ ((i + 1) * n))"
    using subdivide_step'[OF \<open>0 < n\<close> \<open>xs \<noteq> []\<close>] by simp
  also have "... = (\<Sum>i \<leftarrow> [0..<k]. (to_nat (subdivide n (drop n xs) ! i) * (2 ^ n * 2 ^ (i * n))))"
    by (simp add: power_add)
  also have "... = (\<Sum>i \<leftarrow> [0..<k]. 2 ^ n * (to_nat (subdivide n (drop n xs) ! i) * 2 ^ (i * n)))"
    by (simp add: mult.left_commute)
  also have "... = 2 ^ n * (\<Sum>i \<leftarrow> [0..<k]. to_nat (subdivide n (drop n xs) ! i) * 2 ^ (i * n))"
    by (simp add: sum_list_const_mult)
  also have "... = 2 ^ n * to_nat (drop n xs)"
    using Suc.IH[OF \<open>0 < n\<close> \<open>length (drop n xs) = n * k\<close>] by argo
  finally have "(\<Sum>i \<leftarrow> [0..<Suc k]. to_nat (subdivide n xs ! i) * 2 ^ (i * n))
    = to_nat (take n xs) + 2 ^ n * to_nat (drop n xs)"
    by simp
  also have "... = to_nat (take n xs @ drop n xs)"
    by (simp only: to_nat_app \<open>length (take n xs) = n\<close>)
  also have "... = to_nat xs" by simp
  finally show "to_nat xs = (\<Sum>i \<leftarrow> [0..<Suc k]. to_nat (subdivide n xs ! i) * 2 ^ (i * n))"
    by simp
qed

subsection "The @{term bitsize} function"

text "@{term \<open>bitsize n\<close>} calculates how many bits are needed in the LSBF encoding of @{term n}."

fun bitsize :: "nat \<Rightarrow> nat" where
"bitsize 0 = 0"
| "bitsize n = 1 + bitsize (n div 2)"

lemma bitsize_is_floorlog: "bitsize = floorlog 2"
  apply (intro ext)
  subgoal for n
    apply (induction n rule: bitsize.induct)
    by (auto simp add: floorlog_eq_zero_iff compute_floorlog)
  done

corollary bitsize_bitlen: "int (bitsize n) = bitlen (int n)"
  unfolding bitsize_is_floorlog bitlen_def by simp

lemma bitsize_eq: "bitsize n = length (from_nat n)"
proof (induction n rule: less_induct)
  case (less n)
  then show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis by simp
  next
    case False
    then have 1: "bitsize n = 1 + bitsize (n div 2)"
      by (metis bitsize.elims)
    from False have "length (from_nat n) = length ((if n mod 2 = 0 then False else True) # from_nat (n div 2))"
      by (metis from_nat.elims)
    also have "... = 1 + bitsize (n div 2)" using less[of "n div 2"] False by simp
    finally show "bitsize n = length (from_nat n)" using 1 by simp
  qed
qed

lemma bitsize_zero_iff: "bitsize n = 0 \<longleftrightarrow> n = 0"
  by (simp add: bitsize_is_floorlog floorlog_eq_zero_iff)

lemma truncated_iff': "truncated x \<longleftrightarrow> length x = bitsize (to_nat x)"
proof
  assume "truncated x"
  then have "x = from_nat (to_nat x)" unfolding nat_lsbf.f_fixed_point_iff' .
  then show "length x = bitsize (to_nat x)" unfolding bitsize_eq by simp
next
  assume "length x = bitsize (to_nat x)"
  then have "length x = length (from_nat (to_nat x))" unfolding bitsize_eq .
  moreover have "to_nat x = to_nat (from_nat (to_nat x))" by simp
  ultimately show "truncated x" unfolding nat_lsbf.f_fixed_point_iff'
    by (intro nat_lsbf_eqI; argo)
qed

lemma bitsize_length: "bitsize n \<le> k \<longleftrightarrow> n < 2 ^ k"
  unfolding bitsize_is_floorlog floorlog_le_iff by simp

lemma two_pow_bitsize_pos_bound: "n > 0 \<Longrightarrow> 2 ^ bitsize n \<le> 2 * n"
proof -
  assume "n > 0"
  then have "2 ^ (bitsize n - 1) \<le> n"
    using bitsize_length[of n "bitsize n - 1"] by fastforce
  then have "2 ^ (bitsize n - 1 + 1) \<le> 2 * n" by simp
  also have "bitsize n - 1 + 1 = bitsize n" using bitsize_zero_iff[of n] \<open>n > 0\<close> by simp
  finally show ?thesis .
qed

lemma two_pow_bitsize_bound: "2 ^ bitsize n \<le> 2 * n + 1"
  using two_pow_bitsize_pos_bound[of n] by (cases n) simp_all

lemma bitsize_mono: "n1 \<le> n2 \<Longrightarrow> bitsize n1 \<le> bitsize n2"
  unfolding bitsize_is_floorlog by (rule floorlog_mono)

subsubsection "The @{term next_power_of_2} function"

lemma power_of_2_recursion: "(\<exists>k. (n::nat) = 2 ^ k) \<longleftrightarrow> (n = 1 \<or> (n mod 2 = 0 \<and> (\<exists>k. n div 2 = 2 ^ k)))"
proof
  assume "\<exists>k. n = 2 ^ k"
  then obtain k where k_def: "n = 2 ^ k" by blast
  show "n = 1 \<or> (n mod 2 = 0 \<and> (\<exists>k. n div 2 = 2 ^ k))"
    using k_def by (cases k) simp_all
next
  assume "n = 1 \<or> (n mod 2 = 0 \<and> (\<exists>k. n div 2 = 2 ^ k))"
  then consider "n = 1" | "n mod 2 = 0 \<and> (\<exists>k. n div 2 = 2 ^ k)" by argo
  then show "\<exists>k. n = 2 ^ k"
  proof cases
    case 1
    then have "n = 2 ^ 0" by simp
    then show ?thesis by blast
  next
    case 2
    then obtain k where "n div 2 = 2 ^ k" by blast
    with 2 have "n = 2 ^ Suc k" by auto
    then show ?thesis by blast
  qed
qed

fun is_power_of_2 :: "nat \<Rightarrow> bool" where
"is_power_of_2 0 = False"
| "is_power_of_2 (Suc 0) = True"
| "is_power_of_2 n = ((n mod 2 = 0) \<and> is_power_of_2 (n div 2))"

lemma is_power_of_2_correct: "is_power_of_2 n \<longleftrightarrow> (\<exists>k. n = 2 ^ k)"
proof (induction n rule: is_power_of_2.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by (metis is_power_of_2.simps(2) nat_power_eq_Suc_0_iff)
next
  case (3 va)
  let ?n = "Suc (Suc va)"
  have "is_power_of_2 ?n = ((?n mod 2 = 0) \<and> is_power_of_2 (?n div 2))"
    by simp
  also have "... = ((?n mod 2 = 0) \<and> (\<exists>k. (?n div 2) = 2 ^ k))"
    using 3 by argo
  also have "... = (\<exists>k. ?n = 2 ^ k)"
    using power_of_2_recursion[of ?n] by simp
  finally show ?case .
qed


fun next_power_of_2 :: "nat \<Rightarrow> nat" where
"next_power_of_2 n = (if is_power_of_2 n then n else 2 ^ (bitsize n))"

lemma next_power_of_2_lower_bound: "next_power_of_2 k \<ge> k"
  apply (cases "is_power_of_2 k")
  subgoal by simp
  subgoal premises prems
  proof -
    from prems have "next_power_of_2 k - 1 = 2 ^ bitsize k - 1" by simp
    also have "... = 2 ^ (length (from_nat k)) - 1" using bitsize_eq by simp
    also have "... \<ge> k" using to_nat_length_upper_bound[of "from_nat k"] by simp
    finally show ?thesis by simp
  qed
  done

lemma next_power_of_2_upper_bound:
  assumes "k \<noteq> 0"
  shows "next_power_of_2 k \<le> 2 * k"
  apply (cases "is_power_of_2 k")
  subgoal by simp
  subgoal premises prems
  proof -
    have "2 ^ (length (from_nat k) - 1) \<le> to_nat (from_nat k)"
      apply (intro to_nat_length_lower_bound_truncated)
      subgoal using assms by (cases k; simp)
      subgoal by simp
      done
    then have "2 ^ length (from_nat k) \<le> 2 * to_nat (from_nat k)"
      using assms by (cases k; simp)
    also have "... = 2 * k" by simp
    also have "2 ^ length (from_nat k) = next_power_of_2 k"
      using prems bitsize_eq by simp
    finally show ?thesis .
  qed
  done

lemma next_power_of_2_upper_bound': "next_power_of_2 k \<le> 2 * k + 1"
  apply (cases k)
  subgoal by simp
  subgoal using next_power_of_2_upper_bound[of k] by simp
  done

lemma next_power_of_2_is_power_of_2: "\<exists>k. next_power_of_2 n = 2 ^ k"
  using is_power_of_2_correct by simp

subsection "Addition"

(* second entry: carry bit *)
fun bit_add_carry :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<times> bool" where
"bit_add_carry False False False = (False, False)"
| "bit_add_carry False False True = (True, False)"
| "bit_add_carry False True False = (True, False)"
| "bit_add_carry False True True = (False, True)"
| "bit_add_carry True False False = (True, False)"
| "bit_add_carry True False True = (False, True)"
| "bit_add_carry True True False = (False, True)"
| "bit_add_carry True True True = (True, True)"

lemma bit_add_carry_correct: "bit_add_carry c x y = (a, b) \<Longrightarrow> eval_bool c + eval_bool x + eval_bool y = eval_bool a + 2 * eval_bool b"
  by (cases c; cases x; cases y) auto

subsubsection "Increment operation"

(* increases a number by 1 *)
fun inc_nat :: "nat_lsbf \<Rightarrow> nat_lsbf" where
"inc_nat [] = [True]"
| "inc_nat (False # xs) = True # xs"
| "inc_nat (True # xs) = False # (inc_nat xs)"

lemma length_inc_nat': "length (inc_nat xs) = length xs + of_bool (to_nat xs + 1 \<ge> 2 ^ length xs)"
proof (induction xs rule: inc_nat.induct)
  case 1
  then show ?case by simp
next
  case (2 xs)
  then show ?case using to_nat_length_bound[of xs] by simp
next
  case (3 xs)
  then show ?case by simp
qed

lemma length_inc_nat_lower: "length (inc_nat xs) \<ge> length xs"
  unfolding length_inc_nat' by simp

lemma length_inc_nat_upper: "length (inc_nat xs) \<le> length xs + 1"
  unfolding length_inc_nat' by simp

lemma inc_nat_nonempty: "inc_nat xs \<noteq> []"
  by (induction xs rule: inc_nat.induct) simp_all

lemma inc_nat_replicate_True: "inc_nat (replicate m True) = replicate m False @ [True]"
  by (induction m) simp_all

lemma inc_nat_replicate_True_2: "inc_nat (replicate m True @ False # ys) = replicate m False @ True # ys"
  by (induction m) simp_all

lemma length_inc_nat_iff: "length (inc_nat xs) = length xs \<longleftrightarrow> (\<exists>ys zs. xs = ys @ False # zs)"
proof (intro iffI, rule ccontr)
  assume "\<nexists>ys zs. xs = ys @ False # zs"
  then have "\<forall>i \<in> {0..<length xs}. xs!i = True"
    by (metis(full_types) atLeastLessThan_iff in_set_conv_nth split_list)
  then have "xs = replicate (length xs) True"
    by (simp only: list_is_replicate_iff)
  then show "length (inc_nat xs) = length xs \<Longrightarrow> False"
    using inc_nat_replicate_True
    by (metis length_append_singleton length_replicate n_not_Suc_n)
next
  assume "\<exists>ys zs. xs = ys @ False # zs"
  then have "\<exists>n zs'. xs = replicate n True @ False # zs'"
    using bit_strong_decomp_1 by fastforce
  then show "length (inc_nat xs) = length xs"
    using inc_nat_replicate_True_2 by fastforce
qed

lemma inc_nat_last_bit_True: "length (inc_nat xs) = Suc (length xs) \<Longrightarrow> \<exists>zs. inc_nat xs = zs @ [True]"
  by (induction xs rule: inc_nat.induct) auto

lemma inc_nat_truncated: "truncated xs \<Longrightarrow> truncated (inc_nat xs)"
proof (induction xs rule: inc_nat.induct)
  case 1
  then show ?case using truncate_def by simp
next
  case (2 xs)
  then show ?case by (simp add: truncated_iff)
next
  case (3 xs)
  then show ?case by (simp add: truncated_iff inc_nat_nonempty split: if_splits)
qed

lemma inc_nat_correct: "to_nat (inc_nat xs) = to_nat xs + 1"
  by (induction xs rule: inc_nat.induct) simp_all

lemma length_inc_nat: "length (inc_nat xs) = max (length xs) (floorlog 2 (to_nat xs + 1))"
proof (induction xs rule: inc_nat.induct)
  case 1
  then show ?case by (simp add: compute_floorlog)
next
  case (2 xs)
  then show ?case using to_nat_length_bound[of "False # xs"]
    by (simp add: floorlog_leI)
next
  case (3 xs)
  then have "length (inc_nat (True # xs)) = Suc (max (length xs) (floorlog 2 (Suc (to_nat xs))))"
    by simp
  also have "... = max (length (True # xs)) (Suc (floorlog 2 (Suc (to_nat xs))))"
    by simp
  also have "... = max (length (True # xs)) (floorlog 2 (2 * Suc (to_nat xs)))"
    apply (intro arg_cong2[where f = max] refl)
    by (simp add: compute_floorlog)
  finally show ?case by simp 
qed

subsubsection "Addition with a carry bit"

(* performs addition with a carry bit *)
fun add_carry :: "bool \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf" where
"add_carry False [] y = y"
| "add_carry False x [] = x"
| "add_carry True [] y = inc_nat y"
| "add_carry True x [] = inc_nat x"
| "add_carry c (x#xs) (y#ys) = (let (a, b) = bit_add_carry c x y in a#(add_carry b xs ys))"

lemma add_carry_correct: "to_nat (add_carry c x y) = eval_bool c + to_nat x + to_nat y"
proof (induction c x y rule: add_carry.induct)
  case (1 y)
  then show ?case by simp
next
  case (2 v va)
  then show ?case by simp
next
  case (3 y)
  then show ?case using inc_nat_correct by simp
next
  case (4 v va)
  then show ?case using inc_nat_correct by simp
next
  case (5 c x xs y ys)
  define a b where "a = fst (bit_add_carry c x y)" "b = snd (bit_add_carry c x y)"
  then have "to_nat (add_carry c (x#xs) (y#ys)) = to_nat (a # add_carry b xs ys)"
    by (simp add: case_prod_beta' Let_def)
  also have "... = eval_bool a + 2 * to_nat (add_carry b xs ys)" by simp
  also have "... = eval_bool a + 2 * (eval_bool b + to_nat xs + to_nat ys)"
    using 5 a_b_def prod.collapse[of "bit_add_carry c x y"] by algebra
  also have "... = eval_bool c + eval_bool x + eval_bool y + 2 * (to_nat xs + to_nat ys)"
    using bit_add_carry_correct a_b_def by (simp add: prod_eq_iff)
  also have "... = eval_bool c + to_nat (x#xs) + to_nat (y#ys)" by simp
  finally show ?case .
qed

lemma length_add_carry': "length (add_carry c xs ys) = max (length xs) (length ys) + of_bool (to_nat xs + to_nat ys + of_bool c \<ge> 2 ^ max (length xs) (length ys))"
proof (induction c xs ys rule: add_carry.induct)
  case (1 y)
  then show ?case using to_nat_length_bound[of y] by simp
next
  case (2 v va)
  then show ?case
    using to_nat_length_bound[of va] by simp
next
  case (3 y)
  then show ?case by (simp add: length_inc_nat')
next
  case (4 v va)
  then show ?case by (simp add: length_inc_nat')
next
  case (5 c x xs y ys)

  have l: "2 ^ Suc a \<le> 2 * b + 1 \<longleftrightarrow> 2 ^ Suc a \<le> 2 * b" for a b :: nat
    by fastforce

  obtain a b where "bit_add_carry c x y = (a, b)" by fastforce
  then have "add_carry c (x # xs) (y # ys) = a # (add_carry b xs ys)" by simp
  then have "length (add_carry c (x # xs) (y # ys)) = 1 + max (length xs) (length ys) + of_bool (2 ^ max (length xs) (length ys) \<le> to_nat xs + to_nat ys + of_bool b)"
    using "5.IH"[OF \<open>bit_add_carry c x y = (a, b)\<close>[symmetric] refl] by (simp only: length_Cons)
  also have "... = max (length (x # xs)) (length (y # ys)) + of_bool (2 ^ max (length xs) (length ys) \<le> to_nat xs + to_nat ys + of_bool b)"
    by simp
  also have "... = max (length (x # xs)) (length (y # ys)) + of_bool (2 ^ max (length (x # xs)) (length (y # ys)) \<le> to_nat (x # xs) + to_nat (y # ys) + of_bool c)"
  proof (intro arg_cong2[where f = "(+)"] refl arg_cong[where f = of_bool])
    have "to_nat (x # xs) + to_nat (y # ys) + of_bool c =
        2 * to_nat xs + 2 * to_nat ys + of_bool x + of_bool y + of_bool c"
      by simp
    also have "... = 2 * to_nat xs + 2 * to_nat ys + of_bool a + 2 * of_bool b"
      using bit_add_carry_correct[OF \<open>bit_add_carry c x y = (a, b)\<close>] by simp
    finally have r: "to_nat (x # xs) + to_nat (y # ys) + of_bool c = ..." .
    show "(2 ^ max (length xs) (length ys) \<le> to_nat xs + to_nat ys + of_bool b) =
    (2 ^ max (length (x # xs)) (length (y # ys)) \<le> to_nat (x # xs) + to_nat (y # ys) + of_bool c)"
      unfolding r using l[of "max (length xs) (length ys)" "to_nat xs + to_nat ys + of_bool b"]
      by auto
  qed
  finally show ?case .
qed

lemma length_add_carry: "length (add_carry c xs ys) = max (max (length xs) (length ys)) (floorlog 2 (of_bool c + to_nat xs + to_nat ys))"
proof (induction c xs ys rule: add_carry.induct)
  case (1 y)
  then show ?case using to_nat_length_bound[of y]
    by (simp add: floorlog_leI)
next
  case (2 v va)
  then show ?case using to_nat_length_bound[of "v # va"]
    by (simp add: floorlog_leI)
next
  case (3 y)
  then show ?case by (simp add: length_inc_nat)
next
  case (4 v va)
  then show ?case by (simp add: length_inc_nat)
next
  case (5 c x xs y ys)
  obtain a b where "bit_add_carry c x y = (a, b)" by fastforce
  then have "add_carry c (x # xs) (y # ys) = a # (add_carry b xs ys)" by simp
  then have "length (add_carry c (x # xs) (y # ys)) = Suc (max (max (length xs) (length ys)) (floorlog 2 (of_bool b + to_nat xs + to_nat ys)))"
    using 5 \<open>bit_add_carry c x y = (a, b)\<close> by (simp only: length_Cons)
  also have "... = max (max (length (x # xs)) (length (y # ys))) (1 + floorlog 2 (of_bool b + to_nat xs + to_nat ys))"
    by simp
  also have "... = max (max (length (x # xs)) (length (y # ys))) (floorlog 2 (of_bool c + to_nat (x # xs) + to_nat (y # ys)))"
  proof (cases "of_bool a + 2 * (of_bool b + to_nat xs + to_nat ys) > 0")
    case True
    then show ?thesis
    proof (intro arg_cong2[where f = max] refl)
      have "floorlog 2 (of_bool c + to_nat (x # xs) + to_nat (y # ys)) =
          floorlog 2 ((of_bool c + of_bool x + of_bool y) + 2 * (to_nat xs + to_nat ys))"
        by simp
      also have "... = floorlog 2 ((of_bool a + 2 * of_bool b) + 2 * (to_nat xs + to_nat ys))"
        using bit_add_carry_correct[OF \<open>bit_add_carry c x y = (a, b)\<close>] by simp
      also have "... = floorlog 2 (of_bool a + 2 * (of_bool b + to_nat xs + to_nat ys))"
        by simp
      also have "... = 1 + floorlog 2 (of_bool b + to_nat xs + to_nat ys)"
        using compute_floorlog[of 2 "of_bool a + 2 * (of_bool b + to_nat xs + to_nat ys)"] True
        by simp
      finally show "... = floorlog 2 (of_bool c + to_nat (x # xs) + to_nat (y # ys))" by simp
    qed
  next
    case False
    then have 01: "of_bool a = 0" "of_bool b = 0" "to_nat xs = 0" "to_nat ys = 0" by simp_all
    then have 02: "of_bool c = 0" "of_bool x = 0" "of_bool y = 0"
      using bit_add_carry_correct[OF \<open>bit_add_carry c x y = (a, b)\<close>] by simp_all
    from 01 02 show ?thesis by (simp add: floorlog_def)
  qed
  finally show ?case .
qed

lemma length_add_carry_lower: "length (add_carry c xs ys) \<ge> max (length xs) (length ys)"
  unfolding length_add_carry' by simp

lemma length_add_carry_upper: "length (add_carry c xs ys) \<le> max (length xs) (length ys) + 1"
  unfolding length_add_carry' by simp

lemma add_carry_last_bit_True: "length (add_carry c xs ys) = max (length xs) (length ys) + 1 \<Longrightarrow> \<exists>zs. add_carry c xs ys = zs @ [True]"
proof (induction c xs ys rule: add_carry.induct)
  case (1 y)
  then show ?case by simp
next
  case (2 v va)
  then show ?case by simp
next
  case (3 y)
  then show ?case by (simp add: inc_nat_last_bit_True)
next
  case (4 v va)
  then show ?case by (simp add: inc_nat_last_bit_True)
next
  case (5 c x xs y ys)
  obtain a b where "bit_add_carry c x y = (a, b)" by fastforce
  then have 1: "add_carry c (x # xs) (y # ys) = a # (add_carry b xs ys)"
    by simp
  from 5 have "length (add_carry b xs ys) = max (length (x # xs)) (length (y # ys))"
    using \<open>bit_add_carry c x y = (a, b)\<close> by auto
  also have "... = max (length xs) (length ys) + 1" by simp
  finally obtain zs where "add_carry b xs ys = zs @ [True]" using 5 \<open>bit_add_carry c x y = (a, b)\<close>
    by presburger
  then show ?case using 1 by simp
qed

(* Note that this is even stronger than the commutative law obtained by the correctness of
add_carry, since it even holds for non-truncated inputs *)
lemma add_carry_com: "add_carry c xs ys = add_carry c ys xs"
  apply (intro nat_lsbf_eqI)
  subgoal by (simp add: add_carry_correct)
  subgoal by (simp only: length_add_carry' max.commute add.commute)
  done

lemma add_carry_rNil[simp]: "add_carry True y [] = inc_nat y"
  by (cases y; simp)
lemma add_carry_rNil_nocarry[simp]: "add_carry False y [] = y"
  by (cases y; simp)

lemma add_carry_True_inc_nat:
"add_carry True xs ys = inc_nat (add_carry False xs ys) \<and>
 add_carry True xs ys = add_carry False (inc_nat xs) ys \<and>
 add_carry True xs ys = add_carry False xs (inc_nat ys)"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case
    apply (intro conjI)
    subgoal by simp
    subgoal
      apply (cases ys)
      subgoal by simp
      subgoal for a ys'
        by (cases a) simp_all
      done
    subgoal by simp
    done
next
  case (Cons a xs)
  then show ?case
    apply (cases a; cases ys)
    subgoal by simp
    subgoal for b ys'
      apply (cases b)
      subgoal by fastforce
      subgoal by simp
      done
    subgoal by (simp add: add_carry_com)
    subgoal for b ys'
      apply (cases b)
      subgoal by fastforce
      subgoal by simp
      done
    done
qed

lemma inc_nat_add_carry:
  "inc_nat (add_carry c xs ys) = add_carry c (inc_nat xs) ys \<and>
   inc_nat (add_carry c xs ys) = add_carry c xs (inc_nat ys)"
proof (cases c)
  case True
  then have
    "add_carry c (inc_nat xs) ys = inc_nat (add_carry False (inc_nat xs) ys)"
    "add_carry c xs (inc_nat ys) = inc_nat (add_carry False xs (inc_nat ys))"
    using add_carry_True_inc_nat by simp_all
  moreover have
    "add_carry False (inc_nat xs) ys = inc_nat (add_carry False xs ys)"
    using add_carry_True_inc_nat[of xs ys] by argo
  moreover have "add_carry False xs (inc_nat ys) = inc_nat (add_carry False xs ys)"
    using add_carry_True_inc_nat[of xs ys] by argo
  ultimately show ?thesis using add_carry_True_inc_nat True by simp
next
  case False
  then show ?thesis using add_carry_True_inc_nat[of xs ys] by auto
qed

lemma add_carry_inc_nat_simps:
  "add_carry True xs ys = inc_nat (add_carry False xs ys)"
  "add_carry False (inc_nat xs) ys = inc_nat (add_carry False xs ys)"
  "add_carry False xs (inc_nat ys) = inc_nat (add_carry False xs ys)"
  using inc_nat_add_carry[of _ xs ys] add_carry_True_inc_nat[of xs ys]
  by argo+

lemma add_carry_assoc: "add_carry c2 (add_carry c1 xs ys) zs = add_carry c1 xs (add_carry c2 ys zs)"
  apply (intro nat_lsbf_eqI)
  subgoal by (simp add: add_carry_correct)
  subgoal
  proof -
    let ?t1 = "of_bool c1 + to_nat xs + to_nat ys"
    let ?t2 = "of_bool c2 + to_nat ys + to_nat zs"
    let ?t3 = "of_bool c1 + of_bool c2 + to_nat xs + to_nat ys + to_nat zs"

    have "length (add_carry c2 (add_carry c1 xs ys) zs) = max (max (max (max (length xs) (length ys)) (floorlog 2 ?t1)) (length zs))
     (floorlog 2 ?t3)"
      unfolding length_add_carry add_carry_correct eval_bool_is_of_bool
      by (intro arg_cong2[where f = max] refl arg_cong2[where f = floorlog]) simp
    also have "... = max (max (max (max (floorlog 2 ?t1) (floorlog 2 ?t3)) (length xs)) (length ys)) (length zs)"
      using max.commute max.assoc by presburger
    also have "... = max (max (max (floorlog 2 ?t3) (length xs)) (length ys)) (length zs)" (is "... = ?t4")
      by (intro arg_cong2[where f = max] refl max.absorb2 floorlog_mono) simp
    finally have 1: "length (add_carry c2 (add_carry c1 xs ys) zs) = ?t4" .

    have "length (add_carry c1 xs (add_carry c2 ys zs)) = max (max (length xs) (max (max (length ys) (length zs)) (floorlog 2 ?t2)))
     (floorlog 2 ?t3)"
      unfolding length_add_carry add_carry_correct eval_bool_is_of_bool
      by (intro arg_cong2[where f = max] refl arg_cong2[where f = floorlog]) simp
    also have "... = max (max (max (max (floorlog 2 ?t2) (floorlog 2 ?t3)) (length xs)) (length ys)) (length zs)"
      using max.commute max.assoc by presburger
    also have "... = max (max (max (floorlog 2 ?t3) (length xs)) (length ys)) (length zs)"
      by (intro arg_cong2[where f = max] refl max.absorb2 floorlog_mono) simp
    finally have 2: "length (add_carry c1 xs (add_carry c2 ys zs)) = ?t4" .

    show ?thesis unfolding 1 2 by (rule refl)
  qed
  done

lemma truncated_add_carry:
  assumes "truncated xs" "truncated ys"
  shows "truncated (add_carry c xs ys)"
proof -
  have "length (add_carry c xs ys) =
      max (max (length xs) (length ys)) (bitsize (of_bool c + to_nat xs + to_nat ys))"
    unfolding length_add_carry bitsize_is_floorlog by argo
  also have "... = max (max (bitsize (to_nat xs)) (bitsize (to_nat ys))) (bitsize (of_bool c + to_nat xs + to_nat ys))"
    using truncated_iff' assms by algebra
  also have "... = bitsize (of_bool c + to_nat xs + to_nat ys)"
    using bitsize_mono by simp
  also have "... = bitsize (to_nat (add_carry c xs ys))"
    by (simp add: add_carry_correct)
  finally show ?thesis unfolding truncated_iff' .
qed

subsubsection "Addition"

definition add_nat :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf" where
"add_nat x y = add_carry False x y"

corollary length_add_nat_lower: "length (add_nat xs ys) \<ge> max (length xs) (length ys)"
  unfolding add_nat_def by (simp only: length_add_carry_lower)

corollary length_add_nat_upper: "length (add_nat xs ys) \<le> max (length xs) (length ys) + 1"
  unfolding add_nat_def using length_add_carry_upper[of False xs ys] by simp

corollary add_nat_last_bit_True: "length (add_nat xs ys) = max (length xs) (length ys) + 1 \<Longrightarrow> \<exists>zs. add_nat xs ys = zs @ [True]"
  unfolding add_nat_def by (simp add: add_carry_last_bit_True)

lemma add_nat_correct: "to_nat (add_nat x y) = to_nat x + to_nat y"
  unfolding add_nat_def using add_carry_correct by simp

corollary add_nat_com: "add_nat xs ys = add_nat ys xs"
  unfolding add_nat_def by (simp add: add_carry_com)

corollary add_nat_assoc: "add_nat xs (add_nat ys zs) = add_nat (add_nat xs ys) zs"
  unfolding add_nat_def using add_carry_assoc by simp

corollary truncated_add_nat:
  assumes "truncated xs" "truncated ys"
  shows "truncated (add_nat xs ys)"
  unfolding add_nat_def
  by (intro truncated_add_carry assms)

subsection "Comparison and subtraction"

subsubsection "Comparison"

fun compare_nat_same_length_reversed :: "bool list \<Rightarrow> bool list \<Rightarrow> bool" where
"compare_nat_same_length_reversed [] [] = True"
| "compare_nat_same_length_reversed (False#xs) (False#ys) = compare_nat_same_length_reversed xs ys"
| "compare_nat_same_length_reversed (True#xs) (False#ys) = False"
| "compare_nat_same_length_reversed (False#xs) (True#ys) = True"
| "compare_nat_same_length_reversed (True#xs) (True#ys) = compare_nat_same_length_reversed xs ys"
| "compare_nat_same_length_reversed _ _ = undefined"

lemma compare_nat_same_length_reversed_correct:
  "length xs = length ys \<Longrightarrow> compare_nat_same_length_reversed xs ys \<longleftrightarrow> to_nat (rev xs) \<le> to_nat (rev ys)"
proof (induction xs ys rule: compare_nat_same_length_reversed.induct)
  case 1
  then show ?case by simp
next
  case (2 xs ys)
  have "to_nat (rev (False # xs)) = to_nat (rev xs)" "to_nat (rev (False # ys)) = to_nat (rev ys)"
    using to_nat_app by simp_all
  then have "to_nat (rev (False # xs)) \<le> to_nat (rev (False # ys)) \<longleftrightarrow> to_nat (rev xs) \<le> to_nat (rev ys)"
    by simp
  then show ?case using 2 by simp
next
  case (3 xs ys)
  have "to_nat (rev (True # xs)) = 2 ^ (length xs) + to_nat (rev xs)"
    using to_nat_app by simp
  also have "... > to_nat (rev ys)"
    using 3 to_nat_length_upper_bound[of "rev ys"] leI le_add_diff_inverse2 by fastforce
  also have "to_nat (rev ys) = to_nat (rev (False # ys))"
    using to_nat_app by simp
  finally have "to_nat (rev (True # xs)) > to_nat (rev (False # ys))" .
  thus ?case using 3 by simp
next
  case (4 xs ys)
  have "to_nat (rev (False # xs)) = to_nat (rev xs)"
    using to_nat_app by simp
  also have "... \<le> 2 ^ (length xs)"
    using to_nat_length_upper_bound[of "rev xs"] by simp
  also have "... \<le> to_nat (rev (True # ys))"
    using to_nat_app 4 by simp
  finally have "to_nat (rev (False # xs)) \<le> to_nat (rev (True # ys))" .
  thus ?case using 4 by simp
next
  case (5 xs ys)
  have "to_nat (rev (True # xs)) = 2 ^ (length xs) + to_nat (rev xs)" "to_nat (rev (True # ys)) = 2 ^ (length ys) + to_nat (rev ys)"
    using to_nat_app by simp_all
  then have "to_nat (rev (True # xs)) \<le> to_nat (rev (True # ys)) \<longleftrightarrow> to_nat (rev xs) \<le> to_nat (rev ys)"
    using 5 by simp
  then show ?case using 5 by simp
next
  case ("6_1" va)
  then show ?case by simp
next
  case ("6_2" v va)
  then show ?case by simp
next
  case ("6_3" v va)
  then show ?case by simp
next
  case ("6_4" va)
  then show ?case by simp
qed

fun compare_nat_same_length :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> bool" where
"compare_nat_same_length xs ys = compare_nat_same_length_reversed (rev xs) (rev ys)"

lemma compare_nat_same_length_correct:
  "length xs = length ys \<Longrightarrow> compare_nat_same_length xs ys = (to_nat xs \<le> to_nat ys)"
  using compare_nat_same_length_reversed_correct by simp

definition make_same_length :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf \<times> nat_lsbf" where
"make_same_length xs ys = (let n = max (length xs) (length ys) in ((fill n xs), (fill n ys)))"

lemma make_same_length_correct:
  assumes "(fill_xs, fill_ys) = make_same_length xs ys"
  shows "length fill_ys = length fill_xs"
  "length fill_xs = max (length xs) (length ys)"
  "to_nat fill_xs = to_nat xs"
  "to_nat fill_ys = to_nat ys"
  using assms by (simp_all add: Let_def make_same_length_def)

definition compare_nat :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> bool" where
"compare_nat xs ys = (let (fill_xs, fill_ys) = make_same_length xs ys in compare_nat_same_length fill_xs fill_ys)"

lemma compare_nat_correct: "compare_nat xs ys = (to_nat xs \<le> to_nat ys)"
proof -
  obtain fill_xs fill_ys where fills_def: "make_same_length xs ys = (fill_xs, fill_ys)"
    by fastforce
  then show ?thesis unfolding compare_nat_def Let_def
    using make_same_length_correct[OF fills_def[symmetric]]
    using compare_nat_same_length_reversed_correct[of "rev fill_xs" "rev fill_ys"]
    by simp
qed

subsubsection "Subtraction"

definition subtract_nat :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf" where
  "subtract_nat xs ys = (if compare_nat xs ys then [] else
    let (fill_xs, fill_ys) = make_same_length xs ys in
    butlast (add_carry True fill_xs (map Not fill_ys)))"

lemma add_complement: "add_nat xs (map Not xs) = replicate (length xs) True"
proof (induction xs)
  case Nil
  then show ?case unfolding add_nat_def by simp
next
  case (Cons a xs)
  have "add_nat (a # xs) (map Not (a # xs)) = True # (add_carry False xs (map Not xs))"
    unfolding add_nat_def by (cases a) simp_all
  also have "... = True # (replicate (length xs) True)"
    using Cons.IH by (simp add: add_nat_def)
  finally show ?case by simp
qed

lemma to_nat_complement: "to_nat (map Not xs) = 2 ^ (length xs) - 1 - to_nat xs"
  using add_complement[of xs] to_nat_replicate_true[of "length xs"] add_nat_correct[of xs "map Not xs"]
  by simp

lemma to_nat_butlast: "zs = xs @ [True] \<Longrightarrow> to_nat (butlast zs) = to_nat zs - 2 ^ length xs"
  using to_nat_app[of xs "[True]"] by simp

lemma inc_nat_true_prefix[simp]: "inc_nat (replicate n True @ [False] @ ys) = replicate n False @ [True] @ ys"
  by (induction n arbitrary: ys) simp_all

lemma length_inc_nat_aux: "zs = replicate n True @ [False] @ ys \<Longrightarrow> length (inc_nat zs) = length zs"
  using inc_nat_true_prefix[of n ys] by simp

lemma length_inc_nat_aux_2: "length (inc_nat (xs @ [False] @ ys)) = length (xs @ [False] @ ys)"
proof -
  define zs where "zs = xs @ [False] @ ys"
  with bit_strong_decomp_1[of zs False] obtain ys' n where "zs = replicate n True @ [False] @ ys'"
    by auto
  then show ?thesis using length_inc_nat_aux zs_def by simp
qed

lemma subtract_nat_aux: "to_nat (subtract_nat xs ys) = (to_nat xs) - (to_nat ys) \<and> length (subtract_nat xs ys) \<le> max (length xs) (length ys)"
proof (cases "compare_nat xs ys")
  case True
  then show ?thesis using compare_nat_correct unfolding subtract_nat_def by simp
next
  case False

  obtain fill_xs fill_ys where fills_def: "make_same_length xs ys = (fill_xs, fill_ys)"
    by fastforce
  note fills_props = make_same_length_correct[OF fills_def[symmetric]]
  define n where "n = max (length xs) (length ys)"
  then have "length fill_xs = n" "length fill_ys = n" using fills_props by auto

  from False have "to_nat fill_xs > to_nat fill_ys"
    using fills_props compare_nat_correct by simp
  then have "n > 0" using \<open>length fill_xs = n\<close> by auto

  let ?add = "add_carry True fill_xs (map Not fill_ys)"

  have subtract_nat_xs_ys: "subtract_nat xs ys = butlast ?add"
    unfolding subtract_nat_def using False fills_def by simp

  have "to_nat fill_ys \<le> 2 ^ n - 1" "to_nat fill_xs \<le> 2 ^ n - 1" "to_nat (map Not fill_ys) \<le> 2 ^ n - 1"
    subgoal using to_nat_length_upper_bound[of fill_ys] \<open>length fill_ys = n\<close> by argo
    subgoal using to_nat_length_upper_bound[of fill_xs] \<open>length fill_xs = n\<close> by argo
    subgoal using to_nat_length_upper_bound[of "map Not fill_ys"] \<open>length fill_ys = n\<close> by simp
    done
  then have "to_nat ?add \<le> (2 ^ n - 1) + (2 ^ n - 1) + 1" unfolding add_carry_correct by simp
  also have "... = 2 ^ (n + 1) - 2 + 1" by simp
  also have "... = 2 ^ (n + 1) - 1"
    using Nat.diff_diff_right[of 1 2 "2 ^ (n + 1)"] Nat.diff_add_assoc2[of 2 "2 ^ (n + 1)" 1]
    by simp
  finally have "to_nat ?add \<le> ..." .

  from \<open>to_nat fill_xs > to_nat fill_ys\<close> have "to_nat fill_xs \<ge> to_nat fill_ys + 1" by simp
  then have "to_nat fill_xs + 2 ^ n \<ge> 2 ^ n + to_nat fill_ys + 1" by simp
  then have "to_nat fill_xs + (2 ^ n - 1 - to_nat fill_ys) \<ge> 2 ^ n" by simp
  then have "to_nat fill_xs + to_nat (map Not fill_ys) \<ge> 2 ^ n"
    using to_nat_complement[of fill_ys] \<open>length fill_ys = n\<close> by simp
  then have "to_nat ?add \<ge> 2 ^ n"
    using add_carry_correct fills_props by simp
  then have "length ?add \<ge> n + 1"
    using to_nat_bound_to_length_bound by simp
  then have "length ?add = n + 1"
    using length_add_carry_upper[of True fill_xs "map Not fill_ys"] \<open>length fill_xs = n\<close> \<open>length fill_ys = n\<close>
    by simp

  then obtain zs where "?add = zs @ [True]" "length zs = n"
    using add_carry_last_bit_True[of True fill_xs "map Not fill_ys"] \<open>length fill_xs = n\<close> \<open>length fill_ys = n\<close>
    by auto
  then have 1: "to_nat (butlast ?add) = to_nat fill_xs + to_nat (map Not fill_ys) + 1 - 2 ^ n"
    unfolding to_nat_butlast[OF \<open>?add = zs @ [True]\<close>]
    using add_carry_correct by (metis Suc_eq_plus1 add.assoc eval_bool.simps(1) plus_1_eq_Suc)
  also have "... = to_nat fill_xs + (2 ^ n - 1 - to_nat fill_ys) + 1 - 2 ^ n"
    unfolding to_nat_complement[of fill_ys] \<open>length fill_ys = n\<close> by (rule refl)
  also have "... = to_nat fill_xs + (2 ^ n - 1) - to_nat fill_ys + 1 - 2 ^ n"
    using le_add_diff_inverse[OF \<open>to_nat fill_ys \<le> 2 ^ n - 1\<close>] by linarith
  also have "... = to_nat fill_xs - to_nat fill_ys + (2 ^ n - 1) - (2 ^ n - 1)"
    using \<open>to_nat fill_xs > to_nat fill_ys\<close> by simp
  also have "... = to_nat fill_xs - to_nat fill_ys" by simp
  finally have 2: "to_nat (subtract_nat xs ys) = to_nat xs - to_nat ys"
    unfolding subtract_nat_xs_ys fills_props .

  have 3: "length (butlast ?add) = n"
    using \<open>length ?add = n + 1\<close> by simp

  show ?thesis
    apply (intro conjI)
    subgoal by (fact 2)
    subgoal using 3 unfolding subtract_nat_xs_ys n_def[symmetric] by simp
    done
qed

corollary subtract_nat_correct: "to_nat (subtract_nat xs ys) = (to_nat xs) - (to_nat ys)"
  using subtract_nat_aux by simp

corollary length_subtract_nat_le: "length (subtract_nat xs ys) \<le> max (length xs) (length ys)"
  using subtract_nat_aux by simp

subsection "(Grid) Multiplication"

fun grid_mul_nat :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf" where
"grid_mul_nat [] _ = []"
| "grid_mul_nat (False#xs) y = False # (grid_mul_nat xs y)"
| "grid_mul_nat (True#xs) y = add_nat (False # (grid_mul_nat xs y)) y"

lemma grid_mul_nat_correct: "to_nat (grid_mul_nat x y) = to_nat x * to_nat y"
  by (induction x y rule: grid_mul_nat.induct) (simp_all add: add_nat_correct)

lemma length_grid_mul_nat: "length (grid_mul_nat xs ys) \<le> length xs + length ys"
proof (induction xs ys rule: grid_mul_nat.induct)
  case (1 uu)
  then show ?case by simp
next
  case (2 xs y)
  then show ?case by simp
next
  case (3 xs y)
  show ?case
  proof (rule ccontr)
    assume "\<not> length (grid_mul_nat (True # xs) y) \<le> length (True # xs) + length y"
    then have l: "length (grid_mul_nat (True # xs) y) = length xs + length y + 2"
      using length_add_nat_upper[of "False # grid_mul_nat xs y" y] 3 by simp

    then have "length (add_nat (False # grid_mul_nat xs y) y) = max (length (False # grid_mul_nat xs y)) (length y) + 1"
      using length_add_nat_upper[of "False # grid_mul_nat xs y" y] 3 by simp
    then obtain as where "add_nat (False # grid_mul_nat xs y) y = as @ [True]"
      using add_nat_last_bit_True[of "False # grid_mul_nat xs y" y] by auto
    then have as_def: "grid_mul_nat (True # xs) y = as @ [True]" by simp
    then have length_as: "length as = length xs + length y + 1" using l by simp

    from as_def have m: "to_nat (True # xs) * to_nat y = to_nat (as @ [True])"
      using grid_mul_nat_correct by metis
    also have "to_nat (as @ [True]) \<ge> 2 ^ length as"
      using to_nat_length_lower_bound by simp
    also have "2 ^ length as = 2 ^ (length xs + length y + 1)" using length_as by simp
    also have "to_nat (True # xs) * to_nat y < 2 ^ (length xs + 1) * 2 ^ length y"
      apply (intro mult_less_le_imp_less)
      subgoal using to_nat_length_upper_bound[of "True # xs"] by simp
      subgoal using to_nat_length_upper_bound[of y] by simp
      subgoal by simp
      subgoal
        apply (rule ccontr)
        using m to_nat_length_lower_bound[of as] by simp
      done
    finally show "False" by (simp add: power_add)
  qed
qed

subsection "Syntax bundles"


abbreviation "shift_right_flip xs n \<equiv> shift_right n xs"
bundle nat_lsbf_syntax
begin
  notation add_nat (infixl "+\<^sub>n" 65)
  notation compare_nat (infixl "\<le>\<^sub>n" 50)
  notation subtract_nat (infixl "-\<^sub>n" 65)
  notation grid_mul_nat (infixl "*\<^sub>n" 70)
  notation shift_right_flip (infixl ">>\<^sub>n" 55)
end

bundle no_nat_lsbf_syntax
begin
  no_notation add_nat (infixl "+\<^sub>n" 65)
  no_notation compare_nat (infixl "\<le>\<^sub>n" 50)
  no_notation subtract_nat (infixl "-\<^sub>n" 65)
  no_notation grid_mul_nat (infixl "*\<^sub>n" 70)
  no_notation shift_right_flip (infixl ">>\<^sub>n" 55)
end

unbundle nat_lsbf_syntax

end