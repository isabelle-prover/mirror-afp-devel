section \<open>Arithmetic\label{s:tm-arithmetic}\<close>

theory Arithmetic
  imports Memorizing
begin

text \<open>
In this section we define a representation of natural numbers and some reusable
Turing machines for elementary arithmetical operations.  All Turing machines
implementing the operations assume that the tape heads on the tapes containing
the operands and the result(s) contain one natural number each.  In programming
language terms we could say that such a tape corresponds to a variable of type
@{typ nat}. Furthermore, initially the tape heads are on cell number~1, that is,
one to the right of the start symbol. The Turing machines will halt with the
tape heads in that position as well. In that way operations can be concatenated
seamlessly.
\<close>

subsection \<open>Binary numbers\label{s:tm-arithmetic-binary}\<close>

text \<open>
We represent binary numbers as sequences of the symbols \textbf{0} and
\textbf{1}.  Slightly unusually the least significant bit will be on the left.
While every sequence over these symbols represents a natural number, the
representation is not unique due to leading (or rather, trailing) zeros.  The
\emph{canonical} representation is unique and has no trailing zeros, not even for
the number zero, which is thus represented by the empty symbol sequence.  As a
side effect empty tapes can be thought of as being initialized with zero.

Naturally the binary digits 0 and 1 are represented by the symbols \textbf{0}
and \textbf{1}, respectively. For example, the decimal number $14$,
conventionally written $1100_2$ in binary, is represented by the symbol sequence
\textbf{0011}. The next two functions map between symbols and binary digits:
\<close>

abbreviation (input) tosym :: "nat \<Rightarrow> symbol" where
  "tosym z \<equiv> z + 2"

abbreviation todigit :: "symbol \<Rightarrow> nat" where
  "todigit z \<equiv> if z = \<one> then 1 else 0"

text \<open>
The numerical value of a symbol sequence:
\<close>

definition num :: "symbol list \<Rightarrow> nat" where
  "num xs \<equiv> \<Sum>i\<leftarrow>[0..<length xs]. todigit (xs ! i) * 2 ^ i"

text \<open>
The $i$-th digit of a symbol sequence, where digits out of bounds are considered
trailing zeros:
\<close>

definition digit :: "symbol list \<Rightarrow> nat \<Rightarrow> nat" where
  "digit xs i \<equiv> if i < length xs then xs ! i else 0"

text \<open>
Some properties of $num$:
\<close>

lemma num_ge_pow:
  assumes "i < length xs" and "xs ! i = \<one>"
  shows "num xs \<ge> 2 ^ i"
proof -
  let ?ys = "map (\<lambda>i. todigit (xs ! i) * 2 ^ i) [0..<length xs]"
  have "?ys ! i = 2 ^ i"
    using assms by simp
  moreover have "i < length ?ys"
    using assms(1) by simp
  ultimately show "num xs \<ge> 2 ^ i"
    unfolding num_def using elem_le_sum_list by (metis (no_types, lifting))
qed

lemma num_trailing_zero:
  assumes "todigit z = 0"
  shows "num xs = num (xs @ [z])"
proof -
  let ?xs = "xs @ [z]"
  let ?ys = "map (\<lambda>i. todigit (?xs ! i) * 2 ^ i) [0..<length ?xs]"
  have *: "?ys = map (\<lambda>i. todigit (xs ! i) * 2 ^ i) [0..<length xs] @ [0]"
    using assms by (simp add: nth_append)
  have "num ?xs = sum_list ?ys"
    using num_def by simp
  then have "num ?xs = sum_list (map (\<lambda>i. todigit (xs ! i) * 2 ^ i) [0..<length xs] @ [0])"
    using * by metis
  then have "num ?xs = sum_list (map (\<lambda>i. todigit (xs ! i) * 2 ^ i) [0..<length xs])"
    by simp
  then show ?thesis
    using num_def by simp
qed

lemma num_Cons: "num (x # xs) = todigit x + 2 * num xs"
proof -
  have "[0..<length (x # xs)] = [0..<1] @ [1..<length (x # xs)]"
    by (metis length_Cons less_imp_le_nat plus_1_eq_Suc upt_add_eq_append zero_less_one)
  then have 1: "(map (\<lambda>i. todigit ((x # xs) ! i) * 2 ^ i) [0..<length (x # xs)]) =
    (map (\<lambda>i. todigit ((x # xs) ! i) * 2 ^ i) [0..<1]) @
    (map (\<lambda>i. todigit ((x # xs) ! i) * 2 ^ i) [1..<length (x # xs)])"
    by simp

  have "map (\<lambda>i. f i) [1..<Suc m] = map (\<lambda>i. f (Suc i)) [0..<m]" for f :: "nat \<Rightarrow> nat" and m
  proof (rule nth_equalityI)
    show "length (map f [1..<Suc m]) = length (map (\<lambda>i. f (Suc i)) [0..<m])"
      by simp
    then show "\<And>i. i < length (map f [1..<Suc m]) \<Longrightarrow>
        map f [1..<Suc m] ! i = map (\<lambda>i. f (Suc i)) [0..<m] ! i"
      by (metis add.left_neutral length_map length_upt nth_map_upt plus_1_eq_Suc)
  qed
  then have 2: "(\<Sum>i\<leftarrow>[1..<Suc m]. f i) = (\<Sum>i\<leftarrow>[0..<m]. f (Suc i))"
      for f :: "nat \<Rightarrow> nat" and m
    by simp

  have "num (x # xs) = (\<Sum>i\<leftarrow>[0..<length (x # xs)]. todigit ((x # xs) ! i) * 2 ^ i)"
    using num_def by simp
  also have "... = (\<Sum>i\<leftarrow>[0..<1]. (todigit ((x # xs) ! i) * 2 ^ i)) +
      (\<Sum>i\<leftarrow>[1..<length (x # xs)]. todigit ((x # xs) ! i) * 2 ^ i)"
    using 1 by simp
  also have "... = todigit x + (\<Sum>i\<leftarrow>[1..<length (x # xs)]. todigit ((x # xs) ! i) * 2 ^ i)"
    by simp
  also have "... = todigit x + (\<Sum>i\<leftarrow>[0..<length (x # xs) - 1]. todigit ((x # xs) ! (Suc i)) * 2 ^ (Suc i))"
    using 2 by simp
  also have "... = todigit x + (\<Sum>i\<leftarrow>[0..<length xs]. todigit (xs ! i) * 2 ^ (Suc i))"
    by simp
  also have "... = todigit x + (\<Sum>i\<leftarrow>[0..<length xs]. todigit (xs ! i) * (2 * 2 ^ i))"
    by simp
  also have "... = todigit x + (\<Sum>i\<leftarrow>[0..<length xs]. (todigit (xs ! i) * 2 * 2 ^ i))"
    by (simp add: mult.assoc)
  also have "... = todigit x + (\<Sum>i\<leftarrow>[0..<length xs]. (2 * (todigit (xs ! i) * 2 ^ i)))"
    by (metis (mono_tags, opaque_lifting) ab_semigroup_mult_class.mult_ac(1) mult.commute)
  also have "... = todigit x + 2 * (\<Sum>i\<leftarrow>[0..<length xs]. (todigit (xs ! i) * 2 ^ i))"
    using sum_list_const_mult by fastforce
  also have "... = todigit x + 2 * num xs"
    using num_def by simp
  finally show ?thesis .
qed

lemma num_append: "num (xs @ ys) = num xs + 2 ^ length xs * num ys"
proof (induction "length xs" arbitrary: xs)
  case 0
  then show ?case
    using num_def by simp
next
  case (Suc n)
  then have xs: "xs = hd xs # tl xs"
    by (metis hd_Cons_tl list.size(3) nat.simps(3))
  then have "xs @ ys = hd xs # (tl xs @ ys)"
    by simp
  then have "num (xs @ ys) = todigit (hd xs) + 2 * num (tl xs @ ys)"
    using num_Cons by presburger
  also have "... = todigit (hd xs) + 2 * (num (tl xs) + 2 ^ length (tl xs) * num ys)"
    using Suc by simp
  also have "... = todigit (hd xs) + 2 * num (tl xs) + 2 ^ Suc (length (tl xs)) * num ys"
    by simp
  also have "... = num xs + 2 ^ Suc (length (tl xs)) * num ys"
    using num_Cons xs by metis
  also have "... = num xs + 2 ^ length xs * num ys"
    using xs by (metis length_Cons)
  finally show ?case .
qed

lemma num_drop: "num (drop t zs) = todigit (digit zs t) + 2 * num (drop (Suc t) zs)"
proof (cases "t < length zs")
  case True
  then have "drop t zs = zs ! t # drop (Suc t) zs"
    by (simp add: Cons_nth_drop_Suc)
  then have "num (drop t zs) = todigit (zs ! t) + 2 * num (drop (Suc t) zs)"
    using num_Cons by simp
  then show ?thesis
    using digit_def True by simp
next
  case False
  then show ?thesis
    using digit_def num_def by simp
qed

lemma num_take_Suc: "num (take (Suc t) zs) = num (take t zs) + 2 ^ t * todigit (digit zs t)"
proof (cases "t < length zs")
  case True
  let ?zs = "take (Suc t) zs"
  have 1: "?zs ! i = zs ! i" if "i < Suc t" for i
    using that by simp
  have 2: "take t zs ! i = zs ! i" if "i < t" for i
    using that by simp
  have "num ?zs = (\<Sum>i\<leftarrow>[0..<length ?zs]. todigit (?zs ! i) * 2 ^ i)"
    using num_def by simp
  also have "... = (\<Sum>i\<leftarrow>[0..<Suc t]. todigit (?zs ! i) * 2 ^ i)"
    by (simp add: Suc_leI True min_absorb2)
  also have "... = (\<Sum>i\<leftarrow>[0..<Suc t]. todigit (zs ! i) * 2 ^ i)"
    using 1 by (smt (verit, best) atLeastLessThan_iff map_eq_conv set_upt)
  also have "... = (\<Sum>i\<leftarrow>[0..<t]. todigit (zs ! i) * 2 ^ i) + todigit (zs ! t) * 2 ^ t"
    by simp
  also have "... = (\<Sum>i\<leftarrow>[0..<t]. todigit (take t zs ! i) * 2 ^ i) + todigit (zs ! t) * 2 ^ t"
    using 2 by (metis (no_types, lifting) atLeastLessThan_iff map_eq_conv set_upt)
  also have "... = num (take t zs) + todigit (zs ! t) * 2 ^ t"
    using num_def True by simp
  also have "... = num (take t zs) + todigit (digit zs t) * 2 ^ t"
    using digit_def True by simp
  finally show ?thesis
    by simp
next
  case False
  then show ?thesis
    using digit_def by simp
qed

text \<open>
A symbol sequence is a canonical representation of a natural number if the
sequence contains only the symbols \textbf{0} and \textbf{1} and is either empty
or ends in \textbf{1}.
\<close>

definition canonical :: "symbol list \<Rightarrow> bool" where
  "canonical xs \<equiv> bit_symbols xs \<and> (xs = [] \<or> last xs = \<one>)"

lemma canonical_Cons:
  assumes "canonical xs" and "xs \<noteq> []" and "x = \<zero> \<or> x = \<one>"
  shows "canonical (x # xs)"
  using assms canonical_def less_Suc_eq_0_disj by auto

lemma canonical_Cons_3: "canonical xs \<Longrightarrow> canonical (\<one> # xs)"
  using canonical_def less_Suc_eq_0_disj by auto

lemma canonical_tl: "canonical (x # xs) \<Longrightarrow> canonical xs"
  using canonical_def by fastforce

lemma prepend_2_even: "x = \<zero> \<Longrightarrow> even (num (x # xs))"
  using num_Cons by simp

lemma prepend_3_odd: "x = \<one> \<Longrightarrow> odd (num (x # xs))"
  using num_Cons by simp

text \<open>
Every number has exactly one canonical representation.
\<close>

lemma canonical_ex1:
  fixes n :: nat
  shows "\<exists>!xs. num xs = n \<and> canonical xs"
proof (induction n rule: nat_less_induct)
  case IH: (1 n)
  show ?case
  proof (cases "n = 0")
    case True
    have "num [] = 0"
      using num_def by simp
    moreover have "canonical xs \<Longrightarrow> num xs = 0 \<Longrightarrow> xs = []" for xs
    proof (rule ccontr)
      fix xs
      assume "canonical xs" "num xs = 0" "xs \<noteq> []"
      then have "length xs > 0" "last xs = \<one>"
        using canonical_def by simp_all
      then have "xs ! (length xs - 1) = \<one>"
        by (metis Suc_diff_1 last_length)
      then have "num xs \<ge> 2 ^ (length xs - 1)"
        using num_ge_pow by (meson \<open>0 < length xs\<close> diff_less zero_less_one)
      then have "num xs > 0"
        by (meson dual_order.strict_trans1 le0 le_less_trans less_exp)
      then show False
        using \<open>num xs = 0\<close> by auto
    qed
    ultimately show ?thesis
      using IH True canonical_def by (metis less_nat_zero_code list.size(3))
  next
    case False
    then have gt: "n > 0"
      by simp
    define m where "m = n div 2"
    define r where "r = n mod 2"
    have n: "n = 2 * m + r"
      using m_def r_def by simp
    have "m < n"
      using gt m_def by simp
    then obtain xs where "num xs = m" "canonical xs"
      using IH by auto
    then have "num (tosym r # xs) = n"
        (is "num ?xs = n")
      using num_Cons n add.commute r_def by simp
    have "canonical ?xs"
    proof (cases "r = 0")
      case True
      then have "m > 0"
        using gt n by simp
      then have "xs \<noteq> []"
        using `num xs = m` num_def by auto
      then show ?thesis
        using canonical_Cons[of xs] `canonical xs` r_def True by simp
    next
      case False
      then show ?thesis
        using `canonical xs` canonical_Cons_3 r_def
        by (metis One_nat_def not_mod_2_eq_1_eq_0 numeral_3_eq_3 one_add_one plus_1_eq_Suc)
    qed
    moreover have "xs1 = xs2" if "canonical xs1" "num xs1 = n" "canonical xs2" "num xs2 = n" for xs1 xs2
    proof -
      have "xs1 \<noteq> []"
        using gt that(2) num_def by auto
      then obtain x1 ys1 where 1: "xs1 = x1 # ys1"
        by (meson neq_Nil_conv)
      then have x1: "x1 = \<zero> \<or> x1 = \<one>"
        using canonical_def that(1) by auto
      have "xs2 \<noteq> []"
        using gt that(4) num_def by auto
      then obtain x2 ys2 where 2: "xs2 = x2 # ys2"
        by (meson neq_Nil_conv)
      then have x2: "x2 = \<zero> \<or> x2 = \<one>"
        using canonical_def that(3) by auto
      have "x1 = x2"
        using prepend_2_even prepend_3_odd that 1 2 x1 x2 by metis
      moreover have "n = todigit x1 + 2 * num ys1"
        using that(2) num_Cons 1 by simp
      moreover have "n = todigit x2 + 2 * num ys2"
        using that(4) num_Cons 2 by simp
      ultimately have "num ys1 = num ys2"
        by simp
      moreover have "num ys1 < n"
        using that(2) num_Cons 1 gt by simp
      moreover have "num ys2 < n"
        using that(4) num_Cons 2 gt by simp
      ultimately have "ys1 = ys2"
        using IH 1 2 that(1,3) by (metis canonical_tl)
      then show "xs1 = xs2"
        using `x1 = x2` 1 2 by simp
    qed
    ultimately show ?thesis
      using \<open>num (tosym r # xs) = n\<close> by auto
  qed
qed

text \<open>
The canonical representation of a natural number as symbol sequence:
\<close>

definition canrepr :: "nat \<Rightarrow> symbol list" where
  "canrepr n \<equiv> THE xs. num xs = n \<and> canonical xs"

lemma canrepr_inj: "inj canrepr"
  using canrepr_def canonical_ex1 by (smt (verit, del_insts) inj_def the_equality)

lemma canonical_canrepr: "canonical (canrepr n)"
  using theI'[OF canonical_ex1] canrepr_def by simp

lemma canrepr: "num (canrepr n) = n"
  using theI'[OF canonical_ex1] canrepr_def by simp

lemma bit_symbols_canrepr: "bit_symbols (canrepr n)"
  using canonical_canrepr canonical_def by simp

lemma proper_symbols_canrepr: "proper_symbols (canrepr n)"
  using bit_symbols_canrepr by fastforce

lemma canreprI: "num xs = n \<Longrightarrow> canonical xs \<Longrightarrow> canrepr n = xs"
  using canrepr canonical_canrepr canonical_ex1 by blast

lemma canrepr_0: "canrepr 0 = []"
  using num_def canonical_def by (intro canreprI) simp_all

lemma canrepr_1: "canrepr 1 = [\<one>]"
  using num_def canonical_def by (intro canreprI) simp_all

text \<open>
The length of the canonical representation of a number $n$:
\<close>

abbreviation nlength :: "nat \<Rightarrow> nat" where
  "nlength n \<equiv> length (canrepr n)"

lemma nlength_0: "nlength n = 0 \<longleftrightarrow> n = 0"
  by (metis canrepr canrepr_0 length_0_conv)

corollary nlength_0_simp [simp]: "nlength 0 = 0"
  using nlength_0 by simp

lemma num_replicate2_eq_pow: "num (replicate j \<zero> @ [\<one>]) = 2 ^ j"
proof (induction j)
  case 0
  then show ?case
    using num_def by simp
next
  case (Suc j)
  then show ?case
    using num_Cons by simp
qed

lemma num_replicate3_eq_pow_minus_1: "num (replicate j \<one>) = 2 ^ j - 1"
proof (induction j)
  case 0
  then show ?case
    using num_def by simp
next
  case (Suc j)
  then have "num (replicate (Suc j) \<one>) = num (\<one> # replicate j \<one>)"
    by simp
  also have "... = 1 + 2 * (2 ^ j - 1)"
    using Suc num_Cons by simp
  also have "... = 1 + 2 * 2 ^ j - 2"
    by (metis Nat.add_diff_assoc diff_mult_distrib2 mult_2 mult_le_mono2 nat_1_add_1 one_le_numeral one_le_power)
  also have "... = 2 ^ Suc j - 1"
    by simp
  finally show ?case .
qed

lemma nlength_pow2: "nlength (2 ^ j) = Suc j"
proof -
  define xs :: "nat list" where "xs = replicate j 2 @ [3]"
  then have "length xs = Suc j"
    by simp
  moreover have "num xs = 2 ^ j"
    using num_replicate2_eq_pow xs_def by simp
  moreover have "canonical xs"
    using xs_def bit_symbols_append canonical_def by simp
  ultimately show ?thesis
    using canreprI by blast
qed

corollary nlength_1_simp [simp]: "nlength 1 = 1"
  using nlength_pow2[of 0] by simp

corollary nlength_2: "nlength 2 = 2"
  using nlength_pow2[of 1] by simp

lemma nlength_pow_minus_1: "nlength (2 ^ j - 1) = j"
proof -
  define xs :: "nat list" where "xs = replicate j \<one>"
  then have "length xs = j"
    by simp
  moreover have "num xs = 2 ^ j - 1"
    using num_replicate3_eq_pow_minus_1 xs_def by simp
  moreover have "canonical xs"
  proof -
    have "bit_symbols xs"
      using xs_def by simp
    moreover have "last xs = 3 \<or> xs = []"
      by (cases "j = 0") (simp_all add: xs_def)
    ultimately show ?thesis
      using canonical_def by auto
  qed
  ultimately show ?thesis
    using canreprI by metis
qed

corollary nlength_3: "nlength 3 = 2"
  using nlength_pow_minus_1[of 2] by simp

text \<open>
When handling natural numbers, Turing machines will usually have tape contents
of the following form:
\<close>

abbreviation ncontents :: "nat \<Rightarrow> (nat \<Rightarrow> symbol)" ("\<lfloor>_\<rfloor>\<^sub>N") where
  "\<lfloor>n\<rfloor>\<^sub>N \<equiv> \<lfloor>canrepr n\<rfloor>"

lemma ncontents_0: "\<lfloor>0\<rfloor>\<^sub>N = \<lfloor>[]\<rfloor>"
  by (simp add: canrepr_0)

lemma clean_tape_ncontents: "clean_tape (\<lfloor>x\<rfloor>\<^sub>N, i)"
  using bit_symbols_canrepr clean_contents_proper by fastforce

lemma ncontents_1_blank_iff_zero: "\<lfloor>n\<rfloor>\<^sub>N 1 = \<box> \<longleftrightarrow> n = 0"
  using bit_symbols_canrepr contents_def nlength_0
  by (metis contents_outofbounds diff_is_0_eq' leI length_0_conv length_greater_0_conv less_one zero_neq_numeral)

text \<open>
Every bit symbol sequence can be turned into a canonical representation of some
number by stripping trailing zeros. The length of the prefix without trailing
zeros is given by the next function:
\<close>

definition canlen :: "symbol list \<Rightarrow> nat" where
  "canlen zs \<equiv> LEAST m. \<forall>i<length zs. i \<ge> m \<longrightarrow> zs ! i = \<zero>"

lemma canlen_at_ge: "\<forall>i<length zs. i \<ge> canlen zs \<longrightarrow> zs ! i = \<zero>"
proof -
  let ?P = "\<lambda>m. \<forall>i<length zs. i \<ge> m \<longrightarrow> zs ! i = \<zero>"
  have "?P (length zs)"
    by simp
  then show ?thesis
    unfolding canlen_def using LeastI[of ?P "length zs"] by fast
qed

lemma canlen_eqI:
  assumes "\<forall>i<length zs. i \<ge> m \<longrightarrow> zs ! i = \<zero>"
    and "\<And>y. \<forall>i<length zs. i \<ge> y \<longrightarrow> zs ! i = \<zero> \<Longrightarrow> m \<le> y"
  shows "canlen zs = m"
  unfolding canlen_def using assms Least_equality[of _ m, OF _ assms(2)] by presburger

lemma canlen_le_length: "canlen zs \<le> length zs"
proof -
  let ?P = "\<lambda>m. \<forall>i<length zs. i \<ge> m \<longrightarrow> zs ! i = \<zero>"
  have "?P (length zs)"
    by simp
  then show ?thesis
    unfolding canlen_def using Least_le[of _ "length zs"] by simp
qed

lemma canlen_le:
  assumes "\<forall>i<length zs. i \<ge> m \<longrightarrow> zs ! i = \<zero>"
  shows "m \<ge> canlen zs"
  unfolding canlen_def using Least_le[of _ m] assms by simp

lemma canlen_one:
  assumes "bit_symbols zs" and "canlen zs > 0"
  shows "zs ! (canlen zs - 1) = \<one>"
proof (rule ccontr)
  assume "zs ! (canlen zs - 1) \<noteq> \<one>"
  then have "zs ! (canlen zs - 1) = \<zero>"
    using assms canlen_le_length
    by (metis One_nat_def Suc_pred lessI less_le_trans)
  then have "\<forall>i<length zs. i \<ge> canlen zs - 1 \<longrightarrow> zs ! i = 2"
    using canlen_at_ge assms(2) by (metis One_nat_def Suc_leI Suc_pred le_eq_less_or_eq)
  then have "canlen zs - 1 \<ge> canlen zs"
    using canlen_le by auto
  then show False
    using assms(2) by simp
qed

lemma canonical_take_canlen:
  assumes "bit_symbols zs"
  shows "canonical (take (canlen zs) zs)"
proof (cases "canlen zs = 0")
  case True
  then show ?thesis
    using canonical_def by simp
next
  case False
  then show ?thesis
    using canonical_def assms canlen_le_length canlen_one
    by (smt (verit, ccfv_SIG) One_nat_def Suc_pred append_take_drop_id diff_less last_length
      length_take less_le_trans min_absorb2 neq0_conv nth_append zero_less_one)
qed

lemma num_take_canlen_eq: "num (take (canlen zs) zs) = num zs"
proof (induction "length zs - canlen zs" arbitrary: zs)
  case 0
  then show ?case
    by simp
next
  case (Suc x)
  let ?m = "canlen zs"
  have *: "\<forall>i<length zs. i \<ge> ?m \<longrightarrow> zs ! i = \<zero>"
    using canlen_at_ge by auto
  have "canlen zs < length zs"
    using Suc by simp
  then have "zs ! (length zs - 1) = \<zero>"
    using Suc canlen_at_ge canlen_le_length
    by (metis One_nat_def Suc_pred diff_less le_Suc_eq less_nat_zero_code nat_neq_iff zero_less_one)
  then have "todigit (zs ! (length zs - 1)) = 0"
    by simp
  moreover have ys: "zs = take (length zs - 1) zs @ [zs ! (length zs - 1)]"
      (is "zs = ?ys @ _")
    by (metis Suc_diff_1 \<open>canlen zs < length zs\<close> append_butlast_last_id butlast_conv_take
      gr_implies_not0 last_length length_0_conv length_greater_0_conv)
  ultimately have "num ?ys = num zs"
    using num_trailing_zero by metis
  have canlen_ys: "canlen ?ys = canlen zs"
  proof (rule canlen_eqI)
    show "\<forall>i<length ?ys. canlen zs \<le> i \<longrightarrow> ?ys ! i = \<zero>"
      by (simp add: canlen_at_ge)
    show "\<And>y. \<forall>i<length ?ys. y \<le> i \<longrightarrow> ?ys ! i = \<zero> \<Longrightarrow> canlen zs \<le> y"
      using * Suc.hyps(2) canlen_le
      by (smt (verit, del_insts) One_nat_def Suc_pred append_take_drop_id diff_le_self length_take
        length_upt less_Suc_eq less_nat_zero_code list.size(3) min_absorb2 nth_append upt.simps(2) zero_less_Suc)
  qed
  then have "length ?ys - canlen ?ys = x"
    using ys Suc.hyps(2) by (metis butlast_snoc diff_Suc_1 diff_commute length_butlast)
  then have "num (take (canlen ?ys) ?ys) = num ?ys"
    using Suc by blast
  then have "num (take (canlen zs) ?ys) = num ?ys"
    using canlen_ys by simp
  then have "num (take (canlen zs) zs) = num ?ys"
    by (metis \<open>canlen zs < length zs\<close> butlast_snoc take_butlast ys)
  then show ?case
    using \<open>num ?ys = num zs\<close> by presburger
qed

lemma canrepr_take_canlen:
  assumes "num zs = n" and "bit_symbols zs"
  shows "canrepr n = take (canlen zs) zs"
  using assms canrepr canonical_canrepr canonical_ex1 canonical_take_canlen num_take_canlen_eq
  by blast

lemma length_canrepr_canlen:
  assumes "num zs = n" and "bit_symbols zs"
  shows "nlength n = canlen zs"
  using canrepr_take_canlen assms canlen_le_length by (metis length_take min_absorb2)

lemma nlength_ge_pow:
  assumes "nlength n = Suc j"
  shows "n \<ge> 2 ^ j"
proof -
  let ?xs = "canrepr n"
  have "?xs ! (length ?xs - 1) = \<one>"
    using canonical_def assms canonical_canrepr
    by (metis Suc_neq_Zero diff_Suc_1 last_length length_0_conv)
  moreover have "(\<Sum>i\<leftarrow>[0..<length ?xs]. todigit (?xs ! i) * 2 ^ i) \<ge>
      todigit (?xs ! (length ?xs - 1)) * 2 ^ (length ?xs - 1)"
    using assms by simp
  ultimately have "num ?xs \<ge> 2 ^ (length ?xs - 1)"
    using num_def by simp
  moreover have "num ?xs = n"
    using canrepr by simp
  ultimately show ?thesis
    using assms by simp
qed

lemma nlength_less_pow: "n < 2 ^ (nlength n)"
proof (induction "nlength n" arbitrary: n)
  case 0
  then show ?case
    by (metis canrepr canrepr_0 length_0_conv nat_zero_less_power_iff)
next
  case (Suc j)
  let ?xs = "canrepr n"
  have lenxs: "length ?xs = Suc j"
    using Suc by simp
  have hdtl: "?xs = hd ?xs # tl ?xs"
    using Suc by (metis hd_Cons_tl list.size(3) nat.simps(3))
  have len: "length (tl ?xs) = j"
    using Suc by simp
  have can: "canonical (tl ?xs)"
    using hdtl canonical_canrepr canonical_tl by metis
  define n' where "n' = num (tl ?xs)"
  then have "nlength n' = j"
    using len can canreprI by simp
  then have n'_less: "n' < 2 ^ j"
    using Suc by auto
  have "num ?xs = todigit (hd ?xs) + 2 * num (tl ?xs)"
    by (metis hdtl num_Cons)
  then have "n = todigit (hd ?xs) + 2 * num (tl ?xs)"
    using canrepr by simp
  also have "... \<le> 1 + 2 * num (tl ?xs)"
    by simp
  also have "... = 1 + 2 * n'"
    using n'_def by simp
  also have "... \<le> 1 + 2 * (2 ^ j - 1)"
    using n'_less by simp
  also have "... = 2 ^ (Suc j) - 1"
    by (metis (no_types, lifting) add_Suc_right le_add_diff_inverse mult_2 one_le_numeral
      one_le_power plus_1_eq_Suc sum.op_ivl_Suc sum_power2 zero_order(3))
  also have "... < 2 ^ (Suc j)"
    by simp
  also have "... = 2 ^ (nlength n)"
    using lenxs by simp
  finally show ?case .
qed

lemma pow_nlength:
  assumes "2 ^ j \<le> n" and "n < 2 ^ (Suc j)"
  shows "nlength n = Suc j"
proof (rule ccontr)
  assume "nlength n \<noteq> Suc j"
  then have "nlength n < Suc j \<or> nlength n > Suc j"
    by auto
  then show False
  proof
    assume "nlength n < Suc j"
    then have "nlength n \<le> j"
      by simp
    moreover have "n < 2 ^ (nlength n)"
      using nlength_less_pow by simp
    ultimately have "n < 2 ^ j"
      by (metis le_less_trans nat_power_less_imp_less not_less numeral_2_eq_2 zero_less_Suc)
    then show False
      using assms(1) by simp
  next
    assume *: "nlength n > Suc j"
    then have "n \<ge> 2 ^ (nlength n - 1)"
      using nlength_ge_pow by simp
    moreover have "nlength n - 1 \<ge> Suc j"
      using * by simp
    ultimately have "n \<ge> 2 ^ (Suc j)"
      by (metis One_nat_def le_less_trans less_2_cases_iff linorder_not_less power_less_imp_less_exp)
    then show False
      using assms(2) by simp
  qed
qed

lemma nlength_le_n: "nlength n \<le> n"
proof (cases "n = 0")
  case True
  then show ?thesis
    using canrepr_0 by simp
next
  case False
  then have "nlength n > 0"
    using nlength_0 by simp
  moreover from this have "n \<ge> 2 ^ (nlength n - 1)"
    using nlength_0 nlength_ge_pow by auto
  ultimately show ?thesis
    using nlength_ge_pow by (metis Suc_diff_1 Suc_leI dual_order.trans less_exp)
qed

lemma nlength_Suc_le: "nlength n \<le> nlength (Suc n)"
proof (cases "n = 0")
  case True
  then show ?thesis
    by (simp add: canrepr_0)
next
  case False
  then obtain j where j: "nlength n = Suc j"
    by (metis canrepr canrepr_0 gr0_implies_Suc length_greater_0_conv)
  then have "n \<ge> 2 ^ j"
    using nlength_ge_pow by simp
  show ?thesis
  proof (cases "Suc n \<ge> 2 ^ (Suc j)")
    case True
    have "n < 2 ^ (Suc j)"
      using j nlength_less_pow by metis
    then have "Suc n < 2 ^ (Suc (Suc j))"
      by simp
    then have "nlength (Suc n) = Suc (Suc j)"
      using True pow_nlength by simp
    then show ?thesis
      using j by simp
  next
    case False
    then have "Suc n < 2 ^ (Suc j)"
      by simp
    then have "nlength (Suc n) = Suc j"
      using `n \<ge> 2 ^ j` pow_nlength by simp
    then show ?thesis
      using j by simp
  qed
qed

lemma nlength_mono:
  assumes "n1 \<le> n2"
  shows "nlength n1 \<le> nlength n2"
proof -
  have "nlength n \<le> nlength (n + d)" for n d
  proof (induction d)
    case 0
    then show ?case
      by simp
  next
    case (Suc d)
    then show ?case
      using nlength_Suc_le by (metis nat_arith.suc1 order_trans)
  qed
  then show ?thesis
    using assms by (metis le_add_diff_inverse)
qed

lemma nlength_even_le: "n > 0 \<Longrightarrow> nlength (2 * n) = Suc (nlength n)"
proof -
  assume "n > 0"
  then have "nlength n > 0"
    by (metis canrepr canrepr_0 length_greater_0_conv less_numeral_extra(3))
  then have "n \<ge> 2 ^ (nlength n - 1)"
    using Suc_diff_1 nlength_ge_pow by simp
  then have "2 * n \<ge> 2 ^ (nlength n)"
    by (metis Suc_diff_1 \<open>0 < nlength n\<close> mult_le_mono2 power_Suc)
  moreover have "2 * n < 2 ^ (Suc (nlength n))"
    using nlength_less_pow by simp
  ultimately show ?thesis
    using pow_nlength by simp
qed

lemma nlength_prod: "nlength (n1 * n2) \<le> nlength n1 + nlength n2"
proof -
  let ?j1 = "nlength n1" and ?j2 = "nlength n2"
  have "n1 < 2 ^ ?j1" "n2 < 2 ^ ?j2"
    using nlength_less_pow by simp_all
  then have "n1 * n2 < 2 ^ ?j1 * 2 ^ ?j2"
    by (simp add: mult_strict_mono)
  then have "n1 * n2 < 2 ^ (?j1 + ?j2)"
    by (simp add: power_add)
  then have "n1 * n2 \<le> 2 ^ (?j1 + ?j2) - 1"
    by simp
  then have "nlength (n1 * n2) \<le> nlength (2 ^ (?j1 + ?j2) - 1)"
    using nlength_mono by simp
  then show "nlength (n1 * n2) \<le> ?j1 + ?j2"
    using nlength_pow_minus_1 by simp
qed

text \<open>
In the following lemma @{const Suc} is needed because $n^0 = 1$.
\<close>

lemma nlength_pow: "nlength (n ^ d) \<le> Suc (d * nlength n)"
proof (induction d)
  case 0
  then show ?case
    by (metis less_or_eq_imp_le mult_not_zero nat_power_eq_Suc_0_iff nlength_pow2)
next
  case (Suc d)
  have "nlength (n ^ Suc d) = nlength (n ^ d * n)"
    by (simp add: mult.commute)
  then have "nlength (n ^ Suc d) \<le> nlength (n ^ d) + nlength n"
    using nlength_prod by simp
  then show ?case
    using Suc by simp
qed

lemma nlength_sum: "nlength (n1 + n2) \<le> Suc (max (nlength n1) (nlength n2))"
proof -
  let ?m = "max n1 n2"
  have "n1 + n2 \<le> 2 * ?m"
    by simp
  then have "nlength (n1 + n2) \<le> nlength (2 * ?m)"
    using nlength_mono by simp
  moreover have "nlength ?m = max (nlength n1) (nlength n2)"
    using nlength_mono by (metis max.absorb1 max.cobounded2 max_def)
  ultimately show ?thesis
    using nlength_even_le
    by (metis canrepr_0 le_SucI le_zero_eq list.size(3) max_nat.neutr_eq_iff not_gr_zero zero_eq_add_iff_both_eq_0)
qed

lemma nlength_Suc: "nlength (Suc n) \<le> Suc (nlength n)"
  using nlength_sum nlength_1_simp
  by (metis One_nat_def Suc_leI add_Suc diff_Suc_1 length_greater_0_conv max.absorb_iff2
    max.commute max_def nlength_0 plus_1_eq_Suc)

lemma nlength_less_n: "n \<ge> 3 \<Longrightarrow> nlength n < n"
proof (induction n rule: nat_induct_at_least)
  case base
  then show ?case
    by (simp add: nlength_3)
next
  case (Suc n)
  then show ?case
    using nlength_Suc by (metis Suc_le_eq le_neq_implies_less nlength_le_n not_less_eq)
qed


subsubsection \<open>Comparing two numbers\<close>

text \<open>
In order to compare two numbers in canonical representation, we can use the
Turing machine @{const tm_equals}, which works for arbitrary proper symbol
sequences.

\null
\<close>

lemma min_nlength: "min (nlength n1) (nlength n2) = nlength (min n1 n2)"
  by (metis min_absorb2 min_def nat_le_linear nlength_mono)

lemma max_nlength: "max (nlength n1) (nlength n2) = nlength (max n1 n2)"
  using nlength_mono by (metis max.absorb1 max.cobounded2 max_def)

lemma contents_blank_0: "\<lfloor>[\<box>]\<rfloor> = \<lfloor>[]\<rfloor>"
  using contents_def by auto

definition tm_equalsn :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_equalsn \<equiv> tm_equals"

lemma tm_equalsn_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "0 < j3"
  shows "turing_machine k G (tm_equalsn j1 j2 j3)"
  unfolding tm_equalsn_def using assms tm_equals_tm by simp

lemma transforms_tm_equalsnI [transforms_intros]:
  fixes j1 j2 j3 :: tapeidx
  fixes tps tps' :: "tape list" and k b n1 n2 :: nat
  assumes "length tps = k" "j1 \<noteq> j2" "j2 \<noteq> j3" "j1 \<noteq> j3" "j1 < k" "j2 < k" "j3 < k"
    and "b \<le> 1"
  assumes
    "tps ! j1 = (\<lfloor>n1\<rfloor>\<^sub>N, 1)"
    "tps ! j2 = (\<lfloor>n2\<rfloor>\<^sub>N, 1)"
    "tps ! j3 = (\<lfloor>b\<rfloor>\<^sub>N, 1)"
  assumes "ttt = (3 * nlength (min n1 n2) + 7)"
  assumes "tps' = tps
    [j3 := (\<lfloor>if n1 = n2 then 1 else 0\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_equalsn j1 j2 j3) tps ttt tps'"
  unfolding tm_equalsn_def
proof (tform tps: assms)
  show "proper_symbols (canrepr n1)"
    using proper_symbols_canrepr by simp
  show "proper_symbols (canrepr n2)"
    using proper_symbols_canrepr by simp
  show "ttt = 3 * min (nlength n1) (nlength n2) + 7"
    using assms(12) min_nlength by simp
  let ?v = "if canrepr n1 = canrepr n2 then 3::nat else 0::nat"
  have "b = 0 \<or> b = 1"
    using assms(8) by auto
  then have "\<lfloor>b\<rfloor>\<^sub>N = \<lfloor>[]\<rfloor> \<or> \<lfloor>b\<rfloor>\<^sub>N = \<lfloor>[\<one>]\<rfloor>"
    using canrepr_0 canrepr_1 by auto
  then have "tps ! j3 = (\<lfloor>[]\<rfloor>, 1) \<or> tps ! j3 = (\<lfloor>[\<one>]\<rfloor>, 1)"
    using assms(11) by simp
  then have v: "tps ! j3 |:=| ?v = (\<lfloor>[?v]\<rfloor>, 1)"
    using contents_def by auto
  show "tps' = tps[j3 := tps ! j3 |:=| ?v]"
  proof (cases "n1 = n2")
    case True
    then show ?thesis
      using canrepr_1 v assms(13) by auto
  next
    case False
    then have "?v = 0"
      by (metis canrepr)
    then show ?thesis
      using canrepr_0 v assms(13) contents_blank_0 by auto
  qed
qed


subsubsection \<open>Copying a number between tapes\<close>

text \<open>
The next Turing machine overwrites the contents of tape $j_2$ with the contents
of tape $j_1$ and performs a carriage return on both tapes.
\<close>

definition tm_copyn :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_copyn j1 j2 \<equiv>
     tm_erase_cr j2 ;;
     tm_cp_until j1 j2 {\<box>} ;;
     tm_cr j1 ;;
     tm_cr j2"

lemma tm_copyn_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "j1 < k" "j2 < k" "j1 \<noteq> j2" "0 < j2"
  shows "turing_machine k G (tm_copyn j1 j2)"
  unfolding tm_copyn_def using assms tm_cp_until_tm tm_cr_tm tm_erase_cr_tm by simp

locale turing_machine_move =
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> tm_erase_cr j2"
definition "tm2 \<equiv> tm1 ;; tm_cp_until j1 j2 {\<box>}"
definition "tm3 \<equiv> tm2 ;; tm_cr j1"
definition "tm4 \<equiv> tm3 ;; tm_cr j2"

lemma tm4_eq_tm_copyn: "tm4 = tm_copyn j1 j2"
  unfolding tm4_def tm3_def tm2_def tm1_def tm_copyn_def by simp

context
  fixes x y :: nat and tps0 :: "tape list"
  assumes j_less [simp]: "j1 < length tps0" "j2 < length tps0"
  assumes j [simp]: "j1 \<noteq> j2"
    and tps_j1 [simp]: "tps0 ! j1 = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    and tps_j2 [simp]: "tps0 ! j2 = (\<lfloor>y\<rfloor>\<^sub>N, 1)"
begin

definition "tps1 \<equiv> tps0
  [j2 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm1 [transforms_intros]:
  assumes "t = 7 + 2 * nlength y"
  shows "transforms tm1 tps0 t tps1"
  unfolding tm1_def
proof (tform tps: tps1_def time: assms)
  show "proper_symbols (canrepr y)"
    using proper_symbols_canrepr by simp
qed

definition "tps2 \<equiv> tps0
  [j1 := (\<lfloor>x\<rfloor>\<^sub>N, Suc (nlength x)),
   j2 := (\<lfloor>x\<rfloor>\<^sub>N, Suc (nlength x))]"

lemma tm2 [transforms_intros]:
  assumes "t = 8 + (2 * nlength y + nlength x)"
  shows "transforms tm2 tps0 t tps2"
  unfolding tm2_def
proof (tform tps: tps1_def time: assms)
  show "rneigh (tps1 ! j1) {\<box>} (nlength x)"
  proof (rule rneighI)
    show "(tps1 ::: j1) (tps1 :#: j1 + nlength x) \<in> {\<box>}"
      using tps1_def canrepr_0 contents_outofbounds j(1) nlength_0_simp tps_j1
      by (metis fst_eqD lessI nth_list_update_neq plus_1_eq_Suc singleton_iff snd_eqD)
    show "\<And>n'. n' < nlength x \<Longrightarrow> (tps1 ::: j1) (tps1 :#: j1 + n') \<notin> {\<box>}"
      using tps1_def tps_j1 j j_less contents_inbounds proper_symbols_canrepr
      by (metis Suc_leI add_diff_cancel_left' fst_eqD not_add_less2 nth_list_update_neq
        plus_1_eq_Suc singletonD snd_eqD zero_less_Suc)
  qed

  have "(\<lfloor>x\<rfloor>\<^sub>N, Suc (nlength x)) = tps0[j2 := (\<lfloor>[]\<rfloor>, 1)] ! j1 |+| nlength x"
    using tps_j1 tps_j2 by (metis fst_eqD j(1) j_less(2) nth_list_update plus_1_eq_Suc snd_eqD)
  moreover have "(\<lfloor>x\<rfloor>\<^sub>N, Suc (nlength x)) =
      implant (tps0[j2 := (\<lfloor>[]\<rfloor>, 1)] ! j1) (tps0[j2 := (\<lfloor>[]\<rfloor>, 1)] ! j2) (nlength x)"
    using tps_j1 tps_j2 j j_less implant_contents nlength_0_simp
    by (metis add.right_neutral append.simps(1) canrepr_0 diff_Suc_1 drop0 le_eq_less_or_eq
     nth_list_update_eq nth_list_update_neq plus_1_eq_Suc take_all zero_less_one)
  ultimately show "tps2 = tps1
    [j1 := tps1 ! j1 |+| nlength x,
     j2 := implant (tps1 ! j1) (tps1 ! j2) (nlength x)]"
    unfolding tps2_def tps1_def by (simp add: list_update_swap[of j1])
qed

definition "tps3 \<equiv> tps0[j2 := (\<lfloor>x\<rfloor>\<^sub>N, Suc (nlength x))]"

lemma tm3 [transforms_intros]:
  assumes "t = 11 + (2 * nlength y + 2 * nlength x)"
  shows "transforms tm3 tps0 t tps3"
  unfolding tm3_def
proof (tform tps: tps2_def)
  have "tps2 :#: j1 = Suc (nlength x)"
    using assms tps2_def by (metis j(1) j_less(1) nth_list_update_eq nth_list_update_neq snd_conv)
  then show "t = 8 + (2 * nlength y + nlength x) + (tps2 :#: j1 + 2)"
    using assms by simp
  show "clean_tape (tps2 ! j1)"
    using tps2_def by (simp add: clean_tape_ncontents nth_list_update_neq')
  have "tps2 ! j1 |#=| 1 = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    using tps2_def by (simp add: nth_list_update_neq')
  then show "tps3 = tps2[j1 := tps2 ! j1 |#=| 1]"
    using tps3_def tps2_def by (metis j(1) list_update_id list_update_overwrite list_update_swap tps_j1)
qed

definition "tps4 \<equiv> tps0[j2 := (\<lfloor>x\<rfloor>\<^sub>N, 1)]"

lemma tm4:
  assumes "t = 14 + (3 * nlength x + 2 * nlength y)"
  shows "transforms tm4 tps0 t tps4"
  unfolding tm4_def
proof (tform tps: tps3_def time: tps3_def assms)
  show "clean_tape (tps3 ! j2)"
    using tps3_def clean_tape_ncontents by simp
  have "tps3 ! j2 |#=| 1 = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    using tps3_def by (simp add: nth_list_update_neq')
  then show "tps4 = tps3[j2 := tps3 ! j2 |#=| 1]"
    using tps4_def tps3_def by (metis list_update_overwrite tps_j1)
qed

lemma tm4':
  assumes "t = 14 + 3 * (nlength x + nlength y)"
  shows "transforms tm4 tps0 t tps4"
  using tm4 transforms_monotone assms by simp

end

end  (* locale turing_machine_move *)

lemma transforms_tm_copynI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and k x y :: nat
  assumes "j1 \<noteq> j2" "j1 < length tps" "j2 < length tps"
  assumes
    "tps ! j1 = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    "tps ! j2 = (\<lfloor>y\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 14 + 3 * (nlength x + nlength y)"
  assumes "tps' = tps
    [j2 := (\<lfloor>x\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_copyn j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_move j1 j2 .
  show ?thesis
    using assms loc.tm4' loc.tps4_def loc.tm4_eq_tm_copyn by simp
qed


subsubsection \<open>Setting the tape contents to a number\<close>

text \<open>
The Turing machine in this section writes a hard-coded number to a tape.
\<close>

definition tm_setn :: "tapeidx \<Rightarrow> nat \<Rightarrow> machine" where
  "tm_setn j n \<equiv> tm_set j (canrepr n)"

lemma tm_setn_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "j < k" and "0 < j "
  shows "turing_machine k G (tm_setn j n)"
proof -
  have "symbols_lt G (canrepr n)"
    using assms(2) bit_symbols_canrepr by fastforce
  then show ?thesis
    unfolding tm_setn_def using tm_set_tm assms by simp
qed

lemma transforms_tm_setnI [transforms_intros]:
  fixes j :: tapeidx
  fixes tps tps' :: "tape list" and x k n :: nat
  assumes "j < length tps"
  assumes "tps ! j = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
  assumes "t = 10 + 2 * nlength x + 2 * nlength n"
  assumes "tps' = tps[j := (\<lfloor>n\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_setn j n) tps t tps'"
  unfolding tm_setn_def
  using transforms_tm_setI[OF assms(1), of "canrepr x" "canrepr n" t tps'] assms
    canonical_canrepr canonical_def contents_clean_tape'
  by (simp add: eval_nat_numeral(3) numeral_Bit0 proper_symbols_canrepr)


subsection \<open>Incrementing\<close>

text \<open>
In this section we devise a Turing machine that increments a number. The next
function describes how the symbol sequence of the incremented number looks like.
Basically one has to flip all @{text \<one>} symbols starting at the least
significant digit until one reaches a @{text \<zero>}, which is then replaced by a
@{text \<one>}.  If there is no @{text \<zero>}, a @{text \<one>} is appended. Here we
exploit that the most significant digit is to the right.
\<close>

definition nincr :: "symbol list \<Rightarrow> symbol list" where
  "nincr zs \<equiv>
     if \<exists>i<length zs. zs ! i = \<zero>
     then replicate (LEAST i. i < length zs \<and> zs ! i = \<zero>) \<zero> @ [\<one>] @ drop (Suc (LEAST i. i < length zs \<and> zs ! i = \<zero>)) zs
     else replicate (length zs) \<zero> @ [\<one>]"

lemma canonical_nincr:
  assumes "canonical zs"
  shows "canonical (nincr zs)"
proof -
  have 1: "bit_symbols zs"
    using canonical_def assms by simp
  let ?j = "LEAST i. i < length zs \<and> zs ! i = \<zero>"
  have "bit_symbols (nincr zs)"
  proof (cases "\<exists>i<length zs. zs ! i = \<zero>")
    case True
    then have "nincr zs = replicate ?j \<zero> @ [\<one>] @ drop (Suc ?j) zs"
      using nincr_def by simp
    moreover have "bit_symbols (replicate ?j \<zero>)"
      by simp
    moreover have "bit_symbols [\<one>]"
      by simp
    moreover have "bit_symbols (drop (Suc ?j) zs)"
      using 1 by simp
    ultimately show ?thesis
      using bit_symbols_append by presburger
  next
    case False
    then show ?thesis
      using nincr_def bit_symbols_append by auto
  qed
  moreover have "last (nincr zs) = \<one>"
  proof (cases "\<exists>i<length zs. zs ! i = \<zero>")
    case True
    then show ?thesis
      using nincr_def assms canonical_def by auto
  next
    case False
    then show ?thesis
      using nincr_def by auto
  qed
  ultimately show ?thesis
    using canonical_def by simp
qed

lemma nincr:
  assumes "bit_symbols zs"
  shows "num (nincr zs) = Suc (num zs)"
proof (cases "\<exists>i<length zs. zs ! i = \<zero>")
  case True
  define j where "j = (LEAST i. i < length zs \<and> zs ! i = \<zero>)"
  then have 1: "j < length zs \<and> zs ! j = \<zero>"
    using LeastI_ex[OF True] by simp
  have 2: "zs ! i = \<one>" if "i < j" for i
    using that True j_def assms "1" less_trans not_less_Least by blast

  define xs :: "symbol list" where "xs = replicate j \<one> @ [\<zero>]"
  define ys :: "symbol list" where "ys = drop (Suc j) zs"
  have "zs = xs @ ys"
  proof -
    have "xs = take (Suc j) zs"
      using xs_def 1 2
      by (smt (verit, best) le_eq_less_or_eq length_replicate length_take min_absorb2 nth_equalityI
       nth_replicate nth_take take_Suc_conv_app_nth)
    then show ?thesis
      using ys_def by simp
  qed

  have "nincr zs = replicate j \<zero> @ [\<one>] @ drop (Suc j) zs"
    using nincr_def True j_def by simp
  then have "num (nincr zs) = num (replicate j \<zero> @ [\<one>] @ ys)"
    using ys_def by simp
  also have "... = num (replicate j \<zero> @ [\<one>]) + 2 ^ Suc j * num ys"
    using num_append by (metis append_assoc length_append_singleton length_replicate)
  also have "... = Suc (num xs) + 2 ^ Suc j * num ys"
  proof -
    have "num (replicate j \<zero> @ [\<one>]) = 2 ^ j"
      using num_replicate2_eq_pow by simp
    also have "... = Suc (2 ^ j - 1)"
      by simp
    also have "... = Suc (num (replicate j \<one>))"
      using num_replicate3_eq_pow_minus_1 by simp
    also have "... = Suc (num (replicate j \<one> @ [\<zero>]))"
      using num_trailing_zero by simp
    finally have "num (replicate j \<zero> @ [\<one>]) = Suc (num xs)"
      using xs_def by simp
    then show ?thesis
      by simp
  qed
  also have "... = Suc (num xs + 2 ^ Suc j * num ys)"
    by simp
  also have "... = Suc (num zs)"
    using `zs = xs @ ys` num_append xs_def by (metis length_append_singleton length_replicate)
  finally show ?thesis .
next
  case False
  then have "\<forall>i<length zs. zs ! i = \<one>"
    using assms by simp
  then have zs: "zs = replicate (length zs) \<one>"
    by (simp add: nth_equalityI)
  then have num_zs: "num zs = 2 ^ length zs - 1"
    by (metis num_replicate3_eq_pow_minus_1)
  have "nincr zs = replicate (length zs) \<zero> @ [\<one>]"
    using nincr_def False by auto
  then have "num (nincr zs) = 2 ^ length zs"
    by (simp add: num_replicate2_eq_pow)
  then show ?thesis
    using num_zs by simp
qed

lemma nincr_canrepr: "nincr (canrepr n) = canrepr (Suc n)"
  using canrepr canonical_canrepr canreprI bit_symbols_canrepr canonical_nincr nincr
  by metis

text \<open>
The next Turing machine performs the incrementing. Starting from the left of the
symbol sequence on tape $j$, it writes the symbol \textbf{0} until it reaches a
blank or the symbol \textbf{1}. Then it writes a \textbf{1} and returns the tape
head to the beginning.
\<close>

definition tm_incr :: "tapeidx \<Rightarrow> machine" where
  "tm_incr j \<equiv> tm_const_until j j {\<box>, \<zero>} \<zero> ;; tm_write j \<one> ;; tm_cr j"

lemma tm_incr_tm:
  assumes "G \<ge> 4" and "k \<ge> 2" and "j < k" and "j > 0"
  shows "turing_machine k G (tm_incr j)"
  unfolding tm_incr_def using assms tm_const_until_tm tm_write_tm tm_cr_tm by simp

locale turing_machine_incr =
  fixes j :: tapeidx
begin

definition "tm1 \<equiv> tm_const_until j j {\<box>, \<zero>} \<zero>"
definition "tm2 \<equiv> tm1 ;; tm_write j \<one>"
definition "tm3 \<equiv> tm2 ;; tm_cr j"

lemma tm3_eq_tm_incr: "tm3 = tm_incr j"
  unfolding tm3_def tm2_def tm1_def tm_incr_def by simp

context
  fixes x k :: nat and tps :: "tape list"
  assumes jk [simp]: "j < k" "length tps = k"
    and tps0 [simp]: "tps ! j = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
begin

lemma tm1 [transforms_intros]:
  assumes "i0 = (LEAST i. i \<le> nlength x \<and> \<lfloor>x\<rfloor>\<^sub>N (Suc i) \<in> {\<box>, \<zero>})"
    and "tps' = tps[j := constplant (tps ! j) \<zero> i0]"
  shows "transforms tm1 tps (Suc i0) tps'"
  unfolding tm1_def
proof (tform tps: assms(2))
  let ?P = "\<lambda>i. i \<le> nlength x \<and> \<lfloor>x\<rfloor>\<^sub>N (Suc i) \<in> {\<box>, \<zero>}"
  have 2: "i0 \<le> nlength x \<and> \<lfloor>x\<rfloor>\<^sub>N (Suc i0) \<in> {\<box>, \<zero>}"
    using LeastI[of ?P "nlength x"] jk(1) assms(1) by simp
  have 3: "\<not> ?P i" if "i < i0" for i
    using not_less_Least[of i ?P] jk(1) assms(1) that by simp
  show "rneigh (tps ! j) {\<box>, \<zero>} i0"
  proof (rule rneighI)
    show "(tps ::: j) (tps :#: j + i0) \<in> {\<box>, \<zero>}"
      using tps0 2 jk(1) assms(1) by simp
    show "\<And>n'. n' < i0 \<Longrightarrow> (tps ::: j) (tps :#: j + n') \<notin> {\<box>, \<zero>}"
      using tps0 2 3 jk(1) assms(1) by simp
  qed
qed

lemma tm2 [transforms_intros]:
  assumes "i0 = (LEAST i. i \<le> nlength x \<and> \<lfloor>x\<rfloor>\<^sub>N (Suc i) \<in> {\<box>, \<zero>})"
    and "ttt = Suc (Suc i0)"
    and "tps' = tps[j := (\<lfloor>Suc x\<rfloor>\<^sub>N, Suc i0)]"
  shows "transforms tm2 tps ttt tps'"
  unfolding tm2_def
proof (tform tps: assms(1,3) time: assms(1,2))
  let ?P = "\<lambda>i. i \<le> nlength x \<and> \<lfloor>x\<rfloor>\<^sub>N (Suc i) \<in> {\<box>, \<zero>}"
  have 1: "?P (nlength x)"
    by simp
  have 2: "i0 \<le> nlength x \<and> \<lfloor>x\<rfloor>\<^sub>N (Suc i0) \<in> {\<box>, \<zero>}"
    using LeastI[of ?P "nlength x"] assms(1) by simp
  have 3: "\<not> ?P i" if "i < i0" for i
    using not_less_Least[of i ?P] assms(1) that by simp
  let ?i = "LEAST i. i \<le> nlength x \<and> \<lfloor>x\<rfloor>\<^sub>N (Suc i) \<in> {\<box>, \<zero>}"
  show "tps' = tps
    [j := constplant (tps ! j) 2 ?i,
     j := tps[j := constplant (tps ! j) \<zero> ?i] ! j |:=| \<one>]"
     (is "tps' = ?rhs")
  proof -
    have "?rhs = tps [j := constplant (\<lfloor>x\<rfloor>\<^sub>N, Suc 0) \<zero> i0 |:=| \<one>]"
      using jk assms(1) by simp
    moreover have "(\<lfloor>Suc x\<rfloor>\<^sub>N, Suc i0) = constplant (\<lfloor>x\<rfloor>\<^sub>N, Suc 0) 2 i0 |:=| \<one>"
      (is "?l = ?r")
    proof -
      have "snd ?l = snd ?r"
        by (simp add: transplant_def)
      moreover have "\<lfloor>Suc x\<rfloor>\<^sub>N = fst ?r"
      proof -
        let ?zs = "canrepr x"
        have l: "\<lfloor>Suc x\<rfloor>\<^sub>N = \<lfloor>nincr ?zs\<rfloor>"
          by (simp add: nincr_canrepr)
        have r: "fst ?r = (\<lambda>i. if Suc 0 \<le> i \<and> i < Suc i0 then \<zero> else \<lfloor>x\<rfloor>\<^sub>N i)(Suc i0 := \<one>)"
          using constplant by auto
        show ?thesis
        proof (cases "\<exists>i<length ?zs. ?zs ! i = \<zero>")
          case True
          let ?Q = "\<lambda>i. i < length ?zs \<and> ?zs ! i = \<zero>"
          have Q1: "?Q (Least ?Q)"
            using True by (metis (mono_tags, lifting) LeastI_ex)
          have Q2: "\<not> ?Q i" if "i < Least ?Q" for i
            using True not_less_Least that by blast
          have "Least ?P = Least ?Q"
          proof (rule Least_equality)
            show "Least ?Q \<le> nlength x \<and> \<lfloor>x\<rfloor>\<^sub>N (Suc (Least ?Q)) \<in> {\<box>, \<zero>}"
            proof
              show "Least ?Q \<le> nlength x"
                using True by (metis (mono_tags, lifting) LeastI_ex less_imp_le)
              show "\<lfloor>x\<rfloor>\<^sub>N (Suc (Least ?Q)) \<in> {\<box>, \<zero>}"
                using True by (simp add: Q1 Suc_leI)
            qed
            then show "\<And>y. y \<le> nlength x \<and> \<lfloor>x\<rfloor>\<^sub>N (Suc y) \<in> {\<box>, \<zero>} \<Longrightarrow> (Least ?Q) \<le> y"
              using True Q1 Q2 bit_symbols_canrepr contents_def
              by (smt (z3) Least_le Suc_leI bot_nat_0.not_eq_extremum diff_Suc_1 insert_iff le_neq_implies_less
                nat.simps(3) nlength_0_simp nlength_le_n nlength_less_n singletonD)
          qed
          then have i0: "i0 = Least ?Q"
            using assms(1) by simp
          then have nincr_zs: "nincr ?zs = replicate i0 \<zero> @ [\<one>] @ drop (Suc i0) ?zs"
            using nincr_def True by simp
          show ?thesis
          proof
            fix i
            consider
               "i = 0"
             | "Suc 0 \<le> i \<and> i < Suc i0"
             | "i = Suc i0"
             | "i > Suc i0 \<and> i \<le> length ?zs"
             | "i > Suc i0 \<and> i > length ?zs"
              by linarith
            then have "\<lfloor>replicate i0 \<zero> @ [\<one>] @ drop (Suc i0) ?zs\<rfloor> i =
                ((\<lambda>i. if Suc 0 \<le> i \<and> i < Suc i0 then \<zero> else \<lfloor>x\<rfloor>\<^sub>N i)(Suc i0 := \<one>)) i"
                (is "?A i = ?B i")
            proof (cases)
              case 1
              then show ?thesis
                by (simp add: transplant_def)
            next
              case 2
              then have "i - 1 < i0"
                by auto
              then have "(replicate i0 \<zero> @ [\<one>] @ drop (Suc i0) ?zs) ! (i - 1) = \<zero>"
                by (metis length_replicate nth_append nth_replicate)
              then have "?A i = \<zero>"
                using contents_def i0 "2" Q1 nincr_canrepr nincr_zs
                by (metis Suc_le_lessD le_trans less_Suc_eq_le less_imp_le_nat less_numeral_extra(3) nlength_Suc_le)
              moreover have "?B i = \<zero>"
                using i0 2 by simp
              ultimately show ?thesis
                by simp
            next
              case 3
              then show ?thesis
                using i0 Q1 canrepr_0 contents_inbounds nincr_canrepr nincr_zs nlength_0_simp nlength_Suc nlength_Suc_le
                by (smt (z3) Suc_leI append_Cons diff_Suc_1 fun_upd_apply le_trans length_replicate
                  nth_append_length zero_less_Suc)
            next
              case 4
              then have "?A i = (replicate i0 \<zero> @ [\<one>] @ drop (Suc i0) ?zs) ! (i - 1)"
                by auto
              then have "?A i = ((replicate i0 \<zero> @ [\<one>]) @ drop (Suc i0) ?zs) ! (i - 1)"
                by simp
              moreover have "length (replicate i0 \<zero> @ [\<one>]) = Suc i0"
                by simp
              moreover have "i - 1 < length ?zs"
                using 4 by auto
              moreover have "i - 1 >= Suc i0"
                using 4 by auto
              ultimately have "?A i = ?zs ! (i - 1)"
                using i0 Q1
                by (metis (no_types, lifting) Suc_leI append_take_drop_id length_take min_absorb2 not_le nth_append)
              moreover have "?B i = \<lfloor>x\<rfloor>\<^sub>N i"
                using 4 by simp
              ultimately show ?thesis
                using i0 4 contents_def by simp
            next
              case 5
              then show ?thesis
                by auto
            qed
            then show "\<lfloor>Suc x\<rfloor>\<^sub>N i = fst (constplant (\<lfloor>x\<rfloor>\<^sub>N, Suc 0) \<zero> i0 |:=| \<one>) i"
              using nincr_zs l r by simp
          qed
        next
          case False
          then have nincr_zs: "nincr ?zs = replicate (length ?zs) \<zero> @ [\<one>]"
            using nincr_def by auto
          have "Least ?P = length ?zs"
          proof (rule Least_equality)
            show "nlength x \<le> nlength x \<and> \<lfloor>x\<rfloor>\<^sub>N (Suc (nlength x)) \<in> {\<box>, \<zero>}"
              by simp
            show "\<And>y. y \<le> nlength x \<and> \<lfloor>x\<rfloor>\<^sub>N (Suc y) \<in> {\<box>, \<zero>} \<Longrightarrow> nlength x \<le> y"
              using False contents_def bit_symbols_canrepr
              by (metis diff_Suc_1 insert_iff le_neq_implies_less nat.simps(3) not_less_eq_eq numeral_3_eq_3 singletonD)
          qed
          then have i0: "i0 = length ?zs"
            using assms(1) by simp
          show ?thesis
          proof
            fix i
            consider "i = 0" | "Suc 0 \<le> i \<and> i < Suc (length ?zs)" | "i = Suc (length ?zs)" | "i > Suc (length ?zs)"
              by linarith
            then have "\<lfloor>replicate (length ?zs) \<zero> @ [\<one>]\<rfloor> i =
                ((\<lambda>i. if Suc 0 \<le> i \<and> i < Suc i0 then \<zero> else \<lfloor>x\<rfloor>\<^sub>N i)(Suc i0 := \<one>)) i"
                (is "?A i = ?B i")
            proof (cases)
              case 1
              then show ?thesis
                by (simp add: transplant_def)
            next
              case 2
              then have "?A i = \<zero>"
                by (metis One_nat_def Suc_le_lessD add.commute contents_def diff_Suc_1 length_Cons length_append
                  length_replicate less_Suc_eq_0_disj less_imp_le_nat less_numeral_extra(3) list.size(3) nth_append
                   nth_replicate plus_1_eq_Suc)
              moreover have "?B i = \<zero>"
                using i0 2 by simp
              ultimately show ?thesis
                by simp
            next
              case 3
              then show ?thesis
                using i0 canrepr_0 contents_inbounds nincr_canrepr nincr_zs nlength_0_simp nlength_Suc
                by (metis One_nat_def add.commute diff_Suc_1 fun_upd_apply length_Cons length_append
                  length_replicate nth_append_length plus_1_eq_Suc zero_less_Suc)
            next
              case 4
              then show ?thesis
                using i0 by simp
            qed
            then show "\<lfloor>Suc x\<rfloor>\<^sub>N i = fst (constplant (\<lfloor>x\<rfloor>\<^sub>N, Suc 0) \<zero> i0 |:=| \<one>) i"
              using nincr_zs l r by simp
          qed
        qed
      qed
      ultimately show ?thesis
        by simp
    qed
    ultimately show ?thesis
      using assms(3) by simp
  qed
qed

lemma tm3:
  assumes "i0 = (LEAST i. i \<le> nlength x \<and> \<lfloor>x\<rfloor>\<^sub>N (Suc i) \<in> {\<box>, \<zero>})"
    and "ttt = 5 + 2 * i0"
    and "tps' = tps[j := (\<lfloor>Suc x\<rfloor>\<^sub>N, Suc 0)]"
  shows "transforms tm3 tps ttt tps'"
  unfolding tm3_def
proof (tform tps: assms(1,3) time: assms(1,2))
  let ?tps = "tps[j := (\<lfloor>Suc x\<rfloor>\<^sub>N, Suc (LEAST i. i \<le> nlength x \<and> \<lfloor>x\<rfloor>\<^sub>N (Suc i) \<in> {\<box>, \<zero>}))]"
  show "clean_tape (?tps ! j)"
    using clean_tape_ncontents by (simp add: assms(1,3))
qed

lemma tm3':
  assumes "ttt = 5 + 2 * nlength x"
    and "tps' = tps[j := (\<lfloor>Suc x\<rfloor>\<^sub>N, Suc 0)]"
  shows "transforms tm3 tps ttt tps'"
proof -
  let ?P = "\<lambda>i. i \<le> nlength x \<and> \<lfloor>x\<rfloor>\<^sub>N (Suc i) \<in> {\<box>, \<zero>}"
  define i0 where "i0 = Least ?P"
  have "i0 \<le> nlength x \<and> \<lfloor>x\<rfloor>\<^sub>N (Suc i0) \<in> {\<box>, \<zero>}"
    using LeastI[of ?P "nlength x"] i0_def by simp
  then have "5 + 2 * i0 \<le> 5 + 2 * nlength x"
    by simp
  moreover have "transforms tm3 tps (5 + 2 * i0) tps'"
    using assms tm3 i0_def by simp
  ultimately show ?thesis
    using transforms_monotone assms(1) by simp
qed

end  (* context *)

end  (* locale *)

lemma transforms_tm_incrI [transforms_intros]:
  assumes "j < k"
    and "length tps = k"
    and "tps ! j = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    and "ttt = 5 + 2 * nlength x"
    and "tps' = tps[j := (\<lfloor>Suc x\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_incr j) tps ttt tps'"
proof -
  interpret loc: turing_machine_incr j .
  show ?thesis
    using assms loc.tm3' loc.tm3_eq_tm_incr by simp
qed


subsubsection \<open>Incrementing multiple times\<close>

text \<open>
Adding a constant by iteratively incrementing is not exactly efficient, but it
still only takes constant time and thus does not endanger any time bounds.
\<close>

fun tm_plus_const :: "nat \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_plus_const 0 j = []" |
  "tm_plus_const (Suc c) j = tm_plus_const c j ;; tm_incr j"

lemma tm_plus_const_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "0 < j" and "j < k"
  shows "turing_machine k G (tm_plus_const c j)"
  using assms Nil_tm tm_incr_tm by (induction c) simp_all

lemma transforms_tm_plus_constI [transforms_intros]:
  fixes c :: nat
  assumes "j < k"
    and "j > 0"
    and "length tps = k"
    and "tps ! j = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    and "ttt = c * (5 + 2 * nlength (x + c))"
    and "tps' = tps[j := (\<lfloor>x + c\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_plus_const c j) tps ttt tps'"
  using assms(5,6,4)
proof (induction c arbitrary: ttt tps')
  case 0
  then show ?case
    using transforms_Nil assms
    by (metis add_cancel_left_right list_update_id mult_eq_0_iff tm_plus_const.simps(1))
next
  case (Suc c)
  define tpsA where "tpsA = tps[j := (\<lfloor>x + c\<rfloor>\<^sub>N, 1)]"
  let ?ttt = "c * (5 + 2 * nlength (x + c)) + (5 + 2 * nlength (x + c))"
  have "transforms (tm_plus_const c j ;; tm_incr j) tps ?ttt tps'"
  proof (tform tps: assms)
    show "transforms (tm_plus_const c j) tps (c * (5 + 2 * nlength (x + c))) tpsA"
      using tpsA_def assms Suc by simp
    show "j < length tpsA"
      using tpsA_def assms(1,3) by simp
    show "tpsA ! j = (\<lfloor>x + c\<rfloor>\<^sub>N, 1)"
      using tpsA_def assms(1,3) by simp
    show "tps' = tpsA[j := (\<lfloor>Suc (x + c)\<rfloor>\<^sub>N, 1)]"
      using tpsA_def assms Suc by (metis add_Suc_right list_update_overwrite)
  qed
  moreover have "?ttt \<le> ttt"
  proof -
    have "?ttt = Suc c * (5 + 2 * nlength (x + c))"
      by simp
    also have "... \<le> Suc c * (5 + 2 * nlength (x + Suc c))"
      using nlength_mono Suc_mult_le_cancel1 by auto
    finally show "?ttt \<le> ttt"
      using Suc by simp
  qed
  ultimately have "transforms (tm_plus_const c j ;; tm_incr j) tps ttt tps'"
    using transforms_monotone by simp
  then show ?case
    by simp
qed


subsection \<open>Decrementing\<close>

text \<open>
Decrementing a number is almost like incrementing but with the symbols
\textbf{0} and \textbf{1} swapped. One difference is that in order to get a
canonical symbol sequence, a trailing zero must be removed, whereas incrementing
cannot result in a trailing zero. Another difference is that decrementing the
number zero yields zero.

The next function returns the leftmost symbol~\textbf{1}, that is, the one
that needs to be flipped.
\<close>

definition first1 :: "symbol list \<Rightarrow> nat" where
  "first1 zs \<equiv> LEAST i. i < length zs \<and> zs ! i = \<one>"

lemma canonical_ex_3:
  assumes "canonical zs" and "zs \<noteq> []"
  shows "\<exists>i<length zs. zs ! i = \<one>"
  using assms canonical_def by (metis One_nat_def Suc_pred last_conv_nth length_greater_0_conv lessI)

lemma canonical_first1:
  assumes "canonical zs" and "zs \<noteq> []"
  shows "first1 zs < length zs \<and> zs ! first1 zs = \<one>"
  using assms canonical_ex_3 by (metis (mono_tags, lifting) LeastI first1_def)

lemma canonical_first1_less:
  assumes "canonical zs" and "zs \<noteq> []"
  shows "\<forall>i<first1 zs. zs ! i = \<zero>"
proof -
  have "\<forall>i<first1 zs. zs ! i \<noteq> \<one>"
    using assms first1_def canonical_first1 not_less_Least by fastforce
  then show ?thesis
    using assms canonical_def by (meson canonical_first1 less_trans)
qed

text \<open>
The next function describes how the canonical representation of the decremented
symbol sequence looks like. It has special cases for the empty sequence and for
sequences whose only \textbf{1} is the most significant digit.
\<close>

definition ndecr :: "symbol list \<Rightarrow> symbol list" where
  "ndecr zs \<equiv>
    if zs = [] then []
    else if first1 zs = length zs - 1
      then replicate (first1 zs) \<one>
      else replicate (first1 zs) \<one> @ [\<zero>] @ drop (Suc (first1 zs)) zs"

lemma canonical_ndecr:
  assumes "canonical zs"
  shows "canonical (ndecr zs)"
proof -
  let ?i = "first1 zs"
  consider
      "zs = []"
    | "zs \<noteq> [] \<and> first1 zs = length zs - 1"
    | "zs \<noteq> [] \<and> first1 zs < length zs - 1"
    using canonical_first1 assms by fastforce
  then show ?thesis
  proof (cases)
    case 1
    then show ?thesis
      using ndecr_def canonical_def by simp
  next
    case 2
    then show ?thesis
      using canonical_def ndecr_def not_less_eq by fastforce
  next
    case 3
    then have "Suc (first1 zs) < length zs"
      by auto
    then have "last (drop (Suc (first1 zs)) zs) = \<one>"
      using assms canonical_def 3 by simp
    moreover have "bit_symbols (replicate (first1 zs) \<one> @ [\<zero>] @ drop (Suc (first1 zs)) zs)"
    proof -
      have "bit_symbols (replicate (first1 zs) \<one>)"
        by simp
      moreover have "bit_symbols [\<zero>]"
        by simp
      moreover have "bit_symbols (drop (Suc (first1 zs)) zs)"
        using assms canonical_def by simp
      ultimately show ?thesis
        using bit_symbols_append by presburger
    qed
    ultimately show ?thesis
      using canonical_def ndecr_def 3 by auto
  qed
qed

lemma ndecr:
  assumes "canonical zs"
  shows "num (ndecr zs) = num zs - 1"
proof -
  let ?i = "first1 zs"
  consider "zs = []" | "zs \<noteq> [] \<and> first1 zs = length zs - 1" | "zs \<noteq> [] \<and> first1 zs < length zs - 1"
    using canonical_first1 assms by fastforce
  then show ?thesis
  proof (cases)
    case 1
    then show ?thesis
      using ndecr_def canrepr_0 canrepr by (metis zero_diff)
  next
    case 2
    then have less: "zs ! i = \<zero>" if "i < first1 zs" for i
      using that assms canonical_first1_less by simp
    have at: "zs ! (first1 zs) = \<one>"
      using 2 canonical_first1 assms by blast
    have "zs = replicate (first1 zs) \<zero> @ [\<one>]" (is "zs = ?zs")
    proof (rule nth_equalityI)
      show len: "length zs = length ?zs"
        using 2 by simp
      show "zs ! i = ?zs ! i" if "i < length zs" for i
      proof (cases "i < first1 zs")
        case True
        then show ?thesis
          by (simp add: less nth_append)
      next
        case False
        then show ?thesis
          using len that at
          by (metis Suc_leI leD length_append_singleton length_replicate linorder_neqE_nat nth_append_length)
      qed
    qed
    moreover from this have "ndecr zs = replicate (first1 zs) 3"
      using ndecr_def 2 by simp
    ultimately show ?thesis
      using num_replicate2_eq_pow num_replicate3_eq_pow_minus_1 by metis
  next
    case 3
    then have less: "zs ! i = \<zero>" if "i < ?i" for i
      using that assms canonical_first1_less by simp
    have at: "zs ! ?i = \<one>"
      using 3 canonical_first1 assms by simp
    have zs: "zs = replicate ?i \<zero> @ [\<one>] @ drop (Suc ?i) zs" (is "zs = ?zs")
    proof (rule nth_equalityI)
      show len: "length zs = length ?zs"
        using 3 by auto
      show "zs ! i = ?zs ! i" if "i < length zs" for i
      proof -
        consider "i < ?i" | "i = ?i" | "i > ?i"
          by linarith
        then show ?thesis
        proof (cases)
          case 1
          then show ?thesis
            using less by (metis length_replicate nth_append nth_replicate)
        next
          case 2
          then show ?thesis
            using at by (metis append_Cons length_replicate nth_append_length)
        next
          case 3
          have "?zs = (replicate ?i \<zero> @ [\<one>]) @ drop (Suc ?i) zs"
            by simp
          then have "?zs ! i = drop (Suc ?i) zs ! (i - Suc ?i)"
            using 3 by (simp add: nth_append)
          then have "?zs ! i = zs ! i"
            using 3 that by simp
          then show ?thesis
            by simp
        qed
      qed
    qed
    then have "ndecr zs = replicate ?i \<one> @ [\<zero>] @ drop (Suc ?i) zs"
      using ndecr_def 3 by simp
    then have "Suc (num (ndecr zs)) = Suc (num ((replicate ?i \<one> @ [\<zero>]) @ drop (Suc ?i) zs))"
        (is "_ = Suc (num (?xs @ ?ys))")
      by simp
    also have "... = Suc (num ?xs + 2 ^ length ?xs * num ?ys)"
      using num_append by blast
    also have "... = Suc (num ?xs + 2 ^ Suc ?i * num ?ys)"
      by simp
    also have "... = Suc (2 ^ ?i - 1 + 2 ^ Suc ?i * num ?ys)"
      using num_replicate3_eq_pow_minus_1 num_trailing_zero[of 2 "replicate ?i \<one>"] by simp
    also have "... = 2 ^ ?i + 2 ^ Suc ?i * num ?ys"
      by simp
    also have "... = num (replicate ?i \<zero> @ [\<one>]) + 2 ^ Suc ?i * num ?ys"
      using num_replicate2_eq_pow by simp
    also have "... = num ((replicate ?i \<zero> @ [\<one>]) @ ?ys)"
      using num_append by (metis length_append_singleton length_replicate)
    also have "... = num (replicate ?i \<zero> @ [\<one>] @ ?ys)"
      by simp
    also have "... = num zs"
      using zs by simp
    finally have "Suc (num (ndecr zs)) = num zs" .
    then show ?thesis
      by simp
  qed
qed

text \<open>
The next Turing machine implements the function @{const ndecr}. It does nothing
on the empty input, which represents zero. On other inputs it writes symbols
\textbf{1} going right until it reaches a \textbf{1} symbol, which is guaranteed
to happen for non-empty canonical representations. It then overwrites this
\textbf{1} with \textbf{0}.  If there is a blank symbol to the right of this
\textbf{0}, the \textbf{0} is removed again.
\<close>

definition tm_decr :: "tapeidx \<Rightarrow> machine" where
  "tm_decr j \<equiv>
    IF \<lambda>rs. rs ! j = \<box> THEN
      []
    ELSE
      tm_const_until j j {\<one>} \<one> ;;
      tm_rtrans j (\<lambda>_. \<zero>) ;;
      IF \<lambda>rs. rs ! j = \<box> THEN
        tm_left j ;;
        tm_write j \<box>
      ELSE
        []
      ENDIF ;;
      tm_cr j
    ENDIF"

lemma tm_decr_tm:
  assumes "G \<ge> 4" and "k \<ge> 2" and "j < k" and "0 < j"
  shows "turing_machine k G (tm_decr j)"
  unfolding tm_decr_def
  using assms tm_cr_tm tm_const_until_tm tm_rtrans_tm tm_left_tm tm_write_tm
    turing_machine_branch_turing_machine Nil_tm
  by simp

locale turing_machine_decr =
  fixes j :: tapeidx
begin

definition "tm1 \<equiv> tm_const_until j j {\<one>} \<one>"
definition "tm2 \<equiv> tm1 ;; tm_rtrans j (\<lambda>_. \<zero>)"
definition "tm23 \<equiv> tm_left j"
definition "tm24 \<equiv> tm23 ;; tm_write j \<box>"
definition "tm25 \<equiv> IF \<lambda>rs. rs ! j = \<box> THEN tm24 ELSE [] ENDIF"
definition "tm5 \<equiv> tm2 ;; tm25"
definition "tm6 \<equiv> tm5 ;; tm_cr j"
definition "tm7 \<equiv> IF \<lambda>rs. rs ! j = \<box> THEN [] ELSE tm6 ENDIF"

lemma tm7_eq_tm_decr: "tm7 = tm_decr j"
  unfolding tm1_def tm2_def tm23_def tm24_def tm25_def tm5_def tm6_def tm7_def tm_decr_def
  by simp

context
  fixes tps0 :: "tape list" and xs :: "symbol list" and k :: nat
  assumes jk: "length tps0 = k" "j < k"
    and can: "canonical xs"
    and tps0: "tps0 ! j = (\<lfloor>xs\<rfloor>, 1)"
begin

lemma bs: "bit_symbols xs"
  using can canonical_def by simp

context
  assumes read_tps0: "read tps0 ! j = \<box>"
begin

lemma xs_Nil: "xs = []"
  using tps0 jk tapes_at_read' read_tps0 bs contents_inbounds
  by (metis can canreprI canrepr_0 fst_conv ncontents_1_blank_iff_zero snd_conv)

lemma transforms_NilI:
  assumes "ttt = 0"
    and "tps' = tps0[j := (\<lfloor>ndecr xs\<rfloor>, 1)]"
  shows "transforms [] tps0 ttt tps'"
  using transforms_Nil xs_Nil ndecr_def tps0 assms by (metis Basics.transforms_Nil list_update_id)

end  (* context read tps0 ! j = 0 *)

context
  assumes read_tps0': "read tps0 ! j \<noteq> \<box>"
begin

lemma xs: "xs \<noteq> []"
  using tps0 jk tapes_at_read' read_tps0' bs contents_inbounds
  by (metis canrepr_0 fst_conv ncontents_1_blank_iff_zero snd_conv)

lemma first1: "first1 xs < length xs" "xs ! first1 xs = \<one>" "\<forall>i<first1 xs. xs ! i = \<zero>"
  using canonical_first1[OF can xs] canonical_first1_less[OF can xs] by simp_all

definition "tps1 \<equiv> tps0
  [j := (\<lfloor>replicate (first1 xs) \<one> @ [\<one>] @ (drop (Suc (first1 xs)) xs)\<rfloor>, Suc (first1 xs))]"

lemma tm1 [transforms_intros]:
  assumes "ttt = Suc (first1 xs)"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: tps1_def jk time: assms)
  show "rneigh (tps0 ! j) {\<one>} (first1 xs)"
  proof (rule rneighI)
    show "(tps0 ::: j) (tps0 :#: j + first1 xs) \<in> {\<one>}"
      using first1(1,2) tps0 jk by (simp add: Suc_leI)
    show "\<And>n'. n' < first1 xs \<Longrightarrow> (tps0 ::: j) (tps0 :#: j + n') \<notin> {\<one>}"
      using first1(3) tps0 jk by (simp add: contents_def)
  qed
  show "tps1 = tps0
    [j := tps0 ! j |+| first1 xs,
     j := constplant (tps0 ! j) \<one> (first1 xs)]"
  proof -
    have "tps1 ! j = constplant (tps0 ! j) 3 (first1 xs)"
      (is "_ = ?rhs")
    proof -
      have "fst ?rhs = (\<lambda>i. if 1 \<le> i \<and> i < 1 + first1 xs then \<one> else \<lfloor>xs\<rfloor> i)"
        using tps0 jk constplant by auto
      also have "... = \<lfloor>replicate (first1 xs) \<one> @ [\<one>] @ drop (Suc (first1 xs)) xs\<rfloor>"
      proof
        fix i
        consider
            "i = 0"
          | "i \<ge> 1 \<and> i < 1 + first1 xs"
          | "i = 1 + first1 xs"
          | "1 + first1 xs < i \<and> i \<le> length xs"
          | "i > length xs"
          by linarith
        then show "(if 1 \<le> i \<and> i < 1 + first1 xs then \<one> else \<lfloor>xs\<rfloor> i) =
          \<lfloor>replicate (first1 xs) \<one> @ [\<one>] @ drop (Suc (first1 xs)) xs\<rfloor> i"
          (is "?l = ?r")
        proof (cases)
          case 1
          then show ?thesis
            by simp
        next
          case 2
          then show ?thesis
            by (smt (verit) One_nat_def Suc_diff_Suc add_diff_inverse_nat contents_inbounds first1(1) length_append
              length_drop length_replicate less_imp_le_nat less_le_trans list.size(3) list.size(4) not_le not_less_eq
              nth_append nth_replicate plus_1_eq_Suc)
        next
          case 3
          then show ?thesis
            using first1
            by (smt (verit) One_nat_def Suc_diff_Suc Suc_leI add_diff_inverse_nat append_Cons contents_inbounds
              diff_Suc_1 length_append length_drop length_replicate less_SucI less_Suc_eq_0_disj list.size(3)
              list.size(4) not_less_eq nth_append_length)
        next
          case 4
          then have "?r = (replicate (first1 xs) \<one> @ [\<one>] @ drop (Suc (first1 xs)) xs) ! (i - 1)"
            by auto
          also have "... = ((replicate (first1 xs) \<one> @ [\<one>]) @ drop (Suc (first1 xs)) xs) ! (i - 1)"
            by simp
          also have "... = (drop (Suc (first1 xs)) xs) ! (i - 1 - Suc (first1 xs))"
            using 4
            by (metis Suc_leI add_diff_inverse_nat gr_implies_not0 leD length_append_singleton
              length_replicate less_one nth_append plus_1_eq_Suc)
          also have "... = xs ! (i - 1)"
            using 4 by (metis Suc_leI add_diff_inverse_nat first1(1) gr_implies_not0 leD less_one nth_drop plus_1_eq_Suc)
          also have "... = \<lfloor>xs\<rfloor> i"
            using 4 by simp
          also have "... = ?l"
            using 4 by simp
          finally have "?r = ?l" .
          then show ?thesis
            by simp
        next
          case 5
          then show ?thesis
            using first1(1) by simp
        qed
      qed
      also have "... = tps1 ::: j"
        using tps1_def jk by simp
      finally have "fst ?rhs = fst (tps1 ! j)" .
      then show ?thesis
        using tps1_def jk constplant tps0 by simp
    qed
    then show ?thesis
      using tps1_def tps0 jk by simp
  qed
qed

definition "tps2 \<equiv> tps0
  [j := (\<lfloor>replicate (first1 xs) \<one> @ [\<zero>] @ drop (Suc (first1 xs)) xs\<rfloor>, Suc (Suc (first1 xs)))]"

lemma tm2 [transforms_intros]:
  assumes "ttt = first1 xs + 2"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: tps2_def tps1_def jk time: assms)
  show "tps2 = tps1[j := tps1 ! j |:=| \<zero> |+| 1]"
    using tps1_def tps2_def jk contents_append_update by simp
qed

definition "tps5 \<equiv> tps0
  [j := (\<lfloor>ndecr xs\<rfloor>, if read tps2 ! j = \<box> then Suc (first1 xs) else Suc (Suc (first1 xs)))]"

context
  assumes read_tps2: "read tps2 ! j = \<box>"
begin

lemma proper_contents_outofbounds:
  assumes "proper_symbols zs" and "\<lfloor>zs\<rfloor> i = \<box>"
  shows "i > length zs"
  using contents_def proper_symbols_ne0 assms
  by (metis Suc_diff_1 bot_nat_0.not_eq_extremum linorder_le_less_linear not_less_eq zero_neq_one)

lemma first1_eq: "first1 xs = length xs - 1"
proof -
  have "tps2 ! j = (\<lfloor>replicate (first1 xs) \<one> @ [\<zero>] @ drop (Suc (first1 xs)) xs\<rfloor>, Suc (Suc (first1 xs)))"
      (is "_ = (\<lfloor>?zs\<rfloor>, ?i)")
    using tps2_def jk by simp
  have "proper_symbols xs"
    using can bs by fastforce
  then have *: "proper_symbols ?zs"
    using proper_symbols_append[of "[\<zero>]" "drop (Suc (first1 xs)) xs"] proper_symbols_append
    by simp
  have "read tps2 ! j = \<lfloor>?zs\<rfloor> ?i"
    using tps2_def jk tapes_at_read'[of j tps2] by simp
  then have "\<lfloor>?zs\<rfloor> ?i = \<box>"
    using read_tps2 by simp
  then have "?i > length ?zs"
    using * proper_contents_outofbounds by blast
  moreover have "length ?zs = length xs"
    using first1 by simp
  ultimately have "Suc (first1 xs) \<ge> length xs"
    by simp
  moreover have "length xs > 0"
    using xs by simp
  ultimately have "first1 xs \<ge> length xs - 1"
    by simp
  then show ?thesis
    using first1(1) by simp
qed

lemma drop_xs_Nil: "drop (Suc (first1 xs)) xs = []"
  using first1_eq xs by simp

lemma tps2_eq: "tps2 = tps0[j := (\<lfloor>replicate (first1 xs) \<one> @ [\<zero>]\<rfloor>, Suc (Suc (first1 xs)))]"
  using tps2_def drop_xs_Nil jk by simp

definition "tps23 \<equiv> tps0
  [j := (\<lfloor>replicate (first1 xs) \<one> @ [\<zero>]\<rfloor>, Suc (first1 xs))]"

lemma tm23 [transforms_intros]:
  assumes "ttt = 1"
  shows "transforms tm23 tps2 ttt tps23"
  unfolding tm23_def
proof (tform tps: tps2_def tps23_def jk time: assms)
  show "tps23 = tps2[j := tps2 ! j |-| 1]"
    using tps23_def tps2_eq jk by simp
qed

definition "tps24 \<equiv> tps0
  [j := (\<lfloor>replicate (first1 xs) \<one>\<rfloor>, Suc (first1 xs))]"

lemma tm24:
  assumes "ttt = 2"
  shows "transforms tm24 tps2 ttt tps24"
  unfolding tm24_def
proof (tform tps: tps23_def tps24_def time: assms)
  show "tps24 = tps23[j := tps23 ! j |:=| \<box>]"
  proof -
    have "tps23 ! j |:=| \<box> = (\<lfloor>replicate (first1 xs) \<one> @ [\<zero>]\<rfloor>, Suc (first1 xs)) |:=| \<box>"
      using tps23_def jk by simp
    then have "tps23 ! j |:=| \<box> = (\<lfloor>replicate (first1 xs) \<one> @ [\<box>]\<rfloor>, Suc (first1 xs))"
      using contents_append_update by auto
    then have "tps23 ! j |:=| \<box> = (\<lfloor>replicate (first1 xs) \<one>\<rfloor>, Suc (first1 xs))"
      using contents_append_blanks by (metis replicate_0 replicate_Suc)
    moreover have "tps24 ! j = (\<lfloor>replicate (first1 xs) \<one>\<rfloor>, Suc (first1 xs))"
      using tps24_def jk by simp
    ultimately show ?thesis
      using tps23_def tps24_def by auto
  qed
qed

corollary tm24' [transforms_intros]:
  assumes "ttt = 2" and "tps' = tps0[j := (\<lfloor>ndecr xs\<rfloor>, Suc (first1 xs))]"
  shows "transforms tm24 tps2 ttt tps'"
proof -
  have "tps24 = tps0[j := (\<lfloor>ndecr xs\<rfloor>, Suc (first1 xs))]"
    using tps24_def jk ndecr_def first1_eq xs by simp
  then show ?thesis
    using assms tm24 by simp
qed

end  (* context read tps2 ! j = 0 *)

context
  assumes read_tps2': "read tps2 ! j \<noteq> \<box>"
begin

lemma first1_neq: "first1 xs \<noteq> length xs - 1"
proof (rule ccontr)
  assume eq: "\<not> first1 xs \<noteq> length xs - 1"

  have "tps2 ! j = (\<lfloor>replicate (first1 xs) \<one> @ [\<zero>] @ drop (Suc (first1 xs)) xs\<rfloor>, Suc (Suc (first1 xs)))"
      (is "_ = (\<lfloor>?zs\<rfloor>, ?i)")
    using tps2_def jk by simp
  have "length ?zs = length xs"
    using first1 by simp
  then have "Suc (Suc (first1 xs)) = Suc (length ?zs)"
    using xs eq by simp
  then have *: "\<lfloor>?zs\<rfloor> ?i = 0"
    using contents_outofbounds by simp

  have "read tps2 ! j = \<lfloor>?zs\<rfloor> ?i"
    using tps2_def jk tapes_at_read'[of j tps2] by simp
  then have "\<lfloor>?zs\<rfloor> ?i \<noteq> \<box>"
    using read_tps2' by simp
  then show False
    using * by simp
qed

lemma tps2: "tps2 = tps0[j := (\<lfloor>ndecr xs\<rfloor>, Suc (Suc (first1 xs)))]"
  using tps2_def ndecr_def first1_neq xs by simp

end  (* context read tps2 ! j \<noteq> 0 *)

lemma tm25 [transforms_intros]:
  assumes "ttt = (if read tps2 ! j = \<box> then 4 else 1)"
  shows "transforms tm25 tps2 ttt tps5"
  unfolding tm25_def by (tform tps: tps2 tps5_def time: assms)

lemma tm5 [transforms_intros]:
  assumes "ttt = first1 xs + 2 + (if read tps2 ! j = \<box> then 4 else 1)"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def by (tform time: assms)

definition "tps6 \<equiv> tps0
  [j := (\<lfloor>ndecr xs\<rfloor>, 1)]"

lemma tm6:
  assumes "ttt = first1 xs + 2 + (if read tps2 ! j = \<box> then 4 else 1) + (tps5 :#: j + 2)"
  shows "transforms tm6 tps0 ttt tps6"
  unfolding tm6_def
proof (tform tps: tps5_def tps6_def jk time: assms)
  show "clean_tape (tps5 ! j)"
  proof -
    have "tps5 ::: j = \<lfloor>ndecr xs\<rfloor>"
      using tps5_def jk by simp
    moreover have "bit_symbols (ndecr xs)"
      using canonical_ndecr can canonical_def by simp
    ultimately show ?thesis
      using One_nat_def Suc_1 Suc_le_lessD clean_contents_proper
      by (metis contents_clean_tape' lessI one_less_numeral_iff semiring_norm(77))
  qed
qed

lemma tm6' [transforms_intros]:
  assumes "ttt = 2 * first1 xs + 9"
  shows "transforms tm6 tps0 ttt tps6"
proof -
  let ?ttt = "first1 xs + 2 + (if read tps2 ! j = \<box> then 4 else 1) + (tps5 :#: j + 2)"
  have "tps5 :#: j = (if read tps2 ! j = \<box> then Suc (first1 xs) else Suc (Suc (first1 xs)))"
    using tps5_def jk by simp
  then have "?ttt \<le> ttt"
    using assms by simp
  then show ?thesis
    using tm6 transforms_monotone assms by simp
qed

end  (* context read tps0 ! j \<noteq> 0 *)

definition "tps7 \<equiv> tps0[j := (\<lfloor>ndecr xs\<rfloor>, 1)]"

lemma tm7:
  assumes "ttt = 8 + 2 * length xs"
  shows "transforms tm7 tps0 ttt tps7"
  unfolding tm7_def
proof (tform tps: tps6_def tps7_def time: assms)
  show "tps7 = tps0" if "read tps0 ! j = \<box>"
    using that ndecr_def tps0 tps7_def xs_Nil jk by (simp add: list_update_same_conv)
  show "2 * first1 xs + 9 + 1 \<le> ttt" if "read tps0 ! j \<noteq> \<box>"
  proof -
    have "length xs > 0"
      using that xs by simp
    then show ?thesis
      using first1(1) that assms by simp
  qed
qed

end  (* context *)

end  (* locale *)

lemma transforms_tm_decrI [transforms_intros]:
  fixes tps tps' :: "tape list" and n :: nat and k ttt :: nat
  assumes "j < k" "length tps = k"
  assumes "tps ! j = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 8 + 2 * nlength n"
  assumes "tps' = tps[j := (\<lfloor>n - 1\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_decr j) tps ttt tps'"
proof -
  let ?xs = "canrepr n"
  have can: "canonical ?xs"
    using canonical_canrepr by simp
  have tps0: "tps ! j = (\<lfloor>?xs\<rfloor>, 1)"
    using assms by simp
  have tps': "tps' = tps[j := (\<lfloor>ndecr ?xs\<rfloor>, 1)]"
    using ndecr assms(5) by (metis canrepr canreprI can canonical_ndecr)
  interpret loc: turing_machine_decr j .
  have "transforms loc.tm7 tps ttt tps'"
    using loc.tm7 loc.tps7_def by (metis assms(1,2,4) can tps' tps0)
  then show ?thesis
    using loc.tm7_eq_tm_decr by simp
qed


subsection \<open>Addition\<close>

text \<open>
In this section we construct a Turing machine that adds two numbers in canonical
representation each given on a separate tape and overwrites the second number
with the sum. The TM implements the common algorithm with carry starting from
the least significant digit.

Given two symbol sequences @{term xs} and @{term ys} representing numbers, the
next function computes the carry bit that occurs in the $i$-th position. For the
least significant position, 0, there is no carry (that is, it is 0); for
position $i + 1$ the carry is the sum of the bits of @{term xs} and @{term ys}
in position $i$ and the carry for position $i$. The function gives the carry as
symbol \textbf{0} or \textbf{1}, except for position 0, where it is the start
symbol~$\triangleright$. The start symbol represents the same bit as the
symbol~\textbf{0} as defined by @{const todigit}.  The reason for this special
treatment is that the TM will store the carry on a memorization tape
(see~Section~\ref{s:tm-memorizing}), which initially contains the start symbol.
\<close>

fun carry :: "symbol list \<Rightarrow> symbol list \<Rightarrow> nat \<Rightarrow> symbol" where
  "carry xs ys 0 = 1" |
  "carry xs ys (Suc i) = tosym ((todigit (digit xs i) + todigit (digit ys i) + todigit (carry xs ys i)) div 2)"

text \<open>
The next function specifies the $i$-th digit of the sum.
\<close>

definition sumdigit :: "symbol list \<Rightarrow> symbol list \<Rightarrow> nat \<Rightarrow> symbol" where
  "sumdigit xs ys i \<equiv> tosym ((todigit (digit xs i) + todigit (digit ys i) + todigit (carry xs ys i)) mod 2)"

lemma carry_sumdigit: "todigit (sumdigit xs ys i) + 2 * (todigit (carry xs ys (Suc i))) =
    todigit (carry xs ys i) + todigit (digit xs i) + todigit (digit ys i)"
  using sumdigit_def by simp

lemma carry_sumdigit_eq_sum:
  "num xs + num ys =
   num (map (sumdigit xs ys) [0..<t]) + 2 ^ t * todigit (carry xs ys t) + 2 ^ t * num (drop t xs) + 2 ^ t * num (drop t ys)"
proof (induction t)
  case 0
  then show ?case
    using num_def by simp
next
  case (Suc t)
  let ?z = "sumdigit xs ys"
  let ?c = "carry xs ys"
  let ?zzz = "map ?z [0..<Suc t]"
  have "num (take (Suc t) ?zzz) = num (take t ?zzz) + 2 ^ t * todigit (digit ?zzz t)"
    using num_take_Suc by blast
  moreover have "take (Suc t) ?zzz = map (sumdigit xs ys) [0..<Suc t]"
    by simp
  moreover have "take t ?zzz = map (sumdigit xs ys) [0..<t]"
    by simp
  ultimately have 1: "num (map ?z [0..<Suc t]) = num (map ?z [0..<t]) + 2 ^ t * todigit (digit ?zzz t)"
    by simp

  have 2: "digit ?zzz t = sumdigit xs ys t"
    using digit_def
    by (metis One_nat_def add_Suc diff_add_inverse length_map length_upt lessI nth_map_upt plus_1_eq_Suc)

  have "todigit (?z t) + 2 * (todigit (carry xs ys (Suc t))) =
      todigit (carry xs ys t) + todigit (digit xs t) + todigit (digit ys t)"
    using carry_sumdigit .
  then have "2 ^ t * (todigit (?z t) + 2 * (todigit (?c (Suc t)))) =
      2 ^ t * (todigit (?c t) + todigit (digit xs t) + todigit (digit ys t))"
    by simp
  then have "2 ^ t * todigit (?z t) + 2 ^ t * 2 * todigit (?c (Suc t)) =
      2 ^ t * todigit (?c t) + 2 ^ t * todigit (digit xs t) + 2 ^ t * todigit (digit ys t)"
    using add_mult_distrib2 by simp
  then have "num (map ?z [0..<t]) + 2 ^ t * (todigit (?z t)) + 2 ^ Suc t * (todigit (?c (Suc t))) =
      num (map ?z [0..<t]) + 2 ^ t * (todigit (?c t)) + 2 ^ t * (todigit (digit xs t)) + 2^t * (todigit (digit ys t))"
    by simp
  then have "num (map ?z [0..<Suc t]) + 2 ^ Suc t * (todigit (?c (Suc t))) =
      num (map ?z [0..<t]) + 2 ^ t * todigit (?c t) + 2 ^ t * todigit (digit xs t) + 2 ^ t * todigit (digit ys t)"
    using 1 2 by simp
  then have "num (map ?z [0..<Suc t]) + 2 ^ Suc t * (todigit (?c (Suc t))) +
        2 ^ Suc t * num (drop (Suc t) xs) + 2 ^ Suc t * num (drop (Suc t) ys) =
      num (map ?z [0..<t]) + 2 ^ t * todigit (?c t) + 2 ^ t * todigit (digit xs t) + 2 ^ t * todigit (digit ys t) +
        2 ^ Suc t * num (drop (Suc t) xs) + 2 ^ Suc t * num (drop (Suc t) ys)"
    by simp
  also have "... = num (map ?z [0..<t]) + 2 ^ t * (todigit (?c t)) +
        2 ^ t * (todigit (digit xs t) + 2 * num (drop (Suc t) xs)) + 2 ^ t * (todigit (digit ys t) + 2 * num (drop (Suc t) ys))"
    by (simp add: add_mult_distrib2)
  also have "... = num (map ?z [0..<t]) + 2 ^ t * (todigit (?c t)) +
        2 ^ t * num (drop t xs) + 2 ^ t * num (drop t ys)"
    using num_drop by metis
  also have "... = num xs + num ys"
    using Suc by simp
  finally show ?case
    by simp
qed

lemma carry_le:
  assumes "symbols_lt 4 xs" and "symbols_lt 4 ys"
  shows "carry xs ys t \<le> \<one>"
proof (induction t)
  case 0
  then show ?case
    by simp
next
  case (Suc t)
  then have "todigit (carry xs ys t) \<le> 1"
    by simp
  moreover have "todigit (digit xs t) \<le> 1"
    using assms(1) digit_def by auto
  moreover have "todigit (digit ys t) \<le> 1"
    using assms(2) digit_def by auto
  ultimately show ?case
    by simp
qed

lemma num_sumdigit_eq_sum:
  assumes "length xs \<le> n"
    and "length ys \<le> n"
    and "symbols_lt 4 xs"
    and "symbols_lt 4 ys"
  shows "num xs + num ys = num (map (sumdigit xs ys) [0..<Suc n])"
proof -
  have "num xs + num ys =
      num (map (sumdigit xs ys) [0..<Suc n]) + 2 ^ Suc n * todigit (carry xs ys (Suc n)) +
        2 ^ Suc n * num (drop (Suc n) xs) + 2 ^ Suc n * num (drop (Suc n) ys)"
    using carry_sumdigit_eq_sum by blast
  also have "... = num (map (sumdigit xs ys) [0..<Suc n]) + 2 ^ Suc n * todigit (carry xs ys (Suc n))"
    using assms(1,2) by (simp add: num_def)
  also have "... = num (map (sumdigit xs ys) [0..<Suc n])"
  proof -
    have "digit xs n = 0"
      using assms(1) digit_def by simp
    moreover have "digit ys n = 0"
      using assms(2) digit_def by simp
    ultimately have "(digit xs n + digit ys n + todigit (carry xs ys n)) div 2 = 0"
      using carry_le[OF assms(3,4), of n] by simp
    then show ?thesis
      by auto
  qed
  finally show ?thesis .
qed

lemma num_sumdigit_eq_sum':
  assumes "symbols_lt 4 xs" and "symbols_lt 4 ys"
  shows "num xs + num ys = num (map (sumdigit xs ys) [0..<Suc (max (length xs) (length ys))])"
  using assms num_sumdigit_eq_sum by simp

lemma num_sumdigit_eq_sum'':
  assumes "bit_symbols xs" and "bit_symbols ys"
  shows "num xs + num ys = num (map (sumdigit xs ys) [0..<Suc (max (length xs) (length ys))])"
proof -
  have "symbols_lt 4 xs"
    using assms(1) by auto
  moreover have "symbols_lt 4 ys"
    using assms(2) by auto
  ultimately show ?thesis
    using num_sumdigit_eq_sum' by simp
qed

lemma sumdigit_bit_symbols: "bit_symbols (map (sumdigit xs ys) [0..<t])"
  using sumdigit_def by auto

text \<open>
The core of the addition Turing machine is the following command. It scans the
symbols on tape $j_1$ and $j_2$ in lockstep until it reaches blanks on both
tapes. In every step it adds the symbols on both tapes and the symbol on the
last tape, which is a memorization tape storing the carry bit. The sum of these
three bits modulo~2 is written to tape $j_2$ and the new carry to the
memorization tape.
\<close>

definition cmd_plus :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> command" where
  "cmd_plus j1 j2 rs \<equiv>
    (if rs ! j1 = \<box> \<and> rs ! j2 = \<box> then 1 else 0,
     (map (\<lambda>j.
       if j = j1 then (rs ! j, Right)
       else if j = j2 then (tosym ((todigit (rs ! j1) + todigit (rs ! j2) + todigit (last rs)) mod 2), Right)
       else if j = length rs - 1 then (tosym ((todigit (rs ! j1) + todigit (rs ! j2) + todigit (last rs)) div 2), Stay)
       else (rs ! j, Stay)) [0..<length rs]))"

lemma sem_cmd_plus:
  assumes "j1 \<noteq> j2"
    and "j1 < k - 1"
    and "j2 < k - 1"
    and "j2 > 0"
    and "length tps = k"
    and "bit_symbols xs"
    and "bit_symbols ys"
    and "tps ! j1 = (\<lfloor>xs\<rfloor>, Suc t)"
    and "tps ! j2 = (\<lfloor>map (sumdigit xs ys) [0..<t] @ drop t ys\<rfloor>, Suc t)"
    and "last tps = \<lceil>carry xs ys t\<rceil>"
    and "rs = read tps"
    and "tps' = tps
      [j1 := tps!j1 |+| 1,
       j2 := tps!j2 |:=| sumdigit xs ys t |+| 1,
       length tps - 1 := \<lceil>carry xs ys (Suc t)\<rceil>]"
  shows "sem (cmd_plus j1 j2) (0, tps) = (if t < max (length xs) (length ys) then 0 else 1, tps')"
proof
  have "k \<ge> 2"
    using assms(3,4) by simp
  have rs1: "rs ! j1 = digit xs t"
    using assms(2,5,8,11) digit_def read_def contents_def by simp
  let ?zs = "map (sumdigit xs ys) [0..<t] @ drop t ys"
  have rs2: "rs ! j2 = digit ys t"
  proof (cases "t < length ys")
    case True
    then have "?zs ! t = ys ! t"
      by (simp add: nth_append)
    then show ?thesis
      using assms(3,5,9,11) digit_def read_def contents_def by simp
  next
    case False
    then have "length ?zs = t"
      by simp
    then have "\<lfloor>?zs\<rfloor> (Suc t) = \<box>"
      using False contents_def by simp
    then show ?thesis
      using digit_def read_def contents_def False assms(3,5,9,11) by simp
  qed
  have rs3: "last rs = carry xs ys t"
    using `k \<ge> 2` assms onesie_read onesie_def read_def read_length tapes_at_read'
    by (metis (no_types, lifting) diff_less last_conv_nth length_greater_0_conv less_one list.size(3) not_numeral_le_zero)
  have *: "tosym ((todigit (rs ! j1) + todigit (rs ! j2) + todigit (last rs)) mod 2) = sumdigit xs ys t"
    using rs1 rs2 rs3 sumdigit_def by simp

  have "\<not> (digit xs t = 0 \<and> digit ys t = 0)" if "t < max (length xs) (length ys)"
    using assms(6,7) digit_def that by auto
  then have 4: "\<not> (rs ! j1 = 0 \<and> rs ! j2 = 0)" if "t < max (length xs) (length ys)"
    using rs1 rs2 that by simp
  then have fst1: "fst (sem (cmd_plus j1 j2) (0, tps)) = fst (0, tps')" if "t < max (length xs) (length ys)"
    using that cmd_plus_def assms(11) by (smt (verit, ccfv_threshold) fst_conv prod.sel(2) sem)

  have "digit xs t = 0 \<and> digit ys t = 0" if "t \<ge> max (length xs) (length ys)"
    using that digit_def by simp
  then have 5: "rs ! j1 = \<box> \<and> rs ! j2 = \<box>" if "t \<ge> max (length xs) (length ys)"
    using rs1 rs2 that by simp
  then have "fst (sem (cmd_plus j1 j2) (0, tps)) = fst (1, tps')" if "t \<ge> max (length xs) (length ys)"
    using that cmd_plus_def assms(11) by (smt (verit, ccfv_threshold) fst_conv prod.sel(2) sem)
  then show "fst (sem (cmd_plus j1 j2) (0, tps)) = fst (if t < max (length xs) (length ys) then 0 else 1, tps')"
    using fst1 by (simp add: not_less)

  show "snd (sem (cmd_plus j1 j2) (0, tps)) = snd (if t < max (length xs) (length ys) then 0 else 1, tps')"
  proof (rule snd_semI)
    show "proper_command k (cmd_plus j1 j2)"
      using cmd_plus_def by simp
    show "length tps = k"
      using assms(5) .
    show "length tps' = k"
      using assms(5,12) by simp
    have len: "length (read tps) = k"
      by (simp add: assms read_length)
    show "act (cmd_plus j1 j2 (read tps) [!] j) (tps ! j) = tps' ! j"
      if "j < k" for j
    proof -
      have j: "j < length tps"
        using len that assms(5) by simp
      consider
          "j = j1"
        | "j \<noteq> j1 \<and> j = j2"
        | "j \<noteq> j1 \<and> j \<noteq> j2 \<and> j = length rs - 1"
        | "j \<noteq> j1 \<and> j \<noteq> j2 \<and> j \<noteq> length rs - 1"
        by auto
      then show ?thesis
      proof (cases)
        case 1
        then have "cmd_plus j1 j2 (read tps) [!] j = (read tps ! j, Right)"
          using that len cmd_plus_def by simp
        then have "act (cmd_plus j1 j2 (read tps) [!] j) (tps ! j) = tps ! j |+| 1"
          using act_Right[OF j] by simp
        moreover have "tps' ! j = tps ! j |+| 1"
          using assms(1,2,5,12) that 1 by simp
        ultimately show ?thesis
          by simp
      next
        case 2
        then have "cmd_plus j1 j2 (read tps) [!] j =
            (tosym ((todigit (rs ! j1) + todigit (rs ! j2) + todigit (last rs)) mod 2), Right)"
          using that len cmd_plus_def assms(11) by simp
        then have "cmd_plus j1 j2 (read tps) [!] j = (sumdigit xs ys t, Right)"
          using * by simp
        moreover have "tps' ! j2 = tps!j2 |:=| sumdigit xs ys t |+| 1"
          using assms(3,5,12) by simp
        ultimately show ?thesis
          using act_Right' 2 by simp
      next
        case 3
        then have "cmd_plus j1 j2 (read tps) [!] j =
            (tosym ((todigit (rs ! j1) + todigit (rs ! j2) + todigit (last rs)) div 2), Stay)"
          using that len cmd_plus_def assms(11) by simp
        then have "cmd_plus j1 j2 (read tps) [!] j = (carry xs ys (Suc t), Stay)"
          using rs1 rs2 rs3 by simp
        moreover have "tps' ! (length tps - 1) = \<lceil>carry xs ys (Suc t)\<rceil>"
          using 3 assms(5,11,12) len that by simp
        ultimately show ?thesis
          using 3 act_onesie assms(3,5,10,11) len
          by (metis add_diff_inverse_nat last_length less_nat_zero_code nat_diff_split_asm plus_1_eq_Suc)
      next
        case 4
        then have "cmd_plus j1 j2 (read tps) [!] j = (read tps ! j, Stay)"
          using that len cmd_plus_def assms(11) by simp
        then have "act (cmd_plus j1 j2 (read tps) [!] j) (tps ! j) = tps ! j"
          using act_Stay[OF j] by simp
        moreover have "tps' ! j = tps ! j"
          using that 4 len assms(5,11,12) by simp
        ultimately show ?thesis
          by simp
      qed
    qed
  qed
qed

lemma contents_map_append_drop:
  "\<lfloor>map f [0..<t] @ drop t zs\<rfloor>(Suc t := f t) = \<lfloor>map f [0..<Suc t] @ drop (Suc t) zs\<rfloor>"
proof (cases "t < length zs")
  case lt: True
  then have t_lt: "t < length (map f [0..<t] @ drop t zs)"
    by simp
  show ?thesis
  proof
    fix x
    consider
        "x = 0"
      | "x > 0 \<and> x < Suc t"
      | "x = Suc t"
      | "x > Suc t \<and> x \<le> length zs"
      | "x > Suc t \<and> x > length zs"
      by linarith
    then show "(\<lfloor>map f [0..<t] @ drop t zs\<rfloor>(Suc t := f t)) x =
        \<lfloor>map f [0..<Suc t] @ drop (Suc t) zs\<rfloor> x"
        (is "?lhs x = ?rhs x")
    proof (cases)
      case 1
      then show ?thesis
        using contents_def by simp
    next
      case 2
      then have "?lhs x = (map f [0..<t] @ drop t zs) ! (x - 1)"
        using contents_def by simp
      moreover have "x - 1 < t"
        using 2 by auto
      ultimately have left: "?lhs x = f (x - 1)"
        by (metis add.left_neutral diff_zero length_map length_upt nth_append nth_map_upt)
      have "?rhs x = (map f [0..<Suc t] @ drop (Suc t) zs) ! (x - 1)"
        using 2 contents_def by simp
      moreover have "x - 1 < Suc t"
        using 2 by auto
      ultimately have "?rhs x = f (x - 1)"
        by (metis diff_add_inverse diff_zero length_map length_upt nth_append nth_map_upt)
      then show ?thesis
        using left by simp
    next
      case 3
      then show ?thesis
        using contents_def lt
        by (smt (z3) One_nat_def Suc_leI add_Suc append_take_drop_id diff_Suc_1 diff_zero fun_upd_same
          length_append length_map length_take length_upt lessI min_absorb2 nat.simps(3) nth_append nth_map_upt plus_1_eq_Suc)
    next
      case 4
      then have "?lhs x = \<lfloor>map f [0..<t] @ drop t zs\<rfloor> x"
        using contents_def by simp
      then have "?lhs x = (map f [0..<t] @ drop t zs) ! (x - 1)"
        using 4 contents_def by simp
      then have left: "?lhs x = drop t zs ! (x - 1 - t)"
        using 4
        by (metis Suc_lessE diff_Suc_1 length_map length_upt less_Suc_eq_le less_or_eq_imp_le minus_nat.diff_0 not_less_eq nth_append)
      have "x \<le> length (map f [0..<Suc t] @ drop (Suc t) zs)"
        using 4 lt by auto
      moreover have "x > 0"
        using 4 by simp
      ultimately have "?rhs x = (map f [0..<Suc t] @ drop (Suc t) zs) ! (x - 1)"
        using 4 contents_inbounds by simp
      moreover have "x - 1 \<ge> Suc t"
        using 4 by auto
      ultimately have "?rhs x = drop (Suc t) zs ! (x - 1 - Suc t)"
        by (metis diff_zero leD length_map length_upt nth_append)
      then show ?thesis
        using left 4 by (metis Cons_nth_drop_Suc Suc_diff_Suc diff_Suc_eq_diff_pred lt nth_Cons_Suc)
    next
      case 5
      then show ?thesis
        using lt contents_def by auto
    qed
  qed
next
  case False
  moreover have "\<lfloor>map f [0..<t]\<rfloor>(Suc t := f t) = \<lfloor>map f [0..<Suc t]\<rfloor>"
  proof
    fix x
    show "(\<lfloor>map f [0..<t]\<rfloor>(Suc t := f t)) x = \<lfloor>map f [0..<Suc t]\<rfloor> x"
    proof (cases "x < Suc t")
      case True
      then show ?thesis
        using contents_def
        by (smt (verit, del_insts) diff_Suc_1 diff_zero fun_upd_apply length_map length_upt less_Suc_eq_0_disj
          less_Suc_eq_le less_imp_le_nat nat_neq_iff nth_map_upt)
    next
      case ge: False
      show ?thesis
      proof (cases "x = Suc t")
        case True
        then show ?thesis
          using contents_def
          by (metis One_nat_def add_Suc diff_Suc_1 diff_zero fun_upd_same ge le_eq_less_or_eq length_map
            length_upt lessI less_Suc_eq_0_disj nth_map_upt plus_1_eq_Suc)
      next
        case False
        then have "x > Suc t"
          using ge by simp
        then show ?thesis
          using contents_def by simp
      qed
    qed
  qed
  ultimately show ?thesis
    by simp
qed

corollary sem_cmd_plus':
  assumes "j1 \<noteq> j2"
    and "j1 < k - 1"
    and "j2 < k - 1"
    and "j2 > 0"
    and "length tps = k"
    and "bit_symbols xs"
    and "bit_symbols ys"
    and "tps ! j1 = (\<lfloor>xs\<rfloor>, Suc t)"
    and "tps ! j2 = (\<lfloor>map (sumdigit xs ys) [0..<t] @ drop t ys\<rfloor>, Suc t)"
    and "last tps = \<lceil>carry xs ys t\<rceil>"
    and "tps' = tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc (Suc t)),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<Suc t] @ drop (Suc t) ys\<rfloor>, Suc (Suc t)),
       length tps - 1 := \<lceil>carry xs ys (Suc t)\<rceil>]"
  shows "sem (cmd_plus j1 j2) (0, tps) = (if Suc t \<le> max (length xs) (length ys) then 0 else 1, tps')"
proof -
  have "tps ! j1 |+| 1 = (\<lfloor>xs\<rfloor>, Suc (Suc t))"
    using assms(8) by simp
  moreover have "tps ! j2 |:=| sumdigit xs ys t |+| 1 =
      (\<lfloor>map (sumdigit xs ys) [0..<Suc t] @ drop (Suc t) ys\<rfloor>, Suc (Suc t))"
    using contents_map_append_drop assms(9) by simp
  ultimately show ?thesis
    using sem_cmd_plus[OF assms(1-10)] assms(11) by auto
qed

text \<open>
The next Turing machine comprises just the command @{const cmd_plus}. It
overwrites tape $j_2$ with the sum of the numbers on tape $j_1$ and $j_2$. The
carry bit is maintained on the last tape.
\<close>

definition tm_plus :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_plus j1 j2 \<equiv> [cmd_plus j1 j2]"

lemma tm_plus_tm:
  assumes "j2 > 0" and "k \<ge> 2" and "G \<ge> 4"
  shows "turing_machine k G (tm_plus j1 j2)"
  unfolding tm_plus_def using assms(1-3) cmd_plus_def turing_machine_def by auto

lemma tm_plus_immobile:
  fixes k :: nat
  assumes "j1 < k" and "j2 < k"
  shows "immobile (tm_plus j1 j2) k (Suc k)"
proof -
  let ?M = "tm_plus j1 j2"
  { fix q :: nat and rs :: "symbol list"
    assume q: "q < length ?M"
    assume rs: "length rs = Suc k"
    then have len: "length rs - 1 = k"
      by simp
    have neq: "k \<noteq> j1" "k \<noteq> j2"
      using assms by simp_all
    have "?M ! q = cmd_plus j1 j2"
      using tm_plus_def q by simp
    moreover have "(cmd_plus j1 j2) rs [!] k =
        (tosym ((todigit (rs ! j1) + todigit (rs ! j2) + todigit (last rs)) div 2), Stay)"
      using cmd_plus_def rs len neq by fastforce
    ultimately have "(cmd_plus j1 j2) rs [~] k = Stay"
      by simp
  }
  then show ?thesis
    by (simp add: immobile_def tm_plus_def)
qed

lemma execute_tm_plus:
  assumes "j1 \<noteq> j2"
    and "j1 < k - 1"
    and "j2 < k - 1"
    and "j2 > 0"
    and "length tps = k"
    and "bit_symbols xs"
    and "bit_symbols ys"
    and "t \<le> Suc (max (length xs) (length ys))"
    and "tps ! j1 = (\<lfloor>xs\<rfloor>, 1)"
    and "tps ! j2 = (\<lfloor>ys\<rfloor>, 1)"
    and "last tps = \<lceil>\<triangleright>\<rceil>"
  shows "execute (tm_plus j1 j2) (0, tps) t =
    (if t \<le> max (length xs) (length ys) then 0 else 1, tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc t),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<t] @ drop t ys\<rfloor>, Suc t),
       length tps - 1 := \<lceil>carry xs ys t\<rceil>])"
  using assms(8)
proof (induction t)
  case 0
  have "carry xs ys 0 = 1"
    by simp
  moreover have "map (sumdigit xs ys) [0..<0] @ drop 0 ys = ys"
    by simp
  ultimately have "tps = tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc 0),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<0] @ drop 0 ys\<rfloor>, Suc 0),
       length tps - 1 := \<lceil>carry xs ys 0\<rceil>]"
    using assms
    by (metis One_nat_def add_diff_inverse_nat last_length less_nat_zero_code
      list_update_id nat_diff_split_asm plus_1_eq_Suc)
  then show ?case
    by simp
next
  case (Suc t)
  let ?M = "tm_plus j1 j2"
  have "execute ?M (0, tps) (Suc t) = exe ?M (execute ?M (0, tps) t)"
      (is "_ = exe ?M ?cfg")
    by simp
  also have "... = sem (cmd_plus j1 j2) ?cfg"
    using Suc tm_plus_def exe_lt_length by simp
  also have "... = (if Suc t \<le> max (length xs) (length ys) then 0 else 1, tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc (Suc t)),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<Suc t] @ drop (Suc t) ys\<rfloor>, Suc (Suc t)),
       length tps - 1 := \<lceil>carry xs ys (Suc t)\<rceil>])"
  proof -
    let ?tps = "tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc t),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<t] @ drop t ys\<rfloor>, Suc t),
       length tps - 1 := \<lceil>carry xs ys t\<rceil>]"
    let ?tps' = "?tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc (Suc t)),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<Suc t] @ drop (Suc t) ys\<rfloor>, Suc (Suc t)),
       length tps - 1 := \<lceil>carry xs ys (Suc t)\<rceil>]"
    have cfg: "?cfg = (0, ?tps)"
      using Suc by simp
    have tps_k: "length ?tps = k"
      using assms(2,3,5) by simp
    have tps_j1: "?tps ! j1 = (\<lfloor>xs\<rfloor>, Suc t)"
      using assms(1-3,5) by simp
    have tps_j2: "?tps ! j2 = (\<lfloor>map (sumdigit xs ys) [0..<t] @ drop t ys\<rfloor>, Suc t)"
      using assms(1-3,5) by simp
    have tps_last: "last ?tps = \<lceil>carry xs ys t\<rceil>"
      using assms
      by (metis One_nat_def carry.simps(1) diff_Suc_1 last_list_update length_list_update list_update_nonempty prod.sel(2) tps_j1)
    then have "sem (cmd_plus j1 j2) (0, ?tps) = (if Suc t \<le> max (length xs) (length ys) then 0 else 1, ?tps')"
      using sem_cmd_plus'[OF assms(1-4) tps_k assms(6,7) tps_j1 tps_j2 tps_last] assms(1-3)
      by (smt (verit, best) Suc.prems Suc_lessD assms(5) tps_k)
    then have "sem (cmd_plus j1 j2) ?cfg = (if Suc t \<le> max (length xs) (length ys) then 0 else 1, ?tps')"
      using cfg by simp
    moreover have "?tps' = tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc (Suc t)),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<Suc t] @ drop (Suc t) ys\<rfloor>, Suc (Suc t)),
       length tps - 1 := \<lceil>carry xs ys (Suc t)\<rceil>]"
      using assms by (smt (z3) list_update_overwrite list_update_swap)
    ultimately show ?thesis
      by simp
  qed
  finally show ?case
    by simp
qed

lemma tm_plus_bounded_write:
  assumes "j1 < k - 1"
  shows "bounded_write (tm_plus j1 j2) (k - 1) 4"
  using assms cmd_plus_def tm_plus_def bounded_write_def by simp

lemma carry_max_length:
  assumes "bit_symbols xs" and "bit_symbols ys"
  shows "carry xs ys (Suc (max (length xs) (length ys))) = \<zero>"
proof -
  let ?t = "max (length xs) (length ys)"
  have "carry xs ys (Suc ?t) = tosym ((todigit (digit xs ?t) + todigit (digit ys ?t) + todigit (carry xs ys ?t)) div 2)"
    by simp
  then have "carry xs ys (Suc ?t) = tosym (todigit (carry xs ys ?t) div 2)"
    using digit_def by simp
  moreover have "carry xs ys ?t \<le> \<one>"
    using carry_le assms by fastforce
  ultimately show ?thesis
    by simp
qed

corollary execute_tm_plus_halt:
  assumes "j1 \<noteq> j2"
    and "j1 < k - 1"
    and "j2 < k - 1"
    and "j2 > 0"
    and "length tps = k"
    and "bit_symbols xs"
    and "bit_symbols ys"
    and "t = Suc (max (length xs) (length ys))"
    and "tps ! j1 = (\<lfloor>xs\<rfloor>, 1)"
    and "tps ! j2 = (\<lfloor>ys\<rfloor>, 1)"
    and "last tps = \<lceil>\<triangleright>\<rceil>"
  shows "execute (tm_plus j1 j2) (0, tps) t =
    (1, tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc t),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<t]\<rfloor>, Suc t),
       length tps - 1 := \<lceil>\<zero>\<rceil>])"
proof -
  have "execute (tm_plus j1 j2) (0, tps) t =
    (1, tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc t),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<t] @ drop t ys\<rfloor>, Suc t),
       length tps - 1 := \<lceil>carry xs ys t\<rceil>])"
    using assms(8) execute_tm_plus[OF assms(1-7) _ assms(9-11)] Suc_leI Suc_n_not_le_n lessI
    by presburger
  then have "execute (tm_plus j1 j2) (0, tps) t =
    (1, tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc t),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<t]\<rfloor>, Suc t),
       length tps - 1 := \<lceil>carry xs ys t\<rceil>])"
    using assms(8) by simp
  then show "execute (tm_plus j1 j2) (0, tps) t =
    (1, tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc t),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<t]\<rfloor>, Suc t),
       length tps - 1 := \<lceil>\<zero>\<rceil>])"
    using assms(8) carry_max_length[OF assms(6,7)] by metis
qed

lemma transforms_tm_plusI:
  assumes "j1 \<noteq> j2"
    and "j1 < k - 1"
    and "j2 < k - 1"
    and "j2 > 0"
    and "length tps = k"
    and "bit_symbols xs"
    and "bit_symbols ys"
    and "t = Suc (max (length xs) (length ys))"
    and "tps ! j1 = (\<lfloor>xs\<rfloor>, 1)"
    and "tps ! j2 = (\<lfloor>ys\<rfloor>, 1)"
    and "last tps = \<lceil>\<triangleright>\<rceil>"
    and "tps' = tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc t),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<t]\<rfloor>, Suc t),
       length tps - 1 := \<lceil>\<zero>\<rceil>]"
  shows "transforms (tm_plus j1 j2) tps t tps'"
  using assms execute_tm_plus_halt[OF assms(1-11)] tm_plus_def transforms_def transits_def
  by auto

text \<open>
The next Turing machine removes the memorization tape from @{const tm_plus}.
\<close>

definition tm_plus' :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_plus' j1 j2 \<equiv> cartesian (tm_plus j1 j2) 4"

lemma tm_plus'_tm:
  assumes "j2 > 0" and "k \<ge> 2" and "G \<ge> 4"
  shows "turing_machine k G (tm_plus' j1 j2)"
  unfolding tm_plus'_def using assms cartesian_tm tm_plus_tm by simp

lemma transforms_tm_plus'I [transforms_intros]:
  fixes k t :: nat and j1 j2 :: tapeidx and tps tps' :: "tape list" and xs zs :: "symbol list"
  assumes "j1 \<noteq> j2"
    and "j1 < k"
    and "j2 < k"
    and "j2 > 0"
    and "length tps = k"
    and "bit_symbols xs"
    and "bit_symbols ys"
    and "t = Suc (max (length xs) (length ys))"
    and "tps ! j1 = (\<lfloor>xs\<rfloor>, 1)"
    and "tps ! j2 = (\<lfloor>ys\<rfloor>, 1)"
    and "tps' = tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc t),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<t]\<rfloor>, Suc t)]"
  shows "transforms (tm_plus' j1 j2) tps t tps'"
proof -
  let ?tps = "tps @ [\<lceil>\<triangleright>\<rceil>]"
  let ?tps' = "?tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc t),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<t]\<rfloor>, Suc t),
       length ?tps - 1 := \<lceil>\<zero>\<rceil>]"
  let ?M = "tm_plus j1 j2"

  have 1: "length ?tps = Suc k"
    using assms(5) by simp
  have 2: "?tps ! j1 = (\<lfloor>xs\<rfloor>, 1)"
    by (simp add: assms(9) assms(2) assms(5) nth_append)
  have 3: "?tps ! j2 = (\<lfloor>ys\<rfloor>, 1)"
    by (simp add: assms(10) assms(3) assms(5) nth_append)
  have 4: "last ?tps = \<lceil>\<triangleright>\<rceil>"
    by simp
  have 5: "k \<ge> 2"
    using assms(3,4) by simp
  have "transforms (tm_plus j1 j2) ?tps t ?tps'"
    using transforms_tm_plusI[OF assms(1) _ _ assms(4) 1 assms(6,7,8) 2 3 4, of ?tps'] assms(2,3)
    by simp
  moreover have "?tps' = tps' @ [\<lceil>\<zero>\<rceil>]"
    using assms by (simp add: list_update_append)
  ultimately have "transforms (tm_plus j1 j2) (tps @ [\<lceil>\<triangleright>\<rceil>]) t (tps' @ [\<lceil>\<zero>\<rceil>])"
    by simp
  moreover have "turing_machine (Suc k) 4 ?M"
    using tm_plus_tm assms by simp
  moreover have "immobile ?M k (Suc k)"
    using tm_plus_immobile assms by simp
  moreover have "bounded_write (tm_plus j1 j2) k 4"
    using tm_plus_bounded_write[of j1 "Suc k"] assms(2) by simp
  ultimately have "transforms (cartesian (tm_plus j1 j2) 4) tps t tps'"
    using cartesian_transforms_onesie[where ?M="?M" and ?b=4] assms(5) 5
    by simp
  then show ?thesis
    using tm_plus'_def by simp
qed

text \<open>
The next Turing machine is the one we actually use to add two numbers. After
computing the sum by running @{const tm_plus'}, it removes trailing zeros
and performs a carriage return on the tapes $j_1$ and $j_2$.
\<close>

definition tm_add :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_add j1 j2 \<equiv>
    tm_plus' j1 j2 ;;
    tm_lconst_until j2 j2 {h. h \<noteq> \<zero> \<and> h \<noteq> \<box>} \<box> ;;
    tm_cr j1 ;;
    tm_cr j2"

lemma tm_add_tm:
  assumes "j2 > 0" and "k \<ge> 2" and "G \<ge> 4" and "j2 < k"
  shows "turing_machine k G (tm_add j1 j2)"
  unfolding tm_add_def using tm_plus'_tm tm_lconst_until_tm tm_cr_tm assms by simp

locale turing_machine_add =
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> tm_plus' j1 j2"
definition "tm2 \<equiv> tm1 ;; tm_lconst_until j2 j2 {h. h \<noteq> \<zero> \<and> h \<noteq> \<box>} \<box>"
definition "tm3 \<equiv> tm2 ;; tm_cr j1"
definition "tm4 \<equiv> tm3 ;; tm_cr j2"

lemma tm4_eq_tm_add: "tm4 = tm_add j1 j2"
  using tm4_def tm3_def tm2_def tm1_def tm_add_def by simp

context
  fixes x y k :: nat and tps0 :: "tape list"
  assumes jk: "j1 \<noteq> j2" "j1 < k" "j2 < k" "j2 > 0" "k = length tps0"
  assumes tps0:
    "tps0 ! j1 = (\<lfloor>canrepr x\<rfloor>, 1)"
    "tps0 ! j2 = (\<lfloor>canrepr y\<rfloor>, 1)"
begin

abbreviation "xs \<equiv> canrepr x"

abbreviation "ys \<equiv> canrepr y"

lemma xs: "bit_symbols xs"
  using bit_symbols_canrepr by simp

lemma ys: "bit_symbols ys"
  using bit_symbols_canrepr by simp

abbreviation "n \<equiv> Suc (max (length xs) (length ys))"

abbreviation "m \<equiv> length (canrepr (num xs + num ys))"

definition "tps1 \<equiv> tps0
  [j1 := (\<lfloor>xs\<rfloor>, Suc n),
   j2 := (\<lfloor>map (sumdigit xs ys) [0..<n]\<rfloor>, Suc n)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = n"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: jk xs ys tps0 time: assms)
  show "tps1 = tps0
    [j1 := (\<lfloor>xs\<rfloor>, Suc ttt),
     j2 := (\<lfloor>map (sumdigit xs ys) [0..<ttt]\<rfloor>, Suc ttt)]"
    using tps1_def assms by simp
qed

definition "tps2 \<equiv> tps0
  [j1 := (\<lfloor>xs\<rfloor>, Suc n),
   j2 := (\<lfloor>canrepr (num xs + num ys)\<rfloor>, m)]"

lemma contents_canlen:
  assumes "bit_symbols zs"
  shows "\<lfloor>zs\<rfloor> (canlen zs) \<in> {h. h \<noteq> \<zero> \<and> \<box> < h}"
  using assms contents_def canlen_le_length canlen_one by auto

lemma tm2 [transforms_intros]:
  assumes "ttt = n + Suc (Suc n - canlen (map (sumdigit xs ys) [0..<n]))"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: tps1_def jk xs ys tps0)
  let ?zs = "map (sumdigit xs ys) [0..<n]"
  have "bit_symbols ?zs"
    using sumdigit_bit_symbols by blast
  let ?ln = "Suc n - canlen ?zs"
  have "lneigh (\<lfloor>?zs\<rfloor>, Suc n) {h. h \<noteq> \<zero> \<and> \<box> < h} ?ln"
  proof (rule lneighI)
    have "\<lfloor>?zs\<rfloor> (canlen ?zs) \<in> {h. h \<noteq> \<zero> \<and> \<box> < h}"
      using contents_canlen[OF `bit_symbols ?zs`] by simp
    moreover have "Suc n - ?ln = canlen ?zs"
      by (metis One_nat_def diff_Suc_1 diff_Suc_Suc diff_diff_cancel le_imp_less_Suc
        length_map length_upt less_imp_le_nat canlen_le_length)
    ultimately have "\<lfloor>?zs\<rfloor> (Suc n - ?ln) \<in> {h. h \<noteq> \<zero> \<and> \<box> < h}"
      by simp
    then show "fst (\<lfloor>?zs\<rfloor>, Suc n) (snd (\<lfloor>?zs\<rfloor>, Suc n) - ?ln) \<in> {h. h \<noteq> \<zero> \<and> \<box> < h}"
      by simp

    have "\<lfloor>?zs\<rfloor> (Suc n - n') \<in> {\<box>, \<zero>}" if "n' < ?ln" for n'
    proof (cases "Suc n - n' \<le> n")
      case True
      moreover have 1: "Suc n - n' > 0"
        using that by simp
      ultimately have "\<lfloor>?zs\<rfloor> (Suc n - n') = ?zs ! (Suc n - n' - 1)"
        using contents_def by simp
      moreover have "Suc n - n' - 1 < length ?zs"
        using that True by simp
      moreover have "Suc n - n' - 1 \<ge> canlen ?zs"
        using that by simp
      ultimately show ?thesis
        using canlen_at_ge[of ?zs] by simp
    next
      case False
      then show ?thesis
        by simp
    qed
    then have "\<lfloor>?zs\<rfloor> (Suc n - n') \<notin> {h. h \<noteq> \<zero> \<and> \<box> < h}" if "n' < ?ln" for n'
      using that by fastforce
    then show "fst (\<lfloor>?zs\<rfloor>, Suc n) (snd (\<lfloor>?zs\<rfloor>, Suc n) - n') \<notin> {h. h \<noteq> \<zero> \<and> \<box> < h}"
        if "n' < ?ln" for n'
      using that by simp
  qed
  then show "lneigh (tps1 ! j2) {h. h \<noteq> \<zero> \<and> h \<noteq> \<box>} ?ln"
    using assms tps1_def jk by simp
  show "Suc n - canlen (map (sumdigit xs ys) [0..<n]) \<le> tps1 :#: j2"
    "Suc n - canlen (map (sumdigit xs ys) [0..<n]) \<le> tps1 :#: j2"
    using assms tps1_def jk by simp_all

  have num_zs: "num ?zs = num xs + num ys"
    using assms num_sumdigit_eq_sum'' xs ys by simp
  then have canrepr: "canrepr (num xs + num ys) = take (canlen ?zs) ?zs"
    using canrepr_take_canlen `bit_symbols ?zs` by blast
  have len_canrepr: "length (canrepr (num xs + num ys)) = canlen ?zs"
    using num_zs length_canrepr_canlen sumdigit_bit_symbols by blast

  have "lconstplant (\<lfloor>?zs\<rfloor>, Suc n) \<box> ?ln =
      (\<lfloor>canrepr (num xs + num ys)\<rfloor>, m)"
    (is "lconstplant ?tp \<box> ?ln = _")
  proof -
    have "(if Suc n - ?ln < i \<and> i \<le> Suc n then \<box> else \<lfloor>?zs\<rfloor> i) =
        \<lfloor>take (canlen ?zs) ?zs\<rfloor> i"
        (is "?lhs = ?rhs")
      for i
    proof -
      consider
          "i = 0"
        | "i > 0 \<and> i \<le> canlen ?zs"
        | "i > canlen ?zs \<and> i \<le> Suc n"
        | "i > canlen ?zs \<and> i > Suc n"
        by linarith
      then show ?thesis
      proof (cases)
        case 1
        then show ?thesis
          by simp
      next
        case 2
        then have "i \<le> Suc n - ?ln"
          using canlen_le_length
          by (metis diff_diff_cancel diff_zero le_imp_less_Suc length_map length_upt less_imp_le_nat)
        then have lhs: "?lhs = \<lfloor>?zs\<rfloor> i"
          by simp
        have "take (canlen ?zs) ?zs ! (i - 1) = ?zs ! (i - 1)"
          using 2 by (metis Suc_diff_1 Suc_less_eq le_imp_less_Suc nth_take)
        then have "?rhs = \<lfloor>?zs\<rfloor> i"
          using 2 contents_inbounds len_canrepr local.canrepr not_le canlen_le_length
          by (metis add_diff_inverse_nat add_leE)
        then show ?thesis
          using lhs by simp
      next
        case 3
        then have "Suc n - ?ln < i \<and> i \<le> Suc n"
          by (metis diff_diff_cancel less_imp_le_nat less_le_trans)
        then have "?lhs = 0"
          by simp
        moreover have "?rhs = 0"
          using 3 contents_outofbounds len_canrepr canrepr by metis
        ultimately show ?thesis
          by simp
      next
        case 4
        then have "?lhs = 0"
          by simp
        moreover have "?rhs = 0"
          using 4 contents_outofbounds len_canrepr canrepr by metis
        ultimately show ?thesis
          by simp
      qed
    qed
    then have "(\<lambda>i. if Suc n - ?ln < i \<and> i \<le> Suc n then \<box> else \<lfloor>?zs\<rfloor> i) =
        \<lfloor>canrepr (num xs + num ys)\<rfloor>"
      using canrepr by simp
    moreover have "fst ?tp = \<lfloor>?zs\<rfloor>"
      by simp
    ultimately have "(\<lambda>i. if Suc n - ?ln < i \<and> i \<le> Suc n then 0 else fst ?tp i) =
        \<lfloor>canrepr (num xs + num ys)\<rfloor>" by metis
    moreover have "Suc n - ?ln = m"
      using len_canrepr
      by (metis add_diff_inverse_nat diff_add_inverse2 diff_is_0_eq diff_zero le_imp_less_Suc length_map
        length_upt less_imp_le_nat less_numeral_extra(3) canlen_le_length zero_less_diff)
    ultimately show ?thesis
      using lconstplant[of ?tp 0 ?ln] by simp
  qed
  then show "tps2 = tps1
    [j2 := tps1 ! j2 |-| ?ln,
     j2 := lconstplant (tps1 ! j2) 0 ?ln]"
    using tps2_def tps1_def jk by simp

  show "ttt = n + Suc ?ln"
    using assms by simp
qed

definition "tps3 \<equiv> tps0
  [j1 := (\<lfloor>xs\<rfloor>, 1),
   j2 := (\<lfloor>canrepr (num xs + num ys)\<rfloor>, m)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = n + Suc (Suc n - canlen (map (sumdigit xs ys) [0..<n])) + Suc n + 2"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: tps2_def jk xs ys tps0 time: assms tps2_def jk)
  show "clean_tape (tps2 ! j1)"
    using tps2_def jk xs
    by (metis clean_tape_ncontents nth_list_update_eq nth_list_update_neq)
  show "tps3 = tps2[j1 := tps2 ! j1 |#=| 1]"
    using tps3_def tps2_def jk by (simp add: list_update_swap)
qed

definition "tps4 \<equiv> tps0
  [j1 := (\<lfloor>xs\<rfloor>, 1),
   j2 := (\<lfloor>canrepr (num xs + num ys)\<rfloor>, 1)]"

lemma tm4:
  assumes "ttt = n + Suc (Suc n - canlen (map (sumdigit xs ys) [0..<n])) + Suc n + 2 + m + 2"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: tps3_def jk xs ys tps0 time: assms tps3_def jk)
  show "clean_tape (tps3 ! j2)"
    using tps3_def tps2_def jk tps0(1) by (metis clean_tape_ncontents list_update_id nth_list_update_eq)
  show "tps4 = tps3[j2 := tps3 ! j2 |#=| 1]"
    using tps4_def tps3_def jk by simp
qed

lemma tm4':
  assumes "ttt = 3 * max (length xs) (length ys) + 10"
  shows "transforms tm4 tps0 ttt tps4"
proof -
  let ?zs = "map (sumdigit xs ys) [0..<n]"
  have "num ?zs = num xs + num ys"
    using num_sumdigit_eq_sum'' xs ys by simp
  then have 1: "length (canrepr (num xs + num ys)) = canlen ?zs"
    using length_canrepr_canlen sumdigit_bit_symbols by blast
  moreover have "length ?zs = n"
    by simp
  ultimately have "m \<le> n"
    by (metis canlen_le_length)

  have "n + Suc (Suc n - canlen ?zs) + Suc n + 2 + m + 2 =
      n + Suc (Suc n - m) + Suc n + 2 + m + 2"
    using 1 by simp
  also have "... = n + Suc (Suc n - m) + Suc n + 4 + m"
    by simp
  also have "... = n + Suc (Suc n) - m + Suc n + 4 + m"
    using `m \<le> n` by simp
  also have "... = n + Suc (Suc n) + Suc n + 4"
    using `m \<le> n` by simp
  also have "... = 3 * n + 7"
    by simp
  also have "... = ttt"
    using assms by simp
  finally have "n + Suc (Suc n - canlen ?zs) + Suc n + 2 + m + 2 = ttt" .
  then show ?thesis
    using tm4 by simp
qed

definition "tps4' \<equiv> tps0
  [j2 := (\<lfloor>x + y\<rfloor>\<^sub>N, 1)]"

lemma tm4'':
  assumes "ttt = 3 * max (nlength x) (nlength y) + 10"
  shows "transforms tm4 tps0 ttt tps4'"
proof -
  have "canrepr (num xs + num ys) = canrepr (x + y)"
    by (simp add: canrepr)
  then show ?thesis
    using assms tps0(1) tps4'_def tps4_def tm4' by (metis list_update_id)
qed

end  (* context *)

end  (* locale *)

lemma transforms_tm_addI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes x y k ttt :: nat and tps tps' :: "tape list"
  assumes "j1 \<noteq> j2" "j1 < k" "j2 < k" "j2 > 0" "k = length tps"
  assumes
    "tps ! j1 = (\<lfloor>canrepr x\<rfloor>, 1)"
    "tps ! j2 = (\<lfloor>canrepr y\<rfloor>, 1)"
  assumes "ttt = 3 * max (nlength x) (nlength y) + 10"
  assumes "tps' = tps
    [j2 := (\<lfloor>x + y\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_add j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_add j1 j2 .
  show ?thesis
    using loc.tm4_eq_tm_add loc.tps4'_def loc.tm4'' assms by simp
qed


subsection \<open>Multiplication\<close>

text \<open>
In this section we construct a Turing machine that multiplies two numbers, each
on its own tape, and writes the result to another tape. It employs the common
algorithm for multiplication, which for binary numbers requires only doubling a
number and adding two numbers. For the latter we already have a TM; for the
former we are going to construct one.
\<close>


subsubsection \<open>The common algorithm\<close>

text \<open>
For two numbers given as symbol sequences @{term xs} and @{term ys}, the common
algorithm maintains an intermediate result, initialized with 0, and scans @{term
xs} starting from the most significant digit. In each step the intermediate
result is multiplied by two, and if the current digit of @{term xs} is @{text
\<one>}, the value of @{term ys} is added to the intermediate result.
\<close>

fun prod :: "symbol list \<Rightarrow> symbol list \<Rightarrow> nat \<Rightarrow> nat" where
  "prod xs ys 0 = 0" |
  "prod xs ys (Suc i) = 2 * prod xs ys i + (if xs ! (length xs - 1 - i) = 3 then num ys else 0)"

text \<open>
After $i$ steps of the algorithm, the intermediate result is the product of @{term ys}
and the $i$ most significant bits of @{term xs}.
\<close>

lemma prod:
  assumes "i \<le> length xs"
  shows "prod xs ys i = num (drop (length xs - i) xs) * num ys"
  using assms
proof (induction i)
  case 0
  then show ?case
    using num_def by simp
next
  case (Suc i)
  then have "i < length xs"
    by simp
  then have "drop (length xs - Suc i) xs = (xs ! (length xs - 1 - i)) # drop (length xs - i) xs"
    by (metis Cons_nth_drop_Suc Suc_diff_Suc diff_Suc_eq_diff_pred
      diff_Suc_less gr_implies_not0 length_greater_0_conv list.size(3))
  then show ?case
    using num_Cons Suc by simp
qed

text \<open>
After @{term "length xs"} steps, the intermediate result is the final result:
\<close>

corollary prod_eq_prod: "prod xs ys (length xs) = num xs * num ys"
  using prod by simp

definition prod' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "prod' x y i \<equiv> prod (canrepr x) (canrepr y) i"

lemma prod': "prod' x y (nlength x) = x * y"
  using prod_eq_prod prod'_def by (simp add: canrepr)


subsubsection \<open>Multiplying by two\<close>

text \<open>
Since we represent numbers with the least significant bit at the left, a
multiplication by two is a right shift with a \textbf{0} inserted as the least
significant digit. The next command implements the right shift. It scans the
tape $j$ and memorizes the current symbol on the last tape. It only writes the
symbols \textbf{0} and \textbf{1}.
\<close>

definition cmd_double :: "tapeidx \<Rightarrow> command" where
  "cmd_double j rs \<equiv>
    (if rs ! j = \<box> then 1 else 0,
     (map (\<lambda>i.
       if i = j then
         if last rs = \<triangleright> \<and> rs ! j = \<box> then (rs ! i, Right)
         else (tosym (todigit (last rs)), Right)
       else if i = length rs - 1 then (tosym (todigit (rs ! j)), Stay)
       else (rs ! i, Stay)) [0..<length rs]))"

lemma turing_command_double:
  assumes "k \<ge> 2" and "G \<ge> 4" and "j > 0" and "j < k - 1"
  shows "turing_command k 1 G (cmd_double j)"
proof
  show "\<And>gs. length gs = k \<Longrightarrow> length ([!!] cmd_double j gs) = length gs"
    using cmd_double_def by simp
  show "\<And>gs. length gs = k \<Longrightarrow> 0 < k \<Longrightarrow> cmd_double j gs [.] 0 = gs ! 0"
    using assms cmd_double_def by simp
  show "cmd_double j gs [.] j' < G"
    if "length gs = k" "\<And>i. i < length gs \<Longrightarrow> gs ! i < G" "j' < length gs"
    for j' gs
  proof -
    consider "j' = j" | "j' = k - 1" | "j' \<noteq> j \<and> j' \<noteq> k - 1"
      by auto
    then show ?thesis
    proof (cases)
      case 1
      then have "cmd_double j gs [!] j' =
         (if last gs = \<triangleright> \<and> gs ! j = \<box> then (gs ! j, Right)
          else (tosym (todigit (last gs)), Right))"
        using cmd_double_def assms(1,4) that(1) by simp
      then have "cmd_double j gs [.] j' =
         (if last gs = \<triangleright> \<and> gs ! j = \<box> then gs ! j else tosym (todigit (last gs)))"
        by simp
      then show ?thesis
        using that assms by simp
    next
      case 2
      then have "cmd_double j gs [!] j' = (tosym (todigit (gs ! j)), Stay)"
        using cmd_double_def assms(1,4) that(1) by simp
      then show ?thesis
        using assms by simp
    next
      case 3
      then show ?thesis
        using cmd_double_def assms that by simp
    qed
  qed
  show "\<And>gs. length gs = k \<Longrightarrow> [*] (cmd_double j gs) \<le> 1"
    using assms cmd_double_def by simp
qed

lemma sem_cmd_double_0:
  assumes "j < k"
    and "bit_symbols xs"
    and "i \<le> length xs"
    and "i > 0"
    and "length tps = Suc k"
    and "tps ! j = (\<lfloor>xs\<rfloor>, i)"
    and "tps ! k = \<lceil>z\<rceil>"
    and "tps' = tps [j := tps ! j |:=| tosym (todigit z) |+| 1, k := \<lceil>xs ! (i - 1)\<rceil>]"
  shows "sem (cmd_double j) (0, tps) = (0, tps')"
proof (rule semI)
  show "proper_command (Suc k) (cmd_double j)"
    using cmd_double_def by simp
  show "length tps = Suc k"
    using assms(5) .
  show "length tps' = Suc k"
    using assms(5,8) by simp
  show "fst (cmd_double j (read tps)) = 0"
    using assms contents_def cmd_double_def tapes_at_read'[of j tps]
    by (smt (verit, del_insts) One_nat_def Suc_le_lessD Suc_le_mono Suc_pred fst_conv
      less_imp_le_nat snd_conv zero_neq_numeral)
  show "act (cmd_double j (read tps) [!] j') (tps ! j') = tps' ! j'"
      if "j' < Suc k" for j'
  proof -
    define rs where "rs = read tps"
    then have rsj: "rs ! j = xs ! (i - 1)"
      using assms tapes_at_read' contents_inbounds
      by (metis fst_conv le_imp_less_Suc less_imp_le_nat snd_conv)
    then have rs23: "rs ! j = \<zero> \<or> rs ! j = \<one>"
      using assms by simp
    have lenrs: "length rs = Suc k"
      by (simp add: rs_def assms(5) read_length)
    consider "j' = j" | "j' = k" | "j' \<noteq> j \<and> j' \<noteq> k"
      by auto
    then show ?thesis
    proof (cases)
      case 1
      then have "j' < length rs"
        using lenrs that by simp
      then have "cmd_double j rs [!] j' =
         (if last rs = \<triangleright> \<and> rs ! j = \<box> then (rs ! j, Right)
          else (tosym (todigit (last rs)), Right))"
        using cmd_double_def that 1 by simp
      then have "cmd_double j rs [!] j' = (tosym (todigit (last rs)), Right)"
        using rs23 lenrs assms by auto
      moreover have "last rs = z"
        using lenrs assms(5,7) rs_def onesie_read[of z] tapes_at_read'[of _ tps]
        by (metis diff_Suc_1 last_conv_nth length_0_conv lessI old.nat.distinct(2))
      ultimately show ?thesis
        using act_Right' rs_def 1 assms(1,5,8) by simp
    next
      case 2
      then have "j' = length rs - 1" "j' \<noteq> j" "j' < length rs"
        using lenrs that assms(1) by simp_all
      then have "(cmd_double j rs) [!] j' = (tosym (todigit (rs ! j)), Stay)"
        using cmd_double_def by simp
      then have "(cmd_double j rs) [!] j' = (xs ! (i - 1), Stay)"
        using rsj rs23 by auto
      then show ?thesis
        using act_onesie rs_def 2 assms that by simp
    next
      case 3
      then have "j' \<noteq> length rs - 1" "j' \<noteq> j" "j' < length rs"
        using lenrs that by simp_all
      then have "(cmd_double j rs) [!] j' = (rs ! j', Stay)"
        using cmd_double_def by simp
      then show ?thesis
        using act_Stay rs_def assms that 3 by simp
    qed
  qed
qed

lemma sem_cmd_double_1:
  assumes "j < k"
    and "bit_symbols xs"
    and "i > length xs"
    and "length tps = Suc k"
    and "tps ! j = (\<lfloor>xs\<rfloor>, i)"
    and "tps ! k = \<lceil>z\<rceil>"
    and "tps' = tps
      [j := tps ! j |:=| (if z = \<triangleright> then \<box> else tosym (todigit z)) |+| 1,
       k := \<lceil>\<zero>\<rceil>]"
  shows "sem (cmd_double j) (0, tps) = (1, tps')"
proof (rule semI)
  show "proper_command (Suc k) (cmd_double j)"
    using cmd_double_def by simp
  show "length tps = Suc k"
    using assms(4) .
  show "length tps' = Suc k"
    using assms(4,7) by simp
  show "fst (cmd_double j (read tps)) = 1"
    using assms contents_def cmd_double_def tapes_at_read'[of j tps] by simp
  have "j < length tps"
    using assms by simp
  show "act (cmd_double j (read tps) [!] j') (tps ! j') = tps' ! j'"
      if "j' < Suc k" for j'
  proof -
    define rs where "rs = read tps"
    then have rsj: "rs ! j = \<box>"
      using tapes_at_read'[OF `j < length tps`] assms(1,3,4,5) by simp
    have lenrs: "length rs = Suc k"
      by (simp add: rs_def assms(4) read_length)
    consider "j' = j" | "j' = k" | "j' \<noteq> j \<and> j' \<noteq> k"
      by auto
    then show ?thesis
    proof (cases)
      case 1
      then have "j' < length rs"
        using lenrs that by simp
      then have "cmd_double j rs [!] j' =
         (if last rs = \<triangleright> \<and> rs ! j = \<box> then (rs ! j, Right)
          else (tosym (todigit (last rs)), Right))"
        using cmd_double_def that 1 by simp
      moreover have "last rs = z"
        using assms onesie_read rs_def tapes_at_read'
        by (metis diff_Suc_1 last_conv_nth length_0_conv lenrs lessI nat.simps(3))
      ultimately have "cmd_double j rs [!] j' =
         (if z = \<triangleright> then (\<box>, Right) else (tosym (todigit z), Right))"
        using rsj 1 by simp
      then show ?thesis
        using act_Right' rs_def 1 assms(1,4,7) by simp
    next
      case 2
      then have "j' = length rs - 1" "j' \<noteq> j" "j' < length rs"
        using lenrs that assms(1) by simp_all
      then have "(cmd_double j rs) [!] j' = (tosym (todigit (rs ! j)), Stay)"
        using cmd_double_def by simp
      then have "(cmd_double j rs) [!] j' = (2, Stay)"
        using rsj by auto
      then show ?thesis
        using act_onesie rs_def 2 assms that by simp
    next
      case 3
      then have "j' \<noteq> length rs - 1" "j' \<noteq> j" "j' < length rs"
        using lenrs that by simp_all
      then have "(cmd_double j rs) [!] j' = (rs ! j', Stay)"
        using cmd_double_def by simp
      then show ?thesis
        using act_Stay rs_def assms that 3 by simp
    qed
  qed
qed

text \<open>
The next Turing machine consists just of the command @{const cmd_double}.
\<close>

definition tm_double :: "tapeidx \<Rightarrow> machine" where
  "tm_double j \<equiv> [cmd_double j]"

lemma tm_double_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "j > 0" and "j < k - 1"
  shows "turing_machine k G (tm_double j)"
  using assms tm_double_def turing_command_double by auto

lemma execute_tm_double_0:
  assumes "j < k"
    and "bit_symbols xs"
    and "length xs > 0"
    and "length tps = Suc k"
    and "tps ! j = (\<lfloor>xs\<rfloor>, 1)"
    and "tps ! k = \<lceil>\<triangleright>\<rceil>"
    and "t \<ge> 1"
    and "t \<le> length xs"
  shows "execute (tm_double j) (0, tps) t =
    (0, tps [j := (\<lfloor>\<zero> # take (t - 1) xs @ drop t xs\<rfloor>, Suc t), k := \<lceil>xs ! (t - 1)\<rceil>])"
  using assms(7,8)
proof (induction t rule: nat_induct_at_least)
  case base
  have "execute (tm_double j) (0, tps) 1 = exe (tm_double j) (execute (tm_double j) (0, tps) 0)"
    by simp
  also have "... = sem (cmd_double j) (execute (tm_double j) (0, tps) 0)"
    using tm_double_def exe_lt_length by simp
  also have "... = sem (cmd_double j) (0, tps)"
    by simp
  also have "... = (0, tps [j := tps ! j |:=| tosym (todigit 1) |+| 1, k := \<lceil>xs ! (1 - 1)\<rceil>])"
    using assms(7,8) sem_cmd_double_0[OF assms(1-2) _ _ assms(4,5,6)] by simp
  also have "... = (0, tps [j := (\<lfloor>\<zero> # take (1 - 1) xs @ drop 1 xs\<rfloor>, Suc 1), k := \<lceil>xs ! (1 - 1)\<rceil>])"
  proof -
    have "tps ! j |:=| tosym (todigit 1) |+| 1 = (\<lfloor>xs\<rfloor>, 1) |:=| tosym (todigit 1) |+| 1"
      using assms(5) by simp
    also have "... = (\<lfloor>xs\<rfloor>(1 := tosym (todigit 1)), Suc 1)"
      by simp
    also have "... = (\<lfloor>xs\<rfloor>(1 := \<zero>), Suc 1)"
      by auto
    also have "... = (\<lfloor>\<zero> # drop 1 xs\<rfloor>, Suc 1)"
    proof -
      have "\<lfloor>\<zero> # drop 1 xs\<rfloor> = \<lfloor>xs\<rfloor>(1 := \<zero>)"
      proof
        fix i :: nat
        consider "i = 0" | "i = 1" | "i > 1 \<and> i \<le> length xs" | "i > length xs"
          by linarith
        then show "\<lfloor>\<zero> # drop 1 xs\<rfloor> i = (\<lfloor>xs\<rfloor>(1 := \<zero>)) i"
        proof (cases)
          case 1
          then show ?thesis
            by simp
        next
          case 2
          then show ?thesis
            by simp
        next
          case 3
          then have "\<lfloor>\<zero> # drop 1 xs\<rfloor> i = (\<zero> # drop 1 xs) ! (i - 1)"
            using assms(3) by simp
          also have "... = (drop 1 xs) ! (i - 2)"
            using 3 by (metis Suc_1 diff_Suc_eq_diff_pred nth_Cons_pos zero_less_diff)
          also have "... = xs ! (Suc (i - 2))"
            using 3 assms(5) by simp
          also have "... = xs ! (i - 1)"
            using 3 by (metis Suc_1 Suc_diff_Suc)
          also have "... = \<lfloor>xs\<rfloor> i"
            using 3 by simp
          also have "... = (\<lfloor>xs\<rfloor>(1 := \<zero>)) i"
            using 3 by simp
          finally show ?thesis .
        next
          case 4
          then show ?thesis
            by simp
        qed
      qed
      then show ?thesis
        by simp
    qed
    also have "... = (\<lfloor>\<zero> # take (1 - 1) xs @ drop 1 xs\<rfloor>, Suc 1)"
      by simp
    finally show ?thesis
      by auto
  qed
  finally show ?case .
next
  case (Suc t)
  let ?xs = "\<zero> # take (t - 1) xs @ drop t xs"
  let ?z = "xs ! (t - 1)"
  let ?tps = "tps
     [j := (\<lfloor>?xs\<rfloor>, Suc t),
      k := \<lceil>?z\<rceil>]"
  have lenxs: "length ?xs = length xs"
    using Suc by simp
  have 0: "?xs ! t = xs ! t"
  proof -
    have "t > 0"
      using Suc by simp
    then have "length (\<zero> # take (t - 1) xs) = t"
      using Suc by simp
    moreover have "length (drop t xs) > 0"
      using Suc by simp
    moreover have "drop t xs ! 0 = xs ! t"
      using Suc by simp
    ultimately have "((\<zero> # take (t - 1) xs) @ drop t xs) ! t = xs ! t"
      by (metis diff_self_eq_0 less_not_refl3 nth_append)
    then show ?thesis
      by simp
  qed
  have 1: "bit_symbols ?xs"
  proof -
    have "bit_symbols (take (t - 1) xs)"
      using assms(2) by simp
    moreover have "bit_symbols (drop t xs)"
      using assms(2) by simp
    moreover have "bit_symbols [\<zero>]"
      by simp
    ultimately have "bit_symbols ([\<zero>] @ take (t - 1) xs @ drop t xs)"
      using bit_symbols_append by presburger
    then show ?thesis
      by simp
  qed
  have 2: "Suc t \<le> length ?xs"
    using Suc by simp
  have 3: "Suc t > 0"
    using Suc by simp
  have 4: "length ?tps = Suc k"
    using assms by simp
  have 5: "?tps ! j = (\<lfloor>?xs\<rfloor>, Suc t)"
    by (simp add: Suc_lessD assms(1,4) nat_neq_iff)
  have 6: "?tps ! k = \<lceil>?z\<rceil>"
    by (simp add: assms(4))
  have "execute (tm_double j) (0, tps) (Suc t) = exe (tm_double j) (execute (tm_double j) (0, tps) t)"
    by simp
  also have "... = sem (cmd_double j) (execute (tm_double j) (0, tps) t)"
    using tm_double_def exe_lt_length Suc by simp
  also have "... = sem (cmd_double j) (0, ?tps)"
    using Suc by simp
  also have "... = (0, ?tps [j := ?tps ! j |:=| tosym (todigit ?z) |+| 1, k := \<lceil>?xs ! (Suc t - 1)\<rceil>])"
    using sem_cmd_double_0[OF assms(1) 1 2 3 4 5 6] by simp
  also have "... = (0, ?tps [j := ?tps ! j |:=| tosym (todigit ?z) |+| 1, k := \<lceil>xs ! (Suc t - 1)\<rceil>])"
    using 0 by simp
  also have "... = (0, tps [j := ?tps ! j |:=| tosym (todigit ?z) |+| 1, k := \<lceil>xs ! (Suc t - 1)\<rceil>])"
    using assms by (smt (z3) list_update_overwrite list_update_swap)
  also have "... = (0, tps [j := (\<lfloor>?xs\<rfloor>, Suc t) |:=| tosym (todigit ?z) |+| 1, k := \<lceil>xs ! (Suc t - 1)\<rceil>])"
    using 5 by simp
  also have "... = (0, tps
      [j := (\<lfloor>?xs\<rfloor>(Suc t := tosym (todigit ?z)), Suc (Suc t)),
       k := \<lceil>xs ! (Suc t - 1)\<rceil>])"
    by simp
  also have "... = (0, tps
      [j := (\<lfloor>2 # take (Suc t - 1) xs @ drop (Suc t) xs\<rfloor>, Suc (Suc t)),
       k := \<lceil>xs ! (Suc t - 1)\<rceil>])"
  proof -
    have "\<lfloor>?xs\<rfloor>(Suc t := tosym (todigit ?z)) = \<lfloor>\<zero> # take (Suc t - 1) xs @ drop (Suc t) xs\<rfloor>"
    proof
      fix i :: nat
      consider "i = 0" | "i > 0 \<and> i < Suc t" | "i = Suc t" | "i > Suc t \<and> i \<le> length xs" | "i > length xs"
        by linarith
      then show "(\<lfloor>?xs\<rfloor>(Suc t := tosym (todigit ?z))) i = \<lfloor>\<zero> # take (Suc t - 1) xs @ drop (Suc t) xs\<rfloor> i"
      proof (cases)
        case 1
        then show ?thesis
          by simp
      next
        case 2
        then have lhs: "(\<lfloor>?xs\<rfloor>(Suc t := tosym (todigit ?z))) i = ?xs ! (i - 1)"
          using lenxs Suc by simp
        have "\<lfloor>\<zero> # take (Suc t - 1) xs @ drop (Suc t) xs\<rfloor> i =
            (\<zero> # take (Suc t - 1) xs @ drop (Suc t) xs) ! (i - 1)"
          using Suc 2 by auto
        then have "\<lfloor>\<zero> # take (Suc t - 1) xs @ drop (Suc t) xs\<rfloor> i =
            ((\<zero> # take (Suc t - 1) xs) @ drop (Suc t) xs) ! (i - 1)"
          by simp
        moreover have "length (\<zero> # take (Suc t - 1) xs) = Suc t"
          using Suc.prems by simp
        ultimately have "\<lfloor>\<zero> # take (Suc t - 1) xs @ drop (Suc t) xs\<rfloor> i =
            (\<zero> # take (Suc t - 1) xs) ! (i - 1)"
          using 2 by (metis Suc_diff_1 Suc_lessD nth_append)
        also have "... = (\<zero> # take t xs) ! (i - 1)"
          by simp
        also have "... = (\<zero> # take (t - 1) xs @ [xs ! (t - 1)]) ! (i - 1)"
          using Suc by (metis Suc_diff_le Suc_le_lessD Suc_lessD diff_Suc_1 take_Suc_conv_app_nth)
        also have "... = ((\<zero> # take (t - 1) xs) @ [xs ! (t - 1)]) ! (i - 1)"
          by simp
        also have "... = (\<zero> # take (t - 1) xs) ! (i - 1)"
          using 2 Suc
          by (metis One_nat_def Suc_leD Suc_le_eq Suc_pred length_Cons length_take less_Suc_eq_le
            min_absorb2 nth_append)
        also have "... = ((\<zero> # take (t - 1) xs) @ drop t xs) ! (i - 1)"
          using 2 Suc
          by (metis Suc_diff_1 Suc_diff_le Suc_leD Suc_lessD diff_Suc_1 length_Cons length_take
            less_Suc_eq min_absorb2 nth_append)
        also have "... = ?xs ! (i - 1)"
          by simp
        finally have "\<lfloor>\<zero> # take (Suc t - 1) xs @ drop (Suc t) xs\<rfloor> i = ?xs ! (i - 1)" .
        then show ?thesis
          using lhs by simp
      next
        case 3
        moreover have "?z = \<zero> \<or> ?z = \<one>"
          using `bit_symbols ?xs` Suc assms(2) by (metis Suc_diff_le Suc_leD Suc_le_lessD diff_Suc_1)
        ultimately have lhs: "(\<lfloor>?xs\<rfloor>(Suc t := tosym (todigit ?z))) i = ?z"
          by auto
        have "\<lfloor>\<zero> # take (Suc t - 1) xs @ drop (Suc t) xs\<rfloor> i =
            \<lfloor>(\<zero> # take t xs) @ drop (Suc t) xs\<rfloor> (Suc t)"
          using 3 by simp
        also have "... = ((\<zero> # take t xs) @ drop (Suc t) xs) ! t"
          using 3 Suc by simp
        also have "... = (\<zero> # take t xs) ! t"
          using Suc by (metis Suc_leD length_Cons length_take lessI min_absorb2 nth_append)
        also have "... = xs ! (t - 1)"
          using Suc by simp
        finally have "\<lfloor>\<zero> # take (Suc t - 1) xs @ drop (Suc t) xs\<rfloor> i = ?z" .
        then show ?thesis
          using lhs by simp
      next
        case 4
        then have "(\<lfloor>?xs\<rfloor>(Suc t := tosym (todigit ?z))) i = \<lfloor>?xs\<rfloor> i"
          by simp
        also have "... = ?xs ! (i - 1)"
          using 4 by auto
        also have "... = ((\<zero> # take (t - 1) xs) @ drop t xs) ! (i - 1)"
          by simp
        also have "... = drop t xs ! (i - 1 - t)"
          using 4 Suc
          by (smt (verit, ccfv_threshold) Cons_eq_appendI Suc_diff_1 Suc_leD
            add_diff_cancel_right' bot_nat_0.extremum_uniqueI diff_diff_cancel
            length_append length_drop lenxs not_le not_less_eq nth_append)
        also have "... = xs ! (i - 1)"
          using 4 Suc by simp
        finally have lhs: "(\<lfloor>?xs\<rfloor>(Suc t := tosym (todigit ?z))) i = xs ! (i - 1)" .
        have "\<lfloor>\<zero> # take (Suc t - 1) xs @ drop (Suc t) xs\<rfloor> i =
            (\<zero> # take (Suc t - 1) xs @ drop (Suc t) xs) ! (i - 1)"
          using 4 by auto
        also have "... = ((\<zero> # take t xs) @ drop (Suc t) xs) ! (i - 1)"
          by simp
        also have "... = (drop (Suc t) xs) ! (i - 1 - Suc t)"
          using Suc 4
          by (smt (z3) Suc_diff_1 Suc_leD Suc_leI bot_nat_0.extremum_uniqueI length_Cons length_take
            min_absorb2 not_le nth_append)
        also have "... = xs ! (i - 1)"
          using Suc 4 Suc_lessE by fastforce
        finally have "\<lfloor>\<zero> # take (Suc t - 1) xs @ drop (Suc t) xs\<rfloor> i = xs ! (i - 1)" .
        then show ?thesis
          using lhs by simp
      next
        case 5
        then have "(\<lfloor>?xs\<rfloor>(Suc t := tosym (todigit ?z))) i = \<lfloor>?xs\<rfloor> i"
          using Suc by simp
        then have lhs: "(\<lfloor>?xs\<rfloor>(Suc t := tosym (todigit ?z))) i = \<box>"
          using 5 contents_outofbounds lenxs by simp
        have "length (\<zero> # take (Suc t - 1) xs @ drop (Suc t) xs) = length xs"
          using Suc by simp
        then have "\<lfloor>\<zero> # take (Suc t - 1) xs @ drop (Suc t) xs\<rfloor> i = \<box>"
          using 5 contents_outofbounds by simp
        then show ?thesis
          using lhs by simp
      qed
    qed
    then show ?thesis
      by simp
  qed
  finally show ?case .
qed

lemma execute_tm_double_1:
  assumes "j < k"
    and "bit_symbols xs"
    and "length xs > 0"
    and "length tps = Suc k"
    and "tps ! j = (\<lfloor>xs\<rfloor>, 1)"
    and "tps ! k = \<lceil>\<triangleright>\<rceil>"
  shows "execute (tm_double j) (0, tps) (Suc (length xs)) =
    (1, tps [j := (\<lfloor>\<zero> # xs\<rfloor>, length xs + 2), k := \<lceil>\<zero>\<rceil>])"
proof -
  let ?z = "xs ! (length xs - 1)"
  let ?xs = "\<zero> # take (length xs - 1) xs"
  have "?z \<noteq> \<triangleright>"
    using assms(2,3) by (metis One_nat_def Suc_1 diff_less less_Suc_eq not_less_eq numeral_3_eq_3)
  have z23: "?z = \<zero> \<or> ?z = \<one>"
    using assms(2,3) by (meson diff_less zero_less_one)
  have lenxs: "length ?xs = length xs"
    using assms(3) by (metis Suc_diff_1 diff_le_self length_Cons length_take min_absorb2)
  have 0: "bit_symbols ?xs"
    using assms(2) bit_symbols_append[of "[\<zero>]" "take (length xs - 1) xs"] by simp

  have "execute (tm_double j) (0, tps) (length xs) =
    (0, tps
      [j := (\<lfloor>\<zero> # take (length xs - 1) xs @ drop (length xs) xs\<rfloor>, Suc (length xs)),
       k := \<lceil>?z\<rceil>])"
    using execute_tm_double_0[OF assms(1-6), where ?t="length xs"] assms(3) by simp
  then have *: "execute (tm_double j) (0, tps) (length xs) =
    (0, tps [j := (\<lfloor>?xs\<rfloor>, Suc (length ?xs)), k := \<lceil>?z\<rceil>])"
    (is "_ = (0, ?tps)")
    using lenxs by simp

  let ?i = "Suc (length ?xs)"
  have 1: "?i > length ?xs"
    by simp
  have 2: "length ?tps = Suc k"
    using assms(4) by simp
  have 3: "?tps ! j = (\<lfloor>?xs\<rfloor>, ?i)"
    using assms(1,4) by simp
  have 4: "?tps ! k = \<lceil>?z\<rceil>"
    using assms(4) by simp

  have "execute (tm_double j) (0, tps) (Suc (length xs)) = exe (tm_double j) (0, ?tps)"
    using * by simp
  also have "... = sem (cmd_double j) (0, ?tps)"
    using tm_double_def exe_lt_length by simp
  also have "... = (1, ?tps
      [j := ?tps ! j |:=| (if ?z = \<triangleright> then \<box> else tosym (todigit ?z)) |+| 1,
       k := \<lceil>\<zero>\<rceil>])"
    using sem_cmd_double_1[OF assms(1) 0 1 2 3 4] by simp
  also have "... = (1, ?tps
      [j := ?tps ! j |:=| (tosym (todigit ?z)) |+| 1,
       k := \<lceil>\<zero>\<rceil>])"
    using `?z \<noteq> 1` by simp
  also have "... = (1, ?tps
      [j := (\<lfloor>?xs\<rfloor>, Suc (length ?xs)) |:=| (tosym (todigit ?z)) |+| 1,
       k := \<lceil>\<zero>\<rceil>])"
    using 3 by simp
  also have "... = (1, ?tps
      [j := (\<lfloor>?xs\<rfloor>, Suc (length ?xs)) |:=| ?z |+| 1,
       k := \<lceil>\<zero>\<rceil>])"
    using z23 One_nat_def Suc_1 add_2_eq_Suc' numeral_3_eq_3 by presburger
  also have "... = (1, tps
      [j := (\<lfloor>?xs\<rfloor>, Suc (length ?xs)) |:=| ?z |+| 1,
       k := \<lceil>\<zero>\<rceil>])"
    by (smt (z3) list_update_overwrite list_update_swap)
  also have "... = (1, tps
      [j := (\<lfloor>?xs\<rfloor>(Suc (length ?xs) := ?z), length ?xs + 2),
       k := \<lceil>\<zero>\<rceil>])"
    by simp
  also have "... = (1, tps
      [j := (\<lfloor>?xs\<rfloor>(Suc (length ?xs) := ?z), length xs + 2),
       k := \<lceil>\<zero>\<rceil>])"
    using lenxs by simp
  also have "... = (1, tps [j := (\<lfloor>\<zero> # xs\<rfloor>, length xs + 2), k := \<lceil>\<zero>\<rceil>])"
  proof -
    have "\<lfloor>?xs\<rfloor>(Suc (length ?xs) := ?z) = \<lfloor>\<zero> # xs\<rfloor>"
    proof
      fix i
      consider "i = 0" | "i > 0 \<and> i \<le> length xs" | "i = Suc (length xs)" | "i > Suc (length xs)"
        by linarith
      then show "(\<lfloor>?xs\<rfloor>(Suc (length ?xs) := ?z)) i = \<lfloor>\<zero> # xs\<rfloor> i"
      proof (cases)
        case 1
        then show ?thesis
          by simp
      next
        case 2
        then have "(\<lfloor>?xs\<rfloor>(Suc (length ?xs) := ?z)) i = \<lfloor>?xs\<rfloor> i"
          using lenxs by simp
        also have "... = ?xs ! (i - 1)"
          using 2 by auto
        also have "... = (\<zero> # xs) ! (i - 1)"
          using lenxs 2 assms(3) by (metis Suc_diff_1 Suc_le_lessD nth_take take_Suc_Cons)
        also have "... = \<lfloor>\<zero> # xs\<rfloor> i"
          using 2 by simp
        finally show ?thesis .
      next
        case 3
        then have lhs: "(\<lfloor>?xs\<rfloor>(Suc (length ?xs) := ?z)) i = ?z"
          using lenxs by simp
        have "\<lfloor>\<zero> # xs\<rfloor> i = (\<zero> # xs) ! (i - 1)"
          using 3 lenxs by simp
        also have "... = xs ! (i - 2)"
          using 3 assms(3) by simp
        also have "... = ?z"
          using 3 by simp
        finally have "\<lfloor>\<zero> # xs\<rfloor> i = ?z" .
        then show ?thesis
          using lhs by simp
      next
        case 4
        then show ?thesis
          using 4 lenxs by simp
      qed
    qed
    then show ?thesis
      by simp
  qed
  finally show ?thesis .
qed

lemma execute_tm_double_Nil:
  assumes "j < k"
    and "length tps = Suc k"
    and "tps ! j = (\<lfloor>[]\<rfloor>, 1)"
    and "tps ! k = \<lceil>\<triangleright>\<rceil>"
  shows "execute (tm_double j) (0, tps) (Suc 0) =
    (1, tps [j := (\<lfloor>[]\<rfloor>, 2), k := \<lceil>\<zero>\<rceil>])"
proof -
  have "execute (tm_double j) (0, tps) (Suc 0) = exe (tm_double j) (execute (tm_double j) (0, tps) 0)"
    by simp
  also have "... = exe (tm_double j) (0, tps)"
    by simp
  also have "... = sem (cmd_double j) (0, tps)"
    using tm_double_def exe_lt_length by simp
  also have "... = (1, tps
      [j := tps ! j |:=| (if (1::nat) = 1 then 0 else tosym (todigit 1)) |+| 1,
       k := \<lceil>\<zero>\<rceil>])"
    using sem_cmd_double_1[OF assms(1) _ _ assms(2-4)] by simp
  also have "... = (1, tps [j := tps ! j |:=| \<box> |+| 1, k := \<lceil>\<zero>\<rceil>])"
    by simp
  also have "... = (1, tps [j := (\<lfloor>[]\<rfloor>, 1) |:=| \<box> |+| 1, k := \<lceil>\<zero>\<rceil>])"
    using assms(3) by simp
  also have "... = (1, tps [j := (\<lfloor>[]\<rfloor>(1 := \<box>), 2), k := \<lceil>\<zero>\<rceil>])"
    by (metis fst_eqD one_add_one snd_eqD)
  also have "... = (1, tps [j := (\<lfloor>[]\<rfloor>, 2), k := \<lceil>\<zero>\<rceil>])"
    by (metis contents_outofbounds fun_upd_idem_iff list.size(3) zero_less_one)
  finally show ?thesis .
qed

lemma execute_tm_double:
  assumes "j < k"
    and "length tps = Suc k"
    and "tps ! j = (\<lfloor>canrepr n\<rfloor>, 1)"
    and "tps ! k = \<lceil>\<triangleright>\<rceil>"
  shows "execute (tm_double j) (0, tps) (Suc (length (canrepr n))) =
    (1, tps [j := (\<lfloor>canrepr (2 * n)\<rfloor>, length (canrepr n) + 2), k := \<lceil>\<zero>\<rceil>])"
proof (cases "n = 0")
  case True
  then have "canrepr n = []"
    using canrepr_0 by simp
  then show ?thesis
    using execute_tm_double_Nil[OF assms(1-2) _ assms(4)] assms(3) True
    by (metis add_2_eq_Suc' list.size(3) mult_0_right numeral_2_eq_2)
next
  case False
  let ?xs = "canrepr n"
  have "num (\<zero> # ?xs) = 2 * num ?xs"
    using num_Cons by simp
  then have "num (\<zero> # ?xs) = 2 * n"
    using canrepr by simp
  moreover have "canonical (\<zero> # ?xs)"
  proof -
    have "?xs \<noteq> []"
      using False canrepr canrepr_0 by metis
    then show ?thesis
      using canonical_Cons canonical_canrepr by simp
  qed
  ultimately have "canrepr (2 * n) = \<zero> # ?xs"
    using canreprI by blast
  then show ?thesis
    using execute_tm_double_1[OF assms(1) _ _ assms(2) _ assms(4)] assms(3) False canrepr canrepr_0 bit_symbols_canrepr
    by (metis length_greater_0_conv)
qed

lemma execute_tm_double_app:
  assumes "j < k"
    and "length tps = k"
    and "tps ! j = (\<lfloor>canrepr n\<rfloor>, 1)"
  shows "execute (tm_double j) (0, tps @ [\<lceil>\<triangleright>\<rceil>]) (Suc (length (canrepr n))) =
    (1, tps [j := (\<lfloor>canrepr (2 * n)\<rfloor>, length (canrepr n) + 2)] @ [\<lceil>\<zero>\<rceil>])"
proof -
  let ?tps = "tps @ [\<lceil>\<triangleright>\<rceil>]"
  have "length ?tps = Suc k"
    using assms(2) by simp
  moreover have "?tps ! j = (\<lfloor>canrepr n\<rfloor>, 1)"
    using assms(1,2,3) by (simp add: nth_append)
  moreover have "?tps ! k = \<lceil>\<triangleright>\<rceil>"
    using assms(2) by (simp add: nth_append)
  moreover have "tps [j := (\<lfloor>canrepr (2 * n)\<rfloor>, length (canrepr n) + 2)] @ [\<lceil>\<zero>\<rceil>] =
      ?tps [j := (\<lfloor>canrepr (2 * n)\<rfloor>, length (canrepr n) + 2), k := \<lceil>\<zero>\<rceil>]"
    using assms by (metis length_list_update list_update_append1 list_update_length)
  ultimately show ?thesis
    using assms execute_tm_double[OF assms(1), where ?tps="tps @ [\<lceil>\<triangleright>\<rceil>]"]
    by simp
qed

lemma transforms_tm_double:
  assumes "j < k"
    and "length tps = k"
    and "tps ! j = (\<lfloor>canrepr n\<rfloor>, 1)"
  shows "transforms (tm_double j)
    (tps @ [\<lceil>\<triangleright>\<rceil>])
    (Suc (length (canrepr n)))
    (tps [j := (\<lfloor>canrepr (2 * n)\<rfloor>, length (canrepr n) + 2)] @ [\<lceil>\<zero>\<rceil>])"
  using assms transforms_def transits_def tm_double_def execute_tm_double_app by auto

lemma tm_double_immobile:
  fixes k :: nat
  assumes "j > 0" and "j < k"
  shows "immobile (tm_double j) k (Suc k)"
proof -
  let ?M = "tm_double j"
  { fix q :: nat and rs :: "symbol list"
    assume q: "q < length ?M"
    assume rs: "length rs = Suc k"
    then have len: "length rs - 1 = k"
      by simp
    have neq: "k \<noteq> j"
      using assms(2) by simp
    have "?M ! q = cmd_double j"
      using tm_double_def q by simp
    moreover have "(cmd_double j) rs [!] k = (tosym (todigit (rs ! j)), Stay)"
      using cmd_double_def rs len neq by fastforce
    ultimately have "(cmd_double j) rs [~] k = Stay"
      by simp
  }
  then show ?thesis
    by (simp add: immobile_def tm_double_def)
qed

lemma tm_double_bounded_write:
  assumes "j < k - 1"
  shows "bounded_write (tm_double j) (k - 1) 4"
  using assms cmd_double_def tm_double_def bounded_write_def by simp

text \<open>
The next Turing machine removes the memorization tape.
\<close>

definition tm_double' :: "nat \<Rightarrow> machine" where
  "tm_double' j \<equiv> cartesian (tm_double j) 4"

lemma tm_double'_tm:
  assumes "j > 0" and "k \<ge> 2" and "G \<ge> 4" and "j < k"
  shows "turing_machine k G (tm_double' j)"
  unfolding tm_double'_def using assms cartesian_tm tm_double_tm by simp

lemma transforms_tm_double'I [transforms_intros]:
  assumes "j > 0" and "j < k"
    and "length tps = k"
    and "tps ! j = (\<lfloor>canrepr n\<rfloor>, 1)"
    and "t = (Suc (length (canrepr n)))"
    and "tps' = tps [j := (\<lfloor>canrepr (2 * n)\<rfloor>, length (canrepr n) + 2)]"
  shows "transforms (tm_double' j) tps t tps'"
  unfolding tm_double'_def
proof (rule cartesian_transforms_onesie)
  show "turing_machine (Suc k) 4 (tm_double j)"
    using assms(1,2) tm_double_tm by simp
  show "length tps = k" "2 \<le> k" "(1::nat) < 4"
    using assms by simp_all
  show "bounded_write (tm_double j) k 4"
    by (metis assms(2) diff_Suc_1 tm_double_bounded_write)
  show "immobile (tm_double j) k (Suc k)"
    by (simp add: assms(1,2) tm_double_immobile)
  show "transforms (tm_double j) (tps @ [\<lceil>\<triangleright>\<rceil>]) t (tps' @ [\<lceil>\<zero>\<rceil>])"
    using assms transforms_tm_double by simp
qed

text \<open>
The next Turing machine is the one we actually use to double a number. It runs
@{const tm_double'} and performs a carriage return.
\<close>

definition tm_times2 :: "tapeidx \<Rightarrow> machine" where
  "tm_times2 j \<equiv> tm_double' j ;; tm_cr j"

lemma tm_times2_tm:
  assumes "k \<ge> 2" and "j > 0" and "j < k" and "G \<ge> 4"
  shows "turing_machine k G (tm_times2 j)"
  using assms by (simp add: assms(1) tm_cr_tm tm_double'_tm tm_times2_def)

lemma transforms_tm_times2I [transforms_intros]:
  assumes "j > 0" and "j < k"
    and "length tps = k"
    and "tps ! j = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
    and "t = 5 + 2 * nlength n"
    and "tps' = tps [j := (\<lfloor>2 * n\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_times2 j) tps t tps'"
  unfolding tm_times2_def
proof (tform tps: assms)
  show "clean_tape (tps[j := (\<lfloor>2 * n\<rfloor>\<^sub>N, nlength n + 2)] ! j)"
    using clean_tape_ncontents assms by simp
  show "t = Suc (nlength n) + (tps[j := (\<lfloor>2 * n\<rfloor>\<^sub>N, nlength n + 2)] :#: j + 2)"
    using assms by simp
qed


subsubsection \<open>Multiplying arbitrary numbers\<close>

text \<open>
Before we can multiply arbitrary numbers we need just a few more lemmas.

\null
\<close>

lemma num_drop_le_nu: "num (drop j xs) \<le> num xs"
proof (cases "j \<le> length xs")
  case True
  let ?ys = "drop j xs"
  have map_shift_upt: "map (\<lambda>i. f (j + i)) [0..<l] = map f [j..<j + l]"
      for f :: "nat \<Rightarrow> nat" and j l
    by (rule nth_equalityI) simp_all

  have "num ?ys = (\<Sum>i\<leftarrow>[0..<length ?ys]. todigit (?ys ! i) * 2 ^ i)"
    using num_def by simp
  also have "... = (\<Sum>i\<leftarrow>[0..<length ?ys]. todigit (xs ! (j + i)) * 2 ^ i)"
    by (simp add: True)
  also have "... \<le> 2 ^ j * (\<Sum>i\<leftarrow>[0..<length ?ys].  todigit (xs ! (j + i)) * 2 ^ i)"
    by simp
  also have "... = (\<Sum>i\<leftarrow>[0..<length ?ys]. 2 ^ j * todigit (xs ! (j + i)) * 2 ^ i)"
    by (simp add: mult.assoc sum_list_const_mult)
  also have "... = (\<Sum>i\<leftarrow>[0..<length ?ys]. todigit (xs ! (j + i)) * 2 ^ (j + i))"
    by (simp add: ab_semigroup_mult_class.mult_ac(1) mult.commute power_add)
  also have "... = (\<Sum>i\<leftarrow>[j..<j + length ?ys]. todigit (xs ! i) * 2 ^ i)"
    using map_shift_upt[of "\<lambda>i. todigit (xs ! i) * 2 ^ i" j "length ?ys"] by simp
  also have "... \<le> (\<Sum>i\<leftarrow>[0..<j]. todigit (xs ! i) * 2 ^ i) +
      (\<Sum>i\<leftarrow>[j..<j + length ?ys]. todigit (xs ! i) * 2 ^ i)"
    by simp
  also have "... = (\<Sum>i\<leftarrow>[0..<j + length ?ys]. todigit (xs ! i) * 2 ^ i)"
    by (metis (no_types, lifting) le_add2 le_add_same_cancel2 map_append sum_list.append upt_add_eq_append)
  also have "... = (\<Sum>i\<leftarrow>[0..<length xs]. todigit (xs ! i) * 2 ^ i)"
    by (simp add: True)
  also have "... = num xs"
    using num_def by simp
  finally show ?thesis .
next
  case False
  then show ?thesis
    using canrepr canrepr_0 by (metis drop_all nat_le_linear zero_le)
qed

lemma nlength_prod_le_prod:
  assumes "i \<le> length xs"
  shows "nlength (prod xs ys i) \<le> nlength (num xs * num ys)"
  using prod[OF assms] num_drop_le_nu mult_le_mono1 nlength_mono by simp

corollary nlength_prod'_le_prod:
  assumes "i \<le> nlength x"
  shows "nlength (prod' x y i) \<le> nlength (x * y)"
  using assms prod'_def nlength_prod_le_prod by (metis prod' prod_eq_prod)

lemma two_times_prod:
  assumes "i < length xs"
  shows "2 * prod xs ys i \<le> num xs * num ys"
proof -
  have "2 * prod xs ys i \<le> prod xs ys (Suc i)"
    by simp
  also have "... = num (drop (length xs - Suc i) xs) * num ys"
    using prod[of "Suc i" xs] assms by simp
  also have "... \<le> num xs * num ys"
    using num_drop_le_nu by simp
  finally show ?thesis .
qed

corollary two_times_prod':
  assumes "i < nlength x"
  shows "2 * prod' x y i \<le> x * y"
  using assms two_times_prod prod'_def by (metis prod' prod_eq_prod)

text \<open>
The next Turing machine multiplies the numbers on tapes $j_1$ and $j_2$ and
writes the result to tape $j_3$. It iterates over the binary digits on $j_1$
starting from the most significant digit. In each iteration it doubles the
intermediate result on $j_3$. If the current digit is @{text \<one>}, the number on
$j_2$ is added to $j_3$.
\<close>

definition tm_mult :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_mult j1 j2 j3 \<equiv>
    tm_right_until j1 {\<box>} ;;
    tm_left j1 ;;
    WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<triangleright> DO
      tm_times2 j3 ;;
      IF \<lambda>rs. rs ! j1 = \<one> THEN
        tm_add j2 j3
      ELSE
        []
      ENDIF ;;
      tm_left j1
    DONE ;;
    tm_right j1"

lemma tm_mult_tm:
  assumes "j1 \<noteq> j2" "j2 \<noteq> j3" "j3 \<noteq> j1" and "j3 > 0"
  assumes "k \<ge> 2"
    and "G \<ge> 4"
    and "j1 < k" "j2 < k" "j3 < k"
  shows "turing_machine k G (tm_mult j1 j2 j3)"
  unfolding tm_mult_def
  using assms tm_left_tm tm_right_tm Nil_tm tm_add_tm tm_times2_tm tm_right_until_tm
    turing_machine_branch_turing_machine turing_machine_loop_turing_machine
  by simp

locale turing_machine_mult =
  fixes j1 j2 j3 :: tapeidx
begin

definition "tm1 \<equiv> tm_right_until j1 {\<box>}"
definition "tm2 \<equiv> tm1 ;; tm_left j1"
definition "tmIf \<equiv> IF \<lambda>rs. rs ! j1 = \<one> THEN tm_add j2 j3 ELSE [] ENDIF"
definition "tmBody1 \<equiv> tm_times2 j3 ;; tmIf"
definition "tmBody \<equiv> tmBody1 ;; tm_left j1"
definition "tmWhile \<equiv> WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<triangleright> DO tmBody DONE"
definition "tm3 \<equiv> tm2 ;; tmWhile"
definition "tm4 \<equiv> tm3 ;; tm_right j1"

lemma tm4_eq_tm_mult: "tm4 = tm_mult j1 j2 j3"
  using tm1_def tm2_def tm3_def tm4_def tm_mult_def tmIf_def tmBody_def tmBody1_def tmWhile_def
  by simp

context
  fixes x y k :: nat and tps0 :: "tape list"
  assumes jk: "j1 \<noteq> j2" "j2 \<noteq> j3" "j3 \<noteq> j1" "j3 > 0" "j1 < k" "j2 < k" "j3 < k" "length tps0 = k"
  assumes tps0:
    "tps0 ! j1 = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    "tps0 ! j2 = (\<lfloor>y\<rfloor>\<^sub>N, 1)"
    "tps0 ! j3 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
begin

definition "tps1 \<equiv> tps0 [j1 := (\<lfloor>x\<rfloor>\<^sub>N, Suc (nlength x))]"

lemma tm1 [transforms_intros]:
  assumes "t = Suc (nlength x)"
  shows "transforms tm1 tps0 t tps1"
  unfolding tm1_def
proof (tform tps: assms tps0 tps1_def jk)
  show "rneigh (tps0 ! j1) {\<box>} (nlength x)"
  proof (rule rneighI)
    show "(tps0 ::: j1) (tps0 :#: j1 + nlength x) \<in> {\<box>}"
      by (simp add: tps0)
    show "\<And>n'. n' < nlength x \<Longrightarrow> (tps0 ::: j1) (tps0 :#: j1 + n') \<notin> {\<box>}"
      using tps0 bit_symbols_canrepr contents_def by fastforce
  qed
qed

definition "tps2 \<equiv> tps0 [j1 := (\<lfloor>x\<rfloor>\<^sub>N, nlength x)]"

lemma tm2 [transforms_intros]:
  assumes "t = Suc (Suc (nlength x))" and "tps' = tps2"
  shows "transforms tm2 tps0 t tps'"
  unfolding tm2_def by (tform tps: assms tps1_def tps2_def jk)

definition "tpsL t \<equiv> tps0
   [j1 := (\<lfloor>x\<rfloor>\<^sub>N, nlength x - t),
    j3 := (\<lfloor>prod' x y t\<rfloor>\<^sub>N, 1)]"

definition "tpsL1 t \<equiv> tps0
   [j1 := (\<lfloor>x\<rfloor>\<^sub>N, nlength x - t),
    j3 := (\<lfloor>2 * prod' x y t\<rfloor>\<^sub>N, 1)]"

definition "tpsL2 t \<equiv> tps0
   [j1 := (\<lfloor>x\<rfloor>\<^sub>N, nlength x - t),
    j3 := (\<lfloor>prod' x y (Suc t)\<rfloor>\<^sub>N, 1)]"

definition "tpsL3 t \<equiv> tps0
   [j1 := (\<lfloor>x\<rfloor>\<^sub>N, nlength x - t - 1),
    j3 := (\<lfloor>prod' x y (Suc t)\<rfloor>\<^sub>N, 1)]"

lemma tmIf [transforms_intros]:
  assumes "t < nlength x" and "ttt = 12 + 3 * nlength (x * y)"
  shows "transforms tmIf (tpsL1 t) ttt (tpsL2 t)"
  unfolding tmIf_def
proof (tform tps: assms tpsL1_def tps0 jk)
  have "nlength y \<le> nlength (x * y) \<and> nlength (2 * prod' x y t) \<le> nlength (x * y)"
  proof
    have "x > 0"
      using assms(1) gr_implies_not_zero nlength_0 by auto
    then have "y \<le> x * y"
      by simp
    then show "nlength y \<le> nlength (x * y)"
      using nlength_mono by simp
    show "nlength (2 * prod' x y t) \<le> nlength (x * y)"
      using assms(1) by (simp add: nlength_mono two_times_prod')
  qed
  then show "3 * max (nlength y) (nlength (2 * Arithmetic.prod' x y t)) + 10 + 2 \<le> ttt"
    using assms(2) by simp
  let ?xs = "canrepr x" and ?ys = "canrepr y"
  let ?r = "read (tpsL1 t) ! j1"
  have "?r = (\<lfloor>x\<rfloor>\<^sub>N) (nlength x - t)"
    using tpsL1_def jk tapes_at_read'
    by (metis fst_conv length_list_update list_update_swap nth_list_update_eq snd_conv)
  then have r: "?r = canrepr x ! (nlength x - 1 - t)"
    using assms contents_def by simp
  have "prod' x y (Suc t) = 2 * prod' x y t + (if ?xs ! (length ?xs - 1 - t) = \<one> then num ?ys else 0)"
    using prod'_def by simp
  also have "... = 2 * prod' x y t + (if ?r = \<one> then num ?ys else 0)"
    using r by simp
  also have "... = 2 * prod' x y t + (if ?r = \<one> then y else 0)"
    using canrepr by simp
  finally have "prod' x y (Suc t) = 2 * prod' x y t + (if ?r = \<one> then y else 0)" .
  then show "read (tpsL1 t) ! j1 \<noteq> \<one> \<Longrightarrow> tpsL2 t = tpsL1 t"
       and "read (tpsL1 t) ! j1 = \<one> \<Longrightarrow>
      tpsL2 t = (tpsL1 t) [j3 := (\<lfloor>y + 2 * Arithmetic.prod' x y t\<rfloor>\<^sub>N, 1)]"
    by (simp_all add: add.commute tpsL1_def tpsL2_def)
qed

lemma tmBody1 [transforms_intros]:
  assumes "t < nlength x"
    and "ttt = 17 + 2 * nlength (Arithmetic.prod' x y t) + 3 * nlength (x * y)"
  shows "transforms tmBody1 (tpsL t) ttt (tpsL2 t)"
  unfolding tmBody1_def by (tform tps: jk tpsL_def tpsL1_def assms(1) time: assms(2))

lemma tmBody:
  assumes "t < nlength x"
    and "ttt = 6 + 2 * nlength (prod' x y t) + (12 + 3 * nlength (x * y))"
  shows "transforms tmBody (tpsL t) ttt (tpsL (Suc t))"
  unfolding tmBody_def by (tform tps: jk tpsL_def tpsL2_def assms(1) time: assms(2))

lemma tmBody' [transforms_intros]:
  assumes "t < nlength x" and "ttt = 18 + 5 * nlength (x * y)"
  shows "transforms tmBody (tpsL t) ttt (tpsL (Suc t))"
proof -
  have "6 + 2 * nlength (prod' x y t) + (12 + 3 * nlength (x * y)) \<le> 18 + 5 * nlength (x * y)"
    using assms nlength_prod'_le_prod by simp
  then show ?thesis
    using tmBody assms transforms_monotone by blast
qed

lemma read_contents:
  fixes tps :: "tape list" and j :: tapeidx and zs :: "symbol list"
  assumes "tps ! j = (\<lfloor>zs\<rfloor>, i)" and "i > 0" and "i \<le> length zs" and "j < length tps"
  shows "read tps ! j = zs ! (i - 1)"
  using assms tapes_at_read' by fastforce

lemma tmWhile [transforms_intros]:
  assumes "ttt = 1 + 25 * (nlength x + nlength y) * (nlength x + nlength y)"
  shows "transforms tmWhile (tpsL 0) ttt (tpsL (nlength x))"
  unfolding tmWhile_def
proof (tform)
  show "read (tpsL i) ! j1 \<noteq> \<triangleright>" if "i < nlength x" for i
  proof -
    have "(tpsL i) ! j1 = (\<lfloor>x\<rfloor>\<^sub>N, nlength x - i)"
      using tpsL_def jk by simp
    moreover have *: "nlength x - i > 0" "nlength x - i \<le> length (canrepr x)"
      using that by simp_all
    moreover have "length (tpsL i) = k"
      using tpsL_def jk by simp
    ultimately have "read (tpsL i) ! j1 = canrepr x ! (nlength x - i - 1)"
      using jk read_contents by simp
    then show ?thesis
      using * bit_symbols_canrepr
      by (metis One_nat_def Suc_le_lessD Suc_pred less_numeral_extra(4) proper_symbols_canrepr)
  qed
  show "\<not> read (tpsL (nlength x)) ! j1 \<noteq> \<triangleright>"
  proof -
    have "(tpsL (nlength x)) ! j1 = (\<lfloor>x\<rfloor>\<^sub>N, nlength x - nlength x)"
      using tpsL_def jk by simp
    then have "(tpsL (nlength x)) ! j1 = (\<lfloor>x\<rfloor>\<^sub>N, 0)"
      by simp
    then have "read (tpsL (nlength x)) ! j1 = \<triangleright>"
      using tapes_at_read' tpsL_def contents_at_0 jk by (metis fst_conv length_list_update snd_conv)
    then show ?thesis
      by simp
  qed
  show "nlength x * (18 + 5 * nlength (x * y) + 2) + 1 \<le> ttt"
  proof (cases "x = 0")
    case True
    then show ?thesis
      using assms by simp
  next
    case False
    have "nlength x * (18 + 5 * nlength (x * y) + 2) + 1 = nlength x * (20 + 5 * nlength (x * y)) + 1"
      by simp
    also have "... \<le> nlength x * (20 + 5 * (nlength x + nlength y)) + 1"
      using nlength_prod by (meson add_mono le_refl mult_le_mono)
    also have "... \<le> nlength x * (20 * (nlength x + nlength y) + 5 * (nlength x + nlength y)) + 1"
    proof -
      have "1 \<le> nlength x + nlength y"
        using False nlength_0 by (simp add: Suc_leI)
      then show ?thesis
        by simp
    qed
    also have "... \<le> nlength x * (25 * (nlength x + nlength y)) + 1"
      by simp
    also have "... \<le> (nlength x + nlength y) * (25 * (nlength x + nlength y)) + 1"
      by simp
    finally show ?thesis
      using assms by linarith
  qed
qed

lemma tm3:
  assumes "ttt = Suc (Suc (nlength x)) +
    Suc ((25 * nlength x + 25 * nlength y) * (nlength x + nlength y))"
  shows "transforms tm3 tps0 ttt (tpsL (nlength x))"
  unfolding tm3_def
proof (tform time: assms)
  show "tpsL 0 = tps2"
  proof -
    have "prod' x y 0 = 0"
      using prod'_def by simp
    then show ?thesis
      using tpsL_def tps2_def jk tps0 by (metis diff_zero list_update_id list_update_swap)
  qed
qed

definition "tps3 \<equiv> tps0
   [j1 := (\<lfloor>x\<rfloor>\<^sub>N, 0),
    j3 := (\<lfloor>x * y\<rfloor>\<^sub>N, 1)]"

lemma tm3' [transforms_intros]:
  assumes "ttt = 3 + 26 * (nlength x + nlength y) * (nlength x + nlength y)"
  shows "transforms tm3 tps0 ttt tps3"
proof -
  have "Suc (Suc (nlength x)) + Suc ((25 * nlength x + 25 * nlength y) * (nlength x + nlength y)) \<le>
      Suc (Suc (nlength x + nlength y)) + Suc ((25 * nlength x + 25 * nlength y) * (nlength x + nlength y))"
    by simp
  also have "... \<le> 2 + (nlength x + nlength y) * (nlength x + nlength y) + 1 +
      25 * (nlength x + nlength y) * (nlength x + nlength y)"
    by (simp add: le_square)
  also have "... = 3 + 26 * (nlength x + nlength y) * (nlength x + nlength y)"
    by linarith
  finally have "Suc (Suc (nlength x)) + Suc ((25 * nlength x + 25 * nlength y) * (nlength x + nlength y)) \<le>
      3 + 26 * (nlength x + nlength y) * (nlength x + nlength y)" .
  moreover have "tps3 = tpsL (nlength x)"
    using tps3_def tpsL_def by (simp add: prod')
  ultimately show ?thesis
    using tm3 assms transforms_monotone by simp
qed

definition "tps4 \<equiv> tps0
  [j3 := (\<lfloor>x * y\<rfloor>\<^sub>N, 1)]"

lemma tm4:
  assumes "ttt = 4 + 26 * (nlength x + nlength y) * (nlength x + nlength y)"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: tps3_def jk time: assms)
  show "tps4 = tps3[j1 := tps3 ! j1 |+| 1]"
    using tps4_def tps3_def jk tps0
    by (metis One_nat_def add.right_neutral add_Suc_right fst_conv list_update_id list_update_overwrite
     list_update_swap nth_list_update_eq nth_list_update_neq snd_conv)
qed

end  (* context x y k tps0 *)

end  (* locale turing_machine_mult *)

lemma transforms_tm_mult [transforms_intros]:
  fixes j1 j2 j3 :: tapeidx and x y k ttt :: nat and tps tps' :: "tape list"
  assumes "j1 \<noteq> j2" "j2 \<noteq> j3" "j3 \<noteq> j1" "j3 > 0"
  assumes "length tps = k"
    and "j1 < k" "j2 < k" "j3 < k"
    and "tps ! j1 = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    and "tps ! j2 = (\<lfloor>y\<rfloor>\<^sub>N, 1)"
    and "tps ! j3 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    and "ttt = 4 + 26 * (nlength x + nlength y) * (nlength x + nlength y)"
    and "tps' = tps [j3 := (\<lfloor>x * y\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_mult j1 j2 j3) tps ttt tps'"
proof -
  interpret loc: turing_machine_mult j1 j2 j3 .
  show ?thesis
    using assms loc.tps4_def loc.tm4 loc.tm4_eq_tm_mult by metis
qed


subsection \<open>Powers\<close>

text \<open>
In this section we construct for every $d \in \nat$ a Turing machine that
computes $n^d$. The following TMs expect a number $n$ on tape $j_1$ and output
$n^d$ on tape $j_3$. Another tape, $j_2$, is used as scratch space to hold
intermediate values. The TMs initialize tape $j_3$ with~1 and then multiply this
value by $n$ for $d$ times using the TM @{const tm_mult}.
\<close>

fun tm_pow :: "nat \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_pow 0 j1 j2 j3 = tm_setn j3 1" |
  "tm_pow (Suc d) j1 j2 j3 =
     tm_pow d j1 j2 j3 ;; (tm_copyn j3 j2 ;; tm_setn j3 0 ;; tm_mult j1 j2 j3 ;; tm_setn j2 0)"

lemma tm_pow_tm:
  assumes "j1 \<noteq> j2" "j2 \<noteq> j3" "j3 \<noteq> j1"
    and "0 < j2" "0 < j3" "0 < j1"
  assumes "j1 < k" "j2 < k" "j3 < k"
    and "k \<ge> 2"
    and "G \<ge> 4"
  shows "turing_machine k G (tm_pow d j1 j2 j3)"
  using assms tm_copyn_tm tm_setn_tm tm_mult_tm by (induction d) simp_all

locale turing_machine_pow =
  fixes j1 j2 j3 :: tapeidx
begin

definition "tm1 \<equiv> tm_copyn j3 j2 ;; tm_setn j3 0"
definition "tm2 \<equiv> tm1 ;; tm_mult j1 j2 j3"
definition "tm3 \<equiv> tm2 ;; tm_setn j2 0"

fun tm4 :: "nat \<Rightarrow> machine" where
  "tm4 0 = tm_setn j3 1" |
  "tm4 (Suc d) = tm4 d ;; tm3"

lemma tm4_eq_tm_pow: "tm4 d = tm_pow d j1 j2 j3"
  using tm3_def tm2_def tm1_def by (induction d) simp_all

context
  fixes x y k :: nat and tps0 :: "tape list"
  assumes jk: "k = length tps0" "j1 < k" "j2 < k" "j3 < k"
      "j1 \<noteq> j2" "j2 \<noteq> j3" "j3 \<noteq> j1"
      "0 < j2" "0 < j3" "0 < j1"
  assumes tps0:
    "tps0 ! j1 = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    "tps0 ! j2 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! j3 = (\<lfloor>y\<rfloor>\<^sub>N, 1)"
begin

definition "tps1 \<equiv> tps0
  [j2 := (\<lfloor>y\<rfloor>\<^sub>N, 1), j3 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 24 + 5 * nlength y"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: assms jk tps0 tps1_def)
  show "ttt = 14 + 3 * (nlength y + nlength 0) + (10 + 2 * nlength y + 2 * nlength 0)"
    using assms by simp
qed

definition "tps2 \<equiv> tps0
  [j2 := (\<lfloor>y\<rfloor>\<^sub>N, 1),
   j3 := (\<lfloor>x * y\<rfloor>\<^sub>N, 1)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 28 + 5 * nlength y + (26 * nlength x + 26 * nlength y) * (nlength x + nlength y)"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: jk tps1_def time: assms)
  show "tps1 ! j1 = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    using jk tps0 tps1_def by simp
  show "tps2 = tps1[j3 := (\<lfloor>x * y\<rfloor>\<^sub>N, 1)]"
    using tps2_def tps1_def by simp
qed

definition "tps3 \<equiv> tps0
  [j3 := (\<lfloor>x * y\<rfloor>\<^sub>N, 1)]"

lemma tm3:
  assumes "ttt = 38 + 7 * nlength y + (26 * nlength x + 26 * nlength y) * (nlength x + nlength y)"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: jk tps2_def time: assms)
  show "tps3 = tps2[j2 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
    using tps3_def tps2_def jk by (metis list_update_id list_update_overwrite list_update_swap tps0(2))
qed

lemma tm3':
  assumes "ttt = 38 + 33 * (nlength x + nlength y) ^ 2"
  shows "transforms tm3 tps0 ttt tps3"
proof -
  have "38 + 7 * nlength y + (26 * nlength x + 26 * nlength y) * (nlength x + nlength y) =
      38 + 7 * nlength y + 26 * (nlength x + nlength y) * (nlength x + nlength y)"
    by simp
  also have "... \<le> 38 + 33 * (nlength x + nlength y) * (nlength x + nlength y)"
  proof -
    have "nlength y \<le> (nlength x + nlength y) * (nlength x + nlength y)"
      by (meson le_add2 le_square le_trans)
    then show ?thesis
      by linarith
  qed
  also have "... = 38 + 33 * (nlength x + nlength y) ^ 2"
    by algebra
  finally have "38 + 7 * nlength y + (26 * nlength x + 26 * nlength y) * (nlength x + nlength y) \<le> ttt"
    using assms(1) by simp
  then show ?thesis
    using tm3 transforms_monotone assms by meson
qed

end  (* context x y k tps0 *)

lemma tm3'' [transforms_intros]:
  fixes x d k :: nat and tps0 :: "tape list"
  assumes "k = length tps0"
    and "j1 < k" "j2 < k" "j3 < k"
  assumes j_neq [simp]: "j1 \<noteq> j2" "j2 \<noteq> j3" "j3 \<noteq> j1"
    and j_gt [simp]: "0 < j2" "0 < j3" "0 < j1"
    and "tps0 ! j1 = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    and "tps0 ! j2 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    and "tps0 ! j3 = (\<lfloor>x ^ d\<rfloor>\<^sub>N, 1)"
    and "ttt = 71 + 99 * (Suc d) ^ 2 * (nlength x) ^ 2"
    and "tps' = tps0 [j3 := (\<lfloor>x ^ Suc d\<rfloor>\<^sub>N, 1)]"
  shows "transforms tm3 tps0 ttt tps'"
proof -
  let ?l = "nlength x"
  have "transforms tm3 tps0 (38 + 33 * (nlength x + nlength (x ^ d)) ^ 2) tps'"
    using tm3' assms tps3_def by simp
  moreover have "38 + 33 * (nlength x + nlength (x ^ d)) ^ 2 \<le> 71 + 99 * (Suc d) ^ 2 * ?l ^ 2"
  proof -
    have "38 + 33 * (nlength x + nlength (x ^ d)) ^ 2 \<le> 38 + 33 * (Suc (Suc d * ?l)) ^ 2"
      using nlength_pow by simp
    also have "... = 38 + 33 * ((Suc d * ?l)^2 + 2 * (Suc d * ?l) * 1 + 1^2)"
      by (metis Suc_eq_plus1 add_Suc one_power2 power2_sum)
    also have "... = 38 + 33 * ((Suc d * ?l)^2 + 2 * (Suc d * ?l) + 1)"
      by simp
    also have "... \<le> 38 + 33 * ((Suc d * ?l)^2 + 2 * (Suc d * ?l)^2 + 1)"
    proof -
      have "(Suc d * ?l) \<le> (Suc d * ?l) ^ 2"
        by (simp add: le_square power2_eq_square)
      then show ?thesis
        by simp
    qed
    also have "... \<le> 38 + 33 * (3 * (Suc d * ?l)^2 + 1)"
      by simp
    also have "... = 38 + 33 * (3 * (Suc d) ^ 2 * ?l^2 + 1)"
      by algebra
    also have "... = 71 + 99 * (Suc d) ^ 2 * ?l ^ 2"
      by simp
    finally show ?thesis .
  qed
  ultimately show ?thesis
    using transforms_monotone assms(14) by blast
qed

context
  fixes x k :: nat and tps0 :: "tape list"
  assumes jk: "j1 < k" "j2 < k" "j3 < k" "j1 \<noteq> j2" "j2 \<noteq> j3" "j3 \<noteq> j1" "0 < j2" "0 < j3" "0 < j1" "k = length tps0"
  assumes tps0:
    "tps0 ! j1 = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    "tps0 ! j2 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! j3 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
begin

lemma tm4:
  fixes d :: nat
  assumes "tps' = tps0 [j3 := (\<lfloor>x ^ d\<rfloor>\<^sub>N, 1)]"
    and "ttt = 12 + 71 * d + 99 * d ^ 3 * (nlength x) ^ 2"
  shows "transforms (tm4 d) tps0 ttt tps'"
  using assms
proof (induction d arbitrary: tps' ttt)
  case 0
  have "tm4 0 = tm_setn j3 1"
    by simp
  let ?tps = "tps0 [j3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"
  let ?t = "10 + 2 * nlength 1"
  have "transforms (tm_setn j3 1) tps0 ?t ?tps"
    using transforms_tm_setnI[of j3 tps0 0 ?t 1 ?tps] jk tps0 by simp
  then have "transforms (tm_setn j3 1) tps0 ?t tps'"
    using 0 by simp
  then show ?case
    using 0 nlength_1_simp by simp
next
  case (Suc d)
  note Suc.IH [transforms_intros]

  let ?l = "nlength x"
  have "tm4 (Suc d) = tm4 d ;; tm3"
    by simp
  define t where
    "t = 12 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 + (71 + 99 * (Suc d)\<^sup>2 * (nlength x)\<^sup>2)"
  have "transforms (tm4 d ;; tm3) tps0 t tps'"
    by (tform tps: jk tps0 Suc.prems(1) time: t_def)
  moreover have "t \<le> 12 + 71 * Suc d + 99 * Suc d ^ 3 * ?l\<^sup>2"
  proof -
    have "t = 12 + d * 71 + 99 * d ^ 3 * ?l\<^sup>2 + (71 + 99 * (Suc d)\<^sup>2 * ?l\<^sup>2)"
      using t_def by simp
    also have "... = 12 + Suc d * 71 + 99 * d ^ 3 * ?l\<^sup>2 + 99 * (Suc d)\<^sup>2 * ?l\<^sup>2"
      by simp
    also have "... = 12 + Suc d * 71 + 99 * ?l^2 * (d ^ 3 + (Suc d)\<^sup>2)"
      by algebra
    also have "... \<le> 12 + Suc d * 71 + 99 * ?l^2 * Suc d ^ 3"
    proof -
      have "Suc d ^ 3 = Suc d * Suc d ^ 2"
        by algebra
      also have "... = Suc d * (d ^ 2 + 2 * d + 1)"
        by (metis (no_types, lifting) Suc_1 add.commute add_Suc mult_2 one_power2 plus_1_eq_Suc power2_sum)
      also have "... = (d + 1) * (d ^ 2 + 2 * d + 1)"
        by simp
      also have "... = d ^ 3 + 2 * d ^ 2 + d + d ^ 2 + 2 * d + 1"
        by algebra
      also have "... = d ^ 3 + (d + 1) ^ 2 + 2 * d ^ 2 + d"
        by algebra
      also have "... \<ge> d ^ 3 + (d + 1) ^ 2"
        by simp
      finally have "Suc d ^ 3 \<ge> d ^ 3 + Suc d ^ 2"
        by simp
      then show ?thesis
        by simp
    qed
    also have "... = 12 + 71 * Suc d + 99 * Suc d ^ 3 * ?l^2"
      by simp
    finally show ?thesis .
  qed
  ultimately show ?case
    using transforms_monotone Suc by simp
qed

end  (* context x k tps0 *)

end  (* locale turing_machine_power *)

lemma transforms_tm_pow [transforms_intros]:
  fixes d :: nat
  assumes "j1 \<noteq> j2" "j2 \<noteq> j3" "j3 \<noteq> j1" "0 < j2" "0 < j3" "0 < j1" "j1 < k" "j2 < k" "j3 < k" "k = length tps"
  assumes
    "tps ! j1 = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    "tps ! j2 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! j3 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 12 + 71 * d + 99 * d ^ 3 * (nlength x) ^ 2"
  assumes "tps' = tps [j3 := (\<lfloor>x ^ d\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_pow d j1 j2 j3) tps ttt tps'"
proof -
  interpret loc: turing_machine_pow j1 j2 j3 .
  show ?thesis
    using assms loc.tm4_eq_tm_pow loc.tm4 by metis
qed


subsection \<open>Monomials\<close>

text \<open>
A monomial is a power multiplied by a constant coefficient. The following Turing
machines have parameters $c$ and $d$ and expect a number $x$ on tape $j$. They
output $c\cdot x^d$ on tape $j + 3$. The tapes $j+1$ and $j+2$ are
scratch space for use by @{const tm_pow} and @{const tm_mult}.
\<close>

definition tm_monomial :: "nat \<Rightarrow> nat \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_monomial c d j \<equiv>
    tm_pow d j (j + 1) (j + 2) ;;
    tm_setn (j + 1) c ;;
    tm_mult (j + 1) (j + 2) (j + 3);;
    tm_setn (j + 1) 0 ;;
    tm_setn (j + 2) 0"

lemma tm_monomial_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "j + 3 < k" and "0 < j"
  shows "turing_machine k G (tm_monomial c d j)"
  unfolding tm_monomial_def
  using assms tm_setn_tm tm_mult_tm tm_pow_tm turing_machine_sequential_turing_machine
  by simp

locale turing_machine_monomial =
  fixes c d :: nat and j :: tapeidx
begin

definition "tm1 \<equiv> tm_pow d j (j + 1) (j + 2)"
definition "tm2 \<equiv> tm1 ;; tm_setn (j + 1) c"
definition "tm3 \<equiv> tm2 ;; tm_mult (j + 1) (j + 2) (j + 3)"
definition "tm4 \<equiv> tm3 ;; tm_setn (j + 1) 0"
definition "tm5 \<equiv> tm4 ;; tm_setn (j + 2) 0"

lemma tm5_eq_tm_monomial: "tm5 = tm_monomial c d j"
  unfolding tm1_def tm2_def tm3_def tm4_def tm5_def tm_monomial_def by simp

context
  fixes x k :: nat and tps0 :: "tape list"
  assumes jk: "k = length tps0" "j + 3 < k" "0 < j"
  assumes tps0:
    "tps0 ! j = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
begin

definition "tps1 \<equiv> tps0 [(j + 2) := (\<lfloor>x ^ d\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 12 + 71 * d + 99 * d ^ 3 * (nlength x) ^ 2"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def by (tform tps: assms tps0 jk tps1_def)

definition "tps2 \<equiv> tps0
  [j + 2 := (\<lfloor>x ^ d\<rfloor>\<^sub>N, 1),
   j + 1 := (\<lfloor>c\<rfloor>\<^sub>N, 1)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 22 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 + 2 * nlength c"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: assms tps0 jk tps2_def tps1_def)
  show "ttt = 12 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 + (10 + 2 * nlength 0 + 2 * nlength c)"
    using assms(1) by simp
qed

definition "tps3 \<equiv> tps0
  [j + 2 := (\<lfloor>x ^ d\<rfloor>\<^sub>N, 1),
   j + 1 := (\<lfloor>c\<rfloor>\<^sub>N, 1),
   j + 3 := (\<lfloor>c * x ^ d\<rfloor>\<^sub>N, 1)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 26 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 + 2 * nlength c +
    26 * (nlength c + nlength (x ^ d)) ^ 2"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: tps2_def tps3_def tps0 jk)
  show "ttt = 22 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 + 2 * nlength c +
      (4 + 26 * (nlength c + nlength (x ^ d)) * (nlength c + nlength (x ^ d)))"
    using assms by algebra
qed

definition "tps4 \<equiv> tps0
  [j + 2 := (\<lfloor>x ^ d\<rfloor>\<^sub>N, 1),
   j + 3 := (\<lfloor>c * x ^ d\<rfloor>\<^sub>N, 1)]"

lemma tm4 [transforms_intros]:
  assumes "ttt = 36 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 + 4 * nlength c +
    26 * (nlength c + nlength (x ^ d))\<^sup>2"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: tps4_def tps3_def tps0 jk time: assms)
  show "tps4 = tps3[j + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
    unfolding tps4_def tps3_def
    using jk tps0(2) list_update_id[of tps0 "Suc j"] by (simp add: list_update_swap)
qed

definition "tps5 \<equiv> tps0
  [j + 3 := (\<lfloor>c * x ^ d\<rfloor>\<^sub>N, 1)]"

lemma tm5:
  assumes "ttt = 46 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 + 4 * nlength c +
    26 * (nlength c + nlength (x ^ d))\<^sup>2 +
    (2 * nlength (x ^ d))"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def
proof (tform tps: tps5_def tps4_def jk time: assms)
  show "tps5 = tps4[j + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
    unfolding tps5_def tps4_def
    using jk tps0 list_update_id[of tps0 "Suc (Suc j)"]
    by (simp add: list_update_swap)
qed

lemma tm5':
  assumes "ttt = 46 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 + 32 * (nlength c + nlength (x ^ d))\<^sup>2"
  shows "transforms tm5 tps0 ttt tps5"
proof -
  let ?t = "46 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 + 4 * nlength c +
    26 * (nlength c + nlength (x ^ d))\<^sup>2 + (2 * nlength (x ^ d))"
  have "?t \<le> 46 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 + 4 * nlength c +
    28 * (nlength c + nlength (x ^ d))\<^sup>2"
  proof -
    have "2 * nlength (x ^ d) \<le> 2 * (nlength c + nlength (x ^ d))\<^sup>2"
      by (meson add_leE eq_imp_le mult_le_mono2 power2_nat_le_imp_le)
    then show ?thesis
      by simp
  qed
  also have "... \<le> 46 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 + 32 * (nlength c + nlength (x ^ d))\<^sup>2"
  proof -
    have "4 * nlength c \<le> 4 * (nlength c + nlength (x ^ d))\<^sup>2"
      by (simp add: power2_nat_le_eq_le power2_nat_le_imp_le)
    then show ?thesis
      by simp
  qed
  also have "... = ttt"
    using assms(1) by simp
  finally have "?t \<le> ttt" .
  then show ?thesis
    using assms transforms_monotone tm5 by blast
qed

end  (* context x k *)

end  (* locale *)

lemma transforms_tm_monomialI [transforms_intros]:
  fixes ttt x k :: nat and tps tps' :: "tape list" and j :: tapeidx
  assumes "j > 0" and "j + 3 < k" and "k = length tps"
  assumes
    "tps ! j = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 46 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 + 32 * (nlength c + nlength (x ^ d))\<^sup>2"
  assumes "tps' = tps[j + 3 := (\<lfloor>c * x ^ d\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_monomial c d j) tps ttt tps'"
proof -
  interpret loc: turing_machine_monomial c d j .
  show ?thesis
    using loc.tm5_eq_tm_monomial loc.tm5' loc.tps5_def assms by simp
qed


subsection \<open>Polynomials\label{s:tm-arithmetic-poly}\<close>

text \<open>
A polynomial is a sum of monomials. In this section we construct for every
polynomial function $p$ a Turing machine that on input $x\in\nat$ outputs
$p(x)$.

According to our definition of polynomials (see Section~\ref{s:tm-basic-bigoh}),
we can represent each polynomial by a list of coefficients. The value of such a
polynomial with coefficient list @{term cs} on input $x$ is given by the next
function. In the following definition, the coefficients of the polynomial are in
reverse order, which simplifies the Turing machine later.
\<close>

definition polyvalue :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "polyvalue cs x \<equiv> (\<Sum>i\<leftarrow>[0..<length cs]. rev cs ! i * x ^ i)"

lemma polyvalue_Nil: "polyvalue [] x = 0"
  using polyvalue_def by simp

lemma sum_upt_snoc: "(\<Sum>i\<leftarrow>[0..<length (zs @ [z])]. (zs @ [z]) ! i * x ^ i) =
    (\<Sum>i\<leftarrow>[0..<length zs]. zs ! i * x ^ i) + z * x ^ (length zs)"
  by (smt (z3) add.right_neutral atLeastLessThan_iff length_append_singleton list.map(1) list.map(2)
    map_append map_eq_conv nth_append nth_append_length set_upt sum_list_append sum_list_simps(1)
    sum_list_simps(2) upt.simps(2) zero_order(1))

lemma polyvalue_Cons: "polyvalue (c # cs) x = c * x ^ (length cs) + polyvalue cs x"
proof -
  have "polyvalue (c # cs) x = (\<Sum>i\<leftarrow>[0..<Suc (length cs)]. (rev cs @ [c]) ! i * x ^ i)"
    using polyvalue_def by simp
  also have "... = (\<Sum>i\<leftarrow>[0..<length (rev cs @ [c])]. (rev cs @ [c]) ! i * x ^ i)"
    by simp
  also have "... = (\<Sum>i\<leftarrow>[0..<length (rev cs)]. (rev cs) ! i * x ^ i) + c * x ^ (length (rev cs))"
    using sum_upt_snoc by blast
  also have "... = (\<Sum>i\<leftarrow>[0..<length cs]. (rev cs) ! i * x ^ i) + c * x ^ (length cs)"
    by simp
  finally show ?thesis
    using polyvalue_def by simp
qed

lemma polyvalue_Cons_ge: "polyvalue (c # cs) x \<ge> polyvalue cs x"
  using polyvalue_Cons by simp

lemma polyvalue_Cons_ge2: "polyvalue (c # cs) x \<ge> c * x ^ (length cs)"
  using polyvalue_Cons by simp

lemma sum_list_const: "(\<Sum>_\<leftarrow>ns. c) = c * length ns"
  using sum_list_triv[of c ns] by simp

lemma polyvalue_le: "polyvalue cs x \<le> Max (set cs) * length cs * Suc x ^ length cs"
proof -
  define cmax where "cmax = Max (set (rev cs))"
  have "polyvalue cs x = (\<Sum>i\<leftarrow>[0..<length cs]. rev cs ! i * x ^ i)"
    using polyvalue_def by simp
  also have "... \<le> (\<Sum>i\<leftarrow>[0..<length cs]. cmax * x ^ i)"
  proof -
    have "rev cs ! i \<le> cmax" if "i < length cs" for i
      using that cmax_def by (metis List.finite_set Max_ge length_rev nth_mem)
    then show ?thesis
      by (metis (no_types, lifting) atLeastLessThan_iff mult_le_mono1 set_upt sum_list_mono)
  qed
  also have "... = cmax * (\<Sum>i\<leftarrow>[0..<length cs]. x ^ i)"
    using sum_list_const_mult by blast
  also have "... \<le> cmax * (\<Sum>i\<leftarrow>[0..<length cs]. Suc x ^ i)"
    by (simp add: power_mono sum_list_mono)
  also have "... \<le> cmax * (\<Sum>i\<leftarrow>[0..<length cs]. Suc x ^ length cs)"
  proof -
    have "Suc x ^ i \<le> Suc x ^ length cs" if "i < length cs" for i
      using that by (simp add: dual_order.strict_implies_order pow_mono)
    then show ?thesis
      by (metis atLeastLessThan_iff mult_le_mono2 set_upt sum_list_mono)
  qed
  also have "... = cmax * length cs * Suc x ^ length cs"
    using sum_list_const[of _ "[0..<length cs]"] by simp
  finally have "polyvalue cs x \<le> cmax * length cs * Suc x ^ length cs" .
  moreover have "cmax = Max (set cs)"
    using cmax_def by simp
  ultimately show ?thesis
    by simp
qed

lemma nlength_polyvalue:
 "nlength (polyvalue cs x) \<le> nlength (Max (set cs)) + nlength (length cs) + Suc (length cs * nlength (Suc x))"
proof -
  have "nlength (polyvalue cs x) \<le> nlength (Max (set cs) * length cs * Suc x ^ length cs)"
    using polyvalue_le nlength_mono by simp
  also have "... \<le> nlength (Max (set cs) * length cs) + nlength (Suc x ^ length cs)"
    using nlength_prod by simp
  also have "... \<le> nlength (Max (set cs)) + nlength(length cs) + Suc (length cs * nlength (Suc x))"
    by (meson add_mono nlength_pow nlength_prod)
  finally show ?thesis .
qed

text \<open>
The following Turing machines compute polynomials given as lists of
coefficients.  If the polynomial is given by coefficients @{term cs}, the TM
@{term "tm_polycoef cs j"} expect a number $n$ on tape $j$ and writes $p(n)$ to
tape $j + 4$. The tapes $j+1$, $j+2$, and $j + 3$ are auxiliary tapes for use by
@{const tm_monomial}.
\<close>

fun tm_polycoef :: "nat list \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_polycoef [] j = []" |
  "tm_polycoef (c # cs) j =
     tm_polycoef cs j ;;
     (tm_monomial c (length cs) j ;;
      tm_add (j + 3) (j + 4) ;;
      tm_setn (j + 3) 0)"

lemma tm_polycoef_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "j + 4 < k" and "0 < j"
  shows "turing_machine k G (tm_polycoef cs j)"
proof (induction cs)
  case Nil
  then show ?case
    by (simp add: assms(1) assms(2) turing_machine_def)
next
  case (Cons c cs)
  moreover have
    "turing_machine k G (tm_monomial c (length cs) j ;; tm_add (j + 3) (j + 4) ;; tm_setn (j + 3) 0)"
    using tm_monomial_tm tm_add_tm tm_setn_tm assms
    by simp
  ultimately show ?case
    by simp
qed

locale turing_machine_polycoef =
  fixes j :: tapeidx
begin

definition "tm1 c cs \<equiv> tm_monomial c (length cs) j"
definition "tm2 c cs \<equiv> tm1 c cs ;; tm_add (j + 3) (j + 4)"
definition "tm3 c cs \<equiv> tm2 c cs ;; tm_setn (j + 3) 0"

fun tm4 :: "nat list \<Rightarrow> machine" where
  "tm4 [] = []" |
  "tm4 (c # cs) = tm4 cs ;; tm3 c cs"

lemma tm4_eq_tm_polycoef: "tm4 zs = tm_polycoef zs j"
proof (induction zs)
  case Nil
  then show ?case
    by simp
next
  case (Cons z zs)
  then show ?case
    by (simp add: tm1_def tm2_def tm3_def)
qed

context
  fixes x y k :: nat and tps0 :: "tape list"
  fixes c :: nat and cs :: "nat list"
  assumes jk: "0 < j" "j + 4 < k" "k = length tps0"
  assumes tps0:
    "tps0 ! j = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 4) = (\<lfloor>y\<rfloor>\<^sub>N, 1)"
begin

abbreviation "d \<equiv> length cs"

definition "tps1 \<equiv> tps0
  [j + 3 := (\<lfloor>c * x ^ (length cs)\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 46 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 +
      32 * (nlength c + nlength (x ^ d))\<^sup>2"
  shows "transforms (tm1 c cs) tps0 ttt tps1"
  unfolding tm1_def by (tform tps: assms jk tps0 tps1_def)

definition "tps2 = tps0
  [j + 3 := (\<lfloor>c * x ^ (length cs)\<rfloor>\<^sub>N, 1),
   j + 4 := (\<lfloor>c * x ^ (length cs) + y\<rfloor>\<^sub>N, 1)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 46 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 +
    32 * (nlength c + nlength (x ^ d))\<^sup>2 +
    (3 * max (nlength (c * x ^ d)) (nlength y) + 10)"
  shows "transforms (tm2 c cs) tps0 ttt tps2"
  unfolding tm2_def by (tform tps: tps1_def tps2_def jk tps0 time: assms)

definition "tps3 \<equiv> tps0
  [j + 4 := (\<lfloor>c * x ^ d + y\<rfloor>\<^sub>N, 1)]"

lemma tm3:
  assumes "ttt = 66 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 +
      32 * (nlength c + nlength (x ^ d))\<^sup>2 +
      3 * max (nlength (c * x ^ d)) (nlength y) +
      2 * nlength (c * x ^ d)"
  shows "transforms (tm3 c cs) tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: tps2_def tps3_def jk tps0 time: assms)
  show "tps3 = tps2[j + 3 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
    using tps3_def tps2_def jk tps0
    by (smt (z3) One_nat_def add_2_eq_Suc add_left_cancel lessI less_numeral_extra(4) list_update_id
      list_update_overwrite list_update_swap numeral_3_eq_3 numeral_Bit0 plus_1_eq_Suc)
qed

definition "tps3' \<equiv> tps0
  [j + 4 := (\<lfloor>c * x ^ length cs + y\<rfloor>\<^sub>N, 1)]"

lemma tm3':
  assumes "ttt = 66 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 +
      32 * (nlength c + nlength (x ^ d))\<^sup>2 +
      5 * max (nlength (c * x ^ d)) (nlength y)"
  shows "transforms (tm3 c cs) tps0 ttt tps3'"
proof -
  have "66 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 +
      32 * (nlength c + nlength (x ^ d))\<^sup>2 +
      3 * max (nlength (c * x ^ d)) (nlength y) +
      2 * nlength (c * x ^ d) \<le>
      66 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 +
      32 * (nlength c + nlength (x ^ d))\<^sup>2 +
      3 * max (nlength (c * x ^ d)) (nlength y) +
      2 * max (nlength (c * x ^ d)) (nlength y)"
    by simp
  also have "... = 66 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 +
      32 * (nlength c + nlength (x ^ d))\<^sup>2 +
      5 * max (nlength (c * x ^ d)) (nlength y)"
    by simp
  finally have "66 + 71 * d + 99 * d ^ 3 * (nlength x)\<^sup>2 +
      32 * (nlength c + nlength (x ^ d))\<^sup>2 +
      3 * max (nlength (c * x ^ d)) (nlength y) +
      2 * nlength (c * x ^ d) \<le> ttt"
    using assms(1) by simp
  moreover have "tps3' = tps3"
    using tps3'_def tps3_def by simp
  ultimately show ?thesis
    using tm3 transforms_monotone by simp
qed

end  (* context x y k c cs tps0 *)

lemma tm3'' [transforms_intros]:
  fixes c :: nat and cs :: "nat list"
  fixes x k :: nat and tps0 tps' :: "tape list"
  assumes "k = length tps0" and "j + 4 < k" and "0 < j"
  assumes
    "tps0 ! j = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 4) = (\<lfloor>polyvalue cs x\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 66 +
      71 * (length cs) +
      99 * (length cs) ^ 3 * (nlength x)\<^sup>2 +
      32 * (nlength c + nlength (x ^ (length cs)))\<^sup>2 +
      5 * max (nlength (c * x ^ (length cs))) (nlength (polyvalue cs x))"
  assumes "tps' = tps0
    [j + 4 := (\<lfloor>polyvalue (c # cs) x\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm3 c cs) tps0 ttt tps'"
  using assms tm3'[where ?y="polyvalue cs x"] tps3'_def polyvalue_Cons by simp

lemma pow_le_pow_Suc:
  fixes a b :: nat
  shows "a ^ b \<le> Suc a ^ Suc b"
proof -
  have "a ^ b \<le> Suc a ^ b"
    by (simp add: power_mono)
  then show ?thesis
    by simp
qed

lemma tm4:
  fixes x k :: nat and tps0 :: "tape list"
  fixes cs :: "nat list"
  assumes "k = length tps0" and "j + 4 < k" and "0 < j"
  assumes
    "tps0 ! j = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  assumes ttt: "ttt = length cs *
     (66 +
      71 * (length cs) +
      99 * (length cs) ^ 3 * (nlength x)\<^sup>2 +
      32 * (Max (set (map nlength cs)) + nlength (Suc x ^ length cs))\<^sup>2 +
      5 * nlength (polyvalue cs x))"
  shows "transforms (tm4 cs) tps0 ttt (tps0[j + 4 := (\<lfloor>polyvalue cs x\<rfloor>\<^sub>N, 1)])"
  using ttt
proof (induction cs arbitrary: ttt)
  case Nil
  then show ?case
    using polyvalue_Nil transforms_Nil assms by (metis list.size(3) list_update_id mult_is_0 tm4.simps(1))
next
  case (Cons c cs)
  note Cons.IH [transforms_intros]

  have tm4def: "tm4 (c # cs) = tm4 cs ;; tm3 c cs"
    by simp

  let ?t1 = "d cs *
    (66 + 71 * d cs + 99 * d cs ^ 3 * (nlength x)\<^sup>2 +
     32 * (Max (nlength ` set cs) + nlength (Suc x ^ d cs))\<^sup>2 +
     5 * nlength (polyvalue cs x))"
  let ?t2 = "66 + 71 * d cs + 99 * d cs ^ 3 * (nlength x)\<^sup>2 +
     32 * (nlength c + nlength (x ^ d cs))\<^sup>2 +
     5 * max (nlength (c * x ^ d cs)) (nlength (polyvalue cs x))"
  define t where "t = ?t1 + ?t2"
  have tm4: "transforms (tm4 (c # cs)) tps0 t (tps0[j + 4 := (\<lfloor>polyvalue (c # cs) x\<rfloor>\<^sub>N, 1)])"
    unfolding tm4def by (tform tps: assms t_def)

  have "?t1 \<le> d cs *
    (66 + 71 * d (c#cs) + 99 * d cs ^ 3 * (nlength x)\<^sup>2 +
     32 * (Max (nlength ` set cs) + nlength (Suc x ^d cs))\<^sup>2 +
     5 * nlength (polyvalue cs x))"
    by simp
  also have "... \<le> d cs *
    (66 + 71 * d (c#cs) + 99 * d (c#cs) ^ 3 * (nlength x)\<^sup>2 +
     32 * (Max (nlength ` set cs) + nlength (Suc x ^d cs))\<^sup>2 +
     5 * nlength (polyvalue cs x))"
    by simp
  also have "... \<le> d cs *
    (66 + 71 * d (c#cs) + 99 * d (c#cs) ^ 3 * (nlength x)\<^sup>2 +
     32 * (Max (nlength ` set (c#cs)) + nlength (Suc x ^d cs))\<^sup>2 +
     5 * nlength (polyvalue cs x))"
    by simp
  also have "... \<le> d cs *
    (66 + 71 * d (c#cs) + 99 * d (c#cs) ^ 3 * (nlength x)\<^sup>2 +
     32 * (Max (nlength ` set (c#cs)) + nlength (Suc x ^d (c#cs)))\<^sup>2 +
     5 * nlength (polyvalue cs x))"
    using nlength_mono by simp
  also have "... \<le> d cs *
    (66 + 71 * d (c#cs) + 99 * d (c#cs) ^ 3 * (nlength x)\<^sup>2 +
     32 * (Max (nlength ` set (c#cs)) + nlength (Suc x ^d (c#cs)))\<^sup>2 +
     5 * nlength (polyvalue (c#cs) x))"
    using nlength_mono polyvalue_Cons_ge by simp
  finally have t1: "?t1 \<le> d cs *
    (66 + 71 * d (c#cs) + 99 * d (c#cs) ^ 3 * (nlength x)\<^sup>2 +
     32 * (Max (nlength ` set (c#cs)) + nlength (Suc x ^d (c#cs)))\<^sup>2 +
     5 * nlength (polyvalue (c#cs) x))"
    (is "?t1 \<le> d cs * ?t3") .

  have "?t2 \<le>
    66 + 71 * d (c # cs) + 99 * d cs ^ 3 * (nlength x)\<^sup>2 +
      32 * (nlength c + nlength (x ^ d cs))\<^sup>2 +
      5 * max (nlength (c * x ^ d cs)) (nlength (polyvalue cs x))"
    by simp
  also have "... \<le> 66 + 71 * d (c # cs) + 99 * d (c # cs) ^ 3 * (nlength x)\<^sup>2 +
      32 * (nlength c + nlength (x ^ d cs))\<^sup>2 +
      5 * max (nlength (c * x ^ d cs)) (nlength (polyvalue cs x))"
    by simp
  also have "... \<le> 66 + 71 * d (c # cs) + 99 * d (c # cs) ^ 3 * (nlength x)\<^sup>2 +
      32 * (Max (set (map nlength (c # cs))) + nlength (x ^ d cs))\<^sup>2 +
      5 * max (nlength (c * x ^ d cs)) (nlength (polyvalue cs x))"
    by simp
  also have "... \<le> 66 + 71 * d (c # cs) + 99 * d (c # cs) ^ 3 * (nlength x)\<^sup>2 +
      32 * (Max (set (map nlength (c # cs))) + nlength (Suc x ^ d (c#cs)))\<^sup>2 +
      5 * max (nlength (c * x ^ d cs)) (nlength (polyvalue cs x))"
    using nlength_mono pow_le_pow_Suc by simp
  also have "... \<le> 66 + 71 * d (c # cs) + 99 * d (c # cs) ^ 3 * (nlength x)\<^sup>2 +
      32 * (Max (set (map nlength (c # cs))) + nlength (Suc x ^ d (c#cs)))\<^sup>2 +
      5 * max (nlength (c * x ^ d cs)) (nlength (polyvalue (c#cs) x))"
  proof -
    have "nlength (polyvalue cs x) \<le> nlength (polyvalue (c#cs) x)"
      using polyvalue_Cons by (simp add: nlength_mono)
    then show ?thesis
      by simp
  qed
  also have "... \<le> 66 + 71 * d (c # cs) + 99 * d (c # cs) ^ 3 * (nlength x)\<^sup>2 +
      32 * (Max (set (map nlength (c # cs))) + nlength (Suc x ^ d (c#cs)))\<^sup>2 +
      5 * max (nlength (polyvalue (c#cs) x)) (nlength (polyvalue (c#cs) x))"
    using nlength_mono polyvalue_Cons_ge2 by simp
  also have "... \<le> 66 + 71 * d (c # cs) + 99 * d (c # cs) ^ 3 * (nlength x)\<^sup>2 +
      32 * (Max (set (map nlength (c # cs))) + nlength (Suc x ^ d (c#cs)))\<^sup>2 +
      5 * nlength (polyvalue (c#cs) x)"
    by simp
  finally have t2: "?t2 \<le> ?t3"
    by simp

  have "t \<le> d cs * ?t3 + ?t3"
    using t1 t2 t_def add_le_mono by blast
  then have "t \<le> d (c#cs) * ?t3"
    by simp
  moreover have "ttt = d (c#cs) * ?t3"
    using Cons by simp
  ultimately have "t \<le> ttt"
    by simp
  then show ?case
    using tm4 transforms_monotone by simp
qed

end  (* locale turing_machine_polycoef *)

text \<open>
The time bound in the previous lemma for @{const tm_polycoef} is a bit unwieldy.
It depends not only on the length of the input $x$ but also on the list of
coefficients of the polynomial $p$ and on the value $p(x)$.  Next we bound this
time bound by a simpler expression of the form $d + d\cdot|x|^2$ where $d$
depends only on the polynomial. This is accomplished by the next three lemmas.
\<close>

lemma tm_polycoef_time_1: "\<exists>d. \<forall>x. nlength (polyvalue cs x) \<le> d + d * nlength x"
proof -
  { fix x
    have "nlength (polyvalue cs x) \<le> nlength (Max (set cs)) + nlength (length cs) + Suc (length cs * nlength (Suc x))"
      using nlength_polyvalue by simp
    also have "... = nlength (Max (set cs)) + nlength (length cs) + 1 + length cs * nlength (Suc x)"
        (is "_ = ?a + length cs * nlength (Suc x)")
      by simp
    also have "... \<le> ?a + length cs * (Suc (nlength x))"
      using nlength_Suc by (meson add_mono_thms_linordered_semiring(2) mult_le_mono2)
    also have "... = ?a + length cs + length cs * nlength x"
        (is "_ = ?b + length cs * nlength x")
      by simp
    also have "... \<le> ?b + ?b * nlength x"
      by (meson add_left_mono le_add2 mult_le_mono1)
    finally have "nlength (polyvalue cs x) \<le> ?b + ?b * nlength x" .
  }
  then show ?thesis
    by blast
qed

lemma tm_polycoef_time_2: "\<exists>d. \<forall>x. (Max (set (map nlength cs)) + nlength (Suc x ^ length cs))\<^sup>2 \<le> d + d * nlength x ^ 2"
proof -
  { fix x
    have "(Max (set (map nlength cs)) + nlength (Suc x ^ length cs))\<^sup>2 \<le>
        (Max (set (map nlength cs)) + Suc (nlength (Suc x) * length cs))\<^sup>2"
      using nlength_pow by (simp add: mult.commute)
    also have "... = (Suc (Max (set (map nlength cs))) + nlength (Suc x) * length cs)\<^sup>2"
        (is "_ = (?a + ?b)^2")
      by simp
    also have "... = ?a ^ 2 + 2 * ?a * ?b + ?b ^ 2"
      by algebra
    also have "... \<le> ?a ^ 2 + 2 * ?a * ?b ^ 2 + ?b ^ 2"
      by (meson add_le_mono dual_order.eq_iff mult_le_mono2 power2_nat_le_imp_le)
    also have "... \<le> ?a ^ 2 + (2 * ?a + 1) * ?b ^ 2"
      by simp
    also have "... = ?a ^ 2 + (2 * ?a + 1) * (length cs) ^ 2 * nlength (Suc x) ^ 2"
      by algebra
    also have "... \<le> ?a ^ 2 + (2 * ?a + 1) * (length cs) ^ 2 * Suc (nlength x) ^ 2"
      using nlength_Suc by simp
    also have "... = ?a ^ 2 + (2 * ?a + 1) * (length cs) ^ 2 * (nlength x ^ 2 + 2 * nlength x + 1)"
      by (smt (z3) Suc_eq_plus1 add.assoc mult_2 nat_1_add_1 one_power2 plus_1_eq_Suc power2_sum)
    also have "... \<le> ?a ^ 2 + (2 * ?a + 1) * (length cs) ^ 2 * (nlength x ^ 2 + 2 * nlength x ^ 2 + 1)"
    proof -
      have "nlength x ^ 2 + 2 * nlength x + 1 \<le> nlength x ^ 2 + 2 * nlength x ^ 2 + 1"
        by (metis add_le_mono1 add_mono_thms_linordered_semiring(2) le_square mult.commute
        mult_le_mono1 numerals(1) power_add_numeral power_one_right semiring_norm(2))
      then show ?thesis
        by simp
    qed
    also have "... = ?a ^ 2 + (2 * ?a + 1) * (length cs) ^ 2 * (3 * nlength x ^ 2 + 1)"
      by simp
    also have "... = ?a ^ 2 + (2 * ?a + 1) * (length cs) ^ 2 + (2 * ?a + 1) * (length cs) ^ 2 * 3 * nlength x ^ 2"
        (is "_ = _ + ?c * nlength x ^ 2")
      by simp
    also have "... \<le> ?a ^ 2 + ?c + ?c * nlength x ^ 2"
        (is "_ \<le> ?d + ?c * nlength x ^ 2")
      by simp
    also have "... \<le> ?d + ?d * nlength x ^ 2"
      by simp
    finally have "(Max (set (map nlength cs)) + nlength (Suc x ^ length cs))\<^sup>2 \<le> ?d + ?d * nlength x ^ 2" .
  }
  then show ?thesis
    by auto
qed

lemma tm_polycoef_time_3:
  "\<exists>d. \<forall>x. length cs *
    (66 +
     71 * length cs +
     99 * length cs ^ 3 * (nlength x)\<^sup>2 +
     32 * (Max (set (map nlength cs)) + nlength (Suc x ^ length cs))\<^sup>2 +
     5 * nlength (polyvalue cs x)) \<le> d + d * nlength x ^ 2"
proof -
  obtain d1 where d1: "\<forall>x. nlength (polyvalue cs x) \<le> d1 + d1 * nlength x"
    using tm_polycoef_time_1 by auto
  obtain d2 where d2: "\<forall>x. (Max (set (map nlength cs)) + nlength (Suc x ^ length cs))\<^sup>2 \<le> d2 + d2 * nlength x ^ 2"
    using tm_polycoef_time_2 by auto
  { fix x
    let ?lhs = " length cs *
      (66 +
      71 * length cs +
      99 * length cs ^ 3 * (nlength x)\<^sup>2 +
      32 * (Max (set (map nlength cs)) + nlength (Suc x ^ length cs))\<^sup>2 +
      5 * nlength (polyvalue cs x))"
    let ?n = "nlength x"
    have "?lhs \<le> length cs *
        (66 + 71 * length cs + 99 * length cs ^ 3 * ?n ^ 2 +
        32 * (d2 + d2 * ?n ^ 2) + 5 * (d1 + d1 * ?n))"
      using d1 d2 add_le_mono mult_le_mono2 nat_add_left_cancel_le by presburger
    also have "... \<le> length cs *
        (66 + 71 * length cs + 99 * length cs ^ 3 * ?n ^ 2 +
        32 * (d2 + d2 * ?n ^ 2) + 5 * (d1 + d1 * ?n ^ 2))"
      by (simp add: le_square power2_eq_square)
    also have "... = length cs *
        (66 + 71 * length cs + 99 * length cs ^ 3 * ?n ^ 2 +
        32 * d2 + 32 * d2 * ?n ^ 2 + 5 * d1 + 5 * d1 * ?n ^ 2)"
      by simp
    also have "... = length cs *
        (66 + 71 * length cs + 32 * d2 + 5 * d1 +
        (99 * length cs ^ 3 + 32 * d2 + 5 * d1) * ?n ^ 2)"
      by algebra
    also have "... = length cs * (66 + 71 * length cs + 32 * d2 + 5 * d1) +
        length cs * (99 * length cs ^ 3 + 32 * d2 + 5 * d1) * ?n ^ 2"
          (is "_ = ?a + ?b * ?n ^ 2")
      by algebra
    also have "... \<le> max ?a ?b + max ?a ?b * ?n ^ 2"
      by (simp add: add_mono_thms_linordered_semiring(1))
    finally have "?lhs \<le> max ?a ?b + max ?a ?b * ?n ^ 2" .
  }
  then show ?thesis
    by auto
qed

text \<open>
According to our definition of @{const polynomial} (see
Section~\ref{s:tm-basic-bigoh}) every polynomial has a list of coefficients.
Therefore the next definition is well-defined for polynomials $p$.
\<close>

definition coefficients :: "(nat \<Rightarrow> nat) \<Rightarrow> nat list" where
  "coefficients p \<equiv> SOME cs. \<forall>n. p n = (\<Sum>i\<leftarrow>[0..<length cs]. cs ! i * n ^ i)"

text \<open>
The $d$ in our upper bound of the form $d + d\cdot|x|^2$ for the running time of
@{const tm_polycoef} depends on the polynomial. It is given by the next
function:
\<close>

definition d_polynomial :: "(nat \<Rightarrow> nat) \<Rightarrow> nat" where
  "d_polynomial p \<equiv>
   (let cs = rev (coefficients p)
    in SOME d. \<forall>x. length cs *
    (66 +
     71 * length cs +
     99 * length cs ^ 3 * (nlength x)\<^sup>2 +
     32 * (Max (set (map nlength cs)) + nlength (Suc x ^ length cs))\<^sup>2 +
     5 * nlength (polyvalue cs x)) \<le> d + d * nlength x ^ 2)"

text \<open>
The Turing machine @{const tm_polycoef} has the coefficients of a polynomial
as parameter. Next we devise a similar Turing machine that has the polynomial,
as a function $\nat \to \nat$, as parameter.
\<close>

definition tm_polynomial :: "(nat \<Rightarrow> nat) \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_polynomial p j \<equiv> tm_polycoef (rev (coefficients p)) j"

lemma tm_polynomial_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "0 < j" and "j + 4 < k"
  shows "turing_machine k G (tm_polynomial p j)"
  using assms tm_polynomial_def tm_polycoef_tm by simp

lemma transforms_tm_polynomialI [transforms_intros]:
  fixes p :: "nat \<Rightarrow> nat" and j :: tapeidx
  fixes k x :: nat and tps tps' :: "tape list"
  assumes "0 < j" and "k = length tps" and "j + 4 < k"
    and "polynomial p"
  assumes
    "tps ! j = (\<lfloor>x\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  assumes "ttt = d_polynomial p + d_polynomial p * nlength x ^ 2"
  assumes "tps' = tps
    [j + 4 := (\<lfloor>p x\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_polynomial p j) tps ttt tps'"
proof -
  let ?P = "\<lambda>x. \<forall>n. p n = (\<Sum>i\<leftarrow>[0..<length x]. x ! i * n ^ i)"
  define cs where "cs = (SOME x. ?P x)"
  moreover have ex: "\<exists>cs. ?P cs"
    using assms(4) polynomial_def by simp
  ultimately have "?P cs"
    using someI_ex[of ?P] by blast
  then have 1: "polyvalue (rev cs) x = p x"
    using polyvalue_def by simp

  let ?cs = "rev cs"
  have "d_polynomial p = (SOME d. \<forall>x. length ?cs *
    (66 +
     71 * length ?cs +
     99 * length ?cs ^ 3 * (nlength x)\<^sup>2 +
     32 * (Max (set (map nlength ?cs)) + nlength (Suc x ^ length ?cs))\<^sup>2 +
     5 * nlength (polyvalue ?cs x)) \<le> d + d * nlength x ^ 2)"
    using cs_def coefficients_def d_polynomial_def by simp
  then have *: "\<forall>x. length ?cs *
    (66 +
     71 * length ?cs +
     99 * length ?cs ^ 3 * (nlength x)\<^sup>2 +
     32 * (Max (set (map nlength ?cs)) + nlength (Suc x ^ length ?cs))\<^sup>2 +
     5 * nlength (polyvalue ?cs x)) \<le> (d_polynomial p) + (d_polynomial p) * nlength x ^ 2"
    using tm_polycoef_time_3 someI_ex[OF tm_polycoef_time_3] by presburger

  let ?ttt = "length ?cs *
    (66 +
     71 * length ?cs +
     99 * length ?cs ^ 3 * (nlength x)\<^sup>2 +
     32 * (Max (set (map nlength ?cs)) + nlength (Suc x ^ length ?cs))\<^sup>2 +
     5 * nlength (polyvalue ?cs x))"

  interpret loc: turing_machine_polycoef j .

  have "transforms (loc.tm4 ?cs) tps ?ttt (tps[j + 4 := (\<lfloor>polyvalue ?cs x\<rfloor>\<^sub>N, 1)])"
    using loc.tm4 assms * by blast
  then have "transforms (loc.tm4 ?cs) tps ?ttt (tps[j + 4 := (\<lfloor>p x\<rfloor>\<^sub>N, 1)])"
    using 1 by simp
  then have "transforms (loc.tm4 ?cs) tps ?ttt tps'"
    using assms(11) by simp
  moreover have "loc.tm4 ?cs = tm_polynomial p j"
    using tm_polynomial_def loc.tm4_eq_tm_polycoef coefficients_def cs_def by simp
  ultimately have "transforms (tm_polynomial p j) tps ?ttt tps'"
    by simp
  then show "transforms (tm_polynomial p j) tps ttt tps'"
    using * assms(10) transforms_monotone by simp
qed


subsection \<open>Division by two\<close>

text \<open>
In order to divide a number by two, a Turing machine can shift all symbols on
the tape containing the number to the left, of course without overwriting
the start symbol.

The next command implements the left shift. It scans the tape $j$ from right to
left and memorizes the current symbol on the last tape. It works very similar to
@{const cmd_double} only in the opposite direction. Upon reaching the start
symbol, it moves the head one cell to the right.
\<close>

definition cmd_halve :: "tapeidx \<Rightarrow> command" where
  "cmd_halve j rs \<equiv>
    (if rs ! j = 1 then 1 else 0,
     (map (\<lambda>i.
       if i = j then
         if rs ! j = \<triangleright> then (rs ! i, Right)
         else if last rs = \<triangleright> then (\<box>, Left)
         else (tosym (todigit (last rs)), Left)
       else if i = length rs - 1 then (tosym (todigit (rs ! j)), Stay)
       else (rs ! i, Stay)) [0..<length rs]))"

lemma turing_command_halve:
  assumes "G \<ge> 4" and "0 < j" and "j < k"
  shows "turing_command (Suc k) 1 G (cmd_halve j)"
proof
  show "\<And>gs. length gs = Suc k \<Longrightarrow> length ([!!] cmd_halve j gs) = length gs"
    using cmd_halve_def by simp
  moreover have "0 \<noteq> Suc k - 1"
    using assms by simp
  ultimately show "\<And>gs. length gs = Suc k \<Longrightarrow> 0 < Suc k \<Longrightarrow> cmd_halve j gs [.] 0 = gs ! 0"
    using assms cmd_halve_def by (smt (verit) One_nat_def ab_semigroup_add_class.add_ac(1) diff_Suc_1
      length_map neq0_conv nth_map nth_upt plus_1_eq_Suc prod.sel(1) prod.sel(2))
  show "cmd_halve j gs [.] j' < G"
    if "length gs = Suc k" "(\<And>i. i < length gs \<Longrightarrow> gs ! i < G)" "j' < length gs"
    for gs j'
  proof -
    have "cmd_halve j gs [!] j' =
      (if j' = j then
         if gs ! j = \<triangleright> then (gs ! j', Right)
         else if last gs = \<triangleright> then (\<box>, Left)
         else (tosym (todigit (last gs)), Left)
       else if j' = length gs - 1 then (tosym (todigit (gs ! j)), Stay)
       else (gs ! j', Stay))"
      using cmd_halve_def that(3) by simp
    moreover consider "j' = j" | "j' = k" | "j' \<noteq> j \<and> j' \<noteq> k"
      by auto
    ultimately show ?thesis
      using that assms by (cases) simp_all
  qed
  show "\<And>gs. length gs = Suc k \<Longrightarrow> [*] (cmd_halve j gs) \<le> 1"
    using cmd_halve_def by simp
qed

lemma sem_cmd_halve_2:
  assumes "j < k"
    and "bit_symbols xs"
    and "length tps = Suc k"
    and "i \<le> length xs"
    and "i > 0"
    and "z = \<zero> \<or> z = \<one>"
    and "tps ! j = (\<lfloor>xs\<rfloor>, i)"
    and "tps ! k = \<lceil>z\<rceil>"
    and "tps' = tps[j := tps ! j |:=| z |-| 1, k := \<lceil>xs ! (i - 1)\<rceil>]"
  shows "sem (cmd_halve j) (0, tps) = (0, tps')"
proof (rule semI)
  show "proper_command (Suc k) (cmd_halve j)"
    using cmd_halve_def by simp
  show "length tps = Suc k" "length tps' = Suc k"
    using assms(3,9) by simp_all
  define rs where "rs = read tps"
  then have lenrs: "length rs = Suc k"
    using assms(3) read_length by simp
  have rsj: "rs ! j = xs ! (i - 1)"
    using rs_def assms tapes_at_read' contents_inbounds
    by (metis fst_conv le_imp_less_Suc less_imp_le_nat snd_conv)
  then have rsj': "rs ! j > 1"
    using assms Suc_1 Suc_diff_1 Suc_le_lessD by (metis eval_nat_numeral(3) less_Suc_eq)
  then show "fst (cmd_halve j (read tps)) = 0"
    using cmd_halve_def rs_def by simp
  have lastrs: "last rs = z"
    using assms rs_def onesie_read tapes_at_read'
    by (metis diff_Suc_1 last_conv_nth length_0_conv lenrs lessI nat.simps(3))
  show "act (cmd_halve j (read tps) [!] j') (tps ! j') = tps' ! j'" if "j' < Suc k" for j'
  proof -
    have "j' < length rs"
      using that lenrs by simp
    then have *: "cmd_halve j rs [!] j' =
      (if j' = j then
         if rs ! j = \<triangleright> then (rs ! j', Right)
         else if last rs = \<triangleright> then (\<box>, Left)
         else (tosym (todigit (last rs)), Left)
       else if j' = length rs - 1 then (tosym (todigit (rs ! j)), Stay)
       else (rs ! j', Stay))"
      using cmd_halve_def by simp
    consider "j' = j" | "j' = k" | "j' \<noteq> j \<and> j' \<noteq> k"
      by auto
    then show ?thesis
    proof (cases)
      case 1
      then have "cmd_halve j (read tps) [!] j' = (tosym (todigit (last rs)), Left)"
        using rs_def rsj' lastrs * assms(6) by auto
      then have "cmd_halve j (read tps) [!] j' = (z, Left)"
        using lastrs assms(6) by auto
      moreover have "tps' ! j' = tps ! j |:=| z |-| 1"
        using 1 assms(1,3,9) by simp
      ultimately show ?thesis
        using act_Left' 1 that rs_def by metis
    next
      case 2
      then have "cmd_halve j (read tps) [!] j' = (tosym (todigit (rs ! j)), Stay)"
        using rs_def * lenrs assms(1) by simp
      moreover have "tps' ! j' = \<lceil>xs ! (i - 1)\<rceil>"
        using assms 2 by simp
      moreover have "tps ! j' = \<lceil>z\<rceil>"
        using assms 2 by simp
      moreover have "tosym (todigit (rs ! j)) = xs ! (i - 1)"
      proof -
        have "xs ! (i - 1) = \<zero> \<or> xs ! (i - 1) = \<one>"
          using rsj rs_def assms by simp
        then show ?thesis
          using One_nat_def add_2_eq_Suc' numeral_3_eq_3 rsj by presburger
      qed
      ultimately show ?thesis
        using act_onesie by simp
    next
      case 3
      then show ?thesis
        using * act_Stay that assms lenrs rs_def by simp
    qed
  qed
qed

lemma sem_cmd_halve_1:
  assumes "j < k"
    and "bit_symbols xs"
    and "length tps = Suc k"
    and "0 < length xs"
    and "tps ! j = (\<lfloor>xs\<rfloor>, length xs)"
    and "tps ! k = \<lceil>\<triangleright>\<rceil>"
    and "tps' = tps[j := tps ! j |:=| \<box> |-| 1, k := \<lceil>xs ! (length xs - 1)\<rceil>]"
  shows "sem (cmd_halve j) (0, tps) = (0, tps')"
proof (rule semI)
  show "proper_command (Suc k) (cmd_halve j)"
    using cmd_halve_def by simp
  show "length tps = Suc k" "length tps' = Suc k"
    using assms(3,7) by simp_all
  define rs where "rs = read tps"
  then have lenrs: "length rs = Suc k"
    using assms(3) read_length by simp
  have rsj: "rs ! j = xs ! (length xs - 1)"
    using rs_def assms tapes_at_read' contents_inbounds
    by (metis One_nat_def fst_conv le_eq_less_or_eq le_imp_less_Suc snd_conv)
  then have rsj': "rs ! j > 1"
    using assms(2,4) by (metis One_nat_def Suc_1 diff_less lessI less_add_Suc2 numeral_3_eq_3 plus_1_eq_Suc)
  then show "fst (cmd_halve j (read tps)) = \<box>"
    using cmd_halve_def rs_def by simp
  have lastrs: "last rs = \<triangleright>"
    using assms rs_def onesie_read tapes_at_read'
    by (metis diff_Suc_1 last_conv_nth length_0_conv lenrs lessI nat.simps(3))
  show "act (cmd_halve j (read tps) [!] j') (tps ! j') = tps' ! j'" if "j' < Suc k" for j'
  proof -
    have "j' < length rs"
      using that lenrs by simp
    then have *: "cmd_halve j rs [!] j' =
      (if j' = j then
         if rs ! j = \<triangleright> then (rs ! j', Right)
         else if last rs = \<triangleright> then (\<box>, Left)
         else (tosym (todigit (last rs)), Left)
       else if j' = length rs - 1 then (tosym (todigit (rs ! j)), Stay)
       else (rs ! j', Stay))"
      using cmd_halve_def by simp
    consider "j' = j" | "j' = k" | "j' \<noteq> j \<and> j' \<noteq> k"
      by auto
    then show ?thesis
    proof (cases)
      case 1
      then have "cmd_halve j (read tps) [!] j' = (\<box>, Left)"
        using rs_def rsj' lastrs * by simp
      then show ?thesis
        using act_Left' 1 that rs_def assms(1,3,7) by simp
    next
      case 2
      then have "cmd_halve j (read tps) [!] j' = (tosym (todigit (rs ! j)), Stay)"
        using rs_def * lenrs assms(1) by simp
      moreover have "tps' ! j' = \<lceil>xs ! (length xs - 1)\<rceil>"
        using assms 2 by simp
      moreover have "tps ! j' = \<lceil>\<triangleright>\<rceil>"
        using assms 2 by simp
      ultimately show ?thesis
        using act_onesie assms 2 that rs_def rsj
        by (smt (z3) One_nat_def Suc_1 add_2_eq_Suc' diff_less numeral_3_eq_3 zero_less_one)
    next
      case 3
      then show ?thesis
        using * act_Stay that assms lenrs rs_def by simp
    qed
  qed
qed

lemma sem_cmd_halve_0:
  assumes "j < k"
    and "length tps = Suc k"
    and "tps ! j = (\<lfloor>xs\<rfloor>, 0)"
    and "tps ! k = \<lceil>z\<rceil>"
    and "tps' = tps[j := tps ! j |+| 1, k := \<lceil>\<zero>\<rceil>]"
  shows "sem (cmd_halve j) (0, tps) = (1, tps')"
proof (rule semI)
  show "proper_command (Suc k) (cmd_halve j)"
    using cmd_halve_def by simp
  show "length tps = Suc k" "length tps' = Suc k"
    using assms(2,5) by simp_all
  show "fst (cmd_halve j (read tps)) = 1"
    using cmd_halve_def assms contents_at_0 tapes_at_read'
    by (smt (verit) fst_conv le_eq_less_or_eq not_less not_less_eq snd_conv)
  show "act (cmd_halve j (read tps) [!] j') (tps ! j') = tps' ! j'" if "j' < Suc k" for j'
  proof -
    define gs where "gs = read tps"
    then have "length gs = Suc k"
      using assms by (simp add: read_length)
    then have "j' < length gs"
      using that by simp
    then have *: "cmd_halve j gs [!] j' =
      (if j' = j then
         if gs ! j = \<triangleright> then (gs ! j', Right)
         else if last gs = \<triangleright> then (\<box>, Left)
         else (tosym (todigit (last gs)), Left)
       else if j' = length gs - 1 then (tosym (todigit (gs ! j)), Stay)
       else (gs ! j', Stay))"
      using cmd_halve_def by simp
    have gsj: "gs ! j = \<triangleright>"
      using gs_def assms(1,2,3) by (metis contents_at_0 fstI less_Suc_eq sndI tapes_at_read')
    consider "j' = j" | "j' = k" | "j' \<noteq> j \<and> j' \<noteq> k"
      by auto
    then show ?thesis
    proof (cases)
      case 1
      then have "cmd_halve j (read tps) [!] j' = (gs ! j', Right)"
        using gs_def gsj * by simp
      then show ?thesis
        using act_Right assms 1 that gs_def by (metis length_list_update lessI nat_neq_iff nth_list_update)
    next
      case 2
      then have "cmd_halve j (read tps) [!] j' = (tosym (todigit (gs ! j)), Stay)"
        using gs_def * \<open>length gs = Suc k\<close> assms(1) by simp
      moreover have "tps' ! j' = \<lceil>\<zero>\<rceil>"
        using assms 2 by simp
      moreover have "tps ! j' = \<lceil>z\<rceil>"
        using assms 2 by simp
      ultimately show ?thesis
        using act_onesie assms 2 that gs_def gsj
        by (smt (verit, best) One_nat_def Suc_1 add_2_eq_Suc' less_Suc_eq_0_disj less_numeral_extra(3) nat.inject numeral_3_eq_3)
    next
      case 3
      then show ?thesis
        using * act_Stay that assms(2,5) \<open>length gs = Suc k\<close> gs_def by simp
    qed
  qed
qed

definition tm_halve :: "tapeidx \<Rightarrow> machine" where
  "tm_halve j \<equiv> [cmd_halve j]"

lemma tm_halve_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "0 < j" and "j < k"
  shows "turing_machine (Suc k) G (tm_halve j)"
  using tm_halve_def turing_command_halve assms by auto

lemma exe_cmd_halve_0:
  assumes "j < k"
    and "length tps = Suc k"
    and "tps ! j = (\<lfloor>xs\<rfloor>, 0)"
    and "tps ! k = \<lceil>z\<rceil>"
    and "tps' = tps[j := tps ! j |+| 1, k := \<lceil>\<zero>\<rceil>]"
  shows "exe (tm_halve j) (0, tps) = (1, tps')"
  using assms sem_cmd_halve_0 tm_halve_def exe_lt_length by simp

lemma execute_cmd_halve_0:
  assumes "j < k"
    and "length tps = Suc k"
    and "tps ! j = (\<lfloor>[]\<rfloor>, 0)"
    and "tps ! k = \<lceil>\<triangleright>\<rceil>"
    and "tps' = tps[j := tps ! j |+| 1, k := \<lceil>\<zero>\<rceil>]"
  shows "execute (tm_halve j) (0, tps) 1 = (1, tps')"
  using tm_halve_def exe_lt_length sem_cmd_halve_0 assms by simp

definition shift :: "tape \<Rightarrow> nat \<Rightarrow> tape" where
  "shift tp y \<equiv> (\<lambda>x. if x \<le> y then (fst tp) x else (fst tp) (Suc x), y)"

lemma shift_update: "y > 0 \<Longrightarrow> shift tp y |:=| (fst tp) (Suc y) |-| 1 = shift tp (y - 1)"
  unfolding shift_def by fastforce

lemma shift_contents_0:
  assumes "length xs > 0"
  shows "shift (\<lfloor>xs\<rfloor>, length xs) 0 = (\<lfloor>tl xs\<rfloor>, 0)"
proof -
  have "shift (\<lfloor>xs\<rfloor>, length xs) 0 = (\<lfloor>drop 1 xs\<rfloor>, 0)"
    using shift_def contents_def by fastforce
  then show ?thesis
    by (simp add: drop_Suc)
qed

lemma proper_bit_symbols: "bit_symbols ws \<Longrightarrow> proper_symbols ws"
  by auto

lemma bit_symbols_shift:
  assumes "t < length ws" and "bit_symbols ws"
  shows "|.| (shift (\<lfloor>ws\<rfloor>, length ws) (length ws - t)) \<noteq> 1"
  using assms shift_def contents_def nat_neq_iff proper_bit_symbols by simp

lemma exe_cmd_halve_1:
  assumes "j < k"
    and "length tps = Suc k"
    and "bit_symbols xs"
    and "length xs > 0"
    and "tps ! j = (\<lfloor>xs\<rfloor>, length xs)"
    and "tps ! k = \<lceil>\<triangleright>\<rceil>"
    and "tps' = tps[j := tps ! j |:=| \<box> |-| 1, k := \<lceil>xs ! (length xs - 1)\<rceil>]"
  shows "exe (tm_halve j) (0, tps) = (0, tps')"
  using tm_halve_def exe_lt_length sem_cmd_halve_1 assms by simp

lemma shift_contents_eq_take_drop:
  assumes "length xs > 0"
    and "ys = take i xs @ drop (Suc i) xs"
    and "i > 0"
    and "i < length xs"
  shows "shift (\<lfloor>xs\<rfloor>, length xs) i = (\<lfloor>ys\<rfloor>, i)"
proof -
  have "shift (\<lfloor>xs\<rfloor>, length xs) i = (\<lambda>x. if x \<le> i then \<lfloor>xs\<rfloor> x else \<lfloor>xs\<rfloor> (Suc x), i)"
    using shift_def by auto
  moreover have "(\<lambda>x. if x \<le> i then \<lfloor>xs\<rfloor> x else \<lfloor>xs\<rfloor> (Suc x)) = \<lfloor>take i xs @ drop (Suc i) xs\<rfloor>"
    (is "?l = ?r")
  proof
    fix x
    consider "x = 0" | "0 < x \<and> x \<le> i" | "i < x \<and> x \<le> length xs - 1" | "length xs - 1 < x"
      by linarith
    then show "?l x = ?r x"
    proof (cases)
      case 1
      then show ?thesis
        using assms contents_def by simp
    next
      case 2
      then have "?l x = \<lfloor>xs\<rfloor> x"
        by simp
      then have lhs: "?l x = xs ! (x - 1)"
        using assms 2 by simp
      have "?r x = (take i xs @ drop (Suc i) xs) ! (x - 1)"
        using assms 2 by auto
      then have "?r x = xs ! (x - 1)"
        using assms(4) 2
        by (metis diff_less le_eq_less_or_eq length_take less_trans min_absorb2 nth_append nth_take zero_less_one)
      then show ?thesis
        using lhs by simp
    next
      case 3
      then have "?l x = \<lfloor>xs\<rfloor> (Suc x)"
        by simp
      then have lhs: "?l x = xs ! x"
        using 3 assms by auto
      have "?r x = (take i xs @ drop (Suc i) xs) ! (x - 1)"
        using assms 3 by auto
      then have "?r x = drop (Suc i) xs ! (x - 1 - i)"
        using assms(3,4) 3
        by (smt (z3) Suc_diff_1 dual_order.strict_trans length_take less_Suc_eq min_absorb2 nat_less_le nth_append)
      then have "?r x = xs ! x"
        using assms 3 by simp
      then show ?thesis
        using lhs by simp
    next
      case 4
      then show ?thesis
        using contents_def by auto
    qed
  qed
  ultimately show ?thesis
    using assms(2) by simp
qed

lemma exe_cmd_halve_2:
  assumes "j < k"
    and "bit_symbols xs"
    and "length tps = Suc k"
    and "i \<le> length xs"
    and "i > 0"
    and "z = \<zero> \<or> z = \<one>"
    and "tps ! j = (\<lfloor>xs\<rfloor>, i)"
    and "tps ! k = \<lceil>z\<rceil>"
    and "tps' = tps[j := tps ! j |:=| z |-| 1, k := \<lceil>xs ! (i - 1)\<rceil>]"
  shows "exe (tm_halve j) (0, tps) = (0, tps')"
  using tm_halve_def exe_lt_length sem_cmd_halve_2 assms by simp

lemma shift_contents_length_minus_1:
  assumes "length xs > 0"
  shows "shift (\<lfloor>xs\<rfloor>, length xs) (length xs - 1) = (\<lfloor>xs\<rfloor>, length xs) |:=| \<box> |-| 1"
  using contents_def shift_def assms by fastforce

lemma execute_tm_halve_1_less:
  assumes "j < k"
    and "length tps = Suc k"
    and "bit_symbols xs"
    and "length xs > 0"
    and "tps ! j = (\<lfloor>xs\<rfloor>, length xs)"
    and "tps ! k = \<lceil>\<triangleright>\<rceil>"
    and "t \<ge> 1"
    and "t \<le> length xs"
  shows "execute (tm_halve j) (0, tps) t = (0, tps
      [j := shift (tps ! j) (length xs - t),
       k := \<lceil>xs ! (length xs - t)\<rceil>])"
  using assms(7,8)
proof (induction t rule: nat_induct_at_least)
  case base
  have "execute (tm_halve j) (0, tps) 1 = exe (tm_halve j) (0, tps)"
    by simp
  also have "... = (0, tps[j := tps ! j |:=| \<box> |-| 1, k := \<lceil>xs ! (length xs - 1)\<rceil>])"
    using assms exe_cmd_halve_1 by simp
  also have "... = (0, tps[j := shift (tps ! j) (length xs - 1), k := \<lceil>xs ! (length xs - 1)\<rceil>])"
    using shift_contents_length_minus_1 assms(4,5) by simp
  finally show ?case .
next
  case (Suc t)
  then have "t < length xs"
    by simp
  let ?ys = "take (length xs - t) xs @ drop (Suc (length xs - t)) xs"
  have "execute (tm_halve j) (0, tps) (Suc t) = exe (tm_halve j) (execute (tm_halve j) (0, tps) t)"
    by simp
  also have "... = exe (tm_halve j) (0, tps
      [j := shift (tps ! j) (length xs - t),
       k := \<lceil>xs ! (length xs - t)\<rceil>])"
    using Suc by simp
  also have "... = exe (tm_halve j) (0, tps
      [j := shift (\<lfloor>xs\<rfloor>, length xs) (length xs - t),
       k := \<lceil>xs ! (length xs - t)\<rceil>])"
    using assms(5) by simp
  also have "... = exe (tm_halve j) (0, tps
      [j := (\<lfloor>?ys\<rfloor>, length xs - t),
       k := \<lceil>xs ! (length xs - t)\<rceil>])"
      (is "_ = exe _ (0, ?tps)")
    using shift_contents_eq_take_drop Suc assms by simp
  also have "... = (0, ?tps
      [j := ?tps ! j |:=| (xs ! (length xs - t)) |-| 1,
       k := \<lceil>?ys ! (length xs - t - 1)\<rceil>])"
  proof -
    let ?i = "length xs - t"
    let ?z = "xs ! ?i"
    have 1: "bit_symbols ?ys"
      using assms(3) by (intro bit_symbols_append) simp_all
    have 2: "length ?tps = Suc k"
      using assms(2) by simp
    have 3: "?i \<le> length ?ys"
      using Suc assms by simp
    have 4: "?i > 0"
      using Suc assms by simp
    have 5: "?z = 2 \<or> ?z = 3"
      using assms(3,4) Suc by simp
    have 6: "?tps ! j = (\<lfloor>?ys\<rfloor>, ?i)"
      using assms(1,2) by simp
    have 7: "?tps ! k = \<lceil>?z\<rceil>"
      using assms(2) by simp
    then show ?thesis
      using exe_cmd_halve_2[OF assms(1) 1 2 3 4 5 6 7] by simp
  qed
  also have "... = (0, tps
      [j := ?tps ! j |:=| (xs ! (length xs - t)) |-| 1,
       k := \<lceil>?ys ! (length xs - t - 1)\<rceil>])"
    using assms by (smt (z3) list_update_overwrite list_update_swap)
  also have "... = (0, tps
      [j := (\<lfloor>?ys\<rfloor>, length xs - t) |:=| (xs ! (length xs - t)) |-| 1,
       k := \<lceil>?ys ! (length xs - t - 1)\<rceil>])"
    using assms(1,2) by simp
  also have "... = (0, tps
      [j := shift (\<lfloor>xs\<rfloor>, length xs) (length xs - Suc t),
       k := \<lceil>xs ! (length xs - (Suc t))\<rceil>])"
  proof -
    have "(\<lfloor>?ys\<rfloor>, length xs - t) |:=| xs ! (length xs - t) |-| 1 =
        shift (\<lfloor>xs\<rfloor>, length xs) (length xs - t) |:=| (xs ! (length xs - t)) |-| 1"
      using shift_contents_eq_take_drop One_nat_def Suc Suc_le_lessD \<open>t < length xs\<close> assms(4) diff_less zero_less_diff
      by presburger
    also have "... = shift (\<lfloor>xs\<rfloor>, length xs) (length xs - Suc t)"
      using shift_update[of "length xs - t" "(\<lfloor>xs\<rfloor>, length xs)"] assms Suc by simp
    finally have "(\<lfloor>?ys\<rfloor>, length xs - t) |:=| xs ! (length xs - t) |-| 1 =
        shift (\<lfloor>xs\<rfloor>, length xs) (length xs - Suc t)" .
    moreover have "?ys ! (length xs - t - 1) = xs ! (length xs - Suc t)"
      using Suc assms \<open>t < length xs\<close>
      by (metis (no_types, lifting) diff_Suc_eq_diff_pred diff_Suc_less diff_commute diff_less
        length_take min_less_iff_conj nth_append nth_take zero_less_diff zero_less_one)
    ultimately show ?thesis
      by simp
  qed
  also have "... = (0, tps
      [j := shift (tps ! j) (length xs - (Suc t)),
       k := \<lceil>xs ! (length xs - (Suc t))\<rceil>])"
    using assms(5) by simp
  finally show ?case .
qed

lemma execute_tm_halve_1:
  assumes "j < k"
    and "length tps = Suc k"
    and "bit_symbols xs"
    and "length xs > 0"
    and "tps ! j = (\<lfloor>xs\<rfloor>, length xs)"
    and "tps ! k = \<lceil>\<triangleright>\<rceil>"
    and "tps' = tps[j := (\<lfloor>tl xs\<rfloor>, 1), k := \<lceil>\<zero>\<rceil>]"
  shows "execute (tm_halve j) (0, tps) (Suc (length xs)) = (1, tps')"
proof -
  have "execute (tm_halve j) (0, tps) (length xs) = (0, tps[j := shift (tps ! j) 0, k := \<lceil>xs ! 0\<rceil>])"
    using execute_tm_halve_1_less[OF assms(1-6), where ?t="length xs"] assms(4) by simp
  also have "... = (0, tps[j := shift (\<lfloor>xs\<rfloor>, length xs) 0, k := \<lceil>xs ! 0\<rceil>])"
    using assms(5) by simp
  also have "... = (0, tps[j := (\<lfloor>tl xs\<rfloor>, 0), k := \<lceil>xs ! 0\<rceil>])"
    using shift_contents_0 assms(4) by simp
  finally have "execute (tm_halve j) (0, tps) (length xs) = (0, tps[j := (\<lfloor>tl xs\<rfloor>, 0), k := \<lceil>xs ! 0\<rceil>])" .
  then have "execute (tm_halve j) (0, tps) (Suc (length xs)) =
      exe (tm_halve j) (0, tps[j := (\<lfloor>tl xs\<rfloor>, 0), k := \<lceil>xs ! 0\<rceil>])"
      (is "_ = exe _ (0, ?tps)")
    by simp
  also have "... = (1, ?tps[j := (\<lfloor>tl xs\<rfloor>, 0) |+| 1, k := \<lceil>\<zero>\<rceil>])"
    using assms(1,2) exe_cmd_halve_0 by simp
  also have "... = (1, tps[j := (\<lfloor>tl xs\<rfloor>, 0) |+| 1, k := \<lceil>\<zero>\<rceil>])"
    using assms(1,2) by (metis (no_types, opaque_lifting) list_update_overwrite list_update_swap)
  also have "... = (1, tps[j := (\<lfloor>tl xs\<rfloor>, 1), k := \<lceil>\<zero>\<rceil>])"
    by simp
  finally show ?thesis
    using assms(7) by simp
qed

lemma execute_tm_halve:
  assumes "j < k"
    and "length tps = Suc k"
    and "bit_symbols xs"
    and "tps ! j = (\<lfloor>xs\<rfloor>, length xs)"
    and "tps ! k = \<lceil>\<triangleright>\<rceil>"
    and "tps' = tps[j := (\<lfloor>tl xs\<rfloor>, 1), k := \<lceil>\<zero>\<rceil>]"
  shows "execute (tm_halve j) (0, tps) (Suc (length xs)) = (1, tps')"
  using execute_cmd_halve_0 execute_tm_halve_1 assms by (cases "length xs = 0") simp_all

lemma transforms_tm_halve:
  assumes "j < k"
    and "length tps = Suc k"
    and "bit_symbols xs"
    and "tps ! j = (\<lfloor>xs\<rfloor>, length xs)"
    and "tps ! k = \<lceil>\<triangleright>\<rceil>"
    and "tps' = tps[j := (\<lfloor>tl xs\<rfloor>, 1), k := \<lceil>\<zero>\<rceil>]"
  shows "transforms (tm_halve j) tps (Suc (length xs)) tps'"
  using execute_tm_halve assms tm_halve_def transforms_def transits_def by auto

lemma transforms_tm_halve2:
  assumes "j < k"
    and "length tps = k"
    and "bit_symbols xs"
    and "tps ! j = (\<lfloor>xs\<rfloor>, length xs)"
    and "tps' = tps[j := (\<lfloor>tl xs\<rfloor>, 1)]"
  shows "transforms (tm_halve j) (tps @ [\<lceil>\<triangleright>\<rceil>]) (Suc (length xs)) (tps' @ [\<lceil>\<zero>\<rceil>])"
proof -
  let ?tps = "tps @ [\<lceil>\<triangleright>\<rceil>]"
  let ?tps' = "tps' @ [\<lceil>\<zero>\<rceil>]"
  have "?tps ! j = (\<lfloor>xs\<rfloor>, length xs)" "?tps ! k = \<lceil>\<triangleright>\<rceil>"
    using assms by (simp_all add: nth_append)
  moreover have "?tps' ! j = (\<lfloor>tl xs\<rfloor>, 1)" "?tps' ! k = \<lceil>\<zero>\<rceil>"
    using assms by (simp_all add: nth_append)
  moreover have "length ?tps = Suc k"
    using assms(2) by simp
  ultimately show ?thesis
    using assms transforms_tm_halve[OF assms(1), where ?tps="?tps" and ?tps'="?tps'" and ?xs=xs]
    by (metis length_list_update list_update_append1 list_update_length)
qed

text \<open>
The next Turing machine removes the memorization tape from @{const tm_halve}.
\<close>

definition tm_halve' :: "tapeidx \<Rightarrow> machine" where
  "tm_halve' j \<equiv> cartesian (tm_halve j) 4"

lemma bounded_write_tm_halve:
  assumes "j < k"
  shows "bounded_write (tm_halve j) k 4"
  unfolding bounded_write_def
proof standard+
  fix q :: nat and rs :: "symbol list"
  assume q: "q < length (tm_halve j)" and lenrs: "length rs = Suc k"
  have "k < length rs"
    using lenrs by simp
  then have "cmd_halve j rs [!] k =
    (if k = j then
        if rs ! j = \<triangleright> then (rs ! k, Right)
        else if last rs = \<triangleright> then (\<box>, Left)
        else (tosym (todigit (last rs)), Left)
      else if k = length rs - 1 then (tosym (todigit (rs ! j)), Stay)
      else (rs ! k, Stay))"
    using cmd_halve_def by simp
  then have "cmd_halve j rs [!] k = (tosym (todigit (rs ! j)), Stay)"
    using assms lenrs by simp
  then have "cmd_halve j rs [.] k = tosym (todigit (rs ! j))"
    by simp
  moreover have "(tm_halve j ! q) rs [.] k = cmd_halve j rs [.] k"
    using tm_halve_def q by simp
  ultimately show "(tm_halve j ! q) rs [.] k < 4"
    by simp
qed

lemma immobile_tm_halve:
  assumes "j < k"
  shows "immobile (tm_halve j) k (Suc k)"
proof standard+
  fix q :: nat and rs :: "symbol list"
  assume q: "q < length (tm_halve j)" and lenrs: "length rs = Suc k"
  have "k < length rs"
    using lenrs by simp
  then have "cmd_halve j rs [!] k =
    (if k = j then
        if rs ! j = \<triangleright> then (rs ! k, Right)
        else if last rs = \<triangleright> then (\<box>, Left)
        else (tosym (todigit (last rs)), Left)
      else if k = length rs - 1 then (tosym (todigit (rs ! j)), Stay)
      else (rs ! k, Stay))"
    using cmd_halve_def by simp
  then have "cmd_halve j rs [!] k = (tosym (todigit (rs ! j)), Stay)"
    using assms lenrs by simp
  then have "cmd_halve j rs [~] k = Stay"
    by simp
  moreover have "(tm_halve j ! q) rs [~] k = cmd_halve j rs [~] k"
    using tm_halve_def q by simp
  ultimately show "(tm_halve j ! q) rs [~] k = Stay"
    by simp
qed

lemma tm_halve'_tm:
  assumes "G \<ge> 4" and "0 < j" and "j < k"
  shows "turing_machine k G (tm_halve' j)"
  using tm_halve'_def tm_halve_tm assms cartesian_tm by simp

lemma transforms_tm_halve' [transforms_intros]:
  assumes "j > 0" and "j < k"
    and "length tps = k"
    and "bit_symbols xs"
    and "tps ! j = (\<lfloor>xs\<rfloor>, length xs)"
    and "tps' = tps[j := (\<lfloor>tl xs\<rfloor>, 1)]"
  shows "transforms (tm_halve' j) tps (Suc (length xs)) tps'"
  unfolding tm_halve'_def
proof (rule cartesian_transforms_onesie[OF tm_halve_tm immobile_tm_halve _ _ bounded_write_tm_halve assms(3), where ?G=4];
    (simp add: assms)?)
  show "2 \<le> k" and "2 \<le> k"
    using assms(1,2) by simp_all
  show "transforms (tm_halve j) (tps @ [\<lceil>Suc 0\<rceil>]) (Suc (length xs))
     (tps[j := (\<lfloor>tl xs\<rfloor>, Suc 0)] @ [\<lceil>\<zero>\<rceil>])"
    using transforms_tm_halve2 assms by simp
qed

lemma num_tl_div_2: "num (tl xs) = num xs div 2"
proof (cases "xs = []")
  case True
  then show ?thesis
    by (simp add: num_def)
next
  case False
  then have *: "xs = hd xs # tl xs"
    by simp
  then have "num xs = todigit (hd xs) + 2 * num (tl xs)"
    using num_Cons by metis
  then show ?thesis
    by simp
qed

lemma canrepr_div_2: "canrepr (n div 2) = tl (canrepr n)"
  using canreprI canrepr canonical_canrepr num_tl_div_2 canonical_tl
  by (metis hd_Cons_tl list.sel(2))

corollary nlength_times2: "nlength (2 * n) \<le> Suc (nlength n)"
  using canrepr_div_2[of "2 * n"] by simp

corollary nlength_times2plus1: "nlength (2 * n + 1) \<le> Suc (nlength n)"
  using canrepr_div_2[of "2 * n + 1"] by simp

text \<open>
The next Turing machine is the one we actually use to divide a number by two.
First it moves to the end of the symbol sequence representing the number, then
it applies @{const tm_halve'}.
\<close>

definition tm_div2 :: "tapeidx \<Rightarrow> machine" where
  "tm_div2 j \<equiv> tm_right_until j {\<box>} ;; tm_left j ;; tm_halve' j"

lemma tm_div2_tm:
  assumes "G \<ge> 4" and "0 < j" and "j < k"
  shows "turing_machine k G (tm_div2 j)"
  unfolding tm_div2_def using tm_right_until_tm tm_left_tm tm_halve'_tm assms by simp

locale turing_machine_div2 =
  fixes j :: tapeidx
begin

definition "tm1 \<equiv> tm_right_until j {\<box>}"
definition "tm2 \<equiv> tm1 ;; tm_left j"
definition "tm3 \<equiv> tm2 ;; tm_halve' j"

lemma tm3_eq_tm_div2: "tm3 = tm_div2 j"
  unfolding tm3_def tm2_def tm1_def tm_div2_def by simp

context
  fixes tps0 :: "tape list" and k n :: nat
  assumes jk: "0 < j" "j < k" "length tps0 = k"
    and tps0: "tps0 ! j = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
begin

definition "tps1 \<equiv> tps0
  [j := (\<lfloor>n\<rfloor>\<^sub>N, Suc (nlength n))]"

lemma tm1 [transforms_intros]:
  assumes "ttt = Suc (nlength n)"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: tps1_def jk tps0 time: assms)
  have "rneigh (\<lfloor>n\<rfloor>\<^sub>N, Suc 0) {\<box>} (nlength n)"
  proof (intro rneighI)
    show "fst (\<lfloor>n\<rfloor>\<^sub>N, Suc 0) (snd (\<lfloor>n\<rfloor>\<^sub>N, Suc 0) + nlength n) \<in> {\<box>}"
      using contents_def by simp
    show "\<And>n'. n' < nlength n \<Longrightarrow> fst (\<lfloor>n\<rfloor>\<^sub>N, Suc 0) (snd (\<lfloor>n\<rfloor>\<^sub>N, Suc 0) + n') \<notin> {\<box>}"
      using bit_symbols_canrepr contents_def contents_outofbounds proper_symbols_canrepr
      by (metis One_nat_def Suc_leI add_diff_cancel_left' fst_eqD less_Suc_eq_0_disj less_nat_zero_code
        plus_1_eq_Suc singletonD snd_conv)
  qed
  then show "rneigh (tps0 ! j) {\<box>} (nlength n)"
    using tps0 by simp
qed

definition "tps2 \<equiv> tps0
  [j := (\<lfloor>n\<rfloor>\<^sub>N, nlength n)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 2 + nlength n"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def by (tform tps: tps1_def tps2_def jk assms)

definition "tps3 \<equiv> tps0
  [j := (\<lfloor>n div 2\<rfloor>\<^sub>N, 1)]"

lemma tm3:
  assumes "ttt = 2 * nlength n + 3"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: tps3_def tps2_def tps0 jk time: assms)
  show "bit_symbols (canrepr n)"
    using bit_symbols_canrepr .
  show "tps3 = tps2[j := (\<lfloor>tl (canrepr n)\<rfloor>, 1)]"
    using tps3_def tps2_def jk tps0 canrepr_div_2 by simp
qed

end

end  (* locale turing_machine_div2 *)

lemma transforms_tm_div2I [transforms_intros]:
  fixes tps tps' :: "tape list" and ttt k n :: nat and j :: tapeidx
  assumes "0 < j" "j < k"
    and "length tps = k"
    and "tps ! j = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 2 * nlength n + 3"
  assumes "tps' = tps[j := (\<lfloor>n div 2\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_div2 j) tps ttt tps'"
proof -
  interpret loc: turing_machine_div2 j .
  show ?thesis
    using loc.tm3_eq_tm_div2 loc.tm3 loc.tps3_def assms by simp
qed


subsection \<open>Modulo two\<close>

text \<open>
In this section we construct a Turing machine that writes to tape $j_2$ the
symbol @{text \<one>} or @{text \<box>} depending on whether the number on tape $j_1$ is
odd or even. If initially tape $j_2$ contained at most one symbol, it will
contain the numbers~1 or~0.
\<close>

lemma canrepr_odd: "odd n \<Longrightarrow> canrepr n ! 0 = \<one>"
proof -
  assume "odd n"
  then have "0 < n"
    by presburger
  then have len: "length (canrepr n) > 0"
    using nlength_0 by simp
  then have "canrepr n ! 0 = \<zero> \<or> canrepr n ! 0 = \<one>"
    using bit_symbols_canrepr by fastforce
  then show "canrepr n ! 0 = \<one>"
    using prepend_2_even len canrepr `odd n` `0 < n`
    by (metis gr0_implies_Suc length_Suc_conv nth_Cons_0)
qed

lemma canrepr_even: "even n \<Longrightarrow> 0 < n \<Longrightarrow> canrepr n ! 0 = \<zero>"
proof -
  assume "even n" "0 < n"
  then have len: "length (canrepr n) > 0"
    using nlength_0 by simp
  then have "canrepr n ! 0 = \<zero> \<or> canrepr n ! 0 = \<one>"
    using bit_symbols_canrepr by fastforce
  then show "canrepr n ! 0 = \<zero>"
    using prepend_3_odd len canrepr `even n` `0 < n`
    by (metis gr0_implies_Suc length_Suc_conv nth_Cons_0)
qed

definition "tm_mod2 j1 j2 \<equiv> tm_trans2 j1 j2 (\<lambda>z. if z = \<one> then \<one> else \<box>)"

lemma tm_mod2_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "0 < j2" and "j1 < k" and "j2 < k"
  shows "turing_machine k G (tm_mod2 j1 j2)"
  unfolding tm_mod2_def using assms tm_trans2_tm by simp

lemma transforms_tm_mod2I [transforms_intros]:
  assumes "j1 < length tps" and "0 < j2" and "j2 < length tps"
    and "b \<le> 1"
  assumes "tps ! j1 = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
    and "tps ! j2 = (\<lfloor>b\<rfloor>\<^sub>N, 1)"
  assumes "tps' = tps[j2 := (\<lfloor>n mod 2\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_mod2 j1 j2) tps 1 tps'"
proof -
  let ?f = "\<lambda>z::symbol. if z = \<one> then \<one> else \<box>"
  let ?tps = "tps[j2 := tps ! j2 |:=| (?f (tps :.: j1))]"
  have *: "transforms (tm_mod2 j1 j2) tps 1 ?tps"
    using transforms_tm_trans2I assms tm_mod2_def by metis

  have "tps :.: j1 = \<one>" if "odd n"
    using that canrepr_odd assms(5) contents_def
    by (metis One_nat_def diff_Suc_1 fst_conv gr_implies_not0 ncontents_1_blank_iff_zero odd_pos snd_conv)
  moreover have "tps :.: j1 = \<zero>" if "even n" and "n > 0"
    using that canrepr_even assms(5) contents_def
    by (metis One_nat_def diff_Suc_1 fst_conv gr_implies_not0 ncontents_1_blank_iff_zero snd_conv)
  moreover have "tps :.: j1 = \<box>" if "n = 0"
    using that canrepr_even assms(5) contents_def
    by simp
  ultimately have "tps :.: j1 = \<one> \<longleftrightarrow> odd n"
    by linarith
  then have f: "?f (tps :.: j1) = \<one> \<longleftrightarrow> odd n"
    by simp

  have tps_j2: "tps ! j2 |:=| (?f (tps :.: j1)) = ((\<lfloor>b\<rfloor>\<^sub>N)(1 := (?f (tps :.: j1))), 1)"
    using assms by simp

  have "tps ! j2 |:=| (?f (tps :.: j1)) = (\<lfloor>n mod 2\<rfloor>\<^sub>N, 1)"
  proof (cases "even n")
    case True
    then have "tps ! j2 |:=| (?f (tps :.: j1)) = ((\<lfloor>b\<rfloor>\<^sub>N)(1 := 0), 1)"
      using f tps_j2 by auto
    also have "... = (\<lfloor>[]\<rfloor>, 1)"
    proof (cases "b = 0")
      case True
      then have "\<lfloor>b\<rfloor>\<^sub>N = \<lfloor>[]\<rfloor>"
        using canrepr_0 by simp
      then show ?thesis
        by auto
    next
      case False
      then have "\<lfloor>b\<rfloor>\<^sub>N = \<lfloor>[\<one>]\<rfloor>"
        using canrepr_1 assms(4) by (metis One_nat_def bot_nat_0.extremum_uniqueI le_Suc_eq)
      then show ?thesis
        by (metis One_nat_def append.simps(1) append_Nil2 contents_append_update contents_blank_0 list.size(3))
    qed
    also have "... = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
      using canrepr_0 by simp
    finally show ?thesis
      using True by auto
  next
    case False
    then have "tps ! j2 |:=| (?f (tps :.: j1)) = ((\<lfloor>b\<rfloor>\<^sub>N)(1 := \<one>), 1)"
      using f tps_j2 by auto
    also have "... = (\<lfloor>[\<one>]\<rfloor>, 1)"
    proof (cases "b = 0")
      case True
      then have "\<lfloor>b\<rfloor>\<^sub>N = \<lfloor>[]\<rfloor>"
        using canrepr_0 by simp
      then show ?thesis
        by (metis One_nat_def append.simps(1) contents_snoc list.size(3))
    next
      case False
      then have "\<lfloor>b\<rfloor>\<^sub>N = \<lfloor>[\<one>]\<rfloor>"
        using canrepr_1 assms(4) by (metis One_nat_def bot_nat_0.extremum_uniqueI le_Suc_eq)
      then show ?thesis
        by auto
    qed
    also have "... = (\<lfloor>1\<rfloor>\<^sub>N, 1)"
      using canrepr_1 by simp
    also have "... = (\<lfloor>n mod 2\<rfloor>\<^sub>N, 1)"
      using False by (simp add: mod2_eq_if)
    finally show ?thesis
      by auto
  qed
  then show ?thesis
    using * assms(7) by auto
qed


subsection \<open>Boolean operations\<close>

text \<open>
In order to support Boolean operations, we represent the value True by the
number~1 and False by~0.
\<close>

abbreviation bcontents :: "bool \<Rightarrow> (nat \<Rightarrow> symbol)" ("\<lfloor>_\<rfloor>\<^sub>B") where
  "\<lfloor>b\<rfloor>\<^sub>B \<equiv> \<lfloor>if b then 1 else 0\<rfloor>\<^sub>N"

text \<open>
A tape containing a number contains the number~0 iff.\ there is a blank in cell
number~1.
\<close>

lemma read_ncontents_eq_0:
  assumes "tps ! j = (\<lfloor>n\<rfloor>\<^sub>N, 1)" and "j < length tps"
  shows "(read tps) ! j = \<box> \<longleftrightarrow> n = 0"
  using assms tapes_at_read'[of j tps] ncontents_1_blank_iff_zero by (metis prod.sel(1) prod.sel(2))


subsubsection \<open>And\<close>

text \<open>
The next Turing machine, when given two numbers $a, b \in \{0, 1\}$ on tapes
$j_1$ and $j_2$, writes to tape $j_1$ the number~1 if $a = b = 1$; otherwise it
writes the number~0. In other words, it overwrites tape $j_1$ with the logical
AND of the two tapes.
\<close>

definition tm_and :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_and j1 j2 \<equiv> IF \<lambda>rs. rs ! j1 = \<one> \<and> rs ! j2 = \<box> THEN tm_write j1 \<box> ELSE [] ENDIF"

lemma tm_and_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "0 < j1" and "j1 < k"
  shows "turing_machine k G (tm_and j1 j2)"
  using tm_and_def tm_write_tm Nil_tm assms turing_machine_branch_turing_machine by simp

locale turing_machine_and =
  fixes j1 j2 :: tapeidx
begin

context
  fixes tps0 :: "tape list" and k :: nat and a b :: nat
  assumes ab: "a < 2" "b < 2"
  assumes jk: "j1 < k" "j2 < k" "j1 \<noteq> j2" "0 < j1" "length tps0 = k"
  assumes tps0:
    "tps0 ! j1 = (\<lfloor>a\<rfloor>\<^sub>N, 1)"
    "tps0 ! j2 = (\<lfloor>b\<rfloor>\<^sub>N, 1)"
begin

definition "tps1 \<equiv> tps0
  [j1 := (\<lfloor>a = 1 \<and> b = 1\<rfloor>\<^sub>B, 1)]"

lemma tm: "transforms (tm_and j1 j2) tps0 3 tps1"
  unfolding tm_and_def
proof (tform)
  have "read tps0 ! j1 = \<lfloor>canrepr a\<rfloor> 1"
    using jk tps0 tapes_at_read'[of j1 tps0] by simp
  then have 1: "read tps0 ! j1 = \<one> \<longleftrightarrow> a = 1"
    using ab canrepr_odd contents_def ncontents_1_blank_iff_zero
    by (metis (mono_tags, lifting) One_nat_def diff_Suc_1 less_2_cases_iff odd_one)
  have "read tps0 ! j2 = \<lfloor>canrepr b\<rfloor> 1"
    using jk tps0 tapes_at_read'[of j2 tps0] by simp
  then have 2: "read tps0 ! j2 = \<one> \<longleftrightarrow> b = 1"
    using ab canrepr_odd contents_def ncontents_1_blank_iff_zero
    by (metis (mono_tags, lifting) One_nat_def diff_Suc_1 less_2_cases_iff odd_one)

  show "tps1 = tps0" if "\<not> (read tps0 ! j1 = \<one> \<and> read tps0 ! j2 = \<box>)"
  proof -
    have "a = (if a = 1 \<and> b = 1 then 1 else 0)"
      using that 1 2 ab jk by (metis One_nat_def less_2_cases_iff read_ncontents_eq_0 tps0(2))
    then have "tps0 ! j1 = (\<lfloor>a = 1 \<and> b = 1\<rfloor>\<^sub>B, 1)"
      using tps0 by simp
    then show ?thesis
      unfolding tps1_def using list_update_id[of tps0 j1] by simp
  qed
  show "tps1 = tps0[j1 := tps0 ! j1 |:=| \<box>]" if "read tps0 ! j1 = \<one> \<and> read tps0 ! j2 = \<box>"
  proof -
    have "(if a = 1 \<and> b = 1 then 1 else 0) = 0"
      using that 1 2 by simp
    moreover have "tps0 ! j1 |:=| \<box> = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    proof (cases "a = 0")
      case True
      then show ?thesis
        using tps0 jk by auto
    next
      case False
      then have "a = 1"
        using ab by simp
      then have "\<lfloor>a\<rfloor>\<^sub>N = \<lfloor>[\<one>]\<rfloor>"
        using canrepr_1 by simp
      moreover have "(\<lfloor>[\<one>]\<rfloor>, 1) |:=| \<box> = (\<lfloor>[]\<rfloor>, 1)"
        using contents_def by auto
      ultimately have "(\<lfloor>a\<rfloor>\<^sub>N, 1) |:=| \<box> = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
        using ncontents_0 by presburger
      then show ?thesis
        using tps0 jk by simp
    qed
    ultimately have "tps0 ! j1 |:=| \<box> = (\<lfloor>a = 1 \<and> b = 1\<rfloor>\<^sub>B, 1)"
      by (smt (verit, best))
    then show ?thesis
      unfolding tps1_def by auto
  qed
qed

end  (* context *)

end  (* locale *)

lemma transforms_tm_andI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps :: "tape list" and k :: nat and a b :: nat
  assumes "a < 2" "b < 2"
  assumes "length tps = k"
  assumes "j1 < k" "j2 < k" "j1 \<noteq> j2" "0 < j1"
  assumes
    "tps ! j1 = (\<lfloor>a\<rfloor>\<^sub>N, 1)"
    "tps ! j2 = (\<lfloor>b\<rfloor>\<^sub>N, 1)"
  assumes "tps' = tps
    [j1 := (\<lfloor>a = 1 \<and> b = 1\<rfloor>\<^sub>B, 1)]"
  shows "transforms (tm_and j1 j2) tps 3 tps'"
proof -
  interpret loc: turing_machine_and j1 j2 .
  show ?thesis
    using assms loc.tps1_def loc.tm by simp
qed


subsubsection \<open>Not\<close>

text \<open>
The next Turing machine turns the number~1 into~0 and vice versa.
\<close>

definition tm_not :: "tapeidx \<Rightarrow> machine" where
  "tm_not j \<equiv> IF \<lambda>rs. rs ! j = \<box> THEN tm_write j \<one> ELSE tm_write j \<box> ENDIF"

lemma tm_not_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "0 < j" and "j < k"
  shows "turing_machine k G (tm_not j)"
  using tm_not_def tm_write_tm assms turing_machine_branch_turing_machine by simp

locale turing_machine_not =
  fixes j :: tapeidx
begin

context
  fixes tps0 :: "tape list" and k :: nat and a :: nat
  assumes a: "a < 2"
  assumes jk: "j < k" "length tps0 = k"
  assumes tps0: "tps0 ! j = (\<lfloor>a\<rfloor>\<^sub>N, 1)"
begin

definition "tps1 \<equiv> tps0
  [j := (\<lfloor>a \<noteq> 1\<rfloor>\<^sub>B, 1)]"

lemma tm: "transforms (tm_not j) tps0 3 tps1"
  unfolding tm_not_def
proof (tform)
  have *: "read tps0 ! j = \<box> \<longleftrightarrow> a = 0"
    using read_ncontents_eq_0 jk tps0 by simp
  show "tps1 = tps0[j := tps0 ! j |:=| \<one>]" if "read tps0 ! j = \<box>"
  proof -
    have "a = 0"
      using a that * by simp
    then have "(\<lfloor>if a = 1 then 0 else 1\<rfloor>\<^sub>N, 1) = (\<lfloor>1\<rfloor>\<^sub>N, 1)"
      by simp
    moreover have "tps0 ! j |:=| \<one> = (\<lfloor>1\<rfloor>\<^sub>N, 1)"
      using tps0 canrepr_0 canrepr_1 `a = 0` contents_snoc
      by (metis One_nat_def append.simps(1) fst_conv list.size(3) snd_conv)
    ultimately have "tps0[j := tps0 ! j |:=| \<one>] = tps0[j := (\<lfloor>a \<noteq> 1\<rfloor>\<^sub>B, 1)]"
      by auto
    then show ?thesis
      using tps1_def by simp
  qed
  show "tps1 = tps0[j := tps0 ! j |:=| \<box>]" if "read tps0 ! j \<noteq> \<box>"
  proof -
    have "a = 1"
      using a that * by simp
    then have "(\<lfloor>if a = 1 then 0 else 1\<rfloor>\<^sub>N, 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
      by simp
    moreover have "tps0 ! j |:=| \<box> = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
      using tps0 canrepr_0 canrepr_1 `a = 1` contents_snoc
      by (metis Suc_1 append_self_conv2 contents_blank_0 fst_eqD fun_upd_upd nat.inject nlength_0_simp numeral_2_eq_2 snd_eqD)
    ultimately have "tps0[j := tps0 ! j |:=| \<box>] = tps0[j := (\<lfloor>a \<noteq> 1\<rfloor>\<^sub>B, 1)]"
      by auto
    then show ?thesis
      using tps1_def by simp
  qed
qed

end  (* context *)

end  (* locale *)

lemma transforms_tm_notI [transforms_intros]:
  fixes j :: tapeidx
  fixes tps tps' :: "tape list" and k :: nat and a :: nat
  assumes "j < k" "length tps = k"
    and "a < 2"
  assumes "tps ! j = (\<lfloor>a\<rfloor>\<^sub>N, 1)"
  assumes "tps' = tps
    [j := (\<lfloor>a \<noteq> 1\<rfloor>\<^sub>B, 1)]"
  shows "transforms (tm_not j) tps 3 tps'"
proof -
  interpret loc: turing_machine_not j .
  show ?thesis
    using assms loc.tps1_def loc.tm by simp
qed

end