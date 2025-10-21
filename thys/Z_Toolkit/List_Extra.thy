section \<open> Lists: extra functions and properties \<close>

theory List_Extra
  imports
  "HOL-Library.Sublist"
  "HOL-Library.Monad_Syntax"
  "HOL-Library.Prefix_Order"
  "Optics.Lens_Instances"
begin

subsection \<open> Useful Abbreviations \<close>

abbreviation "list_sum xs \<equiv> foldr (+) xs 0"

subsection \<open> Sets \<close>

lemma set_Fpow [simp]: "set xs \<in> Fpow A \<longleftrightarrow> set xs \<subseteq> A"
  by (auto simp add: Fpow_def)

lemma Fpow_as_Pow: "finite A \<Longrightarrow> Fpow A = Pow A"
  by (auto simp add: Pow_def Fpow_def finite_subset)

lemma Fpow_set [code]:
  "Fpow (set []) = {{}}"
  "Fpow (set (x # xs)) = (let A = Fpow (set xs) in A \<union> insert x ` A)"
  by (simp_all add: Fpow_as_Pow Pow_set del: set_simps)

subsection \<open> Folds \<close>

context abel_semigroup
begin

  lemma foldr_snoc: "foldr (\<^bold>*) (xs @ [x]) k = (foldr (\<^bold>*) xs k) \<^bold>* x"
    by (induct xs, simp_all add: commute left_commute)
  
end

subsection \<open> List Lookup \<close>

text \<open>
  The following variant of the standard @{text nth} function returns @{text "\<bottom>"} if the index is 
  out of range.
\<close>

primrec
  nth_el :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" ("_\<langle>_\<rangle>\<^sub>l" [90, 0] 91)
where
  "[]\<langle>i\<rangle>\<^sub>l = None"
| "(x # xs)\<langle>i\<rangle>\<^sub>l = (case i of 0 \<Rightarrow> Some x | Suc j \<Rightarrow> xs \<langle>j\<rangle>\<^sub>l)"

lemma nth_el_appendl[simp]: "i < length xs \<Longrightarrow> (xs @ ys)\<langle>i\<rangle>\<^sub>l = xs\<langle>i\<rangle>\<^sub>l"
proof (induct xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case 
  proof (cases i)
    case 0
    then show ?thesis by simp
  next
    case (Suc nat)
    with Cons show ?thesis by simp
  qed
qed

lemma nth_el_appendr[simp]: "length xs \<le> i \<Longrightarrow> (xs @ ys)\<langle>i\<rangle>\<^sub>l = ys\<langle>i - length xs\<rangle>\<^sub>l"
proof (induct xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case 
  proof (cases i)
    case 0
    with Cons show ?thesis
      by fastforce
  next
    case (Suc nat)
    with Cons show ?thesis by simp
  qed
qed

subsection \<open> Extra List Theorems \<close>

subsubsection \<open> Map \<close>

lemma map_nth_Cons_atLeastLessThan:
  "map (nth (x # xs)) [Suc m..<n] = map (nth xs) [m..<n - 1]"
proof -
  have "nth xs = nth (x # xs) \<circ> Suc"
    by auto
  hence "map (nth xs) [m..<n - 1] = map (nth (x # xs) \<circ> Suc) [m..<n - 1]"
    by simp
  also have "... = map (nth (x # xs)) (map Suc [m..<n - 1])"
    by simp
  also have "... = map (nth (x # xs)) [Suc m..<n]"
    by (metis Suc_diff_1 le_0_eq length_upt list.simps(8) list.size(3) map_Suc_upt not_less upt_0)
  finally show ?thesis ..
qed

subsubsection \<open> Sorted Lists \<close>

lemma sorted_last [simp]: "\<lbrakk> x \<in> set xs; sorted xs \<rbrakk> \<Longrightarrow> x \<le> last xs"
  by (induct xs, auto)

lemma sorted_prefix:
  assumes "xs \<le> ys" "sorted ys"
  shows "sorted xs"
proof -
  obtain zs where "ys = xs @ zs"
    using Prefix_Order.prefixE assms(1) by auto
  thus ?thesis
    using assms(2) sorted_append by blast
qed

lemma sorted_map: "\<lbrakk> sorted xs; mono f \<rbrakk> \<Longrightarrow> sorted (map f xs)"
  by (simp add: monoD sorted_iff_nth_mono)

lemma sorted_distinct [intro]: "\<lbrakk> sorted (xs); distinct(xs) \<rbrakk> \<Longrightarrow> (\<forall> i<length xs - 1. xs!i < xs!(i + 1))"
  apply (induct xs)
   apply (simp_all)
  apply (metis (no_types, opaque_lifting) Suc_leI Suc_less_eq Suc_pred gr0_conv_Suc not_le not_less_iff_gr_or_eq nth_Cons_Suc nth_mem nth_non_equal_first_eq)
  done

text \<open> The concatenation of two lists is sorted provided (1) both the lists are sorted, and (2) 
  the final and first elements are ordered. \<close>

lemma sorted_append_middle:
  "sorted(xs@ys) = (sorted xs \<and> sorted ys \<and> (xs \<noteq> [] \<and> ys \<noteq> [] \<longrightarrow> xs!(length xs - 1) \<le> ys!0))"
proof -
  have "\<And>x y. \<lbrakk> sorted xs; sorted ys; xs ! (length xs - Suc 0) \<le> ys ! 0 \<rbrakk> \<Longrightarrow> x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> x \<le> y"
  proof -
    fix x y
    assume "sorted xs" "sorted ys" "xs ! (length xs - Suc 0) \<le> ys ! 0" "x \<in> set xs" "y \<in> set ys"
    moreover then obtain i j where i: "x = xs!i" "i < length xs" and j: "y = ys!j" "j < length ys"
      by (auto simp add: in_set_conv_nth)
    moreover have "xs ! i \<le> xs!(length xs - 1)"
      by (metis One_nat_def Suc_diff_Suc Suc_leI Suc_le_mono \<open>i < length xs\<close> \<open>sorted xs\<close> diff_less diff_zero gr_implies_not_zero nat.simps(3) sorted_iff_nth_mono zero_less_iff_neq_zero)
    moreover have "ys!0 \<le> ys ! j"
      by (simp add: calculation(2) calculation(9) sorted_nth_mono)
    ultimately have "xs ! i \<le> ys ! j"
      by (metis One_nat_def dual_order.trans) 
    thus "x \<le> y"
      by (simp add: i j)
  qed
  thus ?thesis
    by (auto simp add: sorted_append)
qed

text \<open> Is the given list a permutation of the given set? \<close>

definition is_sorted_list_of_set :: "('a::ord) set \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_sorted_list_of_set A xs = ((\<forall> i<length(xs) - 1. xs!i < xs!(i + 1)) \<and> set(xs) = A)"

lemma sorted_is_sorted_list_of_set:
  assumes "is_sorted_list_of_set A xs"
  shows "sorted(xs)" and "distinct(xs)"
using assms proof (induct xs arbitrary: A)
  show "sorted []"
    by auto
next
  show "distinct []"
    by auto
next
  fix A :: "'a set"
  case (Cons x xs) note hyps = this
  assume isl: "is_sorted_list_of_set A (x # xs)"
  hence srt: "(\<forall>i<length xs - Suc 0. xs ! i < xs ! Suc i)"
    using less_diff_conv by (auto simp add: is_sorted_list_of_set_def)
  with hyps(1) have srtd: "sorted xs"
    by (simp add: is_sorted_list_of_set_def)
  with isl show "sorted (x # xs)"
    apply (simp_all add: is_sorted_list_of_set_def)
    apply (metis (mono_tags, lifting) all_nth_imp_all_set less_le_trans linorder_not_less not_less_iff_gr_or_eq nth_Cons_0 sorted_iff_nth_mono zero_order(3))
    done
  from srt hyps(2) have "distinct xs"
    by (simp add: is_sorted_list_of_set_def)
  with isl show "distinct (x # xs)"
  proof -
    have "(\<forall>n. \<not> n < length (x # xs) - 1 \<or> (x # xs) ! n < (x # xs) ! (n + 1)) \<and> set (x # xs) = A"
      by (meson \<open>is_sorted_list_of_set A (x # xs)\<close> is_sorted_list_of_set_def)
  then show ?thesis
    by (metis \<open>distinct xs\<close> add.commute add_diff_cancel_left' distinct.simps(2) leD length_Cons length_greater_0_conv length_pos_if_in_set less_le nth_Cons_0 nth_Cons_Suc plus_1_eq_Suc set_ConsD sorted_wrt.elims(2) srtd)    
  qed
qed

lemma is_sorted_list_of_set_alt_def:
  "is_sorted_list_of_set A xs \<longleftrightarrow> sorted (xs) \<and> distinct (xs) \<and> set(xs) = A"
  by (metis is_sorted_list_of_set_def sorted_distinct sorted_is_sorted_list_of_set(1,2))

definition sorted_list_of_set_alt :: "('a::ord) set \<Rightarrow> 'a list" where
"sorted_list_of_set_alt A =
  (if (A = {}) then [] else (THE xs. is_sorted_list_of_set A xs))"

lemma is_sorted_list_of_set:
  "finite A \<Longrightarrow> is_sorted_list_of_set A (sorted_list_of_set A)"
  using sorted_distinct sorted_list_of_set(2) by (fastforce simp add: is_sorted_list_of_set_def)

lemma sorted_list_of_set_other_def:
  "finite A \<Longrightarrow> sorted_list_of_set(A) = (THE xs. sorted(xs) \<and> distinct(xs) \<and> set xs = A)"
  by (metis (mono_tags, lifting) sorted_list_of_set.distinct_sorted_key_list_of_set
      sorted_list_of_set.idem_if_sorted_distinct sorted_list_of_set.set_sorted_key_list_of_set
      sorted_list_of_set.sorted_sorted_key_list_of_set the_equality)

lemma sorted_list_of_set_alt [simp]:
  "finite A \<Longrightarrow> sorted_list_of_set_alt(A) = sorted_list_of_set(A)"
  by (metis is_sorted_list_of_set is_sorted_list_of_set_def sorted_is_sorted_list_of_set(1,2)
      sorted_list_of_set.idem_if_sorted_distinct sorted_list_of_set_alt_def sorted_list_of_set_eq_Nil_iff
      the_equality)

text \<open> Sorting lists according to a relation \<close>

definition is_sorted_list_of_set_by :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_sorted_list_of_set_by R A xs = ((\<forall> i<length(xs) - 1. (xs!i, xs!(i + 1)) \<in> R) \<and> set(xs) = A)"

definition sorted_list_of_set_by :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a list" where
"sorted_list_of_set_by R A = (THE xs. is_sorted_list_of_set_by R A xs)"

definition fin_set_lexord :: "'a rel \<Rightarrow> 'a set rel" where
"fin_set_lexord R = {(A, B). finite A \<and> finite B \<and>
                             (\<exists> xs ys. is_sorted_list_of_set_by R A xs \<and> is_sorted_list_of_set_by R B ys
                              \<and> (xs, ys) \<in> lexord R)}"

lemma is_sorted_list_of_set_by_mono:
  "\<lbrakk> R \<subseteq> S; is_sorted_list_of_set_by R A xs \<rbrakk> \<Longrightarrow> is_sorted_list_of_set_by S A xs"
  by (auto simp add: is_sorted_list_of_set_by_def)

lemma lexord_mono':
  "\<lbrakk> (\<And> x y. f x y \<longrightarrow> g x y); (xs, ys) \<in> lexord {(x, y). f x y} \<rbrakk> \<Longrightarrow> (xs, ys) \<in> lexord {(x, y). g x y}"
  by (metis case_prodD case_prodI lexord_take_index_conv mem_Collect_eq)

lemma fin_set_lexord_mono [mono]:
  "(\<And> x y. f x y \<longrightarrow> g x y) \<Longrightarrow> (xs, ys) \<in> fin_set_lexord {(x, y). f x y} \<longrightarrow> (xs, ys) \<in> fin_set_lexord {(x, y). g x y}"
proof
  assume
    fin: "(xs, ys) \<in> fin_set_lexord {(x, y). f x y}" and
    hyp: "(\<And> x y. f x y \<longrightarrow> g x y)"

  from fin have "finite xs" "finite ys"
    using fin_set_lexord_def by fastforce+

  with fin hyp show "(xs, ys) \<in> fin_set_lexord {(x, y). g x y}"
    by (simp add: fin_set_lexord_def, metis case_prod_conv is_sorted_list_of_set_by_def lexord_mono' mem_Collect_eq)

qed

definition distincts :: "'a set \<Rightarrow> 'a list set" where
"distincts A = {xs \<in> lists A. distinct(xs)}"

lemma tl_element:
  "\<lbrakk> x \<in> set xs; x \<noteq> hd(xs) \<rbrakk> \<Longrightarrow> x \<in> set(tl(xs))"
  by (metis in_set_insert insert_Nil list.collapse list.distinct(2) set_ConsD)

subsubsection \<open> List Update \<close>

lemma listsum_update:
  fixes xs :: "'a::ring list"
  assumes "i < length xs"
  shows "list_sum (xs[i := v]) = list_sum xs - xs ! i + v"
using assms proof (induct xs arbitrary: i)
  case Nil
  then show ?case by (simp)
next
  case (Cons a xs)
  then show ?case
  proof (cases i)
    case 0
    thus ?thesis
      by (simp add: add.commute) 
  next
    case (Suc i')
    with Cons show ?thesis
      by (auto)
  qed
qed

subsubsection \<open> Drop While and Take While \<close>

lemma dropWhile_sorted_le_above:
  "\<lbrakk> sorted xs; x \<in> set (dropWhile (\<lambda> x. x \<le> n) xs) \<rbrakk> \<Longrightarrow> x > n"
proof (induct xs)
  case Nil
  then show ?case
    by simp 
next
  case (Cons a xs)
  then show ?case
  proof (cases "a \<le> n")
    case True
    with Cons show ?thesis by simp
  next
    case False
    with Cons show ?thesis
      by force 
  qed
qed

lemma set_dropWhile_le:
  "sorted xs \<Longrightarrow> set (dropWhile (\<lambda> x. x \<le> n) xs) = {x\<in>set xs. x > n}"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  hence "sorted xs"
    using sorted_simps(2) by blast
  with Cons show ?case 
    by force
qed

lemma set_takeWhile_less_sorted:
  "\<lbrakk> sorted I; x \<in> set I; x < n \<rbrakk> \<Longrightarrow> x \<in> set (takeWhile (\<lambda>x. x < n) I)"
proof (induct I arbitrary: x)
  case Nil thus ?case
    by (simp)
next
  case (Cons a I) thus ?case
    by auto
qed

lemma nth_le_takeWhile_ord: "\<lbrakk> sorted xs; i \<ge> length (takeWhile (\<lambda> x. x \<le> n) xs); i < length xs \<rbrakk> \<Longrightarrow> n \<le> xs ! i"
proof (induct xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (meson dual_order.trans nle_le nth_length_takeWhile order_le_less_trans sorted_iff_nth_mono) 
qed

lemma length_takeWhile_less:
  "\<lbrakk> a \<in> set xs; \<not> P a \<rbrakk> \<Longrightarrow> length (takeWhile P xs) < length xs"
  by (metis in_set_conv_nth length_takeWhile_le nat_neq_iff not_less set_takeWhileD takeWhile_nth)

lemma nth_length_takeWhile_less:
  "\<lbrakk> sorted xs; distinct xs; (\<exists> a \<in> set xs. a \<ge> n) \<rbrakk> \<Longrightarrow> xs ! length (takeWhile (\<lambda>x. x < n) xs) \<ge> n"
  by (induct xs, auto)

subsubsection \<open> Last and But Last \<close>

lemma length_gt_zero_butlast_concat:
  assumes "length ys > 0"
  shows "butlast (xs @ ys) = xs @ (butlast ys)"
  using assms by (metis butlast_append length_greater_0_conv)

lemma length_eq_zero_butlast_concat:
  assumes "length ys = 0"
  shows "butlast (xs @ ys) = butlast xs"
  using assms by (metis append_Nil2 length_0_conv)

lemma butlast_single_element:
  shows "butlast [e] = []"
  by (metis butlast.simps(2))

lemma last_single_element:
  shows "last [e] = e"
  by (metis last.simps)

lemma length_zero_last_concat:
  assumes "length t = 0"
  shows "last (s @ t) = last s"
  by (metis append_Nil2 assms length_0_conv)

lemma length_gt_zero_last_concat:
  assumes "length t > 0"
  shows "last (s @ t) = last t"
  by (metis assms last_append length_greater_0_conv)

subsubsection \<open> Prefixes and Strict Prefixes \<close>

lemma prefix_length_eq:
  "\<lbrakk> length xs = length ys; prefix xs ys \<rbrakk> \<Longrightarrow> xs = ys"
  by (metis not_equal_is_parallel parallel_def)

lemma prefix_Cons_elim [elim]:
  assumes "prefix (x # xs) ys"
  obtains ys' where "ys = x # ys'" "prefix xs ys'"
  using assms
  by (metis append_Cons prefix_def)

lemma prefix_map_inj:
  "\<lbrakk> inj_on f (set xs \<union> set ys); prefix (map f xs) (map f ys) \<rbrakk> \<Longrightarrow>
   prefix xs ys"
proof (induct xs arbitrary:ys)
  case Nil
  then show ?case
    by simp 
next
  case (Cons x xs)
  obtain ys' where "map f ys = f x # ys'" "prefix (map f xs) ys'"
    using Cons.prems(2) by auto 
  with Cons show ?case
    by (simp, safe, metis Diff_iff Sublist.Cons_prefix_Cons Un_insert_right empty_iff image_eqI inj_on_insert insert_iff list.simps(15))
qed

lemma prefix_map_inj_eq [simp]:
  "inj_on f (set xs \<union> set ys) \<Longrightarrow>
   prefix (map f xs) (map f ys) \<longleftrightarrow> prefix xs ys"
  using map_mono_prefix prefix_map_inj by blast

lemma strict_prefix_Cons_elim [elim]:
  assumes "strict_prefix (x # xs) ys"
  obtains ys' where "ys = x # ys'" "strict_prefix xs ys'"
  using assms
  by (metis Sublist.strict_prefixE' Sublist.strict_prefixI' append_Cons)

lemma strict_prefix_map_inj:
  "\<lbrakk> inj_on f (set xs \<union> set ys); strict_prefix (map f xs) (map f ys) \<rbrakk> \<Longrightarrow>
   strict_prefix xs ys"
  apply (induct xs arbitrary:ys)
   apply (simp_all)
  using prefix_bot.not_eq_extremum apply fastforce
  apply (erule strict_prefix_Cons_elim)
  apply (safe)
  apply (metis Diff_iff Sublist.strict_prefix_simps(3) Un_insert_right empty_iff imageI inj_on_insert insert_iff
      list.simps(15))
  done

lemma strict_prefix_map_inj_eq [simp]:
  "inj_on f (set xs \<union> set ys) \<Longrightarrow>
   strict_prefix (map f xs) (map f ys) \<longleftrightarrow> strict_prefix xs ys"
  by (simp add: inj_on_map_eq_map strict_prefix_def)

lemma prefix_drop:
  "\<lbrakk> drop (length xs) ys = zs; prefix xs ys \<rbrakk>
   \<Longrightarrow> ys = xs @ zs"
  by (metis append_eq_conv_conj prefix_def)

lemma list_append_prefixD [dest]: "x @ y \<le> z \<Longrightarrow> x \<le> z"
  using append_prefixD less_eq_list_def by blast

lemma prefix_not_empty:
  assumes "strict_prefix xs ys" and "xs \<noteq> []"
  shows "ys \<noteq> []"
  using Sublist.strict_prefix_simps(1) assms(1) by blast

lemma prefix_not_empty_length_gt_zero:
  assumes "strict_prefix xs ys" and "xs \<noteq> []"
  shows "length ys > 0"
  using assms prefix_not_empty by auto

lemma butlast_prefix_suffix_not_empty:
  assumes "strict_prefix (butlast xs) ys"
  shows "ys \<noteq> []"
  using assms prefix_not_empty_length_gt_zero by fastforce

lemma prefix_and_concat_prefix_is_concat_prefix:
  assumes "prefix s t" "prefix (e @ t) u"
  shows "prefix (e @ s) u"
  using Sublist.same_prefix_prefix assms(1) assms(2) prefix_order.dual_order.trans by blast

lemma prefix_eq_exists:
  "prefix s t \<longleftrightarrow> (\<exists>xs . s @ xs = t)"
  using prefix_def by auto

lemma strict_prefix_eq_exists:
  "strict_prefix s t \<longleftrightarrow> (\<exists>xs . s @ xs = t \<and> (length xs) > 0)"
  using prefix_def strict_prefix_def by auto

lemma butlast_strict_prefix_eq_butlast:
  assumes "length s = length t" and "strict_prefix (butlast s) t"
  shows "strict_prefix (butlast s) t \<longleftrightarrow> (butlast s) = (butlast t)"
  by (metis append_butlast_last_id append_eq_append_conv assms(1) assms(2) length_0_conv length_butlast strict_prefix_eq_exists)

lemma butlast_eq_if_eq_length_and_prefix:
  assumes "length s > 0" "length z > 0"
          "length s = length z" "strict_prefix (butlast s) t" "strict_prefix (butlast z) t"
  shows   "(butlast s) = (butlast z)"
  using assms by (auto simp add:strict_prefix_eq_exists)

lemma prefix_imp_length_lteq:
  assumes "prefix s t"
  shows "length s \<le> length t"
  using assms by (simp add: Sublist.prefix_length_le)

lemma prefix_imp_length_not_gt:
  assumes "prefix s t"
  shows "\<not> length t < length s"
  using assms by (simp add: Sublist.prefix_length_le leD)

lemma prefix_and_eq_length_imp_eq_list:
  assumes "prefix s t" and "length t = length s"
  shows "s=t"
  using assms by (simp add: prefix_length_eq)

lemma butlast_prefix_imp_length_not_gt:
  assumes "length s > 0" "strict_prefix (butlast s) t"
  shows "\<not> (length t < length s)"
  using assms prefix_length_less by fastforce

lemma length_not_gt_iff_eq_length:
  assumes "length s > 0" and "strict_prefix (butlast s) t"
  shows "(\<not> (length s < length t)) = (length s = length t)"
proof -
  have "(\<not> (length s < length t)) = ((length t < length s) \<or> (length s = length t))"
      by (metis not_less_iff_gr_or_eq)
  also have "... = (length s = length t)"
      using assms
      by (simp add:butlast_prefix_imp_length_not_gt)

  finally show ?thesis .
qed

lemma list_prefix_iff:
  "(prefix xs ys \<longleftrightarrow> (length xs \<le> length ys \<and> (\<forall> i<length xs. xs!i = ys!i)))"
  apply (safe)
    apply (simp add: prefix_imp_length_lteq)
   apply (metis nth_append prefix_def)
  apply (metis nth_take_lemma order_refl take_all take_is_prefix)
  done

lemma list_le_prefix_iff:
  "(xs \<le> ys \<longleftrightarrow> (length xs \<le> length ys \<and> (\<forall> i<length xs. xs!i = ys!i)))"
  by (simp add: less_eq_list_def list_prefix_iff)

text \<open> Greatest common prefix \<close>

fun gcp :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"gcp [] ys = []" |
"gcp (x # xs) (y # ys) = (if (x = y) then x # gcp xs ys else [])" |
"gcp _ _ = []"

lemma gcp_right [simp]: "gcp xs [] = []"
  by (induct xs, auto)

lemma gcp_append [simp]: "gcp (xs @ ys) (xs @ zs) = xs @ gcp ys zs"
  by (induct xs, auto)

lemma gcp_lb1: "prefix (gcp xs ys) xs"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof (cases ys)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a list)
    then show ?thesis
      by (simp add: Cons.hyps)
  qed
qed

lemma gcp_lb2: "prefix (gcp xs ys) ys"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof (cases ys)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a list)
    then show ?thesis
      by (simp add: Cons.hyps)
  qed
qed

interpretation prefix_semilattice: semilattice_inf gcp prefix strict_prefix
proof
  fix xs ys :: "'a list"
  show "prefix (gcp xs ys) xs"
  proof (induct xs arbitrary: ys)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by (simp add: gcp_lb1) 
  qed
  show "prefix (gcp xs ys) ys"
  proof (induct xs arbitrary: ys)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by (simp add: gcp_lb2) 
  qed
next
  fix xs ys zs :: "'a list"
  assume "prefix xs ys" "prefix xs zs"
  thus "prefix xs (gcp ys zs)"
    by (simp add: prefix_def, auto)
qed

subsubsection \<open> Lexicographic Order \<close>

lemma lexord_append:
  assumes "(xs\<^sub>1 @ ys\<^sub>1, xs\<^sub>2 @ ys\<^sub>2) \<in> lexord R" "length(xs\<^sub>1) = length(xs\<^sub>2)"
  shows "(xs\<^sub>1, xs\<^sub>2) \<in> lexord R \<or> (xs\<^sub>1 = xs\<^sub>2 \<and> (ys\<^sub>1, ys\<^sub>2) \<in> lexord R)"
using assms
proof (induct xs\<^sub>2 arbitrary: xs\<^sub>1)
  case (Cons x\<^sub>2 xs\<^sub>2') note hyps = this
  from hyps(3) obtain x\<^sub>1 xs\<^sub>1' where xs\<^sub>1: "xs\<^sub>1 = x\<^sub>1 # xs\<^sub>1'" "length(xs\<^sub>1') = length(xs\<^sub>2')"
    by (simp, metis Suc_length_conv)
  with hyps(2) have xcases: "(x\<^sub>1, x\<^sub>2) \<in> R \<or> (xs\<^sub>1' @ ys\<^sub>1, xs\<^sub>2' @ ys\<^sub>2) \<in> lexord R"
    by (auto)
  show ?case
  proof (cases "(x\<^sub>1, x\<^sub>2) \<in> R")
    case True with xs\<^sub>1 show ?thesis
      by (auto)
  next
    case False
    with xcases have "(xs\<^sub>1' @ ys\<^sub>1, xs\<^sub>2' @ ys\<^sub>2) \<in> lexord R"
      by (auto)
    with hyps(1) xs\<^sub>1 have dichot: "(xs\<^sub>1', xs\<^sub>2') \<in> lexord R \<or> (xs\<^sub>1' = xs\<^sub>2' \<and> (ys\<^sub>1, ys\<^sub>2) \<in> lexord R)"
      by (auto)
    have "x\<^sub>1 = x\<^sub>2"
      using False hyps(2) xs\<^sub>1(1) by auto
    with dichot xs\<^sub>1 show ?thesis
      by (simp)
  qed
next
  case Nil thus ?case
    by auto
qed

lemma strict_prefix_lexord_rel:
  "strict_prefix xs ys \<Longrightarrow> (xs, ys) \<in> lexord R"
  by (metis Sublist.strict_prefixE' lexord_append_rightI)

lemma strict_prefix_lexord_left:
  assumes "trans R" "(xs, ys) \<in> lexord R" "strict_prefix xs' xs"
  shows "(xs', ys) \<in> lexord R"
  by (metis assms lexord_trans strict_prefix_lexord_rel)

lemma prefix_lexord_right:
  assumes "trans R" "(xs, ys) \<in> lexord R" "strict_prefix ys ys'"
  shows "(xs, ys') \<in> lexord R"
  by (metis assms lexord_trans strict_prefix_lexord_rel)

lemma lexord_eq_length:
  assumes "(xs, ys) \<in> lexord R" "length xs = length ys"
  shows "\<exists> i. (xs!i, ys!i) \<in> R \<and> i < length xs \<and> (\<forall> j<i. xs!j = ys!j)"
using assms proof (induct xs arbitrary: ys)
  case (Cons x xs) note hyps = this
  then obtain y ys' where ys: "ys = y # ys'" "length ys' = length xs"
    by (metis Suc_length_conv)
  show ?case
  proof (cases "(x, y) \<in> R")
    case True with ys show ?thesis
      by force
  next
    case False
    with ys hyps(2) have xy: "x = y" "(xs, ys') \<in> lexord R"
      by auto
    with hyps(1,3) ys obtain i where "(xs!i, ys'!i) \<in> R" "i < length xs" "(\<forall> j<i. xs!j = ys'!j)"
      by force
    with xy ys have "((x # xs) ! Suc i, ys ! Suc i) \<in> R \<and> Suc i < length (x # xs) \<and> (\<forall>j<Suc i. (x # xs) ! j = ys ! j) "
      by (auto simp add: less_Suc_eq_0_disj)
    thus ?thesis
      by blast 
  qed
next
  case Nil thus ?case by (auto)
qed

lemma lexord_intro_elems:
  assumes "length xs > i" "length ys > i" "(xs!i, ys!i) \<in> R" "\<forall> j<i. xs!j = ys!j"
  shows "(xs, ys) \<in> lexord R"
using assms proof (induct i arbitrary: xs ys)
  case 0 thus ?case
    by (simp, metis lexord_cons_cons list.exhaust nth_Cons_0)
next
  case (Suc i) note hyps = this
  then obtain x' y' xs' ys' where "xs = x' # xs'" "ys = y' # ys'"
    by (metis Suc_length_conv Suc_lessE)
  moreover with hyps(5) have "\<forall>j<i. xs' ! j = ys' ! j"
    by (auto)
  ultimately show ?case using hyps
    by (auto)
qed

subsection \<open> Distributed Concatenation \<close>

definition uncurry :: "('a \<Rightarrow> 'b \<Rightarrow>  'c) \<Rightarrow> ('a \<times> 'b \<Rightarrow> 'c)" where
[simp]: "uncurry f = (\<lambda>(x, y). f x y)"

definition dist_concat ::
  "'a list set \<Rightarrow> 'a list set \<Rightarrow> 'a list set" (infixr "\<^sup>\<frown>" 100) where
"dist_concat ls1 ls2 = (uncurry (@) ` (ls1 \<times> ls2))"

lemma dist_concat_left_empty [simp]:
  "{} \<^sup>\<frown> ys = {}"
  by (simp add: dist_concat_def)

lemma dist_concat_right_empty [simp]:
  "xs \<^sup>\<frown> {} = {}"
  by (simp add: dist_concat_def)

lemma dist_concat_insert [simp]:
"insert l ls1 \<^sup>\<frown> ls2 = ((@) l ` ( ls2)) \<union> (ls1 \<^sup>\<frown> ls2)"
  by (auto simp add: dist_concat_def)

subsection \<open> List Domain and Range \<close>

abbreviation seq_dom :: "'a list \<Rightarrow> nat set" ("dom\<^sub>l") where
"seq_dom xs \<equiv> {0..<length xs}"

abbreviation (input) seq_ran :: "'a list \<Rightarrow> 'a set" ("ran\<^sub>l") where
"seq_ran xs \<equiv> set xs"

subsection \<open> Extracting List Elements \<close>

definition seq_extract :: "nat set \<Rightarrow> 'a list \<Rightarrow> 'a list" (infix "\<upharpoonleft>\<^sub>l" 80) where
"seq_extract A xs = nths xs A"

lemma seq_extract_Nil [simp]: "A \<upharpoonleft>\<^sub>l [] = []"
  by (simp add: seq_extract_def)

lemma seq_extract_Cons:
  "A \<upharpoonleft>\<^sub>l (x # xs) = (if 0 \<in> A then [x] else []) @ {j. Suc j \<in> A} \<upharpoonleft>\<^sub>l xs"
  by (simp add: seq_extract_def nths_Cons)

lemma seq_extract_empty [simp]: "{} \<upharpoonleft>\<^sub>l xs = []"
  by (simp add: seq_extract_def)

lemma seq_extract_ident [simp]: "{0..<length xs} \<upharpoonleft>\<^sub>l xs = xs"
  unfolding list_eq_iff_nth_eq
  by (auto simp add: seq_extract_def length_nths atLeast0LessThan)

lemma seq_extract_split:
  assumes "i \<le> length xs"
  shows "{0..<i} \<upharpoonleft>\<^sub>l xs @ {i..<length xs} \<upharpoonleft>\<^sub>l xs = xs"
using assms
proof (induct xs arbitrary: i)
  case Nil thus ?case by (simp add: seq_extract_def)
next
  case (Cons x xs) note hyp = this
  have "{j. Suc j < i} = {0..<i - 1}"
    by (auto)
  moreover have "{j. i \<le> Suc j \<and> j < length xs} = {i - 1..<length xs}"
    by (auto)
  ultimately show ?case
    using hyp by (force simp add: seq_extract_def nths_Cons)
qed

lemma seq_extract_append:
  "A \<upharpoonleft>\<^sub>l (xs @ ys) = (A \<upharpoonleft>\<^sub>l xs) @ ({j. j + length xs \<in> A} \<upharpoonleft>\<^sub>l ys)"
  by (simp add: seq_extract_def nths_append)

lemma seq_extract_range: "A \<upharpoonleft>\<^sub>l xs = (A \<inter> dom\<^sub>l(xs)) \<upharpoonleft>\<^sub>l xs"
  apply (simp add: seq_extract_def nths_def)
  apply (metis (no_types, lifting) atLeastLessThan_iff filter_cong in_set_zip nth_mem set_upt)
done

lemma seq_extract_out_of_range:
  "A \<inter> dom\<^sub>l(xs) = {} \<Longrightarrow> A \<upharpoonleft>\<^sub>l xs = []"
  by (metis seq_extract_def seq_extract_range nths_empty)

lemma seq_extract_length [simp]:
  "length (A \<upharpoonleft>\<^sub>l xs) = card (A \<inter> dom\<^sub>l(xs))"
proof -
  have "{i. i < length(xs) \<and> i \<in> A} = (A \<inter> {0..<length(xs)})"
    by (auto)
  thus ?thesis
    by (simp add: seq_extract_def length_nths)
qed

lemma seq_extract_Cons_atLeastLessThan:
  assumes "m < n"
  shows "{m..<n} \<upharpoonleft>\<^sub>l (x # xs) = (if (m = 0) then x # ({0..<n-1} \<upharpoonleft>\<^sub>l xs) else {m-1..<n-1} \<upharpoonleft>\<^sub>l xs)"
proof -
  have "{j. Suc j < n} = {0..<n - Suc 0}"
    by (auto)
  moreover have "{j. m \<le> Suc j \<and> Suc j < n} = {m - Suc 0..<n - Suc 0}"
    by (auto)

  ultimately show ?thesis using assms
    by (auto simp add: seq_extract_Cons)
qed

lemma seq_extract_singleton:
  assumes "i < length xs"
  shows "{i} \<upharpoonleft>\<^sub>l xs = [xs ! i]"
  using assms
  apply (induct xs arbitrary: i)
   apply (simp_all add: seq_extract_Cons)
  apply safe
  apply (rename_tac xs i)
  apply (subgoal_tac "{j. Suc j = i} = {i - 1}")
   apply (auto)
  done

lemma seq_extract_as_map:
  assumes "m < n" "n \<le> length xs"
  shows "{m..<n} \<upharpoonleft>\<^sub>l xs = map (nth xs) [m..<n]"
using assms proof (induct xs arbitrary: m n)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have "[m..<n] = m # [m+1..<n]"
    using Cons.prems(1) upt_eq_Cons_conv by blast
  moreover have "map (nth (x # xs)) [Suc m..<n] = map (nth xs) [m..<n-1]"
    by (simp add: map_nth_Cons_atLeastLessThan)
  ultimately show ?case
    using Cons upt_rec
    by (auto simp add: seq_extract_Cons_atLeastLessThan)
qed

lemma seq_append_as_extract:
  "xs = ys @ zs \<longleftrightarrow> (\<exists> i\<le>length(xs). ys = {0..<i} \<upharpoonleft>\<^sub>l xs \<and> zs = {i..<length(xs)} \<upharpoonleft>\<^sub>l xs)"
proof
  assume xs: "xs = ys @ zs"
  moreover have "ys = {0..<length ys} \<upharpoonleft>\<^sub>l (ys @ zs)"
    by (simp add: seq_extract_append)
  moreover have "zs = {length ys..<length ys + length zs} \<upharpoonleft>\<^sub>l (ys @ zs)"
  proof -
    have "{length ys..<length ys + length zs} \<inter> {0..<length ys} = {}"
      by auto
    moreover have s1: "{j. j < length zs} = {0..<length zs}"
      by auto
    ultimately show ?thesis
      by (simp add: seq_extract_append seq_extract_out_of_range)
  qed
  ultimately show "(\<exists> i\<le>length(xs). ys = {0..<i} \<upharpoonleft>\<^sub>l xs \<and> zs = {i..<length(xs)} \<upharpoonleft>\<^sub>l xs)"
    using le_iff_add by auto
next
  assume "\<exists>i\<le>length xs. ys = {0..<i} \<upharpoonleft>\<^sub>l xs \<and> zs = {i..<length xs} \<upharpoonleft>\<^sub>l xs"
  thus "xs = ys @ zs"
    by (auto simp add: seq_extract_split)
qed

subsection \<open> Filtering a list according to a set \<close>

definition seq_filter :: "'a list \<Rightarrow> 'a set \<Rightarrow> 'a list" (infix "\<restriction>\<^sub>l" 80) where
"seq_filter xs A = filter (\<lambda> x. x \<in> A) xs"

lemma seq_filter_Cons_in [simp]: 
  "x \<in> cs \<Longrightarrow> (x # xs) \<restriction>\<^sub>l cs = x # (xs \<restriction>\<^sub>l cs)"
  by (simp add: seq_filter_def)

lemma seq_filter_Cons_out [simp]: 
  "x \<notin> cs \<Longrightarrow> (x # xs) \<restriction>\<^sub>l cs = (xs \<restriction>\<^sub>l cs)"
  by (simp add: seq_filter_def)

lemma seq_filter_Nil [simp]: "[] \<restriction>\<^sub>l A = []"
  by (simp add: seq_filter_def)

lemma seq_filter_empty [simp]: "xs \<restriction>\<^sub>l {} = []"
  by (simp add: seq_filter_def)

lemma seq_filter_append: "(xs @ ys) \<restriction>\<^sub>l A = (xs \<restriction>\<^sub>l A) @ (ys \<restriction>\<^sub>l A)"
  by (simp add: seq_filter_def)

lemma seq_filter_UNIV [simp]: "xs \<restriction>\<^sub>l UNIV = xs"
  by (simp add: seq_filter_def)

lemma seq_filter_twice [simp]: "(xs \<restriction>\<^sub>l A) \<restriction>\<^sub>l B = xs \<restriction>\<^sub>l (A \<inter> B)"
  by (simp add: seq_filter_def)

subsection \<open> Minus on lists \<close>

instantiation list :: (type) minus
begin

text \<open> We define list minus so that if the second list is not a prefix of the first, then an arbitrary
        list longer than the combined length is produced. Thus we can always determined from the output
        whether the minus is defined or not. \<close>

definition "xs - ys = (if (prefix ys xs) then drop (length ys) xs else [])"

instance ..
end

lemma minus_cancel [simp]: "xs - xs = []"
  by (simp add: minus_list_def)

lemma append_minus [simp]: "(xs @ ys) - xs = ys"
  by (simp add: minus_list_def)

lemma minus_right_nil [simp]: "xs - [] = xs"
  by (simp add: minus_list_def)

lemma list_concat_minus_list_concat: "(s @ t) - (s @ z) = t - z"
  by (simp add: minus_list_def)

lemma length_minus_list: "y \<le> x \<Longrightarrow> length(x - y) = length(x) - length(y)"
  by (simp add: less_eq_list_def minus_list_def)

lemma map_list_minus:
  "xs \<le> ys \<Longrightarrow> map f (ys - xs) = map f ys - map f xs"
  by (simp add: drop_map less_eq_list_def map_mono_prefix minus_list_def)

lemma list_minus_first_tl [simp]: 
  "[x] \<le> xs \<Longrightarrow> (xs - [x]) = tl xs"
  by (metis Prefix_Order.prefixE append.left_neutral append_minus list.sel(3) not_Cons_self2 tl_append2)

text \<open> Extra lemmas about @{term prefix} and @{term strict_prefix} \<close>

lemma prefix_concat_minus:
  assumes "prefix xs ys"
  shows "xs @ (ys - xs) = ys"
  using assms by (metis minus_list_def prefix_drop)

lemma prefix_minus_concat:
  assumes "prefix s t"
  shows "(t - s) @ z = (t @ z) - s"
  using assms by (simp add: Sublist.prefix_length_le minus_list_def)

lemma strict_prefix_minus_not_empty:
  assumes "strict_prefix xs ys"
  shows "ys - xs \<noteq> []"
  using assms by (metis append_Nil2 prefix_concat_minus strict_prefix_def)

lemma strict_prefix_diff_minus:
  assumes "prefix xs ys" and "xs \<noteq> ys"
  shows "(ys - xs) \<noteq> []"
  using assms by (simp add: strict_prefix_minus_not_empty)

lemma length_tl_list_minus_butlast_gt_zero:
  assumes "length s < length t" and "strict_prefix (butlast s) t" and "length s > 0"
  shows "length (tl (t - (butlast s))) > 0"
  using assms
  by (metis Nitpick.size_list_simp(2) butlast_snoc hd_Cons_tl length_butlast length_greater_0_conv length_tl less_trans nat_neq_iff strict_prefix_minus_not_empty prefix_order.dual_order.strict_implies_order prefix_concat_minus)

lemma list_minus_butlast_eq_butlast_list:
  assumes "length t = length s" and "strict_prefix (butlast s) t"
  shows "t - (butlast s) = [last t]"
  using assms
  by (metis append_butlast_last_id append_eq_append_conv butlast.simps(1) length_butlast less_numeral_extra(3) list.size(3) prefix_order.dual_order.strict_implies_order prefix_concat_minus prefix_length_less)

lemma butlast_strict_prefix_length_lt_imp_last_tl_minus_butlast_eq_last:
  assumes "length s > 0" "strict_prefix (butlast s) t" "length s < length t"
  shows "last (tl (t - (butlast s))) = (last t)"
  using assms by (metis last_append last_tl length_tl_list_minus_butlast_gt_zero less_numeral_extra(3) list.size(3) append_minus strict_prefix_eq_exists)

lemma tl_list_minus_butlast_not_empty:
  assumes "strict_prefix (butlast s) t" and "length s > 0" and "length t > length s"
  shows "tl (t - (butlast s)) \<noteq> []"
  using assms length_tl_list_minus_butlast_gt_zero by fastforce

lemma tl_list_minus_butlast_empty:
  assumes "strict_prefix (butlast s) t" and "length s > 0" and "length t = length s"
  shows "tl (t - (butlast s)) = []"
  using assms by (simp add: list_minus_butlast_eq_butlast_list)

lemma concat_minus_list_concat_butlast_eq_list_minus_butlast:
  assumes "prefix (butlast u) s"
  shows "(t @ s) - (t @ (butlast u)) = s - (butlast u)"
  using assms by (metis append_assoc prefix_concat_minus append_minus)

lemma tl_list_minus_butlast_eq_empty:
  assumes "strict_prefix (butlast s) t" and "length s = length t"
  shows "tl (t - (butlast s)) = []"
  using assms by (metis list.sel(3) list_minus_butlast_eq_butlast_list)

(* this can be shown using length_tl, but care is needed when list is empty? *)
lemma prefix_length_tl_minus:
  assumes "strict_prefix s t"
  shows "length (tl (t-s)) = (length (t-s)) - 1"
  by (auto)

lemma length_list_minus:
  assumes "strict_prefix s t"
  shows "length(t - s) = length(t) - length(s)"
  using assms by (simp add: minus_list_def prefix_order.dual_order.strict_implies_order)

lemma length_minus_le: "length (ys - xs) \<le> length ys"
  by (simp add: minus_list_def)

lemma length_minus_less: "\<lbrakk> xs \<le> ys; xs \<noteq> [] \<rbrakk> \<Longrightarrow> length (ys - xs) < length ys"
  by (simp add: minus_list_def less_eq_list_def)
     (metis diff_less length_greater_0_conv prefix_bot.extremum_uniqueI)

lemma filter_minus [simp]: "ys \<le> xs \<Longrightarrow> filter P (xs - ys) = filter P xs - filter P ys"
  by (simp add: minus_list_def less_eq_list_def filter_mono_prefix)
     (metis filter_append filter_mono_prefix prefix_drop same_append_eq)

subsection \<open> Laws on @{term list_update} \<close>

lemma list_update_0: "length(xs) > 0 \<Longrightarrow> xs[0 := x] = x # tl xs"
  by (metis length_0_conv list.collapse list_update_code(2) nat_less_le)

lemma tl_list_update: "\<lbrakk> length xs > 0; k > 0 \<rbrakk> \<Longrightarrow> tl(xs[k := v]) = (tl xs)[k-1 := v]"
  by (metis One_nat_def Suc_pred length_greater_0_conv list.collapse list.sel(3) list_update_code(3))

subsection \<open> Laws on @{term take}, @{term drop}, and @{term nths} \<close>

lemma take_prefix: "m \<le> n \<Longrightarrow> take m xs \<le> take n xs"
  by (metis Prefix_Order.prefixI append_take_drop_id min_absorb2 take_append take_take)

lemma nths_atLeastAtMost_0_take: "nths xs {0..m} = take (Suc m) xs"
  by (metis atLeast0AtMost lessThan_Suc_atMost nths_upt_eq_take)

lemma nths_atLeastLessThan_0_take: "nths xs {0..<m} = take m xs"
  by (simp add: atLeast0LessThan)

lemma nths_atLeastAtMost_prefix: "m \<le> n \<Longrightarrow> nths xs {0..m} \<le> nths xs {0..n}"
  by (simp add: nths_atLeastAtMost_0_take take_prefix)

lemma sorted_nths_atLeastAtMost_0: "\<lbrakk> m \<le> n; sorted (nths xs {0..n}) \<rbrakk> \<Longrightarrow> sorted (nths xs {0..m})"
  using nths_atLeastAtMost_prefix sorted_prefix by blast

lemma sorted_nths_atLeastLessThan_0: "\<lbrakk> m \<le> n; sorted (nths xs {0..<n}) \<rbrakk> \<Longrightarrow> sorted (nths xs {0..<m})"
  by (metis atLeast0LessThan nths_upt_eq_take sorted_prefix take_prefix)

lemma list_augment_as_update: 
  "k < length xs \<Longrightarrow> list_augment xs k x = list_update xs k x"
  by (metis list_augment_def list_augment_idem list_update_overwrite)

lemma nths_list_update_out: "k \<notin> A \<Longrightarrow> nths (list_update xs k x) A = nths xs A"
proof (induct xs arbitrary: k x A)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases k, auto simp add: nths_Cons)
qed

lemma nths_list_augment_out: "\<lbrakk> k < length xs; k \<notin> A \<rbrakk> \<Longrightarrow> nths (list_augment xs k x) A = nths xs A"
  by (simp add: list_augment_as_update nths_list_update_out)

lemma nths_none: 
  assumes "\<forall>i \<in> I. i \<ge> length xs"
  shows "nths xs I = []"
proof -
  from assms have "\<forall>x\<in>set (zip xs [0..<length xs]). snd x \<notin> I"
    by (metis atLeastLessThan_iff in_set_zip leD nth_mem set_upt)
  thus ?thesis
    by (simp add: nths_def)
qed

lemma nths_uptoLessThan:
  "\<lbrakk> m \<le> n; n < length xs \<rbrakk> \<Longrightarrow> nths xs {m..n} = xs ! m # nths xs {Suc m..n}"
proof (induct xs arbitrary: m n)
case Nil
  then show ?case by (simp)
next
  case (Cons a xs)
  have l1: "\<And> m n. \<lbrakk> 0 < m; m \<le> n \<rbrakk> \<Longrightarrow> {j. m \<le> Suc j \<and> Suc j \<le> n} = {m-1..n-1}"
    by (auto)
  have l2: "\<And> m n. \<lbrakk> 0 < m; m \<le> n \<rbrakk> \<Longrightarrow> {j. m \<le> j \<and> Suc j \<le> n} = {m..n-1}"
    by (auto)
  from Cons show ?case by (auto simp add: nths_Cons l1 l2)
qed

lemma nths_upt_nth: "\<lbrakk> j < i; i < length xs \<rbrakk> \<Longrightarrow> (nths xs {0..<i}) ! j = xs ! j"
  by (metis lessThan_atLeast0 nth_take nths_upt_eq_take)


lemma nths_upt_length: "\<lbrakk> m \<le> n; n \<le> length xs \<rbrakk> \<Longrightarrow> length (nths xs {m..<n}) = n-m"
  by (metis atLeastLessThan_empty diff_is_0_eq length_map length_upt list.size(3) not_less nths_empty seq_extract_as_map seq_extract_def)

lemma nths_upt_le_length: 
  "\<lbrakk> m \<le> n; Suc n \<le> length xs \<rbrakk> \<Longrightarrow> length (nths xs {m..n}) = Suc n - m"
  by (metis atLeastLessThanSuc_atLeastAtMost le_SucI nths_upt_length)

lemma sl1: "n > 0 \<Longrightarrow> {j. Suc j \<le> n} = {0..n-1}"
  by (auto)

lemma sl2: "\<lbrakk> 0 < m; m \<le> n \<rbrakk> \<Longrightarrow> {j. m \<le> Suc j \<and> Suc j \<le> n} = {m-1..n-1}"
  by auto

lemma nths_upt_le_nth: "\<lbrakk> m \<le> n; Suc n \<le> length xs; i < Suc n - m \<rbrakk> 
  \<Longrightarrow> (nths xs {m..n}) ! i = xs ! (i + m)"
proof (induct xs arbitrary: m n i)
  case Nil
  then show ?case by (simp)
next
  case (Cons a xs)
  then show ?case   
  proof (cases "i = 0")
    case True
    with Cons show ?thesis by (auto simp add: nths_Cons sl2)
  next
    case False
    with Cons show ?thesis by (auto simp add: nths_Cons sl1 sl2)
  qed
qed    

lemma nths_split_union:
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> x < y"
  shows "nths l A @ nths l B = nths l (A \<union> B)"
proof (induct l rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  { assume *: "length xs \<notin> (A \<union> B)"
    then have L: "nths (xs @ [x]) (A \<union> B) = nths xs (A \<union> B)"
      by (simp add: nths_append)
    from * have R: "nths (xs @ [x]) A = nths xs A" "nths (xs @ [x]) B = nths xs B"
      by (simp add: nths_append)+
    have ?case
      using L R snoc by presburger
  } note length_notin = this

  { assume *: "length xs \<in> (A \<union> B)"
    then have new_nths: "nths (xs @ [x]) (A \<union> B) = nths xs (A \<union> B) @ [x]"
      by (simp add: nths_append)
    from * consider (A) "length xs \<in> A" | (B) "length xs \<in> B"
      using assms by auto
    then have ?case
    proof cases
      case A
      then have "i \<in> B \<Longrightarrow> i > length xs" for i
        using assms by force
      then have nths_B: "nths (xs @ [x]) B = []"
        by (metis Suc_less_eq le_simps(2) length_Cons length_rotate1 nths_none rotate1.simps(2))
      from A have "nths (xs @ [x]) A = nths xs A @ [x]"
        by (simp add: nths_append)
      then have "nths (xs @ [x]) A @ nths (xs @ [x]) B = (nths xs A @ nths xs B) @ [x]"
        by (metis append_is_Nil_conv nths_B nths_append self_append_conv)
      then show ?thesis
        using snoc new_nths by presburger
    next
      case B
      then have "length xs \<notin> A"
        using assms by blast
      then have "nths (xs @ [x]) A = nths xs A"
        by (simp add: nths_append)
      moreover have "nths (xs @ [x]) B = nths xs B @ [x]"
        by (simp add: B nths_append)
      ultimately show ?thesis
        by (simp add: new_nths snoc)
    qed
  } note length_in=this
   
  show ?case
    using length_in length_notin by blast
qed

corollary nths_upt_le_append_split:
  "j \<le> i \<Longrightarrow> nths xs {0..<j} @ nths xs {j..i} = nths xs {0..i}"
proof -
  assume "j \<le> i"
  have "\<And>x y. x \<in> {0..<j} \<Longrightarrow> y \<in> {j..i} \<Longrightarrow> x < y"
    by auto
  then have "nths xs {0..<j} @ nths xs {j..i} = nths xs ({0..<j} \<union> {j..i})"
    by (rule nths_split_union)
  moreover have "{0..<j} \<union> {j..i} = {0..i}"
    by (simp add: ivl_disj_un_two(7) \<open>j \<le> i\<close>)
  ultimately show ?thesis
    using \<open>j \<le> i\<close> by presburger
qed

lemma nths_Cons_atLeastAtMost: "n > m \<Longrightarrow> nths (x # xs) {m..n} = (if m = 0 then x # nths xs {0..n-1} else nths xs {m-1..n-1})"
  apply (simp add: nths_Cons)
  apply safe
  using One_nat_def sl1 apply presburger
  using One_nat_def le_eq_less_or_eq sl2 apply presburger
  done

lemma nths_atLeastAtMost_eq_drop_take: "nths xs {m..n} = drop m (take (n+1) xs)"
  by (induct xs rule: rev_induct, simp_all split: nat_diff_split add: nths_append, linarith)

lemma drop_as_map: "drop m xs = map (nth xs) [m..<length xs]"
  by (metis add.commute add.right_neutral drop_map drop_upt map_nth)

lemma take_as_map: "take m xs = map (nth xs) [0..<min m (length xs)]"
  by (metis (no_types, lifting) add_0 map_nth min.cobounded2 min.commute min_def take_all_iff take_map take_upt)

lemma nths_atLeastAtMost_as_map: "nths xs {m..n} = map (\<lambda> i. xs ! i) [m..<min (n+1) (length xs)]"
  by (simp add: nths_atLeastAtMost_eq_drop_take drop_as_map take_as_map)

lemma nths_single: "nths xs {k} = (if k < length xs then [xs ! k] else [])"
  using nths_atLeastAtMost_as_map[of xs k k] by simp 

lemma nths_list_update_in_range: "k \<in> {m..n} \<Longrightarrow> nths (list_update xs k x) {m..n} = list_update (nths xs {m..n}) (k - m) x"
proof (induct xs arbitrary: k x m n)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
  proof (cases k)
    case 0
    then show ?thesis apply (simp)
      by (smt (verit, best) Cons.prems append_Cons list_update_code(2) nths_Cons)
  next
    case (Suc nat)
    with Cons show ?thesis
    proof (cases n m rule: linorder_cases)
      case less
      then show ?thesis
        by force
    next
      case equal
      with Suc show ?thesis 
        by (cases k, force)
           (metis (no_types, opaque_lifting) Cons.prems nths_single atLeastAtMost_singleton diff_is_0_eq' length_list_update list_update_code(2) list_update_code(3) list_update_nonempty nle_le nth_list_update_eq singletonD)
    next
      case greater
      with Suc Cons(1)[of nat "m - Suc 0" "n - Suc 0" x] show ?thesis
        by (cases k, simp_all add: nths_Cons_atLeastAtMost nths_atLeastAtMost_0_take take_update_swap, safe)
           (metis Cons.prems Suc_le_mono Suc_pred atLeastAtMost_iff diff_Suc_Suc le_zero_eq not_gr_zero)
    qed
  qed
qed

lemma length_nths_atLeastAtMost [simp]: "length (nths xs {m..n}) = min (Suc n) (length xs) - m"
  by (simp add: nths_atLeastAtMost_as_map)

lemma hd_nths_atLeastAtMost: "\<lbrakk> m < length xs; m \<le> n \<rbrakk> \<Longrightarrow> hd (nths xs {m..n}) = xs ! m"
  by (simp add: nths_atLeastAtMost_as_map upt_conv_Cons)

lemma tl_nths_atLeastAtMost: "tl (nths xs {m..n}) = nths xs {Suc m..n}"
  by (simp add: nths_atLeastAtMost_as_map, metis map_tl tl_upt)

lemma set_nths_atLeastAtMost: "set (nths xs {m..n}) = {xs!i | i. m \<le> i \<and> i \<le> n \<and> i < length xs}"
  by (auto simp add: nths_atLeastAtMost_as_map)

lemma nths_atLeastAtMost_neq_Nil [simp]: "\<lbrakk> m \<le> n; length xs > m \<rbrakk> \<Longrightarrow> nths xs {m..n} \<noteq> []"
  by (force simp add: nths_atLeastAtMost_as_map)

lemma nths_atLeastAtMost_head: "\<lbrakk> m \<le> n; m < length xs \<rbrakk> \<Longrightarrow> nths xs {m..n} = xs ! m # (nths xs {Suc m..n})"
  by (simp add: nths_atLeastAtMost_as_map upt_conv_Cons)

lemma sorted_hd_le_all: "\<lbrakk> xs \<noteq> []; sorted xs; x \<in> set xs \<rbrakk> \<Longrightarrow> hd xs \<le> x"
  by (metis Orderings.order_eq_iff list.sel(1) list.set_cases sorted_simps(2))

subsection \<open> List power \<close>

overloading
  listpow \<equiv> "compow :: nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
begin

fun listpow :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "listpow 0 xs = []" 
| "listpow (Suc n) xs = xs @ listpow n xs"

end

lemma listpow_Nil [simp]: "[] ^^ n = []"
  by (induct n) simp_all

lemma listpow_Suc_right: "xs ^^ Suc n = xs ^^ n @ xs"
  by (induct n) simp_all

lemma listpow_add: "xs ^^ (m + n) = xs ^^ m @ xs ^^ n"
  by (induct m) simp_all

subsection \<open> Alternative List Lexicographic Order \<close>

text \<open> Since we can't instantiate the order class twice for lists, and we often want prefix as
  the default order, we here add syntax for the lexicographic order relation. \<close>

definition list_lex_less :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "<\<^sub>l" 50)
where "xs <\<^sub>l ys \<longleftrightarrow> (xs, ys) \<in> lexord {(u, v). u < v}"

lemma list_lex_less_neq [simp]: "x <\<^sub>l y \<Longrightarrow> x \<noteq> y"
  apply (simp add: list_lex_less_def)
  apply (meson case_prodD less_irrefl lexord_irreflexive mem_Collect_eq)
  done

lemma not_less_Nil [simp]: "\<not> x <\<^sub>l []"
  by (simp add: list_lex_less_def)

lemma Nil_less_Cons [simp]: "[] <\<^sub>l a # x"
  by (simp add: list_lex_less_def)

lemma Cons_less_Cons [simp]: "a # x <\<^sub>l b # y \<longleftrightarrow> a < b \<or> a = b \<and> x <\<^sub>l y"
  by (simp add: list_lex_less_def)

subsection \<open> Bounded List Universe \<close>

text \<open> Analogous to @{const List.n_lists}, but includes all lists with a length up to the given number. \<close>

definition b_lists :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
"b_lists n xs = concat (map (\<lambda> n. List.n_lists n xs) [0..<Suc n])"

lemma b_lists_Nil [simp]: "b_lists n [] = [[]]"
  unfolding b_lists_def by (induct n) simp_all 

lemma length_b_lists_elem: "ys \<in> set (b_lists n xs) \<Longrightarrow> length ys \<le> n"
  unfolding b_lists_def
  by (auto simp add: length_n_lists_elem)

lemma b_lists_in_lists: "ys \<in> set (b_lists n xs) \<Longrightarrow> ys \<in> lists (set xs)"
  by (auto simp add: b_lists_def in_mono set_n_lists)

lemma in_blistsI: 
  assumes "length xs \<le> n" "xs \<in> lists (set A)"
  shows "xs \<in> set (b_lists n A)"
proof -
  have "xs \<notin> set (List.n_lists n A) \<Longrightarrow> xs \<in> set (List.n_lists (length xs) A)"
    using assms(2) in_lists_conv_set set_n_lists by fastforce
  with assms show ?thesis
  by (force simp add: set_n_lists subsetI b_lists_def)
qed

lemma ex_list_nonempty_carrier:
  assumes "A \<noteq> {}"
  obtains xs where "length xs = n" "set xs \<subseteq> A"
proof -
  obtain a where a: "a \<in> A"
    using assms by blast
  hence "set (replicate n a) \<subseteq> A"
    by (simp add: set_replicate_conv_if)
  with that show ?thesis
    by (meson length_replicate)
qed

lemma n_lists_inj:
  assumes "xs \<noteq> []" "List.n_lists m xs = List.n_lists n xs"
  shows "m = n"
proof (rule ccontr)
  assume mn: "m \<noteq> n"
  hence "m < n \<or> m > n"
    by auto
  moreover have "m < n \<longrightarrow> False"
  proof
    assume "m < n"
    then obtain ys where ys: "length ys = n" "set ys \<subseteq> set xs"
      by (metis all_not_in_conv assms(1) ex_list_nonempty_carrier length_0_conv neq0_conv nth_mem)
    hence "ys \<in> set (List.n_lists n xs)"
      by (simp add: set_n_lists)
    moreover have "ys \<notin> set (List.n_lists m xs)"
      using length_n_lists_elem mn ys(1) by blast
    ultimately show False
      by (simp add: assms(2))
  qed
  moreover have "m > n \<longrightarrow> False"
  proof
    assume "n < m"
    then obtain ys where ys: "length ys = m" "set ys \<subseteq> set xs"
      by (metis all_not_in_conv assms(1) ex_list_nonempty_carrier length_0_conv neq0_conv nth_mem)
    hence "ys \<in> set (List.n_lists m xs)"
      by (simp add: set_n_lists)
    moreover have "ys \<notin> set (List.n_lists n xs)"
      using length_n_lists_elem mn ys(1) by blast
    ultimately show False
      by (simp add: assms(2))
  qed
  ultimately show False
    by blast
qed 

lemma distinct_b_lists: "distinct xs \<Longrightarrow> distinct (b_lists n xs)"
  apply (cases "xs = []")
   apply (simp)
  apply (simp add: b_lists_def, safe)
    apply (rule distinct_concat)
      apply (simp add: distinct_map)
      apply (simp add: inj_onI n_lists_inj)
  using distinct_n_lists apply auto[1]
    apply (safe)
    apply (metis ex_map_conv length_n_lists_elem)
   apply (simp add: distinct_n_lists)
  apply (metis atLeastLessThan_iff length_n_lists_elem order_less_irrefl)
  done

definition bounded_lists :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a list set" where
  "bounded_lists n A = {xs\<in>lists A. length xs \<le> n}"

lemma bounded_lists_b_lists [code]: "bounded_lists n (set xs) = set (b_lists n xs)"
  apply (simp add: bounded_lists_def in_blistsI in_listsI, safe)
  using in_blistsI apply blast
  apply (meson b_lists_in_lists in_lists_conv_set)
  apply (meson length_b_lists_elem)
  done

subsection \<open> Disjointness and Partitions \<close>

definition list_disjoint :: "'a set list \<Rightarrow> bool" where
"list_disjoint xs = (\<forall> i < length xs. \<forall> j < length xs. i \<noteq> j \<longrightarrow> xs!i \<inter> xs!j = {})"

definition list_partitions :: "'a set list \<Rightarrow> 'a set \<Rightarrow> bool" where
"list_partitions xs T = (list_disjoint xs \<and> \<Union> (set xs) = T)"

lemma list_disjoint_Nil [simp]: "list_disjoint []"
  by (simp add: list_disjoint_def)

lemma list_disjoint_Cons [simp]: "list_disjoint (A # Bs) = ((\<forall> B \<in> set Bs. A \<inter> B = {}) \<and> list_disjoint Bs)"
  apply (simp add: list_disjoint_def disjoint_iff)
  apply (safe)
    apply (metis Suc_less_eq in_set_conv_nth nat.distinct(1) neq0_conv nth_Cons_0 nth_Cons_Suc)
   apply (metis lessI lift_Suc_mono_less_iff nat.inject nth_Cons_Suc)
  apply (metis less_Suc_eq_0_disj[of _ "length Bs"] nth_Cons_0[of A Bs] nth_Cons_Suc[of A Bs] nth_mem[of _ Bs])
  done

subsection \<open> Code Generation \<close>

lemma set_singleton_iff: "set xs = {x} \<longleftrightarrow> remdups xs = [x]"
  apply (safe)
    apply (metis card_set empty_set insert_not_empty length_0_conv length_Suc_conv list.simps(15) remdups.simps(1) remdups.simps(2) set_remdups the_elem_set)
   apply (metis empty_iff empty_set set_ConsD set_remdups)
  apply (metis list.set_intros(1) set_remdups)
  done

lemma list_singleton_iff: "(\<exists> x. xs = [x]) \<longleftrightarrow> (length xs = 1)"
  by (auto simp add: length_Suc_conv)

end
