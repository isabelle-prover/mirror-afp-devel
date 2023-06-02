subsection \<open>Multisets\<close>

text \<open>Some preliminary results about multisets.\<close>

theory Expander_Graphs_Multiset_Extras
  imports 
    Frequency_Moments.Frequency_Moments_Preliminary_Results 
    Extra_Congruence_Method
begin

unbundle intro_cong_syntax

lemma sum_mset_conv: 
  fixes f :: "'a \<Rightarrow> 'b::{semiring_1}"
  shows "sum_mset (image_mset f A) = sum (\<lambda>x. of_nat (count A x) * f x) (set_mset A)"
proof (induction A rule: disj_induct_mset)
  case 1
  then show ?case by simp
next
  case (2 n M x)
  moreover have "count M x = 0" using 2 by (simp add: count_eq_zero_iff)
  moreover have "\<And>y. y \<in> set_mset M \<Longrightarrow> y \<noteq> x" using 2 by blast
  ultimately show ?case by (simp add:algebra_simps) 
qed

lemma sum_mset_conv_2: 
  fixes f :: "'a \<Rightarrow> 'b::{semiring_1}"
  assumes "set_mset A \<subseteq> B" "finite B"
  shows "sum_mset (image_mset f A) = sum (\<lambda>x. of_nat (count A x) * f x) B" (is "?L = ?R")
proof -
  have "?L = sum (\<lambda>x. of_nat (count A x) * f x) (set_mset A)"
    unfolding sum_mset_conv by simp
  also have "... = ?R"
    by (intro sum.mono_neutral_left assms) (simp_all add: iffD2[OF count_eq_zero_iff])
  finally show ?thesis by simp
qed

lemma count_mset_exp: "count A x = size (filter_mset (\<lambda>y. y = x) A)"
  by (induction A, simp, simp)

lemma mset_repl: "mset (replicate k x) = replicate_mset k x"
  by (induction k, auto)

lemma count_image_mset_inj:
  assumes "inj f"
  shows "count (image_mset f A) (f x) = count A x"
proof (cases "x \<in> set_mset A")
  case True
  hence "f -` {f x} \<inter> set_mset A = {x}" 
    using assms by (auto simp add:vimage_def inj_def) 
  then show ?thesis by (simp add:count_image_mset)
next
  case False
  hence "f -` {f x} \<inter> set_mset A = {}" 
    using assms by (auto simp add:vimage_def inj_def) 
  thus ?thesis  using False by (simp add:count_image_mset count_eq_zero_iff)
qed

lemma count_image_mset_0_triv:
  assumes "x \<notin> range f"
  shows "count (image_mset f A) x = 0" 
proof -
  have "x \<notin> set_mset (image_mset f A)" 
    using assms by auto
  thus ?thesis 
    by (meson count_inI)
qed

lemma filter_mset_ex_predicates:
  assumes "\<And>x. \<not> P x \<or> \<not> Q x"
  shows "filter_mset P M + filter_mset Q M = filter_mset (\<lambda>x. P x \<or> Q x) M"
  using assms by (induction M, auto)

lemma sum_count_2: 
  assumes "finite F"
  shows "sum (count M) F = size (filter_mset (\<lambda>x. x \<in> F) M)"
  using assms
proof (induction F rule:finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  have "sum (count M) (insert x F) = size ({#y \<in># M. y = x#} + {#x \<in># M. x \<in> F#})"
    using insert(1,2,3) by (simp add:count_mset_exp)
  also have "... = size ({#y \<in># M. y = x \<or> y \<in> F#})"
    using insert(2)
    by (intro arg_cong[where f="size"] filter_mset_ex_predicates) simp
  also have "... = size (filter_mset (\<lambda>y. y \<in> insert x F) M)"
    by simp
  finally show ?case by simp
qed

definition concat_mset :: "('a multiset) multiset \<Rightarrow> 'a multiset"
  where "concat_mset xss = fold_mset (\<lambda>xs ys. xs + ys) {#} xss"

lemma image_concat_mset:
  "image_mset f (concat_mset xss) = concat_mset (image_mset (image_mset f) xss)"
  unfolding concat_mset_def by (induction xss, auto)

lemma concat_add_mset:
  "concat_mset (image_mset (\<lambda>x. f x + g x) xs) = concat_mset (image_mset f xs) + concat_mset (image_mset g xs)"
  unfolding concat_mset_def by (induction xs) auto

lemma concat_add_mset_2:
  "concat_mset (xs + ys) = concat_mset xs + concat_mset ys"
  unfolding concat_mset_def by (induction xs, auto)

lemma size_concat_mset:
  "size (concat_mset xss) = sum_mset (image_mset size xss)"
  unfolding concat_mset_def by (induction xss, auto)

lemma filter_concat_mset:
  "filter_mset P (concat_mset xss) = concat_mset (image_mset (filter_mset P) xss)"
  unfolding concat_mset_def by (induction xss, auto)

lemma count_concat_mset:
  "count (concat_mset xss) xs = sum_mset (image_mset (\<lambda>x. count x xs) xss)"
  unfolding concat_mset_def by (induction xss, auto)

lemma set_mset_concat_mset:
  "set_mset (concat_mset xss) = \<Union> (set_mset ` (set_mset xss))"
  unfolding concat_mset_def by (induction xss, auto)

lemma concat_mset_empty: "concat_mset {#} = {#}"
  unfolding concat_mset_def by simp

lemma concat_mset_single: "concat_mset {#x#} = x"
  unfolding concat_mset_def by simp

lemma concat_disjoint_union_mset:
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> finite (A i)"
  assumes "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
  shows  "mset_set (\<Union> (A ` I)) = concat_mset (image_mset (mset_set \<circ> A) (mset_set I))"
  using assms
proof (induction I rule:finite_induct)
  case empty
  then show ?case by (simp add:concat_mset_empty)
next
  case (insert x F)
  have "mset_set (\<Union> (A ` insert x F)) = mset_set (A x \<union> (\<Union> (A ` F)))"
    by simp
  also have "... = mset_set (A x) + mset_set (\<Union> (A ` F))"
    using insert by (intro mset_set_Union) auto
  also have "... = mset_set (A x) + concat_mset (image_mset (mset_set \<circ> A) (mset_set F))"
    using insert by (intro arg_cong2[where f="(+)"] insert(3)) auto
  also have "... = concat_mset (image_mset (mset_set \<circ> A) ({#x#} + mset_set F))"
    by (simp add:concat_mset_def)
  also have "... = concat_mset (image_mset (mset_set \<circ> A) (mset_set (insert x F)))"
    using insert by (intro_cong "[\<sigma>\<^sub>1 concat_mset, \<sigma>\<^sub>2 image_mset]") auto
  finally show ?case by blast
qed

lemma size_filter_mset_conv:
  "size (filter_mset f A) = sum_mset (image_mset (\<lambda>x. of_bool (f x) :: nat) A)"
  by (induction A, auto)

lemma filter_mset_const: "filter_mset (\<lambda>_. c) xs = (if c then xs else {#})"
  by simp

lemma repeat_image_concat_mset: 
  "repeat_mset n (image_mset f A) = concat_mset (image_mset (\<lambda>x. replicate_mset n (f x)) A)"
  unfolding concat_mset_def by (induction A, auto)

lemma mset_prod_eq:
  assumes "finite A" "finite B"
  shows 
    "mset_set (A \<times> B) = concat_mset {# {# (x,y). y \<in># mset_set B #} .x \<in># mset_set A #}"
  using assms(1)
proof (induction rule:finite_induct)
  case empty
  then show ?case unfolding concat_mset_def by simp
next
  case (insert x F)
  have "mset_set (insert x F \<times> B) = mset_set (F \<times> B \<union> (\<lambda>y. (x,y)) ` B)"
    by (intro arg_cong[where f="mset_set"]) auto
  also have "... = mset_set (F \<times> B) + mset_set ((\<lambda>y. (x,y)) ` B)"
    using insert(1,2) assms(2) by (intro mset_set_Union finite_cartesian_product) auto
  also have "... = mset_set (F \<times> B) + {# (x,y). y \<in># mset_set B #}"
    by (intro arg_cong2[where f="(+)"] image_mset_mset_set[symmetric] inj_onI) auto
  also have "... = concat_mset {#image_mset (Pair x) (mset_set B). x \<in># {#x#} + (mset_set F)#}"
    unfolding insert image_mset_union concat_add_mset_2 by (simp add:concat_mset_single)
  also have "... = concat_mset {#image_mset (Pair x) (mset_set B). x \<in># mset_set (insert x F)#}"
    using insert(1,2) by (intro_cong "[\<sigma>\<^sub>1 concat_mset, \<sigma>\<^sub>2 image_mset]") auto
  finally show ?case by simp
qed

lemma sum_mset_repeat: 
  fixes f :: "'a \<Rightarrow> 'b :: {comm_monoid_add,semiring_1}"
  shows "sum_mset (image_mset f (repeat_mset n A)) = of_nat n * sum_mset (image_mset f A)"
  by (induction n, auto simp add:sum_mset.distrib algebra_simps)

unbundle no_intro_cong_syntax

end