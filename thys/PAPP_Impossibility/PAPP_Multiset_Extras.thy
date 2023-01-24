(*
  File:     PAPP_Multiset_Extras.thy
  Author:   Manuel Eberl, University of Innsbruck 
*)
section \<open>Auxiliary Facts About Multisets\<close>
theory PAPP_Multiset_Extras
  imports "HOL-Library.Multiset"
begin

text \<open>
  This section contains a number of not particularly interesting small facts about multisets.
\<close>

lemma mset_set_subset_iff: "finite A \<Longrightarrow> mset_set A \<subseteq># B \<longleftrightarrow> A \<subseteq> set_mset B"
  by (metis finite_set_mset finite_set_mset_mset_set mset_set_set_mset_msubset 
            msubset_mset_set_iff set_mset_mono subset_mset.trans)

lemma mset_subset_size_ge_imp_eq:
  assumes "A \<subseteq># B" "size A \<ge> size B"
  shows   "A = B"
  using assms
proof (induction A arbitrary: B)
  case empty
  thus ?case by auto
next
  case (add x A B)
  have [simp]: "x \<in># B"
    using add.prems  by (simp add: insert_subset_eq_iff)
  define B' where "B' = B - {#x#}"
  have B_eq: "B = add_mset x B'"
    using add.prems unfolding B'_def by (auto simp: add_mset_remove_trivial_If)
  have "A = B'"
    using add.prems by (intro add.IH) (auto simp: B_eq)
  thus ?case
    by (auto simp: B_eq)
qed

lemma mset_psubset_iff:
  "X \<subset># Y \<longleftrightarrow> X \<subseteq># Y \<and> (\<exists>x. count X x < count Y x)"
  by (meson less_le_not_le subset_mset.less_le_not_le subseteq_mset_def)
  
lemma count_le_size: "count A x \<le> size A"
  by (induction A) auto

lemma size_filter_eq_conv_count [simp]: "size (filter_mset (\<lambda>y. y = x) A) = count A x"
  by (induction A) auto

lemma multiset_filter_mono':
  assumes "\<And>x. x \<in># A \<Longrightarrow> P x \<Longrightarrow> Q x"
  shows   "filter_mset P A \<subseteq># filter_mset Q A"
  using assms by (induction A)  (auto simp: subset_mset.absorb_iff1 add_mset_union)

lemma multiset_filter_mono'':
  assumes "A \<subseteq># B" "\<And>x. x \<in># A \<Longrightarrow> P x \<Longrightarrow> Q x"
  shows "filter_mset P A \<subseteq># filter_mset Q B"
  using assms multiset_filter_mono multiset_filter_mono'
  by (metis subset_mset.order_trans)

lemma filter_mset_disjunction:
  assumes "\<And>x. x \<in># X \<Longrightarrow> P x \<Longrightarrow> Q x \<Longrightarrow> False"
  shows   "filter_mset (\<lambda>x. P x \<or> Q x) X = filter_mset P X + filter_mset Q X"
  using assms by (induction X) auto
  
lemma size_mset_sum_mset: "size (sum_mset X) = (\<Sum>x\<in>#X. size (x :: 'a multiset))"
  by (induction X) auto

lemma count_sum_mset: "count (sum_mset X) x = (\<Sum>Y\<in>#X. count Y x)"
  by (induction X) auto

lemma replicate_mset_rec: "n > 0 \<Longrightarrow> replicate_mset n x = add_mset x (replicate_mset (n - 1) x)"
  by (cases n) auto

lemma add_mset_neq: "x \<notin># B \<Longrightarrow> add_mset x A \<noteq> B"
  by force

lemma filter_replicate_mset:
  "filter_mset P (replicate_mset n x) = (if P x then replicate_mset n x else {#})"
  by (induction n) auto

lemma filter_diff_mset': "filter_mset P (X - Y) = filter_mset P X - Y"
  by (rule multiset_eqI) auto

lemma in_diff_multiset_absorb2: "x \<notin># B \<Longrightarrow> x \<in># A - B \<longleftrightarrow> x \<in># A"
  by (metis count_greater_zero_iff count_inI in_diff_count)

end
