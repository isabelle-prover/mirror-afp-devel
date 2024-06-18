\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Least Element With Respect To Some Relation\<close>
theory Binary_Relations_Least
  imports
    Binary_Relations_Antisymmetric
    Bounded_Definite_Description
begin

definition "is_minimal_wrt_rel R (P :: 'a \<Rightarrow> bool) x \<equiv> P x \<and> (\<forall>y : P. R x y)"

lemma is_minimal_wrt_relI [intro]:
  assumes "P x"
  and "\<And>y. P y \<Longrightarrow> R x y"
  shows "is_minimal_wrt_rel R P x"
  unfolding is_minimal_wrt_rel_def using assms by blast

lemma is_minimal_wrt_relE [elim]:
  assumes "is_minimal_wrt_rel R P x"
  obtains "P x" "\<And>y. P y \<Longrightarrow> R x y"
  using assms unfolding is_minimal_wrt_rel_def by blast


definition "is_least_wrt_rel R (P :: 'a \<Rightarrow> bool) x \<equiv>
  is_minimal_wrt_rel R P x \<and> (\<forall>x'. is_minimal_wrt_rel R P x' \<longrightarrow> x' = x)"

lemma is_least_wrt_relI [intro]:
  assumes "is_minimal_wrt_rel R P x"
  and "\<And>x'. is_minimal_wrt_rel R P x' \<Longrightarrow> x' = x"
  shows "is_least_wrt_rel R P x"
  unfolding is_least_wrt_rel_def using assms by blast

lemma is_least_wrt_relE [elim]:
  assumes "is_least_wrt_rel R P x"
  obtains "is_minimal_wrt_rel R P x" "\<And>x'. is_minimal_wrt_rel R P x' \<Longrightarrow> x' = x"
  using assms unfolding is_least_wrt_rel_def by blast

lemma is_least_wrt_rel_if_antisymmetric_onI:
  assumes "antisymmetric_on P R"
  and "is_minimal_wrt_rel R P x"
  shows "is_least_wrt_rel R P x"
  using assms by (intro is_least_wrt_relI) (blast dest: antisymmetric_onD)+

corollary is_least_wrt_rel_eq_is_minimal_wrt_rel_if_antisymmetric_on [simp]:
  assumes "antisymmetric_on P R"
  shows "is_least_wrt_rel R P = is_minimal_wrt_rel R P"
  using assms is_least_wrt_rel_if_antisymmetric_onI by (intro ext iffI) auto


definition "least_wrt_rel R (P :: 'a \<Rightarrow> bool) \<equiv> THE x. is_least_wrt_rel R P x"

lemma least_wrt_rel_eqI:
  assumes "is_least_wrt_rel R P x"
  shows "least_wrt_rel R P = x"
  unfolding least_wrt_rel_def using assms by (intro the1_equality) blast

lemma least_wrt_rel_eq_if_antisymmetric_onI:
  assumes "antisymmetric_on P R"
  and "is_minimal_wrt_rel R P x"
  shows "least_wrt_rel R P = x"
  using assms by (intro least_wrt_rel_eqI) auto

lemma pred_least_wrt_relI:
  assumes "is_least_wrt_rel R P x"
  shows "P (least_wrt_rel R P)"
  unfolding least_wrt_rel_def by (rule the1I2) (use assms in auto)

lemma pred_least_wrt_rel_if_antisymmetric_onI:
  assumes "antisymmetric_on P R"
  and "is_minimal_wrt_rel R P x"
  shows "P (least_wrt_rel R P)"
  by (rule pred_least_wrt_relI) (use assms in auto)


end
