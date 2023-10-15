\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Antisymmetric\<close>
theory Binary_Relations_Antisymmetric
  imports
    Binary_Relation_Functions
    HOL_Syntax_Bundles_Lattices
begin

consts antisymmetric_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"

overloading
  antisymmetric_on_pred \<equiv> "antisymmetric_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "antisymmetric_on_pred P R \<equiv> \<forall>x y. P x \<and> P y \<and> R x y \<and> R y x \<longrightarrow> x = y"
end

lemma antisymmetric_onI [intro]:
  assumes "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> R x y \<Longrightarrow> R y x \<Longrightarrow> x = y"
  shows "antisymmetric_on P R"
  unfolding antisymmetric_on_pred_def using assms by blast

lemma antisymmetric_onD:
  assumes "antisymmetric_on P R"
  and "P x" "P y"
  and "R x y" "R y x"
  shows "x = y"
  using assms unfolding antisymmetric_on_pred_def by blast

definition "antisymmetric (R :: 'a \<Rightarrow> _) \<equiv> antisymmetric_on (\<top> :: 'a \<Rightarrow> bool) R"

lemma antisymmetric_eq_antisymmetric_on:
  "antisymmetric (R :: 'a \<Rightarrow> _) = antisymmetric_on (\<top> :: 'a \<Rightarrow> bool) R"
  unfolding antisymmetric_def ..

lemma antisymmetricI [intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> R y x \<Longrightarrow> x = y"
  shows "antisymmetric R"
  unfolding antisymmetric_eq_antisymmetric_on using assms
  by (intro antisymmetric_onI)

lemma antisymmetricD:
  assumes "antisymmetric R"
  and "R x y" "R y x"
  shows "x = y"
  using assms unfolding antisymmetric_eq_antisymmetric_on
  by (auto dest: antisymmetric_onD)

lemma antisymmetric_on_if_antisymmetric:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "antisymmetric R"
  shows "antisymmetric_on P R"
  using assms by (intro antisymmetric_onI) (blast dest: antisymmetricD)

lemma antisymmetric_if_antisymmetric_on_in_field:
  assumes "antisymmetric_on (in_field R) R"
  shows "antisymmetric R"
  using assms by (intro antisymmetricI) (blast dest: antisymmetric_onD)

corollary antisymmetric_on_in_field_iff_antisymmetric [simp]:
  "antisymmetric_on (in_field R) R \<longleftrightarrow> antisymmetric R"
  using antisymmetric_if_antisymmetric_on_in_field antisymmetric_on_if_antisymmetric
  by blast


end