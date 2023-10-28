\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Irreflexive\<close>
theory Binary_Relations_Irreflexive
  imports
    Binary_Relation_Functions
    HOL_Syntax_Bundles_Lattices
begin

consts irreflexive_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"

overloading
  irreflexive_on_pred \<equiv> "irreflexive_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "irreflexive_on_pred P R \<equiv> \<forall>x. P x \<longrightarrow> \<not>(R x x)"
end

lemma irreflexive_onI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> \<not>(R x x)"
  shows "irreflexive_on P R"
  using assms unfolding irreflexive_on_pred_def by blast

lemma irreflexive_onD [dest]:
  assumes "irreflexive_on P R"
  and "P x"
  shows "\<not>(R x x)"
  using assms unfolding irreflexive_on_pred_def by blast

definition "irreflexive (R :: 'a \<Rightarrow> _) \<equiv> irreflexive_on (\<top> :: 'a \<Rightarrow> bool) R"

lemma irreflexive_eq_irreflexive_on:
  "irreflexive (R :: 'a \<Rightarrow> _) = irreflexive_on (\<top> :: 'a \<Rightarrow> bool) R"
  unfolding irreflexive_def ..

lemma irreflexiveI [intro]:
  assumes "\<And>x. \<not>(R x x)"
  shows "irreflexive R"
  unfolding irreflexive_eq_irreflexive_on using assms by (intro irreflexive_onI)

lemma irreflexiveD:
  assumes "irreflexive R"
  shows "\<not>(R x x)"
  using assms unfolding irreflexive_eq_irreflexive_on by auto

lemma irreflexive_on_if_irreflexive:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "irreflexive R"
  shows "irreflexive_on P R"
  using assms by (intro irreflexive_onI) (blast dest: irreflexiveD)


end