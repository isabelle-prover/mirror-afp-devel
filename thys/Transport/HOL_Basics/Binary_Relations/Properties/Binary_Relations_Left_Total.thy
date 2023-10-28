\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Left Total\<close>
theory Binary_Relations_Left_Total
  imports
    Binary_Relation_Functions
    HOL_Syntax_Bundles_Lattices
begin

consts left_total_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"

overloading
  left_total_on_pred \<equiv> "left_total_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "left_total_on_pred P R \<equiv> \<forall>x. P x \<longrightarrow> in_dom R x"
end

lemma left_total_onI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> in_dom R x"
  shows "left_total_on P R"
  unfolding left_total_on_pred_def using assms by blast

lemma left_total_onE [elim]:
  assumes "left_total_on P R"
  and "P x"
  obtains y where "R x y"
  using assms unfolding left_total_on_pred_def by blast

lemma in_dom_if_left_total_on:
  assumes "left_total_on P R"
  and "P x"
  shows "in_dom R x"
  using assms by blast

definition "left_total (R :: 'a \<Rightarrow> _) \<equiv> left_total_on (\<top> :: 'a \<Rightarrow> bool) R"

lemma left_total_eq_left_total_on:
  "left_total (R :: 'a \<Rightarrow> _) = left_total_on (\<top> :: 'a \<Rightarrow> bool) R"
  unfolding left_total_def ..

lemma left_totalI [intro]:
  assumes "\<And>x. in_dom R x"
  shows "left_total R"
  unfolding left_total_eq_left_total_on using assms by (intro left_total_onI)

lemma left_totalE:
  assumes "left_total R"
  obtains y where "R x y"
  using assms unfolding left_total_eq_left_total_on by (blast intro: top1I)

lemma in_dom_if_left_total:
  assumes "left_total R"
  shows "in_dom R x"
  using assms by (blast elim: left_totalE)

lemma left_total_on_if_left_total:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "left_total R"
  shows "left_total_on P R"
  using assms by (intro left_total_onI) (blast dest: in_dom_if_left_total)


end