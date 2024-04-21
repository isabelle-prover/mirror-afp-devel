\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Left Total\<close>
theory Binary_Relations_Left_Total
  imports
    Functions_Monotone
begin

consts left_total_on :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  left_total_on_pred \<equiv> "left_total_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "left_total_on_pred P R \<equiv> \<forall>x : P. in_dom R x"
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

lemma le_in_dom_if_left_total_on:
  assumes "left_total_on P R"
  shows "P \<le> in_dom R"
  using assms by force

lemma left_total_on_if_le_in_dom:
  assumes "P \<le> in_dom R"
  shows "left_total_on P R"
  using assms by fastforce

lemma mono_left_total_on:
  "((\<ge>) \<Rrightarrow>\<^sub>m (\<le>) \<Rrightarrow> (\<le>)) (left_total_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  by fastforce

lemma le_in_dom_iff_left_total_on: "P \<le> in_dom R \<longleftrightarrow> left_total_on P R"
  using le_in_dom_if_left_total_on left_total_on_if_le_in_dom by auto

lemma mono_left_total_on_top_left_total_on_inf_rel_restrict_left:
  "((R : left_total_on P) \<Rrightarrow>\<^sub>m (P' : \<top>) \<Rrightarrow>\<^sub>m left_total_on (P \<sqinter> P')) rel_restrict_left"
  by fast

lemma mono_left_total_on_comp:
  "((R : left_total_on P) \<Rrightarrow>\<^sub>m left_total_on (in_codom (R\<restriction>\<^bsub>P\<^esub>)) \<Rrightarrow>\<^sub>m left_total_on P) (\<circ>\<circ>)"
  by fast

consts left_total :: "'a \<Rightarrow> bool"

overloading
  left_total \<equiv> "left_total :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "(left_total :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> left_total_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma left_total_eq_left_total_on:
  "(left_total :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> _) = left_total_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding left_total_def ..

lemma left_total_eq_left_total_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: 'a \<Rightarrow> bool"
  shows "left_total :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> _ \<equiv> left_total_on P"
  using assms by (simp add: left_total_eq_left_total_on)

lemma left_totalI [intro]:
  assumes "\<And>x. in_dom R x"
  shows "left_total R"
  using assms by (urule left_total_onI)

lemma left_totalE:
  assumes "left_total R"
  obtains y where "R x y"
  using assms by (urule (e) left_total_onE where chained = insert) simp

lemma in_dom_if_left_total:
  assumes "left_total R"
  shows "in_dom R x"
  using assms by (blast elim: left_totalE)

lemma left_total_on_if_left_total:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "left_total R"
  shows "left_total_on P R"
  using assms by (intro left_total_onI) (blast dest: in_dom_if_left_total)


end