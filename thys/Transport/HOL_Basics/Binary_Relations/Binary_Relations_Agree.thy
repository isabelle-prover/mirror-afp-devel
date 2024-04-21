\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Agreement\<close>
theory Binary_Relations_Agree
  imports
    Functions_Monotone
begin

consts rel_agree_on :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  rel_agree_on_pred \<equiv> "rel_agree_on :: ('a \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "rel_agree_on_pred (P :: 'a \<Rightarrow> bool) (\<R> :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) \<equiv>
    \<forall>R R' : \<R>. R\<restriction>\<^bsub>P\<^esub> = R'\<restriction>\<^bsub>P\<^esub>"
end

lemma rel_agree_onI [intro]:
  assumes "\<And>R R' x y. \<R> R \<Longrightarrow> \<R> R' \<Longrightarrow> P x \<Longrightarrow> R x y \<Longrightarrow> R' x y"
  shows "rel_agree_on P \<R>"
  using assms unfolding rel_agree_on_pred_def by blast

lemma rel_agree_onE:
  assumes "rel_agree_on P \<R>"
  obtains "\<And>R R'. \<R> R \<Longrightarrow> \<R> R' \<Longrightarrow> R\<restriction>\<^bsub>P\<^esub> = R'\<restriction>\<^bsub>P\<^esub>"
  using assms unfolding rel_agree_on_pred_def by blast

lemma rel_restrict_left_eq_if_rel_agree_onI:
  assumes "rel_agree_on P \<R>"
  and "\<R> R" "\<R> R'"
  shows "R\<restriction>\<^bsub>P\<^esub> = R'\<restriction>\<^bsub>P\<^esub>"
  using assms by (blast elim: rel_agree_onE)

lemma rel_agree_onD:
  assumes "rel_agree_on P \<R>"
  and "\<R> R" "\<R> R'"
  and "P x"
  and "R x y"
  shows "R' x y"
  using assms by (blast elim: rel_agree_onE dest: fun_cong)

lemma antimono_rel_agree_on:
  "((\<le>) \<Rrightarrow>\<^sub>m (\<le>) \<Rrightarrow> (\<ge>)) (rel_agree_on :: ('a \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> bool)"
  by (intro mono_wrt_relI Fun_Rel_relI) (fastforce dest: rel_agree_onD)

lemma le_if_in_dom_le_if_rel_agree_onI:
  assumes "rel_agree_on A \<R>"
  and "\<R> R" "\<R> R'"
  and "in_dom R \<le> A"
  shows "R \<le> R'"
  using assms by (auto dest: rel_agree_onD[where ?R="R"])

lemma eq_if_in_dom_le_if_rel_agree_onI:
  assumes "rel_agree_on A \<R>"
  and "\<R> R" "\<R> R'"
  and "in_dom R \<le> A" "in_dom R' \<le> A"
  shows "R = R'"
  using assms le_if_in_dom_le_if_rel_agree_onI by blast

end