\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Evaluation of Functions as Binary Relations\<close>
theory Binary_Relations_Function_Evaluation
  imports
    Binary_Relations_Right_Unique
    Binary_Relations_Extend
begin

consts eval :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"

definition "eval_rel R x \<equiv> THE y. R x y"
adhoc_overloading eval eval_rel

bundle eval_syntax
begin
notation eval ("'(`')")
notation eval ("(_`_)" [999, 1000] 999)
end
bundle no_eval_syntax
begin
no_notation eval ("'(`')")
no_notation eval ("(_`_)" [999, 1000] 999)
end
unbundle eval_syntax

lemma eval_eq_if_right_unique_onI:
  assumes "right_unique_on P R"
  and "P x"
  and "R x y"
  shows "R`x = y"
  using assms unfolding eval_rel_def by (auto dest: right_unique_onD)

lemma eval_eq_if_right_unique_on_eqI:
  assumes "right_unique_on ((=) x) R"
  and "R x y"
  shows "R`x = y"
  using assms by (auto intro: eval_eq_if_right_unique_onI)

lemma rel_eval_if_ex1:
  assumes "\<exists>!y. R x y"
  shows "R x (R`x)"
  using assms unfolding eval_rel_def by (rule theI')

lemma rel_if_eval_eq_if_in_dom_if_right_unique_on_eq:
  assumes "right_unique_on ((=) x) R"
  and "in_dom R x"
  and "R`x = y"
  shows "R x y"
  using assms by (blast intro: rel_eval_if_ex1[of R x] dest: right_unique_onD)

corollary rel_eval_if_in_dom_if_right_unique_on_eq:
  assumes "right_unique_on ((=) x) R"
  and "in_dom R x"
  shows "R x (R`x)"
  using assms by (rule rel_if_eval_eq_if_in_dom_if_right_unique_on_eq) simp

lemma eq_app_eval_eq_eq [simp]: "(\<lambda>x. (=) (f x))`x = f x"
  by (auto intro: eval_eq_if_right_unique_onI)

lemma extend_eval_eq_if_not_in_dom [simp]:
  assumes "\<not>(in_dom R x)"
  shows "(extend x y R)`x = y"
  using assms by (force intro: eval_eq_if_right_unique_on_eqI)

corollary extend_bottom_eval_eq [simp]:
  fixes x :: 'a and y :: 'b
  shows "(extend x y (\<bottom> :: 'a \<Rightarrow> 'b \<Rightarrow> bool))`x = y"
  by (intro extend_eval_eq_if_not_in_dom) auto

lemma glue_eval_eqI:
  assumes "right_unique_on P (glue \<R>)"
  and "\<R> R"
  and "P x"
  and "R x y"
  shows "(glue \<R>)`x = y"
  using assms by (auto intro: eval_eq_if_right_unique_onI)

lemma glue_eval_eq_evalI:
  assumes "right_unique_on P (glue \<R>)"
  and "\<R> R"
  and "P x"
  and "in_dom R x"
  shows "(glue \<R>)`x = R`x"
  using assms by (intro glue_eval_eqI[of P \<R> R])
  (auto intro: rel_if_eval_eq_if_in_dom_if_right_unique_on_eq[of x] dest: right_unique_onD)

text \<open>Note: the following rest on the definition of extend and eval:\<close>

lemma extend_eval_eq_if_neq [simp]:
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  shows "x \<noteq> y \<Longrightarrow> (extend y z R)`x = R`x"
  unfolding extend_rel_def eval_rel_def by auto

lemma sup_eval_eq_left_eval_if_not_in_dom [simp]:
  fixes R S :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  shows "\<not>(in_dom S x) \<Longrightarrow> (R \<squnion> S)`x = R`x"
  unfolding eval_rel_def by (cases "\<exists>y. S x y") auto

lemma sup_eval_eq_right_eval_if_not_in_dom [simp]:
  fixes R S :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  shows "\<not>(in_dom R x) \<Longrightarrow> (R \<squnion> S)`x = S`x"
  unfolding eval_rel_def by (cases "\<exists>y. R x y") auto

lemma rel_restrict_left_eval_eq_if_pred [simp]:
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "P x"
  shows "(R\<restriction>\<^bsub>P\<^esub>)`x = R`x"
  (*FIXME: proof relying on specific definitions; can we do better?*)
  using assms unfolding eval_rel_def rel_restrict_left_pred_def by auto

end
