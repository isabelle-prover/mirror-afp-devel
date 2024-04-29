\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Lambda Abstractions\<close>
theory Binary_Relations_Function_Lambda
  imports Binary_Relations_Clean_Function
begin

consts rel_lambda :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'd"

definition "rel_lambda_pred A f x y \<equiv> A x \<and> f x = y"
adhoc_overloading rel_lambda rel_lambda_pred

bundle rel_lambda_syntax
begin
syntax
  "_rel_lambda"  :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" ("(2\<lambda>_ : _./ _)" 60)
end
bundle no_rel_lambda_syntax
begin
no_syntax
  "_rel_lambda"  :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" ("(2\<lambda>_ : _./ _)" 60)
end
unbundle rel_lambda_syntax
translations
  "\<lambda>x : A. f" \<rightleftharpoons> "CONST rel_lambda A (\<lambda>x. f)"

lemma rel_lambdaI [intro]:
  assumes "A x"
  and "f x = y"
  shows "(\<lambda>x : A. f x) x y"
  using assms unfolding rel_lambda_pred_def by auto

lemma rel_lambda_appI:
  assumes "A x"
  shows "(\<lambda>x : A. f x) x (f x)"
  using assms by auto

lemma rel_lambdaE [elim!]:
  assumes "(\<lambda>x : A. f x) x y"
  obtains "A x" "y = f x"
  using assms unfolding rel_lambda_pred_def by auto

lemma rel_lambda_cong [cong]:
  "\<lbrakk>\<And>x. A x \<longleftrightarrow> A' x; \<And>x. A' x \<Longrightarrow> f x = f' x\<rbrakk> \<Longrightarrow> (\<lambda>x : A. f x) = \<lambda>x : A'. f' x"
  by (intro ext) auto

lemma in_dom_rel_lambda_eq [simp]: "in_dom (\<lambda>x : A. f x) = A"
  by auto

lemma in_codom_rel_lambda_eq_has_inverse_on [simp]: "in_codom (\<lambda>x : A. f x) = has_inverse_on A f"
  by fastforce

lemma left_total_on_rel_lambda: "left_total_on A (\<lambda>x : A. f x)"
  by auto

lemma right_unique_on_rel_lambda: "right_unique_on A (\<lambda>x : A. f x)"
  by auto

lemma crel_dep_mono_wrt_pred_rel_lambda: "((x : A) \<rightarrow>\<^sub>c ((=) (f x))) (\<lambda>x : A. f x)"
  by (intro crel_dep_mono_wrt_predI') auto

text \<open>Compare the following with @{thm mono_rel_dep_mono_wrt_pred_dep_mono_wrt_pred_eval}.\<close>

lemma mono_wrt_pred_mono_crel_dep_mono_wrt_pred_rel_lambda:
  "(((x : A) \<Rightarrow> B x) \<Rightarrow> (x : A) \<rightarrow>\<^sub>c B x) (rel_lambda A)"
  by (intro mono_wrt_predI crel_dep_mono_wrt_predI') auto

lemma rel_lambda_eval_eq [simp]: "A x \<Longrightarrow> (\<lambda>x : A. f x)`x = f x"
  by (rule eval_eq_if_right_unique_onI) auto

lemma app_eq_if_rel_lambda_eqI:
  assumes "(\<lambda>x : A. f x) = (\<lambda>x : A. g x)"
  and "A x"
  shows "f x = g x"
  using assms by (auto dest: fun_cong)

lemma crel_dep_mono_wrt_pred_inf_rel_lambda_inf_if_rel_dep_mono_wrt_pred:
  assumes "((x : A) \<rightarrow> B x) R"
  shows "((x : A \<sqinter> A') \<rightarrow>\<^sub>c B x) (\<lambda>x : A \<sqinter> A'. R`x)"
  using assms by force

corollary crel_dep_mono_wrt_pred_rel_lambda_if_le_if_rel_dep_mono_wrt_pred:
  assumes "((x : A) \<rightarrow> B x) R"
  and [uhint]: "A' \<le> A"
  shows "((x : A') \<rightarrow>\<^sub>c B x) (\<lambda>x : A'. R`x)"
  supply inf_absorb2[uhint]
  by (urule crel_dep_mono_wrt_pred_inf_rel_lambda_inf_if_rel_dep_mono_wrt_pred) (fact assms)

lemma rel_lambda_ext:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  and "\<And>x. A x \<Longrightarrow> f x = R`x"
  shows "(\<lambda>x : A. f x) = R"
  using assms by (intro ext iffI) (auto intro!: rel_lambdaI intro: rel_eval_if_rel_dep_mono_wrt_predI)

lemma rel_lambda_eval_eq_if_crel_dep_mono_wrt_pred [simp]: "((x : A) \<rightarrow>\<^sub>c B x) R \<Longrightarrow> (\<lambda>x : A. R`x) = R"
  by (rule rel_lambda_ext) auto

text \<open>Every element of @{term "(x : A) \<rightarrow>\<^sub>c (B x)"} may be expressed as a lambda abstraction.\<close>

lemma eq_rel_lambda_if_crel_dep_mono_wrt_predE:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  obtains f where "R = (\<lambda>x : A. f x)"
proof
  let ?f="(\<lambda>x. R`x)"
  from assms show "R = (\<lambda>x : A. (\<lambda>x. R`x) x)" by simp
qed

lemma rel_restrict_left_eq_rel_lambda_if_le_if_rel_dep_mono_wrt_pred:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A' \<le> A"
  shows "R\<restriction>\<^bsub>A'\<^esub> = (\<lambda>x : A'. R`x)"
proof -
  from assms mono_rel_dep_mono_wrt_pred_ge_crel_dep_mono_wrt_pred_rel_restrict_left
    have "((x : A') \<rightarrow>\<^sub>c B x) R\<restriction>\<^bsub>A'\<^esub>" by force
  then show ?thesis
    supply \<open>A' \<le> A\<close>[uhint] inf_absorb2[uhint] by (urule rel_lambda_ext[symmetric]) auto
qed

lemma mono_rel_lambda: "mono (\<lambda>A. \<lambda>x : A. f x)"
  by auto


end