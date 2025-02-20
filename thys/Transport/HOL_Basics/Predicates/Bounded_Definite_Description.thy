\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Bounded Definite Description\<close>
theory Bounded_Definite_Description
  imports
    Bounded_Quantifiers
begin

consts bthe :: "'a \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'b"

open_bundle bounded_the_syntax
begin
syntax "_bthe" :: "[idt, 'a, bool] \<Rightarrow> 'b" (\<open>(3THE _ : _./ _)\<close> [0, 0, 10] 10)
end

syntax_consts "_bthe" \<rightleftharpoons> bthe
translations "THE x : P. Q" \<rightleftharpoons> "CONST bthe P (\<lambda>x. Q)"

definition "bthe_pred P Q \<equiv> The (P \<sqinter> Q)"
adhoc_overloading bthe \<rightleftharpoons> bthe_pred

lemma bthe_eqI [intro]:
  assumes "Q a"
  and "P a"
  and "\<And>x. \<lbrakk>P x; Q x\<rbrakk> \<Longrightarrow> x = a"
  shows "(THE x : P. Q x) = a"
  unfolding bthe_pred_def by (auto intro: assms)

lemma pred_bthe_if_ex1E:
  assumes "\<exists>!x : P. Q x"
  obtains "P (THE x : P. Q x)" "Q (THE x : P. Q x)"
  unfolding bthe_pred_def inf_fun_def using theI'[OF assms[unfolded bex1_pred_def]]
  by auto

lemma pred_btheI:
  assumes "\<exists>!x : P. Q x"
  shows "P (THE x : P. Q x)"
  using assms by (elim pred_bthe_if_ex1E)

lemma pred_btheI':
  assumes "\<exists>!x : P. Q x"
  shows "Q (THE x : P. Q x)"
  using assms by (elim pred_bthe_if_ex1E)


end