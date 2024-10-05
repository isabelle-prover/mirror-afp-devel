\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Functions_Restrict
  imports HOL_Basics_Base
begin

consts fun_restrict :: "'a \<Rightarrow> 'b \<Rightarrow> 'a"

bundle fun_restrict_syntax
begin
notation fun_restrict (\<open>(_)\<restriction>(\<^bsub>_\<^esub>)\<close> [1000])
end

definition "fun_restrict_pred f P x \<equiv> if P x then f x else undefined"
adhoc_overloading fun_restrict fun_restrict_pred

context
  includes fun_restrict_syntax
begin

lemma fun_restrict_eq [simp]:
  assumes "P x"
  shows "f\<restriction>\<^bsub>P\<^esub> x = f x"
  using assms unfolding fun_restrict_pred_def by auto

lemma fun_restrict_eq_if_not [simp]:
  assumes "\<not>(P x)"
  shows "f\<restriction>\<^bsub>P\<^esub> x = undefined"
  using assms unfolding fun_restrict_pred_def by auto

lemma fun_restrict_eq_if: "f\<restriction>\<^bsub>P\<^esub> x = (if P x then f x else undefined)"
  by auto

lemma fun_restrict_cong [cong]:
  assumes "P = P'"
  and "\<And>x. P' x \<Longrightarrow> f x = g x"
  shows "f\<restriction>\<^bsub>P\<^esub> = g\<restriction>\<^bsub>P'\<^esub>"
  using assms by (intro ext) (auto simp: fun_restrict_eq_if)

end


end