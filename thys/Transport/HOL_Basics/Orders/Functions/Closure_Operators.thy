\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Closure Operators\<close>
theory Closure_Operators
  imports
    Order_Functions_Base
begin

definition "idempotent_on P R f \<equiv> rel_equivalence_on P (rel_map f R) f"

lemma idempotent_onI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> f x \<equiv>\<^bsub>R\<^esub> f (f x)"
  shows "idempotent_on P R f"
  unfolding idempotent_on_def using assms by fastforce

lemma idempotent_onE [elim]:
  assumes "idempotent_on P R f"
  and "P x"
  obtains "R (f (f x)) (f x)" "R (f x) (f (f x))"
  using assms unfolding idempotent_on_def by fastforce

lemma rel_equivalence_on_rel_map_iff_idempotent_on [iff]:
  "rel_equivalence_on P (rel_map f R) f \<longleftrightarrow> idempotent_on P R f"
  unfolding idempotent_on_def by simp

lemma bi_related_if_idempotent_onD:
  assumes "idempotent_on P R f"
  and "P x"
  shows "f x \<equiv>\<^bsub>R\<^esub> f (f x)"
  using assms by blast

definition "idempotent (R :: 'a \<Rightarrow> _) f \<equiv> idempotent_on (\<top> :: 'a \<Rightarrow> bool) R f"

lemma idempotent_eq_idempotent_on:
  "idempotent (R :: 'a \<Rightarrow> _) f = idempotent_on (\<top> :: 'a \<Rightarrow> bool) R f"
  unfolding idempotent_def ..

lemma idempotentI [intro]:
  assumes "\<And>x. R (f (f x)) (f x)"
  and "\<And>x. R (f x) (f (f x))"
  shows "idempotent R f"
  unfolding idempotent_eq_idempotent_on using assms by blast

lemma idempotentE [elim]:
  assumes "idempotent R f"
  obtains "R (f (f x)) (f x)" "R (f x) (f (f x))"
  using assms unfolding idempotent_eq_idempotent_on by (blast intro: top1I)

lemma idempotent_on_if_idempotent:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "idempotent R f"
  shows "idempotent_on P R f"
  using assms by (intro idempotent_onI) auto

definition "closure_operator R f \<equiv>
  (R \<Rrightarrow>\<^sub>m R) f \<and> inflationary_on (in_field R) R f \<and> idempotent_on (in_field R) R f"

lemma closure_operatorI [intro]:
  assumes "(R \<Rrightarrow>\<^sub>m R) f"
  and "inflationary_on (in_field R) R f"
  and "idempotent_on (in_field R) R f"
  shows "closure_operator R f"
  unfolding closure_operator_def using assms by blast

lemma closure_operatorE [elim]:
  assumes "closure_operator R f"
  obtains "(R \<Rrightarrow>\<^sub>m R) f" "inflationary_on (in_field R) R f"
    "idempotent_on (in_field R) R f"
  using assms unfolding closure_operator_def by blast

lemma mono_wrt_rel_if_closure_operator:
  assumes "closure_operator R f"
  shows "(R \<Rrightarrow>\<^sub>m R) f"
  using assms by (elim closure_operatorE)

lemma inflationary_on_in_field_if_closure_operator:
  assumes "closure_operator R f"
  shows "inflationary_on (in_field R) R f"
  using assms by (elim closure_operatorE)

lemma idempotent_on_in_field_if_closure_operator:
  assumes "closure_operator R f"
  shows "idempotent_on (in_field R) R f"
  using assms by (elim closure_operatorE)


end
