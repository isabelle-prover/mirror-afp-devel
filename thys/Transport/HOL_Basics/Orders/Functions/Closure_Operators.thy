\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Closure Operators\<close>
theory Closure_Operators
  imports
    Order_Functions_Base
begin

consts idempotent_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"

overloading
  idempotent_on_pred \<equiv> "idempotent_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "idempotent_on_pred (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (f :: 'a \<Rightarrow> 'a) \<equiv>
    rel_equivalence_on P (rel_map f R) f"
end

context
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'a"
begin

lemma idempotent_onI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> f x \<equiv>\<^bsub>R\<^esub> f (f x)"
  shows "idempotent_on P R f"
  unfolding idempotent_on_pred_def using assms by fastforce

lemma idempotent_onE [elim]:
  assumes "idempotent_on P R f"
  and "P x"
  obtains "f x \<equiv>\<^bsub>R\<^esub> f (f x)"
  using assms unfolding idempotent_on_pred_def by fastforce

lemma rel_equivalence_on_rel_map_iff_idempotent_on [iff]:
  "rel_equivalence_on P (rel_map f R) f \<longleftrightarrow> idempotent_on P R f"
  unfolding idempotent_on_pred_def by simp

lemma idempotent_onD:
  assumes "idempotent_on P R f"
  and "P x"
  shows "f x \<equiv>\<^bsub>R\<^esub> f (f x)"
  using assms by blast

end

consts idempotent :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  idempotent \<equiv> "idempotent :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "(idempotent :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool) \<equiv> idempotent_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma idempotent_eq_idempotent_on:
  "(idempotent :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool) = idempotent_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding idempotent_def ..

lemma idempotent_eq_idempotent_on_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'a \<Rightarrow> bool)"
  shows "idempotent :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool \<equiv> idempotent_on P"
  using assms by (simp add: idempotent_eq_idempotent_on)

context
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'a"
begin

lemma idempotentI [intro]:
  assumes "\<And>x. f x \<equiv>\<^bsub>R\<^esub> f (f x)"
  shows "idempotent R f"
  using assms by (urule idempotent_onI)

lemma idempotentD [dest]:
  assumes "idempotent R f"
  shows "f x \<equiv>\<^bsub>R\<^esub> f (f x)"
  using assms by (urule (e) idempotent_onE where chained = insert) simp

lemma idempotent_on_if_idempotent:
  assumes "idempotent R f"
  shows "idempotent_on P R f"
  using assms by (intro idempotent_onI) auto

end

consts closure_operator :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  closure_operator \<equiv> "closure_operator :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
begin
definition "closure_operator (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) :: ('a \<Rightarrow> 'a) \<Rightarrow> bool \<equiv>
  (R \<Rrightarrow>\<^sub>m R) \<sqinter> inflationary_on (in_field R) R \<sqinter> idempotent_on (in_field R) R"
end

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

context
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'a"
begin

lemma inflationary_on_in_field_if_closure_operator:
  assumes "closure_operator R f"
  shows "inflationary_on (in_field R) R f"
  using assms by (elim closure_operatorE)

lemma idempotent_on_in_field_if_closure_operator:
  assumes "closure_operator R f"
  shows "idempotent_on (in_field R) R f"
  using assms by (elim closure_operatorE)

end

end
