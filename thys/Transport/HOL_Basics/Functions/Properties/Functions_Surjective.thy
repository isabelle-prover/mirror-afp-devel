\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Surjective\<close>
theory Functions_Surjective
  imports
    Functions_Base
begin

consts surjective_at :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  surjective_at_pred \<equiv> "surjective_at :: ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "surjective_at_pred (P :: 'a \<Rightarrow> bool) (f :: 'b \<Rightarrow> 'a) \<equiv> \<forall>y : P. has_inverse f y"
end

lemma surjective_atI [intro]:
  assumes "\<And>y. P y \<Longrightarrow> has_inverse f y"
  shows "surjective_at P f"
  unfolding surjective_at_pred_def using assms by blast

lemma surjective_atE [elim]:
  assumes "surjective_at P f"
  and "P y"
  obtains x where "y = f x"
  using assms unfolding surjective_at_pred_def by blast

lemma has_inverse_if_pred_if_surjective_at:
  assumes "surjective_at P f"
  and "P y"
  shows "has_inverse f y"
  using assms by blast

consts surjective :: "'a \<Rightarrow> bool"

overloading
  surjective \<equiv> "surjective :: ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "(surjective :: ('b \<Rightarrow> 'a) \<Rightarrow> bool) \<equiv> surjective_at (\<top> :: 'a \<Rightarrow> bool)"
end

lemma surjective_eq_surjective_at:
  "(surjective :: ('b \<Rightarrow> 'a) \<Rightarrow> bool) = surjective_at (\<top> :: 'a \<Rightarrow> bool)"
  unfolding surjective_def ..

lemma surjective_eq_surjective_at_uhint [uhint]:
  assumes "P \<equiv>  \<top> :: 'a \<Rightarrow> bool"
  shows "surjective :: ('b \<Rightarrow> 'a) \<Rightarrow> bool \<equiv> surjective_at P"
  using assms by (simp add: surjective_eq_surjective_at)

lemma surjectiveI [intro]:
  assumes "\<And>y. has_inverse f y"
  shows "surjective f"
  using assms by (urule surjective_atI)

lemma surjectiveE:
  assumes "surjective f"
  obtains "\<And>y. has_inverse f y"
  using assms unfolding surjective_eq_surjective_at by (force dest: has_inverseI)

lemma surjective_at_if_surjective:
  fixes P :: "'a \<Rightarrow> bool" and f :: "'b \<Rightarrow> 'a"
  assumes "surjective f"
  shows "surjective_at P f"
  using assms by (intro surjective_atI) (blast elim: surjectiveE)

end