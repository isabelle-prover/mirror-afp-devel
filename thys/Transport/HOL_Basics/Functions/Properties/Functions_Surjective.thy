\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Surjective\<close>
theory Functions_Surjective
  imports
    HOL_Syntax_Bundles_Lattices
begin

consts surjective_at :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> bool"

overloading
  surjective_at_pred \<equiv> "surjective_at :: ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "surjective_at_pred P f \<equiv> \<forall>y. P y \<longrightarrow> (\<exists>x. y = f x)"
end

lemma surjective_atI [intro]:
  assumes "\<And>y. P y \<Longrightarrow> \<exists>x. y = f x"
  shows "surjective_at P f"
  unfolding surjective_at_pred_def using assms by blast

lemma surjective_atE [elim]:
  assumes "surjective_at P f"
  and "P y"
  obtains x where "y = f x"
  using assms unfolding surjective_at_pred_def by blast

definition "surjective (f :: _ \<Rightarrow> 'a) \<equiv> surjective_at (\<top> :: 'a \<Rightarrow> bool) f"

lemma surjective_eq_surjective_at:
  "surjective (f :: _ \<Rightarrow> 'a) = surjective_at (\<top> :: 'a \<Rightarrow> bool) f"
  unfolding surjective_def ..

lemma surjectiveI [intro]:
  assumes "\<And>y. \<exists>x. y = f x"
  shows "surjective f"
  unfolding surjective_eq_surjective_at using assms by (intro surjective_atI)

lemma surjectiveE:
  assumes "surjective f"
  obtains x where "y = f x"
  using assms unfolding surjective_eq_surjective_at by (blast intro: top1I)

lemma surjective_at_if_surjective:
  fixes P :: "'a \<Rightarrow> bool" and f :: "_ \<Rightarrow> 'a"
  assumes "surjective f"
  shows "surjective_at P f"
  using assms by (intro surjective_atI) (blast elim: surjectiveE)


end