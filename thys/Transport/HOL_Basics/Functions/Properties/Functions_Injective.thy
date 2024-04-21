\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Injective\<close>
theory Functions_Injective
  imports
    Bounded_Quantifiers
    Functions_Base
    HOL_Syntax_Bundles_Lattices
begin

consts injective_on :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  injective_on_pred \<equiv> "injective_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
begin
  definition "injective_on_pred P f \<equiv> \<forall>x x' : P. f x = f x' \<longrightarrow> x = x'"
end

lemma injective_onI [intro]:
  assumes "\<And>x x'. P x \<Longrightarrow> P x' \<Longrightarrow> f x = f x' \<Longrightarrow> x = x'"
  shows "injective_on P f"
  unfolding injective_on_pred_def using assms by blast

lemma injective_onD:
  assumes "injective_on P f"
  and "P x" "P x'"
  and "f x = f x'"
  shows "x = x'"
  using assms unfolding injective_on_pred_def by blast

consts injective :: "'a \<Rightarrow> bool"

overloading
  injective \<equiv> "injective :: ('a \<Rightarrow> 'b) \<Rightarrow> bool"
begin
  definition "(injective :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) \<equiv> injective_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma injective_eq_injective_on:
  "(injective :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) = injective_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding injective_def ..

lemma injective_eq_injective_on_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'a \<Rightarrow> bool)"
  shows "injective :: ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv> injective_on P"
  using assms by (simp add: injective_eq_injective_on)

lemma injectiveI [intro]:
  assumes "\<And>x x'. f x = f x' \<Longrightarrow> x = x'"
  shows "injective f"
  using assms by (urule injective_onI)

lemma injectiveD:
  assumes "injective f"
  and "f x = f x'"
  shows "x = x'"
  using assms by (urule (d) injective_onD where chained = insert) simp_all

lemma injective_on_if_injective:
  fixes P :: "'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> _"
  assumes "injective f"
  shows "injective_on P f"
  using assms by (intro injective_onI) (blast dest: injectiveD)


paragraph \<open>Instantiations\<close>

lemma injective_id: "injective id" by auto


end