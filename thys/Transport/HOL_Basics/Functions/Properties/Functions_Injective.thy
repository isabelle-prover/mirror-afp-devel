\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Injective\<close>
theory Functions_Injective
  imports
    Functions_Base
    HOL_Syntax_Bundles_Lattices
begin

consts injective_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> bool"

overloading
  injective_on_pred \<equiv> "injective_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
begin
  definition "injective_on_pred P f \<equiv> \<forall>x x'. P x \<longrightarrow> P x' \<longrightarrow> f x = f x' \<longrightarrow> x = x'"
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

definition "injective (f :: 'a \<Rightarrow> _) \<equiv> injective_on (\<top> :: 'a \<Rightarrow> bool) f"

lemma injective_eq_injective_on:
  "injective (f :: 'a \<Rightarrow> _) = injective_on (\<top> :: 'a \<Rightarrow> bool) f"
  unfolding injective_def ..

lemma injectiveI [intro]:
  assumes "\<And>x x'. f x = f x' \<Longrightarrow> x = x'"
  shows "injective f"
  unfolding injective_eq_injective_on using assms by (intro injective_onI)

lemma injectiveD:
  assumes "injective f"
  and "f x = f x'"
  shows "x = x'"
  using assms unfolding injective_eq_injective_on by (auto dest: injective_onD)

lemma injective_on_if_injective:
  fixes P :: "'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> _"
  assumes "injective f"
  shows "injective_on P f"
  using assms by (intro injective_onI) (blast dest: injectiveD)


paragraph \<open>Instantiations\<close>

lemma injective_id: "injective id" by auto


end