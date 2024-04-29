\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Reflexive\<close>
theory Binary_Relations_Reflexive
  imports
    Functions_Monotone
    ML_Unification.ML_Unification_HOL_Setup
    ML_Unification.Unify_Resolve_Tactics
begin

consts reflexive_on :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  reflexive_on_pred \<equiv> "reflexive_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "reflexive_on_pred P R \<equiv> \<forall>x. P x \<longrightarrow> R x x"
end

lemma reflexive_onI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> R x x"
  shows "reflexive_on P R"
  using assms unfolding reflexive_on_pred_def by blast

lemma reflexive_onD [dest]:
  assumes "reflexive_on P R"
  and "P x"
  shows "R x x"
  using assms unfolding reflexive_on_pred_def by blast

context
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool"
begin

lemma le_in_dom_if_reflexive_on:
  assumes "reflexive_on P R"
  shows "P \<le> in_dom R"
  using assms by blast

lemma le_in_codom_if_reflexive_on:
  assumes "reflexive_on P R"
  shows "P \<le> in_codom R"
  using assms by blast

lemma in_codom_eq_in_dom_if_reflexive_on_in_field:
  assumes "reflexive_on (in_field R) R"
  shows "in_codom R = in_dom R"
  using assms by blast

lemma reflexive_on_rel_inv_iff_reflexive_on [iff]:
  "reflexive_on P R\<inverse> \<longleftrightarrow> reflexive_on P R"
  by blast

lemma mono_reflexive_on:
  "((\<ge>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<le>)) (reflexive_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool)"
  by fastforce

lemma reflexive_on_if_le_pred_if_reflexive_on:
  fixes P' :: "'a \<Rightarrow> bool"
  assumes "reflexive_on P R"
  and "P' \<le> P"
  shows "reflexive_on P' R"
  using assms by blast

end

lemma reflexive_on_sup_eq [simp]:
  "(reflexive_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) (P \<squnion> Q)
  = reflexive_on P \<sqinter> reflexive_on Q"
  by (intro ext iffI reflexive_onI)
  (auto intro: reflexive_on_if_le_pred_if_reflexive_on)

lemma reflexive_on_iff_eq_restrict_le:
  "reflexive_on (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> _) \<longleftrightarrow> ((=)\<restriction>\<^bsub>P\<^esub> \<le> R)"
  by blast


consts reflexive :: "'a \<Rightarrow> bool"

overloading
  reflexive \<equiv> "reflexive :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "reflexive :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> reflexive_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma reflexive_eq_reflexive_on:
  "(reflexive :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) = reflexive_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding reflexive_def ..

lemma reflexive_eq_reflexive_on_uhint [uhint]:
  "P \<equiv> (\<top> :: 'a \<Rightarrow> bool) \<Longrightarrow> (reflexive :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) \<equiv> reflexive_on P"
  by (simp add: reflexive_eq_reflexive_on)

lemma reflexiveI [intro]:
  assumes "\<And>x. R x x"
  shows "reflexive R"
  using assms by (urule reflexive_onI)

lemma reflexiveD:
  assumes "reflexive R"
  shows "R x x"
  using assms by (urule (d) reflexive_onD where chained = insert) simp

lemma reflexive_on_if_reflexive:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "reflexive R"
  shows "reflexive_on P R"
  using assms by (intro reflexive_onI) (blast dest: reflexiveD)

lemma reflexive_rel_inv_iff_reflexive [iff]:
  "reflexive (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool)\<inverse> \<longleftrightarrow> reflexive R"
  by (blast dest: reflexiveD)

lemma reflexive_iff_eq_le: "reflexive R \<longleftrightarrow> ((=) \<le> R)"
  unfolding reflexive_eq_reflexive_on reflexive_on_iff_eq_restrict_le
  by auto

paragraph \<open>Instantiations\<close>

lemma reflexive_eq: "reflexive (=)"
  by (rule reflexiveI) (rule refl)

lemma reflexive_top: "reflexive (\<top> :: 'a \<Rightarrow> 'a \<Rightarrow> bool)"
  by (rule reflexiveI) auto


end