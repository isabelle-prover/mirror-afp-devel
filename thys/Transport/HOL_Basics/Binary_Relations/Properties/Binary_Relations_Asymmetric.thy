\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Niklas Krofta"\<close>
theory Binary_Relations_Asymmetric
  imports
    Binary_Relations_Irreflexive
    Binary_Relations_Antisymmetric
    Functions_Monotone
begin

consts asymmetric_on :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  asymmetric_on_pred \<equiv> "asymmetric_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "asymmetric_on_pred (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool)
    \<equiv> \<forall>x y : P. R x y \<longrightarrow> \<not>(R y x)"
end

lemma asymmetric_onI [intro]:
  assumes "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> R x y \<Longrightarrow> \<not>(R y x)"
  shows "asymmetric_on P R"
  using assms unfolding asymmetric_on_pred_def by blast

lemma asymmetric_onD [dest]:
  assumes "asymmetric_on P R"
  and "P x" "P y"
  and "R x y"
  shows "\<not>(R y x)"
  using assms unfolding asymmetric_on_pred_def by blast

lemma asymmetric_onE:
  assumes "asymmetric_on P R"
  obtains "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> R x y \<Longrightarrow> \<not>(R y x)"
  using assms unfolding asymmetric_on_pred_def by blast

lemma asymmetric_on_le_irreflexive_on:
  "(asymmetric_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) \<le> irreflexive_on"
  by blast

lemma asymmetric_on_le_antisymmetric_on:
  "(asymmetric_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) \<le> antisymmetric_on"
  by blast

lemma antimono_asymmetric_on:
  "((\<le>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<ge>)) (asymmetric_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool)"
  by blast

lemma asymmetric_on_rel_map_if_mono_wrt_pred_if_asymmetric_on:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "asymmetric_on P R"
  and "(Q \<Rightarrow> P) f"
  shows "asymmetric_on Q (rel_map f R)"
  using assms by fastforce

consts asymmetric :: "'a \<Rightarrow> bool"

overloading
  asymmetric \<equiv> "asymmetric :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "asymmetric :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _ \<equiv> asymmetric_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma asymmetric_eq_asymmetric_on:
  "(asymmetric :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) = asymmetric_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding asymmetric_def ..

lemma asymmetric_eq_asymmetric_on_uhint [uhint]:
  "P \<equiv> (\<top> :: 'a \<Rightarrow> bool) \<Longrightarrow> (asymmetric :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) \<equiv> asymmetric_on P"
  by (simp add: asymmetric_eq_asymmetric_on)

lemma asymmetricI [intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> \<not>(R y x)"
  shows "asymmetric R"
  using assms by (urule asymmetric_onI)

lemma asymmetricD [dest]:
  assumes "asymmetric R"
  and "R x y"
  shows "\<not>(R y x)"
  using assms by (urule (d) asymmetric_onD where chained = insert) simp_all

lemma asymmetricE:
  assumes "asymmetric R"
  obtains "\<And>x y. R x y \<Longrightarrow> \<not>(R y x)"
  using assms by (urule (e) asymmetric_onE where chained = insert) simp_all

lemma asymmetric_on_if_asymmetric:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "asymmetric R"
  shows "asymmetric_on P R"
  using assms by (intro asymmetric_onI) blast

lemma asymmetric_if_asymmetric_on_in_field:
  assumes "asymmetric_on (in_field R) R"
  shows "asymmetric R"
  using assms by (intro asymmetricI) blast

corollary asymmetric_on_in_field_iff_asymmetric [iff]:
  "asymmetric_on (in_field R) R \<longleftrightarrow> asymmetric R"
  using asymmetric_if_asymmetric_on_in_field asymmetric_on_if_asymmetric by blast

lemma asymmetric_on_if_asymmetric_restrict:
  assumes "asymmetric R\<up>\<^bsub>P\<^esub>"
  shows "asymmetric_on P R"
  using assms by blast

lemma asymmetric_restrict_if_asymmetric_on:
  assumes "asymmetric_on P R"
  shows "asymmetric R\<up>\<^bsub>P\<^esub>"
  using assms by blast

corollary asymmetric_restrict_iff_asymmetric_on [iff]: "asymmetric R\<up>\<^bsub>P\<^esub> \<longleftrightarrow> asymmetric_on P R"
  using asymmetric_on_if_asymmetric_restrict asymmetric_restrict_if_asymmetric_on by blast

lemma asymmetric_le_irreflexive:
  "(asymmetric :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) \<le> irreflexive"
  by blast

lemma asymmetric_le_antisymmetric:
  "(asymmetric :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) \<le> antisymmetric"
  by blast

lemma antimono_asymmetric: "antimono (asymmetric :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _)"
  by blast


end