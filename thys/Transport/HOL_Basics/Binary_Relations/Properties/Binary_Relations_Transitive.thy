\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Transitive\<close>
theory Binary_Relations_Transitive
  imports
    Binary_Relation_Functions
    Functions_Monotone
begin

consts transitive_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"

overloading
  transitive_on_pred \<equiv> "transitive_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "transitive_on_pred P R \<equiv> \<forall>x y z. P x \<and> P y \<and> P z \<and> R x y \<and> R y z \<longrightarrow> R x z"
end

lemma transitive_onI [intro]:
  assumes "\<And>x y z. P x \<Longrightarrow> P y \<Longrightarrow> P z \<Longrightarrow> R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  shows "transitive_on P R"
  unfolding transitive_on_pred_def using assms by blast

lemma transitive_onD:
  assumes "transitive_on P R"
  and "P x" "P y" "P z"
  and "R x y" "R y z"
  shows "R x z"
  using assms unfolding transitive_on_pred_def by blast

lemma transitive_on_if_rel_comp_self_imp:
  assumes "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> (R \<circ>\<circ> R) x y \<Longrightarrow> R x y"
  shows "transitive_on P R"
proof (rule transitive_onI)
  fix x y z assume "R x y" "R y z"
  then have "(R \<circ>\<circ> R) x z" by (intro rel_compI)
  moreover assume "P x" "P y" "P z"
  ultimately show "R x z" by (simp only: assms)
qed

lemma transitive_on_rel_inv_iff_transitive_on [iff]:
  "transitive_on P R\<inverse> \<longleftrightarrow> transitive_on (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> _)"
  by (auto intro!: transitive_onI dest: transitive_onD)

lemma antimono_transitive_on [iff]:
  "antimono (\<lambda>(P :: 'a \<Rightarrow> bool). transitive_on P (R :: 'a \<Rightarrow> _))"
  by (intro antimonoI) (auto dest: transitive_onD)

lemma transitive_on_if_le_pred_if_transitive_on:
  fixes P P' :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "transitive_on P R"
  and "P' \<le> P"
  shows "transitive_on P' R"
  using assms by (auto dest: transitive_onD)

definition "transitive (R :: 'a \<Rightarrow> _) \<equiv> transitive_on (\<top> :: 'a \<Rightarrow> bool) R"

lemma transitive_eq_transitive_on:
  "transitive (R :: 'a \<Rightarrow> _) = transitive_on (\<top> :: 'a \<Rightarrow> bool) R"
  unfolding transitive_def ..

lemma transitiveI [intro]:
  assumes "\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  shows "transitive R"
  unfolding transitive_eq_transitive_on using assms by (intro transitive_onI)

lemma transitiveD [dest]:
  assumes "transitive R"
  and "R x y" "R y z"
  shows "R x z"
  using assms unfolding transitive_eq_transitive_on
  by (auto dest: transitive_onD)

lemma transitive_on_if_transitive:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "transitive R"
  shows "transitive_on P R"
  using assms by (intro transitive_onI) blast

lemma transitive_if_rel_comp_le_self:
  assumes "R \<circ>\<circ> R \<le> R"
  shows "transitive R"
  using assms unfolding transitive_eq_transitive_on
    by (intro transitive_on_if_rel_comp_self_imp) blast

lemma rel_comp_le_self_if_transitive:
  assumes "transitive R"
  shows "R \<circ>\<circ> R \<le> R"
  using assms by blast

corollary transitive_iff_rel_comp_le_self: "transitive R \<longleftrightarrow> R \<circ>\<circ> R \<le> R"
  using transitive_if_rel_comp_le_self rel_comp_le_self_if_transitive by blast

lemma transitive_if_transitive_on_in_field:
  assumes "transitive_on (in_field R) R"
  shows "transitive R"
  using assms by (intro transitiveI) (blast dest: transitive_onD)

corollary transitive_on_in_field_iff_transitive [simp]:
  "transitive_on (in_field R) R \<longleftrightarrow> transitive R"
  using transitive_if_transitive_on_in_field transitive_on_if_transitive
  by blast

lemma transitive_rel_inv_iff_transitive [iff]:
  "transitive R\<inverse> \<longleftrightarrow> transitive R"
  by (auto intro!: transitiveI)

paragraph \<open>Instantiations\<close>

lemma transitive_eq: "transitive (=)"
  by (rule transitiveI) (rule trans)

lemma transitive_top: "transitive \<top>"
  by (rule transitiveI) auto


end