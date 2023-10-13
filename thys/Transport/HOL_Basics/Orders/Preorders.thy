\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Preorders\<close>
theory Preorders
  imports
    Binary_Relations_Reflexive
    Binary_Relations_Transitive
begin

definition "preorder_on P R \<equiv> reflexive_on P R \<and> transitive_on P R"

lemma preorder_onI [intro]:
  assumes "reflexive_on P R"
  and "transitive_on P R"
  shows "preorder_on P R"
  unfolding preorder_on_def using assms by blast

lemma preorder_onE [elim]:
  assumes "preorder_on P R"
  obtains "reflexive_on P R" "transitive_on P R"
  using assms unfolding preorder_on_def by blast

lemma reflexive_on_if_preorder_on:
  assumes "preorder_on P R"
  shows "reflexive_on P R"
  using assms by (elim preorder_onE)

lemma transitive_on_if_preorder_on:
  assumes "preorder_on P R"
  shows "transitive_on P R"
  using assms by (elim preorder_onE)

lemma transitive_if_preorder_on_in_field:
  assumes "preorder_on (in_field R) R"
  shows "transitive R"
  using assms by (elim preorder_onE) (rule transitive_if_transitive_on_in_field)

corollary preorder_on_in_fieldE [elim]:
  assumes "preorder_on (in_field R) R"
  obtains "reflexive_on (in_field R) R" "transitive R"
  using assms
  by (blast dest: reflexive_on_if_preorder_on transitive_if_preorder_on_in_field)

lemma preorder_on_rel_inv_if_preorder_on [iff]:
  "preorder_on P R\<inverse> \<longleftrightarrow> preorder_on (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> _)"
  by auto

lemma rel_if_all_rel_if_rel_if_reflexive_on:
  assumes "reflexive_on P R"
  and "\<And>z. P z \<Longrightarrow> R x z \<Longrightarrow> R y z"
  and "P x"
  shows "R y x"
  using assms by blast

lemma rel_if_all_rel_if_rel_if_reflexive_on':
  assumes "reflexive_on P R"
  and "\<And>z. P z \<Longrightarrow> R z x \<Longrightarrow> R z y"
  and "P x"
  shows "R x y"
  using assms by blast

definition "preorder (R :: 'a \<Rightarrow> _) \<equiv> preorder_on (\<top> :: 'a \<Rightarrow> bool) R"

lemma preorder_eq_preorder_on:
  "preorder (R :: 'a \<Rightarrow> _) = preorder_on (\<top> :: 'a \<Rightarrow> bool) R"
  unfolding preorder_def ..

lemma preorderI [intro]:
  assumes "reflexive R"
  and "transitive R"
  shows "preorder R"
  unfolding preorder_eq_preorder_on using assms
  by (intro preorder_onI reflexive_on_if_reflexive transitive_on_if_transitive)

lemma preorderE [elim]:
  assumes "preorder R"
  obtains "reflexive R" "transitive R"
  using assms unfolding preorder_eq_preorder_on by (elim preorder_onE)
  (simp only: reflexive_eq_reflexive_on transitive_eq_transitive_on)

lemma preorder_on_if_preorder:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "preorder R"
  shows "preorder_on P R"
  using assms by (elim preorderE)
  (intro preorder_onI reflexive_on_if_reflexive transitive_on_if_transitive)


paragraph \<open>Instantiations\<close>

lemma preorder_eq: "preorder (=)"
  using reflexive_eq transitive_eq by (rule preorderI)


end
