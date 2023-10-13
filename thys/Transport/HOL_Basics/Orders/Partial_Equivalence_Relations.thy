\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Partial Equivalence Relations\<close>
theory Partial_Equivalence_Relations
  imports
    Binary_Relations_Symmetric
    Preorders
begin

definition "partial_equivalence_rel_on P R \<equiv> transitive_on P R \<and> symmetric_on P R"

lemma partial_equivalence_rel_onI [intro]:
  assumes "transitive_on P R"
  and "symmetric_on P R"
  shows "partial_equivalence_rel_on P R"
  unfolding partial_equivalence_rel_on_def using assms by blast

lemma partial_equivalence_rel_onE [elim]:
  assumes "partial_equivalence_rel_on P R"
  obtains "transitive_on P R" "symmetric_on P R"
  using assms unfolding partial_equivalence_rel_on_def by blast

lemma partial_equivalence_rel_on_rel_self_if_rel_dom:
  assumes "partial_equivalence_rel_on (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool)"
  and "P x" "P y"
  and "R x y"
  shows "R x x"
  using assms by (blast dest: symmetric_onD transitive_onD)

lemma partial_equivalence_rel_on_rel_self_if_rel_codom:
  assumes "partial_equivalence_rel_on (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool)"
  and "P x" "P y"
  and "R x y"
  shows "R y y"
  using assms by (blast dest: symmetric_onD transitive_onD)

lemma partial_equivalence_rel_on_rel_inv_iff_partial_equivalence_rel_on [iff]:
  "partial_equivalence_rel_on P R\<inverse> \<longleftrightarrow> partial_equivalence_rel_on (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> _)"
  by blast

definition "partial_equivalence_rel (R :: 'a \<Rightarrow> _) \<equiv> partial_equivalence_rel_on (\<top> :: 'a \<Rightarrow> bool) R"

lemma partial_equivalence_rel_eq_partial_equivalence_rel_on:
  "partial_equivalence_rel (R :: 'a \<Rightarrow> _) = partial_equivalence_rel_on (\<top> :: 'a \<Rightarrow> bool) R"
  unfolding partial_equivalence_rel_def ..

lemma partial_equivalence_relI [intro]:
  assumes "transitive R"
  and "symmetric R"
  shows "partial_equivalence_rel R"
  unfolding partial_equivalence_rel_eq_partial_equivalence_rel_on using assms
  by (intro partial_equivalence_rel_onI transitive_on_if_transitive symmetric_on_if_symmetric)

lemma reflexive_on_in_field_if_partial_equivalence_rel:
  assumes "partial_equivalence_rel R"
  shows "reflexive_on (in_field R) R"
  using assms unfolding partial_equivalence_rel_eq_partial_equivalence_rel_on
  by (intro reflexive_onI) (blast
    intro: top1I partial_equivalence_rel_on_rel_self_if_rel_dom
    partial_equivalence_rel_on_rel_self_if_rel_codom)

lemma partial_equivalence_relE [elim]:
  assumes "partial_equivalence_rel R"
  obtains "preorder_on (in_field R) R" "symmetric R"
  using assms unfolding partial_equivalence_rel_eq_partial_equivalence_rel_on
  by (elim partial_equivalence_rel_onE)
  (auto intro: reflexive_on_in_field_if_partial_equivalence_rel
    simp flip: transitive_eq_transitive_on symmetric_eq_symmetric_on)

lemma partial_equivalence_rel_on_if_partial_equivalence_rel:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "partial_equivalence_rel R"
  shows "partial_equivalence_rel_on P R"
  using assms by (elim partial_equivalence_relE preorder_on_in_fieldE)
  (intro partial_equivalence_rel_onI transitive_on_if_transitive
    symmetric_on_if_symmetric)

lemma partial_equivalence_rel_rel_inv_iff_partial_equivalence_rel [iff]:
  "partial_equivalence_rel R\<inverse> \<longleftrightarrow> partial_equivalence_rel R"
  unfolding partial_equivalence_rel_eq_partial_equivalence_rel_on by blast

corollary in_codom_eq_in_dom_if_partial_equivalence_rel:
  assumes "partial_equivalence_rel R"
  shows "in_codom R = in_dom R"
  using assms reflexive_on_in_field_if_partial_equivalence_rel
    in_codom_eq_in_dom_if_reflexive_on_in_field
  by auto

lemma partial_equivalence_rel_rel_comp_self_eq_self:
  assumes "partial_equivalence_rel R"
  shows "(R \<circ>\<circ> R) = R"
  using assms by (intro ext) (blast dest: symmetricD)

lemma partial_equivalence_rel_if_partial_equivalence_rel_on_in_field:
  assumes "partial_equivalence_rel_on (in_field R) R"
  shows "partial_equivalence_rel R"
  using assms by (intro partial_equivalence_relI)
  (auto intro: transitive_if_transitive_on_in_field symmetric_if_symmetric_on_in_field)

corollary partial_equivalence_rel_on_in_field_iff_partial_equivalence_rel [iff]:
  "partial_equivalence_rel_on (in_field R) R \<longleftrightarrow> partial_equivalence_rel R"
  using partial_equivalence_rel_if_partial_equivalence_rel_on_in_field
    partial_equivalence_rel_on_if_partial_equivalence_rel
  by blast


paragraph \<open>Instantiations\<close>

lemma partial_equivalence_rel_eq: "partial_equivalence_rel (=)"
  using transitive_eq symmetric_eq by (rule partial_equivalence_relI)

lemma partial_equivalence_rel_top: "partial_equivalence_rel \<top>"
  using transitive_top symmetric_top by (rule partial_equivalence_relI)


end
