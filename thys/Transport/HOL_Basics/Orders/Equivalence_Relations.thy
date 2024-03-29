\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Equivalences\<close>
theory Equivalence_Relations
  imports
    Partial_Equivalence_Relations
begin

definition "equivalence_rel_on \<equiv> partial_equivalence_rel_on \<sqinter> reflexive_on"

lemma equivalence_rel_onI [intro]:
  assumes "partial_equivalence_rel_on P R"
  and "reflexive_on P R"
  shows "equivalence_rel_on P R"
  unfolding equivalence_rel_on_def using assms by auto

lemma equivalence_rel_onE [elim]:
  assumes "equivalence_rel_on P R"
  obtains "partial_equivalence_rel_on P R" "reflexive_on P R"
  using assms unfolding equivalence_rel_on_def by auto

lemma equivalence_rel_on_in_field_if_partial_equivalence_rel:
  assumes "partial_equivalence_rel R"
  shows "equivalence_rel_on (in_field R) R"
  using assms
  by (intro equivalence_rel_onI reflexive_on_in_field_if_partial_equivalence_rel) auto

corollary partial_equivalence_rel_iff_equivalence_rel_on_in_field:
  "partial_equivalence_rel R \<longleftrightarrow> equivalence_rel_on (in_field R) R"
  using equivalence_rel_on_in_field_if_partial_equivalence_rel by auto

consts equivalence_rel :: "'a \<Rightarrow> bool"

overloading
  equivalence_rel \<equiv> "equivalence_rel :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "(equivalence_rel :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> equivalence_rel_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma equivalence_rel_eq_equivalence_rel_on:
  "(equivalence_rel :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = equivalence_rel_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding equivalence_rel_def ..

lemma equivalence_rel_eq_equivalence_rel_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: 'a \<Rightarrow> bool"
  shows "equivalence_rel :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> equivalence_rel_on P"
  using assms by (simp add: equivalence_rel_eq_equivalence_rel_on)

context
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

lemma equivalence_relI [intro]:
  assumes "partial_equivalence_rel R"
  and "reflexive R"
  shows "equivalence_rel R"
  using assms by (urule equivalence_rel_onI)

lemma equivalence_relE [elim]:
  assumes "equivalence_rel R"
  obtains "partial_equivalence_rel R" "reflexive R"
  using assms by (urule (e) equivalence_rel_onE)

lemma equivalence_rel_on_if_equivalence:
  fixes P :: "'a \<Rightarrow> bool"
  assumes "equivalence_rel R"
  shows "equivalence_rel_on P R"
  using assms by (elim equivalence_relE)
  (intro equivalence_rel_onI partial_equivalence_rel_on_if_partial_equivalence_rel
    reflexive_on_if_reflexive)

end

paragraph \<open>Instantiations\<close>

lemma equivalence_eq: "equivalence_rel (=)"
  using partial_equivalence_rel_eq reflexive_eq by (rule equivalence_relI)

lemma equivalence_top: "equivalence_rel (\<top> :: 'a \<Rightarrow> 'a \<Rightarrow> bool)"
  using partial_equivalence_rel_top reflexive_top by (rule equivalence_relI)

end
