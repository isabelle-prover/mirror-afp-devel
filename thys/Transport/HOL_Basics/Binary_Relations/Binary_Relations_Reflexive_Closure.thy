\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Reflexive Closure\<close>
theory Binary_Relations_Reflexive_Closure
  imports
    Binary_Relations_Reflexive
    Restricted_Equality
begin

consts refl_closure_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"

overloading
  refl_closure_on_pred \<equiv> "refl_closure_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"
begin
  definition "refl_closure_on_pred (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<equiv> R \<squnion> (=\<^bsub>P\<^esub>)"
end

lemma refl_closure_on_if_pred [intro]:
  assumes "P x"
  shows "refl_closure_on P R x x"
  using assms unfolding refl_closure_on_pred_def by auto

lemma refl_closure_on_if_rel [intro]:
  assumes "(R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) x y"
  shows "refl_closure_on (P :: 'a \<Rightarrow> bool) R x y"
  using assms unfolding refl_closure_on_pred_def by auto

corollary le_refl_closure_on_self: "(R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<le> refl_closure_on (P :: 'a \<Rightarrow> bool) R"
  by blast

lemma refl_closure_onE [elim]:
  assumes "refl_closure_on P R x y"
  obtains "P x" "x = y" | "R x y"
  using assms unfolding refl_closure_on_pred_def by auto

lemma reflexive_on_refl_closure_on:
  "reflexive_on (P :: 'a \<Rightarrow> bool) (refl_closure_on P (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool))"
  by fastforce


definition "refl_closure_field R \<equiv> refl_closure_on (in_field R) R"

open_bundle refl_closure_field_syntax
begin
notation refl_closure_field (\<open>(_\<^sup>+)\<close> [1000])
end

lemma refl_closure_fieldI [intro]:
  assumes "refl_closure_on (in_field R) R x y"
  shows "R\<^sup>+ x y"
  using assms unfolding refl_closure_field_def by auto

lemma refl_closure_fieldD [dest]:
  assumes "R\<^sup>+ x y"
  shows "refl_closure_on (in_field R) R x y"
  using assms unfolding refl_closure_field_def by auto

lemma refl_closure_field_eq_refl_closure_on_in_field: "R\<^sup>+ = refl_closure_on (in_field R) R"
  by auto


end