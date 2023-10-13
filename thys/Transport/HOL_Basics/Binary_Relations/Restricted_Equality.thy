\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Restricted Equality\<close>
theory Restricted_Equality
  imports
    Binary_Relations_Order_Base
    Binary_Relation_Functions
    Equivalence_Relations
    Partial_Orders
begin

paragraph \<open>Summary\<close>
text \<open>Introduces the concept of restricted equalities.
An equality @{term "(=)"} can be restricted to only apply to a subset of its
elements. The restriction can be formulated, for example, by a predicate or a
set.\<close>

consts eq_restrict :: "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"

bundle eq_restrict_syntax
begin
syntax
  "_eq_restrict" :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" ("(_) =(\<^bsub>_\<^esub>) (_)" [51,51,51] 50)
notation eq_restrict ("'(=(\<^bsub>_\<^esub>)')")
end
bundle no_eq_restrict_syntax
begin
no_syntax
  "_eq_restrict" :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" ("(_) =(\<^bsub>_\<^esub>) (_)" [51,51,51] 50)
no_notation eq_restrict ("'(=(\<^bsub>_\<^esub>)')")
end
unbundle eq_restrict_syntax

translations
  "x =\<^bsub>P\<^esub> y" \<rightleftharpoons> "CONST eq_restrict P x y"

overloading
  eq_restrict_pred \<equiv> "eq_restrict :: ('a \<Rightarrow>  bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
begin
  definition "eq_restrict_pred (P :: 'a \<Rightarrow> bool) \<equiv> ((=) :: 'a \<Rightarrow> _)\<restriction>\<^bsub>P\<^esub>"
end

lemma eq_restrict_eq_eq_restrict_left: "((=\<^bsub>P :: 'a \<Rightarrow> bool\<^esub>) :: 'a \<Rightarrow> _) = (=)\<restriction>\<^bsub>P\<^esub>"
  unfolding eq_restrict_pred_def by simp

lemma eq_restrictI [intro]:
  assumes "x = y"
  and "P x"
  shows "x =\<^bsub>P\<^esub> y"
  unfolding eq_restrict_eq_eq_restrict_left using assms by auto

lemma eq_restrictE [elim]:
  assumes "x =\<^bsub>P\<^esub> y"
  obtains "P x" "y = x"
  using assms unfolding eq_restrict_eq_eq_restrict_left by auto

lemma eq_restrict_iff: "x =\<^bsub>P\<^esub> y \<longleftrightarrow> y = x \<and> P x" by auto

lemma eq_restrict_le_eq: "((=\<^bsub>P :: 'a \<Rightarrow> bool\<^esub>) :: 'a \<Rightarrow> _) \<le> (=)"
  by (intro le_relI) auto

lemma eq_restrict_top_eq_eq [simp]: "(=\<^bsub>\<top> :: 'a \<Rightarrow> bool\<^esub>) = ((=) :: 'a \<Rightarrow> _)"
  unfolding eq_restrict_eq_eq_restrict_left by simp

lemma in_dom_eq_restrict_eq [simp]: "in_dom (=\<^bsub>P\<^esub>) = P" by auto
lemma in_codom_eq_restrict_eq [simp]: "in_codom (=\<^bsub>P\<^esub>) = P" by auto
lemma in_field_eq_restrict_eq [simp]: "in_field (=\<^bsub>P\<^esub>) = P" by auto


paragraph \<open>Order Properties\<close>

context
  fixes P :: "'a \<Rightarrow> bool"
begin

context
begin
lemma reflexive_on_eq_restrict: "reflexive_on P ((=\<^bsub>P\<^esub>) :: 'a \<Rightarrow> _)" by auto
lemma transitive_eq_restrict: "transitive ((=\<^bsub>P\<^esub>) :: 'a \<Rightarrow> _)" by auto
lemma symmetric_eq_restrict: "symmetric ((=\<^bsub>P\<^esub>) :: 'a \<Rightarrow> _)" by auto
lemma antisymmetric_eq_restrict: "antisymmetric ((=\<^bsub>P\<^esub>) :: 'a \<Rightarrow> _)" by auto
end

context
begin
lemma preorder_on_eq_restrict: "preorder_on P ((=\<^bsub>P\<^esub>) :: 'a \<Rightarrow> _)"
  using reflexive_on_eq_restrict transitive_eq_restrict by auto
lemma partial_equivalence_rel_eq_restrict: "partial_equivalence_rel ((=\<^bsub>P\<^esub>) :: 'a \<Rightarrow> _)"
  using symmetric_eq_restrict transitive_eq_restrict by auto
end

lemma partial_order_on_eq_restrict: "partial_order_on P ((=\<^bsub>P\<^esub>) :: 'a \<Rightarrow> _)"
  using preorder_on_eq_restrict antisymmetric_eq_restrict by auto
lemma equivalence_rel_on_eq_restrict: "equivalence_rel_on P ((=\<^bsub>P\<^esub>) :: 'a \<Rightarrow> _)"
  using partial_equivalence_rel_eq_restrict reflexive_on_eq_restrict by blast
end


end
