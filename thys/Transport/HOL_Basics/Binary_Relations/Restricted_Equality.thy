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
text \<open>Introduces notations and theorems for restricted equalities.
An equality @{term "(=)"} can be restricted to only apply to a subset of its
elements. The restriction can be formulated, for example, by a predicate or a set.\<close>

bundle eq_rel_restrict_syntax
begin
syntax
  "_eq_restrict_infix" :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool" ("(_) =(\<^bsub>_\<^esub>) (_)" [51,51,51] 50)
  "_eq_restrict" :: "'b \<Rightarrow> 'a \<Rightarrow> bool" ("'(=(\<^bsub>_\<^esub>)')")
end
bundle no_eq_rel_restrict_syntax
begin
no_syntax
  "_eq_restrict_infix" :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool" ("(_) =(\<^bsub>_\<^esub>) (_)" [51,51,51] 50)
  "_eq_restrict" :: "'b \<Rightarrow> 'a \<Rightarrow> bool" ("'(=(\<^bsub>_\<^esub>)')")
end
unbundle eq_rel_restrict_syntax

translations
  "(=\<^bsub>P\<^esub>)" \<rightleftharpoons> "CONST rel_restrict_left (=) P"
  "x =\<^bsub>P\<^esub> y" \<rightleftharpoons> "CONST rel_restrict_left (=) P x y"

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
