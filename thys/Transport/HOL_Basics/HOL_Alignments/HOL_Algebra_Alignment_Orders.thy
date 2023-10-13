\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Alignment With Definitions from HOL-Algebra\<close>
theory HOL_Algebra_Alignment_Orders
  imports
    "HOL-Algebra.Order"
    HOL_Alignment_Orders
begin

named_theorems HOL_Algebra_order_alignment

context equivalence
begin

lemma reflexive_on_carrier [HOL_Algebra_order_alignment]:
  "reflexive_on (carrier S) (.=)"
  by blast

lemma transitive_on_carrier [HOL_Algebra_order_alignment]:
  "transitive_on (carrier S) (.=)"
  using trans by blast

lemma preorder_on_carrier [HOL_Algebra_order_alignment]:
  "preorder_on (carrier S) (.=)"
  using reflexive_on_carrier transitive_on_carrier by blast

lemma symmetric_on_carrier [HOL_Algebra_order_alignment]:
  "symmetric_on (carrier S) (.=)"
  using sym by blast

lemma partial_equivalence_rel_on_carrier [HOL_Algebra_order_alignment]:
  "partial_equivalence_rel_on (carrier S) (.=)"
  using transitive_on_carrier symmetric_on_carrier by blast

lemma equivalence_rel_on_carrier [HOL_Algebra_order_alignment]:
  "equivalence_rel_on (carrier S) (.=)"
  using reflexive_on_carrier partial_equivalence_rel_on_carrier by blast

end

lemma equivalence_iff_equivalence_rel_on_carrier [HOL_Algebra_order_alignment]:
  "equivalence S \<longleftrightarrow> equivalence_rel_on (carrier S) (.=\<^bsub>S\<^esub>)"
  using equivalence.equivalence_rel_on_carrier
  by (blast dest: intro!: equivalence.intro dest: symmetric_onD transitive_onD)

context partial_order
begin

lemma reflexive_on_carrier [HOL_Algebra_order_alignment]:
  "reflexive_on (carrier L) (\<sqsubseteq>)"
  by blast

lemma transitive_on_carrier [HOL_Algebra_order_alignment]:
  "transitive_on (carrier L) (\<sqsubseteq>)"
  using le_trans by blast

lemma preorder_on_carrier [HOL_Algebra_order_alignment]:
  "preorder_on (carrier L) (\<sqsubseteq>)"
  using reflexive_on_carrier transitive_on_carrier by blast

lemma antisymmetric_on_carrier [HOL_Algebra_order_alignment]:
  "antisymmetric_on (carrier L) (\<sqsubseteq>)"
  by blast

lemma partial_order_on_carrier [HOL_Algebra_order_alignment]:
  "partial_order_on (carrier L) (\<sqsubseteq>)"
  using preorder_on_carrier antisymmetric_on_carrier by blast

end


end