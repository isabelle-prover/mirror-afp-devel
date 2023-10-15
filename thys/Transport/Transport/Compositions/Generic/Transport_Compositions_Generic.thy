\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Transport_Compositions_Generic
  imports
    Transport_Compositions_Generic_Galois_Equivalence
    Transport_Compositions_Generic_Galois_Relator
    Transport_Compositions_Generic_Order_Base
    Transport_Compositions_Generic_Order_Equivalence
begin

paragraph \<open>Summary of Main Results\<close>

subparagraph \<open>Closure of Order and Galois Concepts\<close>

context transport_comp
begin

interpretation flip : transport_comp R2 L2 r2 l2 R1 L1 r1 l1 .

lemma preorder_galois_connection_if_galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "preorder_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "preorder_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R2\<^esub>)) (\<le>\<^bsub>R2\<^esub>)"
  and "middle_compatible_codom"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro preorder_galois_connectionI)
  (auto elim!: t1.galois_equivalenceE t2.galois_equivalenceE
    intro!: galois_connection_left_right_if_galois_equivalenceI
      preorder_on_in_field_leftI flip.preorder_on_in_field_leftI
      mono_in_codom_left_rel_left1_if_in_codom_rel_comp_le
      flip.mono_in_codom_left_rel_left1_if_in_codom_rel_comp_le
      in_codom_eq_in_dom_if_reflexive_on_in_field)

theorem preorder_galois_connection_if_preorder_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "middle_compatible_codom"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro preorder_galois_connection_if_galois_equivalenceI)
  auto

lemma preorder_equivalence_if_galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "preorder_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "preorder_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R2\<^esub>)) (\<le>\<^bsub>R2\<^esub>)"
  and "middle_compatible_codom"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
proof -
  from assms have "((\<le>\<^bsub>L\<^esub>) \<stileturn>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
    by (intro preorder_galois_connection_if_galois_equivalenceI) auto
  with assms show ?thesis by (intro preorder_equivalence_if_galois_equivalenceI)
    (auto intro!: galois_equivalence_if_galois_equivalenceI
      preorder_galois_connection_if_galois_equivalenceI)
qed

theorem preorder_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "middle_compatible_codom"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro preorder_equivalence_if_galois_equivalenceI) auto

theorem partial_equivalence_rel_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "middle_compatible_codom"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro partial_equivalence_rel_equivalence_if_galois_equivalenceI
    galois_equivalence_if_galois_equivalenceI
    partial_equivalence_rel_leftI flip.partial_equivalence_rel_leftI
    in_codom_eq_in_dom_if_partial_equivalence_rel)
  auto


subparagraph \<open>Simplification of Galois relator\<close>

theorem left_Galois_eq_comp_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>R2\<^esub>) \<stileturn>\<^bsub>pre\<^esub> (\<le>\<^bsub>L2\<^esub>)) r2 l2"
  and "middle_compatible_codom"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>))"
  using assms by (intro left_Galois_eq_comp_left_Galois_if_galois_connection_if_galois_equivalenceI)
  auto

text \<open>For theorems with weaker assumptions, see
@{thm "left_Galois_eq_comp_left_GaloisI'"
"left_Galois_eq_comp_left_Galois_if_galois_connection_if_galois_equivalenceI"}.\<close>


subparagraph \<open>Simplification of Compatibility Assumption\<close>

text \<open>See @{theory "Transport.Transport_Compositions_Generic_Base"}.\<close>

end


end