\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Galois Equivalence\<close>
theory Transport_Compositions_Generic_Galois_Equivalence
  imports
    Transport_Compositions_Generic_Galois_Connection
begin

context transport_comp
begin

interpretation flip : transport_comp R2 L2 r2 l2 R1 L1 r1 l1
  rewrites "flip.t2.unit = \<epsilon>\<^sub>1" and "flip.t1.counit \<equiv> \<eta>\<^sub>2" and "flip.t1.unit \<equiv> \<epsilon>\<^sub>2"
  by (simp_all only: order_functors.flip_unit_eq_counit)

lemma galois_equivalenceI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "rel_equivalence_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "((\<le>\<^bsub>R2\<^esub>) \<unlhd> (\<le>\<^bsub>L2\<^esub>)) r2 l2"
  and "rel_equivalence_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "middle_compatible_codom"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_equivalenceI galois_connection_left_rightI
    flip.galois_prop_left_rightI)
  (auto intro!: preorder_on_in_field_if_transitive_if_rel_equivalence_on
    intro: rel_equivalence_on_if_le_pred_if_rel_equivalence_on
      inflationary_on_if_le_pred_if_inflationary_on
      in_field_if_in_dom in_field_if_in_codom)

lemma galois_equivalenceI':
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>R1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>L1\<^esub>)) r1 l1"
  and "inflationary_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and "rel_equivalence_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "((\<le>\<^bsub>L2\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "((\<le>\<^bsub>R2\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L2\<^esub>)) r2 l2"
  and "rel_equivalence_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and "inflationary_on (in_dom (\<le>\<^bsub>R2\<^esub>)) (\<le>\<^bsub>R2\<^esub>) \<epsilon>\<^sub>2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "middle_compatible_dom"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois.galois_equivalenceI galois_connection_left_rightI'
    flip.galois_prop_left_rightI')
  (auto elim!: rel_equivalence_onE
    intro!: preorder_on_in_field_if_transitive_if_rel_equivalence_on
    intro: inflationary_on_if_le_pred_if_inflationary_on
      in_field_if_in_dom)

corollary galois_equivalence_if_galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "preorder_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "preorder_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "middle_compatible_codom"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_equivalenceI)
  (auto intro!: t2.rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence
      flip.t2.rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence
    intro: reflexive_on_if_le_pred_if_reflexive_on
      in_field_if_in_dom in_field_if_in_codom)

corollary galois_equivalence_if_order_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "middle_compatible_codom"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_equivalenceI')
  (auto elim!: rel_equivalence_onE
    intro!: t1.half_galois_prop_left_left_right_if_transitive_if_deflationary_on_if_mono_wrt_rel
      flip.t1.half_galois_prop_left_left_right_if_transitive_if_deflationary_on_if_mono_wrt_rel
      t2.half_galois_prop_right_left_right_if_transitive_if_inflationary_on_if_mono_wrt_rel
      flip.t2.half_galois_prop_right_left_right_if_transitive_if_inflationary_on_if_mono_wrt_rel
      rel_comp_comp_le_assms_if_in_codom_rel_comp_comp_leI
      preorder_on_in_field_if_transitive_if_rel_equivalence_on
    intro: deflationary_on_if_le_pred_if_deflationary_on
      inflationary_on_if_le_pred_if_inflationary_on
      in_field_if_in_dom in_field_if_in_codom)

end


end