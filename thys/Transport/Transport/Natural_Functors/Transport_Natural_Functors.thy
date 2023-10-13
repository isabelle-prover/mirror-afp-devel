\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Transport_Natural_Functors
  imports
    Transport_Natural_Functors_Galois
    Transport_Natural_Functors_Galois_Relator
    Transport_Natural_Functors_Order_Base
    Transport_Natural_Functors_Order_Equivalence
begin

paragraph \<open>Summary\<close>
text \<open>Summary of results for a fixed natural functor with 3 parameters. All
apply-style proofs are written such that they also apply to functors with other
arities. An automatic derivation of these results for all natural functors needs
to be implemented in the BNF package. This is future work.\<close>

context transport_natural_functor
begin

interpretation flip :
  transport_natural_functor R1 L1 r1 l1 R2 L2 r2 l2 R3 L3 r3 l3 .

theorem preorder_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "((\<le>\<^bsub>L3\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R3\<^esub>)) l3 r3"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  apply (insert assms)
  apply (elim transport.preorder_equivalence_galois_equivalenceE)
  apply (intro preorder_equivalence_if_galois_equivalenceI
    galois_equivalenceI
    preorder_on_in_field_leftI flip.preorder_on_in_field_leftI)
  apply assumption+
  done

theorem partial_equivalence_rel_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "((\<le>\<^bsub>L3\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R3\<^esub>)) l3 r3"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  apply (insert assms)
  apply (elim transport.partial_equivalence_rel_equivalenceE
    transport.preorder_equivalence_galois_equivalenceE
    preorder_on_in_fieldE)
  apply (intro partial_equivalence_rel_equivalence_if_galois_equivalenceI
    galois_equivalenceI
    partial_equivalence_rel_leftI flip.partial_equivalence_rel_leftI
    partial_equivalence_relI)
  apply assumption+
  done

text \<open>For the simplification of the Galois relator see
@{thm "left_Galois_eq_Frel_left_Galois"}.\<close>

end


end