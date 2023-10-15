\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Basic Order Properties\<close>
theory Transport_Natural_Functors_Order_Base
  imports
    Transport_Natural_Functors_Base
begin

lemma reflexive_on_in_field_FrelI:
  assumes "reflexive_on (in_field R1) R1"
  and "reflexive_on (in_field R2) R2"
  and "reflexive_on (in_field R3) R3"
  defines "R \<equiv> Frel R1 R2 R3"
  shows "reflexive_on (in_field R) R"
  apply (subst reflexive_on_iff_eq_restrict_left_le)
  apply (subst Frel_eq[symmetric])
  apply (unfold R_def)
  apply (subst in_field_Frel_eq_Fpred_in_in_field)
  apply (subst restrict_left_sup_eq)
  apply (subst Frel_restrict_left_Fpred_eq_Frel_restrict_left)+
  apply (rule le_supI;
    rule Frel_mono;
    subst reflexive_on_iff_eq_restrict_left_le[symmetric],
    rule reflexive_on_if_le_pred_if_reflexive_on,
    rule assms,
    rule le_predI[OF in_field_if_in_dom]
      le_predI[OF in_field_if_in_codom],
    assumption)
  done

lemma transitive_FrelI:
  assumes "transitive R1"
  and "transitive R2"
  and "transitive R3"
  shows "transitive (Frel R1 R2 R3)"
  apply (subst transitive_iff_rel_comp_le_self)
  apply (subst Frel_comp_eq_Frel_rel_comp)
  apply (rule Frel_mono;
    subst transitive_iff_rel_comp_le_self[symmetric],
    rule assms)
  done

lemma preorder_on_in_field_FrelI:
  assumes "preorder_on (in_field R1) R1"
  and "preorder_on (in_field R2) R2"
  and "preorder_on (in_field R3) R3"
  defines "R \<equiv> Frel R1 R2 R3"
  shows "preorder_on (in_field R) R"
  apply (unfold R_def)
  apply (insert assms)
  apply (elim preorder_on_in_fieldE)
  apply (rule preorder_onI)
  apply (rule reflexive_on_in_field_FrelI; assumption)
  apply (subst transitive_on_in_field_iff_transitive)
  apply (rule transitive_FrelI; assumption)
  done

lemma symmetric_FrelI:
  assumes "symmetric R1"
  and "symmetric R2"
  and "symmetric R3"
  shows "symmetric (Frel R1 R2 R3)"
  apply (subst symmetric_iff_rel_inv_eq_self)
  apply (subst Frel_rel_inv_eq_rel_inv_Frel[symmetric])
  apply (subst rel_inv_eq_self_if_symmetric, fact)+
  apply (rule refl)
  done

lemma partial_equivalence_rel_FrelI:
  assumes "partial_equivalence_rel R1"
  and "partial_equivalence_rel R2"
  and "partial_equivalence_rel R3"
  shows "partial_equivalence_rel (Frel R1 R2 R3)"
  apply (insert assms)
  apply (elim partial_equivalence_relE preorder_on_in_fieldE)
  apply (rule partial_equivalence_relI;
    rule transitive_FrelI symmetric_FrelI;
    assumption)
  done

context transport_natural_functor
begin

lemmas reflexive_on_in_field_leftI = reflexive_on_in_field_FrelI
  [of L1 L2 L3, folded transport_defs]

lemmas transitive_leftI = transitive_FrelI[of L1 L2 L3, folded transport_defs]

lemmas preorder_on_in_field_leftI = preorder_on_in_field_FrelI
  [of L1 L2 L3, folded transport_defs]

lemmas symmetricI = symmetric_FrelI[of L1 L2 L3, folded transport_defs]

lemmas partial_equivalence_rel_leftI = partial_equivalence_rel_FrelI
  [of L1 L2 L3, folded transport_defs]

end


end