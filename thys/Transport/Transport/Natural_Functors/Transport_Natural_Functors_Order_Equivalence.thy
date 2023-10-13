\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Order Equivalence\<close>
theory Transport_Natural_Functors_Order_Equivalence
  imports
    Transport_Natural_Functors_Base
begin

lemma inflationary_on_in_dom_FrelI:
  assumes "inflationary_on (in_dom R1) R1 f1"
  and "inflationary_on (in_dom R2) R2 f2"
  and "inflationary_on (in_dom R3) R3 f3"
  defines "R \<equiv> Frel R1 R2 R3"
  shows "inflationary_on (in_dom R) R (Fmap f1 f2 f3)"
  apply (unfold R_def)
  apply (rule inflationary_onI)
  apply (subst (asm) in_dom_Frel_eq_Fpred_in_dom)
  apply (erule FpredE)
  apply (subst Frel_Fmap_eq2)
  apply (rule Frel_refl_strong)
    apply (rule inflationary_onD[where ?R=R1] inflationary_onD[where ?R=R2]
        inflationary_onD[where ?R=R3],
      rule assms,
      assumption+)+
  done

lemma inflationary_on_in_codom_FrelI:
  assumes "inflationary_on (in_codom R1) R1 f1"
  and "inflationary_on (in_codom R2) R2 f2"
  and "inflationary_on (in_codom R3) R3 f3"
  defines "R \<equiv> Frel R1 R2 R3"
  shows "inflationary_on (in_codom R) R (Fmap f1 f2 f3)"
  apply (unfold R_def)
  apply (rule inflationary_onI)
  apply (subst (asm) in_codom_Frel_eq_Fpred_in_codom)
  apply (erule FpredE)
  apply (subst Frel_Fmap_eq2)
  apply (rule Frel_refl_strong)
    apply (rule inflationary_onD[where ?R=R1] inflationary_onD[where ?R=R2]
        inflationary_onD[where ?R=R3],
      rule assms,
      assumption+)+
  done

lemma inflationary_on_in_field_FrelI:
  assumes "inflationary_on (in_field R1) R1 f1"
  and "inflationary_on (in_field R2) R2 f2"
  and "inflationary_on (in_field R3) R3 f3"
  defines "R \<equiv> Frel R1 R2 R3"
  shows "inflationary_on (in_field R) R (Fmap f1 f2 f3)"
  apply (unfold R_def)
  apply (subst in_field_eq_in_dom_sup_in_codom)
  apply (subst inflationary_on_sup_eq)
  apply (unfold inf_apply)
  apply (subst inf_bool_def)
  apply (rule conjI;
    rule inflationary_on_in_dom_FrelI inflationary_on_in_codom_FrelI;
    rule inflationary_on_if_le_pred_if_inflationary_on,
    rule assms,
    rule le_predI,
    rule in_field_if_in_dom in_field_if_in_codom,
    assumption)
  done

lemma deflationary_on_in_dom_FrelI:
  assumes "deflationary_on (in_dom R1) R1 f1"
  and "deflationary_on (in_dom R2) R2 f2"
  and "deflationary_on (in_dom R3) R3 f3"
  defines "R \<equiv> Frel R1 R2 R3"
  shows "deflationary_on (in_dom R) R (Fmap f1 f2 f3)"
  apply (unfold R_def)
  apply (subst deflationary_on_eq_inflationary_on_rel_inv)
  apply (subst in_codom_rel_inv_eq_in_dom[symmetric])
  apply (unfold Frel_rel_inv_eq_rel_inv_Frel[symmetric])
  apply (rule inflationary_on_in_codom_FrelI;
    subst deflationary_on_eq_inflationary_on_rel_inv[symmetric],
    subst in_codom_rel_inv_eq_in_dom,
    rule assms)
  done

lemma deflationary_on_in_codom_FrelI:
  assumes "deflationary_on (in_codom R1) R1 f1"
  and "deflationary_on (in_codom R2) R2 f2"
  and "deflationary_on (in_codom R3) R3 f3"
  defines "R \<equiv> Frel R1 R2 R3"
  shows "deflationary_on (in_codom R) R (Fmap f1 f2 f3)"
  apply (unfold R_def)
  apply (subst deflationary_on_eq_inflationary_on_rel_inv)
  apply (subst in_dom_rel_inv_eq_in_codom[symmetric])
  apply (unfold Frel_rel_inv_eq_rel_inv_Frel[symmetric])
  apply (rule inflationary_on_in_dom_FrelI;
    subst deflationary_on_eq_inflationary_on_rel_inv[symmetric],
    subst in_dom_rel_inv_eq_in_codom,
    rule assms)
  done

lemma deflationary_on_in_field_FrelI:
  assumes "deflationary_on (in_field R1) R1 f1"
  and "deflationary_on (in_field R2) R2 f2"
  and "deflationary_on (in_field R3) R3 f3"
  defines "R \<equiv> Frel R1 R2 R3"
  shows "deflationary_on (in_field R) R (Fmap f1 f2 f3)"
  apply (unfold R_def)
  apply (subst deflationary_on_eq_inflationary_on_rel_inv)
  apply (subst in_field_rel_inv_eq[symmetric])
  apply (unfold Frel_rel_inv_eq_rel_inv_Frel[symmetric])
  apply (rule inflationary_on_in_field_FrelI;
    subst deflationary_on_eq_inflationary_on_rel_inv[symmetric],
    subst in_field_rel_inv_eq,
    rule assms)
  done

lemma rel_equivalence_on_in_field_FrelI:
  assumes "rel_equivalence_on (in_field R1) R1 f1"
  and "rel_equivalence_on (in_field R2) R2 f2"
  and "rel_equivalence_on (in_field R3) R3 f3"
  defines "R \<equiv> Frel R1 R2 R3"
  shows "rel_equivalence_on (in_field R) R (Fmap f1 f2 f3)"
  apply (unfold R_def)
  apply (subst rel_equivalence_on_eq)
  apply (unfold inf_apply)
  apply (subst inf_bool_def)
  apply (insert assms)
  apply (elim rel_equivalence_onE)
  apply (rule conjI;
    rule inflationary_on_in_field_FrelI deflationary_on_in_field_FrelI;
    assumption)
  done

context transport_natural_functor
begin

lemmas inflationary_on_in_field_unitI = inflationary_on_in_field_FrelI
  [of L1 "\<eta>\<^sub>1" L2 "\<eta>\<^sub>2" L3 "\<eta>\<^sub>3", folded transport_defs unit_eq_Fmap]

lemmas deflationary_on_in_field_unitI = deflationary_on_in_field_FrelI
  [of L1 "\<eta>\<^sub>1" L2 "\<eta>\<^sub>2" L3 "\<eta>\<^sub>3", folded transport_defs unit_eq_Fmap]

lemmas rel_equivalence_on_in_field_unitI = rel_equivalence_on_in_field_FrelI
  [of L1 "\<eta>\<^sub>1" L2 "\<eta>\<^sub>2" L3 "\<eta>\<^sub>3", folded transport_defs unit_eq_Fmap]

interpretation flip :
  transport_natural_functor R1 L1 r1 l1 R2 L2 r2 l2 R3 L3 r3 l3
  rewrites "flip.unit \<equiv> \<epsilon>" and "flip.t1.unit \<equiv> \<epsilon>\<^sub>1"
  and "flip.t2.unit \<equiv> \<epsilon>\<^sub>2" and "flip.t3.unit \<equiv> \<epsilon>\<^sub>3"
  by (simp_all only: order_functors.flip_counit_eq_unit)

lemma order_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "((\<le>\<^bsub>L3\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R3\<^esub>)) l3 r3"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  apply (insert assms)
  apply (elim order_functors.order_equivalenceE)
  apply (rule order_equivalenceI;
    rule mono_wrt_rel_leftI
      flip.mono_wrt_rel_leftI
      rel_equivalence_on_in_field_unitI
      flip.rel_equivalence_on_in_field_unitI;
    assumption)
  done

end


end