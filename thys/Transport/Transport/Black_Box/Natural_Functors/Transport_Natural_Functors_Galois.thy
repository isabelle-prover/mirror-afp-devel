\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Galois Concepts\<close>
theory Transport_Natural_Functors_Galois
  imports
    Transport_Natural_Functors_Base
begin

context transport_natural_functor
begin

lemma half_galois_prop_leftI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "((\<le>\<^bsub>L3\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R3\<^esub>)) l3 r3"
  shows "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  apply (rule half_galois_prop_leftI)
  apply (erule left_GaloisE)
  apply (unfold left_rel_eq_Frel right_rel_eq_Frel left_eq_Fmap right_eq_Fmap)
  apply (subst (asm) in_codom_Frel_eq_Fpred_in_codom)
  apply (erule FpredE)
  apply (unfold Frel_Fmap_eqs)
  apply (rule Frel_mono_strong,
    assumption;
    rule t1.half_galois_prop_leftD t2.half_galois_prop_leftD t3.half_galois_prop_leftD,
    rule assms,
    rule t1.left_GaloisI t2.left_GaloisI t3.left_GaloisI;
    assumption)
  done

interpretation flip_inv : transport_natural_functor "(\<ge>\<^bsub>R1\<^esub>)" "(\<ge>\<^bsub>L1\<^esub>)" r1 l1
  "(\<ge>\<^bsub>R2\<^esub>)" "(\<ge>\<^bsub>L2\<^esub>)" r2 l2 "(\<ge>\<^bsub>R3\<^esub>)" "(\<ge>\<^bsub>L3\<^esub>)" r3 l3
  rewrites "flip_inv.R \<equiv> (\<ge>\<^bsub>L\<^esub>)"
  and "flip_inv.L \<equiv> (\<ge>\<^bsub>R\<^esub>)"
  and "\<And>R S f g. (R\<inverse> \<^sub>h\<unlhd> S\<inverse>) f g \<equiv> (S \<unlhd>\<^sub>h R) g f"
  by (simp_all only: flip_inv_left_eq_ge_right flip_inv_right_eq_ge_left
    galois_prop.half_galois_prop_left_rel_inv_iff_half_galois_prop_right)

lemma half_galois_prop_rightI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "((\<le>\<^bsub>L3\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R3\<^esub>)) l3 r3"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro flip_inv.half_galois_prop_leftI)

corollary galois_propI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<unlhd> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "((\<le>\<^bsub>L3\<^esub>) \<unlhd> (\<le>\<^bsub>R3\<^esub>)) l3 r3"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (elim galois_prop.galois_propE)
  (intro galois_propI half_galois_prop_leftI half_galois_prop_rightI)

interpretation flip :
  transport_natural_functor R1 L1 r1 l1 R2 L2 r2 l2 R3 L3 r3 l3 .

corollary galois_connectionI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<stileturn> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "((\<le>\<^bsub>L3\<^esub>) \<stileturn> (\<le>\<^bsub>R3\<^esub>)) l3 r3"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (elim galois.galois_connectionE) (intro
    galois_connectionI galois_propI mono_wrt_rel_leftI flip.mono_wrt_rel_leftI)

corollary galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "((\<le>\<^bsub>L3\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R3\<^esub>)) l3 r3"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (elim galois.galois_equivalenceE flip.t1.galois_connectionE
    flip.t2.galois_connectionE flip.t3.galois_connectionE)
  (intro galois_equivalenceI galois_connectionI flip.galois_propI)

end


end