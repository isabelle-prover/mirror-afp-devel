\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Galois Relator\<close>
theory Transport_Compositions_Generic_Galois_Relator
  imports
    Transport_Compositions_Generic_Base
begin

context transport_comp
begin

interpretation flip : transport_comp R2 L2 r2 l2 R1 L1 r1 l1
  rewrites "flip.t2.unit \<equiv> \<epsilon>\<^sub>1"
  by (simp only: t1.flip_unit_eq_counit)

lemma left_Galois_le_comp_left_GaloisI:
  assumes mono_r1: "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and galois_prop1: "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and preorder_R1: "preorder_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and rel_comp_le: "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  and mono_in_codom_r2: "([in_codom (\<le>\<^bsub>R\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>R1\<^esub>)) r2"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) \<le> ((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>))"
proof (rule le_relI)
  fix x z assume "x \<^bsub>L\<^esub>\<lessapprox> z"
  then have "in_codom (\<le>\<^bsub>R\<^esub>) z" "x \<le>\<^bsub>L\<^esub> r z" by auto
  with galois_prop1 obtain y y' where "in_dom (\<le>\<^bsub>L1\<^esub>) x" "l1 x \<le>\<^bsub>R1\<^esub> y" "y \<le>\<^bsub>L2\<^esub> y'" "y' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 (r2 z)"
    by (auto elim!: left_relE)
  moreover  have "\<epsilon>\<^sub>1 (r2 z) \<le>\<^bsub>R1\<^esub> r2 z"
  proof -
    from mono_in_codom_r2 \<open>in_codom (\<le>\<^bsub>R\<^esub>) z\<close> have "in_codom (\<le>\<^bsub>R1\<^esub>) (r2 z)" by blast
    with mono_r1 galois_prop1 preorder_R1 show ?thesis by (blast intro!:
      t1.counit_rel_if_reflexive_on_if_half_galois_prop_left_if_mono_wrt_rel)
  qed
  ultimately have "y' \<le>\<^bsub>R1\<^esub> r2 z" using preorder_R1 by blast
  with \<open>l1 x \<le>\<^bsub>R1\<^esub> y\<close> \<open>y \<le>\<^bsub>L2\<^esub> y'\<close> have "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) (l1 x) (r2 z)"
    by blast
  with rel_comp_le obtain y'' where "l1 x \<le>\<^bsub>R1\<^esub> y''" "y'' \<le>\<^bsub>L2\<^esub> r2 z" by blast
  with galois_prop1 \<open>in_dom (\<le>\<^bsub>L1\<^esub>) x\<close>  have "x \<^bsub>L1\<^esub>\<lessapprox> y''"
    by (intro t1.left_Galois_if_Galois_right_if_half_galois_prop_right t1.left_GaloisI)
    auto
  moreover from \<open>in_codom (\<le>\<^bsub>R\<^esub>) z\<close> \<open>y'' \<le>\<^bsub>L2\<^esub> r2 z\<close> have "y'' \<^bsub>L2\<^esub>\<lessapprox> z"
    by (intro t2.left_GaloisI) auto
  ultimately show "((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>)) x z" by blast
qed

lemma comp_left_Galois_le_left_GaloisI:
  assumes mono_r1: "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and half_galois_prop_left1: "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and half_galois_prop_right1: "((\<le>\<^bsub>R1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>L1\<^esub>)) r1 l1"
  and refl_R1: "reflexive_on (in_codom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and mono_l2: "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and refl_L2: "reflexive_on (in_dom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and in_codom_rel_comp_le: "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  shows "((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>)) \<le> (\<^bsub>L\<^esub>\<lessapprox>)"
proof (intro le_relI left_GaloisI)
  fix x z assume "((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>)) x z"
  from \<open>((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>)) x z\<close> obtain y where "x \<^bsub>L1\<^esub>\<lessapprox> y" "y \<^bsub>L2\<^esub>\<lessapprox> z" by blast
  with half_galois_prop_left1 have "l1 x \<le>\<^bsub>R1\<^esub> y" "y \<le>\<^bsub>L2\<^esub> r2 z" by auto
  with refl_R1 refl_L2 have "y \<le>\<^bsub>R1\<^esub> y" "y \<le>\<^bsub>L2\<^esub> y" by auto
  show "in_codom (\<le>\<^bsub>R\<^esub>) z"
  proof (intro in_codomI flip.left_relI)
    from mono_l2 \<open>y \<le>\<^bsub>L2\<^esub> y\<close> show "l2 y \<^bsub>R2\<^esub>\<lessapprox> y" by blast
    show "y \<le>\<^bsub>R1\<^esub> y" "y \<^bsub>L2\<^esub>\<lessapprox> z" by fact+
  qed
  show "x \<le>\<^bsub>L\<^esub> r z"
  proof (intro left_relI)
    show "x \<^bsub>L1\<^esub>\<lessapprox> y" "y \<le>\<^bsub>L2\<^esub> r2 z" by fact+
    show "r2 z \<^bsub>R1\<^esub>\<lessapprox> r z"
    proof (intro flip.t2.left_GaloisI)
      from \<open>y \<le>\<^bsub>L2\<^esub> y\<close> \<open>y \<le>\<^bsub>R1\<^esub> y\<close> \<open>y \<le>\<^bsub>L2\<^esub> r2 z\<close> have "((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) y (r2 z)"
        by blast
      with in_codom_rel_comp_le have "in_codom (\<le>\<^bsub>R1\<^esub>) (r2 z)" by blast
      with refl_R1 have "r2 z \<le>\<^bsub>R1\<^esub> r2 z" by blast
      with mono_r1 show "in_codom (\<le>\<^bsub>L1\<^esub>) (r z)" by auto
      with \<open>r2 z \<le>\<^bsub>R1\<^esub> r2 z\<close>  half_galois_prop_right1 mono_r1
        show "r2 z \<le>\<^bsub>R1\<^esub> l1 (r z)" by (auto intro:
        flip.t2.rel_unit_if_left_rel_if_half_galois_prop_right_if_mono_wrt_rel)
    qed
  qed
qed

corollary left_Galois_eq_comp_left_GaloisI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>R1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>L1\<^esub>)) r1 l1"
  and "preorder_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "reflexive_on (in_dom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  and "([in_codom (\<le>\<^bsub>R\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>R1\<^esub>)) r2"
  and "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>))"
  using assms
  by (intro antisym left_Galois_le_comp_left_GaloisI comp_left_Galois_le_left_GaloisI)
  (auto elim!: preorder_on_in_fieldE
    intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_codom)

corollary left_Galois_eq_comp_left_GaloisI':
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>R1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>L1\<^esub>)) r1 l1"
  and "preorder_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "((\<le>\<^bsub>R2\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L2\<^esub>)) r2 l2"
  and "reflexive_on (in_dom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  and "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>))"
  using assms by (intro left_Galois_eq_comp_left_GaloisI
    flip.mono_in_codom_left_rel_left1_if_in_codom_rel_comp_le)
  auto

theorem left_Galois_eq_comp_left_Galois_if_galois_connection_if_galois_equivalenceI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "preorder_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<stileturn> (\<le>\<^bsub>L2\<^esub>)) r2 l2"
  and "reflexive_on (in_dom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  and "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>))"
  using assms by (intro left_Galois_eq_comp_left_GaloisI')
  (auto elim!: t1.galois_equivalenceE)

corollary left_Galois_eq_comp_left_Galois_if_galois_connection_if_galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "preorder_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<stileturn> (\<le>\<^bsub>L2\<^esub>)) r2 l2"
  and "reflexive_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "in_codom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_codom (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  and "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>))"
  using assms
  by (intro left_Galois_eq_comp_left_Galois_if_galois_connection_if_galois_equivalenceI'
    flip.left2_right1_left2_le_left2_right1_if_right1_left2_right1_le_left2_right1)
  auto

corollary left_Galois_eq_comp_left_Galois_if_preorder_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>R2\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>L2\<^esub>)) r2 l2"
  and "in_codom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_codom (\<le>\<^bsub>L2\<^esub>)"
  and "(\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<le> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)"
  and "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>))"
  using assms by (intro
    left_Galois_eq_comp_left_Galois_if_galois_connection_if_galois_equivalenceI)
  auto

end


end