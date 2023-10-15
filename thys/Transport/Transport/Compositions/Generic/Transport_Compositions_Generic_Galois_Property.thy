\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Galois Property\<close>
theory Transport_Compositions_Generic_Galois_Property
  imports
    Transport_Compositions_Generic_Base
begin

context transport_comp
begin

interpretation flip : transport_comp R2 L2 r2 l2 R1 L1 r1 l1
  rewrites "flip.t2.unit = \<epsilon>\<^sub>1" and "flip.t1.counit \<equiv> \<eta>\<^sub>2"
  by (simp_all only: t1.flip_unit_eq_counit t2.flip_counit_eq_unit)

lemma half_galois_prop_left_left_rightI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and deflationary_counit1: "deflationary_on (in_codom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and trans_R1: "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "reflexive_on (in_codom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  and "in_codom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_codom (\<le>\<^bsub>L2\<^esub>)"
  and mono_in_codom_r2: "([in_codom (\<le>\<^bsub>R\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>R1\<^esub>)) r2"
  shows "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
proof (rule half_galois_prop_leftI)
  fix x z assume "x \<^bsub>L\<^esub>\<lessapprox> z"
  then show "l x \<le>\<^bsub>R\<^esub> z"
  proof (intro right_rel_if_left_relI)
    from \<open>x \<^bsub>L\<^esub>\<lessapprox> z\<close> show "in_codom (\<le>\<^bsub>R2\<^esub>) z" by blast
    fix y assume "y \<le>\<^bsub>R1\<^esub> l1 (r z)"
    moreover have "l1 (r z) \<le>\<^bsub>R1\<^esub> r2 z"
    proof -
      from mono_in_codom_r2 \<open>x \<^bsub>L\<^esub>\<lessapprox> z\<close> have "in_codom (\<le>\<^bsub>R1\<^esub>) (r2 z)" by blast
      with deflationary_counit1 show "l1 (r z) \<le>\<^bsub>R1\<^esub> r2 z" by auto
    qed
    ultimately show "y \<le>\<^bsub>R1\<^esub> r2 z" using trans_R1 by blast
  next
    fix y assume "l1 x \<le>\<^bsub>L2\<^esub> y"
    with \<open>((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2\<close> show "l x \<le>\<^bsub>R2\<^esub> l2 y" by auto
  qed (insert assms, auto)
qed

lemma half_galois_prop_left_left_rightI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and deflationary_counit1: "deflationary_on (in_codom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and trans_R1: "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and refl_L2: "reflexive_on (in_dom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  and "in_dom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_dom (\<le>\<^bsub>L2\<^esub>)"
  and mono_in_codom_r2: "([in_codom (\<le>\<^bsub>R\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>R1\<^esub>)) r2"
  shows "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
proof (rule half_galois_prop_leftI)
  fix x z assume "x \<^bsub>L\<^esub>\<lessapprox> z"
  then show "l x \<le>\<^bsub>R\<^esub> z"
  proof (intro right_rel_if_left_relI')
    from \<open>x \<^bsub>L\<^esub>\<lessapprox> z\<close> show "in_codom (\<le>\<^bsub>R2\<^esub>) z" by blast
    fix y assume "y \<le>\<^bsub>R1\<^esub> l1 (r z)"
    moreover have "l1 (r z) \<le>\<^bsub>R1\<^esub> r2 z"
    proof -
      from mono_in_codom_r2 \<open>x \<^bsub>L\<^esub>\<lessapprox> z\<close> have "in_codom (\<le>\<^bsub>R1\<^esub>) (r2 z)" by blast
      with deflationary_counit1 show "l1 (r z) \<le>\<^bsub>R1\<^esub> r2 z" by auto
    qed
    ultimately show "y \<le>\<^bsub>R1\<^esub> r2 z" using trans_R1 by blast
  next
    assume "in_dom (\<le>\<^bsub>L2\<^esub>) (l1 x)"
    with refl_L2 have "l1 x \<le>\<^bsub>L2\<^esub> l1 x" by blast
    with \<open>((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2\<close> show "in_codom (\<le>\<^bsub>L2\<^esub>) (l1 x)" "l x \<le>\<^bsub>R2\<^esub> l2 (l1 x)"
      by auto
  qed (insert assms, auto)
qed

lemma half_galois_prop_right_left_rightI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and inflationary_counit1: "inflationary_on (in_codom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and "((\<le>\<^bsub>R2\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L2\<^esub>)) r2 l2"
  and inflationary_unit2: "inflationary_on (in_dom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and trans_L2: "transitive (\<le>\<^bsub>L2\<^esub>)"
  and mono_in_dom_l1: "([in_dom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_dom (\<le>\<^bsub>L2\<^esub>)) l1"
  and "((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  and "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
proof (rule half_galois_prop_rightI)
  fix x z assume "x \<lessapprox>\<^bsub>R\<^esub> z"
  then show "x \<le>\<^bsub>L\<^esub> r z"
  proof (intro flip.right_rel_if_left_relI)
    fix y assume "r2 (l x) \<le>\<^bsub>L2\<^esub> y"
    moreover have "l1 x \<le>\<^bsub>L2\<^esub> r2 (l x)"
    proof -
      from mono_in_dom_l1 \<open>x \<lessapprox>\<^bsub>R\<^esub> z\<close> have "in_dom (\<le>\<^bsub>L2\<^esub>) (l1 x)" by blast
      with inflationary_unit2 show "l1 x \<le>\<^bsub>L2\<^esub> r2 (l x)" by auto
    qed
    ultimately show "l1 x \<le>\<^bsub>L2\<^esub> y" using trans_L2 by blast
    fix y assume "l1 x \<le>\<^bsub>R1\<^esub> y"
    with \<open>((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1\<close> \<open>x \<lessapprox>\<^bsub>R\<^esub> z\<close> show "x \<le>\<^bsub>L1\<^esub> r1 y" by blast
  next
    assume "in_codom (\<le>\<^bsub>R1\<^esub>) (r2 z)"
    with inflationary_counit1 show "r2 z \<le>\<^bsub>R1\<^esub> l1 (r z)" by auto
    from \<open>((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1\<close> \<open>in_codom (\<le>\<^bsub>R1\<^esub>) (r2 z)\<close> show "in_codom (\<le>\<^bsub>L1\<^esub>) (r z)"
      by (auto intro: in_codom_if_rel_if_dep_mono_wrt_rel)
  qed (insert assms, auto elim: galois_rel.left_GaloisE)
qed

lemma half_galois_prop_right_left_rightI':
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and inflationary_unit1: "inflationary_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and inflationary_counit1: "\<And>y z. y \<le>\<^bsub>R1\<^esub> r2 z \<Longrightarrow> y \<le>\<^bsub>R1\<^esub> l1 (r z)"
  and "in_dom (\<le>\<^bsub>R1\<^esub>) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L2\<^esub>)) r2 l2"
  and inflationary_unit2: "inflationary_on (in_dom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and trans_L2: "transitive (\<le>\<^bsub>L2\<^esub>)"
  and mono_in_dom_l1: "([in_dom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_dom (\<le>\<^bsub>L2\<^esub>)) l1"
  and "((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  and "in_dom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_dom (\<le>\<^bsub>R1\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
proof (rule half_galois_prop_rightI)
  fix x z assume "x \<lessapprox>\<^bsub>R\<^esub> z"
  then show "x \<le>\<^bsub>L\<^esub> r z"
  proof (intro flip.right_rel_if_left_relI')
    from \<open>x \<lessapprox>\<^bsub>R\<^esub> z\<close> inflationary_unit1 show "x \<le>\<^bsub>L1\<^esub> r1 (l1 x)"
      by (fastforce elim: galois_rel.left_GaloisE)
    fix y assume "y \<le>\<^bsub>R1\<^esub> r2 z"
    with inflationary_counit1 show "y \<le>\<^bsub>R1\<^esub> l1 (r z)" by auto
  next
    fix y
    from mono_in_dom_l1 \<open>x \<lessapprox>\<^bsub>R\<^esub> z\<close> have "in_dom (\<le>\<^bsub>L2\<^esub>) (l1 x)" by blast
    with inflationary_unit2 have "l1 x \<le>\<^bsub>L2\<^esub> r2 (l x)" by auto
    moreover assume "r2 (l x) \<le>\<^bsub>L2\<^esub> y"
    ultimately show "l1 x \<le>\<^bsub>L2\<^esub> y" using trans_L2 by blast
  qed (insert assms, auto elim: galois_rel.left_GaloisE)
qed

lemma galois_prop_left_rightI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "rel_equivalence_on (in_codom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "((\<le>\<^bsub>R2\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L2\<^esub>)) r2 l2"
  and "inflationary_on (in_dom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and "preorder_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "middle_compatible_codom"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_propI
    half_galois_prop_left_left_rightI half_galois_prop_right_left_rightI
    flip.mono_in_codom_left_rel_left1_if_in_codom_rel_comp_le
    mono_in_dom_left_rel_left1_if_in_dom_rel_comp_le
    in_dom_right1_left2_right1_le_if_right1_left2_right1_le)
  (auto elim!: preorder_on_in_fieldE
    intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_codom)

lemma galois_prop_left_rightI':
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "inflationary_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and rel_equiv_counit1: "rel_equivalence_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and trans_R1: "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "((\<le>\<^bsub>R2\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L2\<^esub>)) r2 l2"
  and "inflationary_on (in_dom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and "preorder_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "middle_compatible_dom"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
proof (rule galois_propI)
  show "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r" using assms
    by (intro half_galois_prop_left_left_rightI'
      flip.mono_in_codom_left_rel_left1_if_in_codom_rel_comp_le
      flip.in_codom_right1_left2_right1_le_if_right1_left2_right1_le)
    (auto elim!: rel_equivalence_onE preorder_on_in_fieldE
      intro: deflationary_on_if_le_pred_if_deflationary_on
        reflexive_on_if_le_pred_if_reflexive_on
        in_field_if_in_dom in_field_if_in_codom)
  have "y \<le>\<^bsub>R1\<^esub> l1 (r1 (r2 z))" if "y \<le>\<^bsub>R1\<^esub> r2 z" for y z
  proof -
    note \<open>y \<le>\<^bsub>R1\<^esub> r2 z\<close>
    moreover with rel_equiv_counit1 have "r2 z \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 (r2 z)" by auto
    ultimately show ?thesis using trans_R1 by auto
  qed
  moreover have "in_dom (\<le>\<^bsub>R1\<^esub>) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  proof -
    from rel_equiv_counit1 trans_R1 have "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
      by (intro reflexive_on_in_field_if_transitive_if_rel_equivalence_on) auto
    then show ?thesis by (simp only: in_codom_eq_in_dom_if_reflexive_on_in_field)
  qed
  ultimately show "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r" using assms
    by (intro half_galois_prop_right_left_rightI'
      mono_in_dom_left_rel_left1_if_in_dom_rel_comp_le)
    auto
qed

end


end