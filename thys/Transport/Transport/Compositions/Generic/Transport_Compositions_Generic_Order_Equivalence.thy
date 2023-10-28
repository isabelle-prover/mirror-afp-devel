\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Order Equivalence\<close>
theory Transport_Compositions_Generic_Order_Equivalence
  imports
    Transport_Compositions_Generic_Monotone
begin

context transport_comp
begin

context
begin

interpretation flip : transport_comp R2 L2 r2 l2 R1 L1 r1 l1  .

subsubsection \<open>Unit\<close>
paragraph \<open>Inflationary\<close>

lemma inflationary_on_in_dom_unitI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and inflationary_unit1: "inflationary_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and inflationary_counit1: "inflationary_on (in_codom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and refl_R1: "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and inflationary_unit2: "inflationary_on (in_dom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and refl_L2: "reflexive_on (in_dom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and mono_in_dom_l1: "([in_dom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_dom (\<le>\<^bsub>L2\<^esub>)) l1"
  and in_codom_rel_comp_le: "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom ((\<le>\<^bsub>R1\<^esub>))"
  shows "inflationary_on (in_dom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
proof (rule inflationary_onI)
  fix x assume "in_dom (\<le>\<^bsub>L\<^esub>) x"
  show "x \<le>\<^bsub>L\<^esub> \<eta> x"
  proof (rule left_relI)
    from \<open>in_dom (\<le>\<^bsub>L\<^esub>) x\<close> \<open>((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1\<close> have "in_dom (\<le>\<^bsub>R1\<^esub>) (l1 x)" by blast
    with refl_R1 have "l1 x \<le>\<^bsub>R1\<^esub> l1 x" by blast
    moreover from \<open>in_dom (\<le>\<^bsub>L\<^esub>) x\<close> have "in_dom (\<le>\<^bsub>L1\<^esub>) x" by blast
    moreover note inflationary_unit1
    ultimately show "x \<^bsub>L1\<^esub>\<lessapprox> l1 x" by (intro t1.left_GaloisI) auto
    from \<open>in_dom (\<le>\<^bsub>L\<^esub>) x\<close> mono_in_dom_l1 have "in_dom (\<le>\<^bsub>L2\<^esub>) (l1 x)" by blast
    with inflationary_unit2 show "l1 x \<le>\<^bsub>L2\<^esub> r2 (l x)" by auto
    show "r2 (l x) \<^bsub>R1\<^esub>\<lessapprox> \<eta> x"
    proof (rule flip.t2.left_GaloisI)
      from refl_L2 \<open>in_dom (\<le>\<^bsub>L2\<^esub>) (l1 x)\<close> have "l1 x \<le>\<^bsub>L2\<^esub> l1 x" by blast
      with in_codom_rel_comp_le \<open>l1 x \<le>\<^bsub>R1\<^esub> l1 x\<close> \<open>l1 x \<le>\<^bsub>L2\<^esub> r2 (l x)\<close>
        have "in_codom (\<le>\<^bsub>R1\<^esub>) (r2 (l x))" by blast
      with \<open>((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1\<close> show "in_codom (\<le>\<^bsub>L1\<^esub>) (\<eta> x)"
        by (auto intro: in_codom_if_rel_if_dep_mono_wrt_rel)
      from \<open>in_codom (\<le>\<^bsub>R1\<^esub>) (r2 (l x))\<close> inflationary_counit1
        show "r2 (l x) \<le>\<^bsub>R1\<^esub> l1 (\<eta> x)" by auto
    qed
  qed
qed

lemma inflationary_on_in_codom_unitI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and inflationary_unit1: "inflationary_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and inflationary_counit1: "inflationary_on (in_codom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and refl_R1: "reflexive_on (in_codom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and inflationary_unit2: "inflationary_on (in_codom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and refl_L2: "reflexive_on (in_codom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and mono_in_codom_l1: "([in_codom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>L2\<^esub>)) l1"
  and in_codom_rel_comp_le: "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom ((\<le>\<^bsub>R1\<^esub>))"
  shows "inflationary_on (in_codom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
proof (rule inflationary_onI)
  fix x assume "in_codom (\<le>\<^bsub>L\<^esub>) x"
  show "x \<le>\<^bsub>L\<^esub> \<eta> x"
  proof (rule left_relI)
    from \<open>in_codom (\<le>\<^bsub>L\<^esub>) x\<close> have "in_codom (\<le>\<^bsub>L1\<^esub>) x" "in_codom (\<le>\<^bsub>R1\<^esub>) (l1 x)" by blast+
    with inflationary_unit1 show "x \<^bsub>L1\<^esub>\<lessapprox> l1 x" by (intro t1.left_GaloisI) auto
    from mono_in_codom_l1 \<open>in_codom (\<le>\<^bsub>L\<^esub>) x\<close> have "in_codom (\<le>\<^bsub>L2\<^esub>) (l1 x)" by blast
    with inflationary_unit2 show "l1 x \<le>\<^bsub>L2\<^esub> r2 (l x)" by auto
    show "r2 (l x) \<^bsub>R1\<^esub>\<lessapprox> \<eta> x"
    proof (rule flip.t2.left_GaloisI)
      from refl_L2 \<open>in_codom (\<le>\<^bsub>L2\<^esub>) (l1 x)\<close> have "l1 x \<le>\<^bsub>L2\<^esub> l1 x" by blast
      moreover from refl_R1 \<open>in_codom (\<le>\<^bsub>R1\<^esub>) (l1 x)\<close> have "l1 x \<le>\<^bsub>R1\<^esub> l1 x" by blast
      moreover note in_codom_rel_comp_le \<open>l1 x \<le>\<^bsub>L2\<^esub> r2 (l x)\<close>
      ultimately have "in_codom (\<le>\<^bsub>R1\<^esub>) (r2 (l x))" by blast
      with \<open>((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1\<close> show "in_codom (\<le>\<^bsub>L1\<^esub>) (\<eta> x)"
        by (auto intro: in_codom_if_rel_if_dep_mono_wrt_rel)
      from \<open>in_codom (\<le>\<^bsub>R1\<^esub>) (r2 (l x))\<close> inflationary_counit1
        show "r2 (l x) \<le>\<^bsub>R1\<^esub> l1 (\<eta> x)" by auto
    qed
  qed
qed

corollary inflationary_on_in_field_unitI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "inflationary_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and "inflationary_on (in_codom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "inflationary_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and "reflexive_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "([in_dom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_dom (\<le>\<^bsub>L2\<^esub>)) l1"
  and "([in_codom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>L2\<^esub>)) l1"
  and "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom ((\<le>\<^bsub>R1\<^esub>))"
  shows "inflationary_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
proof -
  from assms have "inflationary_on (in_dom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
    by (intro inflationary_on_in_dom_unitI)
    (auto intro: inflationary_on_if_le_pred_if_inflationary_on
      reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom)
  moreover from assms have "inflationary_on (in_codom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
    by (intro inflationary_on_in_codom_unitI)
    (auto intro: inflationary_on_if_le_pred_if_inflationary_on
      reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_codom)
  ultimately show ?thesis by (auto iff: in_field_iff_in_dom_or_in_codom)
qed


text \<open>Deflationary\<close>

lemma deflationary_on_in_dom_unitI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1" "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and refl_L1: "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and in_dom_R1_le_in_codom_R1: "in_dom (\<le>\<^bsub>R1\<^esub>) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  and deflationary_L2: "deflationary_on (in_dom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and refl_L2: "reflexive_on (in_dom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and mono_in_dom_l1: "([in_dom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_dom (\<le>\<^bsub>L2\<^esub>)) l1"
  and in_dom_rel_comp_le: "in_dom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_dom ((\<le>\<^bsub>R1\<^esub>))"
  shows "deflationary_on (in_dom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
proof (rule deflationary_onI)
  fix x assume "in_dom (\<le>\<^bsub>L\<^esub>) x"
  show "\<eta> x \<le>\<^bsub>L\<^esub> x"
  proof (rule left_relI)
    from refl_L1 \<open>in_dom (\<le>\<^bsub>L\<^esub>) x\<close> have "x \<le>\<^bsub>L1\<^esub> x" by blast
    moreover with \<open>((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1\<close> have "l1 x \<le>\<^bsub>R1\<^esub> l1 x" by blast
    ultimately show "l1 x \<^bsub>R1\<^esub>\<lessapprox> x" by auto
    from mono_in_dom_l1 \<open>in_dom (\<le>\<^bsub>L\<^esub>) x\<close> have "in_dom (\<le>\<^bsub>L2\<^esub>) (l1 x)" by blast
    with deflationary_L2 show "r2 (l x) \<le>\<^bsub>L2\<^esub> l1 x" by auto
    show "\<eta> x \<^bsub>L1\<^esub>\<lessapprox> r2 (l x)"
    proof (rule t1.left_GaloisI)
      from refl_L2 \<open>in_dom (\<le>\<^bsub>L2\<^esub>) (l1 x)\<close> have "l1 x \<le>\<^bsub>L2\<^esub> l1 x" by blast
      with in_dom_rel_comp_le \<open>r2 (l x) \<le>\<^bsub>L2\<^esub> l1 x\<close> \<open>l1 x \<le>\<^bsub>R1\<^esub> l1 x\<close>
        have "in_dom (\<le>\<^bsub>R1\<^esub>) (r2 (l x))" by blast
      with \<open>((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1\<close> have "in_dom (\<le>\<^bsub>L1\<^esub>) (\<eta> x)"
        by (auto intro: in_dom_if_rel_if_dep_mono_wrt_rel)
      with refl_L1 show "\<eta> x \<le>\<^bsub>L1\<^esub> r1 (r2 (l x))"
        by (auto intro: in_field_if_in_codom)
      from \<open>in_dom (\<le>\<^bsub>R1\<^esub>) (r2 (l x))\<close> in_dom_R1_le_in_codom_R1
        show "in_codom (\<le>\<^bsub>R1\<^esub>) (r2 (l x))" by blast
    qed
  qed
qed

lemma deflationary_on_in_codom_unitI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1" "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and refl_L1: "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and in_dom_R1_le_in_codom_R1: "in_dom (\<le>\<^bsub>R1\<^esub>) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  and deflationary_L2: "deflationary_on (in_codom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and refl_L2: "reflexive_on (in_codom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and mono_in_codom_l1: "([in_codom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>L2\<^esub>)) l1"
  and in_dom_rel_comp_le: "in_dom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_dom ((\<le>\<^bsub>R1\<^esub>))"
  shows "deflationary_on (in_codom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
proof (rule deflationary_onI)
  fix x assume "in_codom (\<le>\<^bsub>L\<^esub>) x"
  show "\<eta> x \<le>\<^bsub>L\<^esub> x"
  proof (rule left_relI)
    from refl_L1 \<open>in_codom (\<le>\<^bsub>L\<^esub>) x\<close> have "x \<le>\<^bsub>L1\<^esub> x" by blast
    moreover with \<open>((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1\<close> have "l1 x \<le>\<^bsub>R1\<^esub> l1 x" by blast
    ultimately show "l1 x \<^bsub>R1\<^esub>\<lessapprox> x" by auto
    from mono_in_codom_l1 \<open>in_codom (\<le>\<^bsub>L\<^esub>) x\<close> have "in_codom (\<le>\<^bsub>L2\<^esub>) (l1 x)" by blast
    with deflationary_L2 show "r2 (l x) \<le>\<^bsub>L2\<^esub> l1 x" by auto
    show "\<eta> x \<^bsub>L1\<^esub>\<lessapprox> r2 (l x)"
    proof (rule t1.left_GaloisI)
      from refl_L2 \<open>in_codom (\<le>\<^bsub>L2\<^esub>) (l1 x)\<close> have "l1 x \<le>\<^bsub>L2\<^esub> l1 x" by blast
      with in_dom_rel_comp_le \<open>r2 (l x) \<le>\<^bsub>L2\<^esub> l1 x\<close> \<open>l1 x \<le>\<^bsub>R1\<^esub> l1 x\<close>
        have "in_dom (\<le>\<^bsub>R1\<^esub>) (r2 (l x))" by blast
      with in_dom_R1_le_in_codom_R1 show "in_codom (\<le>\<^bsub>R1\<^esub>) (r2 (l x))" by blast
      with \<open>((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1\<close> have "in_codom (\<le>\<^bsub>L1\<^esub>) (\<eta> x)"
        by (auto intro: in_codom_if_rel_if_dep_mono_wrt_rel)
      with refl_L1 show "\<eta> x \<le>\<^bsub>L1\<^esub> r1 (r2 (l x))" by auto
    qed
  qed
qed

corollary deflationary_on_in_field_unitI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1" "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "in_dom (\<le>\<^bsub>R1\<^esub>) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  and "deflationary_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and "reflexive_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "([in_dom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_dom (\<le>\<^bsub>L2\<^esub>)) l1"
  and "([in_codom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>L2\<^esub>)) l1"
  and "in_dom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_dom ((\<le>\<^bsub>R1\<^esub>))"
  shows "deflationary_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
proof -
  from assms have "deflationary_on (in_dom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
    by (intro deflationary_on_in_dom_unitI)
    (auto intro: deflationary_on_if_le_pred_if_deflationary_on
      reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom)
  moreover from assms have "deflationary_on (in_codom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
    by (intro deflationary_on_in_codom_unitI)
    (auto intro: deflationary_on_if_le_pred_if_deflationary_on
      reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_codom)
  ultimately show ?thesis by (auto iff: in_field_iff_in_dom_or_in_codom)
qed


text \<open>Relational Equivalence\<close>

corollary rel_equivalence_on_in_field_unitI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1" "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "inflationary_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and "inflationary_on (in_codom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "rel_equivalence_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and "reflexive_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "([in_dom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_dom (\<le>\<^bsub>L2\<^esub>)) l1"
  and "([in_codom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>L2\<^esub>)) l1"
  and "in_dom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_dom ((\<le>\<^bsub>R1\<^esub>))"
  and "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom ((\<le>\<^bsub>R1\<^esub>))"
  shows "rel_equivalence_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  using assms by (intro rel_equivalence_onI
    inflationary_on_in_field_unitI deflationary_on_in_field_unitI)
  (auto simp only: in_codom_eq_in_dom_if_reflexive_on_in_field)


subsubsection \<open>Counit\<close>

text \<open>Corresponding lemmas for the counit can be obtained by flipping the
interpretation of the locale, i.e.
\<open>
interpretation flip : transport_comp R2 L2 r2 l2 R1 L1 r1 l1
  rewrites "flip.t2.unit \<equiv> \<epsilon>\<^sub>1" and "flip.t2.counit \<equiv> \<eta>\<^sub>1"
  and "flip.t1.unit \<equiv> \<epsilon>\<^sub>2" and "flip.t1.counit \<equiv> \<eta>\<^sub>2"
  and "flip.unit \<equiv> \<epsilon>" and "flip.counit \<equiv> \<eta>"
  unfolding transport_comp.transport_defs
  by (auto simp: order_functors.flip_counit_eq_unit)
\<close>
\<close>

end


subsubsection \<open>Order Equivalence\<close>

interpretation flip : transport_comp R2 L2 r2 l2 R1 L1 r1 l1
  rewrites "flip.t2.unit \<equiv> \<epsilon>\<^sub>1" and "flip.t2.counit \<equiv> \<eta>\<^sub>1"
  and "flip.t1.unit \<equiv> \<epsilon>\<^sub>2" and "flip.t1.counit \<equiv> \<eta>\<^sub>2"
  and "flip.counit \<equiv> \<eta>" and "flip.unit \<equiv> \<epsilon>"
  by (simp_all only: order_functors.flip_counit_eq_unit)

lemma order_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1" "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "inflationary_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and rel_equiv_counit1: "rel_equivalence_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2" "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "((\<le>\<^bsub>R2\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L2\<^esub>)) r2 l2"
  and rel_equiv_unit2: "rel_equivalence_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and "inflationary_on (in_field (\<le>\<^bsub>R2\<^esub>)) (\<le>\<^bsub>R2\<^esub>) \<epsilon>\<^sub>2"
  and "reflexive_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R2\<^esub>)) (\<le>\<^bsub>R2\<^esub>)"
  and middle_compatible: "middle_compatible_codom"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
proof (rule order_equivalenceI)
  show "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l" using rel_equiv_unit2 \<open>((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1\<close>
      \<open>((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2\<close> middle_compatible
    by (intro mono_wrt_rel_leftI) auto
  show "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r" using rel_equiv_counit1 \<open>((\<le>\<^bsub>R2\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L2\<^esub>)) r2 l2\<close>
      \<open>((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1\<close> middle_compatible
    by (intro flip.mono_wrt_rel_leftI)
    (auto intro: inflationary_on_if_le_pred_if_inflationary_on
      in_field_if_in_codom)
  from middle_compatible have in_dom_rel_comp_les:
    "in_dom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_dom (\<le>\<^bsub>L2\<^esub>)"
    "in_dom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_dom ((\<le>\<^bsub>R1\<^esub>))"
    by (auto intro: in_dom_right1_left2_right1_le_if_right1_left2_right1_le
      flip.in_dom_right1_left2_right1_le_if_right1_left2_right1_le)
  moreover then have "([in_dom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_dom (\<le>\<^bsub>L2\<^esub>)) l1"
    and "([in_codom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>L2\<^esub>)) l1"
    using \<open>((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1\<close> middle_compatible
    by (auto intro: mono_in_dom_left_rel_left1_if_in_dom_rel_comp_le
      mono_in_codom_left_rel_left1_if_in_codom_rel_comp_le)
  ultimately show "rel_equivalence_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
    using assms by (intro rel_equivalence_on_in_field_unitI)
    (auto intro: inflationary_on_if_le_pred_if_inflationary_on
      intro!: in_field_if_in_codom)
  note in_dom_rel_comp_les
  moreover then have "([in_dom (\<le>\<^bsub>R\<^esub>)] \<Rrightarrow>\<^sub>m in_dom (\<le>\<^bsub>R1\<^esub>)) r2"
    and "([in_codom (\<le>\<^bsub>R\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>R1\<^esub>)) r2"
    using \<open>((\<le>\<^bsub>R2\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L2\<^esub>)) r2 l2\<close> middle_compatible
    by (auto intro!: flip.mono_in_dom_left_rel_left1_if_in_dom_rel_comp_le
      flip.mono_in_codom_left_rel_left1_if_in_codom_rel_comp_le)
  ultimately show "rel_equivalence_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>) \<epsilon>"
    using assms by (intro flip.rel_equivalence_on_in_field_unitI)
    (auto intro: inflationary_on_if_le_pred_if_inflationary_on
      intro!: in_field_if_in_codom)
qed

corollary order_equivalence_if_order_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R2\<^esub>)) (\<le>\<^bsub>R2\<^esub>)"
  and "middle_compatible_codom"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro order_equivalenceI) (auto
    elim!: t1.order_equivalenceE t2.order_equivalenceE rel_equivalence_onE
    intro!: reflexive_on_in_field_if_transitive_if_rel_equivalence_on
      t1.half_galois_prop_left_left_right_if_transitive_if_deflationary_on_if_mono_wrt_rel
      flip.t1.half_galois_prop_left_left_right_if_transitive_if_deflationary_on_if_mono_wrt_rel
    intro: deflationary_on_if_le_pred_if_deflationary_on in_field_if_in_codom)

corollary order_equivalence_if_galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "reflexive_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R2\<^esub>)) (\<le>\<^bsub>R2\<^esub>)"
  and "middle_compatible_codom"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro order_equivalenceI)
  (auto elim!: t1.galois_equivalenceE t2.galois_equivalenceE
    intro!: t1.inflationary_on_unit_if_reflexive_on_if_galois_equivalence
      flip.t1.inflationary_on_unit_if_reflexive_on_if_galois_equivalence
      t2.rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence
      flip.t2.rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence)

end


end