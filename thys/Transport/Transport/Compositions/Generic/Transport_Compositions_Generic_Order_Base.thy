\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Basic Order Properties\<close>
theory Transport_Compositions_Generic_Order_Base
  imports
   Transport_Compositions_Generic_Base
begin

context transport_comp
begin

interpretation flip1 : galois R1 L1 r1 l1 .

subsubsection \<open>Reflexivity\<close>

lemma reflexive_on_in_dom_leftI:
  assumes galois_prop: "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and in_dom_L1_le: "in_dom (\<le>\<^bsub>L1\<^esub>) \<le> in_codom (\<le>\<^bsub>L1\<^esub>)"
  and refl_R1: "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and refl_L2: "reflexive_on (in_dom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and mono_in_dom_l1: "([in_dom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_dom (\<le>\<^bsub>L2\<^esub>)) l1"
  shows "reflexive_on (in_dom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
proof (rule reflexive_onI)
  fix x assume "in_dom (\<le>\<^bsub>L\<^esub>) x"
  then obtain x' where "x \<le>\<^bsub>L\<^esub> x'" "in_dom (\<le>\<^bsub>L1\<^esub>) x" by blast
  show "x \<le>\<^bsub>L\<^esub> x"
  proof (rule left_relI)
    from refl_R1 have "l1 x \<le>\<^bsub>R1\<^esub> l1 x"
    proof (rule reflexive_onD)
      from \<open>x \<le>\<^bsub>L\<^esub> x'\<close> galois_prop show "in_dom (\<le>\<^bsub>R1\<^esub>) (l1 x)" by blast
    qed
    then show "x \<^bsub>L1\<^esub>\<lessapprox> l1 x"
    proof (intro t1.left_GaloisI)
      from galois_prop \<open>in_dom (\<le>\<^bsub>L1\<^esub>) x\<close> \<open>l1 x \<le>\<^bsub>R1\<^esub> l1 x\<close> show "x \<le>\<^bsub>L1\<^esub> r1 (l1 x)" by blast
    qed blast
    from refl_L2 show "l1 x \<le>\<^bsub>L2\<^esub> l1 x"
    proof (rule reflexive_onD)
      from mono_in_dom_l1 \<open>x \<le>\<^bsub>L\<^esub> x'\<close> show "in_dom (\<le>\<^bsub>L2\<^esub>) (l1 x)" by blast
    qed
    from \<open>l1 x \<le>\<^bsub>R1\<^esub> l1 x\<close> show "l1 x \<^bsub>R1\<^esub>\<lessapprox> x"
    proof (intro flip1.left_GaloisI)
      from \<open>in_dom (\<le>\<^bsub>L1\<^esub>) x\<close> in_dom_L1_le show "in_codom (\<le>\<^bsub>L1\<^esub>) x" by blast
    qed
  qed
qed

lemma reflexive_on_in_codom_leftI:
  assumes L1_r1_l1I: "\<And>x. in_dom (\<le>\<^bsub>L1\<^esub>) x \<Longrightarrow> l1 x \<le>\<^bsub>R1\<^esub> l1 x \<Longrightarrow> x \<le>\<^bsub>L1\<^esub> r1 (l1 x)"
  and in_codom_L1_le: "in_codom (\<le>\<^bsub>L1\<^esub>) \<le> in_dom (\<le>\<^bsub>L1\<^esub>)"
  and refl_R1: "reflexive_on (in_codom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and refl_L2: "reflexive_on (in_codom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and mono_in_codom_l1: "([in_codom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>L2\<^esub>)) l1"
  shows "reflexive_on (in_codom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
proof (rule reflexive_onI)
  fix x assume "in_codom (\<le>\<^bsub>L\<^esub>) x"
  then obtain x' where "x' \<le>\<^bsub>L\<^esub> x" "in_codom (\<le>\<^bsub>L1\<^esub>) x" "in_codom (\<le>\<^bsub>R1\<^esub>) (l1 x)"
    by blast
  show "x \<le>\<^bsub>L\<^esub> x"
  proof (rule left_relI)
    from refl_R1 \<open>in_codom (\<le>\<^bsub>R1\<^esub>) (l1 x)\<close> have "l1 x \<le>\<^bsub>R1\<^esub> l1 x" by blast
    show "x \<^bsub>L1\<^esub>\<lessapprox> l1 x"
    proof (rule t1.left_GaloisI)
      from in_codom_L1_le \<open>in_codom (\<le>\<^bsub>L1\<^esub>) x\<close> have "in_dom (\<le>\<^bsub>L1\<^esub>) x" by blast
      with \<open>l1 x \<le>\<^bsub>R1\<^esub> l1 x\<close> show "x \<le>\<^bsub>L1\<^esub> r1 (l1 x)" by (intro L1_r1_l1I)
    qed fact
    from refl_L2 show "l1 x \<le>\<^bsub>L2\<^esub> l1 x"
    proof (rule reflexive_onD)
      from mono_in_codom_l1 \<open>x' \<le>\<^bsub>L\<^esub> x\<close> show "in_codom (\<le>\<^bsub>L2\<^esub>) (l1 x)" by blast
    qed
    show "l1 x \<^bsub>R1\<^esub>\<lessapprox> x" by (rule flip1.left_GaloisI) fact+
  qed
qed

corollary reflexive_on_in_field_leftI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "in_codom (\<le>\<^bsub>L1\<^esub>) = in_dom (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "([in_field (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_field (\<le>\<^bsub>L2\<^esub>)) l1"
  shows "reflexive_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
proof -
  from assms have "reflexive_on (in_dom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
    by (intro reflexive_on_in_dom_leftI)
    (auto 0 4 intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom)
  moreover from assms have "reflexive_on (in_codom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
    by (intro reflexive_on_in_codom_leftI)
    (auto 0 4 intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_codom)
  ultimately show ?thesis by (auto iff: in_field_iff_in_dom_or_in_codom)
qed


subsubsection \<open>Transitivity\<close>

text\<open>There are many similar proofs for transitivity. They slightly differ in
their assumptions, particularly which of @{term "(\<le>\<^bsub>R1\<^esub>)"} and @{term "(\<le>\<^bsub>L2\<^esub>)"} has
to be transitive and the order of commutativity for the relations.

In the following, we just give two of them that suffice for many purposes.\<close>

lemma transitive_leftI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and trans_L2: "transitive (\<le>\<^bsub>L2\<^esub>)"
  and R1_L2_R1_le: "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  shows "transitive (\<le>\<^bsub>L\<^esub>)"
proof (rule transitiveI)
  fix x1 x2 x3 assume "x1 \<le>\<^bsub>L\<^esub> x2" "x2 \<le>\<^bsub>L\<^esub> x3"
  from \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> obtain y1 y2 where "x1 \<^bsub>L1\<^esub>\<lessapprox> y1" "y1 \<le>\<^bsub>L2\<^esub> y2" "y2 \<le>\<^bsub>R1\<^esub> l1 x2"
    by blast
  from \<open>x2 \<le>\<^bsub>L\<^esub> x3\<close> \<open>((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1\<close> obtain y3 y4 where
    "l1 x2 \<le>\<^bsub>R1\<^esub> y3" "y3 \<le>\<^bsub>L2\<^esub> y4" "y4 \<le>\<^bsub>R1\<^esub> l1 x3" "in_codom (\<le>\<^bsub>L1\<^esub>) x3" by blast
  with R1_L2_R1_le have "((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) (l1 x2) (l1 x3)" by blast
  then obtain y where "l1 x2 \<le>\<^bsub>L2\<^esub> y" "y \<le>\<^bsub>R1\<^esub> l1 x3" by blast
  with \<open>y2 \<le>\<^bsub>R1\<^esub> l1 x2\<close> R1_L2_R1_le have "((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) y2 (l1 x3)" by blast
  then obtain y' where "y2 \<le>\<^bsub>L2\<^esub> y'" "y' \<le>\<^bsub>R1\<^esub> l1 x3" by blast
  with \<open>y1 \<le>\<^bsub>L2\<^esub> y2\<close> have "y1 \<le>\<^bsub>L2\<^esub> y'" using trans_L2 by blast
  show "x1 \<le>\<^bsub>L\<^esub> x3"
  proof (rule left_relI)
    show "x1 \<^bsub>L1\<^esub>\<lessapprox> y1" "y1 \<le>\<^bsub>L2\<^esub> y'" by fact+
    show "y' \<^bsub>R1\<^esub>\<lessapprox> x3" by (rule flip1.left_GaloisI) fact+
  qed
qed

lemma transitive_leftI':
  assumes galois_prop: "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and trans_L2: "transitive (\<le>\<^bsub>L2\<^esub>)"
  and R1_L2_R1_le: "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  shows "transitive (\<le>\<^bsub>L\<^esub>)"
proof (rule transitiveI)
  fix x1 x2 x3 assume "x1 \<le>\<^bsub>L\<^esub> x2" "x2 \<le>\<^bsub>L\<^esub> x3"
  from \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> galois_prop obtain y1 y2 where
    "in_dom (\<le>\<^bsub>L1\<^esub>) x1" "l1 x1 \<le>\<^bsub>R1\<^esub> y1" "y1 \<le>\<^bsub>L2\<^esub> y2" "y2 \<le>\<^bsub>R1\<^esub> l1 x2" by blast
  with R1_L2_R1_le have "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) (l1 x1) (l1 x2)" by blast
  then obtain y where "l1 x1 \<le>\<^bsub>R1\<^esub> y" "y \<le>\<^bsub>L2\<^esub> l1 x2" by blast
  moreover from \<open>x2 \<le>\<^bsub>L\<^esub> x3\<close> galois_prop obtain y3 y4 where
    "l1 x2 \<le>\<^bsub>R1\<^esub> y3" "y3 \<le>\<^bsub>L2\<^esub> y4" "y4 \<^bsub>R1\<^esub>\<lessapprox> x3" by blast
  moreover note R1_L2_R1_le
  ultimately have "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) (l1 x1) y3" by blast
  then obtain y' where "l1 x1 \<le>\<^bsub>R1\<^esub> y'" "y' \<le>\<^bsub>L2\<^esub> y3" by blast
  with \<open>y3 \<le>\<^bsub>L2\<^esub> y4\<close> have "y' \<le>\<^bsub>L2\<^esub> y4" using trans_L2 by blast
  show "x1 \<le>\<^bsub>L\<^esub> x3"
  proof (rule left_relI)
    from \<open>in_dom (\<le>\<^bsub>L1\<^esub>) x1\<close> \<open>l1 x1 \<le>\<^bsub>R1\<^esub> y'\<close> galois_prop show "x1 \<^bsub>L1\<^esub>\<lessapprox> y'"
      by (intro t1.left_Galois_if_Galois_right_if_half_galois_prop_right t1.left_GaloisI)
      auto
    show "y' \<le>\<^bsub>L2\<^esub> y4" by fact
    from \<open>y' \<le>\<^bsub>L2\<^esub> y4\<close> \<open>y4 \<^bsub>R1\<^esub>\<lessapprox> x3\<close> show "y4 \<^bsub>R1\<^esub>\<lessapprox> x3" by blast
  qed
qed


subsubsection \<open>Preorders\<close>

lemma preorder_on_in_field_leftI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "in_codom (\<le>\<^bsub>L1\<^esub>) = in_dom (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "preorder_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and mono_in_codom_l1: "([in_codom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>L2\<^esub>)) l1"
  and R1_L2_R1_le: "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  shows "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
proof -
  have "([in_field (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_field (\<le>\<^bsub>L2\<^esub>)) l1"
  proof -
    from \<open>((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1\<close> R1_L2_R1_le
      have "([in_dom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_dom (\<le>\<^bsub>L2\<^esub>)) l1"
      by (intro mono_in_dom_left_rel_left1_if_in_dom_rel_comp_le
        in_dom_right1_left2_right1_le_if_right1_left2_right1_le)
      auto
    with mono_in_codom_l1 show ?thesis by (intro dep_mono_wrt_predI) blast
  qed
  with assms show ?thesis by (intro preorder_onI)
    (auto intro: reflexive_on_in_field_leftI transitive_leftI)
qed

lemma preorder_on_in_field_leftI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "in_codom (\<le>\<^bsub>L1\<^esub>) = in_dom (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "preorder_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and mono_in_dom_l1: "([in_dom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_dom (\<le>\<^bsub>L2\<^esub>)) l1"
  and R1_L2_R1_le: "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  shows "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
proof -
  have "([in_field (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_field (\<le>\<^bsub>L2\<^esub>)) l1"
  proof -
    from \<open>((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1\<close> R1_L2_R1_le
      have "([in_codom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>L2\<^esub>)) l1"
      by (intro mono_in_codom_left_rel_left1_if_in_codom_rel_comp_le
        in_codom_right1_left2_right1_le_if_right1_left2_right1_le)
      auto
    with mono_in_dom_l1 show ?thesis by (intro dep_mono_wrt_predI) blast
  qed
  with assms show ?thesis by (intro preorder_onI)
    (auto intro: reflexive_on_in_field_leftI transitive_leftI')
qed


subsubsection \<open>Symmetry\<close>

lemma symmetric_leftI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "in_codom (\<le>\<^bsub>L1\<^esub>) = in_dom (\<le>\<^bsub>L1\<^esub>)"
  and "symmetric (\<le>\<^bsub>R1\<^esub>)"
  and "symmetric (\<le>\<^bsub>L2\<^esub>)"
  shows "symmetric (\<le>\<^bsub>L\<^esub>)"
proof -
  from assms have "(\<greaterapprox>\<^bsub>R1\<^esub>) = (\<^bsub>L1\<^esub>\<lessapprox>)" by (intro
    t1.ge_Galois_right_eq_left_Galois_if_symmetric_if_in_codom_eq_in_dom_if_galois_prop)
  moreover then have "(\<^bsub>R1\<^esub>\<lessapprox>) = (\<greaterapprox>\<^bsub>L1\<^esub>)"
    by (subst rel_inv_eq_iff_eq[symmetric]) simp
  ultimately show ?thesis using assms unfolding left_rel_eq_comp
    by (subst symmetric_iff_rel_inv_eq_self) (simp add: rel_comp_assoc)
qed

lemma partial_equivalence_rel_leftI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "in_codom (\<le>\<^bsub>L1\<^esub>) = in_dom (\<le>\<^bsub>L1\<^esub>)"
  and "symmetric (\<le>\<^bsub>R1\<^esub>)"
  and "partial_equivalence_rel (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  shows "partial_equivalence_rel (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro partial_equivalence_relI transitive_leftI symmetric_leftI)
  auto

lemma partial_equivalence_rel_leftI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "in_codom (\<le>\<^bsub>L1\<^esub>) = in_dom (\<le>\<^bsub>L1\<^esub>)"
  and "symmetric (\<le>\<^bsub>R1\<^esub>)"
  and "partial_equivalence_rel (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  shows "partial_equivalence_rel (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro partial_equivalence_relI transitive_leftI' symmetric_leftI)
  auto

end


end