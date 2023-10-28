\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Galois Equivalence\<close>
theory Transport_Functions_Galois_Equivalence
  imports
    Transport_Functions_Galois_Connection
    Transport_Functions_Order_Base
begin

paragraph \<open>Dependent Function Relator\<close>

context transport_Dep_Fun_Rel
begin

subparagraph \<open>Lemmas for Monotone Function Relator\<close>

lemma flip_half_galois_prop_left2_if_half_galois_prop_left2_if_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and half_galois_prop_left2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow>
    ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>) (l2\<^bsub>x' x\<^esub>) "
  and "(\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>) = (\<le>\<^bsub>L2 x x\<^esub>)"
  and "(\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) = (\<le>\<^bsub>L2 x x\<^esub>)"
  and "x \<le>\<^bsub>L1\<^esub> x"
  shows "((\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub>)"
proof -
  from assms have "x \<^bsub>L1\<^esub>\<lessapprox> l1 x" by (intro t1.left_Galois_left_if_left_relI) auto
  with half_galois_prop_left2
    have "((\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub>)" by auto
  with assms show ?thesis by simp
qed

lemma flip_half_galois_prop_right2_if_half_galois_prop_right2_if_GaloisI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and half_galois_prop_right2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow>
    ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>) (l2\<^bsub>x' x\<^esub>)"
  and "(\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) = (\<le>\<^bsub>R2 x' x'\<^esub>)"
  and "(\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>) = (\<le>\<^bsub>R2 x' x'\<^esub>)"
  and "x' \<le>\<^bsub>R1\<^esub> x'"
  shows "((\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') x'\<^esub>) (l2\<^bsub>x' (r1 x')\<^esub>)"
proof -
  from assms have "r1 x' \<^bsub>L1\<^esub>\<lessapprox> x'" by (intro t1.right_left_Galois_if_right_relI) auto
  with half_galois_prop_right2
    have "((\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') x'\<^esub>) (l2\<^bsub>x' (r1 x')\<^esub>)" by auto
  with assms show ?thesis by simp
qed

interpretation flip : transport_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2
  rewrites "flip.t1.counit \<equiv> \<eta>\<^sub>1" and "flip.t1.unit \<equiv> \<epsilon>\<^sub>1"
  by (simp_all only: t1.flip_counit_eq_unit t1.flip_unit_eq_counit)

lemma galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI:
  assumes galois_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and preorder_L1: "preorder_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and mono_L2: "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  shows "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | \<eta>\<^sub>1 x2 \<le>\<^bsub>L1\<^esub> x1] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2" (is ?goal1)
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x2 \<le>\<^bsub>L1\<^esub> x3 \<and> x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3)] \<Rrightarrow> (\<ge>)) L2" (is ?goal2)
proof -
  show ?goal1
  proof (intro dep_mono_wrt_relI rel_if_if_impI Dep_Fun_Rel_relI)
    fix x1 x2 x3 x4 assume "x1 \<le>\<^bsub>L1\<^esub> x2"
    moreover with galois_equiv1 preorder_L1 have "x2 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2"
      by (blast intro: t1.rel_unit_if_reflexive_on_if_galois_connection)
    moreover assume "\<eta>\<^sub>1 x2 \<le>\<^bsub>L1\<^esub> x1"
    ultimately have "x2 \<equiv>\<^bsub>L1\<^esub> x1" using preorder_L1 by blast
    moreover assume "x3 \<le>\<^bsub>L1\<^esub> x4" "x2 \<le>\<^bsub>L1\<^esub> x3"
    ultimately show "(\<le>\<^bsub>L2 x1 x3\<^esub>) \<le> (\<le>\<^bsub>L2 x2 x4\<^esub>)" using preorder_L1 mono_L2 by blast
  qed
  show ?goal2
  proof (intro dep_mono_wrt_relI rel_if_if_impI Dep_Fun_Rel_relI)
    fix x1 x2 x3 x4 presume "x3 \<le>\<^bsub>L1\<^esub> x4" "x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3"
    moreover with galois_equiv1 preorder_L1 have "\<eta>\<^sub>1 x3 \<le>\<^bsub>L1\<^esub> x3"
      by (blast intro: flip.t1.counit_rel_if_reflexive_on_if_galois_connection)
    ultimately have "x3 \<equiv>\<^bsub>L1\<^esub> x4" using preorder_L1 by blast
    moreover presume "x1 \<le>\<^bsub>L1\<^esub> x2" "x2 \<le>\<^bsub>L1\<^esub> x3"
    ultimately show "(\<le>\<^bsub>L2 x2 x4\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x3\<^esub>)" using preorder_L1 mono_L2 by fast
  qed auto
qed

lemma galois_equivalence_if_mono_if_galois_equivalence_Dep_Fun_Rel_pred_assm_leftI:
  assumes galois_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_L1: "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and refl_R1: "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and mono_L2: "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and mono_R2: "([x1' x2' \<Colon> (\<ge>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x1' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and mono_l2: "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "x \<le>\<^bsub>L1\<^esub> x"
  shows "([in_codom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub>)"
proof (intro Dep_Fun_Rel_predI)
  fix y assume "in_codom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>) y"
  moreover from \<open>x \<le>\<^bsub>L1\<^esub> x\<close> galois_equiv1 refl_L1 have "x \<equiv>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x"
    by (blast intro: bi_related_if_rel_equivalence_on
      t1.rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence)
  moreover with refl_L1 have "\<eta>\<^sub>1 x \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x" by blast
  ultimately have "in_codom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) (\<eta>\<^sub>1 x)\<^esub>) y" using mono_L2 by blast
  moreover from \<open>x \<le>\<^bsub>L1\<^esub> x\<close> galois_equiv1
    have "l1 x \<le>\<^bsub>R1\<^esub> l1 x" "\<eta>\<^sub>1 x \<le>\<^bsub>L1\<^esub> x" "x \<^bsub>L1\<^esub>\<lessapprox> l1 x"
    by (blast intro: t1.left_Galois_left_if_left_relI
      flip.t1.counit_rel_if_right_rel_if_galois_connection)+
  moreover note
    Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_l2 \<open>l1 x \<le>\<^bsub>R1\<^esub> l1 x\<close>] \<open>\<eta>\<^sub>1 x \<le>\<^bsub>L1\<^esub> x\<close>]
  ultimately have "l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y \<le>\<^bsub>R2 (\<epsilon>\<^sub>1 (l1 x)) (l1 x)\<^esub> l2\<^bsub>(l1 x) x\<^esub> y" by auto
  moreover note \<open>l1 x \<le>\<^bsub>R1\<^esub> l1 x\<close>
  moreover with galois_equiv1 refl_R1 have "l1 x \<equiv>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 (l1 x)"
    by (blast intro: bi_related_if_rel_equivalence_on
      flip.t1.rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence)
  ultimately show "l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y \<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub> l2\<^bsub>(l1 x) x\<^esub> y"
    using mono_R2 by blast
qed

lemma galois_equivalence_if_mono_if_galois_equivalence_Dep_Fun_Rel_pred_assm_right:
  assumes galois_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_R1: "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and mono_L2: "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and mono_R2: "([x1' x2' \<Colon> (\<ge>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x1' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and mono_r2: "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "x' \<le>\<^bsub>R1\<^esub> x'"
  shows "([in_dom (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') x'\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>)"
proof (intro Dep_Fun_Rel_predI)
  fix y assume "in_dom (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>) y"
  moreover from \<open>x' \<le>\<^bsub>R1\<^esub> x'\<close> galois_equiv1 refl_R1 have "x' \<equiv>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x'"
    by (blast intro: bi_related_if_rel_equivalence_on
      flip.t1.rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence)
  moreover with refl_R1 have "\<epsilon>\<^sub>1 x' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x'" by blast
  ultimately have "in_dom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') (\<epsilon>\<^sub>1 x')\<^esub>) y" using mono_R2 by blast
  moreover from \<open>x' \<le>\<^bsub>R1\<^esub> x'\<close> galois_equiv1
    have "r1 x' \<le>\<^bsub>L1\<^esub> r1 x'" "x' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x'" "r1 x' \<^bsub>L1\<^esub>\<lessapprox> x'"
    by (blast intro: t1.right_left_Galois_if_right_relI
      flip.t1.rel_unit_if_left_rel_if_galois_connection)+
  moreover note
    Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_r2 \<open>r1 x' \<le>\<^bsub>L1\<^esub> r1 x'\<close>] \<open>x' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x'\<close>]
  ultimately have "r2\<^bsub>(r1 x') x'\<^esub> y \<le>\<^bsub>L2 (r1 x') (\<eta>\<^sub>1 (r1 x'))\<^esub> r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y" by auto
  moreover note \<open>r1 x' \<le>\<^bsub>L1\<^esub> r1 x'\<close>
  moreover with galois_equiv1 refl_R1 have "r1 x' \<equiv>\<^bsub>L1\<^esub> \<eta>\<^sub>1 (r1 x')"
    by (blast intro: bi_related_if_rel_equivalence_on
      t1.rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence)
  ultimately show "r2\<^bsub>(r1 x') x'\<^esub> y \<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub> r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y"
    using mono_L2 by blast
qed

end


paragraph \<open>Monotone Dependent Function Relator\<close>

context transport_Mono_Dep_Fun_Rel
begin

context
begin

interpretation flip : transport_Mono_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2
  rewrites "flip.t1.counit \<equiv> \<eta>\<^sub>1" and "flip.t1.unit \<equiv> \<epsilon>\<^sub>1"
  by (simp_all only: t1.flip_counit_eq_unit t1.flip_unit_eq_counit)

lemma galois_equivalence_if_galois_equivalenceI:
  assumes galois_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_L1: "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and galois_equiv2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow>
    ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>) \<le> (\<le>\<^bsub>L2 x x\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x2' x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>) \<le> (\<le>\<^bsub>R2 x' x'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x1' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x2')\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x1)\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') x'\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
proof -
  from galois_equiv2 have
    "((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<stileturn> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
    "((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>) (l2\<^bsub>x' x\<^esub>)"
    "((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>) (l2\<^bsub>x' x\<^esub>)"
    if "x \<^bsub>L1\<^esub>\<lessapprox> x'" for x x' using \<open>x \<^bsub>L1\<^esub>\<lessapprox> x'\<close>
    by (blast elim: galois.galois_connectionE galois_prop.galois_propE)+
  moreover from galois_equiv1 galois_equiv2 have
    "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
      ((\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
    by (intro tdfr.mono_wrt_rel_left2_if_mono_wrt_rel_left2_if_left_GaloisI) auto
  moreover from galois_equiv1 galois_equiv2 have
    "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
    by (intro tdfr.mono_wrt_rel_right2_if_mono_wrt_rel_right2_if_left_GaloisI)
    (auto elim!: t1.galois_equivalenceE)
  moreover from galois_equiv1 refl_L1 have
    "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> x \<equiv>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x"
    "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> x' \<equiv>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x'"
    by (blast intro!: bi_related_if_rel_equivalence_on
      t1.rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence
      flip.t1.rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence)+
  ultimately show ?thesis using assms
    by (intro galois_equivalenceI
      galois_connection_left_right_if_galois_connectionI flip.galois_prop_left_rightI
      tdfr.flip_half_galois_prop_left2_if_half_galois_prop_left2_if_left_GaloisI
      tdfr.flip_half_galois_prop_right2_if_half_galois_prop_right2_if_GaloisI
      tdfr.mono_wrt_rel_left_if_transitiveI tdfr.mono_wrt_rel_right_if_transitiveI
      flip.tdfr.left_rel_right_if_left_right_rel_le_right2_assmI
      flip.tdfr.left_right_rel_if_left_rel_right_ge_left2_assmI
      tdfr.left_rel2_unit_eqs_left_rel2I
      flip.tdfr.left_rel2_unit_eqs_left_rel2I)
    (auto elim!: t1.galois_equivalenceE
      intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom
      in_field_if_in_codom)
qed

corollary galois_equivalence_if_galois_equivalenceI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>) \<le> (\<le>\<^bsub>L2 x x\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x2' x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>) \<le> (\<le>\<^bsub>R2 x' x'\<^esub>)"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub>)"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') x'\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_equivalence_if_galois_equivalenceI
    tdfr.galois_connection_left_right_if_galois_connection_mono_assms_leftI
    tdfr.galois_connection_left_right_if_galois_connection_mono_assms_rightI
    tdfr.galois_connection_left_right_if_galois_connection_mono_2_assms_leftI
    tdfr.galois_connection_left_right_if_galois_connection_mono_2_assms_rightI)
  (auto intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom
    in_field_if_in_codom)

corollary galois_equivalence_if_mono_if_galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | \<eta>\<^sub>1 x2 \<le>\<^bsub>L1\<^esub> x1] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x2 \<le>\<^bsub>L1\<^esub> x3 \<and> x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3)] \<Rrightarrow> (\<ge>)) L2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | \<epsilon>\<^sub>1 x2' \<le>\<^bsub>R1\<^esub> x1'] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | (x2' \<le>\<^bsub>R1\<^esub> x3' \<and> x4' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x3')] \<Rrightarrow> (\<ge>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub>)"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') x'\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_equivalence_if_galois_equivalenceI'
    tdfr.left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_leftI
    flip.tdfr.left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_leftI
    tdfr.left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_rightI
    flip.tdfr.left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_rightI)
  auto

end

interpretation flip : transport_Mono_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2
  rewrites "flip.t1.counit \<equiv> \<eta>\<^sub>1" and "flip.t1.unit \<equiv> \<epsilon>\<^sub>1"
  by (simp_all only: t1.flip_counit_eq_unit t1.flip_unit_eq_counit)

lemma galois_equivalence_if_mono_if_preorder_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1' x2' \<Colon> (\<ge>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x1' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_equivalence_if_mono_if_galois_equivalenceI
    tdfr.galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI
    flip.tdfr.galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI
    tdfr.galois_equivalence_if_mono_if_galois_equivalence_Dep_Fun_Rel_pred_assm_leftI
    tdfr.galois_equivalence_if_mono_if_galois_equivalence_Dep_Fun_Rel_pred_assm_right)
  auto

theorem galois_equivalence_if_mono_if_preorder_equivalenceI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1' x2' \<Colon> (\<ge>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x1' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_equivalence_if_mono_if_preorder_equivalenceI
    tdfr.transitive_left2_if_preorder_equivalenceI
    tdfr.transitive_right2_if_preorder_equivalenceI)
  auto

end


paragraph \<open>Monotone Function Relator\<close>

context transport_Mono_Fun_Rel
begin

interpretation flip : transport_Mono_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2 .

lemma galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "transitive (\<le>\<^bsub>R2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro tpdfr.galois_equivalenceI
    galois_connection_left_rightI flip.galois_prop_left_rightI)
  (auto intro: reflexive_on_if_le_pred_if_reflexive_on
    in_field_if_in_dom in_field_if_in_codom)

end


end