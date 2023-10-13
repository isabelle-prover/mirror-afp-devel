\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Monotonicity\<close>
theory Transport_Functions_Monotone
  imports
    Transport_Functions_Base
begin

paragraph \<open>Dependent Function Relator\<close>

context transport_Dep_Fun_Rel
begin

interpretation flip : transport_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2 .

lemma mono_wrt_rel_leftI:
  assumes mono_r1: "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and mono_l2: "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ((\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
  and R2_le1: "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and R2_l2_le1: "\<And>x1' x2' y. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) y \<Longrightarrow>
    (\<le>\<^bsub>R2 x1' x2'\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub> y) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>) (l2\<^bsub>x1' (r1 x1')\<^esub> y)"
  and ge_R2_l2_le2: "\<And>x1' x2' y. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> in_codom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) y \<Longrightarrow>
    (\<ge>\<^bsub>R2 x1' x2'\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub> y) \<le> (\<ge>\<^bsub>R2 x1' x2'\<^esub>) (l2\<^bsub>x2' (r1 x2')\<^esub> y)"
  shows "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
proof (intro dep_mono_wrt_relI flip.left_relI)
  fix f1 f2 x1' x2' assume [iff]: "x1' \<le>\<^bsub>R1\<^esub> x2'"
  with mono_r1 have "r1 x1' \<le>\<^bsub>L1\<^esub> r1 x2'" (is "?x1 \<le>\<^bsub>L1\<^esub> ?x2") by blast
  moreover assume "f1 \<le>\<^bsub>L\<^esub> f2"
  ultimately have "f1 ?x1 \<le>\<^bsub>L2 ?x1 ?x2\<^esub> f2 ?x2" (is "?y1 \<le>\<^bsub>L2 ?x1 ?x2\<^esub> ?y2") by blast
  with mono_l2 have "l2\<^bsub>x2' ?x1\<^esub> ?y1 \<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub> l2\<^bsub>x2' ?x1\<^esub> ?y2" by blast
  with R2_le1 have "l2\<^bsub>x2' ?x1\<^esub> ?y1 \<le>\<^bsub>R2 x1' x2'\<^esub> l2\<^bsub>x2' ?x1\<^esub> ?y2" by blast
  with R2_l2_le1 have "l2\<^bsub>x1' ?x1\<^esub> ?y1 \<le>\<^bsub>R2 x1' x2'\<^esub> l2\<^bsub>x2' ?x1\<^esub> ?y2"
    using \<open>?y1 \<le>\<^bsub>L2 ?x1 ?x2\<^esub> _\<close>  by blast
  with ge_R2_l2_le2 have "l2\<^bsub>x1' ?x1\<^esub> ?y1 \<le>\<^bsub>R2 x1' x2'\<^esub> l2\<^bsub>x2' ?x2\<^esub> ?y2"
    using \<open>_ \<le>\<^bsub>L2 ?x1 ?x2\<^esub> ?y2\<close>  by blast
  then show "l f1 x1' \<le>\<^bsub>R2 x1' x2'\<^esub> l f2 x2'" by simp
qed

lemma mono_wrt_rel_left_in_dom_mono_left_assm:
  assumes "([in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>))
    (l2\<^bsub>x1' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
  and "transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "x1' \<le>\<^bsub>R1\<^esub> x2'"
  and "in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) y"
  shows "(\<le>\<^bsub>R2 x1' x2'\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub> y) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>) (l2\<^bsub>x1' (r1 x1')\<^esub> y)"
  using assms by blast

lemma mono_wrt_rel_left_in_codom_mono_left_assm:
  assumes "([in_codom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>))
    (l2\<^bsub>x2' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x2')\<^esub>)"
  and "transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "x1' \<le>\<^bsub>R1\<^esub> x2'"
  and "in_codom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) y"
  shows "(\<ge>\<^bsub>R2 x1' x2'\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub> y) \<le> (\<ge>\<^bsub>R2 x1' x2'\<^esub>) (l2\<^bsub>x2' (r1 x2')\<^esub> y)"
  using assms by blast

lemma mono_wrt_rel_left_if_transitiveI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ((\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x1' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x2')\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  using assms by (intro mono_wrt_rel_leftI
    mono_wrt_rel_left_in_dom_mono_left_assm
    mono_wrt_rel_left_in_codom_mono_left_assm)
  auto

lemma mono_wrt_rel_left2_if_mono_wrt_rel_left2_if_left_GaloisI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>)"
  shows "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ((\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
  using assms by (intro dep_mono_wrt_relI) fastforce

interpretation flip_inv :
  transport_Dep_Fun_Rel "(\<ge>\<^bsub>R1\<^esub>)" "(\<ge>\<^bsub>L1\<^esub>)" r1 l1 "flip2 R2" "flip2 L2" r2 l2
  rewrites "flip_inv.R \<equiv> (\<ge>\<^bsub>L\<^esub>)" and "flip_inv.L \<equiv> (\<ge>\<^bsub>R\<^esub>)"
  and "flip_inv.t1.counit \<equiv> \<eta>\<^sub>1"
  and "\<And>R x y. (flip2 R x y)\<inverse> \<equiv> R y x"
  and "\<And>R x1 x2. in_dom (flip2 R x1 x2) \<equiv> in_codom (R x2 x1)"
  and "\<And>R x1 x2. in_codom (flip2 R x1 x2) \<equiv> in_dom (R x2 x1)"
  and "\<And>R S. (R\<inverse> \<Rrightarrow>\<^sub>m S\<inverse>) \<equiv> (R \<Rrightarrow>\<^sub>m S)"
  and "\<And>x1 x2 x1' x2'. (flip2 R2 x1' x2' \<Rrightarrow>\<^sub>m flip2 L2 x1 x2) \<equiv>
    ((\<le>\<^bsub>R2 x2' x1'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x2 x1\<^esub>))"
  and "\<And>x1 x2 x3 x4. flip2 L2 x1 x2 \<le> flip2 L2 x3 x4 \<equiv> (\<le>\<^bsub>L2 x2 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x4 x3\<^esub>)"
  and "\<And>x1' x2' y1 y2.
    flip_inv.dfro2.right_infix y1 x1' x2' \<le> flip_inv.dfro2.right_infix y2 x1' x2' \<equiv>
      (\<ge>\<^bsub>L2 x2' x1'\<^esub>) y1 \<le> (\<ge>\<^bsub>L2 x2' x1'\<^esub>) y2"
  and "\<And>P x1 x2. ([P] \<Rrightarrow> flip2 L2 x1 x2) \<equiv> ([P] \<Rrightarrow> (\<ge>\<^bsub>L2 x2 x1\<^esub>))"
  and "\<And>P R. ([P] \<Rrightarrow> R\<inverse>) \<equiv> ([P] \<Rrightarrow> R)\<inverse>"
  and "\<And>x1 x2. transitive (flip2 L2 x1 x2) \<equiv> transitive (\<le>\<^bsub>L2 x2 x1\<^esub>)"
  by (simp_all add: flip_inv_left_eq_ge_right flip_inv_right_eq_ge_left
    t1.flip_counit_eq_unit del: rel_inv_iff_rel)

lemma mono_wrt_rel_rightI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2 y'. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub> y')"
  and "\<And>x1 x2 y'. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y' \<Longrightarrow>
    (\<le>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x1)\<^esub> y')"
  shows "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  using assms by (intro flip_inv.mono_wrt_rel_leftI[simplified rel_inv_iff_rel])

lemma mono_wrt_rel_right_if_transitiveI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x1)\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  shows "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  using assms by (intro flip_inv.mono_wrt_rel_left_if_transitiveI
    [simplified rel_inv_iff_rel])

lemma mono_wrt_rel_right2_if_mono_wrt_rel_right2_if_left_GaloisI:
  assumes assms1: "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1" "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and mono_r2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  shows "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
proof -
  show "((\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>)" if "x1 \<le>\<^bsub>L1\<^esub> x2" for x1 x2
  proof -
    from \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have "x1 \<^bsub>L1\<^esub>\<lessapprox> l1 x2"
      using assms1 by (intro t1.left_Galois_left_if_left_relI) blast
    with mono_r2 show ?thesis by auto
  qed
qed

end


paragraph \<open>Function Relator\<close>

context transport_Fun_Rel
begin

lemma mono_wrt_rel_leftI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  shows "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  using assms by (intro tdfr.mono_wrt_rel_leftI) simp_all

end


paragraph \<open>Monotone Dependent Function Relator\<close>

context transport_Mono_Dep_Fun_Rel
begin

lemmas mono_wrt_rel_leftI = mono_wrt_rel_Refl_Rel_Refl_Rel_if_mono_wrt_rel
  [of tdfr.L tdfr.R l, folded transport_defs]

end

paragraph \<open>Monotone Function Relator\<close>

context transport_Mono_Fun_Rel
begin

lemmas mono_wrt_rel_leftI = tpdfr.mono_wrt_rel_leftI[OF tfr.mono_wrt_rel_leftI]

end


end