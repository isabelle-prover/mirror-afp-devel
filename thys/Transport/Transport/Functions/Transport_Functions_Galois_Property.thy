\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Galois Property\<close>
theory Transport_Functions_Galois_Property
  imports
    Transport_Functions_Monotone
begin

paragraph \<open>Dependent Function Relator\<close>

context transport_Dep_Fun_Rel
begin

context
begin

interpretation flip : transport_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2 .

lemma left_right_rel_if_left_rel_rightI:
  assumes mono_r1: "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and half_galois_prop_left1: "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_R1: "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and half_galois_prop_left2: "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ((\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)) (l2\<^bsub> x' (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
  and R2_le1: "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) \<le> (\<le>\<^bsub>R2 x' x'\<^esub>)"
  and R2_le2: "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and ge_L2_r2_le2: "\<And>x' y'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y') \<le> (\<ge>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub> y')"
  and trans_R2: "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "g \<le>\<^bsub>R\<^esub> g"
  and "f \<le>\<^bsub>L\<^esub> r g"
  shows "l f \<le>\<^bsub>R\<^esub> g"
proof (rule flip.left_relI)
  fix x1' x2'
  assume [iff]: "x1' \<le>\<^bsub>R1\<^esub> x2'"
  with refl_R1 have [iff]: "x1' \<le>\<^bsub>R1\<^esub> x1'" by auto
  with mono_r1 half_galois_prop_left1 have [iff]: "\<epsilon>\<^sub>1 x1' \<le>\<^bsub>R1\<^esub> x1'"
    by (intro t1.counit_rel_if_right_rel_if_half_galois_prop_left_if_mono_wrt_rel)
  with refl_R1 have "\<epsilon>\<^sub>1 x1' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x1'" by blast
  with \<open>g \<le>\<^bsub>R\<^esub> g\<close> have "g (\<epsilon>\<^sub>1 x1') \<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') (\<epsilon>\<^sub>1 x1')\<^esub> g (\<epsilon>\<^sub>1 x1')" by blast
  with R2_le2 have "g (\<epsilon>\<^sub>1 x1') \<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x1'\<^esub> g (\<epsilon>\<^sub>1 x1')" by blast

  let ?x1 = "r1 x1'"
  from \<open>f \<le>\<^bsub>L\<^esub> r g\<close> \<open>x1' \<le>\<^bsub>R1\<^esub> x1'\<close> have "f ?x1 \<le>\<^bsub>L2 ?x1 ?x1\<^esub> r g ?x1" using mono_r1 by blast
  then have "f ?x1 \<le>\<^bsub>L2 ?x1 ?x1\<^esub> r2\<^bsub>?x1 (\<epsilon>\<^sub>1 x1')\<^esub> (g (\<epsilon>\<^sub>1 x1'))" by simp
  with ge_L2_r2_le2 have "f ?x1 \<le>\<^bsub>L2 ?x1 ?x1\<^esub> r2\<^bsub>?x1 x1'\<^esub> (g (\<epsilon>\<^sub>1 x1'))"
    using \<open>_ \<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x1'\<^esub> g (\<epsilon>\<^sub>1 x1')\<close> by blast
  with half_galois_prop_left2 have "l2\<^bsub> x1' ?x1\<^esub> (f ?x1) \<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x1'\<^esub> g (\<epsilon>\<^sub>1 x1')"
    using \<open>_ \<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x1'\<^esub> g (\<epsilon>\<^sub>1 x1')\<close> by auto
  moreover from \<open>g \<le>\<^bsub>R\<^esub> g\<close> \<open>\<epsilon>\<^sub>1 x1' \<le>\<^bsub>R1\<^esub> x1'\<close> have "... \<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x1'\<^esub> g x1'" by blast
  ultimately have "l2\<^bsub> x1' ?x1\<^esub> (f ?x1) \<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x1'\<^esub> g x1'" using trans_R2 by blast
  with R2_le1 R2_le2 have "l2\<^bsub> x1' ?x1\<^esub> (f ?x1) \<le>\<^bsub>R2 x1' x2'\<^esub> g x1'" by blast
  moreover from \<open>g \<le>\<^bsub>R\<^esub> g\<close> \<open>x1' \<le>\<^bsub>R1\<^esub> x2'\<close> have "... \<le>\<^bsub>R2 x1' x2'\<^esub> g x2'" by blast
  ultimately have "l2\<^bsub> x1' ?x1\<^esub> (f ?x1) \<le>\<^bsub>R2 x1' x2'\<^esub> g x2'" using trans_R2 by blast
  then show "l f x1' \<le>\<^bsub>R2 x1' x2'\<^esub> g x2'" by simp
qed

lemma left_right_rel_if_left_rel_right_ge_left2_assmI:
  assumes mono_r1: "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "([in_codom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>))
    (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "x' \<le>\<^bsub>R1\<^esub> x'"
  and "in_codom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) y'"
  shows "(\<ge>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y') \<le> (\<ge>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub> y')"
  using dep_mono_wrt_relD[OF mono_r1 \<open>x' \<le>\<^bsub>R1\<^esub> x'\<close>] assms(2-4,6)
  by (blast dest!: t1.half_galois_prop_leftD)

interpretation flip_inv :
  transport_Dep_Fun_Rel "(\<ge>\<^bsub>R1\<^esub>)" "(\<ge>\<^bsub>L1\<^esub>)" r1 l1 "flip2 R2" "flip2 L2" r2 l2
  rewrites "flip_inv.L \<equiv> (\<ge>\<^bsub>R\<^esub>)" and "flip_inv.R \<equiv> (\<ge>\<^bsub>L\<^esub>)"
  and "flip_inv.t1.counit \<equiv> \<eta>\<^sub>1"
  and "\<And>R x y. (flip2 R x y)\<inverse> \<equiv> R y x"
  and "\<And>R. in_dom R\<inverse> \<equiv> in_codom R"
  and "\<And>R x1 x2. in_codom (flip2 R x1 x2) \<equiv> in_dom (R x2 x1)"
  and "\<And>R S. (R\<inverse> \<Rrightarrow>\<^sub>m S\<inverse>) \<equiv> (R \<Rrightarrow>\<^sub>m S)"
  and "\<And>R S x1 x2 x1' x2'. (flip2 R x1 x2 \<^sub>h\<unlhd> flip2 S x1' x2') \<equiv> (S x2' x1' \<unlhd>\<^sub>h R x2 x1)\<inverse>"
  and "\<And>R S. (R\<inverse> \<^sub>h\<unlhd> S\<inverse>) \<equiv> (S \<unlhd>\<^sub>h R)\<inverse>"
  and "\<And>x1 x2 x3 x4. flip2 L2 x1 x2 \<le> flip2 L2 x3 x4 \<equiv> (\<le>\<^bsub>L2 x2 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x4 x3\<^esub>)"
  and "\<And>(R :: 'z \<Rightarrow> _) (P :: 'z \<Rightarrow> bool). reflexive_on P R\<inverse> \<equiv> reflexive_on P R"
  and "\<And>R x1 x2. transitive (flip2 R x1 x2) \<equiv> transitive (R x2 x1)"
  and "\<And>x x. ([in_dom (\<le>\<^bsub>L2 x' \<eta>\<^sub>1 x'\<^esub>)] \<Rrightarrow> flip2 R2 (l1 x') (l1 x'))
    \<equiv> ([in_dom (\<le>\<^bsub>L2 x' \<eta>\<^sub>1 x'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x') (l1 x')\<^esub>))\<inverse>"
  by (simp_all add: flip_inv_left_eq_ge_right flip_inv_right_eq_ge_left
    t1.flip_counit_eq_unit
    galois_prop.rel_inv_half_galois_prop_right_eq_half_galois_prop_left_rel_inv)

lemma left_rel_right_if_left_right_relI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> ((\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (r2\<^bsub>x (l1 x)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) \<le> (\<le>\<^bsub>L2 x x\<^esub>)"
  and "\<And>x y. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> in_dom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) y \<Longrightarrow>
    (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y) \<le> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub> y)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "f \<le>\<^bsub>L\<^esub> f"
  and "l f \<le>\<^bsub>R\<^esub> g"
  shows "f \<le>\<^bsub>L\<^esub> r g"
  using assms
  by (intro flip_inv.left_right_rel_if_left_rel_rightI[simplified rel_inv_iff_rel])

lemma left_rel_right_if_left_right_rel_le_right2_assmI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>))\<inverse> r1 l1"
  and "([in_dom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "x \<le>\<^bsub>L1\<^esub> x"
  and "in_dom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) y"
  shows "(\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y) \<le> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub> y)"
  using assms by (intro flip_inv.left_right_rel_if_left_rel_right_ge_left2_assmI
    [simplified rel_inv_iff_rel])
  auto

end

lemma left_rel_right_iff_left_right_relI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ((\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)) (l2\<^bsub> x' (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> ((\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (r2\<^bsub>x (l1 x)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) \<le> (\<le>\<^bsub>L2 x x\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) \<le> (\<le>\<^bsub>R2 x' x'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x y. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> in_dom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) y \<Longrightarrow>
    (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y) \<le> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub> y)"
  and "\<And>x' y'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y') \<le> (\<ge>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub> y')"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "f \<le>\<^bsub>L\<^esub> f"
  and "g \<le>\<^bsub>R\<^esub> g"
  shows "f \<le>\<^bsub>L\<^esub> r g \<longleftrightarrow> l f \<le>\<^bsub>R\<^esub> g"
  using assms by (intro iffI left_right_rel_if_left_rel_rightI)
  (auto intro!: left_rel_right_if_left_right_relI)

lemma half_galois_prop_left2_if_half_galois_prop_left2_if_left_GaloisI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "x' \<le>\<^bsub>R1\<^esub> x'"
  shows "((\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)) (l2\<^bsub> x' (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
  using assms by (auto intro: t1.right_left_Galois_if_right_relI)

lemma half_galois_prop_right2_if_half_galois_prop_right2_if_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "x \<le>\<^bsub>L1\<^esub> x"
  shows "((\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (r2\<^bsub>x (l1 x)\<^esub>)"
  by (auto intro!: assms t1.left_Galois_left_if_left_relI)

lemma left_rel_right_iff_left_right_relI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and galois_prop2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow>
    ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<unlhd> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) \<le> (\<le>\<^bsub>L2 x x\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) \<le> (\<le>\<^bsub>R2 x' x'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "f \<le>\<^bsub>L\<^esub> f"
  and "g \<le>\<^bsub>R\<^esub> g"
  shows "f \<le>\<^bsub>L\<^esub> r g \<longleftrightarrow> l f \<le>\<^bsub>R\<^esub> g"
proof -
  from galois_prop2 have
    "((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
    "((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
    if "x \<^bsub>L1\<^esub>\<lessapprox> x'" for x x'
    using \<open>x \<^bsub>L1\<^esub>\<lessapprox> x'\<close> by blast+
  with assms show ?thesis
    by (intro left_rel_right_iff_left_right_relI
      left_right_rel_if_left_rel_right_ge_left2_assmI
      left_rel_right_if_left_right_rel_le_right2_assmI
      half_galois_prop_left2_if_half_galois_prop_left2_if_left_GaloisI
      half_galois_prop_right2_if_half_galois_prop_right2_if_left_GaloisI)
    auto
qed

lemma left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_leftI:
  assumes galois_conn1: "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_L1: "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and antimono_L2:
    "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x2 \<le>\<^bsub>L1\<^esub> x3 \<and> x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3)] \<Rrightarrow> (\<ge>)) L2"
  shows "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
proof -
  fix x1 x2 assume "x1 \<le>\<^bsub>L1\<^esub> x2"
  with galois_conn1 refl_L1 have "x1 \<le>\<^bsub>L1\<^esub> x1" "x2 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2"
    by (blast intro:
      t1.rel_unit_if_left_rel_if_half_galois_prop_right_if_mono_wrt_rel)+
  moreover with refl_L1 have "x2 \<le>\<^bsub>L1\<^esub> x2" "\<eta>\<^sub>1 x2 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2" by auto
  moreover note dep_mono_wrt_relD[OF antimono_L2 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close>]
    and dep_mono_wrt_relD[OF antimono_L2 \<open>x1 \<le>\<^bsub>L1\<^esub> x1\<close>]
  ultimately show "(\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)" "(\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
    using \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> by auto
qed

lemma left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_rightI:
  assumes galois_conn1: "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_R1: "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and mono_R2:
    "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | \<epsilon>\<^sub>1 x2' \<le>\<^bsub>R1\<^esub> x1'] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  shows "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
proof -
  fix x1' x2' assume "x1' \<le>\<^bsub>R1\<^esub> x2'"
  with galois_conn1 refl_R1 have "x2' \<le>\<^bsub>R1\<^esub> x2'" "\<epsilon>\<^sub>1 x1' \<le>\<^bsub>R1\<^esub> x1'"
    by (blast intro:
      t1.counit_rel_if_right_rel_if_half_galois_prop_left_if_mono_wrt_rel)+
  moreover with refl_R1 have "x1' \<le>\<^bsub>R1\<^esub> x1'" "\<epsilon>\<^sub>1 x1' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x1'" by auto
  moreover note dep_mono_wrt_relD[OF mono_R2 \<open>\<epsilon>\<^sub>1 x1' \<le>\<^bsub>R1\<^esub> x1'\<close>]
    and dep_mono_wrt_relD[OF mono_R2 \<open>x1' \<le>\<^bsub>R1\<^esub> x1'\<close>]
  ultimately show "(\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)" "(\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
    using \<open>x1' \<le>\<^bsub>R1\<^esub> x2'\<close> by auto
qed

corollary left_rel_right_iff_left_right_rel_if_monoI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<unlhd> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x2 \<le>\<^bsub>L1\<^esub> x3 \<and> x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3)] \<Rrightarrow> (\<ge>)) L2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | \<epsilon>\<^sub>1 x2' \<le>\<^bsub>R1\<^esub> x1'] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "f \<le>\<^bsub>L\<^esub> f"
  and "g \<le>\<^bsub>R\<^esub> g"
  shows "f \<le>\<^bsub>L\<^esub> r g \<longleftrightarrow> l f \<le>\<^bsub>R\<^esub> g"
  using assms by (intro left_rel_right_iff_left_right_relI'
    left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_leftI
    left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_rightI)
  (auto intro: reflexive_on_if_le_pred_if_reflexive_on
    in_field_if_in_dom in_field_if_in_codom)

end


paragraph \<open>Function Relator\<close>

context transport_Fun_Rel
begin

corollary left_right_rel_if_left_rel_rightI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "transitive (\<le>\<^bsub>R2\<^esub>)"
  and "g \<le>\<^bsub>R\<^esub> g"
  and "f \<le>\<^bsub>L\<^esub> r g"
  shows "l f \<le>\<^bsub>R\<^esub> g"
  using assms by (intro tdfr.left_right_rel_if_left_rel_rightI) simp_all

corollary left_rel_right_if_left_right_relI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "f \<le>\<^bsub>L\<^esub> f"
  and "l f \<le>\<^bsub>R\<^esub> g"
  shows "f \<le>\<^bsub>L\<^esub> r g"
  using assms by (intro tdfr.left_rel_right_if_left_right_relI) simp_all

corollary left_rel_right_iff_left_right_relI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<unlhd> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "transitive (\<le>\<^bsub>R2\<^esub>)"
  and "f \<le>\<^bsub>L\<^esub> f"
  and "g \<le>\<^bsub>R\<^esub> g"
  shows "f \<le>\<^bsub>L\<^esub> r g \<longleftrightarrow> l f \<le>\<^bsub>R\<^esub> g"
  using assms by (intro tdfr.left_rel_right_iff_left_right_relI) auto

end


paragraph \<open>Monotone Dependent Function Relator\<close>

context transport_Mono_Dep_Fun_Rel
begin

lemma half_galois_prop_left_left_rightI:
  assumes "(tdfr.L \<Rrightarrow>\<^sub>m tdfr.R) l"
  and "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ((\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)) (l2\<^bsub> x' (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) \<le> (\<le>\<^bsub>R2 x' x'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x' y'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y') \<le> (\<ge>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub> y')"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  unfolding left_rel_eq_tdfr_left_Refl_Rel right_rel_eq_tdfr_right_Refl_Rel using assms
  by (intro
    half_galois_prop_leftI[unfolded left_rel_eq_tdfr_left_Refl_Rel right_rel_eq_tdfr_right_Refl_Rel]
    Refl_Rel_app_leftI[where ?f=l]
    tdfr.left_right_rel_if_left_rel_rightI)
  (auto elim!: galois_rel.left_GaloisE)

lemma half_galois_prop_right_left_rightI:
  assumes "(tdfr.R \<Rrightarrow>\<^sub>m tdfr.L) r"
  and "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> ((\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (r2\<^bsub>x (l1 x)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) \<le> (\<le>\<^bsub>L2 x x\<^esub>)"
  and "\<And>x y. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> in_dom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) y \<Longrightarrow>
    (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y) \<le> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub> y)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  unfolding left_rel_eq_tdfr_left_Refl_Rel right_rel_eq_tdfr_right_Refl_Rel using assms
  by (intro
    half_galois_prop_rightI[unfolded left_rel_eq_tdfr_left_Refl_Rel right_rel_eq_tdfr_right_Refl_Rel]
    Refl_Rel_app_rightI[where ?f=r]
    tdfr.left_rel_right_if_left_right_relI)
  (auto elim!: galois_rel.left_GaloisE in_codomE Refl_RelE intro!: in_fieldI)

corollary galois_prop_left_rightI:
  assumes "(tdfr.L \<Rrightarrow>\<^sub>m tdfr.R) l" and "(tdfr.R \<Rrightarrow>\<^sub>m tdfr.L) r"
  and "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ((\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)) (l2\<^bsub> x' (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> ((\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (r2\<^bsub>x (l1 x)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) \<le> (\<le>\<^bsub>L2 x x\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) \<le> (\<le>\<^bsub>R2 x' x'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x y. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> in_dom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) y \<Longrightarrow>
    (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y) \<le> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub> y)"
  and "\<And>x' y'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y') \<le> (\<ge>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub> y')"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_propI half_galois_prop_left_left_rightI
    half_galois_prop_right_left_rightI)
  auto

corollary galois_prop_left_rightI':
  assumes "(tdfr.L \<Rrightarrow>\<^sub>m tdfr.R) l" and "(tdfr.R \<Rrightarrow>\<^sub>m tdfr.L) r"
  and "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and galois_prop2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow>
    ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<unlhd> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) \<le> (\<le>\<^bsub>L2 x x\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) \<le> (\<le>\<^bsub>R2 x' x'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
proof -
  from galois_prop2 have
    "((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
    "((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
    if "x \<^bsub>L1\<^esub>\<lessapprox> x'" for x x'
    using \<open>x \<^bsub>L1\<^esub>\<lessapprox> x'\<close> by blast+
  with assms show ?thesis by (intro galois_prop_left_rightI
    tdfr.left_right_rel_if_left_rel_right_ge_left2_assmI
    tdfr.left_rel_right_if_left_right_rel_le_right2_assmI
    tdfr.half_galois_prop_left2_if_half_galois_prop_left2_if_left_GaloisI
    tdfr.half_galois_prop_right2_if_half_galois_prop_right2_if_left_GaloisI)
    auto
qed

corollary galois_prop_left_right_if_mono_if_galois_propI:
  assumes "(tdfr.L \<Rrightarrow>\<^sub>m tdfr.R) l" and "(tdfr.R \<Rrightarrow>\<^sub>m tdfr.L) r"
  and "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<unlhd> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x2 \<le>\<^bsub>L1\<^esub> x3 \<and> x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3)] \<Rrightarrow> (\<ge>)) L2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | \<epsilon>\<^sub>1 x2' \<le>\<^bsub>R1\<^esub> x1'] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_prop_left_rightI'
    tdfr.left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_leftI
    tdfr.left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_rightI)
  (auto intro: reflexive_on_if_le_pred_if_reflexive_on
    in_field_if_in_dom in_field_if_in_codom)

text \<open>Note that we could further rewrite
@{thm "galois_prop_left_right_if_mono_if_galois_propI"},
as we will do later for Galois connections, by applying
@{thm "tdfr.mono_wrt_rel_leftI"} and @{thm "tdfr.mono_wrt_rel_rightI"} to the
first premises. However, this is not really helpful here.
Moreover, the resulting theorem will not result in a
useful lemma for the flipped instance of @{locale transport_Dep_Fun_Rel}
since @{thm "tdfr.mono_wrt_rel_leftI"} and @{thm "tdfr.mono_wrt_rel_rightI"} are
not flipped dual but only flipped-inversed dual.\<close>

end


paragraph \<open>Monotone Function Relator\<close>

context transport_Mono_Fun_Rel
begin

lemma half_galois_prop_left_left_rightI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "((\<le>\<^bsub>L2\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "transitive (\<le>\<^bsub>R2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms
  by (intro tpdfr.half_galois_prop_left_left_rightI tfr.mono_wrt_rel_leftI)
  simp_all

interpretation flip : transport_Mono_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2 .

lemma half_galois_prop_right_left_rightI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2"
  and "((\<le>\<^bsub>L2\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  using assms
  by (intro tpdfr.half_galois_prop_right_left_rightI flip.tfr.mono_wrt_rel_leftI)
  simp_all

corollary galois_prop_left_rightI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<stileturn> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "transitive (\<le>\<^bsub>R2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro tpdfr.galois_propI
    half_galois_prop_left_left_rightI half_galois_prop_right_left_rightI)
  auto

end


end