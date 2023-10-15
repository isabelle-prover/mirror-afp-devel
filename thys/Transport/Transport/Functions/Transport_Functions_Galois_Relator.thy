\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Galois Relator\<close>
theory Transport_Functions_Galois_Relator
  imports
    Transport_Functions_Relation_Simplifications
begin

paragraph \<open>Dependent Function Relator\<close>

context transport_Dep_Fun_Rel
begin

interpretation flip : transport_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2
  rewrites "flip.t1.counit \<equiv> \<eta>\<^sub>1" by (simp only: t1.flip_counit_eq_unit)

lemma Dep_Fun_Rel_left_Galois_if_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_L1: "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and mono_r2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and L2_le2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and ge_L2_r2_le2: "\<And>x x' y'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> in_dom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x (l1 x)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x x'\<^esub> y')"
  and trans_L2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "g \<le>\<^bsub>R\<^esub> g"
  and "f \<^bsub>L\<^esub>\<lessapprox> g"
  shows "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
proof (intro Dep_Fun_Rel_relI)
  fix x x' assume "x \<^bsub>L1\<^esub>\<lessapprox> x'"
  show "f x \<^bsub>L2 x x'\<^esub>\<lessapprox> g x'"
  proof (intro t2.left_GaloisI)
    from \<open>x \<^bsub>L1\<^esub>\<lessapprox> x'\<close> \<open>((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1\<close> have "x \<le>\<^bsub>L1\<^esub> r1 x'" "l1 x \<le>\<^bsub>R1\<^esub> x'" by auto
    with \<open>g \<le>\<^bsub>R\<^esub> g\<close> have "g (l1 x) \<le>\<^bsub>R2 (l1 x) x'\<^esub> g x'" by blast
    then show "in_codom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>) (g x')" by blast

    from \<open>f \<^bsub>L\<^esub>\<lessapprox> g\<close> have "f \<le>\<^bsub>L\<^esub> r g" by blast
    moreover from refl_L1 \<open>x \<^bsub>L1\<^esub>\<lessapprox> x'\<close> have "x \<le>\<^bsub>L1\<^esub> x" by blast
    ultimately have "f x \<le>\<^bsub>L2 x x\<^esub> (r g) x" by blast
    with L2_le2 \<open>x \<le>\<^bsub>L1\<^esub> r1 x'\<close> have "f x \<le>\<^bsub>L2 x (r1 x')\<^esub> (r g) x" by blast
    then have "f x \<le>\<^bsub>L2 x (r1 x')\<^esub> r2\<^bsub>x (l1 x)\<^esub> (g (l1 x))" by simp
    with ge_L2_r2_le2 have "f x \<le>\<^bsub>L2 x (r1 x')\<^esub> r2\<^bsub>x x'\<^esub> (g (l1 x))"
      using \<open>x \<^bsub>L1\<^esub>\<lessapprox> x'\<close> \<open>g (l1 x) \<le>\<^bsub>R2 (l1 x) x'\<^esub> _\<close> by blast
    moreover have "... \<le>\<^bsub>L2 x (r1 x')\<^esub> r2\<^bsub>x x'\<^esub> (g x')"
      using mono_r2 \<open>x \<^bsub>L1\<^esub>\<lessapprox> x'\<close> \<open>g (l1 x) \<le>\<^bsub>R2 (l1 x) x'\<^esub> g x'\<close> by blast
    ultimately show "f x \<le>\<^bsub>L2 x (r1 x')\<^esub> r2\<^bsub>x x'\<^esub> (g x')"
      using trans_L2 \<open>x \<^bsub>L1\<^esub>\<lessapprox> x'\<close> by blast
  qed
qed

lemma left_rel_right_if_Dep_Fun_Rel_left_GaloisI:
  assumes mono_l1: "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and half_galois_prop_right1: "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and L2_unit_le2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and ge_L2_r2_le1: "\<And>x1 x2 y'. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub> y')"
  and rel_f_g: "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  shows "f \<le>\<^bsub>L\<^esub> r g"
proof (intro left_relI)
  fix x1 x2 assume "x1 \<le>\<^bsub>L1\<^esub> x2"
  with mono_l1 half_galois_prop_right1 have "x1 \<^bsub>L1\<^esub>\<lessapprox> l1 x2"
    by (intro t1.left_Galois_left_if_left_relI) auto
  with rel_f_g have "f x1 \<^bsub>L2 x1 (l1 x2)\<^esub>\<lessapprox> g (l1 x2)" by blast
  then have "in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) (g (l1 x2))"
    "f x1 \<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub> r2\<^bsub>x1 (l1 x2)\<^esub> (g (l1 x2))" by auto
  with L2_unit_le2 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have "f x1 \<le>\<^bsub>L2 x1 x2\<^esub> r2\<^bsub>x1 (l1 x2)\<^esub> (g (l1 x2))" by blast
  with ge_L2_r2_le1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> \<open>in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) (g (l1 x2))\<close>
    have "f x1 \<le>\<^bsub>L2 x1 x2\<^esub> r2\<^bsub>x2 (l1 x2)\<^esub> (g (l1 x2))" by blast
  then show "f x1 \<le>\<^bsub>L2 x1 x2\<^esub> r g x2" by simp
qed

lemma left_Galois_if_Dep_Fun_Rel_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2 y'. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub> y')"
  and "in_codom (\<le>\<^bsub>R\<^esub>) g"
  and "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g"
  using assms by (intro left_GaloisI left_rel_right_if_Dep_Fun_Rel_left_GaloisI) auto

lemma left_right_rel_if_Dep_Fun_Rel_left_GaloisI:
  assumes mono_r1: "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and half_galois_prop_left2: "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ((\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>) (r2\<^bsub>(r1 x1') x2'\<^esub>)"
  and R2_le1: "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and R2_l2_le1: "\<And>x1' x2' y. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) y \<Longrightarrow>
    (\<le>\<^bsub>R2 x1' x2'\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub> y) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>) (l2\<^bsub>x1' (r1 x1')\<^esub> y)"
  and rel_f_g: "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  shows "l f \<le>\<^bsub>R\<^esub> g"
proof (rule flip.left_relI)
  fix x1' x2' assume "x1' \<le>\<^bsub>R1\<^esub> x2'"
  with mono_r1 have "r1 x1' \<^bsub>L1\<^esub>\<lessapprox> x2'" by blast
  with rel_f_g have "f (r1 x1') \<^bsub>L2 (r1 x1') x2'\<^esub>\<lessapprox> g x2'" by blast
  with half_galois_prop_left2[OF \<open>x1' \<le>\<^bsub>R1\<^esub> x2'\<close>]
    have "l2\<^bsub>x2' (r1 x1')\<^esub> (f (r1 x1')) \<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub> g x2'" by auto
  with R2_le1 \<open>x1' \<le>\<^bsub>R1\<^esub> x2'\<close> have "l2\<^bsub>x2' (r1 x1')\<^esub> (f (r1 x1')) \<le>\<^bsub>R2 x1' x2'\<^esub> g x2'"
    by blast
  with R2_l2_le1 \<open>x1' \<le>\<^bsub>R1\<^esub> x2'\<close> \<open>f (r1 x1') \<^bsub>L2 (r1 x1') x2'\<^esub>\<lessapprox> _\<close>
    have "l2\<^bsub>x1' (r1 x1')\<^esub> (f (r1 x1')) \<le>\<^bsub>R2 x1' x2'\<^esub> g x2'" by blast
  then show "l f x1' \<le>\<^bsub>R2 x1' x2'\<^esub> g x2'" by simp
qed

lemma left_Galois_if_Dep_Fun_Rel_left_GaloisI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1" and "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ((\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>) (r2\<^bsub>(r1 x1') x2'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1 x2 y'. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub> y')"
  and "\<And>x1' x2' y. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) y \<Longrightarrow>
    (\<le>\<^bsub>R2 x1' x2'\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub> y) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>) (l2\<^bsub>x1' (r1 x1')\<^esub> y)"
  and "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g"
  using assms by (intro left_Galois_if_Dep_Fun_Rel_left_GaloisI in_codomI[where ?x="l f"])
  (auto intro!: left_right_rel_if_Dep_Fun_Rel_left_GaloisI)

lemma left_Galois_iff_Dep_Fun_Rel_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2 y'. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub> y')"
  and "\<And>x x' y'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> in_dom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x (l1 x)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x x'\<^esub> y')"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "g \<le>\<^bsub>R\<^esub> g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms by (intro iffI)
  (auto intro!: Dep_Fun_Rel_left_Galois_if_left_GaloisI left_Galois_if_Dep_Fun_Rel_left_GaloisI)

lemma left_Galois_iff_Dep_Fun_Rel_left_Galois_ge_left_rel2_assmI:
  assumes "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  shows "\<And>x1 x2 y'. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub> y')"
  using assms by blast

lemma left_Galois_iff_Dep_Fun_Rel_left_Galois_ge_left_rel2_assmI':
  assumes "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  shows "\<And>x x' y'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> in_dom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x (l1 x)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x x'\<^esub> y')"
  using assms by blast

lemma left_Galois_iff_Dep_Fun_Rel_left_Galois_mono_assm_in_codom_rightI:
  assumes mono_l1: "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and half_galois_prop_right1: "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_L1: "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and L2_le_unit2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and mono_r2: "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "x1 \<le>\<^bsub>L1\<^esub> x2"
  shows "([in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub>)"
proof (intro Dep_Fun_Rel_predI)
  from mono_l1 half_galois_prop_right1 refl_L1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close>
  have "l1 x2 \<le>\<^bsub>R1\<^esub> l1 x2" "x2 \<^bsub>L1\<^esub>\<lessapprox> l1 x2"
    by (blast intro: t1.left_Galois_left_if_left_relI)+
  fix y' assume "in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y'"
  with Dep_Fun_Rel_relD[OF
    dep_mono_wrt_relD[OF mono_r2 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close>] \<open>l1 x2 \<le>\<^bsub>R1\<^esub> l1 x2\<close>]
    have "r2\<^bsub>x1 (l1 x2)\<^esub> y' \<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub> r2\<^bsub>x2 (l1 x2)\<^esub> y'"
    using \<open>x2 \<^bsub>L1\<^esub>\<lessapprox> l1 x2\<close> by (auto dest: in_field_if_in_codom)
  with L2_le_unit2 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> show "r2\<^bsub>x1 (l1 x2)\<^esub> y' \<le>\<^bsub>L2 x1 x2\<^esub> r2\<^bsub>x2 (l1 x2)\<^esub> y'"
    by blast
qed

lemma left_Galois_iff_Dep_Fun_Rel_left_Galois_mono_assm_in_dom_rightI:
  assumes mono_l1: "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and half_galois_prop_right1: "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_L1: "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and mono_r2: "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "x \<^bsub>L1\<^esub>\<lessapprox> x'"
  shows "([in_dom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>) (r2\<^bsub>x x'\<^esub>)"
proof -
  from mono_l1 half_galois_prop_right1 refl_L1 \<open>x \<^bsub>L1\<^esub>\<lessapprox> x'\<close>
    have "x \<le>\<^bsub>L1\<^esub> x" "l1 x \<le>\<^bsub>R1\<^esub> x'" "x \<^bsub>L1\<^esub>\<lessapprox> l1 x"
    by (auto intro!: t1.half_galois_prop_leftD t1.left_Galois_left_if_left_relI)
  with Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_r2 \<open>x \<le>\<^bsub>L1\<^esub> x\<close>] \<open>l1 x \<le>\<^bsub>R1\<^esub> x'\<close>]
    show ?thesis by blast
qed

lemma left_Galois_iff_Dep_Fun_Rel_left_Galois_if_monoI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "g \<le>\<^bsub>R\<^esub> g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms by (intro left_Galois_iff_Dep_Fun_Rel_left_GaloisI
    left_Galois_iff_Dep_Fun_Rel_left_Galois_ge_left_rel2_assmI
    left_Galois_iff_Dep_Fun_Rel_left_Galois_ge_left_rel2_assmI'
    left_Galois_iff_Dep_Fun_Rel_left_Galois_mono_assm_in_dom_rightI
    left_Galois_iff_Dep_Fun_Rel_left_Galois_mono_assm_in_codom_rightI)
  (auto intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom
    in_field_if_in_codom)

lemma left_Galois_iff_Dep_Fun_Rel_left_Galois_left_rel2_le_assmI:
  assumes refl_L1: "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and mono_L2: "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 _ \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x2] \<Rrightarrow>\<^sub>m (\<le>)) L2"
  and "x1 \<le>\<^bsub>L1\<^esub> x2"
  shows "(\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
proof -
  from refl_L1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have "x1 \<le>\<^bsub>L1\<^esub> x1" by blast
  with dep_mono_wrt_relD[OF dep_mono_wrt_predD[OF mono_L2] \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close>]
    show "(\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)" by auto
qed

lemma left_Galois_iff_Dep_Fun_Rel_left_Galois_left_rel2_unit1_le_assmI:
  assumes mono_l1: "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and half_galois_prop_right1: "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_L1: "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and antimono_L2:
    "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 x3 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x1 \<le>\<^bsub>L1\<^esub> x2 \<and> x3 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2)] \<Rrightarrow>\<^sub>m (\<ge>)) L2"
  and "x1 \<le>\<^bsub>L1\<^esub> x2"
  shows "(\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
proof -
  from mono_l1 half_galois_prop_right1 refl_L1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have "x2 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2"
    by (blast intro: t1.rel_unit_if_reflexive_on_if_half_galois_prop_right_if_mono_wrt_rel)
  with refl_L1 have "\<eta>\<^sub>1 x2 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2" by blast
  with dep_mono_wrt_relD[OF dep_mono_wrt_predD[OF antimono_L2] \<open>x2 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2\<close>]
    show "(\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)" using \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> by auto
qed

lemma left_Galois_iff_Dep_Fun_Rel_left_Galois_if_monoI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 _ \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x2] \<Rrightarrow>\<^sub>m (\<le>)) L2"
  and "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 x3 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x1 \<le>\<^bsub>L1\<^esub> x2 \<and> x3 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2)] \<Rrightarrow>\<^sub>m (\<ge>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "g \<le>\<^bsub>R\<^esub> g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms by (intro left_Galois_iff_Dep_Fun_Rel_left_Galois_if_monoI
    left_Galois_iff_Dep_Fun_Rel_left_Galois_left_rel2_unit1_le_assmI
    left_Galois_iff_Dep_Fun_Rel_left_Galois_left_rel2_le_assmI)
  (auto intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_codom
    in_field_if_in_dom)

corollary left_Galois_iff_Dep_Fun_Rel_left_Galois_if_mono_if_galois_connectionI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 _ \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x2] \<Rrightarrow>\<^sub>m (\<le>)) L2"
  and "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 x3 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x1 \<le>\<^bsub>L1\<^esub> x2 \<and> x3 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2)] \<Rrightarrow>\<^sub>m (\<ge>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "g \<le>\<^bsub>R\<^esub> g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms by (intro left_Galois_iff_Dep_Fun_Rel_left_Galois_if_monoI') auto

interpretation flip_inv : galois "(\<ge>\<^bsub>R1\<^esub>)" "(\<ge>\<^bsub>L1\<^esub>)" r1 l1 .

lemma left_Galois_iff_Dep_Fun_Rel_left_Galois_left_rel2_unit1_le_assm_if_galois_equivI:
  assumes galois_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_L1: "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and mono_L2: "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 _ \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x2] \<Rrightarrow>\<^sub>m (\<le>)) L2"
  and "x1 \<le>\<^bsub>L1\<^esub> x2"
  shows "(\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
proof -
  from refl_L1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have "x1 \<le>\<^bsub>L1\<^esub> x1" by blast
  from galois_equiv1 refl_L1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have "\<eta>\<^sub>1 x2 \<le>\<^bsub>L1\<^esub> x2" by (intro
    flip.t1.counit_rel_if_reflexive_on_if_half_galois_prop_left_if_mono_wrt_rel)
    blast+
  have "x1 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2" by (rule t1.rel_unit_if_left_rel_if_mono_wrt_relI)
    (insert galois_equiv1 refl_L1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close>, auto)
  with dep_mono_wrt_relD[OF dep_mono_wrt_predD[OF mono_L2] \<open>\<eta>\<^sub>1 x2 \<le>\<^bsub>L1\<^esub> x2\<close>]
    show "(\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)" by auto
qed

lemma left_Galois_iff_Dep_Fun_Rel_left_Galois_if_galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 _ \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x2] \<Rrightarrow>\<^sub>m (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "g \<le>\<^bsub>R\<^esub> g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms by (intro
    left_Galois_iff_Dep_Fun_Rel_left_Galois_if_monoI
    left_Galois_iff_Dep_Fun_Rel_left_Galois_left_rel2_le_assmI
    left_Galois_iff_Dep_Fun_Rel_left_Galois_left_rel2_unit1_le_assm_if_galois_equivI)
  auto

corollary left_Galois_iff_Dep_Fun_Rel_left_Galois_if_galois_equivalenceI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "g \<le>\<^bsub>R\<^esub> g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms by (intro left_Galois_iff_Dep_Fun_Rel_left_Galois_if_galois_equivalenceI
    reflexive_on_in_field_mono_assm_left2I)
  auto

corollary left_Galois_iff_Dep_Fun_Rel_left_Galois_if_preorder_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "g \<le>\<^bsub>R\<^esub> g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms by (intro left_Galois_iff_Dep_Fun_Rel_left_Galois_if_galois_equivalenceI')
  auto


corollary left_Galois_iff_Dep_Fun_Rel_left_Galois_if_preorder_equivalenceI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "g \<le>\<^bsub>R\<^esub> g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms by (intro left_Galois_iff_Dep_Fun_Rel_left_Galois_if_preorder_equivalenceI
    transitive_left2_if_preorder_equivalenceI)
  (auto 5 0)


subparagraph \<open>Simplification of Restricted Function Relator\<close>

lemma Dep_Fun_Rel_left_Galois_restrict_left_right_eq_Dep_Fun_Rel_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1" and "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ((\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>) (r2\<^bsub>(r1 x1') x2'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2' y. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) y \<Longrightarrow>
    (\<le>\<^bsub>R2 x1' x2'\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub> y) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>) (l2\<^bsub>x1' (r1 x1')\<^esub> y)"
  and "\<And>x1 x2 y'. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub> y')"
  shows "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub>
    = ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))"
  using assms by (intro ext iffI restrict_leftI restrict_rightI
    in_domI[where ?y="r _"] left_rel_right_if_Dep_Fun_Rel_left_GaloisI
    in_codomI[where ?x="l _"] left_right_rel_if_Dep_Fun_Rel_left_GaloisI)
  auto

lemma Dep_Fun_Rel_left_Galois_restrict_left_right_eq_Dep_Fun_Rel_left_GaloisI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ((\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>) (r2\<^bsub>(r1 x1') x2'\<^esub>)"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x2 \<le>\<^bsub>L1\<^esub> x3 \<and> x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3)] \<Rrightarrow> (\<ge>)) L2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | \<epsilon>\<^sub>1 x2' \<le>\<^bsub>R1\<^esub> x1'] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub>
    = ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))"
  using assms by (intro
    Dep_Fun_Rel_left_Galois_restrict_left_right_eq_Dep_Fun_Rel_left_GaloisI
    left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_leftI
    reflexive_on_in_field_mono_assm_left2I
    left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_rightI
    mono_wrt_rel_left_in_dom_mono_left_assm
    galois_connection_left_right_if_galois_connection_mono_assms_leftI
    galois_connection_left_right_if_galois_connection_mono_assms_rightI
    left_Galois_iff_Dep_Fun_Rel_left_Galois_ge_left_rel2_assmI)
  auto

text \<open>Simplification of Restricted Function Relator for Nested Transports\<close>

lemma Dep_Fun_Rel_left_Galois_restrict_left_right_restrict_left_right_eq:
  fixes S :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> 'b1 \<Rightarrow> 'b2 \<Rightarrow> bool"
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  shows "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (S x x')\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L2 x (r1 x')\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)\<^esub>)
      \<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub> =
    ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> S x x')\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub>" (is "?lhs = ?rhs")
proof -
  have "?lhs =
    ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (S x x')\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)\<^esub>)
      \<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub>"
    by (subst restrict_left_right_eq_restrict_right_left,
      subst restrict_left_Dep_Fun_Rel_rel_restrict_left_eq)
    auto
  also have "... = ?rhs"
    using assms by (subst restrict_left_right_eq_restrict_right_left,
      subst restrict_right_Dep_Fun_Rel_rel_restrict_right_eq)
    (auto elim!: in_codomE t1.left_GaloisE
      simp only: restrict_left_right_eq_restrict_right_left)
  finally show ?thesis .
qed

end


paragraph \<open>Function Relator\<close>

context transport_Fun_Rel
begin

corollary Fun_Rel_left_Galois_if_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "g \<le>\<^bsub>R\<^esub> g"
  and "f \<^bsub>L\<^esub>\<lessapprox> g"
  shows "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>)) f g"
  using assms by (intro tdfr.Dep_Fun_Rel_left_Galois_if_left_GaloisI) simp_all

corollary left_Galois_if_Fun_Rel_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "in_codom (\<le>\<^bsub>R\<^esub>) g"
  and "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>)) f g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g"
  using assms by (intro tdfr.left_Galois_if_Dep_Fun_Rel_left_GaloisI) simp_all

lemma left_Galois_if_Fun_Rel_left_GaloisI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1" and "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>)) f g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g"
  using assms by (intro tdfr.left_Galois_if_Dep_Fun_Rel_left_GaloisI') simp_all

corollary left_Galois_iff_Fun_Rel_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "g \<le>\<^bsub>R\<^esub> g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>)) f g"
  using assms by (intro tdfr.left_Galois_iff_Dep_Fun_Rel_left_GaloisI) simp_all


subparagraph \<open>Simplification of Restricted Function Relator\<close>

lemma Fun_Rel_left_Galois_restrict_left_right_eq_Fun_Rel_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1" and "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  shows "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub> = ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>))"
  using assms
  by (intro tdfr.Dep_Fun_Rel_left_Galois_restrict_left_right_eq_Dep_Fun_Rel_left_GaloisI)
  simp_all

text \<open>Simplification of Restricted Function Relator for Nested Transports\<close>

lemma Fun_Rel_left_Galois_restrict_left_right_restrict_left_right_eq:
  fixes S :: "'b1 \<Rightarrow> 'b2 \<Rightarrow> bool"
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  shows "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> S\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L2\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R2\<^esub>)\<^esub>)\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub> =
    ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> S)\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub>"
  using assms
  by (intro tdfr.Dep_Fun_Rel_left_Galois_restrict_left_right_restrict_left_right_eq)
  simp_all

end


paragraph \<open>Monotone Dependent Function Relator\<close>

context transport_Mono_Dep_Fun_Rel
begin

lemma Dep_Fun_Rel_left_Galois_if_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x x' y'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> in_dom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x (l1 x)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x x'\<^esub> y')"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "f \<^bsub>L\<^esub>\<lessapprox> g"
  shows "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms unfolding left_rel_eq_tdfr_left_Refl_Rel right_rel_eq_tdfr_right_Refl_Rel
  by (intro tdfr.Dep_Fun_Rel_left_Galois_if_left_GaloisI tdfr.left_GaloisI)
  (auto elim!: galois_rel.left_GaloisE in_codomE)

lemma left_Galois_if_Dep_Fun_Rel_left_GaloisI:
  assumes "(tdfr.R \<Rrightarrow>\<^sub>m tdfr.L) r"
  and "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2 y'. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub> y')"
  and "in_dom (\<le>\<^bsub>L\<^esub>) f"
  and "in_codom (\<le>\<^bsub>R\<^esub>) g"
  and "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g"
  using assms unfolding left_rel_eq_tdfr_left_Refl_Rel right_rel_eq_tdfr_right_Refl_Rel
  by (intro tdfr.Galois_Refl_RelI tdfr.left_Galois_if_Dep_Fun_Rel_left_GaloisI)
  (auto simp: in_codom_eq_in_dom_if_reflexive_on_in_field)

lemma left_Galois_iff_Dep_Fun_Rel_left_GaloisI:
  assumes "(tdfr.R \<Rrightarrow>\<^sub>m tdfr.L) r"
  and "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "in_dom (\<le>\<^bsub>L\<^esub>) f"
  and "in_codom (\<le>\<^bsub>R\<^esub>) g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms by (intro iffI Dep_Fun_Rel_left_Galois_if_left_GaloisI
    tdfr.left_Galois_iff_Dep_Fun_Rel_left_Galois_ge_left_rel2_assmI'
    tdfr.left_Galois_iff_Dep_Fun_Rel_left_Galois_mono_assm_in_dom_rightI)
  (auto intro!: left_Galois_if_Dep_Fun_Rel_left_GaloisI
    tdfr.left_Galois_iff_Dep_Fun_Rel_left_Galois_ge_left_rel2_assmI
    tdfr.left_Galois_iff_Dep_Fun_Rel_left_Galois_mono_assm_in_codom_rightI
    intro: reflexive_on_if_le_pred_if_reflexive_on
      in_field_if_in_dom in_field_if_in_codom)

lemma left_Galois_iff_Dep_Fun_Rel_left_Galois_if_mono_if_galois_connectionI:
  assumes galois_conn1: "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_L1: "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and L2_le_unit2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and mono_r2: "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and trans_L2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "in_dom (\<le>\<^bsub>L\<^esub>) f"
  and "in_codom (\<le>\<^bsub>R\<^esub>) g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have "(\<le>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x1)\<^esub> y')"
    if hyps: "x1 \<le>\<^bsub>L1\<^esub> x2" "in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y'" for x1 x2 y'
  proof -
    have "([in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x1)\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
    proof (intro Dep_Fun_Rel_predI)
      from galois_conn1 refl_L1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close>
        have "x1 \<le>\<^bsub>L1\<^esub> x1" "l1 x1 \<le>\<^bsub>R1\<^esub> l1 x2" "x1 \<^bsub>L1\<^esub>\<lessapprox> l1 x1"
        by (blast intro: t1.left_Galois_left_if_left_relI)+
      fix y' assume "in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y'"
      with Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_r2 \<open>x1 \<le>\<^bsub>L1\<^esub> x1\<close>]
        \<open>l1 x1 \<le>\<^bsub>R1\<^esub> l1 x2\<close>]
        have "r2\<^bsub>x1 (l1 x1)\<^esub> y' \<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub> r2\<^bsub>x1 (l1 x2)\<^esub> y'"
        using \<open>x1 \<^bsub>L1\<^esub>\<lessapprox> l1 x1\<close> by (auto dest: in_field_if_in_dom)
      with L2_le_unit2 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> show "r2\<^bsub>x1 (l1 x1)\<^esub> y' \<le>\<^bsub>L2 x1 x2\<^esub> r2\<^bsub>x1 (l1 x2)\<^esub> y'"
        by blast
    qed
    with hyps show ?thesis using trans_L2 by blast
  qed
  then show ?thesis using assms
    using assms by (intro left_Galois_iff_Dep_Fun_Rel_left_GaloisI
      tdfr.mono_wrt_rel_rightI
      tdfr.mono_wrt_rel_right2_if_mono_wrt_rel_right2_if_left_GaloisI
      tdfr.left_Galois_iff_Dep_Fun_Rel_left_Galois_ge_left_rel2_assmI
      tdfr.left_Galois_iff_Dep_Fun_Rel_left_Galois_mono_assm_in_codom_rightI)
    (auto intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_codom)
qed

corollary left_Galois_iff_Dep_Fun_Rel_left_Galois_if_mono_if_galois_connectionI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 _ \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x2] \<Rrightarrow>\<^sub>m (\<le>)) L2"
  and "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 x3 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x1 \<le>\<^bsub>L1\<^esub> x2 \<and> x3 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2)] \<Rrightarrow>\<^sub>m (\<ge>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "in_dom (\<le>\<^bsub>L\<^esub>) f"
  and "in_codom (\<le>\<^bsub>R\<^esub>) g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g" (is "?lhs \<longleftrightarrow> ?rhs")
  using assms by (intro
    left_Galois_iff_Dep_Fun_Rel_left_Galois_if_mono_if_galois_connectionI
    tdfr.left_Galois_iff_Dep_Fun_Rel_left_Galois_left_rel2_unit1_le_assmI
    tdfr.left_Galois_iff_Dep_Fun_Rel_left_Galois_left_rel2_le_assmI)
  auto

corollary left_Galois_eq_Dep_Fun_Rel_left_Galois_restrict_if_mono_if_galois_connectionI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 _ \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x2] \<Rrightarrow>\<^sub>m (\<le>)) L2"
  and "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 x3 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x1 \<le>\<^bsub>L1\<^esub> x2 \<and> x3 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2)] \<Rrightarrow>\<^sub>m (\<ge>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub>"
  using assms by (intro ext iffI restrict_leftI restrict_rightI
    iffD1[OF left_Galois_iff_Dep_Fun_Rel_left_Galois_if_mono_if_galois_connectionI'])
  (auto intro!:
    iffD2[OF left_Galois_iff_Dep_Fun_Rel_left_Galois_if_mono_if_galois_connectionI'])

lemma left_Galois_iff_Dep_Fun_Rel_left_Galois_if_galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "in_dom (\<le>\<^bsub>L\<^esub>) f"
  and "in_codom (\<le>\<^bsub>R\<^esub>) g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms by (intro left_Galois_iff_Dep_Fun_Rel_left_Galois_if_mono_if_galois_connectionI
    tdfr.left_Galois_iff_Dep_Fun_Rel_left_Galois_left_rel2_le_assmI
    tdfr.reflexive_on_in_field_mono_assm_left2I
    tdfr.left_Galois_iff_Dep_Fun_Rel_left_Galois_left_rel2_unit1_le_assm_if_galois_equivI)
  auto

theorem left_Galois_eq_Dep_Fun_Rel_left_Galois_restrict_if_galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub>"
  using assms by (intro ext iffI restrict_leftI restrict_rightI
    iffD1[OF left_Galois_iff_Dep_Fun_Rel_left_Galois_if_galois_equivalenceI])
  (auto intro!: iffD2[OF left_Galois_iff_Dep_Fun_Rel_left_Galois_if_galois_equivalenceI])

corollary left_Galois_iff_Dep_Fun_Rel_left_Galois_if_preorder_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "in_dom (\<le>\<^bsub>L\<^esub>) f"
  and "in_codom (\<le>\<^bsub>R\<^esub>) g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms by (intro left_Galois_iff_Dep_Fun_Rel_left_Galois_if_galois_equivalenceI)
  auto

corollary left_Galois_eq_Dep_Fun_Rel_left_Galois_restrict_if_preorder_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub>"
  using assms by (intro ext iffI restrict_leftI restrict_rightI
    iffD1[OF left_Galois_iff_Dep_Fun_Rel_left_Galois_if_preorder_equivalenceI])
  (auto intro!: iffD2[OF left_Galois_iff_Dep_Fun_Rel_left_Galois_if_preorder_equivalenceI])

corollary left_Galois_iff_Dep_Fun_Rel_left_Galois_if_preorder_equivalenceI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "in_dom (\<le>\<^bsub>L\<^esub>) f"
  and "in_codom (\<le>\<^bsub>R\<^esub>) g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms by (intro left_Galois_iff_Dep_Fun_Rel_left_Galois_if_preorder_equivalenceI
    tdfr.transitive_left2_if_preorder_equivalenceI)
  (auto 5 0)

corollary left_Galois_eq_Dep_Fun_Rel_left_Galois_restrict_if_preorder_equivalenceI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub>"
  using assms by (intro ext iffI restrict_leftI restrict_rightI
    iffD1[OF left_Galois_iff_Dep_Fun_Rel_left_Galois_if_preorder_equivalenceI'])
  (auto intro!: iffD2[OF left_Galois_iff_Dep_Fun_Rel_left_Galois_if_preorder_equivalenceI'])


subparagraph \<open>Simplification of Restricted Function Relator\<close>

lemma Dep_Fun_Rel_left_Galois_restrict_left_right_eq_Dep_Fun_Rel_left_Galois_if_reflexive_onI:
  assumes "reflexive_on (in_field tdfr.L) tdfr.L"
  and "reflexive_on (in_field tdfr.R) tdfr.R"
  and "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ((\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>) (r2\<^bsub>(r1 x1') x2'\<^esub>)"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x2 \<le>\<^bsub>L1\<^esub> x3 \<and> x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3)] \<Rrightarrow> (\<ge>)) L2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | \<epsilon>\<^sub>1 x2' \<le>\<^bsub>R1\<^esub> x1'] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub>
    = ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))"
  using assms by (auto simp only: left_rel_eq_tdfr_left_rel_if_reflexive_on
      right_rel_eq_tdfr_right_rel_if_reflexive_on
    intro!: tdfr.Dep_Fun_Rel_left_Galois_restrict_left_right_eq_Dep_Fun_Rel_left_GaloisI')

interpretation flip : transport_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2
  rewrites "flip.t1.unit \<equiv> \<epsilon>\<^sub>1" by (simp only: t1.flip_unit_eq_counit)

lemma Dep_Fun_Rel_left_Galois_restrict_left_right_eq_Dep_Fun_Rel_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ((\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>) (r2\<^bsub>(r1 x1') x2'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1' x2' \<Colon> (\<ge>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x1' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and PERS: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> partial_equivalence_rel (\<le>\<^bsub>L2 x1 x2\<^esub>)"
    "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> partial_equivalence_rel (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub>
    = ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))"
  using assms by (intro
    Dep_Fun_Rel_left_Galois_restrict_left_right_eq_Dep_Fun_Rel_left_Galois_if_reflexive_onI
    tdfr.reflexive_on_in_field_left_if_equivalencesI
    flip.reflexive_on_in_field_left_if_equivalencesI
    tdfr.galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI
    flip.galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI)
  (auto dest!: PERS)


text \<open>Simplification of Restricted Function Relator for Nested Transports\<close>

lemma Dep_Fun_Rel_left_Galois_restrict_left_right_restrict_left_right_eq:
  fixes S :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> 'b1 \<Rightarrow> 'b2 \<Rightarrow> bool"
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  shows "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (S x x')\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L2 x (r1 x')\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)\<^esub>)
      \<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub> =
    ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> S x x')\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub>"
    (is "?lhs\<restriction>\<^bsub>?DL\<^esub>\<upharpoonleft>\<^bsub>?CR\<^esub> = ?rhs\<restriction>\<^bsub>?DL\<^esub>\<upharpoonleft>\<^bsub>?CR\<^esub>")
proof (intro ext)
  fix f g
  have "?lhs\<restriction>\<^bsub>?DL\<^esub>\<upharpoonleft>\<^bsub>?CR\<^esub> f g \<longleftrightarrow> ?lhs f g \<and> ?DL f \<and> ?CR g" by blast
  also have "... \<longleftrightarrow> ?lhs\<restriction>\<^bsub>in_dom tdfr.L\<^esub>\<upharpoonleft>\<^bsub>in_codom tdfr.R\<^esub> f g \<and> ?DL f \<and> ?CR g"
    unfolding left_rel_eq_tdfr_left_Refl_Rel right_rel_eq_tdfr_right_Refl_Rel
    by blast
  also with assms have "... \<longleftrightarrow> ?rhs\<restriction>\<^bsub>in_dom tdfr.L\<^esub>\<upharpoonleft>\<^bsub>in_codom tdfr.R\<^esub> f g \<and> ?DL f \<and> ?CR g"
    by (simp only:
      tdfr.Dep_Fun_Rel_left_Galois_restrict_left_right_restrict_left_right_eq)
  also have "... \<longleftrightarrow> ?rhs\<restriction>\<^bsub>?DL\<^esub>\<upharpoonleft>\<^bsub>?CR\<^esub> f g"
    unfolding left_rel_eq_tdfr_left_Refl_Rel right_rel_eq_tdfr_right_Refl_Rel
    by blast
  finally show "?lhs\<restriction>\<^bsub>?DL\<^esub>\<upharpoonleft>\<^bsub>?CR\<^esub> f g \<longleftrightarrow> ?rhs\<restriction>\<^bsub>?DL\<^esub>\<upharpoonleft>\<^bsub>?CR\<^esub> f g" .
qed

end


paragraph \<open>Monotone Function Relator\<close>

context transport_Mono_Fun_Rel
begin

corollary Fun_Rel_left_Galois_if_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) (r2)"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "f \<^bsub>L\<^esub>\<lessapprox> g"
  shows "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>)) f g"
  using assms by (intro tpdfr.Dep_Fun_Rel_left_Galois_if_left_GaloisI) simp_all

interpretation flip : transport_Mono_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2 .

lemma left_Galois_if_Fun_Rel_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2"
  and "in_dom (\<le>\<^bsub>L\<^esub>) f"
  and "in_codom (\<le>\<^bsub>R\<^esub>) g"
  and "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>)) f g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g"
  using assms
  by (intro tpdfr.left_Galois_if_Dep_Fun_Rel_left_GaloisI flip.tfr.mono_wrt_rel_leftI)
  simp_all

corollary left_Galois_iff_Fun_Rel_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) (r2)"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "in_dom (\<le>\<^bsub>L\<^esub>) f"
  and "in_codom (\<le>\<^bsub>R\<^esub>) g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>)) f g"
  using assms by (intro iffI Fun_Rel_left_Galois_if_left_GaloisI)
  (auto intro!: left_Galois_if_Fun_Rel_left_GaloisI)

theorem left_Galois_eq_Fun_Rel_left_Galois_restrictI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub>"
  using assms by (intro ext iffI restrict_leftI restrict_rightI
    iffD1[OF left_Galois_iff_Fun_Rel_left_GaloisI])
  (auto elim!: tpdfr.left_GaloisE intro!: iffD2[OF left_Galois_iff_Fun_Rel_left_GaloisI])


subparagraph \<open>Simplification of Restricted Function Relator\<close>

lemma Fun_Rel_left_Galois_restrict_left_right_eq_Fun_Rel_left_Galois_if_reflexive_onI:
  assumes "reflexive_on (in_field tfr.tdfr.L) tfr.tdfr.L"
  and "reflexive_on (in_field tfr.tdfr.R) tfr.tdfr.R"
  and "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1" and "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  shows "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub> = ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>))"
  using assms by (auto simp only: tpdfr.left_rel_eq_tdfr_left_rel_if_reflexive_on
      tpdfr.right_rel_eq_tdfr_right_rel_if_reflexive_on
    intro!: tfr.Fun_Rel_left_Galois_restrict_left_right_eq_Fun_Rel_left_GaloisI)

lemma Fun_Rel_left_Galois_restrict_left_right_eq_Fun_Rel_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1" and "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "partial_equivalence_rel (\<le>\<^bsub>L2\<^esub>)"
  and "partial_equivalence_rel (\<le>\<^bsub>R2\<^esub>)"
  shows "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub> = ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>))"
  using assms by (intro
    Fun_Rel_left_Galois_restrict_left_right_eq_Fun_Rel_left_Galois_if_reflexive_onI
    tfr.reflexive_on_in_field_leftI
    flip.tfr.reflexive_on_in_field_leftI)
  auto


text \<open>Simplification of Restricted Function Relator for Nested Transports\<close>

lemma Fun_Rel_left_Galois_restrict_left_right_restrict_left_right_eq:
  fixes S :: "'b1 \<Rightarrow> 'b2 \<Rightarrow> bool"
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  shows "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> S\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L2\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R2\<^esub>)\<^esub>)\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub> =
    ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> S)\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub>"
  using assms
  by (intro tpdfr.Dep_Fun_Rel_left_Galois_restrict_left_right_restrict_left_right_eq)
  simp_all

end


end