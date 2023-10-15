\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Order Equivalence\<close>
theory Transport_Functions_Order_Equivalence
  imports
    Transport_Functions_Monotone
    Transport_Functions_Galois_Equivalence
begin

paragraph \<open>Dependent Function Relator\<close>

context transport_Dep_Fun_Rel
begin

subparagraph \<open>Inflationary\<close>

lemma rel_unit_self_if_rel_selfI:
  assumes inflationary_unit1: "inflationary_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and refl_L1: "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and trans_L1: "transitive (\<le>\<^bsub>L1\<^esub>)"
  and mono_l2: "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> ((\<le>\<^bsub>L2 x x\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>)"
  and mono_r2: "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>)"
  and inflationary_unit2: "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    inflationary_on (in_codom (\<le>\<^bsub>L2 x x\<^esub>)) (\<le>\<^bsub>L2 x x\<^esub>) (\<eta>\<^bsub>2 x (l1 x)\<^esub>)"
  and L2_le1: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and L2_unit_le2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and ge_R2_l2_le2: "\<And>x y. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> in_codom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) y \<Longrightarrow>
    (\<ge>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub> y) \<le> (\<ge>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y)"
  and trans_L2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "f \<le>\<^bsub>L\<^esub> f"
  shows "f \<le>\<^bsub>L\<^esub> \<eta> f"
proof (intro left_relI)
  fix x1 x2 assume [iff]: "x1 \<le>\<^bsub>L1\<^esub> x2"
  moreover with inflationary_unit1 have "x2 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2" by blast
  ultimately have "x1 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2" using trans_L1 by blast
  with \<open>f \<le>\<^bsub>L\<^esub> f\<close> have "f x1 \<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub> f (\<eta>\<^sub>1 x2)" by blast
  with L2_unit_le2 have "f x1 \<le>\<^bsub>L2 x1 x2\<^esub> f (\<eta>\<^sub>1 x2)" by blast
  moreover have "... \<le>\<^bsub>L2 x1 x2\<^esub> \<eta> f x2"
  proof -
    from refl_L1 \<open>x2 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2\<close> have "\<eta>\<^sub>1 x2 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2" by blast
    with \<open>f \<le>\<^bsub>L\<^esub> f\<close> have "f (\<eta>\<^sub>1 x2) \<le>\<^bsub>L2 (\<eta>\<^sub>1 x2) (\<eta>\<^sub>1 x2)\<^esub> f (\<eta>\<^sub>1 x2)" by blast
    with L2_le1 have "f (\<eta>\<^sub>1 x2) \<le>\<^bsub>L2 x2 (\<eta>\<^sub>1 x2)\<^esub> f (\<eta>\<^sub>1 x2)"
      using \<open>x2 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2\<close> by blast
    moreover from refl_L1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have [iff]: "x2 \<le>\<^bsub>L1\<^esub> x2" by blast
    ultimately have "f (\<eta>\<^sub>1 x2) \<le>\<^bsub>L2 x2 x2\<^esub> f (\<eta>\<^sub>1 x2)" using L2_unit_le2 by blast
    with inflationary_unit2 have "f (\<eta>\<^sub>1 x2) \<le>\<^bsub>L2 x2 x2\<^esub> \<eta>\<^bsub>2 x2 (l1 x2)\<^esub> (f (\<eta>\<^sub>1 x2))" by blast
    moreover have "... \<le>\<^bsub>L2 x2 x2\<^esub> \<eta> f x2"
    proof -
      from \<open>f (\<eta>\<^sub>1 x2) \<le>\<^bsub>L2 x2 x2\<^esub> f (\<eta>\<^sub>1 x2)\<close> mono_l2
        have "l2\<^bsub>(l1 x2) x2\<^esub> (f (\<eta>\<^sub>1 x2)) \<le>\<^bsub>R2 (l1 x2) (l1 x2)\<^esub> l2\<^bsub>(l1 x2) x2\<^esub> (f (\<eta>\<^sub>1 x2))"
        by blast
      with ge_R2_l2_le2
        have "l2\<^bsub>(l1 x2) x2\<^esub> (f (\<eta>\<^sub>1 x2)) \<le>\<^bsub>R2 (l1 x2) (l1 x2)\<^esub> l2\<^bsub>(l1 x2) (\<eta>\<^sub>1 x2)\<^esub> (f (\<eta>\<^sub>1 x2))"
        using \<open>f (\<eta>\<^sub>1 x2) \<le>\<^bsub>L2 x2 (\<eta>\<^sub>1 x2)\<^esub> f (\<eta>\<^sub>1 x2)\<close> by blast
      with mono_r2 have "\<eta>\<^bsub>2 x2 (l1 x2)\<^esub> (f (\<eta>\<^sub>1 x2)) \<le>\<^bsub>L2 x2 (\<eta>\<^sub>1 x2)\<^esub> \<eta> f x2"
        by auto
      with L2_unit_le2 show ?thesis by blast
    qed
    ultimately have "f (\<eta>\<^sub>1 x2) \<le>\<^bsub>L2 x2 x2\<^esub> \<eta> f x2" using trans_L2 by blast
    with L2_le1 show ?thesis by blast
  qed
  ultimately show "f x1 \<le>\<^bsub>L2 x1 x2\<^esub> \<eta> f x2" using trans_L2 by blast
qed

subparagraph \<open>Deflationary\<close>

interpretation flip_inv :
  transport_Dep_Fun_Rel "(\<ge>\<^bsub>R1\<^esub>)" "(\<ge>\<^bsub>L1\<^esub>)" r1 l1 "flip2 R2" "flip2 L2" r2 l2
  rewrites "flip_inv.L \<equiv> (\<ge>\<^bsub>R\<^esub>)" and "flip_inv.R \<equiv> (\<ge>\<^bsub>L\<^esub>)"
  and "flip_inv.unit \<equiv> \<epsilon>"
  and "flip_inv.t1.unit \<equiv> \<epsilon>\<^sub>1"
  and "\<And>x y. flip_inv.t2_unit x y \<equiv> \<epsilon>\<^bsub>2 y x\<^esub>"
  and "\<And>R x y. (flip2 R x y)\<inverse> \<equiv> R y x"
  and "\<And>R. in_codom R\<inverse> \<equiv> in_dom R"
  and "\<And>R x1 x2. in_codom (flip2 R x1 x2) \<equiv> in_dom (R x2 x1)"
  and "\<And>x1 x2 x1' x2'. (flip2 R2 x1' x2' \<Rrightarrow>\<^sub>m flip2 L2 x1 x2) \<equiv> ((\<le>\<^bsub>R2 x2' x1'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x2 x1\<^esub>))"
  and "\<And>x1 x2 x1' x2'. (flip2 L2 x1 x2 \<Rrightarrow>\<^sub>m flip2 R2 x1' x2') \<equiv> ((\<le>\<^bsub>L2 x2 x1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 x2' x1'\<^esub>))"
  and "\<And>P. inflationary_on P (\<ge>\<^bsub>R1\<^esub>) \<equiv> deflationary_on P (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>P x. inflationary_on P (flip2 R2 x x) \<equiv> deflationary_on P (\<le>\<^bsub>R2 x x\<^esub>)"
  and "\<And>x1 x2 x3 x4. flip2 R2 x1 x2 \<le> flip2 R2 x3 x4 \<equiv> (\<le>\<^bsub>R2 x2 x1\<^esub>) \<le> (\<le>\<^bsub>R2 x4 x3\<^esub>)"
  and "\<And>(R :: 'z \<Rightarrow> _) (P :: 'z \<Rightarrow> bool). reflexive_on P R\<inverse> \<equiv> reflexive_on P R"
  and "\<And>R. transitive R\<inverse> \<equiv> transitive R"
  and "\<And>x1' x2'. transitive (flip2 R2 x1' x2') \<equiv> transitive (\<le>\<^bsub>R2 x2' x1'\<^esub>)"
  by (simp_all add: flip_inv_left_eq_ge_right flip_inv_right_eq_ge_left
    flip_unit_eq_counit t1.flip_unit_eq_counit t2.flip_unit_eq_counit
    galois_prop.rel_inv_half_galois_prop_right_eq_half_galois_prop_left_rel_inv)

lemma counit_rel_self_if_rel_selfI:
  assumes "deflationary_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> ((\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)) (l2\<^bsub> x' (r1 x')\<^esub>)"
  and "\<And>x' x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> ((\<le>\<^bsub>R2 x' x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') x'\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> deflationary_on (in_dom (\<le>\<^bsub>R2 x' x'\<^esub>)) (\<le>\<^bsub>R2 x' x'\<^esub>) (\<epsilon>\<^bsub>2 (r1 x') x'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x' y'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> in_dom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) y' \<Longrightarrow>
    (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub> y') \<le> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y')"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "g \<le>\<^bsub>R\<^esub> g"
  shows "\<epsilon> g \<le>\<^bsub>R\<^esub> g"
  using assms by (intro flip_inv.rel_unit_self_if_rel_selfI[simplified rel_inv_iff_rel])


subparagraph \<open>Relational Equivalence\<close>

lemma bi_related_unit_self_if_rel_self_aux:
  assumes rel_equiv_unit1: "rel_equivalence_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and mono_r2: "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x x\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>)"
  and rel_equiv_unit2: "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    rel_equivalence_on (in_field (\<le>\<^bsub>L2 x x\<^esub>)) (\<le>\<^bsub>L2 x x\<^esub>) (\<eta>\<^bsub>2 x (l1 x)\<^esub>)"
  and L2_le1: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and L2_le2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and [iff]: "x \<le>\<^bsub>L1\<^esub> x"
  shows "((\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>)"
  and "((\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>)"
  and "deflationary_on (in_dom (\<le>\<^bsub>L2 x x\<^esub>)) (\<le>\<^bsub>L2 x x\<^esub>) \<eta>\<^bsub>2 x (l1 x)\<^esub>"
  and "inflationary_on (in_codom (\<le>\<^bsub>L2 x x\<^esub>)) (\<le>\<^bsub>L2 x x\<^esub>) \<eta>\<^bsub>2 x (l1 x)\<^esub>"
proof -
  from rel_equiv_unit1 have "x \<equiv>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x" by blast
  with mono_r2 show "((\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>)"
    and "((\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>)"
    using L2_le1 L2_le2 by blast+
qed (insert rel_equiv_unit2, blast+)

interpretation flip : transport_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2
  rewrites "flip.counit \<equiv> \<eta>" and "flip.t1.counit \<equiv> \<eta>\<^sub>1"
  and "\<And>x y. flip.t2_counit x y \<equiv> \<eta>\<^bsub>2 y x\<^esub>"
  by (simp_all add: order_functors.flip_counit_eq_unit)

lemma bi_related_unit_self_if_rel_selfI:
  assumes rel_equiv_unit1: "rel_equivalence_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and trans_L1: "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> ((\<le>\<^bsub>L2 x x\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x x\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    rel_equivalence_on (in_field (\<le>\<^bsub>L2 x x\<^esub>)) (\<le>\<^bsub>L2 x x\<^esub>) (\<eta>\<^bsub>2 x (l1 x)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x1) x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x y. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> in_dom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>) y \<Longrightarrow>
    (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub> y) \<le> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y)"
  and "\<And>x y. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> in_codom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) y \<Longrightarrow>
    (\<ge>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub> y) \<le> (\<ge>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "f \<le>\<^bsub>L\<^esub> f"
  shows "f \<equiv>\<^bsub>L\<^esub> \<eta> f"
proof -
  from rel_equiv_unit1 trans_L1 have "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
    by (intro reflexive_on_in_field_if_transitive_if_rel_equivalence_on)
  with assms show ?thesis
    by (intro bi_relatedI rel_unit_self_if_rel_selfI
      flip.counit_rel_self_if_rel_selfI
      bi_related_unit_self_if_rel_self_aux)
    (auto intro: inflationary_on_if_le_pred_if_inflationary_on
      deflationary_on_if_le_pred_if_deflationary_on
      reflexive_on_if_le_pred_if_reflexive_on
      in_field_if_in_dom in_field_if_in_codom)
qed


subparagraph \<open>Lemmas for Monotone Function Relator\<close>

lemma order_equivalence_if_order_equivalence_mono_assms_leftI:
  assumes order_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_R1: "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and R2_counit_le1: "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and mono_l2: "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and [iff]: "x1' \<le>\<^bsub>R1\<^esub> x2'"
  shows "([in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x1' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
  and "([in_codom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x2')\<^esub>)"
proof -
  from refl_R1 have "x1' \<le>\<^bsub>R1\<^esub> x1'" "x2' \<le>\<^bsub>R1\<^esub> x2'" by auto
  moreover with order_equiv1
    have "r1 x1' \<le>\<^bsub>L1\<^esub> r1 x2'" "r1 x1' \<le>\<^bsub>L1\<^esub> r1 x1'" "r1 x2' \<le>\<^bsub>L1\<^esub> r1 x2'" by auto
  ultimately have "r1 x1' \<^bsub>L1\<^esub>\<lessapprox> x1'" "r1 x2' \<^bsub>L1\<^esub>\<lessapprox> x2'" by blast+
  note Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_l2 \<open>x1' \<le>\<^bsub>R1\<^esub> x2'\<close>]
    \<open>r1 x1' \<le>\<^bsub>L1\<^esub> r1 x1'\<close>]
  with \<open>r1 x1' \<^bsub>L1\<^esub>\<lessapprox> x1'\<close> R2_counit_le1
    show "([in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x1' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
    by (intro Dep_Fun_Rel_predI) (auto dest!: in_field_if_in_dom)
  note Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_l2 \<open>x2' \<le>\<^bsub>R1\<^esub> x2'\<close>]
    \<open>r1 x1' \<le>\<^bsub>L1\<^esub> r1 x2'\<close>]
  with \<open>r1 x2' \<^bsub>L1\<^esub>\<lessapprox> x2'\<close> R2_counit_le1
    show "([in_codom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x2')\<^esub>)"
    by (intro Dep_Fun_Rel_predI) (auto dest!: in_field_if_in_codom)
qed

lemma order_equivalence_if_order_equivalence_mono_assms_rightI:
  assumes order_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_L1: "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and L2_unit_le2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and mono_r2: "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and [iff]: "x1 \<le>\<^bsub>L1\<^esub> x2"
  shows "([in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub>)"
  and "([in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x1)\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
proof -
  from refl_L1 have "x1 \<le>\<^bsub>L1\<^esub> x1" "x2 \<le>\<^bsub>L1\<^esub> x2" by auto
  moreover with order_equiv1
    have "l1 x1 \<le>\<^bsub>R1\<^esub> l1 x2" "l1 x1 \<le>\<^bsub>R1\<^esub> l1 x1" "l1 x2 \<le>\<^bsub>R1\<^esub> l1 x2" by auto
  ultimately have "x1 \<^bsub>L1\<^esub>\<lessapprox> l1 x1" "x2 \<^bsub>L1\<^esub>\<lessapprox> l1 x2" using order_equiv1
    by (auto intro!: t1.left_Galois_left_if_in_codom_if_inflationary_onI)
  note Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_r2 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close>]
    \<open>l1 x2 \<le>\<^bsub>R1\<^esub> l1 x2\<close>]
  with \<open>x2 \<^bsub>L1\<^esub>\<lessapprox> l1 x2\<close> L2_unit_le2
    show "([in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub>)"
    by (intro Dep_Fun_Rel_predI) (auto dest!: in_field_if_in_codom)
  note Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_r2 \<open>x1 \<le>\<^bsub>L1\<^esub> x1\<close>]
    \<open>l1 x1 \<le>\<^bsub>R1\<^esub> l1 x2\<close>]
  with \<open>x1 \<^bsub>L1\<^esub>\<lessapprox> l1 x1\<close> L2_unit_le2
    show "([in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x1)\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
    by (intro Dep_Fun_Rel_predI) (auto dest!: in_field_if_in_dom)
qed

lemma l2_unit_bi_rel_selfI:
  assumes pre_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and mono_L2:
    "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x2 \<le>\<^bsub>L1\<^esub> x3 \<and> x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3)] \<Rrightarrow> (\<ge>)) L2"
  and mono_R2:
    "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | (x2' \<le>\<^bsub>R1\<^esub> x3' \<and> x4' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x3')] \<Rrightarrow> (\<ge>)) R2"
  and mono_l2: "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "x \<le>\<^bsub>L1\<^esub> x"
  and "in_field (\<le>\<^bsub>L2 x x\<^esub>) y"
  shows "l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y \<equiv>\<^bsub>R2 (l1 x) (l1 x)\<^esub> l2\<^bsub>(l1 x) x\<^esub> y"
proof (rule bi_relatedI)
  note t1.preorder_equivalence_order_equivalenceE[elim!]
  from \<open>x \<le>\<^bsub>L1\<^esub> x\<close> pre_equiv1 have "l1 x \<le>\<^bsub>R1\<^esub> l1 x" "x \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x" "\<eta>\<^sub>1 x \<le>\<^bsub>L1\<^esub> x" by blast+
  with pre_equiv1 have "x \<^bsub>L1\<^esub>\<lessapprox> l1 x" "\<eta>\<^sub>1 x \<^bsub>L1\<^esub>\<lessapprox> l1 x" by (auto 4 3)
  from pre_equiv1 \<open>x \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x\<close> have "x \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 (\<eta>\<^sub>1 x)" by fastforce
  moreover note \<open>in_field (\<le>\<^bsub>L2 x x\<^esub>) y\<close>
    Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_L2 \<open>\<eta>\<^sub>1 x \<le>\<^bsub>L1\<^esub> x\<close>] \<open>\<eta>\<^sub>1 x \<le>\<^bsub>L1\<^esub> x\<close>]
    Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_L2 \<open>x \<le>\<^bsub>L1\<^esub> x\<close>] \<open>\<eta>\<^sub>1 x \<le>\<^bsub>L1\<^esub> x\<close>]
  ultimately have "in_field (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) (\<eta>\<^sub>1 x)\<^esub>) y" "in_field (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) y"
    using \<open>x \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x\<close> by blast+
  moreover note \<open>x \<^bsub>L1\<^esub>\<lessapprox> l1 x\<close>
    Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_l2 \<open>l1 x \<le>\<^bsub>R1\<^esub> l1 x\<close>] \<open>\<eta>\<^sub>1 x \<le>\<^bsub>L1\<^esub> x\<close>]
  ultimately have "l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y \<le>\<^bsub>R2 (\<epsilon>\<^sub>1 (l1 x)) (l1 x)\<^esub> l2\<^bsub>(l1 x) x\<^esub> y" by auto
  moreover from pre_equiv1 \<open>l1 x \<le>\<^bsub>R1\<^esub> l1 x\<close>
    have "\<epsilon>\<^sub>1 (l1 x) \<le>\<^bsub>R1\<^esub> l1 x" "l1 x \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 (l1 x)" by fastforce+
  moreover note Dep_Fun_Rel_relD[OF dep_mono_wrt_relD
    [OF mono_R2 \<open>l1 x \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 (l1 x)\<close>] \<open>l1 x \<le>\<^bsub>R1\<^esub> l1 x\<close>]
  ultimately show "l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y \<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub> l2\<^bsub>(l1 x) x\<^esub> y" by blast
  note \<open>\<eta>\<^sub>1 x \<^bsub>L1\<^esub>\<lessapprox> l1 x\<close> \<open>in_field (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) y\<close>
    Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_l2 \<open>l1 x \<le>\<^bsub>R1\<^esub> l1 x\<close>] \<open>x \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x\<close>]
  then show "l2\<^bsub>(l1 x) x\<^esub> y \<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub> l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y" by auto
qed

lemma r2_counit_bi_rel_selfI:
  assumes pre_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and mono_L2:
    "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x2 \<le>\<^bsub>L1\<^esub> x3 \<and> x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3)] \<Rrightarrow> (\<ge>)) L2"
  and mono_R2:
    "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | (x2' \<le>\<^bsub>R1\<^esub> x3' \<and> x4' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x3')] \<Rrightarrow> (\<ge>)) R2"
  and mono_r2: "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "x' \<le>\<^bsub>R1\<^esub> x'"
  and "in_field (\<le>\<^bsub>R2 x' x'\<^esub>) y'"
  shows "r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y' \<equiv>\<^bsub>L2 (r1 x') (r1 x')\<^esub> r2\<^bsub>(r1 x') x'\<^esub> y'"
proof (rule bi_relatedI)
  note t1.preorder_equivalence_order_equivalenceE[elim!]
  from \<open>x' \<le>\<^bsub>R1\<^esub> x'\<close> pre_equiv1 have "r1 x' \<le>\<^bsub>L1\<^esub> r1 x'" "x' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x'" "\<epsilon>\<^sub>1 x' \<le>\<^bsub>R1\<^esub> x'" by blast+
  with pre_equiv1 have "r1 x' \<^bsub>L1\<^esub>\<lessapprox> x'" "r1 x' \<^bsub>L1\<^esub>\<lessapprox> \<epsilon>\<^sub>1 x'" by auto
  from pre_equiv1 \<open>x' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x'\<close> have "x' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 (\<epsilon>\<^sub>1 x')" by fastforce
  moreover note \<open>in_field (\<le>\<^bsub>R2 x' x'\<^esub>) y'\<close>
    Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_R2 \<open>\<epsilon>\<^sub>1 x' \<le>\<^bsub>R1\<^esub> x'\<close>] \<open>\<epsilon>\<^sub>1 x' \<le>\<^bsub>R1\<^esub> x'\<close>]
    Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_R2 \<open>\<epsilon>\<^sub>1 x' \<le>\<^bsub>R1\<^esub> x'\<close>] \<open>x' \<le>\<^bsub>R1\<^esub> x'\<close>]
  ultimately have "in_field (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') (\<epsilon>\<^sub>1 x')\<^esub>) y'" "in_field (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) y'"
    using \<open>x' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x'\<close> \<open>x' \<le>\<^bsub>R1\<^esub> x'\<close> by blast+
  moreover note \<open>r1 x' \<^bsub>L1\<^esub>\<lessapprox> \<epsilon>\<^sub>1 x'\<close>
    Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_r2 \<open>r1 x' \<le>\<^bsub>L1\<^esub> r1 x'\<close>] \<open>\<epsilon>\<^sub>1 x' \<le>\<^bsub>R1\<^esub> x'\<close>]
  ultimately show "r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y' \<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub> r2\<^bsub>(r1 x') x'\<^esub> y'" by auto
  note \<open>r1 x' \<^bsub>L1\<^esub>\<lessapprox> x'\<close> \<open>in_field (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') (\<epsilon>\<^sub>1 x')\<^esub>) y'\<close>
    Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_r2 \<open>r1 x' \<le>\<^bsub>L1\<^esub> r1 x'\<close>] \<open>x' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x'\<close>]
  then have "r2\<^bsub>(r1 x') x'\<^esub> y' \<le>\<^bsub>L2 (r1 x') (\<eta>\<^sub>1 (r1 x'))\<^esub> r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y'" by auto
  moreover from pre_equiv1 \<open>r1 x' \<le>\<^bsub>L1\<^esub> r1 x'\<close>
    have "\<eta>\<^sub>1 (r1 x') \<le>\<^bsub>L1\<^esub> r1 x'" "r1 x' \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 (r1 x')" by fastforce+
  moreover note Dep_Fun_Rel_relD[OF dep_mono_wrt_relD
    [OF mono_L2 \<open>r1 x' \<le>\<^bsub>L1\<^esub> r1 x'\<close>] \<open>r1 x' \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 (r1 x')\<close>]
  ultimately show "r2\<^bsub>(r1 x') x'\<^esub> y' \<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub> r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y'"
    using pre_equiv1 by blast
qed

end


paragraph \<open>Function Relator\<close>

context transport_Fun_Rel
begin

corollary rel_unit_self_if_rel_selfI:
  assumes "inflationary_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2"
  and "inflationary_on (in_codom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "f \<le>\<^bsub>L\<^esub> f"
  shows "f \<le>\<^bsub>L\<^esub> \<eta> f"
  using assms by (intro tdfr.rel_unit_self_if_rel_selfI) simp_all

corollary counit_rel_self_if_rel_selfI:
  assumes "deflationary_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2"
  and "deflationary_on (in_dom (\<le>\<^bsub>R2\<^esub>)) (\<le>\<^bsub>R2\<^esub>) \<epsilon>\<^sub>2"
  and "transitive (\<le>\<^bsub>R2\<^esub>)"
  and "g \<le>\<^bsub>R\<^esub> g"
  shows "\<epsilon> g \<le>\<^bsub>R\<^esub> g"
  using assms by (intro tdfr.counit_rel_self_if_rel_selfI) simp_all

lemma bi_related_unit_self_if_rel_selfI:
  assumes "rel_equivalence_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2"
  and "rel_equivalence_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "f \<le>\<^bsub>L\<^esub> f"
  shows "f \<equiv>\<^bsub>L\<^esub> \<eta> f"
  using assms by (intro tdfr.bi_related_unit_self_if_rel_selfI) simp_all

end


paragraph \<open>Monotone Dependent Function Relator\<close>

context transport_Mono_Dep_Fun_Rel
begin

subparagraph \<open>Inflationary\<close>

lemma inflationary_on_unitI:
  assumes "(tdfr.L \<Rrightarrow>\<^sub>m tdfr.R) l" and "(tdfr.R \<Rrightarrow>\<^sub>m tdfr.L) r"
  and "inflationary_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> ((\<le>\<^bsub>L2 x x\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> inflationary_on (in_codom (\<le>\<^bsub>L2 x x\<^esub>)) (\<le>\<^bsub>L2 x x\<^esub>) (\<eta>\<^bsub>2 x (l1 x)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x y. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> in_codom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) y \<Longrightarrow>
    (\<ge>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub> y) \<le> (\<ge>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  shows "inflationary_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  unfolding left_rel_eq_tdfr_left_Refl_Rel using assms
  by (intro inflationary_onI Refl_RelI)
  (auto intro: tdfr.rel_unit_self_if_rel_selfI[simplified unit_eq] elim!: Refl_RelE)


subparagraph \<open>Deflationary\<close>

lemma deflationary_on_counitI:
  assumes "(tdfr.L \<Rrightarrow>\<^sub>m tdfr.R) l" and "(tdfr.R \<Rrightarrow>\<^sub>m tdfr.L) r"
  and "deflationary_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> ((\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)) (l2\<^bsub> x' (r1 x')\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ((\<le>\<^bsub>R2 x' x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') x'\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> deflationary_on (in_dom (\<le>\<^bsub>R2 x' x'\<^esub>)) (\<le>\<^bsub>R2 x' x'\<^esub>) (\<epsilon>\<^bsub>2 (r1 x') x'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x' y'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> in_dom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) y' \<Longrightarrow>
    (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub> y') \<le> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y')"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "deflationary_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>) \<epsilon>"
  unfolding right_rel_eq_tdfr_right_Refl_Rel using assms
  by (intro deflationary_onI Refl_RelI)
  (auto intro: tdfr.counit_rel_self_if_rel_selfI[simplified counit_eq]
    elim!: Refl_RelE)


subparagraph \<open>Relational Equivalence\<close>

context
begin

interpretation flip : transport_Mono_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2
  rewrites "flip.counit \<equiv> \<eta>" and "flip.t1.counit \<equiv> \<eta>\<^sub>1"
  and "\<And>x y. flip.t2_counit x y \<equiv> \<eta>\<^bsub>2 y x\<^esub>"
  by (simp_all add: order_functors.flip_counit_eq_unit)

lemma rel_equivalence_on_unitI:
  assumes "(tdfr.L \<Rrightarrow>\<^sub>m tdfr.R) l" and "(tdfr.R \<Rrightarrow>\<^sub>m tdfr.L) r"
  and rel_equiv_unit1: "rel_equivalence_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and trans_L1: "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> ((\<le>\<^bsub>L2 x x\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x x\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> rel_equivalence_on (in_field (\<le>\<^bsub>L2 x x\<^esub>)) (\<le>\<^bsub>L2 x x\<^esub>) (\<eta>\<^bsub>2 x (l1 x)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x1) x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x y. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> in_dom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>) y \<Longrightarrow>
    (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub> y) \<le> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y)"
  and "\<And>x y. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> in_codom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) y \<Longrightarrow>
    (\<ge>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub> y) \<le> (\<ge>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  shows "rel_equivalence_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
proof -
  from rel_equiv_unit1 trans_L1 have "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
    by (intro reflexive_on_in_field_if_transitive_if_rel_equivalence_on)
  with assms show ?thesis
    by (intro rel_equivalence_onI inflationary_on_unitI
      flip.deflationary_on_counitI)
    (auto intro!: tdfr.bi_related_unit_self_if_rel_self_aux
      intro: inflationary_on_if_le_pred_if_inflationary_on
        deflationary_on_if_le_pred_if_deflationary_on
        reflexive_on_if_le_pred_if_reflexive_on
        in_field_if_in_dom in_field_if_in_codom
      elim!: rel_equivalence_onE
      simp only:)
qed

end

subparagraph \<open>Order Equivalence\<close>

interpretation flip : transport_Mono_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2
  rewrites "flip.unit \<equiv> \<epsilon>" and "flip.t1.unit \<equiv> \<epsilon>\<^sub>1"
  and "flip.counit \<equiv> \<eta>" and "flip.t1.counit \<equiv> \<eta>\<^sub>1"
  and "\<And>x y. flip.t2_unit x y \<equiv> \<epsilon>\<^bsub>2 y x\<^esub>"
  by (simp_all add: order_functors.flip_counit_eq_unit)

lemma order_equivalenceI:
  assumes "(tdfr.L \<Rrightarrow>\<^sub>m tdfr.R) l" and "(tdfr.R \<Rrightarrow>\<^sub>m tdfr.L) r"
  and "rel_equivalence_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and "rel_equivalence_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)" and "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> ((\<le>\<^bsub>L2 x x\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> ((\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 x' x'\<^esub>)) (l2\<^bsub>x' (r1 x')\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> ((\<le>\<^bsub>R2 x' x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') x'\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x x\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> rel_equivalence_on (in_field (\<le>\<^bsub>L2 x x\<^esub>)) (\<le>\<^bsub>L2 x x\<^esub>) (\<eta>\<^bsub>2 x (l1 x)\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    rel_equivalence_on (in_field (\<le>\<^bsub>R2 x' x'\<^esub>)) (\<le>\<^bsub>R2 x' x'\<^esub>) (\<epsilon>\<^bsub>2 (r1 x') x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x1) x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x2' x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' (\<epsilon>\<^sub>1 x2')\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x y. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> in_dom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>) y \<Longrightarrow>
    (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub> y) \<le> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y)"
  and "\<And>x y. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> in_codom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) y \<Longrightarrow>
    (\<ge>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub> y) \<le> (\<ge>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y)"
  and "\<And>x' y'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> in_dom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) y' \<Longrightarrow>
    (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub> y') \<le> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y')"
  and "\<And>x' y'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> in_codom (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub> y') \<le> (\<ge>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y')"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>R1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1 x2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  using assms
  by (intro order_equivalenceI rel_equivalence_on_unitI flip.rel_equivalence_on_unitI
    mono_wrt_rel_leftI flip.mono_wrt_rel_leftI)
  auto

lemma order_equivalence_if_preorder_equivalenceI:
  assumes pre_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and order_equiv2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow>
    ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and L2_les: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
    "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x1) x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
    "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
    "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and R2_les: "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x2' x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
    "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
    "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
    "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' (\<epsilon>\<^sub>1 x2')\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x1' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x2')\<^esub>)"
  and l2_bi_rel: "\<And>x y. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> in_field (\<le>\<^bsub>L2 x x\<^esub>) y \<Longrightarrow>
    l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y \<equiv>\<^bsub>R2 (l1 x) (l1 x)\<^esub> l2\<^bsub>(l1 x) x\<^esub> y"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x1)\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
  and r2_bi_rel: "\<And>x' y'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> in_field (\<le>\<^bsub>R2 x' x'\<^esub>) y' \<Longrightarrow>
    r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y' \<equiv>\<^bsub>L2 (r1 x') (r1 x')\<^esub> r2\<^bsub>(r1 x') x'\<^esub> y'"
  and trans_L2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and trans_R2: "\<And>x1 x2. x1 \<le>\<^bsub>R1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1 x2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
proof -
  from pre_equiv1 L2_les have L2_unit_eq1: "(\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>) = (\<le>\<^bsub>L2 x x\<^esub>)"
    and L2_unit_eq2: "(\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) = (\<le>\<^bsub>L2 x x\<^esub>)"
    if "x \<le>\<^bsub>L1\<^esub> x" for x using \<open>x \<le>\<^bsub>L1\<^esub> x\<close>
    by (auto elim!: t1.preorder_equivalence_order_equivalenceE
      intro!: tdfr.left_rel2_unit_eqs_left_rel2I bi_related_if_rel_equivalence_on
      simp del: t1.unit_eq)
  from pre_equiv1 R2_les have R2_counit_eq1: "(\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) = (\<le>\<^bsub>R2 x' x'\<^esub>)"
    and R2_counit_eq2: "(\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>) = (\<le>\<^bsub>R2 x' x'\<^esub>)" (is ?goal2)
    if "x' \<le>\<^bsub>R1\<^esub> x'" for x' using \<open>x' \<le>\<^bsub>R1\<^esub> x'\<close>
    by (auto elim!: t1.preorder_equivalence_order_equivalenceE
      intro!: flip.tdfr.left_rel2_unit_eqs_left_rel2I bi_related_if_rel_equivalence_on
      simp del: t1.counit_eq)
  from order_equiv2 have
    mono_l2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>)"
    and mono_r2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
    by auto
  moreover have "rel_equivalence_on (in_field (\<le>\<^bsub>L2 x x\<^esub>)) (\<le>\<^bsub>L2 x x\<^esub>) (\<eta>\<^bsub>2 x (l1 x)\<^esub>)" (is ?goal1)
    and "((\<le>\<^bsub>L2 x x\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>)" (is ?goal2)
    if [iff]: "x \<le>\<^bsub>L1\<^esub> x" for x
  proof -
    from pre_equiv1 have "x \<^bsub>L1\<^esub>\<lessapprox> l1 x"
      by (auto intro!: t1.left_GaloisI
        elim!: t1.preorder_equivalence_order_equivalenceE t1.order_equivalenceE)
    with order_equiv2 have "((\<le>\<^bsub>L2 x x\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (r2\<^bsub>x (l1 x)\<^esub>)"
      by (auto simp flip: L2_unit_eq2)
    then show ?goal1 ?goal2 by (auto elim: order_functors.order_equivalenceE)
  qed
  moreover have
    "rel_equivalence_on (in_field (\<le>\<^bsub>R2 x' x'\<^esub>)) (\<le>\<^bsub>R2 x' x'\<^esub>) (\<epsilon>\<^bsub>2 (r1 x') x'\<^esub>)" (is ?goal1)
    and "((\<le>\<^bsub>R2 x' x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') x'\<^esub>)" (is ?goal2)
    if [iff]: "x' \<le>\<^bsub>R1\<^esub> x'" for x'
  proof -
    from pre_equiv1 have "r1 x' \<^bsub>L1\<^esub>\<lessapprox> x'" by blast
    with order_equiv2 have "((\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R2 x' x'\<^esub>)) (l2\<^bsub>x' (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
      by (auto simp flip: R2_counit_eq1)
    then show ?goal1 ?goal2 by (auto elim: order_functors.order_equivalenceE)
  qed
  moreover from mono_l2 tdfr.mono_wrt_rel_left2_if_mono_wrt_rel_left2_if_left_GaloisI
    have "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> ((\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
    using pre_equiv1 R2_les(2) by blast
  moreover from pre_equiv1 have "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
    by (intro t1.half_galois_prop_right_left_right_if_transitive_if_order_equivalence)
    (auto elim!: t1.preorder_equivalence_order_equivalenceE)
  moreover with mono_r2 tdfr.mono_wrt_rel_right2_if_mono_wrt_rel_right2_if_left_GaloisI
    have "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
    using pre_equiv1 by blast
  moreover with L2_les
    have "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
    by blast
  moreover have "in_dom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>) y \<Longrightarrow>
      (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub> y) \<le> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y)"
      (is "_ \<Longrightarrow> ?goal1")
    and "in_codom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) y \<Longrightarrow>
      (\<ge>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub> y) \<le> (\<ge>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y)"
      (is "_ \<Longrightarrow> ?goal2")
    if [iff]: "x \<le>\<^bsub>L1\<^esub> x" for x y
  proof -
    presume "in_dom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>) y \<or> in_codom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) y"
    then have "in_field (\<le>\<^bsub>L2 x x\<^esub>) y" using L2_unit_eq1 L2_unit_eq2 by auto
    with l2_bi_rel have "l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y \<equiv>\<^bsub>R2 (l1 x) (l1 x)\<^esub> l2\<^bsub>(l1 x) x\<^esub> y" by blast
    moreover from pre_equiv1 have \<open>l1 x \<le>\<^bsub>R1\<^esub> l1 x\<close> by blast
    ultimately show ?goal1 ?goal2 using trans_R2 by blast+
  qed auto
  moreover have "in_dom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) y' \<Longrightarrow>
      (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub> y') \<le> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y')"
      (is "_ \<Longrightarrow> ?goal1")
    and "in_codom (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>) y' \<Longrightarrow>
      (\<ge>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub> y') \<le> (\<ge>\<^bsub>L2 (r1 x') (r1 x')\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y')"
      (is "_ \<Longrightarrow> ?goal2")
    if [iff]: "x' \<le>\<^bsub>R1\<^esub> x'" for x' y'
  proof -
    presume "in_dom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) y' \<or> in_codom (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>) y'"
    then have "in_field (\<le>\<^bsub>R2 x' x'\<^esub>) y'" using R2_counit_eq1 R2_counit_eq2 by auto
    with r2_bi_rel have "r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y' \<equiv>\<^bsub>L2 (r1 x') (r1 x')\<^esub> r2\<^bsub>(r1 x') x'\<^esub> y'"
      by blast
    moreover from pre_equiv1 have \<open>r1 x' \<le>\<^bsub>L1\<^esub> r1 x'\<close> by blast
    ultimately show ?goal1 ?goal2 using trans_L2 by blast+
  qed auto
  ultimately show ?thesis using assms
    by (intro order_equivalenceI
      tdfr.mono_wrt_rel_left_if_transitiveI
      tdfr.mono_wrt_rel_left2_if_mono_wrt_rel_left2_if_left_GaloisI
      tdfr.mono_wrt_rel_right_if_transitiveI
      tdfr.mono_wrt_rel_right2_if_mono_wrt_rel_right2_if_left_GaloisI)
    (auto elim!: t1.preorder_equivalence_order_equivalenceE)
qed

lemma order_equivalence_if_preorder_equivalenceI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x1) x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x2' x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' (\<epsilon>\<^sub>1 x2')\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "\<And>x y. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> in_field (\<le>\<^bsub>L2 x x\<^esub>) y \<Longrightarrow>
    l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y \<equiv>\<^bsub>R2 (l1 x) (l1 x)\<^esub> l2\<^bsub>(l1 x) x\<^esub> y"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x' y'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> in_field (\<le>\<^bsub>R2 x' x'\<^esub>) y' \<Longrightarrow>
    r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y' \<equiv>\<^bsub>L2 (r1 x') (r1 x')\<^esub> r2\<^bsub>(r1 x') x'\<^esub> y'"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>R1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1 x2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro order_equivalence_if_preorder_equivalenceI
    tdfr.order_equivalence_if_order_equivalence_mono_assms_leftI
    tdfr.order_equivalence_if_order_equivalence_mono_assms_rightI
    reflexive_on_in_field_if_transitive_if_rel_equivalence_on)
  (auto elim!: t1.preorder_equivalence_order_equivalenceE)

lemma order_equivalence_if_mono_if_preorder_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | \<eta>\<^sub>1 x2 \<le>\<^bsub>L1\<^esub> x1] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x2 \<le>\<^bsub>L1\<^esub> x3 \<and> x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3)] \<Rrightarrow> (\<ge>)) L2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | \<epsilon>\<^sub>1 x2' \<le>\<^bsub>R1\<^esub> x1'] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | (x2' \<le>\<^bsub>R1\<^esub> x3' \<and> x4' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x3')] \<Rrightarrow> (\<ge>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>R1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1 x2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro order_equivalence_if_preorder_equivalenceI'
    tdfr.l2_unit_bi_rel_selfI tdfr.r2_counit_bi_rel_selfI
    tdfr.left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_leftI
    flip.tdfr.left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_leftI
    tdfr.left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_rightI
    flip.tdfr.left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_rightI
    t1.galois_connection_left_right_if_transitive_if_order_equivalence
    flip.t1.galois_connection_left_right_if_transitive_if_order_equivalence
    reflexive_on_in_field_if_transitive_if_rel_equivalence_on)
  (auto elim!: t1.preorder_equivalence_order_equivalenceE)

theorem order_equivalence_if_mono_if_preorder_equivalenceI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1' x2' \<Colon> (\<ge>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x1' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro order_equivalence_if_mono_if_preorder_equivalenceI
    tdfr.galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI
    flip.tdfr.galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI
    tdfr.transitive_left2_if_preorder_equivalenceI
    tdfr.transitive_right2_if_preorder_equivalenceI
    t1.preorder_on_in_field_left_if_transitive_if_order_equivalence
    flip.t1.preorder_on_in_field_left_if_transitive_if_order_equivalence
    t1.galois_equivalence_left_right_if_transitive_if_order_equivalence
    flip.t1.galois_equivalence_left_right_if_transitive_if_order_equivalence)
  (auto elim!: t1.preorder_equivalence_order_equivalenceE
    t2.preorder_equivalence_order_equivalenceE)

end


paragraph \<open>Monotone Function Relator\<close>

context transport_Mono_Fun_Rel
begin

interpretation flip : transport_Mono_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2 .

lemma inflationary_on_unitI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "inflationary_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2"
  and "inflationary_on (in_codom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  shows "inflationary_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  using assms by (intro tpdfr.inflationary_on_unitI
    tfr.mono_wrt_rel_leftI flip.tfr.mono_wrt_rel_leftI)
  simp_all

lemma deflationary_on_counitI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "deflationary_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>) \<epsilon>\<^sub>1"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2"
  and "deflationary_on (in_dom (\<le>\<^bsub>R2\<^esub>)) (\<le>\<^bsub>R2\<^esub>) \<epsilon>\<^sub>2"
  and "transitive (\<le>\<^bsub>R2\<^esub>)"
  shows "deflationary_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>) \<epsilon>"
  using assms by (intro tpdfr.deflationary_on_counitI
    tfr.mono_wrt_rel_leftI flip.tfr.mono_wrt_rel_leftI)
  simp_all

lemma rel_equivalence_on_unitI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "rel_equivalence_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2"
  and "rel_equivalence_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  shows "rel_equivalence_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  using assms by (intro tpdfr.rel_equivalence_on_unitI
    tfr.mono_wrt_rel_leftI flip.tfr.mono_wrt_rel_leftI)
  simp_all

lemma order_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro tpdfr.order_equivalenceI
    tfr.mono_wrt_rel_leftI flip.tfr.mono_wrt_rel_leftI)
  (auto elim!: tdfrs.t1.preorder_equivalence_order_equivalenceE
    tdfrs.t2.preorder_equivalence_order_equivalenceE)

end


end