\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Galois Connection\<close>
theory Transport_Functions_Galois_Connection
  imports
    Transport_Functions_Galois_Property
    Transport_Functions_Monotone
begin

paragraph \<open>Dependent Function Relator\<close>

context transport_Dep_Fun_Rel
begin

subparagraph \<open>Lemmas for Monotone Function Relator\<close>

lemma galois_connection_left_right_if_galois_connection_mono_2_assms_leftI:
  assumes galois_conn1: "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_R1: "reflexive_on (in_codom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and R2_le1: "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and mono_l2_2: "([x' \<Colon> in_codom (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x'] \<Rrightarrow>\<^sub>m
    [in_field (\<le>\<^bsub>L2 x1 (r1 x')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x'\<^esub>)) l2"
  shows "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x2')\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>)"
proof -
  show "([in_codom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x2')\<^esub>)"
    if "x1' \<le>\<^bsub>R1\<^esub> x2'" for x1' x2'
  proof -
    from galois_conn1 \<open>x1' \<le>\<^bsub>R1\<^esub> x2'\<close> have "r1 x1' \<le>\<^bsub>L1\<^esub> r1 x2'" "r1 x2' \<^bsub>L1\<^esub>\<lessapprox> x2'"
      using refl_R1 by (auto intro: t1.right_left_Galois_if_reflexive_onI)
    with mono_l2_2 show ?thesis using R2_le1 \<open>x1' \<le>\<^bsub>R1\<^esub> x2'\<close> by fastforce
  qed
  show "([in_dom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>)"
    if "x \<le>\<^bsub>L1\<^esub> x" for x
  proof -
    from galois_conn1 \<open>x \<le>\<^bsub>L1\<^esub> x\<close> have "x \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x" "\<eta>\<^sub>1 x \<^bsub>L1\<^esub>\<lessapprox> l1 x"
      by (auto intro!: t1.right_left_Galois_if_right_relI
        t1.rel_unit_if_left_rel_if_half_galois_prop_right_if_mono_wrt_rel
          [unfolded t1.unit_eq])
    with mono_l2_2 show ?thesis by fastforce
  qed
qed

lemma galois_connection_left_right_if_galois_connection_mono_assms_leftI:
  assumes galois_conn1: "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_R1: "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and R2_le1: "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and mono_l2: "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  shows "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x1' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
  and "([x' \<Colon> in_codom (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x'] \<Rrightarrow>\<^sub>m
    [in_field (\<le>\<^bsub>L2 x1 (r1 x')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x'\<^esub>)) l2"
proof -
  show "([in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x1' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
    if "x1' \<le>\<^bsub>R1\<^esub> x2'" for x1' x2'
  proof -
    from galois_conn1 \<open>x1' \<le>\<^bsub>R1\<^esub> x2'\<close> have "r1 x1' \<le>\<^bsub>L1\<^esub> r1 x1'" "r1 x1' \<^bsub>L1\<^esub>\<lessapprox> x1'"
      using refl_R1 by blast+
    with mono_l2 show ?thesis using \<open>x1' \<le>\<^bsub>R1\<^esub> x2'\<close> R2_le1 by (auto 9 0)
  qed
  from mono_l2 show "([x' \<Colon> in_codom (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x'] \<Rrightarrow>\<^sub>m
    [in_field (\<le>\<^bsub>L2 x1 (r1 x')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x'\<^esub>)) l2" using refl_R1 by blast
qed

text \<open>In theory, the following lemmas can be obtained by taking the flipped,
inverse interpretation of the locale; however, rewriting the assumptions is more
involved than simply copying and adapting above proofs.\<close>

lemma galois_connection_left_right_if_galois_connection_mono_2_assms_rightI:
  assumes galois_conn1: "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_L1: "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and L2_le2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and mono_r2_2: "([x \<Colon> in_dom (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>\<^sub>m
    [in_field (\<le>\<^bsub>R2 (l1 x) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x (r1 x2')\<^esub>)) r2"
  shows "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x1)\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
proof -
  show "([in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x1)\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
    if "x1 \<le>\<^bsub>L1\<^esub> x2" for x1 x2
  proof -
    from galois_conn1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have "x1 \<^bsub>L1\<^esub>\<lessapprox> l1 x1" "l1 x1 \<le>\<^bsub>R1\<^esub> l1 x2"
      using refl_L1 by (auto intro!: t1.left_Galois_left_if_reflexive_on_if_half_galois_prop_rightI)
    with mono_r2_2 show ?thesis using L2_le2 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> by (auto 9 0)
  qed
  show "([in_codom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
    if "x' \<le>\<^bsub>R1\<^esub> x'" for x'
  proof -
    from galois_conn1 \<open>x' \<le>\<^bsub>R1\<^esub> x'\<close> have "r1 x' \<^bsub>L1\<^esub>\<lessapprox> \<epsilon>\<^sub>1 x'" "\<epsilon>\<^sub>1 x' \<le>\<^bsub>R1\<^esub> x'"
      by (auto intro!: t1.left_Galois_left_if_left_relI
        t1.counit_rel_if_right_rel_if_half_galois_prop_left_if_mono_wrt_rel
          [unfolded t1.counit_eq])
    with mono_r2_2 show ?thesis by fastforce
  qed
qed

lemma galois_connection_left_right_if_galois_connection_mono_assms_rightI:
  assumes galois_conn1: "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_L1: "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and L2_le2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and mono_r2: "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  shows "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub>)"
  and "([x \<Colon> in_dom (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>\<^sub>m
    [in_field (\<le>\<^bsub>R2 (l1 x) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x (r1 x2')\<^esub>)) r2"
proof -
  show "([in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub>)"
    if "x1 \<le>\<^bsub>L1\<^esub> x2" for x1 x2
  proof -
    from galois_conn1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have "x2 \<^bsub>L1\<^esub>\<lessapprox> l1 x2" "l1 x2 \<le>\<^bsub>R1\<^esub> l1 x2"
      using refl_L1 by (blast intro: t1.left_Galois_left_if_reflexive_on_if_half_galois_prop_rightI)+
    with mono_r2 show ?thesis using \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> L2_le2 by fastforce
  qed
  from mono_r2 show "([x \<Colon> in_dom (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>\<^sub>m
    [in_field (\<le>\<^bsub>R2 (l1 x) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x (r1 x2')\<^esub>)) r2" using refl_L1 by blast
qed

end


paragraph \<open>Monotone Dependent Function Relator\<close>

context transport_Mono_Dep_Fun_Rel
begin

interpretation flip : transport_Mono_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2 .

lemma galois_connection_left_rightI:
  assumes "(tdfr.L \<Rrightarrow>\<^sub>m tdfr.R) l" and "(tdfr.R \<Rrightarrow>\<^sub>m tdfr.L) r"
  and "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<unlhd> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
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
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms
  by (intro galois_connectionI galois_prop_left_rightI' mono_wrt_rel_leftI
    flip.mono_wrt_rel_leftI)
  auto

lemma galois_connection_left_rightI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ((\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<unlhd> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x1' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x2')\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x1)\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms
  by (intro galois_connection_left_rightI tdfr.mono_wrt_rel_left_if_transitiveI
    tdfr.mono_wrt_rel_right_if_transitiveI)
  auto

lemma galois_connection_left_right_if_galois_connectionI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<stileturn> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x1' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x2')\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x1)\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms
  by (intro galois_connection_left_rightI'
    tdfr.mono_wrt_rel_left2_if_mono_wrt_rel_left2_if_left_GaloisI
    tdfr.mono_wrt_rel_right2_if_mono_wrt_rel_right2_if_left_GaloisI)
  (auto 7 0)

corollary galois_connection_left_right_if_galois_connectionI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow>
    ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<stileturn> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x1' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
  and "([x' \<Colon> in_codom (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x'] \<Rrightarrow>\<^sub>m
    [in_field (\<le>\<^bsub>L2 x1 (r1 x')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x'\<^esub>)) l2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub>)"
  and "([x \<Colon> in_dom (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>\<^sub>m
    [in_field (\<le>\<^bsub>R2 (l1 x) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_connection_left_right_if_galois_connectionI
    tdfr.galois_connection_left_right_if_galois_connection_mono_2_assms_leftI
    tdfr.galois_connection_left_right_if_galois_connection_mono_2_assms_rightI)
  (auto intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom in_field_if_in_codom)

corollary galois_connection_left_right_if_mono_if_galois_connectionI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<stileturn> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_connection_left_right_if_galois_connectionI'
    tdfr.galois_connection_left_right_if_galois_connection_mono_assms_leftI
    tdfr.galois_connection_left_right_if_galois_connection_mono_assms_rightI)
  auto

corollary galois_connection_left_right_if_mono_if_galois_connectionI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<stileturn> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "([_ x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x2 \<le>\<^bsub>L1\<^esub> x3 \<and> x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3)] \<Rrightarrow> (\<ge>)) L2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | \<epsilon>\<^sub>1 x2' \<le>\<^bsub>R1\<^esub> x1'] \<Rrightarrow>\<^sub>m [x3' _ \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_connection_left_right_if_mono_if_galois_connectionI
    tdfr.left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_leftI
    tdfr.left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_rightI)
  auto

end


paragraph \<open>Monotone Function Relator\<close>

context transport_Mono_Fun_Rel
begin

interpretation flip : transport_Mono_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2 .

lemma galois_connection_left_rightI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<stileturn> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "transitive (\<le>\<^bsub>R2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro tpdfr.galois_connectionI galois_prop_left_rightI
    mono_wrt_rel_leftI flip.mono_wrt_rel_leftI)
  auto

end


end