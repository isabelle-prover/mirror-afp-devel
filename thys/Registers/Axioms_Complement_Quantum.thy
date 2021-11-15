section \<open>Quantum instantiation of complements\<close>

theory Axioms_Complement_Quantum
  imports Laws_Quantum Finite_Tensor_Product Quantum_Extra
begin

no_notation m_inv ("inv\<index> _" [81] 80)
no_notation Lattice.join (infixl "\<squnion>\<index>" 65)

typedef ('a::finite,'b::finite) complement_domain = \<open>{..< if CARD('b) div CARD('a) \<noteq> 0 then CARD('b) div CARD('a) else 1}\<close>
  by auto

instance complement_domain :: (finite, finite) finite
proof intro_classes
  have \<open>inj Rep_complement_domain\<close>
    by (simp add: Rep_complement_domain_inject inj_on_def)
  moreover have \<open>finite (range Rep_complement_domain)\<close>
    by (metis finite_lessThan type_definition.Rep_range type_definition_complement_domain)
  ultimately show \<open>finite (UNIV :: ('a,'b) complement_domain set)\<close>
    using finite_image_iff by blast
qed

lemma CARD_complement_domain: 
  assumes \<open>CARD('b::finite) = n * CARD('a::finite)\<close>
  shows \<open>CARD(('a,'b) complement_domain) = n\<close>
proof -
  from assms have \<open>n > 0\<close>
    by (metis zero_less_card_finite zero_less_mult_pos2)
  have *: \<open>inj Rep_complement_domain\<close>
    by (simp add: Rep_complement_domain_inject inj_on_def)
  moreover have \<open>card (range (Rep_complement_domain :: ('a,'b) complement_domain \<Rightarrow> _)) = n\<close>
    apply (subst type_definition.Rep_range[OF type_definition_complement_domain])
    using assms \<open>n > 0\<close> by simp
  ultimately show ?thesis
    by (metis card_image)
qed


lemma register_decomposition:
  fixes \<Phi> :: \<open>'a::finite update \<Rightarrow> 'b::finite update\<close>
  assumes [simp]: \<open>register \<Phi>\<close>
  shows \<open>\<exists>U :: ('a \<times> ('a, 'b) complement_domain) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> 
              (\<forall>\<theta>. \<Phi> \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun))\<close>
  \<comment> \<open>Proof based on @{cite daws21unitalanswer}\<close>
proof -
  note [[simproc del: compatibility_warn]]
  fix \<xi>0 :: 'a

  have [simp]: \<open>clinear \<Phi>\<close>
    by simp

  define P where \<open>P i = Proj (ccspan {ket i})\<close> for i :: 'a
  have P_butter: \<open>P i = selfbutterket i\<close> for i
    by (simp add: P_def butterfly_eq_proj)

  define P' where \<open>P' i = \<Phi> (P i)\<close> for i :: 'a
  have proj_P': \<open>is_Proj (P' i)\<close> for i
    by (simp add: P_def P'_def register_projector)
  have \<open>(\<Sum>i\<in>UNIV. P i) = id_cblinfun\<close>
    using sum_butterfly_ket P_butter by simp
  then have sumP'id: \<open>(\<Sum>i\<in>UNIV. P' i) = id_cblinfun\<close>
    unfolding P'_def 
    apply (subst complex_vector.linear_sum[OF \<open>clinear \<Phi>\<close>, symmetric])
    by auto

  define S where \<open>S i = P' i *\<^sub>S \<top>\<close> for i :: 'a
  have P'id: \<open>P' i *\<^sub>V \<psi> = \<psi>\<close> if \<open>\<psi> \<in> space_as_set (S i)\<close> for i \<psi>
    using S_def that proj_P'
    by (metis cblinfun_fixes_range is_Proj_algebraic)

  obtain B0 where finiteB0: \<open>finite (B0 i)\<close> and cspanB0: \<open>cspan (B0 i) = space_as_set (S i)\<close> for i
    apply atomize_elim apply (simp flip: all_conj_distrib) apply (rule choice)
    by (meson cfinite_dim_finite_subspace_basis csubspace_space_as_set)

  obtain B where orthoB: \<open>is_ortho_set (B i)\<close>
    and normalB: \<open>\<And>b. b \<in> B i \<Longrightarrow> norm b = 1\<close>
    and cspanB: \<open>cspan (B i) = cspan (B0 i)\<close>
    and finiteB: \<open>finite (B i)\<close> for i
    apply atomize_elim apply (simp flip: all_conj_distrib) apply (rule choice)
    using orthonormal_basis_of_cspan[OF finiteB0] by blast

  from cspanB cspanB0 have cspanB: \<open>cspan (B i) = space_as_set (S i)\<close> for i
    by simp
  then have ccspanB: \<open>ccspan (B i) = S i\<close> for i
    by (metis ccspan.rep_eq closure_finite_cspan finiteB space_as_set_inject)
  from orthoB have indepB: \<open>cindependent (B i)\<close> for i
    by (simp add: Complex_Inner_Product.is_ortho_set_cindependent)

  have orthoBiBj: \<open>is_orthogonal x y\<close> if \<open>x \<in> B i\<close> and \<open>y \<in> B j\<close> and \<open>i \<noteq> j\<close> for x y i j
  proof -
    from \<open>x \<in> B i\<close> obtain x' where x: \<open>x = P' i *\<^sub>V x'\<close>
      by (metis S_def cblinfun_fixes_range complex_vector.span_base cspanB is_Proj_idempotent proj_P')
    from \<open>y \<in> B j\<close> obtain y' where y: \<open>y = P' j *\<^sub>V y'\<close>
      by (metis S_def cblinfun_fixes_range complex_vector.span_base cspanB is_Proj_idempotent proj_P')
    have \<open>cinner x y = cinner (P' i *\<^sub>V x') (P' j *\<^sub>V  y')\<close>
      using x y by simp
    also have \<open>\<dots> = cinner (P' j *\<^sub>V P' i *\<^sub>V x') y'\<close>
      by (metis cinner_adj_left is_Proj_algebraic proj_P')
    also have \<open>\<dots> = cinner (\<Phi> (P j o\<^sub>C\<^sub>L P i) *\<^sub>V x') y'\<close>
      unfolding P'_def register_mult[OF \<open>register \<Phi>\<close>, symmetric] by simp
    also have \<open>\<dots> = cinner (\<Phi> (selfbutterket j o\<^sub>C\<^sub>L selfbutterket i) *\<^sub>V x') y'\<close>
      unfolding P_butter by simp
    also have \<open>\<dots> = cinner (\<Phi> 0 *\<^sub>V x') y'\<close>
      by (metis butterfly_comp_butterfly complex_vector.scale_eq_0_iff orthogonal_ket that(3))
    also have \<open>\<dots> = 0\<close>
      by (simp add: complex_vector.linear_0)
    finally show ?thesis
      by -
  qed


  define B' where \<open>B' = (\<Union>i\<in>UNIV. B i)\<close>

  have P'B: \<open>P' i = Proj (ccspan (B i))\<close> for i
    unfolding ccspanB S_def
    using proj_P' Proj_on_own_range'[symmetric] is_Proj_algebraic by blast

  have \<open>(\<Sum>i\<in>UNIV. P' i) = Proj (ccspan B')\<close>
  proof (unfold B'_def, use finite[of UNIV] in induction)
    case empty
    show ?case by auto
  next
    case (insert j M)
    have \<open>(\<Sum>i\<in>insert j M. P' i) = P' j + (\<Sum>i\<in>M. P' i)\<close>
      by (meson insert.hyps(1) insert.hyps(2) sum.insert)
    also have \<open>\<dots> = Proj (ccspan (B j)) + Proj (ccspan (\<Union>i\<in>M. B i))\<close>
      unfolding P'B insert.IH[symmetric] by simp
    also have \<open>\<dots> = Proj (ccspan (B j \<union> (\<Union>i\<in>M. B i)))\<close>
      apply (rule Proj_orthog_ccspan_union[symmetric])
      using orthoBiBj insert.hyps(2) by auto
    also have \<open>\<dots> = Proj (ccspan (\<Union>i\<in>insert j M. B i))\<close>
      by auto
    finally show ?case
      by simp
  qed

  with sumP'id 
  have ccspanB': \<open>ccspan B' = \<top>\<close>
    by (metis Proj_range cblinfun_image_id)
  hence cspanB': \<open>cspan B' = UNIV\<close>
    by (metis B'_def finiteB ccspan.rep_eq finite_UN_I finite_class.finite_UNIV closure_finite_cspan top_ccsubspace.rep_eq)

  from orthoBiBj orthoB have orthoB': \<open>is_ortho_set B'\<close>
    unfolding B'_def is_ortho_set_def by blast
  then have indepB': \<open>cindependent B'\<close>
    using is_ortho_set_cindependent by blast
  have cardB': \<open>card B' = CARD('b)\<close>
    apply (subst complex_vector.dim_span_eq_card_independent[symmetric])
     apply (rule indepB')
    apply (subst cspanB')
    using cdim_UNIV_ell2 by auto

  from orthoBiBj orthoB
  have Bdisj: \<open>B i \<inter> B j = {}\<close> if \<open>i \<noteq> j\<close> for i j
    unfolding is_ortho_set_def
    apply auto by (metis cinner_eq_zero_iff that)

  have cardBsame: \<open>card (B i) = card (B j)\<close> for i j
  proof -
    define Si_to_Sj where \<open>Si_to_Sj i j \<psi> = \<Phi> (butterket j i) *\<^sub>V \<psi>\<close> for i j \<psi>
    have S2S2S: \<open>Si_to_Sj j i (Si_to_Sj i j \<psi>) = \<psi>\<close> if \<open>\<psi> \<in> space_as_set (S i)\<close> for i j \<psi>
      using that P'id
      by (simp add: Si_to_Sj_def cblinfun_apply_cblinfun_compose[symmetric] register_mult P_butter P'_def)
    also have lin[simp]: \<open>clinear (Si_to_Sj i j)\<close> for i j
      unfolding Si_to_Sj_def by simp
    have S2S: \<open>Si_to_Sj i j x \<in> space_as_set (S j)\<close> for i j x
    proof -
      have \<open>Si_to_Sj i j x = P' j *\<^sub>V Si_to_Sj i j x\<close>
        by (simp add: Si_to_Sj_def cblinfun_apply_cblinfun_compose[symmetric] register_mult P_butter P'_def)
      also have \<open>P' j *\<^sub>V Si_to_Sj i j x \<in> space_as_set (S j)\<close>
        by (simp add: S_def)
      finally show ?thesis by -
    qed
    have bij: \<open>bij_betw (Si_to_Sj i j) (space_as_set (S i)) (space_as_set (S j))\<close>
      apply (rule bij_betwI[where g=\<open>Si_to_Sj j i\<close>])
      using S2S S2S2S by (auto intro!: funcsetI)
    have \<open>cdim (space_as_set (S i)) = cdim (space_as_set (S j))\<close>
      using lin apply (rule isomorphic_equal_cdim[where f=\<open>Si_to_Sj i j\<close>])
      using bij apply (auto simp: bij_betw_def)
      by (metis complex_vector.span_span cspanB)
    then show ?thesis
      by (metis complex_vector.dim_span_eq_card_independent cspanB indepB)
  qed

  have CARD'b: \<open>CARD('b) = card (B \<xi>0) * CARD('a)\<close>
  proof -
    have \<open>CARD('b) = card B'\<close>
      using cardB' by simp
    also have \<open>\<dots> = (\<Sum>i\<in>UNIV. card (B i))\<close>
      unfolding B'_def apply (rule card_UN_disjoint)
      using finiteB Bdisj by auto
    also have \<open>\<dots> = (\<Sum>(i::'a)\<in>UNIV. card (B \<xi>0))\<close>
      using cardBsame by metis
    also have \<open>\<dots> = card (B \<xi>0) * CARD('a)\<close>
      by auto
    finally show ?thesis by -
  qed

  obtain f where bij_f: \<open>bij_betw f (UNIV::('a,'b) complement_domain set) (B \<xi>0)\<close>
    apply atomize_elim apply (rule finite_same_card_bij)
    using finiteB CARD_complement_domain[OF CARD'b] by auto

  define u where \<open>u = (\<lambda>(\<xi>,\<alpha>). \<Phi> (butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>)\<close> for \<xi> :: 'a and \<alpha> :: \<open>('a,'b) complement_domain\<close>
  obtain U where Uapply: \<open>U *\<^sub>V ket \<xi>\<alpha> = u \<xi>\<alpha>\<close> for \<xi>\<alpha>
    apply atomize_elim
    apply (rule exI[of _ \<open>cblinfun_extension (range ket) (\<lambda>k. u (inv ket k))\<close>])
    apply (subst cblinfun_extension_apply)
      apply (rule cblinfun_extension_exists_finite_dim)
    by (auto simp add: inj_ket cindependent_ket)

  define eqa where \<open>eqa a b = (if a = b then 1 else 0 :: complex)\<close> for a b :: 'a
  define eqc where \<open>eqc a b = (if a = b then 1 else 0 :: complex)\<close> for a b :: \<open>('a,'b) complement_domain\<close>
  define eqac where \<open>eqac a b = (if a = b then 1 else 0 :: complex)\<close> for a b :: \<open>'a * ('a,'b) complement_domain\<close>

  have \<open>cinner (U *\<^sub>V ket \<xi>\<alpha>) (U *\<^sub>V ket \<xi>'\<alpha>') = eqac \<xi>\<alpha> \<xi>'\<alpha>'\<close> for \<xi>\<alpha> \<xi>'\<alpha>'
  proof -
    obtain \<xi> \<alpha> \<xi>' \<alpha>' where \<xi>\<alpha>: \<open>\<xi>\<alpha> = (\<xi>,\<alpha>)\<close> and \<xi>'\<alpha>': \<open>\<xi>'\<alpha>' = (\<xi>',\<alpha>')\<close>
      apply atomize_elim by auto
    have \<open>cinner (U *\<^sub>V ket (\<xi>,\<alpha>)) (U *\<^sub>V ket (\<xi>', \<alpha>')) = cinner (\<Phi> (butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>) (\<Phi> (butterket \<xi>' \<xi>0) *\<^sub>V f \<alpha>')\<close>
      unfolding Uapply u_def by simp
    also have \<open>\<dots> = cinner ((\<Phi> (butterket \<xi>' \<xi>0))* *\<^sub>V \<Phi> (butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (simp add: cinner_adj_left)
    also have \<open>\<dots> = cinner (\<Phi> (butterket \<xi>' \<xi>0 *) *\<^sub>V \<Phi> (butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (metis (no_types, lifting) assms register_def)
    also have \<open>\<dots> = cinner (\<Phi> (butterket \<xi>0 \<xi>' o\<^sub>C\<^sub>L butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (simp add: register_mult cblinfun_apply_cblinfun_compose[symmetric])
    also have \<open>\<dots> = cinner (\<Phi> (eqa \<xi>' \<xi> *\<^sub>C selfbutterket \<xi>0) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      apply simp by (metis eqa_def cinner_ket)
    also have \<open>\<dots> = eqa \<xi>' \<xi> * cinner (\<Phi> (selfbutterket \<xi>0) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (smt (verit, ccfv_threshold) \<open>clinear \<Phi>\<close> eqa_def cblinfun.scaleC_left cinner_commute 
              cinner_scaleC_left cinner_zero_right complex_cnj_one complex_vector.linear_scale)
    also have \<open>\<dots> = eqa \<xi>' \<xi> * cinner (P' \<xi>0 *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      using P_butter P'_def by simp
    also have \<open>\<dots> = eqa \<xi>' \<xi> * cinner (f \<alpha>) (f \<alpha>')\<close>
      apply (subst P'id)
       apply (metis bij_betw_imp_surj_on bij_f complex_vector.span_base cspanB rangeI)
      by simp
    also have \<open>\<dots> = eqa \<xi>' \<xi> * eqc \<alpha> \<alpha>'\<close>
      using bij_f orthoB normalB unfolding is_ortho_set_def eqc_def apply auto
       apply (metis bij_betw_imp_surj_on cnorm_eq_1 rangeI)
      by (smt (z3) bij_betw_iff_bijections iso_tuple_UNIV_I)
    finally show ?thesis
      by (simp add: eqa_def eqac_def eqc_def \<xi>'\<alpha>' \<xi>\<alpha>)
  qed
  then have \<open>isometry U\<close>
    apply (rule_tac orthogonal_on_basis_is_isometry[where B=\<open>range ket\<close>])
    using eqac_def by auto

  have \<open>U* o\<^sub>C\<^sub>L \<Phi> (butterket \<xi> \<eta>) o\<^sub>C\<^sub>L U = butterket \<xi> \<eta> \<otimes>\<^sub>o id_cblinfun\<close> for \<xi> \<eta>
  proof (rule equal_ket, rename_tac \<xi>1\<alpha>)
    fix \<xi>1\<alpha> obtain \<xi>1 :: 'a and \<alpha> :: \<open>('a,'b) complement_domain\<close> where \<xi>1\<alpha>: \<open>\<xi>1\<alpha> = (\<xi>1,\<alpha>)\<close> 
      apply atomize_elim by auto
    have \<open>(U* o\<^sub>C\<^sub>L \<Phi> (butterket \<xi> \<eta>) o\<^sub>C\<^sub>L U) *\<^sub>V ket \<xi>1\<alpha> = U* *\<^sub>V \<Phi> (butterket \<xi> \<eta>) *\<^sub>V \<Phi> (butterket \<xi>1 \<xi>0) *\<^sub>V f \<alpha>\<close>
      unfolding cblinfun_apply_cblinfun_compose \<xi>1\<alpha> Uapply u_def by simp
    also have \<open>\<dots> = U* *\<^sub>V \<Phi> (butterket \<xi> \<eta> o\<^sub>C\<^sub>L butterket \<xi>1 \<xi>0) *\<^sub>V f \<alpha>\<close>
      by (metis (no_types, lifting) assms butterfly_comp_butterfly lift_cblinfun_comp(4) register_mult)
    also have \<open>\<dots> = U* *\<^sub>V \<Phi> (eqa \<eta> \<xi>1 *\<^sub>C butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>\<close>
      by (simp add: eqa_def cinner_ket)
    also have \<open>\<dots> = eqa \<eta> \<xi>1 *\<^sub>C U* *\<^sub>V \<Phi> (butterket \<xi> \<xi>0) *\<^sub>V f \<alpha>\<close>
      by (simp add: complex_vector.linear_scale)
    also have \<open>\<dots> = eqa \<eta> \<xi>1 *\<^sub>C U* *\<^sub>V U *\<^sub>V ket (\<xi>, \<alpha>)\<close>
      unfolding Uapply u_def by simp
    also from \<open>isometry U\<close> have \<open>\<dots> = eqa \<eta> \<xi>1 *\<^sub>C ket (\<xi>, \<alpha>)\<close>
      unfolding cblinfun_apply_cblinfun_compose[symmetric] by simp
    also have \<open>\<dots> = (butterket \<xi> \<eta> *\<^sub>V ket \<xi>1) \<otimes>\<^sub>s ket \<alpha>\<close>
      by (simp add: eqa_def tensor_ell2_scaleC1)
    also have \<open>\<dots> = (butterket \<xi> \<eta> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket \<xi>1\<alpha>\<close>
      by (simp add: \<xi>1\<alpha> tensor_op_ket)
    finally show \<open>(U* o\<^sub>C\<^sub>L \<Phi> (butterket \<xi> \<eta>) o\<^sub>C\<^sub>L U) *\<^sub>V ket \<xi>1\<alpha> = (butterket \<xi> \<eta> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket \<xi>1\<alpha>\<close>
      by -
  qed
  then have 1: \<open>U* o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L U = \<theta> \<otimes>\<^sub>o id_cblinfun\<close> for \<theta>
    apply (rule_tac clinear_eq_butterfly_ketI[THEN fun_cong, where x=\<theta>])
    by (auto intro!: clinearI simp add: bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose complex_vector.linear_add complex_vector.linear_scale)

  have \<open>unitary U\<close>
  proof -
    have \<open>\<Phi> (butterket \<xi> \<xi>1) *\<^sub>S \<top> \<le> U *\<^sub>S \<top>\<close> for \<xi> \<xi>1
    proof -
      have *: \<open>\<Phi> (butterket \<xi> \<xi>0) *\<^sub>V b \<in> space_as_set (U *\<^sub>S \<top>)\<close> if \<open>b \<in> B \<xi>0\<close> for b
        apply (subst asm_rl[of \<open>\<Phi> (butterket \<xi> \<xi>0) *\<^sub>V b = u (\<xi>, inv f b)\<close>])
         apply (simp add: u_def, metis bij_betw_inv_into_right bij_f that)
        by (metis Uapply cblinfun_apply_in_image)

      have \<open>\<Phi> (butterket \<xi> \<xi>1) *\<^sub>S \<top> = \<Phi> (butterket \<xi> \<xi>0) *\<^sub>S \<Phi> (butterket \<xi>0 \<xi>0) *\<^sub>S \<Phi> (butterket \<xi>0 \<xi>1) *\<^sub>S \<top>\<close>
        unfolding cblinfun_compose_image[symmetric] register_mult[OF assms]
        by simp
      also have \<open>\<dots> \<le> \<Phi> (butterket \<xi> \<xi>0) *\<^sub>S \<Phi> (butterket \<xi>0 \<xi>0) *\<^sub>S \<top>\<close>
        by (meson cblinfun_image_mono top_greatest)
      also have \<open>\<dots> = \<Phi> (butterket \<xi> \<xi>0) *\<^sub>S S \<xi>0\<close>
        by (simp add: S_def P'_def P_butter)
      also have \<open>\<dots> = \<Phi> (butterket \<xi> \<xi>0) *\<^sub>S ccspan (B \<xi>0)\<close>
        by (simp add: ccspanB)
      also have \<open>\<dots> = ccspan (\<Phi> (butterket \<xi> \<xi>0) ` B \<xi>0)\<close>
        by (meson cblinfun_image_ccspan)
      also have \<open>\<dots> \<le> U *\<^sub>S \<top>\<close>
        by (rule ccspan_leqI, use * in auto)
      finally show ?thesis by -
    qed
    moreover have \<open>\<Phi> id_cblinfun *\<^sub>S \<top> \<le> (SUP \<xi>\<in>UNIV. \<Phi> (selfbutterket \<xi>) *\<^sub>S \<top>)\<close>
      unfolding sum_butterfly_ket[symmetric]
      apply (subst complex_vector.linear_sum, simp)
      by (rule cblinfun_sum_image_distr)
    ultimately have \<open>\<Phi> id_cblinfun *\<^sub>S \<top> \<le> U *\<^sub>S \<top>\<close>
      apply auto by (meson SUP_le_iff order.trans)
    then have \<open>U *\<^sub>S \<top> = \<top>\<close>
      apply auto
      using top.extremum_unique by blast
    with \<open>isometry U\<close> show \<open>unitary U\<close>
      by (rule surj_isometry_is_unitary)
  qed

  have \<open>\<Phi> \<theta> = U o\<^sub>C\<^sub>L (\<theta> \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L U*\<close> for \<theta>
  proof -
    from \<open>unitary U\<close>
    have \<open>\<Phi> \<theta> = (U o\<^sub>C\<^sub>L U*) o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L (U o\<^sub>C\<^sub>L U*)\<close>
      by simp
    also have \<open>\<dots> = U o\<^sub>C\<^sub>L (U*  o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L U) o\<^sub>C\<^sub>L U*\<close>
      by (simp add: cblinfun_assoc_left)
    also have \<open>\<dots> = U o\<^sub>C\<^sub>L (\<theta> \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L U*\<close>
      using 1 by simp
    finally show ?thesis
      by -
  qed

  with \<open>unitary U\<close> show ?thesis
    by (auto simp: sandwich_def)
qed

lemma register_decomposition_converse: 
  assumes \<open>unitary U\<close>
  shows \<open>register (\<lambda>x. sandwich U (id_cblinfun \<otimes>\<^sub>o x))\<close>
  using _ unitary_sandwich_register apply (rule register_comp[unfolded o_def])
  using assms by auto


lemma register_inj: \<open>inj F\<close> if \<open>register F\<close>
proof -
  obtain U :: \<open>('a \<times> ('a, 'b) complement_domain) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    where \<open>unitary U\<close> and F: \<open>F a = sandwich U (a \<otimes>\<^sub>o id_cblinfun)\<close> for a
    apply atomize_elim using \<open>register F\<close> by (rule register_decomposition)
  have \<open>inj (sandwich U)\<close>
    by (smt (verit, best) \<open>unitary U\<close> cblinfun_assoc_left inj_onI sandwich_def cblinfun_compose_id_right cblinfun_compose_id_left unitary_def)
  moreover have \<open>inj (\<lambda>a::'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L _. a \<otimes>\<^sub>o id_cblinfun)\<close>
    by (rule inj_tensor_left, simp)
  ultimately show \<open>inj F\<close>
    unfolding F
    by (smt (z3) inj_def) 
qed

lemma iso_register_decomposition:
  assumes [simp]: \<open>iso_register F\<close>
  shows \<open>\<exists>U. unitary U \<and> F = sandwich U\<close>
proof -
  have [simp]: \<open>register F\<close>
    using assms iso_register_is_register by blast 

  let ?ida = \<open>id_cblinfun :: ('a, 'b) complement_domain ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close>

  from register_decomposition[OF \<open>register F\<close>]
  obtain V :: \<open>('a \<times> ('a, 'b) complement_domain) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where \<open>unitary V\<close>
    and FV: \<open>F \<theta> = sandwich V (\<theta> \<otimes>\<^sub>o ?ida)\<close> for \<theta>
    by auto

  have \<open>surj F\<close>
    by (meson assms iso_register_inv_comp2 surj_iff)
  have surj_tensor: \<open>surj (\<lambda>a::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2. a \<otimes>\<^sub>o ?ida)\<close>
    apply (rule surj_from_comp[where g=\<open>sandwich V\<close>])
    using \<open>surj F\<close> apply (auto simp: FV)
    by (meson \<open>unitary V\<close> register_inj unitary_sandwich_register)
  then obtain a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close> 
    where a: \<open>a \<otimes>\<^sub>o ?ida = selfbutterket undefined \<otimes>\<^sub>o selfbutterket undefined\<close>
    by (smt (verit, best) surjD)

  then have \<open>a \<noteq> 0\<close>
    apply auto
    by (metis butterfly_apply cblinfun.zero_left complex_vector.scale_eq_0_iff ket_nonzero orthogonal_ket)

  obtain \<gamma> where \<gamma>: \<open>?ida = \<gamma> *\<^sub>C selfbutterket undefined\<close>
    apply atomize_elim
    using a \<open>a \<noteq> 0\<close> by (rule tensor_op_almost_injective)
  then have \<open>?ida (ket undefined) = \<gamma> *\<^sub>C (selfbutterket undefined *\<^sub>V ket undefined)\<close>
    by (simp add: \<open>id_cblinfun = \<gamma> *\<^sub>C selfbutterket undefined\<close> scaleC_cblinfun.rep_eq)
  then have \<open>ket undefined = \<gamma> *\<^sub>C ket undefined\<close>
    by (metis butterfly_apply cinner_scaleC_right id_cblinfun_apply cinner_ket_same mult.right_neutral scaleC_one)
  then have \<open>\<gamma> = 1\<close>
    by (smt (z3) \<gamma> butterfly_apply butterfly_scaleC_left cblinfun_id_cblinfun_apply complex_vector.scale_cancel_right cinner_ket_same ket_nonzero)

  define T U where \<open>T = CBlinfun (\<lambda>\<psi>. \<psi> \<otimes>\<^sub>s ket undefined)\<close> and \<open>U = V o\<^sub>C\<^sub>L T\<close>
  have T: \<open>T \<psi> = \<psi> \<otimes>\<^sub>s ket undefined\<close> for \<psi>
    unfolding T_def
    apply (subst bounded_clinear_CBlinfun_apply)
    by (auto intro!: bounded_clinear_finite_dim clinear_tensor_ell22)
  have sandwich_T: \<open>sandwich T a = a \<otimes>\<^sub>o ?ida\<close> for a
    apply (rule fun_cong[where x=a])
    apply (rule clinear_eq_butterfly_ketI)
      apply auto
    by (metis (no_types, opaque_lifting) Misc.sandwich_def T \<gamma> \<open>\<gamma> = 1\<close> adj_cblinfun_compose butterfly_adjoint cblinfun_comp_butterfly scaleC_one tensor_butterfly)

  have \<open>F (butterfly x y) = V o\<^sub>C\<^sub>L (butterfly x y \<otimes>\<^sub>o ?ida) o\<^sub>C\<^sub>L V*\<close> for x y
    by (simp add: Misc.sandwich_def FV)
  also have \<open>\<dots> x y = V o\<^sub>C\<^sub>L (butterfly (T x) (T y)) o\<^sub>C\<^sub>L V*\<close> for x y
    by (simp add: T \<gamma> \<open>\<gamma> = 1\<close>)
  also have \<open>\<dots> x y = U o\<^sub>C\<^sub>L (butterfly x y) o\<^sub>C\<^sub>L U*\<close> for x y
    by (simp add: U_def butterfly_comp_cblinfun cblinfun_comp_butterfly)
  finally have F_rep:  \<open>F a = U o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L U*\<close> for a
    apply (rule_tac fun_cong[where x=a])
    apply (rule_tac clinear_eq_butterfly_ketI)
      apply auto
    by (metis (no_types, lifting) cblinfun_apply_clinear clinear_iff sandwich_apply)

  have \<open>isometry T\<close>
    apply (rule orthogonal_on_basis_is_isometry[where B=\<open>range ket\<close>])
    by (auto simp: T)
  moreover have \<open>T *\<^sub>S \<top> = \<top>\<close>
  proof -
    have 1: \<open>\<phi> \<otimes>\<^sub>s \<xi> \<in> range ((*\<^sub>V) T)\<close> for \<phi> \<xi>
    proof -
      have \<open>T *\<^sub>V (cinner (ket undefined) \<xi> *\<^sub>C \<phi>) = \<phi> \<otimes>\<^sub>s (cinner (ket undefined) \<xi> *\<^sub>C ket undefined)\<close>
        by (simp add: T tensor_ell2_scaleC2)
      also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s (selfbutterket undefined *\<^sub>V \<xi>)\<close>
        by simp
      also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s (?ida *\<^sub>V \<xi>)\<close>
        by (simp add: \<gamma> \<open>\<gamma> = 1\<close>)
      also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s \<xi>\<close>
        by simp
      finally show ?thesis
        by (metis range_eqI)
    qed

    have \<open>\<top> \<le> ccspan {ket x | x. True}\<close>
      by (simp add: full_SetCompr_eq)
    also have \<open>\<dots> \<le> ccspan {\<phi> \<otimes>\<^sub>s \<xi> | \<phi> \<xi>. True}\<close>
      apply (rule ccspan_mono)
      by (auto simp flip: tensor_ell2_ket)
    also from 1 have \<open>\<dots> \<le> ccspan (range ((*\<^sub>V) T))\<close>
      by (auto intro!: ccspan_mono)
    also have \<open>\<dots> = T *\<^sub>S \<top>\<close>
      by (metis (mono_tags, opaque_lifting) calculation cblinfun_image_ccspan cblinfun_image_mono eq_iff top_greatest)
    finally show \<open>T *\<^sub>S \<top> = \<top>\<close>
      using top.extremum_uniqueI by blast
  qed

  ultimately have \<open>unitary T\<close>
    by (rule surj_isometry_is_unitary)
  then have \<open>unitary U\<close>
    by (simp add: U_def \<open>unitary V\<close>)

  from F_rep \<open>unitary U\<close> show ?thesis
    by (auto simp: sandwich_def[abs_def])
qed

lemma complement_exists:
  fixes F :: \<open>'a::finite update \<Rightarrow> 'b::finite update\<close>
  assumes \<open>register F\<close>
  shows \<open>\<exists>G :: ('a, 'b) complement_domain update \<Rightarrow> 'b update. compatible F G \<and> iso_register (F;G)\<close>
proof -
  note [[simproc del: Laws_Quantum.compatibility_warn]]
  obtain U :: \<open>('a \<times> ('a, 'b) complement_domain) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    where [simp]: "unitary U" and F: \<open>F a = sandwich U (a \<otimes>\<^sub>o id_cblinfun)\<close> for a
    apply atomize_elim using assms by (rule register_decomposition)
  define G :: \<open>(('a, 'b) complement_domain) update \<Rightarrow> 'b update\<close> where \<open>G b = sandwich U (id_cblinfun \<otimes>\<^sub>o b)\<close> for b
  have [simp]: \<open>register G\<close>
    unfolding G_def apply (rule register_decomposition_converse) by simp
  have \<open>F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a\<close> for a b
  proof -
    have \<open>F a o\<^sub>C\<^sub>L G b = sandwich U (a \<otimes>\<^sub>o b)\<close>
      apply (auto simp: F G_def sandwich_def)
      by (metis (no_types, lifting) \<open>unitary U\<close> isometryD cblinfun_assoc_left(1) comp_tensor_op cblinfun_compose_id_right cblinfun_compose_id_left unitary_isometry)
    moreover have \<open>G b o\<^sub>C\<^sub>L F a = sandwich U (a \<otimes>\<^sub>o b)\<close>
      apply (auto simp: F G_def sandwich_def)
      by (metis (no_types, lifting) \<open>unitary U\<close> isometryD cblinfun_assoc_left(1) comp_tensor_op cblinfun_compose_id_right cblinfun_compose_id_left unitary_isometry)
    ultimately show ?thesis by simp
  qed
  then have [simp]: \<open>compatible F G\<close>
    by (auto simp: compatible_def \<open>register F\<close> \<open>register G\<close>)
  moreover have \<open>iso_register (F;G)\<close>
  proof -
    have \<open>(F;G) (a \<otimes>\<^sub>o b) = sandwich U (a \<otimes>\<^sub>o b)\<close> for a b
      apply (auto simp: register_pair_apply F G_def sandwich_def)
      by (metis (no_types, lifting) \<open>unitary U\<close> isometryD cblinfun_assoc_left(1) comp_tensor_op cblinfun_compose_id_right cblinfun_compose_id_left unitary_isometry)
    then have FG: \<open>(F;G) = sandwich U\<close>
      apply (rule tensor_extensionality[rotated -1])
      by (simp_all add: bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose bounded_cbilinear.add_right clinearI)
    define I where \<open>I = sandwich (U*)\<close> for x
    have [simp]: \<open>register I\<close>
      by (simp add: I_def unitary_sandwich_register)
    have \<open>I o (F;G) = id\<close> and FGI: \<open>(F;G) o I = id\<close>
       apply (auto intro!:ext simp: I_def[abs_def] FG sandwich_def)
       apply (metis (no_types, opaque_lifting) \<open>unitary U\<close> isometryD cblinfun_assoc_left(1) cblinfun_compose_id_right cblinfun_compose_id_left unitary_isometry)
      by (metis (no_types, lifting) \<open>unitary U\<close> cblinfun_assoc_left(1) cblinfun_compose_id_left cblinfun_compose_id_right unitaryD2)
    then show \<open>iso_register (F;G)\<close>
      by (auto intro!: iso_registerI)
  qed
  ultimately show ?thesis
    apply (rule_tac exI[of _ G]) by (auto)
qed

definition \<open>commutant F = {x. \<forall>y\<in>F. x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x}\<close>

lemma commutant_exchange:
  fixes F :: \<open>'a::finite update \<Rightarrow> 'b::finite update\<close>
  assumes \<open>iso_register F\<close>
  shows \<open>commutant (F ` X) = F ` commutant X\<close>
proof (rule Set.set_eqI)
  fix x :: \<open>'b update\<close>
  from assms
  obtain G where \<open>F o G = id\<close> and \<open>G o F = id\<close> and [simp]: \<open>register G\<close>
    using iso_register_def by blast
  from assms have [simp]: \<open>register F\<close>
    using iso_register_def by blast
  have \<open>x \<in> commutant (F ` X) \<longleftrightarrow> (\<forall>y \<in> F ` X. x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x)\<close>
    by (simp add: commutant_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y \<in> F ` X. G x o\<^sub>C\<^sub>L G y = G y o\<^sub>C\<^sub>L G x)\<close>
    by (metis (no_types, opaque_lifting) \<open>F \<circ> G = id\<close> \<open>G o F = id\<close> \<open>register G\<close> comp_def eq_id_iff register_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y \<in> X. G x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L G x)\<close>
    by (simp add: \<open>G \<circ> F = id\<close> pointfree_idE)
  also have \<open>\<dots> \<longleftrightarrow> G x \<in> commutant X\<close>
    by (simp add: commutant_def)
  also have \<open>\<dots> \<longleftrightarrow> x \<in> F ` commutant X\<close>
    by (metis (no_types, opaque_lifting) \<open>G \<circ> F = id\<close> \<open>F \<circ> G = id\<close> image_iff pointfree_idE)
  finally show \<open>x \<in> commutant (F ` X) \<longleftrightarrow> x \<in> F ` commutant X\<close>
    by -
qed

lemma commutant_tensor1: \<open>commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun)) = range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
proof (rule Set.set_eqI, rule iffI)
  fix x :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close>
  fix \<gamma> :: 'a
  assume \<open>x \<in> commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
  then have comm: \<open>(a \<otimes>\<^sub>o id_cblinfun) *\<^sub>V x *\<^sub>V \<psi> = x *\<^sub>V (a \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<psi>\<close> for a \<psi>
    by (metis (mono_tags, lifting) commutant_def mem_Collect_eq rangeI cblinfun_apply_cblinfun_compose)

  obtain x' where x': \<open>cinner (ket j) (x' *\<^sub>V ket l) = cinner (ket (\<gamma>,j)) (x *\<^sub>V ket (\<gamma>,l))\<close> for j l
  proof atomize_elim
    obtain \<psi> where \<psi>: \<open>cinner (ket j) (\<psi> l) = cinner (ket (\<gamma>, j)) (x *\<^sub>V ket (\<gamma>, l))\<close> for l j
      apply (atomize_elim, rule choice, rule allI)
      apply (rule_tac x=\<open>Abs_ell2 (\<lambda>j. cinner (ket (\<gamma>, j)) (x *\<^sub>V ket (\<gamma>, l)))\<close> in exI)
      by (simp add: cinner_ket_left Abs_ell2_inverse)
    obtain x' where \<open>x' *\<^sub>V ket l = \<psi> l\<close> for l
      apply atomize_elim
      apply (rule exI[of _ \<open>cblinfun_extension (range ket) (\<lambda>l. \<psi> (inv ket l))\<close>])
      apply (subst cblinfun_extension_apply)
        apply (rule cblinfun_extension_exists_finite_dim)
      by (auto simp add: inj_ket cindependent_ket)
    with \<psi> have \<open>cinner (ket j) (x' *\<^sub>V ket l) = cinner (ket (\<gamma>, j)) (x *\<^sub>V ket (\<gamma>, l))\<close> for j l
      by auto
    then show \<open>\<exists>x'. \<forall>j l. cinner (ket j) (x' *\<^sub>V ket l) = cinner (ket (\<gamma>, j)) (x *\<^sub>V ket (\<gamma>, l))\<close>
      by auto
  qed

  have \<open>cinner (ket (i,j)) (x *\<^sub>V ket (k,l)) = cinner (ket (i,j)) ((id_cblinfun \<otimes>\<^sub>o x') *\<^sub>V ket (k,l))\<close> for i j k l
  proof -
    have \<open>cinner (ket (i,j)) (x *\<^sub>V ket (k,l))
        = cinner ((butterket i \<gamma> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,j)) (x *\<^sub>V (butterket k \<gamma> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      by (auto simp: tensor_op_ket)
    also have \<open>\<dots> = cinner (ket (\<gamma>,j)) ((butterket \<gamma> i \<otimes>\<^sub>o id_cblinfun) *\<^sub>V x *\<^sub>V (butterket k \<gamma> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      by (metis (no_types, lifting) cinner_adj_left butterfly_adjoint id_cblinfun_adjoint tensor_op_adjoint)
    also have \<open>\<dots> = cinner (ket (\<gamma>,j)) (x *\<^sub>V (butterket \<gamma> i \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L butterket k \<gamma> \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      unfolding comm by (simp add: cblinfun_apply_cblinfun_compose)
    also have \<open>\<dots> = cinner (ket i) (ket k) * cinner (ket (\<gamma>,j)) (x *\<^sub>V ket (\<gamma>,l))\<close>
      by (simp add: comp_tensor_op tensor_op_ket tensor_op_scaleC_left)
    also have \<open>\<dots> = cinner (ket i) (ket k) * cinner (ket j) (x' *\<^sub>V ket l)\<close>
      by (simp add: x')
    also have \<open>\<dots> = cinner (ket (i,j)) ((id_cblinfun \<otimes>\<^sub>o x') *\<^sub>V ket (k,l))\<close>
      apply (simp add: tensor_op_ket)
      by (simp flip: tensor_ell2_ket)
    finally show ?thesis by -
  qed
  then have \<open>x = (id_cblinfun \<otimes>\<^sub>o x')\<close>
    by (auto intro!: equal_ket cinner_ket_eqI)
  then show \<open>x \<in> range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
    by auto
next
  fix x :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close>
  assume \<open>x \<in> range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
  then obtain b where x: \<open>x = id_cblinfun \<otimes>\<^sub>o b\<close>
    by auto
  then show \<open>x \<in> commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
    by (auto simp: x commutant_def comp_tensor_op)
qed

lemma complement_range:
  assumes [simp]: \<open>compatible F G\<close> and [simp]: \<open>iso_register (F;G)\<close>
  shows \<open>range G = commutant (range F)\<close>
proof -
  have [simp]: \<open>register F\<close> \<open>register G\<close>
    using assms compatible_def by metis+
  have [simp]: \<open>(F;G) (a \<otimes>\<^sub>o b) = F a o\<^sub>C\<^sub>L G b\<close> for a b
    using Laws_Quantum.register_pair_apply assms by blast
  have [simp]: \<open>range F = (F;G) ` range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun)\<close>
    by force
  have [simp]: \<open>range G = (F;G) ` range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
    by force
  show \<open>range G = commutant (range F)\<close>
    by (simp add: commutant_exchange commutant_tensor1)
qed

lemma same_range_equivalent:
  fixes F :: \<open>'a::finite update \<Rightarrow> 'c::finite update\<close> and G :: \<open>'b::finite update \<Rightarrow> 'c::finite update\<close>
  assumes [simp]: \<open>register F\<close> and [simp]: \<open>register G\<close>
  assumes \<open>range F = range G\<close>
  shows \<open>equivalent_registers F G\<close>
proof -
  have G_rangeF[simp]: \<open>G x \<in> range F\<close> for x
    by (simp add: assms)
  have F_rangeG[simp]: \<open>F x \<in> range G\<close> for x
    by (simp add: assms(3)[symmetric])
  have [simp]: \<open>inj F\<close> and [simp]: \<open>inj G\<close>
    by (simp_all add: register_inj)
  have [simp]: \<open>clinear F\<close> \<open>clinear G\<close>
    by simp_all
  define I J where \<open>I x = inv F (G x)\<close> and \<open>J y = inv G (F y)\<close> for x y
  have addI: \<open>I (x + y) = I x + I y\<close> for x y
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst complex_vector.linear_add[OF \<open>clinear F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)+
    by (simp add: complex_vector.linear_add)
  have addJ: \<open>J (x + y) = J x + J y\<close> for x y
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst complex_vector.linear_add[OF \<open>clinear G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    by (simp add: complex_vector.linear_add)
  have scaleI: \<open>I (r *\<^sub>C x) = r *\<^sub>C I x\<close> for r x
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst complex_vector.linear_scale[OF \<open>clinear F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)+
    by (simp add: complex_vector.linear_scale)
  have scaleJ: \<open>J (r *\<^sub>C x) = r *\<^sub>C J x\<close> for r x
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst complex_vector.linear_scale[OF \<open>clinear G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    by (simp add: complex_vector.linear_scale)
  have unitalI: \<open>I id_cblinfun = id_cblinfun\<close>
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F])
     apply auto
    by (metis register_of_id G_rangeF assms(2))
  have unitalJ: \<open>J id_cblinfun = id_cblinfun\<close>
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G])
     apply auto
    by (metis register_of_id F_rangeG assms(1))
  have multI: \<open>I (a o\<^sub>C\<^sub>L b) = I a o\<^sub>C\<^sub>L I b\<close> for a b
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst register_mult[symmetric, OF \<open>register F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)+
    by (simp add: register_mult)
  have multJ: \<open>J (a o\<^sub>C\<^sub>L b) = J a o\<^sub>C\<^sub>L J b\<close> for a b
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst register_mult[symmetric, OF \<open>register G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    by (simp add: register_mult)
  have adjI: \<open>I (a*) = (I a)*\<close> for a
    unfolding I_def
    apply (rule injD[OF \<open>inj F\<close>])
    apply (subst register_adjoint[OF \<open>register F\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)+
    using assms(2) register_adjoint by blast
  have adjJ: \<open>J (a*) = (J a)*\<close> for a
    unfolding J_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst register_adjoint[OF \<open>register G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    using assms(1) register_adjoint by blast

  from addI scaleI unitalI multI adjI
  have \<open>register I\<close>
    unfolding register_def by (auto intro!: clinearI)
  from addJ scaleJ unitalJ multJ adjJ
  have \<open>register J\<close>
    unfolding register_def by (auto intro!: clinearI)

  have \<open>I o J = id\<close>
    unfolding I_def J_def o_def
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)
    apply (subst Hilbert_Choice.inv_f_f[OF \<open>inj F\<close>])
    by auto
  have \<open>J o I = id\<close>
    unfolding I_def J_def o_def
    apply (subst Hilbert_Choice.f_inv_into_f[where f=F], simp)
    apply (subst Hilbert_Choice.inv_f_f[OF \<open>inj G\<close>])
    by auto

  from \<open>I o J = id\<close> \<open>J o I = id\<close> \<open>register I\<close> \<open>register J\<close>
  have \<open>iso_register I\<close>
    using iso_register_def by blast

  have \<open>F o I = G\<close>
    unfolding I_def o_def
    by (subst Hilbert_Choice.f_inv_into_f[where f=F], auto)

  with \<open>iso_register I\<close> show ?thesis
    unfolding equivalent_registers_def by auto
qed

lemma complement_unique:
  assumes "compatible F G" and \<open>iso_register (F;G)\<close>
  assumes "compatible F H" and \<open>iso_register (F;H)\<close>
  shows \<open>equivalent_registers G H\<close>
  by (metis assms compatible_def complement_range same_range_equivalent)

end
