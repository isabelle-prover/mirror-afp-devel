(*  Title:   Alaoglu_Theorem.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section  \<open>Alaoglu's Theorem\<close>
theory Alaoglu_Theorem
  imports "Lemmas_Levy_Prokhorov"
          "Riesz_Representation.Riesz_Representation"
begin

text \<open> We prove (a special case of) Alaoglu's theorem for the space of continuous functions.
       We refer to Section~9 of the lecture note by Heil~\cite{Heil}.\<close>

subsection \<open> Metrizability of the Space of Uniformly Bounded Positive Linear Functionals \<close>
lemma metrizable_functional:
  fixes X :: "'a topology" and r :: real
  defines "prod_space \<equiv> powertop_real (mspace (cfunspace X euclidean_metric))"
  defines "B \<equiv> {\<phi>\<in>topspace prod_space. \<phi> (\<lambda>x\<in>topspace X. 1) \<le> r \<and> positive_linear_functional_on_CX X \<phi>}"
  defines "\<Phi> \<equiv> subtopology prod_space B"
  assumes compact: "compact_space X" and met: "metrizable_space X"
  shows "metrizable_space \<Phi>"
proof(cases "X = trivial_topology")
  case True
  hence "metrizable_space prod_space"
    by(auto simp: prod_space_def metrizable_space_product_topology metrizable_space_euclidean intro!: countable_finite)
  thus ?thesis
    using \<Phi>_def metrizable_space_subtopology by blast
next
  case X_ne:False
  have Haus: "Hausdorff_space X"
    using met metrizable_imp_Hausdorff_space by blast
  consider "r \<ge> 0" | "r < 0"
    by fastforce
  then show ?thesis
  proof cases
    case r:1
    have B: "B \<subseteq> topspace prod_space"
      by(auto simp: B_def)
    have ext_eq: "\<And>f::'a \<Rightarrow> real. f \<in> mspace (cfunspace X euclidean_metric) \<Longrightarrow> (\<lambda>x\<in>topspace X. f x) = f"
      by (auto simp: extensional_def)
    have met1: "metrizable_space (mtopology_of (cfunspace X euclidean_metric))"
      by (metis Metric_space.metrizable_space_mtopology Metric_space_mspace_mdist mtopology_of_def)
    have "separable_space (mtopology_of (cfunspace X (euclidean_metric :: real metric)))"
    proof -
      have "separable_space (mtopology_of (cfunspace X (Met_TC.Self :: real metric)))"
        using Met_TC.Metric_space_axioms  Met_TC.separable_space_iff_second_countable
        by(auto intro!: Metric_space.separable_space_cfunspace[OF _ _ _ met compact])
      thus ?thesis
        by (simp add: Met_TC.Self_def euclidean_metric_def)
    qed
    then obtain F where dense:"mdense_of (cfunspace X (euclidean_metric :: real metric)) F" and F_count: "countable F"
      using separable_space_def2 by blast
    have "infinite (topspace (mtopology_of (cfunspace X (euclidean_metric :: real metric))))"
    proof(rule infinite_super[where S="(\<lambda>n::nat. \<lambda>x\<in>topspace X. real n) ` UNIV"])
      show "infinite  (range (\<lambda>n. \<lambda>x\<in>topspace X. real n))"
      proof(intro range_inj_infinite inj_onI)
        fix n m
        assume h:"(\<lambda>x\<in>topspace X. real n) = (\<lambda>x\<in>topspace X. real m)"
        from X_ne obtain x where "x \<in> topspace X" by fastforce
        with fun_cong[OF h,of x] show "n = m"
          by simp
      qed
    qed(auto simp: bounded_iff)
    from countable_as_injective_image[OF F_count dense_in_infinite[OF metrizable_imp_t1_space[OF met1] this dense]]
    obtain gn :: "nat \<Rightarrow> _" where gn: "F = range gn" "inj gn"
      by blast
    then have gn_in: "\<And>n. gn n \<in> F" "\<And>n. gn n \<in> mspace (cfunspace X euclidean_metric)"
      using dense_in_subset[OF dense] by auto
    hence gn_ext: "\<And>n. (\<lambda>x\<in>topspace X. gn n x) = gn n"
      by(auto intro!: ext_eq)     
    define d :: "[('a \<Rightarrow> real) \<Rightarrow> real, ('a \<Rightarrow> real) \<Rightarrow> real] \<Rightarrow> real"
      where "d \<equiv> (\<lambda>\<phi> \<psi>. (\<Sum>n. (1 / 2) ^ n * mdist (capped_metric 1 euclidean_metric)
                                                   (\<phi> (\<lambda>x\<in>topspace X. gn n x)) (\<psi> (\<lambda>x\<in>topspace X. gn n x))))"
    have smble[simp]: "summable (\<lambda>n. (1 / 2) ^ n * mdist (capped_metric 1 (euclidean_metric :: real metric)) (a n) (b n))"
      for a b
      by(rule summable_comparison_test'[where N=0 and g="\<lambda>n. (1 / 2) ^ n * 1"]) (auto intro!: mdist_capped)
    interpret d: Metric_space "topspace \<Phi>" d
    proof
      show "\<And>x y. 0 \<le> d x y"
        by(auto intro!: suminf_nonneg simp: d_def)
      show "\<And>x y. d x y = d y x"
        by(auto simp: d_def simp: mdist_commute)
    next
      fix \<phi> \<psi>
      assume h:"\<phi> \<in> topspace \<Phi>" "\<psi> \<in> topspace \<Phi>"
      show "d \<phi> \<psi> = 0 \<longleftrightarrow> \<phi> = \<psi>"
      proof
        assume "d \<phi> \<psi> = 0"
        then have "\<forall>n. (1 / 2) ^ n * mdist (capped_metric 1 euclidean_metric)
                                           (\<phi> (\<lambda>x\<in>topspace X. gn n x)) (\<psi> (\<lambda>x\<in>topspace X. gn n x)) = 0"
          by(intro suminf_eq_zero_iff[THEN iffD1]) (auto simp: d_def)
        hence eq:"\<And>n. \<phi> (\<lambda>x\<in>topspace X. gn n x) = \<psi> (\<lambda>x\<in>topspace X. gn n x)"
          by simp
        show "\<phi> = \<psi>"
        proof
          fix f
          consider "f \<notin> mspace (cfunspace X (euclidean_metric :: real metric))"
            | "f \<in> mspace (cfunspace X (euclidean_metric :: real metric))"
            by blast
          thus "\<phi> f = \<psi> f"
          proof cases
            case 1
            then show ?thesis
              using h by(auto simp: \<Phi>_def prod_space_def PiE_def extensional_def simp del: mspace_cfunspace)
          next
            case f:2
            then have "positive_linear_functional_on_CX X \<phi>" "positive_linear_functional_on_CX X \<psi>"
              using h by(auto simp: \<Phi>_def topspace_subtopology_subset[OF B] B_def)
            from Riesz_representation_real_compact_metrizable[OF compact met this(1)]
              Riesz_representation_real_compact_metrizable[OF compact met this(2)]
            obtain N L where
              N: "sets N = sets (borel_of X)" "finite_measure N"
              "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> \<phi> (restrict f (topspace X)) = integral\<^sup>L N f"
              and L: "sets L = sets (borel_of X)" "finite_measure L"
              "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> \<psi> (restrict f (topspace X)) = integral\<^sup>L L f"
              by auto
            have f_ext:"(\<lambda>x\<in>topspace X. f x) = f"
              using f by (auto simp: extensional_def)
            have "\<phi> f = \<phi> (\<lambda>x\<in>topspace X. f x)"
              by(simp add: f_ext)
            also have "... = integral\<^sup>L N f"
              using f by(auto intro!: N)
            also have "... = integral\<^sup>L L f"
            proof(rule finite_measure_integral_eq_dense[where F=F and X=X])
              fix g
              assume "g \<in> F"
              then obtain n where n:"g = gn n"
                using gn by fast
              hence "integral\<^sup>L N g = integral\<^sup>L N (gn n)"
                by simp
              also have "... = \<phi> (\<lambda>x\<in>topspace X. gn n x)"
                using gn_in by(auto intro!: N(3)[symmetric])
              also have "... = integral\<^sup>L L g"
                using gn_in by(auto simp: eq n intro!: L(3))
              finally show "integral\<^sup>L N g = integral\<^sup>L L g" .
            qed(use N L dense f in auto)
            also have "... = \<psi> (\<lambda>x\<in>topspace X. f x)"
              using f by(auto intro!: L(3)[symmetric])
            also have "... = \<psi> f"
              by(simp add: f_ext)
            finally show ?thesis .
          qed
        qed
      qed (auto simp add: d_def capped_metric_mdist)
    next
      fix \<phi>1 \<phi>2 \<phi>3
      assume h: "\<phi>1 \<in> topspace \<Phi>" "\<phi>2 \<in> topspace \<Phi>" "\<phi>3 \<in> topspace \<Phi>"
      show "d \<phi>1 \<phi>3 \<le> d \<phi>1 \<phi>2 + d \<phi>2 \<phi>3"
      proof -
        have "d \<phi>1 \<phi>3 \<le> (\<Sum>n. (1 / 2) ^ n * mdist (capped_metric 1 euclidean_metric)
                                                   (\<phi>1 (\<lambda>x\<in>topspace X. gn n x)) (\<phi>2 (\<lambda>x\<in>topspace X. gn n x))
                             + (1 / 2) ^ n * mdist (capped_metric 1 euclidean_metric)
                                                   (\<phi>2 (\<lambda>x\<in>topspace X. gn n x)) (\<phi>3 (\<lambda>x\<in>topspace X. gn n x)))"
          by(auto intro!: suminf_le mdist_triangle summable_add[OF smble smble,simplified distrib_left[symmetric]]
              simp: d_def distrib_left[symmetric])
        also have "... = d \<phi>1 \<phi>2 + d \<phi>2 \<phi>3"
          by(simp add: suminf_add d_def)
        finally show ?thesis .
      qed
    qed
    have "\<Phi> = d.mtopology"
      unfolding topology_eq
    proof safe
      have "continuous_map d.mtopology (subtopology prod_space B) id"
        unfolding continuous_map_in_subtopology prod_space_def id_apply image_id continuous_map_componentwise
      proof safe
        fix f :: "'a \<Rightarrow> real"
        assume f: "f \<in> mspace (cfunspace X (euclidean_metric))"
        hence f_ext: "(\<lambda>x\<in>topspace X. f x) = f"
          by(auto intro!: ext_eq)
        show "continuous_map d.mtopology euclideanreal (\<lambda>x. x f)"
          unfolding continuous_map_iff_limit_seq[OF d.first_countable_mtopology]
        proof safe
          fix \<phi>n \<phi>
          assume \<phi>_limit:"limitin d.mtopology \<phi>n \<phi> sequentially"
          have "(\<lambda>n. \<phi>n n f) \<longlonglongrightarrow> \<phi> f"
          proof(rule LIMSEQ_I)
            fix e :: real
            assume e: "e > 0"
            from f mdense_of_def3[THEN iffD1,OF dense] obtain fn where fn:
              "\<And>n. fn n \<in> F" "limitin (mtopology_of (cfunspace X euclidean_metric)) fn f sequentially"
              by fast
            with f dense_in_subset[OF dense] have fn_ext:"\<And>n. (\<lambda>x\<in>topspace X. fn n x) = fn n"
              by(intro ext_eq) auto
            define a0 where "a0 \<equiv> (SOME n. \<forall>x\<in>topspace X. \<bar>fn n x - f x\<bar> \<le> (1 / 3) * (1 / (r + 1)) * e)"
            have a0:"\<forall>x\<in>topspace X. \<bar>fn a0 x - f x\<bar> \<le> (1 / 3) * (1 / (r + 1)) * e"
              unfolding a0_def
            proof(rule someI_ex)
              have "\<And>e. e > 0 \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. mdist (cfunspace X euclidean_metric) (fn n) f < e"
                by (metis Metric_space.limit_metric_sequentially Metric_space_mspace_mdist fn(2) mtopology_of_def)
              from this[of "((1 / 3) * (1 / (r + 1)) * e)"]
              obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> mdist (cfunspace X euclidean_metric) (fn n) f < ((1 / 3) * (1 / (r + 1)) * e)"
                using e r by auto
              hence "mdist (cfunspace X euclidean_metric) (fn N) f \<le> ((1 / 3) * (1 / (r + 1)) * e)"
                by fastforce
              from mdist_cfunspace_imp_mdist_le[OF _ _ this]
              have le:"\<And>x. x \<in> topspace X \<Longrightarrow> \<bar>fn N x - f x\<bar> \<le> ((1 / 3) * (1 / (r + 1)) * e)"
                using fn(1)[of N] dense_in_subset[OF dense] f dist_real_def by auto
              thus "\<exists>n. \<forall>x\<in>topspace X. \<bar>fn n x - f x\<bar> \<le> 1 / 3 * (1 / (r + 1)) * e"
                by(auto intro!: exI[where x=N])
            qed
            obtain l where l: "fn a0 = gn l"
              using fn gn by blast
            have "\<And>e. e > 0 \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. \<phi>n n \<in> topspace \<Phi> \<and> d (\<phi>n n) \<phi> < e"
              using \<phi>_limit by(fastforce simp: mtopology_of_def d.limit_metric_sequentially)
            from this[of "(1 / 2) ^ l * (1 / 3) * min 3 e"] e
            obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> \<phi>n n \<in> topspace \<Phi>"
              "\<And>n. n \<ge> N \<Longrightarrow> d (\<phi>n n) \<phi> < (1 / 2) ^ l * (1 / 3) * min 3 e"
              by auto
            show "\<exists>no. \<forall>n\<ge>no. norm (\<phi>n n f - \<phi> f) < e"
            proof(safe intro!: exI[where x=N])
              fix n
              assume n: "N \<le> n"
              have "norm (\<phi>n n f - \<phi> f) \<le> \<bar>\<phi>n n (fn a0) - \<phi> (fn a0)\<bar> + \<bar>\<phi> (fn a0) - \<phi> f\<bar> + \<bar>\<phi>n n (fn a0) - \<phi>n n f\<bar>"
                by fastforce
              also have "... < (1 / 3) * e + (1 / 3) * e + (1 / 3) * e"
              proof -
                have 1: "\<bar>\<phi>n n (fn a0) - \<phi> (fn a0)\<bar> < (1 / 3) * e"
                proof(rule ccontr)
                  assume " \<not> \<bar>\<phi>n n (fn a0) - \<phi> (fn a0)\<bar> < 1 / 3 * e"
                  then have 1:"\<bar>\<phi>n n (fn a0) - \<phi> (fn a0)\<bar> \<ge> (1 / 3) * e"
                    by linarith
                  have le1: "\<bar>\<phi>n n (fn a0) - \<phi> (fn a0)\<bar> < 1"
                  proof (rule ccontr)
                    assume "\<not> \<bar>\<phi>n n (fn a0) - \<phi> (fn a0)\<bar> < 1"
                    then have contr:"\<bar>\<phi>n n (fn a0) - \<phi> (fn a0)\<bar> \<ge> 1"
                      by linarith
                    consider "e > 3" | "e \<le> 3"
                      by fastforce
                    then show False
                    proof cases
                      case 1
                      with N[OF n] have "d (\<phi>n n) \<phi> < (1 / 2) ^ l"
                        by simp
                      also have "... = (\<Sum>m. if m = l then (1 / 2) ^ l else 0)"
                        using suminf_split_initial_segment[where f="\<lambda>m. if m = l then (1 / 2) ^ l else (0 :: real)" and k="Suc l"]
                        by simp
                      also have "... \<le> d (\<phi>n n) \<phi>"
                        unfolding d_def
                      proof(rule suminf_le)
                        fix m
                        show "(if m = l then (1 / 2) ^ l else 0)
                               \<le> (1 / 2) ^ m * mdist (capped_metric 1 euclidean_metric)
                                                      (\<phi>n n (restrict (gn m) (topspace X)))
                                                      (\<phi> (restrict (gn m) (topspace X)))"
                          using contr by(auto simp: l gn_ext capped_metric_mdist dist_real_def)
                      qed auto
                      finally show False
                        by blast
                    next
                      case 2
                      then have "(1 / 2) ^ l * (1 / 3) * min 3 e \<le> (1 / 2)^l"
                        by simp
                      also have "... = (\<Sum>m. if m = l then (1 / 2) ^ l else 0)"
                        using suminf_split_initial_segment[where f="\<lambda>m. if m = l then (1 / 2) ^ l else (0 :: real)" and k="Suc l"]
                        by simp
                      also have "... \<le> d (\<phi>n n) \<phi>"
                        unfolding d_def
                      proof(rule suminf_le)
                        fix m
                        show "(if m = l then (1 / 2) ^ l else 0)
                               \<le> (1 / 2) ^ m * mdist (capped_metric 1 euclidean_metric)
                                                      (\<phi>n n (restrict (gn m) (topspace X)))
                                                      (\<phi> (restrict (gn m) (topspace X)))"
                          using contr by(auto simp: l gn_ext capped_metric_mdist dist_real_def)
                      qed auto
                      also have "... < (1 / 2) ^ l * (1 / 3) * min 3 e"
                        by(rule N[OF n])
                      finally show False by simp
                    qed
                  qed
                  hence mdist1: "mdist (capped_metric 1 euclidean_metric)
                                       (\<phi>n n (restrict (gn l) (topspace X)))
                                       (\<phi> (restrict (gn l) (topspace X)))
                                 = \<bar>\<phi>n n (fn a0) - \<phi> (fn a0)\<bar>"
                    by(auto simp: capped_metric_mdist dist_real_def gn_ext l)
                  have "(1 / 2) ^ l * (1 / 3) * min 3 e \<le> (1 / 2) ^ l * (1 / 3) * e"
                    using e by simp
                  also have "... = (\<Sum>m. if m = l then (1 / 2) ^ l * (1 / 3) * e else 0)"
                    using suminf_split_initial_segment[where f="\<lambda>m. if m = l then (1 / 2) ^ l * (1 / 3) * e else 0" and k="Suc l"]
                    by simp
                  also have "... \<le> d (\<phi>n n) \<phi>"
                    using 1 le1 by (fastforce simp: mdist1 d_def intro!: suminf_le)
                  finally show False
                    using N[OF n] by linarith
                qed
                have 2: " \<bar>\<phi> (fn a0) - \<phi> f\<bar> \<le> (1 / 3) * e"
                proof -
                  from limitin_topspace[OF \<phi>_limit,simplified]
                  have plf:"positive_linear_functional_on_CX X \<phi>"
                    by(simp add: \<Phi>_def B_def)
                  from Riesz_representation_real_compact_metrizable[OF compact met this]
                  obtain N where N: "sets N = sets (borel_of X)" "finite_measure N"
                    "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> \<phi> (restrict f (topspace X)) = integral\<^sup>L N f"
                    by blast
                  hence space_N: "space N = topspace X"
                    by(auto cong: sets_eq_imp_space_eq simp: space_borel_of)
                  interpret N: finite_measure N by fact
                  have [measurable]: "fn a0 \<in> borel_measurable N" "f \<in> borel_measurable N"
                    using continuous_map_measurable[of X euclideanreal] fn(1) f dense_in_subset[OF dense]
                    by(auto simp: measurable_cong_sets[OF N(1) refl]
                        intro!: continuous_map_measurable[of X euclideanreal,simplified borel_of_euclidean])
                  have "\<phi> (fn a0) - \<phi> f = \<phi> (\<lambda>x\<in>topspace X. fn a0 x) - \<phi> (\<lambda>x\<in>topspace X. f x)"
                    by(simp add: fn_ext f_ext)
                  also have "... = \<phi> (\<lambda>x\<in>topspace X. fn a0 x) + \<phi> (\<lambda>x\<in>topspace X. - f x)"
                    using f by(auto intro!: pos_lin_functional_on_CX_compact_lin(1)[OF plf compact,of _ "-1",simplified,symmetric])
                  also have "... = \<phi> (\<lambda>x\<in>topspace X. fn a0 x + - f x)"
                    by(rule pos_lin_functional_on_CX_compact_lin(2)[symmetric])
                      (use fn(1) f dense_in_subset[OF dense] plf compact in auto)
                  also have "... = \<phi> (\<lambda>x\<in>topspace X. fn a0 x - f x)"
                    by simp
                  also have "... = (\<integral>x. fn a0 x - f x \<partial>N)"
                    using fn(1) f dense_in_subset[OF dense] by(auto intro!: N(3) continuous_map_diff)
                  finally have "\<bar>\<phi> (fn a0) - \<phi> f\<bar> = \<bar>(\<integral>x. fn a0 x - f x \<partial>N)\<bar>"
                    by simp
                  also have "... \<le> (\<integral>x. \<bar>fn a0 x - f x\<bar> \<partial>N)"
                    by(rule integral_abs_bound)
                  also have "... \<le> (\<integral>x. (1 / 3) * (1 / (r + 1)) * e \<partial>N)"
                    by(rule Bochner_Integration.integral_mono,insert a0)
                      (auto intro!: N.integrable_const_bound[where B="(1 / 3) * (1 / (r + 1)) * e"] simp: space_N)
                  also have "... = (1 / 3) * e * ((1 / (r + 1) * measure N (space N)))"
                    by simp
                  also have "... \<le> (1 / 3) * e"
                  proof -
                    have "measure N (space N) = (\<integral>x. 1 \<partial>N)"
                      by simp
                    also have "... = \<phi> (\<lambda>x\<in>topspace X. 1)"
                      by(intro N(3)[symmetric]) simp
                    also have "... \<le> r"
                      using limitin_topspace[OF \<phi>_limit,simplified] by(auto simp: \<Phi>_def B_def)
                    finally have "(1 / (r + 1) * measure N (space N)) \<le> 1"
                      using r by simp
                    thus ?thesis
                      unfolding mult_le_cancel_left2 using e by auto
                  qed
                  finally show ?thesis .
                qed
                have 3: " \<bar>\<phi>n n (fn a0) - \<phi>n n f\<bar> \<le> (1 / 3) * e"
                proof -
                  have plf:"positive_linear_functional_on_CX X (\<phi>n n)"
                    using N(1)[OF n] by(simp add: \<Phi>_def B_def)
                  from Riesz_representation_real_compact_metrizable[OF compact met this]
                  obtain N where N': "sets N = sets (borel_of X)" "finite_measure N"
                    "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> \<phi>n n (restrict f (topspace X)) = integral\<^sup>L N f"
                    by blast
                  hence space_N: "space N = topspace X"
                    by(auto cong: sets_eq_imp_space_eq simp: space_borel_of)
                  interpret N: finite_measure N by fact
                  have [measurable]: "fn a0 \<in> borel_measurable N" "f \<in> borel_measurable N"
                    using continuous_map_measurable[of X euclideanreal] fn(1) f dense_in_subset[OF dense]
                    by(auto simp: measurable_cong_sets[OF N'(1) refl]
                        intro!: continuous_map_measurable[of X euclideanreal,simplified borel_of_euclidean])
                  have "\<phi>n n (fn a0) - \<phi>n n f = \<phi>n n (\<lambda>x\<in>topspace X. fn a0 x) - \<phi>n n (\<lambda>x\<in>topspace X. f x)"
                    by(simp add: fn_ext f_ext)
                  also have "... = \<phi>n n (\<lambda>x\<in>topspace X. fn a0 x) + \<phi>n n (\<lambda>x\<in>topspace X. - f x)"
                    using f by(auto intro!: pos_lin_functional_on_CX_compact_lin(1)[OF plf compact,of _ "-1",simplified,symmetric])
                  also have "... = \<phi>n n (\<lambda>x\<in>topspace X. fn a0 x + - f x)"
                    by(rule pos_lin_functional_on_CX_compact_lin(2)[symmetric])
                      (use fn(1) plf compact f dense_in_subset[OF dense] in auto)
                  also have "... = \<phi>n n (\<lambda>x\<in>topspace X. fn a0 x - f x)"
                    by simp
                  also have "... = (\<integral>x. fn a0 x - f x \<partial>N)"
                    using fn(1) f dense_in_subset[OF dense] by(auto intro!: N'(3) continuous_map_diff)
                  finally have "\<bar>\<phi>n n (fn a0) - \<phi>n n f\<bar> = \<bar>(\<integral>x. fn a0 x - f x \<partial>N)\<bar>"
                    by simp
                  also have "... \<le> (\<integral>x. \<bar>fn a0 x - f x\<bar> \<partial>N)"
                    by(rule integral_abs_bound)
                  also have "... \<le> (\<integral>x. (1 / 3) * (1 / (r + 1)) * e \<partial>N)"
                    by(rule Bochner_Integration.integral_mono,insert a0)
                      (auto intro!: N.integrable_const_bound[where B="(1 / 3) * (1 / (r + 1)) * e"] simp: space_N)
                  also have "... = (1 / 3) * e * ((1 / (r + 1) * measure N (space N)))"
                    by simp
                  also have "... \<le> (1 / 3) * e"
                  proof -
                    have "measure N (space N) = (\<integral>x. 1 \<partial>N)"
                      by simp
                    also have "... = \<phi>n n (\<lambda>x\<in>topspace X. 1)"
                      by(intro N'(3)[symmetric]) simp
                    also have "... \<le> r"
                      using N(1)[OF n] by(auto simp: \<Phi>_def B_def)
                    finally have "(1 / (r + 1) * measure N (space N)) \<le> 1"
                      using r by simp
                    thus ?thesis
                      unfolding mult_le_cancel_left2 using e by auto
                  qed
                  finally show ?thesis .
                qed
                show ?thesis
                  using 1 2 3 by simp
              qed
              also have "... = e"
                by simp
              finally show "norm (\<phi>n n f - \<phi> f) < e" .
            qed
          qed
          thus "limitin euclideanreal (\<lambda>n. \<phi>n n f) (\<phi> f) sequentially"
            by simp
        qed
      next
        show "\<And>x. x \<in> topspace d.mtopology \<Longrightarrow> x \<in> extensional (mspace (cfunspace X euclidean_metric))"
          unfolding d.topspace_mtopology by (auto simp: \<Phi>_def prod_space_def extensional_def simp del: mspace_cfunspace)
      qed (simp, auto simp: \<Phi>_def)

      thus "\<And>S. openin \<Phi> S \<Longrightarrow> openin d.mtopology S"
        by (metis \<Phi>_def d.topspace_mtopology topology_finer_continuous_id)
    next
      have "continuous_map \<Phi> d.mtopology id"
        unfolding d.continuous_map_to_metric id_apply
      proof safe
        fix \<phi> and e::real
        assume \<phi>: "\<phi> \<in> topspace \<Phi>" and e: "0 < e"
        then obtain N where N: "(1 / 2)^N < e / 2"
          by (meson half_gt_zero_iff one_less_numeral_iff reals_power_lt_ex semiring_norm(76))
        define e' where "e' \<equiv> e / 2 - (1 / 2)^N"
        have e': "0 < e'"
          using N by(auto simp: e'_def)
        define U' where "U' \<equiv> \<Pi>\<^sub>E f\<in>mspace (cfunspace X euclidean_metric).
              if \<exists>n<N. f = gn n then {\<phi> (\<lambda>x\<in>topspace X. f x) - e'<..<\<phi> (\<lambda>x\<in>topspace X. f x) + e'} else UNIV"
        define U where "U \<equiv> U' \<inter> B"
        show "\<exists>U. openin \<Phi> U \<and> \<phi> \<in> U \<and> (\<forall>y\<in>U. y \<in> d.mball \<phi> e)"
        proof(safe intro!: exI[where x=U])
          show "openin \<Phi> U"
            unfolding \<Phi>_def openin_subtopology U_def
          proof(safe intro!: exI[where x=U'])
            show "openin prod_space U'"
              unfolding prod_space_def U'_def openin_PiE_gen
              by (auto simp: Let_def)
          qed
        next
          show "\<phi> \<in> U"
            unfolding U_def U'_def
          proof safe
            fix f :: "'a \<Rightarrow> real"
            assume f: "f \<in> mspace (cfunspace X euclidean_metric)"
            then show "\<phi> f \<in> (if \<exists>n<N. f = gn n
                              then {\<phi> (restrict f (topspace X)) - e'<..<\<phi> (restrict f (topspace X)) + e'}
                              else UNIV)"
              using e' by(auto simp: Let_def gn_ext)
          qed(use \<phi> \<Phi>_def prod_space_def in auto)
        next
          fix \<psi>
          assume \<psi>:"\<psi> \<in> U"
          then have \<psi>2: "\<psi> \<in> topspace \<Phi>"
            using topspace_subtopology_subset[OF B] by(auto simp: U_def \<Phi>_def)
          have \<psi>_le: "\<bar>\<phi> (\<lambda>x\<in>topspace X. gn n x) - \<psi> (\<lambda>x\<in>topspace X. gn n x)\<bar> < e'" if n: "n < N" for n
          proof -
            have "\<psi> \<in> (\<Pi>\<^sub>E f\<in>mspace (cfunspace X euclidean_metric).
                         if \<exists>n<N. f = gn n
                         then {\<phi> (restrict f (topspace X)) - e'<..<\<phi> (restrict f (topspace X)) + e'}
                         else UNIV)"
              using \<psi> by(auto simp: U_def U'_def)
            from PiE_mem[OF this gn_in(2)[of n]]
            have "\<psi> (\<lambda>x\<in>topspace X. gn n x) \<in> (if \<exists>m<N. gn n = gn m
                                              then {\<phi> (restrict (gn n) (topspace X)) - e'<..<\<phi> (restrict (gn n) (topspace X)) + e'}
                                              else UNIV)"
              by(simp add: gn_ext)
            thus ?thesis
              by (metis abs_diff_less_iff diff_less_eq greaterThanLessThan_iff n)              
          qed
          have "d \<phi> \<psi> < e"
          proof -
            have "d \<phi> \<psi> = (\<Sum>n. (1 / 2) ^ (n + N) * mdist (capped_metric 1 euclidean_metric)
                                                           (\<phi> (\<lambda>x\<in>topspace X. gn (n + N) x))
                                                           (\<psi> (\<lambda>x\<in>topspace X. gn (n + N) x)))
                          + (\<Sum>n<N. (1 / 2) ^ n * mdist (capped_metric 1 euclidean_metric)
                                                        (\<phi> (\<lambda>x\<in>topspace X. gn n x))
                                                        (\<psi> (\<lambda>x\<in>topspace X. gn n x)))"
              unfolding d_def by(rule suminf_split_initial_segment d_def) simp
            also have "... \<le> (\<Sum>n. (1 / 2) ^ (n + N))
                              + (\<Sum>n<N. (1 / 2) ^ n * mdist (capped_metric 1 euclidean_metric)
                                                            (\<phi> (\<lambda>x\<in>topspace X. gn n x))
                                                            (\<psi> (\<lambda>x\<in>topspace X. gn n x)))"
              by(auto intro!: suminf_le mdist_capped summable_ignore_initial_segment[where k=N])
            also have "... = (1 / 2)^N * 2 
                             + (\<Sum>n<N. (1 / 2) ^ n * mdist (capped_metric 1 euclidean_metric)
                                                           (\<phi> (\<lambda>x\<in>topspace X. gn n x))
                                                           (\<psi> (\<lambda>x\<in>topspace X. gn n x)))"
              using nsum_of_r'[where r="1/2" and K=1 and k=N,simplified] by simp
            also have "... \<le> (1 / 2)^N * 2
                             + (\<Sum>n<N. (1 / 2) ^ n * \<bar>\<phi> (\<lambda>x\<in>topspace X. gn n x) - \<psi> (\<lambda>x\<in>topspace X. gn n x)\<bar>)"
              by(auto intro!: sum_mono mdist_capped_le[where m="euclidean_metric :: real metric",simplified,simplified dist_real_def])
            also have "... \<le> (1 / 2)^N * 2 + (\<Sum>n<N. (1 / 2) ^ n * e')"
              using \<psi>_le by(fastforce intro!: sum_mono)
            also have "... < (1 / 2)^N * 2 + (\<Sum>n<Suc N. (1 / 2) ^ n * e')"
              using e' by(auto intro!: sum_strict_mono2)
            also have "... \<le> (1 / 2)^N * 2 + (\<Sum>n. (1 / 2) ^ n * e')"
              using e' by(auto intro!: sum_le_suminf summable_mult2 simp del: sum.lessThan_Suc)
            also have "... = (1 / 2)^N * 2 + (\<Sum>n. (1 / 2) ^ n) * e'"
              by(auto intro!: suminf_mult2[symmetric])
            also have "... = (1 / 2)^N * 2 + 2 * e'"
              by(auto simp: suminf_geometric)
            also have "... = e"
              by(auto simp: e'_def)
            finally show ?thesis .
          qed
          with \<phi> \<psi>2 show "\<psi> \<in> d.mball \<phi> e"
            by simp
        qed
      qed
      thus "\<And>S. openin d.mtopology S \<Longrightarrow> openin \<Phi> S"
        by (metis d.topspace_mtopology topology_finer_continuous_id)
    qed
    thus ?thesis
      using d.metrizable_space_mtopology by presburger
  next
    case r:2
    have False if h:"\<phi> \<in> B" for \<phi>
    proof -
      have 1: "\<phi> (\<lambda>x\<in>topspace X. 1) \<le> r"
        using h by(auto simp: B_def)
      have 2: "\<phi> (\<lambda>x\<in>topspace X. 1) \<ge> 0"
        using h by(auto simp: B_def pos_lin_functional_on_CX_compact_pos[OF _ compact])
      from 1 2 r show False by linarith
    qed
    hence "B = {}"
      by auto
    thus ?thesis
      by(auto simp: \<Phi>_def)
  qed
qed

subsection  \<open>Alaoglu's Theorem\<close>
text \<open> According to Alaoglu's theorem, $\{\varphi\in C(X)^*\mid \Vert \varphi\Vert\leq r\}$ is compact.
       We show that
       $\Phi = \{\varphi\in C(X)^*\mid \Vert\varphi\Vert\leq r\land \varphi\text{ is positive}\}$ 
       is compact.
       Note that $\Vert \varphi\Vert = \varphi(1)$ when $\varphi\in C(X)^*$ is positive.\<close>
theorem Alaoglu_theorem_real_functional:
  fixes X :: "'a topology" and r :: real
  defines "prod_space \<equiv> powertop_real (mspace (cfunspace X euclidean_metric))"
  defines "B \<equiv> {\<phi>\<in>topspace prod_space. \<phi> (\<lambda>x\<in>topspace X. 1) \<le> r \<and> positive_linear_functional_on_CX X \<phi>}"
  assumes compact: "compact_space X" and ne: "topspace X \<noteq> {}"
  shows "compactin prod_space B"
proof -
  consider "r \<ge> 0" | "r < 0"
    by linarith
  then show ?thesis
  proof cases
    assume rpos:"r \<ge> 0"
    have continuous_map_compact_space_bounded: "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> bounded (f ` topspace X)"
      by (meson compact compact_imp_bounded compact_space_def compactin_euclidean_iff image_compactin)
    have 1: "compactin prod_space
               (\<Pi>\<^sub>E f\<in>mspace (cfunspace X euclidean_metric). {- r * (\<Squnion>x\<in>topspace X. \<bar>f x\<bar>).. r * (\<Squnion>x\<in>topspace X. \<bar>f x\<bar>)})"
      by(auto simp: prod_space_def compactin_PiE)
    have 2: "B \<subseteq> (\<Pi>\<^sub>E f\<in>mspace (cfunspace X euclidean_metric). {- r * (\<Squnion>x\<in>topspace X. \<bar>f x\<bar>).. r * (\<Squnion>x\<in>topspace X. \<bar>f x\<bar>)})"
    proof safe
      fix \<phi> and f :: "'a \<Rightarrow> real"
      assume h:"\<phi> \<in> B" "f \<in> mspace (cfunspace X euclidean_metric)"
      then have f: "continuous_map X euclideanreal f" "f \<in> topspace X \<rightarrow>\<^sub>E UNIV"
        by (auto simp: extensional_def)
      have plf:"positive_linear_functional_on_CX X \<phi>"
        using h(1) by(auto simp: B_def)
      note \<phi> = pos_lin_functional_on_CX_compact_lin[OF plf compact]
               pos_lin_functional_on_CX_compact_pos[OF plf compact]
      note \<phi>_mono = pos_lin_functional_on_CX_compact_mono[OF plf compact]
      note \<phi>_neg = pos_lin_functional_on_CX_compact_uminus[OF plf compact f(1),symmetric]
      obtain K where K: "\<And>x. x \<in> topspace X \<Longrightarrow> \<bar>f x\<bar> \<le> K"
        using h(2) bounded_real by auto
      have f_Sup: "\<And>x. x \<in> topspace X \<Longrightarrow> \<bar>f x\<bar> \<le> (\<Squnion>x\<in>topspace X. \<bar>f x\<bar>)"
        by(auto intro!: cSup_upper bdd_aboveI[where M=B] K)
      hence f_Sup_nonneg: "(\<Squnion>x\<in>topspace X. \<bar>f x\<bar>) \<ge> 0"
        using ne by fastforce
      have "\<bar>\<phi> f\<bar> = \<bar>\<phi> (\<lambda>x\<in>topspace X. f x)\<bar>"
        using f(2) by fastforce
      also have "... \<le> \<phi> (\<lambda>x\<in>topspace X. \<bar>f x\<bar>)"
        using \<phi>_mono[OF _ f(1) continuous_map_norm[OF f(1),simplified]]
          \<phi>(3)[OF continuous_map_norm[OF f(1),simplified]]
          \<phi>_mono[OF _ continuous_map_minus[OF f(1)] continuous_map_norm[OF f(1),simplified]]
        by(cases "\<phi> (restrict f (topspace X)) \<ge> 0") (auto simp: \<phi>_neg)
      also have "... \<le> \<phi> (\<lambda>x\<in>topspace X. (\<Squnion>x\<in>topspace X. \<bar>f x\<bar>) * 1)"
        using continuous_map_norm[where 'b=real] f(1) f_Sup
        by(intro \<phi>_mono) auto
      also have "... = (\<Squnion>x\<in>topspace X. \<bar>f x\<bar>) * \<phi> (\<lambda>x\<in>topspace X. 1)"
        by(intro \<phi>) simp
      also have "... \<le> r * (\<Squnion>x\<in>topspace X. \<bar>f x\<bar>)"
        using h(1) f_Sup_nonneg by(auto simp: B_def mult.commute mult_right_mono)
      finally show "\<phi> f \<in> {- r * (\<Squnion>x\<in>topspace X. \<bar>f x\<bar>).. r * (\<Squnion>x\<in>topspace X. \<bar>f x\<bar>)}"
        by auto
    qed (auto simp: prod_space_def B_def)
    have 3: "closedin prod_space B"
    proof(rule closedin_limitin)
      fix \<phi>n \<phi>
      assume h:"\<And>U. \<phi> \<in> U \<Longrightarrow> openin prod_space U \<Longrightarrow> \<phi>n U \<noteq> \<phi>"
               "\<And>U. \<phi> \<in> U \<Longrightarrow> openin prod_space U \<Longrightarrow> \<phi>n U \<in> B"
               "limitin prod_space \<phi>n \<phi> (nhdsin_sets prod_space \<phi>)"
      then have xnx:"\<phi> \<in> extensional (mspace (cfunspace X euclidean_metric))"
        "(\<forall>\<^sub>F U in nhdsin_sets prod_space \<phi>. \<phi>n U \<in> topspace prod_space)" 
        "\<And>f. f\<in>mspace (cfunspace X euclidean_metric) \<Longrightarrow> limitin euclideanreal (\<lambda>c. \<phi>n c f) (\<phi> f) (nhdsin_sets prod_space \<phi>)"
        by(auto simp: limitin_componentwise prod_space_def)
      have \<phi>_top:"\<phi> \<in> topspace prod_space"
        by (meson h(3) limitin_topspace) 
      show "\<phi> \<in> B"
        unfolding B_def
      proof safe
        have limit: "limitin euclideanreal (\<lambda>c. \<phi>n c (\<lambda>x\<in>topspace X. 1)) (\<phi> (\<lambda>x\<in>topspace X. 1)) (nhdsin_sets prod_space \<phi>)"
          by(rule xnx(3)) (auto simp: bounded_iff)
        show "\<phi> (\<lambda>x\<in>topspace X. 1) \<le> r"
          using h(2)
          by(auto intro!: tendsto_upperbound[OF limit[simplified] _ nhdsin_sets_bot[OF \<phi>_top]]
                          eventually_nhdsin_setsI[OF \<phi>_top] simp: B_def)
      next
        show "positive_linear_functional_on_CX X \<phi>"
          unfolding positive_linear_functional_on_CX_compact[OF compact]
        proof safe
          fix c f
          assume f: "continuous_map X euclideanreal f"
          then have f':"(\<lambda>x\<in>topspace X. c * f x) \<in> mspace (cfunspace X euclidean_metric)"
            "(\<lambda>x\<in>topspace X. f x) \<in> mspace (cfunspace X euclidean_metric)"
            by(auto simp:  intro!: continuous_map_compact_space_bounded continuous_map_real_mult_left)
          have tends1:"((\<lambda>U. c * \<phi>n U (\<lambda>x\<in>topspace X. f x)) \<longlongrightarrow> \<phi> (\<lambda>x\<in>topspace X. c * f x)) (nhdsin_sets prod_space \<phi>)"
            using B_def f h(2) by(fastforce intro!: tendsto_cong[THEN iffD1,OF _ xnx(3)[OF f'(1),simplified]]
                eventually_nhdsin_setsI[OF \<phi>_top] pos_lin_functional_on_CX_compact_lin[OF _ compact f])
          show "\<phi> (\<lambda>x\<in>topspace X. c * f x) = c * \<phi> (\<lambda>x\<in>topspace X. f x)"
            by(rule tendsto_unique[OF nhdsin_sets_bot[OF \<phi>_top] tends1 tendsto_mult_left[OF xnx(3)[OF f'(2),simplified]]])
        next
          fix f g
          assume fg:"continuous_map X euclideanreal f" "continuous_map X euclideanreal g"
          then have fg': "(\<lambda>x\<in>topspace X. f x) \<in> mspace (cfunspace X euclidean_metric)"
            "(\<lambda>x\<in>topspace X. g x) \<in> mspace (cfunspace X euclidean_metric)"
            "(\<lambda>x\<in>topspace X. f x + g x) \<in> mspace (cfunspace X euclidean_metric)"
            by(auto intro!: continuous_map_compact_space_bounded continuous_map_add)
          have "((\<lambda>c. \<phi>n c (\<lambda>x\<in>topspace X. f x) + \<phi>n c (\<lambda>x\<in>topspace X. g x))
                  \<longlongrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x + g x)) (nhdsin_sets prod_space \<phi>)"
            using B_def fg h(2)
            by(fastforce intro!: tendsto_cong[THEN iffD1,OF _ xnx(3)[OF fg'(3),simplified]]
                eventually_nhdsin_setsI[OF \<phi>_top] pos_lin_functional_on_CX_compact_lin[OF _ compact])
          moreover have "((\<lambda>c. \<phi>n c (\<lambda>x\<in>topspace X. f x) + \<phi>n c (\<lambda>x\<in>topspace X. g x))
                           \<longlongrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) + \<phi> (\<lambda>x\<in>topspace X. g x)) (nhdsin_sets prod_space \<phi>)"
            using xnx fg' by(auto intro!: tendsto_add)
          ultimately show "\<phi> (\<lambda>x\<in>topspace X. f x + g x) = \<phi> (\<lambda>x\<in>topspace X. f x) + \<phi> (\<lambda>x\<in>topspace X. g x)"
            by(rule tendsto_unique[OF nhdsin_sets_bot[OF \<phi>_top]])
        next
          fix f
          assume f:"continuous_map X euclideanreal f" "\<forall>x\<in>topspace X. 0 \<le> f x"
          then have 1:"(\<lambda>x\<in>topspace X. f x) \<in> mspace (cfunspace X euclidean_metric)"
            by(auto intro!: continuous_map_compact_space_bounded)
          from f h(2) show "0 \<le> \<phi> (\<lambda>x\<in>topspace X. f x)"
           by(auto intro!: tendsto_lowerbound[OF xnx(3)[OF 1,simplified] _ nhdsin_sets_bot[OF \<phi>_top]]
               eventually_nhdsin_setsI[OF \<phi>_top] simp: B_def pos_lin_functional_on_CX_compact_pos[OF _ compact f(1)])
        qed
      qed fact
    qed(auto simp: B_def)
    show ?thesis
      using 1 2 3 by(rule closed_compactin)
  next
    assume r:"r < 0"
    have "B = {}"
    proof safe
      fix \<phi>
      assume h:"\<phi> \<in> B"
      then have "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> (\<And>x. x \<in> topspace X \<Longrightarrow> f x \<ge> 0) \<Longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) \<ge> 0"
        by(auto simp: B_def pos_lin_functional_on_CX_compact_pos[OF _ compact])
      from this[of "\<lambda>x. 1"] h r show "\<phi> \<in> {}"
        by(auto simp: B_def)
    qed
    thus "compactin prod_space B"
      by blast
  qed
qed

theorem Alaoglu_theorem_real_functional_seq:
  fixes X :: "'a topology" and r :: real
  defines "prod_space \<equiv> powertop_real (mspace (cfunspace X euclidean_metric))"
  defines "B \<equiv> {\<phi>\<in>topspace prod_space. \<phi> (\<lambda>x\<in>topspace X. 1) \<le> r \<and> positive_linear_functional_on_CX X \<phi>}"
  assumes compact:"compact_space X" and ne: "topspace X \<noteq> {}" and met: "metrizable_space X"
  shows "seq_compactin prod_space B"
proof -
  have "compactin prod_space B"
    using Alaoglu_theorem_real_functional[OF compact ne] by(auto simp: B_def prod_space_def)
  hence "compact_space (subtopology prod_space B)"
    using compact_space_subtopology by blast
  hence "seq_compact_space (subtopology prod_space B)"
    unfolding B_def prod_space_def
    using metrizable_seq_compact_space_iff_compact_space[OF metrizable_functional[OF compact met]]
    by fast
  moreover have "B \<subseteq> topspace prod_space"
    by(auto simp: B_def)
  ultimately show ?thesis
    by (simp add: inf.absorb_iff2 seq_compact_space_def seq_compactin_subtopology)
qed

end