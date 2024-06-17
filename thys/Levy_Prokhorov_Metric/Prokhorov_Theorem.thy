(*  Title:   Prokhorov_Theorem.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section  \<open>Prokhorov's Theorem\<close>
theory Prokhorov_Theorem
  imports Levy_Prokhorov_Distance
          Alaoglu_Theorem
begin

subsection  \<open>Prokhorov's Theorem\<close>
context Levy_Prokhorov
begin

lemma relatively_compact_imp_tight_LP:
  assumes "\<Gamma> \<subseteq> \<P>" "separable_space mtopology" mcomplete
      and "compactin LPm.mtopology (LPm.mtopology closure_of \<Gamma>)"
    shows "tight_on_set mtopology \<Gamma>"
proof(cases "M = {}")
  case True
  then have "\<Gamma> = {} \<or> \<Gamma> = {null_measure (borel_of mtopology)}"
    using assms(1) M_empty_P' by auto
  thus ?thesis
    by(auto simp: tight_on_set_def intro!: finite_measureI)
next
  case M_ne:False
  have 1: "\<exists>k. \<forall>N\<in>\<Gamma>. measure N (\<Union>m\<le>k. Ui m) > measure N M - e"
    if Ui: "\<And>i::nat. openin mtopology (Ui i)" "(\<Union>i. Ui i) = M" and e:"e > 0" for Ui e
  proof(rule ccontr)
    assume "\<nexists>k. \<forall>N\<in>\<Gamma>. measure N (\<Union>m\<le>k. Ui m) > measure N M - e"
    then have h: "\<forall>k. \<exists>N\<in>\<Gamma>. measure N (\<Union>m\<le>k. Ui m) \<le> measure N M - e"
      by(auto simp: linorder_class.not_less)
    then obtain Nk where Nk: "\<And>k. Nk k \<in> \<Gamma>" "\<And>k. measure (Nk k) (\<Union>m\<le>k. Ui m) \<le> measure (Nk k) M - e"
      by metis
    obtain N r where Nr: "N \<in> LPm.mtopology closure_of \<Gamma>" "strict_mono r"
      "limitin LPm.mtopology (Nk \<circ> r) N sequentially"
      using assms(1,4) Nk(1) closure_of_subset[of \<Gamma> LPm.mtopology]
      by(simp add: LPm.compactin_sequentially) (metis image_subset_iff subsetD)
    then interpret mweak_conv_fin M d "\<lambda>i. Nk (r i)" N sequentially
      using assms(1) Nk(1) closure_of_subset_topspace[of LPm.mtopology]
      by(auto intro!: inP_mweak_conv_fin_all)
    have sets_Nk[measurable_cong,simp]:"\<And>i. sets (Nk (r i)) = sets (borel_of mtopology)"
      using Nk(1) assms(1) inP_D(2) by blast
    have wc: "mweak_conv_seq (\<lambda>i. Nk (r i)) N"
      using converge_imp_mweak_conv[OF Nr(3)] Nk(1) assms(1) by(auto simp: comp_def)
    interpret Nk: finite_measure "Nk k" for k
      using Nk(1) assms(1) inP_D by blast
    interpret N: finite_measure N
      using finite_measure_N by blast
    have 1:"measure N (\<Union>i\<le>n. Ui i) \<le> measure N M - e" for n
    proof -
      have "measure N (\<Union>i\<le>n. Ui i) \<le> liminf (\<lambda>j. measure (Nk (r j)) (\<Union>i\<le>n. Ui i))"
        using Ui by(auto intro!: conjunct2[OF mweak_conv_eq3[THEN iffD1,OF wc],rule_format])
      also have "... \<le> liminf (\<lambda>j. measure (Nk (r j)) (\<Union>i\<le>r j. Ui i))"
        by(rule Liminf_mono)
          (auto intro!: Ui(1) exI[where x=n] Nk.finite_measure_mono[OF UN_mono]
                        le_trans[OF _ strict_mono_imp_increasing[OF Nr(2)]] borel_of_open
                  simp: eventually_sequentially sets_N)
      also have "... \<le> liminf (\<lambda>j. measure (Nk (r j)) M + ereal (- e))"
        using Nk by(auto intro!: Liminf_mono eventuallyI)
      also have "... \<le> liminf (\<lambda>j. measure (Nk (r j)) M) + limsup (\<lambda>i. - e)"
        by(rule ereal_liminf_limsup_add)
      also have "... = liminf (\<lambda>j. measure (Nk (r j)) M) + ereal (- e)"
        using Limsup_const[of sequentially "- e"] by simp
      also have "... = measure N M + ereal (- e)"
      proof -
        have "(\<lambda>k. measure (Nk (r k)) M) \<longlonglongrightarrow> measure N M"
          using wc mweak_conv_eq2 by fastforce
        from limI[OF tendsto_ereal[OF this]] convergent_liminf_cl[OF convergentI[OF tendsto_ereal[OF this]]]
        show ?thesis by simp
      qed
      finally show ?thesis
        by simp
    qed
    have 2:"(\<lambda>n. measure N (\<Union>i\<le>n. Ui i)) \<longlonglongrightarrow> measure N M"
    proof -
      have "(\<lambda>n. measure N (\<Union>i\<le>n. Ui i)) \<longlonglongrightarrow> measure N (\<Union> (range (\<lambda>n. \<Union>i\<le>n. Ui i)))"
        by(fastforce intro!: Ui(1) N.finite_Lim_measure_incseq borel_of_open incseq_SucI simp: sets_N)
      moreover have "\<Union> (range (\<lambda>n. \<Union>i\<le>n. Ui i)) = M"
        using Ui(2) by blast
      ultimately show ?thesis
        by simp
    qed
    show False
      using e Lim_bounded[OF 2,of 0 "measure N M - e"] 1 by auto
  qed
  show ?thesis
    unfolding tight_on_set_def
  proof safe
    fix e :: real
    assume e: "0 < e"
    obtain U where U: "countable U" "mdense U"
      using assms(2) separable_space_def2 by blast
    let ?an = "from_nat_into U"
    have an: "\<And>n. ?an n \<in> M" "mdense (range ?an)"
      by (metis M_ne U(2) from_nat_into mdense_def2 mdense_empty_iff subsetD)
         (metis M_ne U(1) U(2) mdense_empty_iff range_from_nat_into)
    have "\<exists>k. \<forall>N\<in>\<Gamma>. measure N (\<Union>n\<le>k. mball (?an n) (1 / Suc m)) > measure N M - (e / 2) * (1 / 2) ^ Suc m" for m
      by(rule 1) (use mdense_balls_cover[OF an(2)] e in auto)
    then obtain k where k:
      "\<And>m N. N \<in> \<Gamma> \<Longrightarrow> measure N (\<Union>n\<le>k m. mball (?an n) (1 / Suc m)) > measure N M - (e / 2) * (1 / 2) ^ Suc m"
      by metis
    let ?K = "\<Inter>m. (\<Union>i\<le>k m. mcball (?an i) (1 / Suc m))"
    show "\<exists>K. compactin mtopology K \<and> (\<forall>M\<in>\<Gamma>. measure M (space M - K) < e)"
    proof(safe intro!: exI[where x="?K"])
      have "closedin mtopology ?K"
        by(auto intro!: closedin_Union)
      moreover have "?K \<subseteq> M"
        by auto
      moreover have "mtotally_bounded ?K"
        unfolding mtotally_bounded_def2
      proof safe
        fix e :: real
        assume e: "0 < e"
        then obtain m where m: "e > 1 / Suc m"
          using nat_approx_posE by blast
        have "?K \<subseteq> (\<Union>i\<le>k m. mcball (?an i) (1 / real (Suc m)))"
          by auto
        also have "... \<subseteq> (\<Union>x\<in>?an ` {..k m}. mball x e)"
          using mcball_subset_mball_concentric[OF m] by blast
        finally show "\<exists>K. finite K \<and> K \<subseteq> M \<and> ?K \<subseteq> (\<Union>x\<in>K. mball x e)"
          using an(1) by(fastforce intro!: exI[where x="?an ` {..k m}"])
      qed
      ultimately show "compactin mtopology ?K"
        using mtotally_bounded_eq_compact_closedin[OF assms(3)] by auto
    next
      fix N
      assume N: "N \<in> \<Gamma>"
      then interpret N: finite_measure N
        using assms(1) inP_D by blast
      have sets_N: "sets N = sets (borel_of mtopology)"
        using N assms(1) by(auto simp: \<P>_def)
      hence space_N: "space N = M"
        by(auto cong: sets_eq_imp_space_eq simp: space_borel_of)
      have [measurable]:"\<And>a b. mcball a b \<in> sets N" "M \<in> sets N"
        by(auto simp: sets_N intro!: borel_of_closed)
      have Ne:"measure N (M - (\<Union>i\<le>k m. mcball (?an i) (1 / real (Suc m)))) < (e / 2) * (1 / 2) ^ Suc m" for m
      proof -
        have "measure N (M - (\<Union>i\<le>k m. mcball (?an i) (1 / real (Suc m))))
              = measure N M - measure N (\<Union>i\<le>k m. mcball (?an i) (1 / real (Suc m)))"
          by(auto simp: N.finite_measure_compl[simplified space_N])
        also have "... \<le> measure N M - measure N (\<Union>i\<le>k m. mball (?an i) (1 / real (Suc m)))"
          by(fastforce intro!: N.finite_measure_mono)
        also have "... < (e / 2) * (1 / 2) ^ Suc m"
          using k[OF N,of m] by simp
        finally show ?thesis .
      qed
      have Ne_sum: "summable (\<lambda>m. (e / 2) * (1 / 2) ^ Suc m)"
        by auto
      have sum2: "summable (\<lambda>m. measure N (M - (\<Union>i\<le>k m. mcball (from_nat_into U i) (1 / real (Suc m)))))"
        using Ne by(auto intro!: summable_comparison_test_ev[OF _ Ne_sum] eventuallyI) (use less_eq_real_def in blast)
      show "measure N (space N - ?K) < e"
      proof -
        have "measure N (space N - ?K) = measure N (\<Union>m. (M - (\<Union>i\<le>k m. mcball (?an i) (1 / Suc m))))"
          by(auto simp: space_N)
        also have "... \<le> (\<Sum>m. measure N (M - (\<Union>i\<le>k m. mcball (?an i) (1 / Suc m))))"
          by(rule N.finite_measure_subadditive_countably) (use sum2 in auto)
        also have "... \<le> (\<Sum>m. (e / 2) * (1 / 2) ^ Suc m)"
          by(rule suminf_le) (use Ne less_eq_real_def sum2 in auto)
        also have "... = (e / 2) * (\<Sum>m. (1 / 2) ^ Suc m)"
          by(rule suminf_mult) auto
        also have "... = e / 2"
          using power_half_series sums_unique by fastforce
        also have "... < e"
          using e by simp
        finally show ?thesis .
      qed
    qed
  qed(use assms inP_D in auto)
qed

lemma mcompact_imp_LPmcompact:
  assumes "compact_space mtopology"
  shows "compactin LPm.mtopology {N. sets N = sets (borel_of mtopology) \<and> N (space N) \<le> ennreal r}"
    (is "compactin _ ?N")
proof -
  consider "M = {}" | "r < 0" | "r \<ge> 0" "M \<noteq> {}"
    by linarith
  then show ?thesis
  proof cases
    assume "M = {}"
    then have "finite (topspace LPm.mtopology)"
      unfolding LPm.topspace_mtopology using M_empty_P by fastforce
    thus ?thesis
      using closedin_bounded_measures closedin_compact_space compact_space_def finite_imp_compactin_eq by blast
  next
    assume "r < 0"
    then have "?N = {null_measure (borel_of mtopology)}"
      using emeasure_eq_0[OF _ _ sets.sets_into_space]
      by(safe,intro measure_eqI) (auto simp: ennreal_lt_0)
    thus ?thesis
      by(auto intro!: inP_I finite_measureI)
  next
    assume M_ne:"M \<noteq> {}" and r:"r \<ge> 0"
    hence [simp]: "mtopology \<noteq> trivial_topology"
      using topspace_mtopology by force
    define Cb where "Cb \<equiv> cfunspace mtopology (euclidean_metric :: real metric)"
    define Cb' where "Cb' \<equiv> powertop_real (mspace (cfunspace mtopology (euclidean_metric :: real metric)))"
    define B where
      "B \<equiv> {\<phi>\<in>topspace Cb'. \<phi> (\<lambda>x\<in>topspace mtopology. 1) \<le> r \<and> positive_linear_functional_on_CX mtopology \<phi>}"
    define T :: "'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real"
      where "T \<equiv> \<lambda>N. \<lambda>f\<in>mspace (cfunspace mtopology euclidean_metric). \<integral>x. f x \<partial>N"
    have compact: "compactin Cb' B"
      unfolding B_def Cb'_def by(rule Alaoglu_theorem_real_functional[OF assms(1)]) (use M_ne in simp)
    have metrizable: "metrizable_space (subtopology Cb' B)"
      unfolding B_def Cb'_def by(rule  metrizable_functional[OF assms metrizable_space_mtopology])
    have homeo: "homeomorphic_map (subtopology LPm.mtopology ?N) (subtopology Cb' B) T"
    proof -
      have T_cont': "continuous_map (subtopology LPm.mtopology ?N) Cb' T"
        unfolding continuous_map_atin
      proof safe
        fix N
        assume N:"N \<in> topspace (subtopology LPm.mtopology ?N)"
        show "limitin Cb' T (T N) (atin (subtopology LPm.mtopology ?N) N)"
          unfolding Cb'_def limitin_componentwise
        proof safe
          fix g :: "'a \<Rightarrow> real"
          assume g:"g \<in> mspace (cfunspace mtopology euclidean_metric)"
          then have g_bounded:"\<exists>B. \<forall>x\<in>M. \<bar>g x\<bar> \<le> B"
            by(auto simp: bounded_pos_less order_less_le)
          show "limitin euclideanreal (\<lambda>c. T c g) (T N g) (atin (subtopology LPm.mtopology ?N) N)"
            unfolding limitin_canonical_iff
          proof
            fix e :: real
            assume e:"0 < e"
            have N_in: "N \<in> ?N"
              using N by simp
            show  "\<forall>\<^sub>F c in atin (subtopology LPm.mtopology ?N) N. dist (T c g) (T N g) < e "
              unfolding atin_subtopology_within[OF N_in]
            proof (safe intro!: eventually_within_imp[THEN iffD2,OF LPm.eventually_atin_sequentially[THEN iffD2]])
              fix Ni
              assume Ni:"range Ni \<subseteq> \<P> - {N}" "limitin LPm.mtopology Ni N sequentially"
              with N interpret mweak_conv_fin M d Ni N sequentially
                by(auto intro!: inP_mweak_conv_fin_all)
              have wc:"mweak_conv_seq Ni N"
                using Ni by(auto intro!: converge_imp_mweak_conv)
              hence 1:"(\<lambda>n. T (Ni n) g) \<longlonglongrightarrow> T N g"
                unfolding T_def by(auto simp: g mweak_conv_def g_bounded)
              show "\<forall>\<^sub>F n in sequentially. Ni n \<in> ?N \<longrightarrow> dist (T (Ni n) g) (T N g) < e"
                by(rule eventually_mp[OF _ 1[simplified tendsto_iff,rule_format,OF e]]) simp
            qed
          qed
        qed(auto simp: T_def)
      qed
      have T_cont: "continuous_map (subtopology LPm.mtopology ?N) (subtopology Cb' B) T"
        unfolding continuous_map_in_subtopology
      proof
        show "T ` topspace (subtopology LPm.mtopology ?N) \<subseteq> B"
          unfolding B_def Cb'_def
        proof safe
          fix N
          assume N:"N \<in> topspace (subtopology LPm.mtopology ?N)"
          then have "finite_measure N" and sets_N:"sets N = sets (borel_of mtopology)"
            and space_N:"space N = M" and N_r:"emeasure N (space N) \<le> ennreal r"
            by(auto intro!: inP_D)
          hence N_r':"measure N (space N) \<le> r"
            by (simp add: finite_measure.emeasure_eq_measure r)
          interpret N: finite_measure N
            by fact
          have TN_def: "T N (\<lambda>x\<in>topspace mtopology. f x) = (\<integral>x. f x \<partial>N)" "T N (\<lambda>x\<in>M. f x) = (\<integral>x. f x \<partial>N)"
            if f:"continuous_map mtopology euclideanreal f" for f
            using f Bochner_Integration.integral_cong[OF refl,of N "\<lambda>x\<in>M. f x" f,simplified space_N]
              compact_imp_bounded[OF compactin_euclidean_iff[THEN iffD1,
                  OF image_compactin[OF assms[simplified compact_space_def] f]]]
            by(auto simp: T_def)
          have N_integrable[simp]: "integrable N f" if f:"continuous_map mtopology euclideanreal f" for f
            using compact_imp_bounded[OF compactin_euclidean_iff[THEN iffD1,OF image_compactin[OF
                    assms[simplified compact_space_def] f]]] continuous_map_measurable[OF f]
            by(auto intro!: N.integrable_const_bound AE_I2[of N]
                      simp: bounded_iff measurable_cong_sets[OF sets_N] borel_of_euclidean space_N)

          show "T N (\<lambda>x\<in>topspace mtopology. 1) \<le> r"
            unfolding TN_def[OF continuous_map_canonical_const]
            using N_r' by simp
          show "positive_linear_functional_on_CX mtopology (T N)"
            unfolding positive_linear_functional_on_CX_compact[OF assms]
          proof safe
            fix f c
            assume f: "continuous_map mtopology euclideanreal f"
            show "T N (\<lambda>x\<in>topspace mtopology. c * f x) = c * T N (\<lambda>x\<in>topspace mtopology. f x)"
              using f continuous_map_real_mult_left[OF f,of c] by(auto simp: TN_def)
          next
            fix f g
            assume fg: "continuous_map mtopology euclideanreal f"
              "continuous_map mtopology euclideanreal g"
            show "T N (\<lambda>x\<in>topspace mtopology. f x + g x)
                  = T N (\<lambda>x\<in>topspace mtopology. f x) + T N (\<lambda>x\<in>topspace mtopology. g x)"
              using fg continuous_map_add[OF fg]
              by(auto simp: TN_def intro!: Bochner_Integration.integral_add)
          next
            fix f
            assume "continuous_map mtopology euclideanreal f" "\<forall>x\<in>topspace mtopology. 0 \<le> f x"
            then show "0 \<le> T N (\<lambda>x\<in>topspace mtopology. f x)"
              by(auto simp: TN_def space_N intro!: Bochner_Integration.integral_nonneg)
          qed
          show "T N \<in> topspace (powertop_real (mspace (cfunspace mtopology euclidean_metric)))"
            by(auto simp: T_def)
        qed
      qed fact
      define T_inv :: "(('a \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> 'a measure" where
        "T_inv \<equiv> (\<lambda>\<phi>. THE N. sets N = sets (borel_of mtopology) \<and> finite_measure N \<and>
                            (\<forall>f. continuous_map mtopology euclideanreal f
                                 \<longrightarrow> \<phi> (restrict f (topspace mtopology)) = integral\<^sup>L N f))"
      have T_T_inv: "\<forall>N\<in>topspace (subtopology LPm.mtopology ?N). T_inv (T N) = N"
      proof safe
        fix N
        assume N:"N \<in> topspace (subtopology LPm.mtopology ?N)"
        from Pi_mem[OF continuous_map_funspace[OF T_cont] this]
        have TN:"T N \<in> topspace (subtopology Cb' B)"
          by blast
        hence "\<exists>!N'. sets N' = sets (borel_of mtopology) \<and> finite_measure N' \<and>
                     (\<forall>f. continuous_map mtopology euclideanreal f
                          \<longrightarrow> T N (restrict f (topspace mtopology)) = integral\<^sup>L N' f)"
          by(intro Riesz_representation_real_compact_metrizable[OF assms metrizable_space_mtopology])
            (auto simp del: topspace_mtopology restrict_apply simp: B_def)
        moreover have "sets N = sets (borel_of mtopology) \<and> finite_measure N \<and>
                      (\<forall>f. continuous_map mtopology euclideanreal f
                           \<longrightarrow> T N (restrict f (topspace mtopology)) = integral\<^sup>L N f)"
          using compact_imp_bounded[OF compactin_euclidean_iff[THEN iffD1,OF image_compactin[OF
                  assms[simplified compact_space_def] _]]] N
          by(auto simp: T_def dest:inP_D cong: Bochner_Integration.integral_cong)
        ultimately show "T_inv (T N) = N"
          unfolding T_inv_def by(rule the1_equality)
      qed
      have T_inv_T: "\<forall>\<phi>\<in>topspace (subtopology Cb' B). T (T_inv \<phi>) = \<phi>"
      proof safe
        fix \<phi>
        assume \<phi>:"\<phi>\<in>topspace (subtopology Cb' B)"
        hence 1:"\<exists>!N'. sets N' = sets (borel_of mtopology) \<and> finite_measure N' \<and>
                       (\<forall>f. continuous_map mtopology euclideanreal f
                             \<longrightarrow> \<phi> (restrict f (topspace mtopology)) = integral\<^sup>L N' f)"
          by(intro Riesz_representation_real_compact_metrizable[OF assms metrizable_space_mtopology])
            (auto simp del: topspace_mtopology restrict_apply simp add: B_def)
        have T_inv_\<phi>:"sets (T_inv \<phi>) = sets (borel_of mtopology)" "finite_measure (T_inv \<phi>)"
          "\<And>f. continuous_map mtopology euclideanreal f
                \<Longrightarrow> \<phi> (\<lambda>x\<in>topspace mtopology. f x) = integral\<^sup>L (T_inv \<phi>) f"
          unfolding T_inv_def by(use theI'[OF 1] in blast)+
        show "T (T_inv \<phi>) = \<phi>"
        proof
          fix f
          consider "f \<in> mspace Cb" | "f \<notin> mspace Cb"
            by fastforce
          then show "T (T_inv \<phi>) f = \<phi> f"
          proof cases
            case 1
            then have "T (T_inv \<phi>) f = integral\<^sup>L (T_inv \<phi>) f"
              by(auto simp: T_def Cb_def)
            also have "... = \<phi> (\<lambda>x\<in>topspace mtopology. f x)"
              by(rule T_inv_\<phi>(3)[symmetric]) (use 1 Cb_def in auto)
            also have "... = \<phi> f"
            proof -
              have 2: "(\<lambda>x\<in>topspace mtopology. f x) = f"
                using 1 by(auto simp: extensional_def Cb_def)
              show ?thesis
                unfolding 2 by blast
            qed
            finally show ?thesis .
          next
            case 2
            then have "T (T_inv \<phi>) f = undefined"
              by (auto simp: Cb_def T_def)
            also have "... = \<phi> f"
              using 2 \<phi> Cb'_def Cb_def PiE_arb by auto
            finally show ?thesis .
          qed
        qed
      qed
      have T_inv_cont: "continuous_map (subtopology Cb' B) (subtopology LPm.mtopology ?N) T_inv"
        unfolding seq_continuous_iff_continuous_first_countable[OF metrizable_imp_first_countable[OF
              metrizable],symmetric] seq_continuous_map
      proof safe
        fix \<phi>n \<phi>
        assume "limitin (subtopology Cb' B) \<phi>n \<phi> sequentially"
        then have \<phi>B: "\<phi> \<in> B" and h:"limitin Cb' \<phi>n \<phi> sequentially" "\<forall>\<^sub>F n in sequentially. \<phi>n n \<in> B"
          by(auto simp: limitin_subtopology)
        then obtain n0 where n0: "\<And>n. n \<ge> n0 \<Longrightarrow> \<phi>n n \<in> B"
          by(auto simp: eventually_sequentially)
        have limit: "\<And>f. f \<in> mspace (cfunspace mtopology euclidean_metric) \<Longrightarrow> (\<lambda>n. \<phi>n n f) \<longlonglongrightarrow> \<phi> f"
          using h(1) by(auto simp: limitin_componentwise Cb'_def)
        show "limitin (subtopology LPm.mtopology ?N) (\<lambda>n. T_inv (\<phi>n n)) (T_inv \<phi>) sequentially"
        proof(rule limitin_sequentially_offset_rev[where k=n0])
          from \<phi>B have "\<exists>!N. sets N = sets (borel_of mtopology) \<and> finite_measure N \<and>
                        (\<forall>f. continuous_map mtopology euclideanreal f 
                            \<longrightarrow> \<phi> (restrict f (topspace mtopology)) = integral\<^sup>L N f)"
            by(intro Riesz_representation_real_compact_metrizable[OF assms metrizable_space_mtopology])
              (auto simp del: topspace_mtopology restrict_apply simp: B_def)
          hence "sets (T_inv \<phi>) = sets (borel_of mtopology) \<and> finite_measure (T_inv \<phi>) \<and>
                  (\<forall>f. continuous_map mtopology euclideanreal f
                       \<longrightarrow> \<phi> (restrict f (topspace mtopology)) = integral\<^sup>L (T_inv \<phi>) f)"
            unfolding T_inv_def by(rule theI')
          hence T_inv_\<phi>: "sets (T_inv \<phi>) = sets (borel_of mtopology)" "finite_measure (T_inv \<phi>)"
            "\<And>f. continuous_map mtopology euclideanreal f
                  \<Longrightarrow> \<phi> (restrict f (topspace mtopology)) = integral\<^sup>L (T_inv \<phi>) f"
            by auto
          from this(2) this(3)[of "\<lambda>x. 1"] \<phi>B have  T_inv_\<phi>_r: "T_inv \<phi> (space (T_inv \<phi>)) \<le> ennreal r"
            unfolding B_def by simp (metis ennreal_le_iff finite_measure.emeasure_eq_measure r)
          {
            fix n
            from n0[of "n + n0",simplified] have "\<exists>!N. sets N = sets (borel_of mtopology) \<and>
                finite_measure N \<and> (\<forall>f. continuous_map mtopology euclideanreal f
                                       \<longrightarrow> \<phi>n (n + n0) (restrict f (topspace mtopology)) = integral\<^sup>L N f)"
              by(intro Riesz_representation_real_compact_metrizable[OF assms metrizable_space_mtopology])
                (auto simp del: topspace_mtopology restrict_apply simp: B_def)
            hence "sets (T_inv (\<phi>n (n + n0))) = sets (borel_of mtopology) \<and> finite_measure (T_inv (\<phi>n (n + n0))) \<and>
                (\<forall>f. continuous_map mtopology euclideanreal f
                 \<longrightarrow> \<phi>n (n + n0) (restrict f (topspace mtopology)) = integral\<^sup>L (T_inv (\<phi>n (n + n0))) f)"
              unfolding T_inv_def by(rule theI')
            hence "sets (T_inv (\<phi>n (n + n0))) = sets (borel_of mtopology)"
              "finite_measure (T_inv (\<phi>n (n + n0)))"
              "\<And>f. continuous_map mtopology euclideanreal f
             \<Longrightarrow> \<phi>n (n + n0) (restrict f (topspace mtopology)) = integral\<^sup>L (T_inv (\<phi>n (n + n0))) f"
              by auto
          }
          note T_inv_\<phi>n = this
          have T_inv_\<phi>n_r: "T_inv (\<phi>n (n + n0)) (space (T_inv (\<phi>n (n + n0)))) \<le> ennreal r" for n
            using T_inv_\<phi>n(2)[of n] T_inv_\<phi>n(3)[of "\<lambda>x. 1" n] n0[of "n + n0",simplified]
            unfolding B_def by simp (metis ennreal_le_iff finite_measure.emeasure_eq_measure r)
          show "limitin (subtopology LPm.mtopology ?N)  (\<lambda>n. T_inv (\<phi>n (n + n0))) (T_inv \<phi>) sequentially"
          proof(intro limitin_subtopology[THEN iffD2] mweak_conv_imp_converge conjI)
            show "mweak_conv_seq (\<lambda>n. T_inv (\<phi>n (n + n0))) (T_inv \<phi>)"
              unfolding mweak_conv_seq_def
            proof safe
              fix f :: "'a \<Rightarrow> real" and B
              assume f:"continuous_map mtopology euclideanreal f" and B:"\<forall>x\<in>M. \<bar>f x\<bar> \<le> B"
              hence f': "restrict f (topspace mtopology) \<in> mspace (cfunspace mtopology euclidean_metric)"
                by (auto simp: bounded_pos_less intro!: exI[where x="\<bar>B\<bar> + 1"])
              have 1:"(\<lambda>n. \<integral>x. f x \<partial> T_inv (\<phi>n (n + n0))) = (\<lambda>n. \<phi>n (n + n0) (restrict f (topspace mtopology)))"
                by(subst T_inv_\<phi>n(3)) (use f in auto)
              have 2:"(\<integral>x. f x \<partial> T_inv \<phi>) = \<phi> (restrict f (topspace mtopology))"
                by(subst T_inv_\<phi>(3)) (use f in auto)
              show "(\<lambda>n. \<integral>x. f x \<partial> T_inv (\<phi>n (n + n0))) \<longlonglongrightarrow> (\<integral>x. f x \<partial>T_inv \<phi>)"
                unfolding 1 2 using limit[OF f'] LIMSEQ_ignore_initial_segment by blast
            qed(use T_inv_\<phi>(1,2) T_inv_\<phi>n(1,2) eventuallyI in auto)
          next
            show " \<forall>\<^sub>F a in sequentially. T_inv (\<phi>n (a + n0)) \<in> ?N"
              by (simp add: T_inv_\<phi>n(1) T_inv_\<phi>n_r)
          next
            show "T_inv \<phi> \<in> {N. sets N = sets (borel_of mtopology) \<and> emeasure N (space N) \<le> ennreal r}"
              using T_inv_\<phi>(1) T_inv_\<phi>_r by auto
          qed(use T_inv_\<phi>n(1) T_inv_\<phi>n_r T_inv_\<phi>(1) T_inv_\<phi>_r compact_space_imp_separable[OF assms] in auto)
        qed
      qed
      show ?thesis
        using T_inv_cont T_cont T_T_inv T_inv_T
        by(auto intro!: homeomorphic_maps_imp_map[where g=T_inv] simp: homeomorphic_maps_def)
    qed
    show ?thesis
      using homeomorphic_compact_space[OF homeomorphic_map_imp_homeomorphic_space[OF homeo]]
         compact_space_subtopology[OF compact] LPm.closedin_metric closedin_bounded_measures compactin_subspace
      by fastforce
  qed
qed

lemma tight_imp_relatively_compact_LP:
  assumes "\<Gamma> \<subseteq> {N. sets N = sets (borel_of mtopology) \<and> N (space N) \<le> ennreal r}" "separable_space mtopology"
      and "tight_on_set mtopology \<Gamma>"
    shows "compactin LPm.mtopology (LPm.mtopology closure_of \<Gamma>)"
proof(cases "r < 0")
  assume "r < 0"
  then have *:"{N. sets N = sets (borel_of mtopology) \<and> N (space N) \<le> ennreal r} = {null_measure (borel_of mtopology)}"
    using emeasure_eq_0[OF _ _ sets.sets_into_space]
    by(safe,intro measure_eqI) (auto simp: ennreal_lt_0)
  with assms(1) have "\<Gamma> = {} \<or> \<Gamma> = {null_measure (borel_of mtopology)}"
    by auto
  hence "LPm.mtopology closure_of \<Gamma> = {} \<or> LPm.mtopology closure_of \<Gamma> = {null_measure (borel_of mtopology)}"
    by (metis (no_types) * closedin_bounded_measures closure_of_empty closure_of_eq)
  thus ?thesis
    by(auto intro!: inP_I finite_measureI)
next
  assume "\<not> r < 0"
  then have r_nonneg:"r \<ge> 0"
    by simp
  have subst1: "\<Gamma> \<subseteq> \<P>"
    using assms(1) linorder_not_le by(force intro!: finite_measureI inP_I)
  have subst2: "LPm.mtopology closure_of \<Gamma> \<subseteq> {N. sets N = sets (borel_of mtopology) \<and> N (space N) \<le> ennreal r}"
    by (simp add: assms(1) closedin_bounded_measures closure_of_minimal)
  have tight: "tight_on_set mtopology (LPm.mtopology closure_of \<Gamma>)"
    unfolding tight_on_set_def
  proof safe
    fix e :: real
    assume e: "0 < e"
    then obtain K where K: "compactin mtopology K" "\<And>N. N \<in> \<Gamma> \<Longrightarrow> measure N (space N - K) < e / 2"
      by (metis assms(3) tight_on_set_def zero_less_divide_iff zero_less_numeral)
    show "\<exists>K. compactin mtopology K \<and> (\<forall>M\<in>LPm.mtopology closure_of \<Gamma>. measure M (space M - K) < e)"
    proof(safe intro!: exI[where x=K])
      fix N
      assume N:"N \<in> LPm.mtopology closure_of \<Gamma>"
      then obtain Nn where Nn: "\<And>n. Nn n \<in> \<Gamma>" "limitin LPm.mtopology Nn N sequentially"
        unfolding LPm.closure_of_sequentially by auto
      with N subst1 interpret mweak_conv_fin M d Nn N sequentially
        using closure_of_subset_topspace by(fastforce intro!: inP_mweak_conv_fin_all simp: closure_of_subset_topspace)
      have space_Ni:"\<And>i. space (Nn i) = M"
        by (meson Nn(1) inP_D(3) subsetD subst1)
      have "openin mtopology (M - K)"
        using compactin_imp_closedin[OF Hausdorff_space_mtopology K(1)] by blast
      hence "ereal (measure N (M - K)) \<le> liminf (\<lambda>n. ereal (measure (Nn n) (M -K)))"
        using mweak_conv_eq3 converge_imp_mweak_conv[OF Nn(2)] Nn(1) subst1 by blast
      also have "... \<le> ereal (e / 2)"
        using K(2) Nn(1) space_Ni
        by(intro Liminf_le eventuallyI ereal_less_eq(3)[THEN iffD2] order.strict_implies_order) fastforce+
      also have "... < ereal e"
        using e by auto
      finally show "measure N (space N - K) < e"
        by(auto simp: space_N)
    qed fact
  qed(use closure_of_subset_topspace[of LPm.mtopology \<Gamma>] inP_D in auto)
  show ?thesis
    unfolding LPm.compactin_sequentially
  proof safe
    fix Ni :: "nat \<Rightarrow> 'a measure"
    assume Ni: "range Ni \<subseteq> LPm.mtopology closure_of \<Gamma>"
    then have Ni2: "\<And>i. finite_measure (Ni i)" and Ni_le_r: "\<And>i. Ni i (space (Ni i)) \<le> ennreal r"
      and sets_Ni[measurable_cong]:"\<And>i. sets (Ni i) = sets (borel_of mtopology)"
      and space_Ni:"\<And>i. space (Ni i) = M"
      using closure_of_subset_topspace[of LPm.mtopology \<Gamma>] inP_D subst2 by fastforce+
    interpret Ni: finite_measure "Ni i" for i
      by fact
    have "metrizable_space Hilbert_cube_topology"
      by(auto simp: metrizable_space_product_topology metrizable_space_euclidean intro!: metrizable_space_subtopology)
    then obtain dH where dH: "Metric_space (UNIV \<rightarrow>\<^sub>E {0..1}) dH"
      "Metric_space.mtopology (UNIV \<rightarrow>\<^sub>E {0..1}) dH = Hilbert_cube_topology"
      by (metis Metric_space.topspace_mtopology metrizable_space_def topspace_Hilbert_cube)
    then interpret dH: Metric_space "UNIV \<rightarrow>\<^sub>E {0..1}" dH
      by auto
    have compact_dH:"compact_space dH.mtopology"
      unfolding dH(2) by(auto simp: compact_space_def compactin_PiE)
    from embedding_into_Hilbert_cube[OF metrizable_space_mtopology assms(2)]
    obtain A where A: "A \<subseteq>topspace Hilbert_cube_topology"
      "mtopology homeomorphic_space subtopology Hilbert_cube_topology A"
      by auto
    then obtain T T_inv where T: "continuous_map mtopology (subtopology Hilbert_cube_topology A) T"
      "continuous_map (subtopology Hilbert_cube_topology A) mtopology T_inv"
      "\<And>x. x \<in> topspace (subtopology Hilbert_cube_topology A)
            \<Longrightarrow> T (T_inv x) = x" "\<And>x. x \<in> M \<Longrightarrow> T_inv (T x) = x"
      unfolding homeomorphic_space_def homeomorphic_maps_def by fastforce
    hence injT: "inj_on T M"
      by(intro inj_on_inverseI)
    have T_cont: "continuous_map mtopology dH.mtopology T"
      by (metis T(1) continuous_map_in_subtopology dH(2))
    from continuous_map_measurable[OF this]
    have T_meas[measurable]: "T \<in> measurable (Ni n) (borel_of dH.mtopology)" for n
      by(auto simp: sets_Ni cong: measurable_cong_sets)
    define \<nu>n where "\<nu>n \<equiv> (\<lambda>i. distr (Ni i) (borel_of dH.mtopology) T)"
    have sets_\<nu>n: "\<And>n. sets (\<nu>n n) = sets (borel_of dH.mtopology)"
      unfolding \<nu>n_def by simp
    hence space_\<nu>n: "\<And>n. space (\<nu>n n) = UNIV \<rightarrow>\<^sub>E {0..1}"
      by(auto cong: sets_eq_imp_space_eq simp: space_borel_of)
    interpret \<nu>n: finite_measure "\<nu>n n" for n
      by(auto simp: \<nu>n_def space_borel_of PiE_eq_empty_iff intro!: Ni.finite_measure_distr)
    have \<nu>n_le_r: "\<nu>n n (space (\<nu>n n)) \<le> ennreal r" for n
      by(auto simp: \<nu>n_def emeasure_distr order.trans[OF emeasure_space Ni_le_r[of n]])
    have measure_\<nu>n_compact:"measure (\<nu>n n) (space (\<nu>n n) - T ` K) = measure (Ni n) (space (Ni n) - K)"
      if K: "compactin mtopology K" for K n
    proof -
      have "compactin dH.mtopology (T ` K)"
        using T_cont image_compactin K by blast
      hence "T ` K \<in> sets (borel_of dH.mtopology)"
        by(auto intro!: borel_of_closed compactin_imp_closedin dH.Hausdorff_space_mtopology)
      hence "measure (\<nu>n n) (space (\<nu>n n) - T ` K)
             = measure (Ni n) (T -` (space (\<nu>n n) - T ` K) \<inter> space (Ni n))"
        by(simp add: \<nu>n_def measure_distr)
      also have "... = measure (Ni n) (space (Ni n) - K)"
        using compactin_subset_topspace[OF K] T(4) Pi_mem[OF continuous_map_funspace[OF T(1)]]
        by(auto intro!: arg_cong[where f="measure (Ni n)"] simp: space_Ni subset_iff space_\<nu>n) metis
      finally show ?thesis .
    qed
    define HP where "HP \<equiv> {N. sets N = sets (borel_of dH.mtopology) \<and> N (space N) \<le> ennreal r}"
    interpret dHs: Levy_Prokhorov "UNIV \<rightarrow>\<^sub>E {0..1}" dH
      using dH(1) by(auto simp: HP_def Levy_Prokhorov_def)
    have HP:"HP \<subseteq> {N. sets N = sets (borel_of dH.mtopology) \<and> finite_measure N}"
      by(auto simp: HP_def top.extremum_unique intro!: finite_measureI)
    have \<nu>n_HP:"range \<nu>n \<subseteq> HP"
      by(fastforce simp: HP_def sets_\<nu>n \<nu>n_le_r)
    then obtain \<nu>' a where \<nu>': "\<nu>' \<in> HP" "strict_mono a" "limitin dHs.LPm.mtopology (\<nu>n \<circ> a) \<nu>' sequentially"
      using dHs.mcompact_imp_LPmcompact[OF compact_dH,of r]
      unfolding dHs.LPm.compactin_sequentially HP_def by meson
    hence sets_\<nu>'[measurable_cong]: "sets \<nu>' = sets (borel_of dH.mtopology)"
      and \<nu>'_le_r: "\<nu>' (space \<nu>') \<le> ennreal r"
      by(auto simp: HP_def space_borel_of)
    have space_\<nu>': "space \<nu>' = UNIV \<rightarrow>\<^sub>E {0..1}"
      using sets_eq_imp_space_eq[OF sets_\<nu>'] by(simp add: space_borel_of)
    interpret \<nu>': finite_measure \<nu>'
      using \<nu>'_le_r by(auto intro!: finite_measureI simp: top_unique)
    interpret wc:mweak_conv_fin "UNIV \<rightarrow>\<^sub>E {0..1}" dH "\<nu>n \<circ> a" \<nu>' sequentially
      using \<nu>n_HP HP by(fastforce intro!: dHs.inP_mweak_conv_fin_all \<nu>' dHs.inP_I)
    have claim: "\<exists>E\<subseteq>A. E \<in> sets (borel_of dH.mtopology) \<and> measure \<nu>' (space \<nu>' - E) = 0"
    proof -
      {
        fix n
        have "\<exists>Kn. compactin mtopology Kn \<and> (\<forall>N\<in>LPm.mtopology closure_of \<Gamma>. measure N (space N - Kn) < 1 / Suc n)"
          using tight by(auto simp: tight_on_set_def)
      }
      then obtain Kn where Kn: "\<And>n. compactin mtopology (Kn n)"
        "\<And>N n. N \<in> LPm.mtopology closure_of \<Gamma> \<Longrightarrow> measure N (space N - Kn n) < 1 / Suc n"
        by metis
      have TKn_compact:"\<And>n. compactin dH.mtopology (T ` (Kn n))"
        by (metis Kn(1) T_cont image_compactin)
      hence [measurable]:"\<And>n. T ` Kn n \<in> sets (borel_of dH.mtopology)"
        by(auto intro!: borel_of_closed compactin_imp_closedin dH.Hausdorff_space_mtopology)
      have T_img: "\<And>n. T ` (Kn n) \<subseteq> A"
        using continuous_map_image_subset_topspace[OF T(1)] compactin_subset_topspace[OF Kn(1)]
        by fastforce
      define E where "E \<equiv> (\<Union>n. T ` (Kn n))"
      have [measurable]: "E \<in> sets (borel_of dH.mtopology)"
        by(simp add: E_def)
      show ?thesis
      proof(safe intro!: exI[where x=E])
        show "measure \<nu>' (space \<nu>' - E) = 0"
        proof(rule antisym[OF field_le_epsilon])
          fix e :: real
          assume e: "0 < e"
          then obtain n0 where n0: "1 / (Suc n0) < e"
            using nat_approx_posE by blast
          show "measure \<nu>' (space \<nu>' - E) \<le> 0 + e"
          proof -
            have "ereal (measure \<nu>' (space \<nu>' - E)) \<le> ereal (measure \<nu>' (space \<nu>' - T ` (Kn n0)))"
              by(auto intro!: \<nu>'.finite_measure_mono simp: E_def)
            also have "... \<le> liminf (\<lambda>n. ereal (measure ((\<nu>n \<circ> a) n) (space \<nu>' - T ` (Kn n0))))"
            proof -
              have "openin dH.mtopology (space \<nu>' - T ` (Kn n0))"
                by (metis TKn_compact compactin_imp_closedin dH.Hausdorff_space_mtopology dH.open_in_mspace openin_diff wc.space_N)
              with wc.mweak_conv_eq3[THEN iffD1,OF dHs.converge_imp_mweak_conv[OF \<nu>'(3)]]
              show ?thesis
                using \<nu>n_HP HP by(auto simp: dHs.inP_iff)
            qed
            also have "... = liminf (\<lambda>n. ereal (measure ((\<nu>n \<circ> a) n) (space ((\<nu>n \<circ> a) n) - T ` (Kn n0))))"
              by(auto simp: space_\<nu>n space_\<nu>')
            also have "... = liminf (\<lambda>n. ereal (measure ((Ni \<circ> a) n) (space ((Ni \<circ> a) n) - Kn n0)))"
              by(simp add: measure_\<nu>n_compact[OF Kn(1)])
            also have "... \<le> 1 / (Suc n0)"
              using Ni
              by(intro Liminf_le eventuallyI ereal_less_eq(3)[THEN iffD2] order.strict_implies_order Kn(2))
                auto
            also have "... < ereal e"
              using n0 by auto
            finally show ?thesis
              by simp
          qed
        qed simp
      qed(use E_def T_img in auto)
    qed
    then obtain E where E[measurable]: "E \<subseteq> A"
      "E \<in> sets (borel_of dH.mtopology)" "measure \<nu>' (space \<nu>' - E) = 0"
      by blast
    have measure_\<nu>': "measure \<nu>' (B \<inter> E) = measure \<nu>' B"
      if B[measurable]: "B \<in> sets (borel_of dH.mtopology)" for B
    proof(rule antisym)
      have "measure \<nu>' B = measure \<nu>' (B \<inter> E \<union> B \<inter> (space \<nu>' - E))"
        using sets.sets_into_space[OF B]
        by(auto intro!: arg_cong[where f="measure \<nu>'"] simp: space_\<nu>' space_borel_of)
      also have "... \<le> measure \<nu>' (B \<inter> E) +  measure \<nu>' (B \<inter> (space \<nu>' - E))"
        by(auto intro!: measure_Un_le)
      also have "... \<le> measure \<nu>' (B \<inter> E) +  measure \<nu>' ((space \<nu>' - E))"
        by(auto intro!: \<nu>'.finite_measure_mono)
      also have "... = measure \<nu>' (B \<inter> E)"
        by(simp add: E)
      finally show "measure \<nu>' B \<le> measure \<nu>' (B \<inter> E)" .
    qed(auto intro!: \<nu>'.finite_measure_mono)
    from this[of "space \<nu>'"] sets.sets_into_space[OF E(2)]
    have measure_\<nu>'E:"measure \<nu>' E = measure \<nu>' (space \<nu>')"
      by(auto simp: space_\<nu>' borel_of_open space_borel_of inf.absorb_iff2)
    show "\<exists>N r. N \<in> LPm.mtopology closure_of \<Gamma> \<and> strict_mono r \<and> limitin LPm.mtopology (Ni \<circ> r) N sequentially"
    proof -
      define \<nu> where "\<nu> \<equiv> restrict_space \<nu>' E"
      interpret \<nu>: finite_measure \<nu>
        by(auto intro!: finite_measure_restrict_space \<nu>'.finite_measure_axioms simp: \<nu>_def)
      have space_\<nu>:"space \<nu> = E"
        using E(2) \<nu>_def sets_\<nu>' space_restrict_space2 by blast
      have \<nu>_le_r: "\<nu> (space \<nu>) \<le> ennreal r"
        by(simp add: \<nu>_def emeasure_restrict_space order.trans[OF emeasure_space \<nu>'_le_r])
      have measure_\<nu>'2: "measure \<nu>' B = measure \<nu> (B \<inter> E)"
        if B[measurable]: "B \<in> sets (borel_of dH.mtopology)" for B
        by(auto simp: \<nu>_def measure_restrict_space measure_\<nu>')
      have T_inv_measurable[measurable]: "T_inv \<in> \<nu> \<rightarrow>\<^sub>M borel_of mtopology"
        using continuous_map_measurable[OF continuous_map_from_subtopology_mono[OF T(2) E(1)]]
        by(auto simp: \<nu>_def borel_of_subtopology dH
                cong: sets_restrict_space_cong[OF sets_\<nu>'] measurable_cong_sets)
      define N where "N \<equiv> distr \<nu> (borel_of mtopology) T_inv"
      have N_inP:"N \<in> \<P>"
        using Ni2[of 0,simplified subprob_space_def subprob_space_axioms_def]
        by(auto simp: \<P>_def N_def space_Ni emeasure_distr order.trans[OF emeasure_space \<nu>_le_r] \<nu>.finite_measure_distr)
      then interpret wcN:mweak_conv_fin M d "Ni \<circ> a" N sequentially
        using subset_trans[OF Ni closure_of_subset_topspace] by(auto intro!: inP_mweak_conv_fin_all)  
      show "\<exists>N r. N \<in> LPm.mtopology closure_of \<Gamma> \<and> strict_mono r \<and> limitin LPm.mtopology (Ni \<circ> r) N sequentially"
      proof(safe intro!: exI[where x=N] exI[where x=a])
        show limit: "limitin LPm.mtopology (Ni \<circ> a) N sequentially"
        proof(rule mweak_conv_imp_converge)
          show "mweak_conv_seq (Ni \<circ> a) N"
            unfolding wcN.mweak_conv_eq2
          proof safe
            have [measurable]:"UNIV \<rightarrow>\<^sub>E {0..1} \<in> sets (borel_of dH.mtopology)"
              by(auto simp: borel_of_open)
            have 1:"measure ((Ni \<circ> a) n) M = measure ((\<nu>n \<circ> a) n) (UNIV \<rightarrow>\<^sub>E {0..1})" for n
              using continuous_map_funspace[OF T(1)]
              by(auto simp: \<nu>n_def measure_distr space_Ni intro!: arg_cong[where f="measure (Ni (a n))"])
            have 2: "measure N M = measure \<nu>' (space \<nu>')"
            proof -
              have [measurable]: "M \<in> sets (borel_of mtopology)"
                by(auto intro!: borel_of_open)
              have "measure N M = measure \<nu> (T_inv -` M \<inter> space \<nu>)"
                by(auto simp: N_def intro!: measure_distr)
              also have "... = measure \<nu> (space \<nu> \<inter> E)"
                using measurable_space[OF T_inv_measurable]
                by(auto intro!: arg_cong[where f="measure \<nu>"] simp: space_borel_of space_\<nu>)
              also have "... = measure \<nu>' (space \<nu>)"
                by(rule measure_\<nu>'2[symmetric]) (simp add: space_\<nu>)
              also have "... = measure \<nu>' (space \<nu>')"
                by(simp add: measure_\<nu>'E space_\<nu>)
              finally show ?thesis .
            qed
            show "(\<lambda>n. measure ((Ni \<circ> a) n) M) \<longlonglongrightarrow> measure N M"
              unfolding 1 2 using HP \<nu>n_HP wc.mweak_conv_eq2[THEN iffD1,OF dHs.converge_imp_mweak_conv[OF \<nu>'(3)]]
              by(auto simp: space_\<nu>' dHs.inP_iff)
          next
            fix C
            assume C: "closedin mtopology C"
            hence [measurable]: "C \<in> sets (borel_of mtopology)"
              by(auto intro!: borel_of_closed)
            have "closedin (subtopology dH.mtopology A) (T ` C)"
            proof -
              have "T ` C = {x \<in> topspace (subtopology Hilbert_cube_topology A). T_inv x \<in> C}"
                using closedin_subset[OF C] T(3,4) continuous_map_funspace[OF T(1)] continuous_map_funspace[OF T(2)]
                by (auto simp: rev_image_eqI)
              also note closedin_continuous_map_preimage[OF T(2) C]
              finally show ?thesis
                by(simp add: dH)
            qed
            then obtain K where K: "closedin dH.mtopology K" "T ` C = K \<inter> A"
              by (meson closedin_subtopology)
            hence [measurable]: "K \<in> sets (borel_of dH.mtopology)"
              by(simp add: borel_of_closed)
            have C_eq:"C = T -` K \<inter> M"
            proof -
              have "C = (T -` T ` C) \<inter> M"
                using closedin_subset[OF C] injT by(auto dest: inj_onD)
              also have "... = (T -` (K \<inter> A)) \<inter> M"
                by(simp only: K(2))
              also have "... = T -` K \<inter> M"
                using A(1) continuous_map_funspace[OF T(1)] by auto
              finally show ?thesis .
            qed
            hence 1:"measure ((Ni \<circ> a) n) C = measure ((\<nu>n \<circ> a) n) K" for n
              by(auto simp: \<nu>n_def measure_distr space_Ni)
            have "limsup (\<lambda>n. ereal (measure ((Ni \<circ> a) n) C)) = limsup (\<lambda>n. ereal (measure ((\<nu>n \<circ> a) n) K))"
              unfolding 1 by simp
            also have "... \<le> ereal (measure \<nu>' K)"
              using \<nu>n_HP HP wc.mweak_conv_eq2[THEN iffD1,OF dHs.converge_imp_mweak_conv[OF \<nu>'(3)]] K(1) dHs.inP_iff by auto
            also have "... = ereal (measure \<nu> (K \<inter> E))"
              by(simp add: measure_\<nu>'2)
            also have "... = ereal (measure \<nu> (T_inv -` C \<inter> space \<nu>))"
              using measurable_space[OF T_inv_measurable] K(2) E(1) closedin_subset[OF K(1)] A(1) T(3,4)
              by(fastforce intro!: arg_cong[where f="measure \<nu>"] simp: space_\<nu> C_eq space_borel_of subsetD)
            also have "... = ereal (measure N C)"
              by(auto simp: N_def measure_distr)
            finally show "limsup (\<lambda>n. ereal (measure ((Ni \<circ> a) n) C)) \<le> ereal (measure N C)" .
          qed
        qed(use N_inP Ni assms closure_of_subset_topspace[of LPm.mtopology \<Gamma>] in auto)
        have "range (Ni \<circ> a) \<subseteq> LPm.mtopology closure_of \<Gamma>"
          using Ni by auto
        thus "N \<in> LPm.mtopology closure_of \<Gamma>"
          using limit LPm.metric_closedin_iff_sequentially_closed[THEN iffD1,OF closedin_closure_of[of _ \<Gamma>]]
          by blast
      qed fact
    qed
  qed(use assms(1) closedin_subset[OF closedin_closure_of[of LPm.mtopology]] in auto)
qed

corollary Prokhorov_theorem_LP:
  assumes "\<Gamma> \<subseteq> {N. sets N = sets (borel_of mtopology) \<and> emeasure N (space N) \<le> ennreal r}"
    and "separable_space mtopology" mcomplete
  shows "compactin LPm.mtopology (LPm.mtopology closure_of \<Gamma>) \<longleftrightarrow> tight_on_set mtopology \<Gamma>"
proof -
  have "\<Gamma> \<subseteq> \<P>"
    using assms(1) by(auto intro!: finite_measureI inP_I simp: top.extremum_unique)
  thus ?thesis
    using assms by(auto simp: relatively_compact_imp_tight_LP tight_imp_relatively_compact_LP)
qed

subsection \<open> Completeness of the L\'evy-Prokhorov Metric \<close>
lemma mcomplete_tight_on_set:
  assumes "\<Gamma> \<subseteq> \<P>" mcomplete
    and "\<And>e f. e > 0 \<Longrightarrow> f > 0
          \<Longrightarrow> \<exists>an n. an ` {..n::nat} \<subseteq> M \<and> (\<forall>N\<in>\<Gamma>. measure N (M - (\<Union>i\<le>n. mball (an i) f)) \<le> e)"
  shows "tight_on_set mtopology \<Gamma>"
  unfolding tight_on_set_def
proof safe
  fix e :: real
  assume e: "0 < e"
  then have "\<exists>an n. an ` {..n::nat} \<subseteq> M \<and>
     (\<forall>N\<in>\<Gamma>. measure N (M - (\<Union>i\<le>n. mball (an i) (1 / (1 + real m)))) \<le> e / 2 * (1 / 2) ^ Suc m)" for m
    using assms(3)[of "e / 2 * (1 / 2) ^ Suc m" "1 / (1 + real m)"] by fastforce
  then obtain anm nm where anm: "\<And>m. anm m ` {..nm m::nat} \<subseteq> M"
    "\<And>m N. N \<in> \<Gamma> \<Longrightarrow> measure N (M - (\<Union>i\<le>nm m. mball (anm m i) (1 / (1 + real m)))) \<le> e/ 2 * (1 / 2)^Suc m"
    by metis
  define K where "K \<equiv> (\<Inter>m. (\<Union>i\<le>nm m. mcball (anm m i) (1 / (1 + real m))))"
  have K_closed: "closedin mtopology K"
    by(auto simp: K_def intro!: closedin_Union)
  show "\<exists>K. compactin mtopology K \<and> (\<forall>M\<in>\<Gamma>. measure M (space M - K) < e)"
  proof(safe intro!: exI[where x=K])
    have "mtotally_bounded K"
      unfolding mtotally_bounded_def2
    proof safe
      fix \<epsilon> :: real
      assume \<epsilon>: "0 < \<epsilon>"
      then obtain m where m: "1 / (1 + real m) < \<epsilon>"
        using nat_approx_posE by auto
      show "\<exists>Ka. finite Ka \<and> Ka \<subseteq> M \<and> K \<subseteq> (\<Union>x\<in>Ka. mball x \<epsilon>)"
      proof(safe intro!: exI[where x="anm m ` {..nm m}"])
        fix x
        assume "x \<in> K"
        then have "x \<in> (\<Union>i\<le>nm m. mcball (anm m i) (1 / (1 + real m)))"
          by(auto simp: K_def)
        also have "... \<subseteq> (\<Union>i\<le>nm m. mball (anm m i) \<epsilon>)"
          by(rule UN_mono) (use m in auto)
        finally show "x \<in> (\<Union>x\<in>anm m ` {..nm m}. mball x \<epsilon>)"
          by auto
      qed(use anm in auto)
    qed
    thus "compactin mtopology K"
      by(simp add: mtotally_bounded_eq_compact_closedin[OF assms(2) K_closed])
  next
    fix N
    assume N:"N \<in> \<Gamma>"
    then interpret N: finite_measure N
      using assms(1) inP_D(1) by auto
    have [measurable]: "M \<in> sets N" "\<And>a b. mcball a b \<in> sets N"
      using N inP_D(2) assms(1) by(auto intro!: borel_of_closed)
    have [measurable]: "\<And>a b. mball a b \<in> sets N"
      using N inP_D(2) assms(1) by(auto intro!: borel_of_open)
    have [simp]: "summable (\<lambda>m. measure N (M - (\<Union>i\<le>nm m. mball (anm m i) (1 / (1 + real m)))))"
      using anm(2)[OF N]
      by(auto intro!: summable_comparison_test_ev[where g="\<lambda>n. e / 2 * (1 / 2) ^ Suc n"
            and f="\<lambda>m. measure N (M - (\<Union>i\<le>nm m. mball (anm m i) (1 / (1 + real m))))"] eventuallyI)
    show "measure N (space N - K) < e"
    proof -
      have "measure N (space N - K) = measure N (M - K)"
        using N assms(1) inP_D(3) by auto
      also have "... = measure N (\<Union>m. M - (\<Union>i\<le>nm m. mcball (anm m i) (1 / (1 + real m))))"
        by(auto simp: K_def)
      also have "... \<le> (\<Sum>m. e / 2 * (1 / 2) ^ Suc m)"
      proof -
        have "(\<lambda>k. measure N (\<Union>m\<le>k. M - (\<Union>i\<le>nm m. mcball (anm m i) (1 / (1 + real m)))))
               \<longlonglongrightarrow> measure N (\<Union>i. \<Union>m\<le>i. M - (\<Union>i\<le>nm m. mcball (anm m i) (1 / (1 + real m))))"
          by(rule N.finite_Lim_measure_incseq) (auto intro!: incseq_SucI)
        moreover have "(\<Union>i. \<Union>m\<le>i. M - (\<Union>i\<le>nm m. mcball (anm m i) (1 / (1 + real m))))
                        = (\<Union>m. M - (\<Union>i\<le>nm m. mcball (anm m i) (1 / (1 + real m))))"
          by blast
        ultimately have 1:"(\<lambda>k. measure N (\<Union>m\<le>k. M - (\<Union>i\<le>nm m. mcball (anm m i) (1 / (1 + real m)))))
                            \<longlonglongrightarrow> measure N  (\<Union>m. M - (\<Union>i\<le>nm m. mcball (anm m i) (1 / (1 + real m))))"
          by simp
        show ?thesis
        proof(safe intro!: Lim_bounded[OF 1])
          fix n
          show "measure N (\<Union>m\<le>n. M - (\<Union>i\<le>nm m. mcball (anm m i) (1 / (1 + real m))))
                \<le> (\<Sum>m. e / 2 * (1 / 2) ^ Suc m)" (is "?lhs \<le> ?rhs")
          proof -
            have "?lhs \<le> (\<Sum>m\<le>n. measure N (M - (\<Union>i\<le>nm m. mcball (anm m i) (1 / (1 + real m)))))"
              by(rule N.finite_measure_subadditive_finite) auto
            also have "... \<le> (\<Sum>m\<le>n. measure N (M - (\<Union>i\<le>nm m. mball (anm m i) (1 / (1 + real m)))))"
              by(rule sum_mono) (auto intro!: N.finite_measure_mono)
            also have "... \<le> (\<Sum>m. measure N (M - (\<Union>i\<le>nm m. mball (anm m i) (1 / (1 + real m)))))"
              by(rule sum_le_suminf) auto
            also have "... \<le> ?rhs"
              by(rule suminf_le) (use anm(2)[OF N] in auto)
            finally show ?thesis .
          qed
        qed
      qed
      also have "... = e / 2 * (\<Sum>m. (1 / 2) ^ Suc m)"
        by(rule suminf_mult) auto
      also have "... = e / 2"
        using power_half_series sums_unique by fastforce
      also have "... < e"
        using e by simp
      finally show ?thesis .
    qed
  qed
qed(use assms(1) inP_D in auto)

lemma mcomplete_LPmcomplete:
  assumes mcomplete "separable_space mtopology"
  shows LPm.mcomplete
proof -
  consider "M = {}" | "M \<noteq> {}"
    by blast
  then show ?thesis
  proof cases
    case 1
    from M_empty_P[OF this]
    have "\<P> = {} \<or> \<P> = {count_space {}}" .
    then show ?thesis
      using LPm.compact_space_eq_Bolzano_Weierstrass LPm.compact_space_imp_mcomplete finite_subset
      by fastforce
  next
    case M_ne:2
    show ?thesis
      unfolding LPm.mcomplete_def
    proof safe
      fix Ni
      assume cauchy: "LPm.MCauchy Ni"
      hence range_Ni: "range Ni \<subseteq> \<P>"
        by(auto simp: LPm.MCauchy_def)
      hence range_Ni2: "range Ni \<subseteq> LPm.mtopology closure_of (range Ni)"
        by (simp add: closure_of_subset)
      have Ni_inP: "\<And>i. Ni i \<in> \<P>"
        using cauchy by(auto simp: LPm.MCauchy_def)
      hence "\<And>n. finite_measure (Ni n)"
        and sets_Ni[measurable_cong]:"\<And>n. sets (Ni n) = sets (borel_of mtopology)"
        and space_Ni: "\<And>n. space (Ni n) = M"
        by(auto dest: inP_D)
      then interpret Ni: finite_measure "Ni n" for n
        by simp
      have "\<exists>r\<ge>0. \<forall>i. Ni i (space (Ni i)) \<le> ennreal r"
      proof -
        obtain N where N: "\<And>n m. n \<ge> N \<Longrightarrow> m \<ge> N \<Longrightarrow> LPm (Ni n) (Ni m) < 1"
          using LPm.MCauchy_def cauchy zero_less_one by blast
        define r where "r = max (Max ((\<lambda>i. measure (Ni i) (space (Ni i))) ` {..N})) (measure (Ni N) (space (Ni N)) + 1)"
        show ?thesis
        proof(safe intro!: exI[where x=r])
          fix i
          consider "i \<le> N" | "N \<le> i"
            by fastforce
          then show "Ni i (space (Ni i)) \<le> ennreal r"
          proof cases
            assume "i \<le> N"
            then have "measure (Ni i) (space (Ni i)) \<le> r"
              by(auto simp: r_def intro!: max.coboundedI1)
            thus ?thesis
              by (simp add: measure_def enn2real_le)
          next
            assume i:"i \<ge> N"
            have "measure (Ni i) (space (Ni i)) \<le> r"
            proof -
              have "measure (Ni i) M \<le> measure (Ni N) (\<Union>a\<in>M. mball a 1) + 1"
                using range_Ni by(auto intro!: LPm_less_then[of "Ni N"] N i borel_of_open)
              also have "... \<le> measure (Ni N) (space (Ni N)) + 1"
                using Ni.bounded_measure by auto
              also have "... \<le> r"
                by(auto simp: r_def)
              finally show ?thesis
                by(simp add: space_Ni)
            qed
            thus ?thesis
              by (simp add: Ni.emeasure_eq_measure ennreal_leI)
          qed
        qed(auto simp: r_def intro!: max.coboundedI2)
      qed
      then obtain r where r_nonneg: "r \<ge> 0" and r_bounded:"\<And>i. Ni i (space (Ni i)) \<le> ennreal r"
        by blast
      with sets_Ni have range_Ni':
        "range Ni \<subseteq> {N. sets N = sets (borel_of mtopology) \<and> emeasure N (space N) \<le> ennreal r}"
        by blast
      have M_meas[measurable]: "M \<in> sets (borel_of mtopology)"
        by(simp add: borel_of_open)
      have mball_meas[measurable]: "mball a e \<in> sets (borel_of mtopology)" for a e
        by(auto intro!: borel_of_open)
      have Ni_Cauchy: "\<And>e. e > 0 \<Longrightarrow>  \<exists>n0. \<forall>n n'. n0 \<le> n \<longrightarrow> n0 \<le> n' \<longrightarrow> LPm (Ni n) (Ni n') < e"
        using cauchy by(auto simp: LPm.MCauchy_def)
      have "tight_on_set mtopology (range Ni)"
      proof(rule mcomplete_tight_on_set[OF range_Ni assms(1)])
        fix e f :: real
        assume e: "e > 0" and f: "f > 0"
        with Ni_Cauchy[of "min e f / 2"] obtain n0 where n0:
          "\<And>n m. n0 \<le> n \<Longrightarrow> n0 \<le> m \<Longrightarrow> LPm (Ni n) (Ni m) < min e f / 2"
          by fastforce
        obtain D where D: "mdense D" "countable D"
          using assms(2) separable_space_def2 by blast
        then obtain an where an: "\<And>n::nat. an n \<in> D" "range an = D"
          by (metis M_ne mdense_empty_iff rangeI uncountable_def)
        have "\<exists>n1. \<forall>i\<le>n0. measure (Ni i) (M - (\<Union>i\<le>n1. mball (an i) (f / 2))) \<le> min e f / 2"
        proof -
          have "\<exists>n1. measure (Ni i) (M - (\<Union>i\<le>n1. mball (an i) (f / 2))) \<le> min e f / 2" for i
          proof -
            have "(\<lambda>n1. measure (Ni i) (M - (\<Union>i\<le>n1. mball (an i) (f / 2)))) \<longlonglongrightarrow> 0"
            proof -
              have 1: "(\<lambda>n1. measure (Ni i) (M - (\<Union>i\<le>n1. mball (an i) (f / 2))))
                        = (\<lambda>n1. measure (Ni i) M - measure (Ni i) ((\<Union>i\<le>n1. mball (an i) (f / 2))))"
                using Ni.finite_measure_compl by(auto simp: space_Ni)
              have "(\<lambda>n1. measure (Ni i) ((\<Union>i\<le>n1. mball (an i) (f / 2)))) \<longlonglongrightarrow> measure (Ni i) M"
              proof -
                have "(\<lambda>n1. measure (Ni i) ((\<Union>i\<le>n1. mball (an i) (f / 2))))
                       \<longlonglongrightarrow> measure (Ni i) (\<Union>n1. (\<Union>i\<le>n1. mball (an i) (f / 2)))"
                  by(intro Ni.finite_Lim_measure_incseq incseq_SucI UN_mono) auto
                moreover have "(\<Union>n1. (\<Union>i\<le>n1. mball (an i) (f / 2))) = M"
                  using mdense_balls_cover[OF D(1)[simplified an(2)[symmetric]],of "f / 2"] f by auto
                ultimately show ?thesis by argo
              qed
              from tendsto_diff[OF tendsto_const[where k="measure (Ni i) M"] this] show ?thesis
                unfolding 1 by simp
            qed
            thus ?thesis
              by (meson e f LIMSEQ_le_const half_gt_zero less_eq_real_def linorder_not_less min_less_iff_conj)
          qed
          then obtain ni where ni: "\<And>i. measure (Ni i) (M - (\<Union>i\<le>ni i. mball (an i) (f / 2))) \<le> min e f / 2"
            by metis
          define n1 where "n1 \<equiv> Max (ni ` {..n0})"
          show ?thesis
          proof(safe intro!: exI[where x=n1])
            fix i
            assume i: "i \<le> n0"
            then have nii:"ni i \<le> n1"
              by (simp add: n1_def)
            show "measure (Ni i) (M - (\<Union>i\<le>n1. mball (an i) (f / 2))) \<le> min e f / 2"
            proof -
              have "measure (Ni i) (M - (\<Union>i\<le>n1. mball (an i) (f / 2)))
                    \<le> measure (Ni i) (M - (\<Union>i\<le>ni i. mball (an i) (f / 2)))"
                using nii by(fastforce intro!: Ni.finite_measure_mono)
              also have "... \<le> min e f / 2"
                by fact
              finally show ?thesis .
            qed
          qed
        qed
        then obtain n1 where n1: 
          "\<And>i. i \<le> n0 \<Longrightarrow> measure (Ni i) (M - (\<Union>i\<le>n1. mball (an i) (f / 2))) \<le> e / 2"
          "\<And>i. i \<le> n0 \<Longrightarrow> measure (Ni i) (M - (\<Union>i\<le>n1. mball (an i) (f / 2))) \<le> f / 2"
          by auto
        show "\<exists>an n. an ` {..n::nat} \<subseteq> M \<and> (\<forall>N\<in>range Ni. measure N (M - (\<Union>i\<le>n. mball (an i) f)) \<le> e)"
        proof(safe intro!: exI[where x=an] exI[where x=n1])
          fix n
          consider "n \<le> n0" | "n0 \<le> n"
            by linarith
          then show "measure (Ni n) (M - (\<Union>i\<le>n1. mball (an i) f)) \<le> e"
          proof cases
            case 1
            have "measure (Ni n) (M - (\<Union>i\<le>n1. mball (an i) f))
                   \<le> measure (Ni n) (M - (\<Union>i\<le>n1. mball (an i) (f / 2)))"
              using f by(fastforce intro!: Ni.finite_measure_mono)
            also have "... \<le> e"
              using n1[OF 1] e by linarith
            finally show ?thesis .
          next
            case 2
            have "measure (Ni n) (M - (\<Union>i\<le>n1. mball (an i) f))
                  \<le> measure (Ni n0) (\<Union>a\<in>M - (\<Union>i\<le>n1. mball (an i) f). mball a (min e f / 2)) + min e f / 2"
              by(intro LPm_less_then(2) n0 2 Ni_inP) auto
            also have "... \<le> measure (Ni n0) (M - (\<Union>i\<le>n1. mball (an i) (f / 2))) + min e f / 2"
            proof -
              have "(\<Union>a\<in>M - (\<Union>i\<le>n1. mball (an i) f). mball a (min e f / 2))
                     \<subseteq> M - (\<Union>i\<le>n1. mball (an i) (f / 2))"
              proof safe
                fix x a i
                assume x: "x \<in> mball a (min e f / 2)"  "x \<in> mball (an i) (f / 2)"
                  and a:"a \<in> M" "a \<notin> (\<Union>i\<le>n1. mball (an i) f)" and i:"i \<le> n1"
                hence "d (an i) x < f / 2" "d x a < f / 2"
                  by(auto simp: commute)
                hence "d (an i) a < f"
                  using triangle[of "an i" x a] a(1) x(2) by auto
                with a(2) i
                show False
                  using a(1) atMost_iff image_eqI x(2) by auto
              qed simp
              thus ?thesis
                by(auto intro!: Ni.finite_measure_mono)
            qed
            also have "... \<le> e"
              using n1(1)[OF order.refl] by linarith
            finally show ?thesis .
          qed
        qed(use an dense_in_subset[OF D(1)] in auto)
      qed
      from tight_imp_relatively_compact_LP[OF range_Ni' assms(2) this] range_Ni2
      obtain l N where "strict_mono l" "limitin LPm.mtopology (Ni \<circ> l) N sequentially" 
        unfolding LPm.compactin_sequentially by blast
      from LPm.MCauchy_convergent_subsequence[OF cauchy this]
      show "\<exists>N. limitin LPm.mtopology Ni N sequentially"
        by blast
    qed
  qed
qed

subsection \<open> Equivalence of Separability, Completeness, and Compactness \<close>
lemma return_inP[simp]:"return (borel_of mtopology) x \<in> \<P>"
  by (metis emeasure_empty ennreal_top_neq_zero finite_measureI inP_I infinity_ennreal_def sets_return space_return subprob_space.axioms(1) subprob_space_return_ne)

lemma LPm_return_eq:
  assumes "x \<in> M" "y \<in> M"
  shows "LPm (return (borel_of mtopology) x) (return (borel_of mtopology) y) = min 1 (d x y)"
proof(rule antisym[OF min.boundedI])
  show "LPm (return (borel_of mtopology) x) (return (borel_of mtopology) y) \<le> d x y"
  proof(rule field_le_epsilon)
    fix e :: real
    assume e: "e > 0"
    show "LPm (return (borel_of mtopology) x) (return (borel_of mtopology) y) \<le> d x y + e"
    proof(rule LPm_imp_le)
      fix B
      assume B[measurable]: "B \<in> sets (borel_of mtopology)"
      have "x \<in> B \<Longrightarrow> y \<in> (\<Union>a\<in>B. mball a (d x y + e))"
        using e assms by auto
      thus "measure (return (borel_of mtopology) x) B
            \<le> measure (return (borel_of mtopology) y) (\<Union>a\<in>B. mball a (d x y + e)) + (d x y + e)"
        using e by(simp add: measure_return indicator_def)
    next
      fix B
      assume B[measurable]: "B \<in> sets (borel_of mtopology)"
      have "y \<in> B \<Longrightarrow> x \<in> (\<Union>a\<in>B. mball a (d x y + e))"
        using e assms by (auto simp: commute)
      thus "measure (return (borel_of mtopology) y) B
            \<le> measure (return (borel_of mtopology) x) (\<Union>a\<in>B. mball a (d x y + e)) + (d x y + e)"
        using e by(simp add: measure_return indicator_def)
    qed (simp add: add.commute add_pos_nonneg e)
  qed
next
  consider "LPm (return (borel_of mtopology) x) (return (borel_of mtopology) y) < 1"
    | "LPm (return (borel_of mtopology) x) (return (borel_of mtopology) y) \<ge> 1"
    by linarith
  then show "min 1 (d x y)\<le> LPm (return (borel_of mtopology) x) (return (borel_of mtopology) y)"
  proof cases
    case 1
    have 2:"d x y < a" if a: "LPm (return (borel_of mtopology) x) (return (borel_of mtopology) y) < a"
      "a < 1" for a
    proof -
      have [measurable]: "{x} \<in> sets (borel_of mtopology)"
        using assms by(auto simp add: closedin_t1_singleton t1_space_mtopology intro!: borel_of_closed)
      have "measure (return (borel_of mtopology) x) {x}
            \<le> measure (return (borel_of mtopology) y) (\<Union>b\<in>{x}. mball b a) + a"
        using assms subprob_space.subprob_emeasure_le_1[OF subprob_space_return_ne[of "borel_of mtopology"]]
        by(intro LPm_less_then(1)[where A="{x}",OF _ _ a(1)])
          (auto simp: space_borel_of space_scale_measure)
      thus ?thesis
        using assms a(2) linorder_not_less by(fastforce simp: measure_return indicator_def)
    qed
    have "d x y < a" if a: "LPm (return (borel_of mtopology) x) (return (borel_of mtopology) y) < a" for a
    proof(cases "a < 1")
      assume r1:"~ a < 1"
      obtain k where k:"LPm (return (borel_of mtopology) x) (return (borel_of mtopology) y) < k" "k < 1"
        using dense 1 by blast
      show ?thesis
        using 2[OF k] k(2) r1 by linarith
    qed(use 2 a in auto)
    thus ?thesis
      by force
  qed simp
next
  show "LPm (return (borel_of mtopology) x) (return (borel_of mtopology) y) \<le> 1"
    by(rule order.trans[OF LPm_le_max_measure])
      (metis assms(1) assms(2) indicator_simps(1) max.idem measure_return nle_le sets.top space_borel_of space_return topspace_mtopology)
qed

corollary LPm_return_eq_capped_dist:
  assumes "x \<in> M" "y \<in> M"
  shows "LPm (return (borel_of mtopology) x)(return (borel_of mtopology) y) = capped_dist 1 x y"
  by(simp add: capped_dist_def assms LPm_return_eq)

corollary MCauchy_iff_MCauchy_return:
  assumes "range xn \<subseteq> M"
  shows "MCauchy xn \<longleftrightarrow> LPm.MCauchy (\<lambda>n. return (borel_of mtopology) (xn n))"
proof -
  interpret c: Metric_space M "capped_dist 1"
    using capped_dist by blast
  show ?thesis
    using range_subsetD[OF assms(1)]
    by(auto simp: MCauchy_capped_metric[of 1,symmetric] c.MCauchy_def LPm.MCauchy_def LPm_return_eq_capped_dist)
qed

lemma conv_conv_return:
  assumes "limitin mtopology xn x sequentially"
  shows "limitin LPm.mtopology (\<lambda>n. return (borel_of mtopology) (xn n)) (return (borel_of mtopology) x) sequentially"
proof -
  interpret c: Metric_space M "capped_dist 1"
    using capped_dist by blast
  have clim:"limitin c.mtopology xn x sequentially"
    using assms by (simp add: mtopology_capped_metric)
  show ?thesis
    using LPm_return_eq_capped_dist clim
    by(fastforce simp: c.limit_metric_sequentially LPm.limit_metric_sequentially)
qed

lemma conv_iff_conv_return:
  assumes "range xn \<subseteq> M" "x \<in> M"
  shows "limitin mtopology xn x sequentially
         \<longleftrightarrow> limitin LPm.mtopology (\<lambda>n. return (borel_of mtopology) (xn n))
                                   (return (borel_of mtopology) x) sequentially"
proof -
  have xn: "\<And>n. xn n \<in> M"
    using assms by auto
  interpret c: Metric_space M "capped_dist 1"
    using capped_dist by blast
  have "limitin mtopology xn x sequentially \<longleftrightarrow> limitin c.mtopology xn x sequentially"
    by (simp add: mtopology_capped_metric)
  also have "...
    \<longleftrightarrow> limitin LPm.mtopology (\<lambda>n. return (borel_of mtopology) (xn n)) (return (borel_of mtopology) x) sequentially"
    using xn assms by(auto simp: c.limit_metric_sequentially LPm.limit_metric_sequentially LPm_return_eq_capped_dist)
  finally show ?thesis .
qed

lemma continuous_map_return: "continuous_map mtopology LPm.mtopology (\<lambda>x. return (borel_of mtopology) x)"
  by(auto simp: continuous_map_iff_limit_seq[OF first_countable_mtopology] conv_conv_return)

lemma homeomorphic_map_return:
  "homeomorphic_map mtopology
                    (subtopology LPm.mtopology ((\<lambda>x. return (borel_of mtopology) x) ` M))
                    (\<lambda>x. return (borel_of mtopology) x)"
proof(rule homeomorphic_maps_imp_map)
  define inv where "inv \<equiv> (\<lambda>N. THE x. x \<in> M \<and> N = return (borel_of mtopology) x)"
  have inv_eq: "inv (return (borel_of mtopology) x) = x" if x: "x \<in> M" for x
  proof -
    have "inv (return (borel_of mtopology) x) \<in> M \<and> return (borel_of mtopology) x
           = return (borel_of mtopology) (inv (return (borel_of mtopology) x))"
      unfolding inv_def
    proof(rule theI)
      fix y
      assume "y \<in> M \<and> return (borel_of mtopology) x = return (borel_of mtopology) y"
      then show "y = x"
        using LPm_return_eq[OF x,of y] x
        by (auto intro!: zero[THEN iffD1] simp: commute simp del: zero)
    qed(use x in auto)
    thus ?thesis
      by (metis LPm_return_eq_capped_dist Metric_space.zero capped_dist x)
  qed
  interpret s: Submetric \<P> LPm "(\<lambda>x. return (borel_of mtopology) x) ` M"
    by standard auto
  have "continuous_map mtopology s.sub.mtopology (\<lambda>x. return (borel_of mtopology) x)"
    using continuous_map_return
    by (simp add: LPm.Metric_space_axioms metric_continuous_map s.sub.Metric_space_axioms)
  moreover have "continuous_map s.sub.mtopology mtopology inv"
    unfolding continuous_map_iff_limit_seq[OF s.sub.first_countable_mtopology]
  proof safe
    fix Ni N
    assume h:"limitin s.sub.mtopology Ni N sequentially"
    then obtain x where x: "x \<in> M" "N = return (borel_of mtopology) x"
      using s.sub.limit_metric_sequentially by auto
    interpret c: Metric_space M "capped_dist 1"
      using capped_dist by blast
    show "limitin mtopology (\<lambda>n. inv (Ni n)) (inv N) sequentially"
      unfolding c.limit_metric_sequentially mtopology_capped_metric[of 1,symmetric]
    proof safe
      fix e :: real
      assume "e > 0"
      then obtain n0 where n0:
        "\<And>n. n \<ge> n0 \<Longrightarrow> Ni n \<in> (\<lambda>x. return (borel_of mtopology) x) ` M"
        "\<And>n. n \<ge> n0 \<Longrightarrow> LPm (Ni n) N < e"
        by (metis h s.sub.limit_metric_sequentially)
      then obtain xn where xn:  "\<And>n. n \<ge> n0 \<Longrightarrow> xn n \<in> M"
        "\<And>n. n \<ge> n0 \<Longrightarrow> Ni n = return (borel_of mtopology) (xn n)"
        unfolding image_def by simp metis
      thus "\<exists>Na. \<forall>n\<ge>Na. inv (Ni n) \<in> M \<and> capped_dist 1 (inv (Ni n)) (inv N) < e"
        using n0 by(auto intro!: exI[where x=n0] simp: inv_eq x LPm_return_eq_capped_dist)
    qed(simp add: inv_eq x)
  qed
  moreover have "\<forall>x\<in>topspace mtopology. inv (return (borel_of mtopology) x) = x"
    "\<forall>y\<in>topspace s.sub.mtopology. return (borel_of mtopology) (inv y) = y"
    by(auto simp: inv_eq)
  ultimately show "homeomorphic_maps mtopology (subtopology LPm.mtopology ((\<lambda>x. return (borel_of mtopology) x) ` M))
                                     (\<lambda>x. return (borel_of mtopology) x) inv"
    by(simp add: s.mtopology_submetric homeomorphic_maps_def)
qed

corollary homeomorphic_space_mtopology_return:
  "mtopology homeomorphic_space (subtopology LPm.mtopology ((\<lambda>x. return (borel_of mtopology) x) ` M))"
  using homeomorphic_map_return homeomorphic_space by fast

lemma closedin_returnM: "closedin LPm.mtopology ((\<lambda>x. return (borel_of mtopology) x) ` M)"
  unfolding LPm.metric_closedin_iff_sequentially_closed
proof safe
  fix Ni N
  assume h:"range Ni \<subseteq> (\<lambda>x. return (borel_of mtopology) x) ` M" "limitin LPm.mtopology Ni N sequentially"
  from range_subsetD[OF this(1)]
  obtain xi where xi: "\<And>i. xi i \<in> M" "Ni = (\<lambda>i. return (borel_of mtopology) (xi i))"
    unfolding image_def by simp metis
  have sets_N[measurable_cong]: "sets N = sets (borel_of mtopology)"
    by (meson LPm.limitin_mspace h(2) inP_D)
  have [measurable]:"\<And>n. {xi n} \<in> sets N"
    by (simp add: Hausdorff_space_mtopology borel_of_closed closedin_Hausdorff_sing_eq sets_N xi(1))
  interpret N: finite_measure N
    by (meson LPm.limitin_metric_dist_null h(2) inP_D(1))
  interpret Ni: prob_space "Ni i" for i
    by(auto intro!: prob_space_return simp: xi space_borel_of)
  have N_r: "ereal (measure N A) \<le> ereal 1" for A
    unfolding ereal_less_eq(3)
  proof(rule order.trans[OF N.bounded_measure])
    interpret mweak_conv_fin M d Ni N sequentially
      using limitin_topspace[OF h(2)] by(auto intro!: inP_mweak_conv_fin inP_I return_inP simp: xi(2))
    have "mweak_conv_seq Ni N"
      using converge_imp_mweak_conv h(2) xi(2) by force
    from mweak_conv_imp_limit_space[OF this]
    show "measure N (space N) \<le> 1"
      by(auto intro!: tendsto_upperbound[where F=sequentially and f="\<lambda>n. Ni.prob n (space N)"] simp: space_N space_Ni)
  qed
  have "\<exists>x. limitin mtopology xi x sequentially"
  proof(rule ccontr)
    assume contr:"\<nexists>x. limitin mtopology xi x sequentially"
    have MCauchy_xi: "MCauchy xi"
      using MCauchy_iff_MCauchy_return[THEN iffD2,of xi,
          OF  _  LPm.convergent_imp_MCauchy[OF _ h(2)[simplified xi(2)]]] xi
      by fastforce
    have 0:"\<nexists>x. limitin mtopology (xi \<circ> a) x sequentially" if a: "strict_mono a" for a :: "nat \<Rightarrow> nat"
      using MCauchy_convergent_subsequence[OF MCauchy_xi a] contr by blast
    have inf: "infinite (range xi)"
      by (metis 0 Bolzano_Weierstrass_property MCauchy_xi MCauchy_def finite_subset preorder_class.order.refl)
    have cl: "closedin mtopology (range (xi \<circ> a))" if a: "strict_mono a" for a :: "nat \<Rightarrow> nat"
      unfolding closedin_metric
    proof safe
      fix x
      assume x:"x \<in> M" "x \<notin> range (xi \<circ> a)"
      from 0 a have "\<not> limitin mtopology (xi \<circ> a) x sequentially"
        by blast
      then obtain e where e: "e > 0" "\<And>n0. \<exists>n\<ge>n0. d ((xi \<circ> a) n) x \<ge> e"
        using xi(1) x by(fastforce simp: limit_metric_sequentially)
      then obtain n0 where n0: "\<And>n m. n \<ge> n0 \<Longrightarrow> m \<ge> n0 \<Longrightarrow> d ((xi \<circ> a) n)  ((xi \<circ> a) m) < e / 2"
        using MCauchy_subsequence[OF a MCauchy_xi]
        by (meson MCauchy_def zero_less_divide_iff zero_less_numeral)
      obtain n1 where n1: "n1 \<ge> n0" "d ((xi \<circ> a) n1) x \<ge> e"
        using e(2) by blast
      define e' where "e' \<equiv> Min ((\<lambda>n. d x ((xi \<circ> a) n))` {..n0})"
      have e'_pos: "e' > 0"
        unfolding e'_def using x xi(1) by(subst  linorder_class.Min_gr_iff) auto
      have "d x ((xi \<circ> a) n) \<ge> min (e / 2) e'" for n
      proof(cases "n \<le> n0")
        assume "\<not> n \<le> n0"
        then have "d ((xi \<circ> a) n) ((xi \<circ> a) n1) < e / 2"
          using n1(1) n0 by simp
        hence "e / 2 \<le> d x ((xi \<circ> a) n1) - d ((xi \<circ> a) n) ((xi \<circ> a) n1)"
          using n1(2) by(simp add: commute)
        also have "... \<le> d x ((xi \<circ> a) n)"
          using triangle[OF x(1) xi(1)[of "a n"] xi(1)[of "a n1"]] by simp
        finally show ?thesis
          by simp
      qed(auto intro!: linorder_class.Min_le min.coboundedI2 simp: e'_def)
      thus "\<exists>r>0. disjnt (range (xi \<circ> a)) (mball x r)"
        using e'_pos e(1) x(1) xi(1)  linorder_not_less
        by(fastforce intro!: exI[where x="min (e / 2) e'"] simp: disjnt_def simp del: min_less_iff_conj)
    qed(use xi in auto)
    hence meas: "strict_mono a \<Longrightarrow> (range (xi \<circ> a)) \<in> sets (borel_of mtopology)" for a :: "nat \<Rightarrow> nat"
      by(auto simp: borel_of_closed)
    have 1:"measure N (range (xi \<circ> a)) = 1" if a: "strict_mono a" for a :: "nat \<Rightarrow> nat"
    proof -
      interpret mweak_conv_fin M d Ni N sequentially
        using limitin_topspace[OF h(2)] xi(1) by(auto intro!: inP_mweak_conv_fin simp: xi(2))
      have "mweak_conv_seq Ni N"
        using converge_imp_mweak_conv[OF h(2)] xi(2) by simp
      hence *: "closedin mtopology A \<Longrightarrow> limsup (\<lambda>n. ereal (measure (Ni n) A)) \<le> ereal (measure N A)" for A
        using mweak_conv_eq2 by blast
      have "ereal 1 \<le> limsup (\<lambda>n. ereal (measure (Ni n) (range (xi \<circ> a))))"
        using meas[OF a] seq_suble[OF a]
        by(auto simp: limsup_INF_SUP le_Inf_iff le_Sup_iff xi(2) measure_return indicator_def one_ereal_def)
      also have "... \<le> ereal (measure N (range (xi \<circ> a)))"
        by(intro * a cl)
      finally show ?thesis
        using N_r by(auto intro!: antisym)
    qed
    have 2:"measure N {xi n} = 0" for n
    proof -
      have "infinite {i. xi i \<noteq> xi n}"
      proof
        assume "finite {i. xi i \<noteq> xi n}"
        then have "finite (xi ` {i. xi i \<noteq> xi n})"
          by blast
        moreover have "(xi ` {i. xi i \<noteq> xi n}) = range xi - {xi n}"
          by auto
        ultimately show False
          using inf by auto
      qed
      from infinite_enumerate[OF this]
      obtain a :: "nat \<Rightarrow> nat" where r: "strict_mono a" "\<And>i. a i \<in> {i. xi i \<noteq> xi n}"
        by blast
      hence disj: "range (xi \<circ> a) \<inter> {xi n} = {}"
        by fastforce
      from N.finite_measure_Union[OF _ _ this]
      have "measure N (range (xi \<circ> a) \<union> {xi n}) = 1 + measure N {xi n}"
        using meas[OF r(1)] 1[OF r(1)] by simp
      thus ?thesis
        using N_r[of "range (xi \<circ> a) \<union> {xi n}"] measure_nonneg[of N "{xi n}"] by simp
    qed
    have "measure N (range xi) = 0"
    proof -
      have count: "countable (range xi)"
        by blast
      define Xn where "Xn \<equiv> (\<lambda>n. {from_nat_into (range xi) n})"
      have Un_Xn: "range xi = (\<Union>n. Xn n)"
        using bij_betw_from_nat_into[OF count inf] by (simp add: UNION_singleton_eq_range Xn_def)
      have disjXn: "disjoint_family Xn"
        using bij_betw_from_nat_into[OF count inf] by (simp add: inf disjoint_family_on_def Xn_def)
      have [measurable]: "\<And>n. Xn n \<in> sets N"
        using bij_betw_from_nat_into[OF count inf]
        by (metis UNIV_I Xn_def \<open>\<And>n. {xi n} \<in> sets N\<close> bij_betw_iff_bijections image_iff)
      have eq0: "\<And>n. measure N (Xn n) = 0"
        by (metis bij_betw_from_nat_into[OF count inf] 2 UNIV_I Xn_def bij_betw_imp_surj_on image_iff)
      have "measure N (range xi) = measure N (\<Union>n. Xn n)"
        by(simp add: Un_Xn)
      also have "... = (\<Sum>n. measure N (Xn n))"
        using N.suminf_measure[OF _ disjXn] by fastforce
      also have "... = 0"
        by(simp add: eq0)
      finally show ?thesis .
    qed
    with 1[OF strict_mono_id] show False by simp
  qed
  then obtain x where x: "limitin mtopology xi x sequentially"
    by blast
  show "N \<in> (\<lambda>x. return (borel_of mtopology) x) ` M"
    using limitin_topspace[OF x] by(simp add: LPm.limitin_metric_unique[OF h(2)[simplified xi(2)] conv_conv_return[OF x]])
qed simp

corollary separable_iff_LPm_separable: "separable_space mtopology \<longleftrightarrow> separable_space LPm.mtopology"
  using homeomorphic_space_second_countability[OF homeomorphic_space_mtopology_return] separable_LPm
  by(auto simp: separable_space_iff_second_countable LPm.separable_space_iff_second_countable second_countable_subtopology)

corollary LPmcomplete_mcomplete:
  assumes LPm.mcomplete
  shows mcomplete
  unfolding mcomplete_def
proof safe
  fix xn
  assume h: "MCauchy xn"
  hence 1: "range xn \<subseteq> M"
    using MCauchy_def by blast
  interpret Submetric \<P> LPm "(\<lambda>x. return (borel_of mtopology) x) ` M"
    by (metis LPm.Metric_space_axioms LPm.topspace_mtopology Submetric.intro Submetric_axioms.intro closedin_returnM closedin_subset)
  have "sub.mcomplete"
    using assms(1) closedin_eq_mcomplete closedin_returnM by blast
  moreover have "sub.MCauchy (\<lambda>n. return (borel_of mtopology) (xn n))"
    using MCauchy_iff_MCauchy_return[OF 1] 1 by (simp add: MCauchy_submetric h image_subset_iff)
  ultimately obtain x where
    x: "x \<in> M" "limitin LPm.mtopology (\<lambda>n. return (borel_of mtopology) (xn n))
                        (return (borel_of mtopology) x) sequentially"
    unfolding sub.mcomplete_def limitin_submetric_iff by blast
  thus "\<exists>x. limitin mtopology xn x sequentially"
    by(auto simp: conv_iff_conv_return[OF 1 x(1),symmetric])
qed

corollary mcomplete_iff_LPmcomplete: "separable_space mtopology \<Longrightarrow> mcomplete \<longleftrightarrow> LPm.mcomplete"
  by(auto simp add: mcomplete_LPmcomplete LPmcomplete_mcomplete)

lemma LPmcompact_imp_mcompact: "compact_space LPm.mtopology \<Longrightarrow> compact_space mtopology"
  by (meson closedin_compact_space closedin_returnM compact_space_subtopology homeomorphic_compact_space homeomorphic_space_mtopology_return)

end

corollary Polish_space_weak_conv_topology:
  assumes "Polish_space X"
  shows "Polish_space (weak_conv_topology X)"
proof -
  obtain d where d:"Metric_space (topspace X) d" "Metric_space.mcomplete (topspace X) d"
    "Metric_space.mtopology (topspace X) d = X"
    by (metis Metric_space.topspace_mtopology assms completely_metrizable_space_def Polish_space_imp_completely_metrizable_space)
  then interpret Levy_Prokhorov "topspace X" d
    by(auto simp: Levy_Prokhorov_def)
  have "separable_space mtopology"
    by (simp add: assms d(3) Polish_space_imp_separable_space)
  thus ?thesis
    using LPm.Polish_space_mtopology LPmtopology_eq_weak_conv_topology d(2) d(3) mcomplete_LPmcomplete separable_LPm by force
qed

subsection \<open> Prokhorov Theorem for Topology of Weak Convergence \<close>
lemma relatively_compact_imp_tight:
  assumes "Polish_space X" "\<Gamma> \<subseteq> {N. sets N = sets (borel_of X) \<and> finite_measure N}"
      and "compactin (weak_conv_topology X) (weak_conv_topology X closure_of \<Gamma>)"
    shows "tight_on_set X \<Gamma>"
proof -
  obtain d where d:"Metric_space (topspace X) d" "Metric_space.mcomplete (topspace X) d"
    "Metric_space.mtopology (topspace X) d = X"
    by (metis Metric_space.topspace_mtopology assms(1) completely_metrizable_space_def Polish_space_imp_completely_metrizable_space)
  note sep = Polish_space_imp_separable_space[OF assms(1)]
  hence sep':"separable_space (Metric_space.mtopology (topspace X) d)"
    by(simp add: d)
  interpret Levy_Prokhorov "topspace X" d
    by(auto simp: d Levy_Prokhorov_def)
  show ?thesis
    using relatively_compact_imp_tight_LP[of \<Gamma>] assms sep inP_iff
    by(fastforce simp add: d LPmtopology_eq_weak_conv_topology[OF sep'])
qed

lemma tight_imp_relatively_compact:
  assumes "metrizable_space X" "separable_space X"
    "\<Gamma> \<subseteq> {N. N (space N) \<le> ennreal r \<and> sets N = sets (borel_of X)}"
      and "tight_on_set X \<Gamma>"
    shows "compactin (weak_conv_topology X) (weak_conv_topology X closure_of \<Gamma>)"
proof -
  obtain d where d:"Metric_space (topspace X) d" "Metric_space.mtopology (topspace X) d = X"
    by (metis Metric_space.topspace_mtopology assms(1) metrizable_space_def)
  hence sep':"separable_space (Metric_space.mtopology (topspace X) d)"
    by(simp add: d assms)
  show ?thesis
  proof(cases "r \<le> 0")
    assume "r \<le> 0"
    then have "{N. N (space N) \<le> ennreal r \<and> sets N = sets (borel_of X)} = {null_measure (borel_of X)}"
      by(fastforce simp: ennreal_neg le_zero_eq[THEN iffD1,OF order.trans[OF emeasure_space]] intro!: measure_eqI)
    then have "\<Gamma> = {} \<or> \<Gamma> = {null_measure (borel_of X)}"
      using assms(3) by auto
    moreover have "weak_conv_topology X closure_of {null_measure (borel_of X)} = {null_measure (borel_of X)}"
      by(intro closure_of_eq[THEN iffD2] closedin_Hausdorff_singleton metrizable_imp_Hausdorff_space
          metrizable_space_subtopology metrizable_weak_conv_topology assms)
        (auto intro!: finite_measureI)
    ultimately show ?thesis
      by (auto intro!: finite_measureI)
  next
    assume "\<not> r \<le> 0"
    then interpret Levy_Prokhorov "topspace X" d
      by(auto simp: d Levy_Prokhorov_def)
    show ?thesis
      using tight_imp_relatively_compact_LP[of \<Gamma>] assms
      by(auto simp add: d LPmtopology_eq_weak_conv_topology[OF sep'])
  qed
qed

lemma Prokhorov:
  assumes "Polish_space X" "\<Gamma> \<subseteq> {N. N (space N) \<le> ennreal r \<and> sets N = sets (borel_of X)}"
  shows "tight_on_set X \<Gamma> \<longleftrightarrow> compactin (weak_conv_topology X) (weak_conv_topology X closure_of \<Gamma>)"
proof -
  have "\<Gamma> \<subseteq> {N. sets N = sets (borel_of X) \<and> finite_measure N}"
    using assms(2) by(auto intro!: finite_measureI simp: top.extremum_unique)
  thus ?thesis
    using relatively_compact_imp_tight tight_imp_relatively_compact assms
          Polish_space_imp_metrizable_space Polish_space_imp_separable_space
    by (metis (mono_tags, lifting))
qed

corollary tight_on_set_imp_convergent_subsequence:
  fixes Ni :: "nat \<Rightarrow> _ measure"
  assumes "metrizable_space X" "separable_space X"
    and "tight_on_set X (range Ni)" "\<And>i. (Ni i) (space (Ni i)) \<le> ennreal r"
  shows "\<exists>a N. strict_mono a \<and> finite_measure N \<and> sets N = sets (borel_of X)
               \<and> N (space N) \<le> ennreal r \<and> weak_conv_on (Ni \<circ> a) N sequentially X"
proof(cases "r \<le> 0")
  case True
  then have "Ni = (\<lambda>i. null_measure (borel_of X))"
    using assms(3)  order.trans[OF emeasure_space assms(4)]
    by(auto simp: tight_on_set_def ennreal_neg intro!: measure_eqI)
  thus?thesis
    using weak_conv_on_const[of Ni]
    by(auto intro!: exI[where x=id] exI[where x="null_measure (borel_of X)"] strict_mono_id finite_measureI)
next
  case False
  then have r[arith]:"r > 0" by linarith
  obtain d where d: "Metric_space (topspace X) d" "Metric_space.mtopology (topspace X) d = X"
    by (metis Metric_space.topspace_mtopology assms(1) metrizable_space_def)
  then interpret d: Metric_space "topspace X" d
    by blast
  interpret Levy_Prokhorov "topspace X" d
    by(auto simp: Levy_Prokhorov_def d )
  have range_Ni: "range Ni \<subseteq> {N. N (space N) \<le> ennreal r \<and> sets N = sets (borel_of X)}"
    using assms(3,4) by(auto simp: tight_on_set_def)
  hence Ni_fin: "\<And>i. finite_measure (Ni i)"
    by (meson assms(3) range_eqI tight_on_set_def)  
  have range_Ni':"LPm.mtopology closure_of range Ni
                  \<subseteq> {N. N (space N) \<le> ennreal r \<and> sets N = sets (borel_of X)}"
    by (metis (no_types, lifting) Collect_cong closedin_bounded_measures closure_of_minimal d(2) range_Ni)
  have "compactin LPm.mtopology (LPm.mtopology closure_of (range Ni))"
    using assms(2,3) range_Ni by(auto intro!: tight_imp_relatively_compact_LP simp: d(2))
  from LPm.compactin_sequentially[THEN iffD1,OF this] range_Ni
  obtain a N where "N \<in> LPm.mtopology closure_of range Ni" "strict_mono a"
    "limitin LPm.mtopology (Ni \<circ> a) N sequentially"
    by (metis (no_types, lifting) LPm.topspace_mtopology assms(3) closure_of_subset d(2) inP_I subsetI tight_on_set_def)
  moreover hence "finite_measure N" "sets N = sets (borel_of X)" "N (space N) \<le> ennreal r"
    using range_Ni' by (auto simp add: LPm.limitin_metric inP_iff)
  ultimately show ?thesis
    using range_Ni Ni_fin assms(4)
    by(fastforce intro!: converge_imp_mweak_conv[simplified d] exI[where x=a] exI[where x=N] inP_I
                   simp: image_subset_iff d(2))
qed

end