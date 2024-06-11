(*  Title:   Space_of_Finite_Measures.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

theory Space_of_Finite_Measures
  imports Prokhorov_Theorem
begin

section \<open> Measurable Space of Finite Measures \<close>
subsection \<open> Measurable Space of Finite Measures \<close>
text \<open> We define the measurable space of all finite measures in the same way as @{term subprob_algebra}.\<close>
definition finite_measure_algebra :: "'a measure \<Rightarrow> 'a measure measure" where
  "finite_measure_algebra K =
    (SUP A \<in> sets K. vimage_algebra {M. finite_measure M \<and> sets M = sets K} (\<lambda>M. emeasure M A) borel)"

lemma space_finite_measure_algebra:
  "space (finite_measure_algebra A) = {M. finite_measure M \<and> sets M = sets A}"
  by (auto simp add:finite_measure_algebra_def space_Sup_eq_UN)

lemma finite_measure_algebra_cong: "sets M = sets N \<Longrightarrow> finite_measure_algebra M = finite_measure_algebra N"
  by (simp add: finite_measure_algebra_def)

lemma measurable_emeasure_finite_measure_algebra[measurable]:
  "a \<in> sets A \<Longrightarrow> (\<lambda>M. emeasure M a) \<in> borel_measurable (finite_measure_algebra A)"
  by (auto intro!: measurable_Sup1 measurable_vimage_algebra1 simp: finite_measure_algebra_def)

lemma measurable_measure_finite_measure_algebra[measurable]:
  "a \<in> sets A \<Longrightarrow> (\<lambda>M. measure M a) \<in> borel_measurable (finite_measure_algebra A)"
  unfolding measure_def by measurable

lemma finite_measure_measurableD:
  assumes N: "N \<in> measurable M (finite_measure_algebra S)" and x: "x \<in> space M"
  shows "space (N x) = space S"
    and "sets (N x) = sets S"
    and "measurable (N x) K = measurable S K"
    and "measurable K (N x) = measurable K S"
  using measurable_space[OF N x]
  by (auto simp: space_finite_measure_algebra intro!: measurable_cong_sets dest: sets_eq_imp_space_eq)

ML \<open>

fun finite_measure_cong thm ctxt = (
  let
    val thm' = Thm.transfer' ctxt thm
    val free = thm' |> Thm.concl_of |> HOLogic.dest_Trueprop |> dest_comb |> fst |>
      dest_comb |> snd |> strip_abs_body |> head_of |> is_Free
  in
    if free then ([], Measurable.add_local_cong (thm' RS @{thm finite_measure_measurableD(2)}) ctxt)
            else ([], ctxt)
  end
  handle THM _ => ([], ctxt) | TERM _ => ([], ctxt))

\<close>

setup \<open>
  Context.theory_map (Measurable.add_preprocessor "finite_measure_cong" subprob_cong)
\<close>

context
  fixes K M N assumes K: "K \<in> measurable M (finite_measure_algebra N)"
begin

lemma finite_measure_space_kernel: "a \<in> space M \<Longrightarrow> finite_measure (K a)"
  using measurable_space[OF K] by (simp add: space_finite_measure_algebra)

lemma sets_finite_kernel: "a \<in> space M \<Longrightarrow> sets (K a) = sets N"
  using measurable_space[OF K] by (simp add: space_finite_measure_algebra)

lemma measurable_emeasure_finite_kernel[measurable]:
    "A \<in> sets N \<Longrightarrow> (\<lambda>a. emeasure (K a) A) \<in> borel_measurable M"
  using measurable_compose[OF K measurable_emeasure_finite_measure_algebra] .

end

lemma measurable_finite_measure_algebra:
  "(\<And>a. a \<in> space M \<Longrightarrow> finite_measure (K a)) \<Longrightarrow>
  (\<And>a. a \<in> space M \<Longrightarrow> sets (K a) = sets N) \<Longrightarrow>
  (\<And>A. A \<in> sets N \<Longrightarrow> (\<lambda>a. emeasure (K a) A) \<in> borel_measurable M) \<Longrightarrow>
  K \<in> measurable M (finite_measure_algebra N)"
  by (auto intro!: measurable_Sup2 measurable_vimage_algebra2 simp: finite_measure_algebra_def)

lemma measurable_finite_markov:
  "K \<in> measurable M (finite_measure_algebra M) \<longleftrightarrow>
    (\<forall>x\<in>space M. finite_measure (K x) \<and> sets (K x) = sets M) \<and>
    (\<forall>A\<in>sets M. (\<lambda>x. emeasure (K x) A) \<in> measurable M borel)"
proof
  assume "(\<forall>x\<in>space M. finite_measure (K x) \<and> sets (K x) = sets M) \<and>
    (\<forall>A\<in>sets M. (\<lambda>x. emeasure (K x) A) \<in> borel_measurable M)"
  then show "K \<in> measurable M (finite_measure_algebra M)"
    by (intro measurable_finite_measure_algebra) auto
next
  assume "K \<in> measurable M (finite_measure_algebra M)"
  then show "(\<forall>x\<in>space M. finite_measure (K x) \<and> sets (K x) = sets M) \<and>
    (\<forall>A\<in>sets M. (\<lambda>x. emeasure (K x) A) \<in> borel_measurable M)"
    by (auto dest: finite_measure_space_kernel sets_finite_kernel)
qed

lemma measurable_finite_measure_algebra_generated:
  assumes eq: "sets N = sigma_sets \<Omega> G" and "Int_stable G" "G \<subseteq> Pow \<Omega>"
  assumes subsp: "\<And>a. a \<in> space M \<Longrightarrow> finite_measure (K a)"
  assumes sets: "\<And>a. a \<in> space M \<Longrightarrow> sets (K a) = sets N"
  assumes "\<And>A. A \<in> G \<Longrightarrow> (\<lambda>a. emeasure (K a) A) \<in> borel_measurable M"
  assumes \<Omega>: "(\<lambda>a. emeasure (K a) \<Omega>) \<in> borel_measurable M"
  shows "K \<in> measurable M (finite_measure_algebra N)"
proof (rule measurable_finite_measure_algebra)
  fix a assume "a \<in> space M" then show "finite_measure (K a)" "sets (K a) = sets N" by fact+
next
  interpret G: sigma_algebra \<Omega> "sigma_sets \<Omega> G"
    using \<open>G \<subseteq> Pow \<Omega>\<close> by (rule sigma_algebra_sigma_sets)
  fix A assume "A \<in> sets N" with assms(2,3) show "(\<lambda>a. emeasure (K a) A) \<in> borel_measurable M"
    unfolding \<open>sets N = sigma_sets \<Omega> G\<close>
  proof (induction rule: sigma_sets_induct_disjoint)
    case (basic A) then show ?case by fact
  next
    case empty then show ?case by simp
  next
    case (compl A)
    have "(\<lambda>a. emeasure (K a) (\<Omega> - A)) \<in> borel_measurable M \<longleftrightarrow>
      (\<lambda>a. emeasure (K a) \<Omega> - emeasure (K a) A) \<in> borel_measurable M"
      using G.top G.sets_into_space sets eq compl finite_measure.emeasure_finite[OF subsp]
      by (intro measurable_cong emeasure_Diff) auto
    with compl \<Omega> show ?case
      by simp
  next
    case (union F)
    moreover have "(\<lambda>a. emeasure (K a) (\<Union>i. F i)) \<in> borel_measurable M \<longleftrightarrow>
        (\<lambda>a. \<Sum>i. emeasure (K a) (F i)) \<in> borel_measurable M"
      using sets union eq
      by (intro measurable_cong suminf_emeasure[symmetric]) auto
    ultimately show ?case
      by auto
  qed
qed

lemma space_finite_measure_algebra_empty: "space N = {} \<Longrightarrow> space (finite_measure_algebra N) = {null_measure N}"
  by(fastforce simp: space_finite_measure_algebra space_empty_iff intro!: measure_eqI finite_measureI)

lemma sets_subprob_algebra_restrict:
  "sets (subprob_algebra M) = sets (restrict_space (finite_measure_algebra M) {N. subprob_space N})"
  (is "sets ?L = sets ?R")
proof -
  have 1:"id \<in> measurable ?L ?R"
    using sets.sets_into_space[of _ M]
    by(auto intro!: measurable_restrict_space2 Int_stableI
                    measurable_finite_measure_algebra_generated[where \<Omega>="space M" and G="sets M"]
              simp: space_subprob_algebra subprob_space_def sets.sigma_sets_eq)
  have 2:"id \<in> measurable ?R ?L"
    using sets.sets_into_space[of _ M]
    by(auto intro!: measurable_subprob_algebra_generated[where \<Omega>="space M" and G="sets M"] Int_stableI
        simp: sets.sigma_sets_eq space_restrict_space space_finite_measure_algebra measurable_restrict_space1)
  have 3: "space ?L = space ?R"
    by(auto simp: space_restrict_space space_subprob_algebra space_finite_measure_algebra subprob_space_def)
  have [simp]:"\<And>A. A \<in> sets ?L \<Longrightarrow> A \<inter> space ?R = A" "\<And>A. A \<in> sets ?R \<Longrightarrow> A \<inter> space ?L = A"
    using 3 sets.sets_into_space by auto
  show ?thesis
    using measurable_sets[OF 1] measurable_sets[OF 2] by auto
qed

subsection \<open> Equivalence between Spaces of Finite Measures \<close>
text \<open>Corollary 17.21~\cite{descriptiveset}.\<close>
lemma(in Levy_Prokhorov) openin_lower_semicontinuous:
  assumes "openin mtopology U"
  shows "lower_semicontinuous_map LPm.mtopology (\<lambda>N. measure N U)"
  unfolding lower_semicontinuous_map_liminf_real[OF LPm.first_countable_mtopology]
proof safe
  fix Ni N
  assume h:"limitin LPm.mtopology Ni N sequentially"
  then obtain K where K: "\<And>n. n \<ge> K \<Longrightarrow> Ni n \<in> \<P>"
    by(simp add: mtopology_of_def LPm.limit_metric_sequentially)
      (meson LPm.mbounded_alt_pos LPm.mbounded_empty)
  have h': "limitin LPm.mtopology (\<lambda>n. Ni (n + K)) N sequentially"
    by (simp add: h limitin_sequentially_offset)
  interpret mweak_conv_fin M d "\<lambda>n. Ni (n + K)" N sequentially
    using K h by(auto intro!: inP_mweak_conv_fin simp: mtopology_of_def dest: LPm.limitin_mspace)
  have "mweak_conv_seq (\<lambda>n. Ni (n + K)) N"
    using K LPm.Self_def converge_imp_mweak_conv h' by auto
  hence "ereal (measure N U) \<le> liminf (\<lambda>x. ereal (measure (Ni (x + K)) U))"
    using assms by(simp add: mweak_conv_eq3) 
  thus "ereal (measure N U) \<le> liminf (\<lambda>x. ereal (measure (Ni x) U))"
    unfolding liminf_shift_k[of "\<lambda>x. ereal (measure (Ni x) U)" K] .
qed

lemma(in Levy_Prokhorov) closedin_upper_semicontinuous:
  assumes "closedin mtopology A"
  shows "upper_semicontinuous_map LPm.mtopology (\<lambda>N. measure N A)"
  unfolding upper_semicontinuous_map_limsup_real[OF LPm.first_countable_mtopology]
proof safe
  fix Ni N
  assume h:"limitin LPm.mtopology Ni N sequentially"
  then obtain K where K: "\<And>n. n \<ge> K \<Longrightarrow> Ni n \<in> \<P>"
    by(simp add: mtopology_of_def LPm.limit_metric_sequentially)
      (meson LPm.mbounded_alt_pos LPm.mbounded_empty)
  have h': "limitin LPm.mtopology (\<lambda>n. Ni (n + K)) N sequentially"
    by (simp add: h limitin_sequentially_offset)
  interpret mweak_conv_fin M d "\<lambda>n. Ni (n + K)" N sequentially
    using K h by(auto intro!: inP_mweak_conv_fin simp: mtopology_of_def dest: LPm.limitin_mspace)
  have "mweak_conv_seq (\<lambda>n. Ni (n + K)) N"
    using K LPm.Self_def converge_imp_mweak_conv h' by auto
  hence "limsup (\<lambda>x. ereal (measure (Ni (x + K)) A)) \<le> ereal (measure N A)"
    using assms by(auto simp: mweak_conv_eq2)
  thus "limsup (\<lambda>x. ereal (measure (Ni x) A)) \<le> ereal (measure N A)"
    unfolding limsup_shift_k[of "\<lambda>x. ereal (measure (Ni x) A)" K] .
qed

context Levy_Prokhorov
begin

text \<open> We show that the measurable space generated from @{term LPm.mtopology} is equal to
       @{term \<open>finite_measure_algebra (borel_of LPm.mtopology)\<close>}.\<close>
lemma sets_LPm1: "sets (finite_measure_algebra (borel_of mtopology))
                  \<subseteq> sets (borel_of LPm.mtopology)" (is "sets ?Giry \<subseteq> sets ?Levy")
proof safe
  have space_eq: "space ?Levy = space ?Giry"
    by(simp add: space_finite_measure_algebra space_borel_of) (auto simp add: \<P>_def)
  have 1:"\<And>A. openin mtopology A \<Longrightarrow> (\<lambda>N. measure N A) \<in> borel_measurable ?Levy"
    by(auto intro!: lower_semicontinuous_map_measurable openin_lower_semicontinuous)
  have m:"id \<in> ?Levy \<rightarrow>\<^sub>M ?Giry"
  proof(rule measurable_finite_measure_algebra_generated[where \<Omega>=M and G="{U. openin mtopology U}"])
    show "sets (borel_of mtopology) = sigma_sets M {U. openin mtopology U}"
      using sets_borel_of[of mtopology] by simp
  next
    show "Int_stable {U. openin mtopology U}"
      by(auto intro!: Int_stableI)
  next
    show "{U. openin mtopology U} \<subseteq> Pow M"
      using openin_subset[of mtopology] by auto
  next
    show "\<And>a. a \<in> space (borel_of LPm.mtopology) \<Longrightarrow> finite_measure (id a)"
      by(simp add: space_borel_of) (simp add: \<P>_def)
  next
    show "\<And>a. a \<in> space (borel_of LPm.mtopology) \<Longrightarrow> sets (id a) = sets (borel_of mtopology)"
      by(simp add: space_borel_of) (simp add: \<P>_def)
  next
    fix A
    assume "A \<in> {U. openin mtopology U}"
    then have "(\<lambda>N. measure (id N) A) \<in> borel_measurable (borel_of LPm.mtopology)"
      by(simp add: 1)
    then have 1:"(\<lambda>N. ennreal (measure (id N) A)) \<in> borel_measurable (borel_of LPm.mtopology)"
      by simp
    have 2:"\<And>N. N \<in> space (borel_of LPm.mtopology) \<Longrightarrow> ennreal (measure (id N) A) = emeasure (id N) A"
      unfolding measure_def
      by(rule ennreal_enn2real)
        (simp add: finite_measure.emeasure_eq_measure space_eq space_finite_measure_algebra)
    show "(\<lambda>N. emeasure (id N) A) \<in> borel_measurable (borel_of LPm.mtopology)"
      using 1 measurable_cong[THEN iffD1,OF 2 1] by auto
  next
    have "openin mtopology M"
      by simp
    then have "(\<lambda>N. measure (id N) M) \<in> borel_measurable (borel_of LPm.mtopology)"
      by(simp add: 1)
    then have 1:"(\<lambda>N. ennreal (measure (id N) M)) \<in> borel_measurable (borel_of LPm.mtopology)"
      by simp
    have 2:"\<And>N. N \<in> space (borel_of LPm.mtopology) \<Longrightarrow> ennreal (measure (id N) M) = emeasure (id N) M"
      unfolding measure_def by(rule ennreal_enn2real)
        (simp add: finite_measure.emeasure_eq_measure space_eq space_finite_measure_algebra)
    show "(\<lambda>N. emeasure (id N) M) \<in> borel_measurable (borel_of LPm.mtopology)"
      using 1 measurable_cong[THEN iffD1,OF 2 1] by auto
  qed

  fix A
  assume A:"A \<in> sets ?Giry"
  from measurable_sets[OF m this] have "A \<inter> space ?Levy \<in> sets ?Levy"
    by simp
  moreover have "A \<inter> space ?Levy = A"
    by (simp add: A space_eq)
  ultimately show "A \<in> sets ?Levy"
    by simp
qed

lemma sets_LPm2:
  assumes mcomplete "separable_space mtopology"
  shows "sets (borel_of LPm.mtopology) \<subseteq> sets (finite_measure_algebra (borel_of mtopology))"
    (is "sets ?Levy \<subseteq> sets ?Giry")
proof -
  obtain \<O> where base: "countable \<O>" "base_in mtopology \<O>"
    using assms(2) second_countable_base_in separable_space_imp_second_countable by blast
  define funion_of_base where "funion_of_base \<equiv> \<Union> ` {U. finite U \<and> U \<subseteq> \<O>}"
  have funion_of_base_ne: "funion_of_base \<noteq> {}"
    by(auto simp: funion_of_base_def)
  have open_funion_of_base: "\<And>A. A \<in> funion_of_base \<Longrightarrow> openin mtopology A"
    using base_in_openin[OF base(2)] by(auto simp: funion_of_base_def )
  hence meas_funion_of_base[measurable]: "\<And>A. A \<in> funion_of_base \<Longrightarrow> A \<in> sets (borel_of mtopology)"
    by(auto simp: borel_of_open)
  have countable_funion_of_base: "countable funion_of_base"
    using countable_Collect_finite_subset[OF base(1)] by(auto simp: funion_of_base_def)

  have "sets ?Levy = sigma_sets \<P> {LPm.mball a \<epsilon> |a \<epsilon>. a \<in> \<P> \<and> 0 < \<epsilon>}"
    by(auto simp: borel_of_second_countable'[OF separable_LPm[OF assms(2),
                   simplified LPm.separable_space_iff_second_countable]
                  base_is_subbase[OF LPm.mtopology_base_in_balls]] intro!: sets_measure_of)
  also have "... = sigma_sets \<P> {LPm.mcball a \<epsilon> |a \<epsilon>. a \<in> \<P> \<and> 0 \<le> \<epsilon>}"
  proof(safe intro!: sigma_sets_eqI)
    fix L and e :: real
    assume h:"L \<in> \<P>" and "0 < e"
    have "LPm.mball L e = (\<Union>n. LPm.mcball L (e - 1 / (Suc n)))"
    proof safe
      fix N
      assume N: "N \<in> LPm.mball L e"
      then obtain n where "1 / Suc n < e - LPm L N"
        by (meson LPm.in_mball diff_gt_0_iff_gt nat_approx_posE)
      thus "N \<in> (\<Union>n. LPm.mcball L (e - 1 / real (Suc n)))"
        using N by(auto intro!: exI[where x=n] simp: LPm.mcball_def)
    next
      fix N n
      assume N: "N \<in> LPm.mcball L (e - 1 / (Suc n))"
      with order.strict_trans1[of "LPm L N" "e - 1 / (Suc n)" e]
      show "N \<in> LPm.mball L e"
        by auto
    qed
    also have "... \<in> sigma_sets \<P> {LPm.mcball a \<epsilon> |a \<epsilon>. a \<in> \<P> \<and> 0 \<le> \<epsilon>}"
    proof(rule Union)
      fix n
      consider "e - 1 / real (Suc n) < 0" | "0 \<le> e - 1 / real (Suc n)" by fastforce
      then show "LPm.mcball L (e - 1 / real (Suc n)) \<in> sigma_sets \<P> {LPm.mcball a \<epsilon> |a \<epsilon>. a \<in> \<P> \<and> 0 \<le> \<epsilon>}"
      proof cases
        case 2
        then show ?thesis
          using h by fast
      qed(use LPm.mcball_eq_empty[of _ "e - 1 / real (Suc n)"] sigma_sets.Empty in auto)
    qed
    finally show "LPm.mball L e \<in> sigma_sets \<P> {LPm.mcball a \<epsilon> |a \<epsilon>. a \<in> \<P> \<and> 0 \<le> \<epsilon>}" .
  next
    fix L and e :: real
    assume h:"L \<in> \<P>" "0 \<le> e"
    have "LPm.mcball L e = (\<Inter>n. LPm.mball L (e + 1 / Suc n))"
    proof safe
      fix N n
      assume "N \<in> LPm.mcball L e"
      with order.strict_trans1[of "LPm L N" e "e + 1 / (Suc n)"]
      show "N \<in> LPm.mball L (e + 1 / (Suc n))"
        by auto
    next
      fix N
      assume hn:"N \<in> (\<Inter>n. LPm.mball L (e + 1 / real (Suc n)))"
      then have N:"N \<in> \<P>"
        by auto
      show "N \<in> LPm.mcball L e"
      proof -
        have "LPm L N \<le> e"
        proof(rule field_le_epsilon)
          fix l :: real
          assume "l > 0"
          then obtain n where "1 / (1 + real n) < l"
            using nat_approx_posE by auto
          with hn show "LPm L N \<le> e + l"
            by(auto intro!: order.trans[of "LPm L N" "e + 1 / (1 + real n)" "e + l",OF less_imp_le])
        qed
        thus ?thesis
          using hn by auto
      qed
    qed
    also have "... \<in> sigma_sets \<P> {LPm.mball a \<epsilon> |a \<epsilon>. a \<in> \<P> \<and> 0 < \<epsilon>}"
    proof(rule sigma_sets_Inter)
      fix n
      show "LPm.mball L (e + 1 / real (Suc n)) \<in> sigma_sets \<P> {LPm.mball a \<epsilon> |a \<epsilon>. a \<in> \<P> \<and> 0 < \<epsilon>}"
        using h by(auto intro!: exI[where x=L] exI[where x="e + 1 / (1 + real n)"] add_nonneg_pos)
    qed auto
    finally show "LPm.mcball L e \<in> sigma_sets \<P> {LPm.mball a \<epsilon> |a \<epsilon>. a \<in> \<P> \<and> 0 < \<epsilon>}" .
  qed
  also have "... = sigma_sets (space ?Giry) {LPm.mcball a \<epsilon> |a \<epsilon>. a \<in> \<P> \<and> 0 \<le> \<epsilon>}"
    unfolding space_finite_measure_algebra \<P>_def by meson
  also have "... \<subseteq> sets ?Giry"
  proof(rule sigma_sets_le_sets_iff[THEN iffD2])
    show "{LPm.mcball a \<epsilon> |a \<epsilon>. a \<in> \<P> \<and> 0 \<le> \<epsilon>} \<subseteq> sets ?Giry"
    proof safe
      fix L and e :: real
      assume L:"L \<in> \<P>" and e:"0 \<le> e"
      then have sets_L: "sets (borel_of mtopology) = sets L" and "finite_measure L"
        by(auto simp: inP_D)
      interpret L: finite_measure L by fact
      have "LPm.mcball L e
       = (\<Inter>A\<in>funion_of_base.
           (\<Inter>n. (\<lambda>N. measure N A) -`
                  {..measure L (\<Union>a\<in>A. mball a (e + 1 / (1 + real n))) + (e + 1 / (1 + real n))} \<inter> \<P>)
         \<inter> (\<Inter>n. (\<lambda>N. measure N
                 (\<Union>a\<in>A. mball a (e + 1 / (1 + real n)))) -` {measure L A - (e + 1 / (1 + real n))..} \<inter> \<P>))"
        (is "_ = ?rhs")
        unfolding set_eq_iff
      proof(intro allI iffI)
        fix N
        assume N: "N \<in> LPm.mcball L e"
        have sets_N: "sets (borel_of mtopology) = sets N" and "finite_measure N"
          using N by simp_all (auto simp: inP_D)
        then interpret N: finite_measure N by simp
        show "N \<in>?rhs"
        proof safe
          fix A n
          assume [measurable]:"A \<in> funion_of_base"
          have "LPm L N < e + 1 / (1 + real n)"
            by(rule order.strict_trans1[of "LPm L N" e "e + 1 / (1 + real n)"]) (use N in auto)
          thus "N \<in> (\<lambda>N. measure N A) -` {..measure L (\<Union>a\<in>A. mball a (e + 1 / (1 + real n))) + (e + 1 / (1 + real n))}"
               "N \<in> (\<lambda>N. measure N (\<Union>a\<in>A. mball a (e + 1 / (1 + real n)))) -` {measure L A - (e + 1 / (1 + real n))..}"
            using LPm_less_then[of L N "e + 1 / (1 + real n)" A] N L by auto
        qed(use N in auto)
      next
        fix N
        assume "N \<in> ?rhs"
        then have N: "N \<in> \<P>"
          "\<And>A n. A \<in> funion_of_base
         \<Longrightarrow> measure N A \<le> measure L (\<Union>a\<in>A. mball a (e + 1 / (1 + real n))) + (e + 1 / (1 + real n))"
          "\<And>A n. A \<in> funion_of_base
         \<Longrightarrow> measure L A \<le> measure N (\<Union>a\<in>A. mball a (e + 1 / (1 + real n))) + (e + 1 / (1 + real n))"
          using funion_of_base_ne by (auto simp: diff_le_eq)
        then have sets_N: "sets (borel_of mtopology) = sets N"
          by(auto simp: inP_D)
        interpret N: finite_measure N
          using N by(auto simp: inP_D)
        have [measurable]: "\<And>A e. (\<Union>a\<in>A. mball a e) \<in> sets N" "\<And>A e. (\<Union>a\<in>A. mball a e) \<in> sets L"
          by(auto simp: sets_L[symmetric] sets_N[symmetric])
        have ne: "{e. e > 0 \<and> (\<forall>A\<in>{U. openin mtopology U}.
                                   measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                                   measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)} \<noteq> {}"
          using LPm_ne'[OF L.finite_measure_axioms N.finite_measure_axioms] by fastforce
        have "(\<Sqinter> {e. e > 0 \<and> (\<forall>A\<in>{U. openin mtopology U}.
                                  measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                                  measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)}) \<le> e"
        proof(safe intro!: cInf_le_iff_less[where f=id,simplified,THEN iffD2,OF ne])
          fix y
          assume y:"e < y"
          then obtain n where "1 / Suc n < y - e"
            by (meson diff_gt_0_iff_gt nat_approx_posE)
          hence n: "e + 1 / (1 + real n) < y" by simp
          show "\<exists>i\<in>{e. 0 < e \<and> (\<forall>A\<in>{U. openin mtopology U}.
                                   measure L A \<le> measure N (\<Union>a\<in>A. mball a e) + e \<and>
                                   measure N A \<le> measure L (\<Union>a\<in>A. mball a e) + e)}. i \<le> y"
          proof(safe intro!: bexI[where x="e + 1 / (1 + real n)"])
            fix A
            assume A: "openin mtopology A"
            then have A'[measurable]: "A \<in> sets L"  "A \<in> sets N"
              by(auto simp: borel_of_open sets_N[symmetric] sets_L[symmetric])
            have "measure L A = \<Squnion> (measure L ` {K. compactin mtopology K \<and> K \<subseteq> A})"
              by(auto intro!: L.inner_regular_Polish[OF Polish_space_mtopology[OF assms] sets_L])
            also have "... \<le> \<Squnion> (measure L ` {U. U \<in>funion_of_base \<and> U \<subseteq> A})"
            proof(safe intro!: cSup_mono bdd_aboveI[where M="measure L (space L)"] L.bounded_measure)
              fix K
              assume K:"compactin mtopology K" "K \<subseteq> A"
              obtain \<U> where Aun: "A = \<Union> \<U>" "\<U> \<subseteq> \<O>"
                using A base by(auto simp: base_in_def)
              obtain \<F> where F: "finite \<F>" "\<F> \<subseteq> \<U>" "K \<subseteq> \<Union> \<F>"
                using compactinD[OF K(1),of "\<U>"] Aun K base_in_openin[OF base(2)] by blast
              hence Ffunion: "\<Union> \<F> \<in> funion_of_base" "\<Union> \<F> \<subseteq> A"
                using F Aun K by (auto simp: funion_of_base_def)
              with F(3) show "\<exists>a\<in>measure L ` {U \<in> funion_of_base. U \<subseteq> A}. measure L K \<le> a"
                by(auto intro!: exI[where x="\<Union> \<F>"] L.finite_measure_mono meas_funion_of_base[simplified sets_L])
            qed auto
            also have "... \<le> \<Squnion> {measure N (\<Union>a\<in>U. mball a (e + 1 / (1 + real n)))+(e+1 / (1+real n))
                                  | U. U \<in> funion_of_base \<and> U \<subseteq> A}"
              by(force intro!: cSup_mono N bdd_aboveI[where M="measure N (space N)+(e + 1/(1+real n))"] 
                              N.bounded_measure simp: funion_of_base_def)
            also have "... \<le> measure N (\<Union>a\<in>A. mball a (e + 1 / (1 + real n))) + (e + 1 / (1 + real n))"
              by(fastforce intro!:
                  cSup_le_iff[THEN iffD2] bdd_aboveI[where M="measure N (space N) +  (e + 1 / (1 + real n))"]
                  N.bounded_measure N.finite_measure_mono
                  simp: funion_of_base_def) 
            finally show "measure L A
                          \<le> measure N (\<Union>a\<in>A. mball a (e + 1 / (1 + real n))) + (e + 1 / (1 + real n))" .
            have "measure N A = \<Squnion> (measure N ` {K. compactin mtopology K \<and> K \<subseteq> A})"
              by(auto intro!: N.inner_regular_Polish[OF Polish_space_mtopology sets_N] assms)
            also have "... \<le> \<Squnion> (measure N ` {U. U \<in> funion_of_base \<and> U \<subseteq> A})"
            proof(safe intro!: cSup_mono bdd_aboveI[where M="measure N (space N)"] N.bounded_measure)
              fix K
              assume K:"compactin mtopology K" "K \<subseteq> A"
              obtain \<U> where Aun: "A = \<Union> \<U>" "\<U> \<subseteq> \<O>"
                using A base by(auto simp: base_in_def)
              obtain \<F> where F: "finite \<F>" "\<F> \<subseteq> \<U>" "K \<subseteq> \<Union> \<F>"
                using compactinD[OF K(1),of "\<U>"] Aun K base_in_openin[OF base(2)] by blast
              hence Ffunion: "\<Union> \<F> \<in> funion_of_base" "\<Union> \<F> \<subseteq> A"
                using F Aun K by (auto simp: funion_of_base_def)
              with F(3) show "\<exists>y\<in> measure N ` {U \<in> funion_of_base. U \<subseteq> A}. measure N K \<le> y"
                by(auto intro!: exI[where x="\<Union> \<F>"] N.finite_measure_mono meas_funion_of_base[simplified sets_N])
            qed auto
            also have "... \<le> \<Squnion> {measure L (\<Union>a\<in>U. mball a (e + 1 / (1 + real n))) + (e + 1 / (1 + real n))
                                 | U. U \<in> funion_of_base \<and> U \<subseteq> A}"
              by(force intro!: cSup_mono N bdd_aboveI[where M="measure L (space L) +  (e + 1 / (1 + real n))"]
                               L.bounded_measure simp: funion_of_base_def)
            also have "... \<le> measure L (\<Union>a\<in>A. mball a (e + 1 / (1 + real n))) + (e + 1 / (1 + real n))"
              by(fastforce intro!:
                  cSup_le_iff[THEN iffD2] bdd_aboveI[where M="measure L (space L) +  (e + 1 / (1 + real n))"]
                  L.bounded_measure L.finite_measure_mono
                  simp: funion_of_base_def)
            finally show "measure N A \<le> measure L (\<Union>a\<in>A. mball a (e + 1 / (1 + real n))) + (e + 1 / (1 + real n))" .
          qed(insert e n, auto intro!: add_nonneg_pos)
        qed(fastforce intro!: bdd_belowI[where m=0])
        thus "N \<in> LPm.mcball L e"
          using N(1) L by(auto simp: LPm_open)
      qed
      also have "... \<in> sets ?Giry"
      proof -
        have h:"(\<lambda>N. measure N A) -`
                  {..measure L (\<Union>a\<in>A. mball a (e + 1 / (1 + real n))) + (e + 1 / (1 + real n))} \<inter> \<P>
                \<in> sets ?Giry" (is ?m1)
               "(\<lambda>N. measure N
                 (\<Union>a\<in>A. mball a (e + 1 / (1 + real n)))) -` {measure L A - (e + 1 / (1 + real n))..} \<inter> \<P>
                \<in> sets ?Giry" (is ?m2) if "A\<in>funion_of_base" for A n
        proof -
          have P:"\<P> = space ?Giry" unfolding \<P>_def space_finite_measure_algebra by auto
          have [measurable]:"A \<in> sets (borel_of mtopology)"
            "(\<Union>a\<in>A. mball a (e + 1 / (1 + real n))) \<in> sets (borel_of mtopology)"
            using that by simp (auto intro!: borel_of_open)
          show ?m1 ?m2
            by(auto intro!: measurable_sets simp: P)
        qed
        show ?thesis
          by(rule sets.countable_INT'[OF countable_funion_of_base funion_of_base_ne]) (use h in blast)
      qed
      finally show "LPm.mcball L e \<in> sets ?Giry" .
    qed
  qed
  finally show ?thesis .
qed

corollary sets_LPm_eq_sets_finite_measure_algebra:
  assumes mcomplete "separable_space mtopology"
  shows "sets (borel_of LPm.mtopology) = sets (finite_measure_algebra (borel_of mtopology))"
  using sets_LPm1 sets_LPm2[OF assms] by simp

end

corollary weak_conv_topology_eq_finite_measure_algebra:
  assumes "Polish_space X"
  shows "sets (borel_of (weak_conv_topology X)) = sets (finite_measure_algebra (borel_of X))"
proof -
  obtain d where d:"Metric_space (topspace X) d" "Metric_space.mcomplete (topspace X) d"
    "Metric_space.mtopology (topspace X) d = X"
    by (metis Metric_space.topspace_mtopology assms completely_metrizable_space_def Polish_space_imp_completely_metrizable_space)
  then interpret Levy_Prokhorov "topspace X" d
    by (auto simp add: Levy_Prokhorov_def)
  have sep: "separable_space mtopology"
    by (simp add: assms d(3) Polish_space_imp_separable_space)
  show ?thesis
    using sets_LPm_eq_sets_finite_measure_algebra[OF d(2) sep] LPmtopology_eq_weak_conv_topology[OF sep]
    by(simp add: d)
qed

corollary weak_conv_topology_eq_subprob_algebra:
  assumes "Polish_space X"
  shows "sets (borel_of (subtopology (weak_conv_topology X) {N. subprob_space N \<and> sets N = sets (borel_of X)}))
         = sets (subprob_algebra (borel_of X))" (is "?lhs = ?rhs")
proof -
  have "?lhs = sets (borel_of (subtopology (weak_conv_topology X) {N. sets N = sets (borel_of X) \<and> subprob_space N}))"
    by meson
  also have "... = sets (borel_of (subtopology (weak_conv_topology X) {N. subprob_space N}))"
    using subtopology_restrict[of "weak_conv_topology X" "{N. subprob_space N}"]
    by(auto intro!: arg_cong[where f="\<lambda>x. sets (borel_of x)"] simp: Collect_conj_eq[symmetric] subprob_space_def)
  also have "... = ?rhs"
    by(auto simp: borel_of_subtopology sets_subprob_algebra_restrict
        weak_conv_topology_eq_finite_measure_algebra[OF assms]
        intro!: sets_restrict_space_cong)
  finally show ?thesis .
qed

corollary weak_conv_topology_eq_prob_algebra:
  assumes "Polish_space X"
  shows "sets (borel_of (subtopology (weak_conv_topology X) {N. prob_space N \<and> sets N = sets (borel_of X)}))
         = sets (prob_algebra (borel_of X))" (is "?lhs = ?rhs")
proof -
  have "?lhs = sets (borel_of (subtopology
                            (subtopology (weak_conv_topology X) {N. subprob_space N \<and> sets N = sets (borel_of X)})
                            {N. prob_space N}))"
    by(auto simp: subtopology_subtopology Collect_conj_eq[symmetric] dest:prob_space_imp_subprob_space
        intro!: arg_cong[where f="\<lambda>x. sets (borel_of (subtopology _ x))"])
  also have "... = sets (restrict_space (borel_of (subtopology (weak_conv_topology X)
                             {N. subprob_space N \<and> sets N = sets (borel_of X)})) {N. prob_space N})"
    by(simp add: borel_of_subtopology)
  also have "... = sets (restrict_space (subprob_algebra (borel_of X)) {N. prob_space N})"
    by(simp cong: sets_restrict_space_cong add: weak_conv_topology_eq_subprob_algebra[OF assms])
  also have "... = ?rhs"
    by(simp add: prob_algebra_def)
  finally show ?thesis .
qed

subsection \<open> Standardness \<close>
lemma closedin_weak_conv_topology_r:
  "closedin (weak_conv_topology X) {N. sets N = sets (borel_of X) \<and> N (space N) \<le> ennreal r}"
proof(rule closedin_limitin)
  fix Ni N
  assume h:"\<And>U. Ni U \<in> topspace (weak_conv_topology X)"
    "limitin (weak_conv_topology X) Ni N (nhdsin_sets (weak_conv_topology X) N)"
         "\<And>U. N \<in> U \<Longrightarrow> openin (weak_conv_topology X) U
               \<Longrightarrow> Ni U \<in> {N. sets N = sets (borel_of X) \<and> emeasure N (space N) \<le> ennreal r}"
  have x: "sets N = sets (borel_of X)" "finite_measure N"
    using limitin_topspace[OF h(2)] by auto
  interpret N: finite_measure N
    by fact
  interpret Ni: finite_measure "Ni i" for i
    using h(1) by simp
  have "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> (\<exists>B. \<forall>x\<in> topspace X. abs (f x) \<le> B)
            \<Longrightarrow> ((\<lambda>n. \<integral>x. f x \<partial>Ni n) \<longlongrightarrow> (\<integral>x. f x \<partial>N)) (nhdsin_sets (weak_conv_topology X) N)"
    using h(2) by(auto simp: weak_conv_on_def)
  from this[of "\<lambda>x. 1"]
  have "((\<lambda>n. measure (Ni n) (space (Ni n))) \<longlongrightarrow> measure N (space N)) (nhdsin_sets (weak_conv_topology X) N)"
    by auto
  hence "((\<lambda>n. Ni n (space (Ni n))) \<longlongrightarrow> N (space N)) (nhdsin_sets (weak_conv_topology X) N)"
    by (simp add: N.emeasure_eq_measure Ni.emeasure_eq_measure)
  hence "emeasure N (space N) \<le> ennreal r"
   using limitin_topspace[OF h(2)] h(3) by(auto intro!: tendsto_upperbound eventually_nhdsin_setsI)
  thus "N \<in> {N. sets N = sets (borel_of X) \<and> emeasure N (space N) \<le> ennreal r}"
    using x by blast
qed (auto intro!: finite_measureI simp: top.extremum_unique)

lemma closedin_weak_conv_topology_subprob:
  "closedin (weak_conv_topology X) {N. subprob_space N \<and> sets N = sets (borel_of X)}"
proof(rule closedin_limitin)
  fix Ni N
  assume h:"\<And>U. Ni U \<in> topspace (weak_conv_topology X)"
    "limitin (weak_conv_topology X) Ni N (nhdsin_sets (weak_conv_topology X) N)"
         "\<And>U. N \<in> U \<Longrightarrow> openin (weak_conv_topology X) U
              \<Longrightarrow> Ni U \<in> {N. subprob_space N \<and> sets N = sets (borel_of X)}"
  have x: "sets N = sets (borel_of X)" "finite_measure N"
    using limitin_topspace[OF h(2)] by auto
  have X:"topspace X \<noteq> {}"
    using h(3)[OF limitin_topspace[OF h(2)],simplified openin_topspace]
    by(auto simp: subprob_space_def space_borel_of subprob_space_axioms_def cong: sets_eq_imp_space_eq)
  interpret N: finite_measure N
    by fact
  interpret Ni: finite_measure "Ni i" for i
    using h(1) by simp
  have "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> (\<exists>B. \<forall>x\<in> topspace X. abs (f x) \<le> B)
             \<Longrightarrow> ((\<lambda>n. \<integral>x. f x \<partial>Ni n) \<longlongrightarrow> (\<integral>x. f x \<partial>N)) (nhdsin_sets (weak_conv_topology X) N)"
    using h by(auto simp: weak_conv_on_def)
  from this[of "\<lambda>x. 1"]
  have "((\<lambda>n. measure (Ni n) (space (Ni n))) \<longlongrightarrow> measure N (space N)) (nhdsin_sets (weak_conv_topology X) N)"
    by auto
  hence 1:"((\<lambda>n. Ni n (space (Ni n))) \<longlongrightarrow> N (space N)) (nhdsin_sets (weak_conv_topology X) N)"
    by (simp add: N.emeasure_eq_measure Ni.emeasure_eq_measure)
  hence "emeasure N (space N) \<le> 1"
    using limitin_topspace[OF h(2)] h(3)
    by(auto intro!: tendsto_upperbound[OF 1] eventually_nhdsin_setsI dest:subprob_space.subprob_emeasure_le_1)
  hence "subprob_space N"
    using X by(auto intro!: subprob_spaceI simp: sets_eq_imp_space_eq[OF x(1)] space_borel_of)
  thus "N \<in> {N. subprob_space N \<and> sets N = sets (borel_of X)}"
    using x h(3) by fast
qed (auto simp: subprob_space_def)

lemma closedin_weak_conv_topology_prob:
  "closedin (weak_conv_topology X) {N. prob_space N \<and> sets N = sets (borel_of X)}"
proof(rule closedin_limitin)
  fix Ni N
  assume h:"\<And>U. Ni U \<in> topspace (weak_conv_topology X)"
    "limitin (weak_conv_topology X) Ni N (nhdsin_sets (weak_conv_topology X) N)"
         "\<And>U. N \<in> U \<Longrightarrow> openin (weak_conv_topology X) U
              \<Longrightarrow> Ni U \<in> {N. prob_space N \<and> sets N = sets (borel_of X)}"
  have x: "sets N = sets (borel_of X)" "finite_measure N"
    using limitin_topspace[OF h(2)] by auto
  interpret N: finite_measure N
    by fact
  interpret Ni: finite_measure "Ni i" for i
    using h(1) by simp
  have "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> (\<exists>B. \<forall>x\<in> topspace X. abs (f x) \<le> B)
             \<Longrightarrow> ((\<lambda>n. \<integral>x. f x \<partial>Ni n) \<longlongrightarrow> (\<integral>x. f x \<partial>N)) (nhdsin_sets (weak_conv_topology X) N)"
    using h by(auto simp: weak_conv_on_def)
  from this[of "\<lambda>x. 1"]
  have "((\<lambda>n. measure (Ni n) (space (Ni n))) \<longlongrightarrow> measure N (space N)) (nhdsin_sets (weak_conv_topology X) N)"
    by auto
  hence "((\<lambda>n. 1) \<longlongrightarrow> measure N (space N)) (nhdsin_sets (weak_conv_topology X) N)"
    using x h
    by(auto intro!: tendsto_cong[where f="\<lambda>n. measure (Ni n) (space (Ni n))"
                     and g="\<lambda>n. 1",THEN iffD1] eventually_nhdsin_setsI prob_space.prob_space)
  hence "measure N (space N) = 1"
    by (metis nhdsin_sets_bot h(2) limitin_topspace tendsto_const_iff)
  hence "prob_space N"
    by (simp add: N.emeasure_eq_measure prob_spaceI)
  thus "N \<in> {N. prob_space N \<and> sets N = sets (borel_of X)}"
    using x by blast
qed (auto simp: prob_space.finite_measure)


corollary
  assumes "standard_borel M"
  shows standard_borel_finite_measure_algebra: "standard_borel (finite_measure_algebra M)"
    and standard_borel_ne_finite_measure_algebra: "standard_borel_ne (finite_measure_algebra M)"
    and standard_borel_subprob_algebra: "standard_borel (subprob_algebra M)"
    and standard_borel_prob_algebra: "standard_borel (prob_algebra M)"
proof -
  interpret sbn: standard_borel M by fact
  obtain X where X: "Polish_space X" "sets M = sets (borel_of X)"
    using sbn.Polish_space by blast
  show 1:"standard_borel (finite_measure_algebra M)"
    by (metis X finite_measure_algebra_cong Polish_space_weak_conv_topology standard_borel.intro weak_conv_topology_eq_finite_measure_algebra)
  moreover have "null_measure M \<in> space (finite_measure_algebra M)"
    by(auto simp: space_finite_measure_algebra intro!: finite_measureI)
  ultimately show "standard_borel_ne (finite_measure_algebra M)"
    using standard_borel_ne_axioms_def standard_borel_ne_def by force
  show "standard_borel (subprob_algebra M)"
    using Polish_space_closedin[OF Polish_space_weak_conv_topology[OF X(1)] closedin_weak_conv_topology_subprob] 
    by(auto cong: subprob_algebra_cong
            simp: X(2) weak_conv_topology_eq_subprob_algebra[OF X(1),symmetric] standard_borel_def)
  show "standard_borel (prob_algebra M)"
    using Polish_space_closedin[OF Polish_space_weak_conv_topology[OF X(1)] closedin_weak_conv_topology_prob] 
    by(auto cong: prob_algebra_cong
            simp: X(2) weak_conv_topology_eq_prob_algebra[OF X(1),symmetric] standard_borel_def)
qed

corollary
  assumes "standard_borel_ne M"
  shows standard_borel_ne_subprob_algebra: "standard_borel_ne (subprob_algebra M)"
    and standard_borel_ne_prob_algebra: "standard_borel_ne (prob_algebra M)"
proof -
  obtain x where x: "x \<in> space M"
    using assms standard_borel_ne.space_ne by auto
  then have "return M x \<in> space (subprob_algebra M)" "return M x \<in> space (prob_algebra M)"
    using prob_space_return
    by(auto intro!: prob_space_imp_subprob_space simp: space_subprob_algebra space_prob_algebra)
  thus "standard_borel_ne (subprob_algebra M)" "standard_borel_ne (prob_algebra M)"
    using assms standard_borel_subprob_algebra standard_borel_prob_algebra
    by(auto simp: standard_borel_ne_def standard_borel_ne_axioms_def)
qed

end