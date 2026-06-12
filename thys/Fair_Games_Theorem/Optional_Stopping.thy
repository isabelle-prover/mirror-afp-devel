section \<open>Fair Games Theorem\<close>

theory Optional_Stopping
  imports
    Piecewise_Stopping_Time
    "Martingales.Martingale"
begin

text \<open>The optional stopping theorem (fair games theorem): an adapted integrable process is a
  submartingale if and only if for all bounded stopping times @{term \<tau>} and @{term \<pi>} with
  @{term "\<tau> \<le> \<pi>"}, the expected stopped value at @{term \<tau>} is at most that at @{term \<pi>}.
  We also prove that the stopped process of a submartingale is a submartingale.\<close>

context nat_sigma_finite_filtered_measure
begin

subsection \<open>Helper lemmas\<close>

lemma indicator_set_in_F:
  assumes \<tau>_st: "stopping_time \<tau>" and \<pi>_st: "stopping_time \<pi>"
  shows "{\<omega> \<in> space M. \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega>} \<in> sets (F i)"
proof -
  have *: "Measurable.pred (F i) (\<lambda>\<omega>. \<tau> \<omega> \<le> i \<and> \<not> \<pi> \<omega> \<le> i)"
    by (simp add: \<pi>_st \<tau>_st pred_intros_logic stopping_timeD)
  have eq: "{\<omega> \<in> space M. \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega>} = {\<omega> \<in> space (F i). \<tau> \<omega> \<le> i \<and> \<not> \<pi> \<omega> \<le> i}"
    by auto
  show ?thesis using Measurable.predE[OF *] sets_F_subset[of i]
    by (auto simp: eq)
qed

subsection \<open>Forward direction\<close>

text \<open>If @{term X} is a submartingale and @{term "\<tau> \<le> \<pi>"} are bounded stopping times,
  then @{term "(\<integral>\<omega>. stopped_value X \<tau> \<omega> \<partial>M) \<le> (\<integral>\<omega>. stopped_value X \<pi> \<omega> \<partial>M)"}.
  This corresponds to \<^verbatim>\<open>Submartingale.expected_stoppedValue_mono\<close> in Mathlib.\<close>

theorem expected_stopped_value_mono:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes sub: "submartingale_linorder M F 0 X"
    and \<tau>_st: "stopping_time \<tau>" and \<pi>_st: "stopping_time \<pi>"
    and le: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<tau> \<omega> \<le> \<pi> \<omega>"
    and bnd: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<pi> \<omega> \<le> N"
  shows "(\<integral>\<omega>. stopped_value X \<tau> \<omega> \<partial>M) \<le> (\<integral>\<omega>. stopped_value X \<pi> \<omega> \<partial>M)"
proof -
  from sub interpret S: submartingale_linorder M F 0 X .
  have \<tau>_bnd: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<tau> \<omega> \<le> N"
    using le bnd by (meson order_trans)
  \<comment> \<open>Integrability of stopped values\<close>
  obtain int_\<tau>: "integrable M (stopped_value X \<tau>)" and int_\<pi>: "integrable M (stopped_value X \<pi>)"
    by (meson S.integrable \<tau>_bnd \<tau>_st \<pi>_st bnd integrable_stopped_value zero_le)
  \<comment> \<open>Suffices to show the difference is non-negative\<close>
  have "0 \<le> (\<integral>\<omega>. stopped_value X \<pi> \<omega> \<partial>M) - (\<integral>\<omega>. stopped_value X \<tau> \<omega> \<partial>M)"
  proof -
    have "(\<integral>\<omega>. stopped_value X \<pi> \<omega> \<partial>M) - (\<integral>\<omega>. stopped_value X \<tau> \<omega> \<partial>M) =
          (\<integral>\<omega>. stopped_value X \<pi> \<omega> - stopped_value X \<tau> \<omega> \<partial>M)"
      by (rule Bochner_Integration.integral_diff[OF int_\<pi> int_\<tau>, symmetric])
    \<comment> \<open>Apply the telescoping identity AE\<close>
    also have "\<dots> = (\<integral>\<omega>. (\<Sum>i\<le>N. indicator {\<omega> \<in> space M. \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega>} \<omega> *
      (X (Suc i) \<omega> - X i \<omega>)) \<partial>M)"
    proof (rule Bochner_Integration.integral_cong_AE)
      show "(\<lambda>\<omega>. stopped_value X \<pi> \<omega> - stopped_value X \<tau> \<omega>) \<in> borel_measurable M"
        using int_\<pi> int_\<tau> by (intro borel_measurable_diff) auto
      show "(\<lambda>\<omega>. \<Sum>i\<le>N. indicator {\<omega> \<in> space M. \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega>} \<omega> *
        (X (Suc i) \<omega> - X i \<omega>)) \<in> borel_measurable M"
      proof (intro borel_measurable_sum borel_measurable_times borel_measurable_indicator
                   borel_measurable_diff borel_measurable_integrable)
        fix i assume "i \<in> {..N}"
        show "{\<omega> \<in> space M. \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega>} \<in> sets M"
          using indicator_set_in_F[OF \<tau>_st \<pi>_st] sets_F_subset by blast
      qed (auto simp: S.integrable)
      show "AE \<omega> in M. stopped_value X \<pi> \<omega> - stopped_value X \<tau> \<omega> =
        (\<Sum>i\<le>N. indicator {\<omega> \<in> space M. \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega>} \<omega> * (X (Suc i) \<omega> - X i \<omega>))"
        by (rule AE_I2) (simp add: stopped_value_sub_eq_sum[OF \<tau>_st \<pi>_st le bnd])
    qed
    \<comment> \<open>Exchange integral and sum\<close>
    also have "\<dots> = (\<Sum>i\<le>N. \<integral>\<omega>. indicator {\<omega> \<in> space M. \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega>} \<omega> *
      (X (Suc i) \<omega> - X i \<omega>) \<partial>M)"
    proof (rule Bochner_Integration.integral_sum)
      fix i assume "i \<in> {..N}"
      have "{\<omega> \<in> space M. \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega>} \<in> sets M"
        using indicator_set_in_F[OF \<tau>_st \<pi>_st] sets_F_subset by blast
      then show "integrable M (\<lambda>\<omega>. indicator {\<omega> \<in> space M. \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega>} \<omega> * (X (Suc i) \<omega> - X i \<omega>))"
        by (simp add: S.integrable integrable_real_mult_indicator mult.commute)
    qed
    \<comment> \<open>Each summand is non-negative via @{text set_integral_le}\<close>
    also have "\<dots> \<ge> 0"
    proof (rule sum_nonneg)
      fix i assume "i \<in> {..N}"
      let ?A = "{\<omega> \<in> space M. \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega>}"
      have A_Fi: "?A \<in> sets (F i)"
        by (rule indicator_set_in_F[OF \<tau>_st \<pi>_st])
      \<comment> \<open>The summand equals @{text "\<integral>\<^sub>A X(Suc i) - \<integral>\<^sub>A X i"}\<close>
      have eq: "(\<integral>\<omega>. indicat_real ?A \<omega> * (X (Suc i) \<omega> - X i \<omega>) \<partial>M) =
        set_lebesgue_integral M ?A (X (Suc i)) - set_lebesgue_integral M ?A (X i)"
      proof -
        have "?A \<in> sets M"
          using A_Fi sets_F_subset by blast
        then have int: "integrable M (\<lambda>x. indicat_real ?A x * X j x)" for j
          by (simp add: S.integrable integrable_real_mult_indicator mult.commute)
        have "(\<integral>\<omega>. indicat_real ?A \<omega> * (X (Suc i) \<omega> - X i \<omega>) \<partial>M) =
          (\<integral>\<omega>. indicat_real ?A \<omega> * X (Suc i) \<omega> - indicat_real ?A \<omega> * X i \<omega> \<partial>M)"
          by (simp add: right_diff_distrib)
        also have "\<dots> = (\<integral>\<omega>. indicat_real ?A \<omega> * X (Suc i) \<omega> \<partial>M) - (\<integral>\<omega>. indicat_real ?A \<omega> * X i \<omega> \<partial>M)"
          using Bochner_Integration.integral_diff int by blast
        also have "\<dots> = set_lebesgue_integral M ?A (X (Suc i)) - set_lebesgue_integral M ?A (X i)"
          unfolding set_lebesgue_integral_def by (simp add: scaleR_conv_of_real)
        finally show ?thesis .
      qed
      \<comment> \<open>Apply the submartingale @{text set_integral_le} property\<close>
      have "set_lebesgue_integral M ?A (X i) \<le> set_lebesgue_integral M ?A (X (Suc i))"
        by (rule S.set_integral_le[OF A_Fi]) simp_all
      then show "0 \<le> (\<integral>\<omega>. indicat_real ?A \<omega> * (X (Suc i) \<omega> - X i \<omega>) \<partial>M)"
        unfolding eq by simp
    qed
    finally show ?thesis by simp
  qed
  then show ?thesis by simp
qed

subsection \<open>Converse direction\<close>

text \<open>If an adapted integrable process satisfies the monotonicity of expected stopped values
  for all bounded stopping times, then it is a submartingale.
  This corresponds to \<^verbatim>\<open>submartingale_of_expected_stoppedValue_mono\<close> in Mathlib.\<close>

theorem submartingale_of_expected_stopped_value_mono:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes adapted: "adapted_process M F 0 X"
    and integrable: "\<And>i. integrable M (X i)"
    and mono: "\<And>\<tau> \<pi> N. stopping_time \<tau> \<Longrightarrow> stopping_time \<pi> \<Longrightarrow>
      (\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<tau> \<omega> \<le> \<pi> \<omega>) \<Longrightarrow> (\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<pi> \<omega> \<le> N) \<Longrightarrow>
      (\<integral>\<omega>. stopped_value X \<tau> \<omega> \<partial>M) \<le> (\<integral>\<omega>. stopped_value X \<pi> \<omega> \<partial>M)"
  shows "submartingale M F 0 X"
proof (rule submartingale_of_set_integral_le_Suc[OF adapted integrable])
  fix A :: "'a set" and i :: nat
  assume A_Fi: "A \<in> sets (F i)"
  \<comment> \<open>Construct piecewise stopping times\<close>
  define \<tau> :: "'a \<Rightarrow> nat" where "\<tau> \<omega> = (if \<omega> \<in> A then i else Suc i)" for \<omega>
  define \<pi> :: "'a \<Rightarrow> nat" where "\<pi> \<omega> = Suc i" for \<omega>
  have \<tau>_st: "stopping_time \<tau>"
    unfolding \<tau>_def by (rule stopping_time_piecewise_const) (simp_all add: A_Fi)
  have \<pi>_st: "stopping_time \<pi>"
    unfolding \<pi>_def by (rule stopping_time_const) simp
  have \<tau>_le_\<pi>: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<tau> \<omega> \<le> \<pi> \<omega>"
    unfolding \<tau>_def \<pi>_def by simp
  have \<pi>_bnd: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<pi> \<omega> \<le> Suc i"
    unfolding \<pi>_def by simp
  \<comment> \<open>Apply the monotonicity hypothesis\<close>
  have ineq: "(\<integral>\<omega>. stopped_value X \<tau> \<omega> \<partial>M) \<le> (\<integral>\<omega>. stopped_value X \<pi> \<omega> \<partial>M)"
    by (rule mono[OF \<tau>_st \<pi>_st \<tau>_le_\<pi> \<pi>_bnd])
  \<comment> \<open>Decompose stopped values\<close>
  have A_sub: "A \<subseteq> space M"
    using A_Fi sets_F_subset sets.sets_into_space by blast
  have sv_\<tau>: "stopped_value X \<tau> = (\<lambda>\<omega>. if \<omega> \<in> A then X i \<omega> else X (Suc i) \<omega>)"
    unfolding \<tau>_def by (rule stopped_value_piecewise_const[OF A_sub])
  have sv_\<pi>: "stopped_value X \<pi> = X (Suc i)"
    unfolding \<pi>_def stopped_value_def by simp
  \<comment> \<open>Decompose the integral of the piecewise function\<close>
  have A_meas: "A \<in> sets M"
    using A_Fi sets_F_subset by blast
  have lhs: "(\<integral>\<omega>. stopped_value X \<tau> \<omega> \<partial>M) =
    set_lebesgue_integral M A (X i) + set_lebesgue_integral M (space M - A) (X (Suc i))"
    unfolding sv_\<tau> by (rule integral_piecewise[OF A_meas integrable integrable])
  have rhs: "(\<integral>\<omega>. stopped_value X \<pi> \<omega> \<partial>M) =
             set_lebesgue_integral M A (X (Suc i)) + set_lebesgue_integral M (space M - A) (X (Suc i))"
  proof -
    have "(\<integral>\<omega>. stopped_value X \<pi> \<omega> \<partial>M) = (\<integral>\<omega>. X (Suc i) \<omega> \<partial>M)"
      unfolding sv_\<pi> ..
    also have "\<dots> = (\<integral>\<omega>. (if \<omega> \<in> A then X (Suc i) \<omega> else X (Suc i) \<omega>) \<partial>M)"
      by simp
    also have "\<dots> = set_lebesgue_integral M A (X (Suc i)) +
      set_lebesgue_integral M (space M - A) (X (Suc i))"
      by (rule integral_piecewise[OF A_meas integrable integrable])
    finally show ?thesis .
  qed
  show "set_lebesgue_integral M A (X i) \<le> set_lebesgue_integral M A (X (Suc i))"
    using ineq lhs rhs by simp
qed

subsection \<open>The optional stopping theorem (iff)\<close>

text \<open>The full characterization: an adapted integrable process is a submartingale iff
  expected stopped values are monotone for all bounded stopping times.
  This corresponds to \<^verbatim>\<open>submartingale_iff_expected_stoppedValue_mono\<close> in Mathlib.\<close>

theorem submartingale_iff_expected_stopped_value_mono:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "adapted_process M F 0 X" "\<And>i. integrable M (X i)"
  shows "submartingale M F 0 X \<longleftrightarrow>
    (\<forall>\<tau> \<pi>. stopping_time \<tau> \<longrightarrow> stopping_time \<pi> \<longrightarrow>
      (\<forall>\<omega>\<in>space M. \<tau> \<omega> \<le> \<pi> \<omega>) \<longrightarrow> (\<exists>N. \<forall>\<omega>\<in>space M. \<pi> \<omega> \<le> N) \<longrightarrow>
      (\<integral>\<omega>. stopped_value X \<tau> \<omega> \<partial>M) \<le> (\<integral>\<omega>. stopped_value X \<pi> \<omega> \<partial>M))" (is "?L = ?R")
proof
  show "?L \<Longrightarrow> ?R"
    by (metis expected_stopped_value_mono submartingale_linorder_def)
  show "?R \<Longrightarrow> ?L"
    by (intro submartingale_of_expected_stopped_value_mono[OF assms]) blast
qed

subsection \<open>Stopped process of a submartingale\<close>

text \<open>The stopped process of a submartingale with respect to a stopping time is a submartingale.
  This corresponds to \<^verbatim>\<open>Submartingale.stoppedProcess\<close> in Mathlib.\<close>

text \<open>We first show the stopped process is adapted. The proof proceeds by induction:
  @{text "X\<^sup>\<tau> 0 = X 0"} is trivially @{term "F 0"}-measurable, and
  @{text "X\<^sup>\<tau> (Suc n) = if \<tau> \<le> n then X\<^sup>\<tau> n else X (Suc n)"} is @{term "F (Suc n)"}-measurable
  by the induction hypothesis, adaptedness of @{term X}, and the stopping time property.\<close>

lemma adapted_stopped_process:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes adapted: "adapted_process M F 0 X" and \<tau>_st: "stopping_time \<tau>"
  shows "adapted_process M F 0 (stopped_process X \<tau>)"
proof (rule adapted_process.intro[OF filtered_measure_axioms])
  show "adapted_process_axioms F 0 (stopped_process X \<tau>)"
  proof (rule adapted_process_axioms.intro)
    fix i :: nat assume "0 \<le> i"
    show "stopped_process X \<tau> i \<in> borel_measurable (F i)"
    proof (induction i)
      case 0
      have "stopped_process X \<tau> 0 = X 0"
        unfolding stopped_process_def by simp
      then show ?case
        using adapted_process.adapted[OF adapted, of 0] by simp
    next
      case (Suc n)
      \<comment> \<open>The stopped process at @{term "Suc n"} equals a piecewise function on @{term "space M"}\<close>
      have eq: "\<And>\<omega>. stopped_process X \<tau> (Suc n) \<omega> =
        (if \<tau> \<omega> \<le> n then stopped_process X \<tau> n \<omega> else X (Suc n) \<omega>)"
        unfolding stopped_process_def by (auto simp: min_def)
      \<comment> \<open>@{term "F n"} is a sub-sigma-algebra of @{term "F (Suc n)"}\<close>
      have subalg: "subalgebra (F (Suc n)) (F n)"
        unfolding subalgebra_def using space_F sets_F_mono[of n "Suc n"] by auto
      \<comment> \<open>The induction hypothesis gives @{term "F n"}-measurability, lift to @{term "F (Suc n)"}\<close>
      have meas_n: "stopped_process X \<tau> n \<in> borel_measurable (F (Suc n))"
        by (rule measurable_from_subalg[OF subalg Suc.IH])
      \<comment> \<open>@{term "X (Suc n)"} is @{term "F (Suc n)"}-measurable by adaptedness\<close>
      have meas_Sn: "X (Suc n) \<in> borel_measurable (F (Suc n))"
        using adapted_process.adapted[OF adapted] by simp
      \<comment> \<open>The set @{term "{\<omega>. \<tau> \<omega> \<le> n}"} is in @{term "sets (F (Suc n))"}\<close>
      have set_Sn: "{\<omega> \<in> space (F (Suc n)). \<tau> \<omega> \<le> n} \<in> sets (F (Suc n))"
        using \<tau>_st order_less_imp_le predE stopping_time_measurable_le by blast
      \<comment> \<open>The piecewise function is @{term "F (Suc n)"}-measurable\<close>
      let ?A = "{\<omega> \<in> space (F (Suc n)). \<tau> \<omega> \<le> n}"
      have A_sets: "?A \<in> sets (F (Suc n))" by (rule set_Sn)
      have A_sub: "?A \<subseteq> space (F (Suc n))" using sets.sets_into_space[OF A_sets] .
      have meas_pw: "(\<lambda>\<omega>. if \<omega> \<in> ?A then stopped_process X \<tau> n \<omega> else X (Suc n) \<omega>)
        \<in> borel_measurable (F (Suc n))"
        using measurable_If_set meas_n meas_Sn set_Sn by blast
      \<comment> \<open>Transfer: the stopped process agrees with the piecewise function on @{term "space (F (Suc n))"}\<close>
      show ?case
        using measurable_cong[of "F (Suc n)" "stopped_process X \<tau> (Suc n)"
          "\<lambda>\<omega>. if \<omega> \<in> ?A then stopped_process X \<tau> n \<omega> else _ \<omega>"]
          eq meas_pw by fastforce
    qed
  qed
qed

theorem stopped_process_submartingale:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes sub: "submartingale_linorder M F 0 X"
    and \<tau>_st: "stopping_time \<tau>"
  shows "submartingale M F 0 (stopped_process X \<tau>)"
proof -
  let ?sv = "stopped_value (stopped_process X \<tau>)"
  from sub interpret S: submartingale_linorder M F 0 X .
  \<comment> \<open>Use the converse direction: suffices to show monotonicity of expected stopped values\<close>
  show ?thesis
  proof (rule submartingale_of_expected_stopped_value_mono)
    show "adapted_process M F 0 (stopped_process X \<tau>)"
      by (simp add: S.adapted_process_axioms \<tau>_st adapted_stopped_process)
    show "\<And>i. integrable M (stopped_process X \<tau> i)"
      by (simp add: S.integrable \<tau>_st integrable_stopped_process)
  next
    fix \<sigma> \<rho> :: "'a \<Rightarrow> nat" and N :: nat
    assume \<sigma>_st: "stopping_time \<sigma>" and \<rho>_st: "stopping_time \<rho>"
      and "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<sigma> \<omega> \<le> \<rho> \<omega>"
      and bnd: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<rho> \<omega> \<le> N"
    then have le': "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> min (\<sigma> \<omega>) (\<tau> \<omega>) \<le> min (\<rho> \<omega>) (\<tau> \<omega>)"
      by (simp add: min_le_iff_disj)
    \<comment> \<open>stopped value of the stopped process equals that of @{term X} with @{const min}\<close>
    have sv: "?sv \<sigma> = stopped_value X (\<lambda>\<omega>. min (\<sigma> \<omega>) (\<tau> \<omega>))" "?sv \<rho> = stopped_value X (\<lambda>\<omega>. min (\<rho> \<omega>) (\<tau> \<omega>))"
      unfolding stopped_value_def stopped_process_def by auto
    \<comment> \<open>@{term "\<lambda>\<omega>. min (\<sigma> \<omega>) (\<tau> \<omega>)"} and @{term "\<lambda>\<omega>. min (\<rho> \<omega>) (\<tau> \<omega>)"} are stopping times\<close>
    have st_\<sigma>': "stopping_time (\<lambda>\<omega>. min (\<sigma> \<omega>) (\<tau> \<omega>))"
      by (intro stopping_time_min \<sigma>_st \<tau>_st)
    have st_\<rho>': "stopping_time (\<lambda>\<omega>. min (\<rho> \<omega>) (\<tau> \<omega>))"
      by (intro stopping_time_min \<rho>_st \<tau>_st)
    \<comment> \<open>Apply the forward direction\<close>
    show "(\<integral>\<omega>. ?sv \<sigma> \<omega> \<partial>M) \<le> (\<integral>\<omega>. ?sv \<rho> \<omega> \<partial>M)"
      using expected_stopped_value_mono[OF sub st_\<sigma>' st_\<rho>' le'] sv bnd min_le_iff_disj
      by metis
  qed
qed

end

end

