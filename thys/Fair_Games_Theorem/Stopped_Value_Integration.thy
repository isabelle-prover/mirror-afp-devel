section \<open>Integrability of Stopped Values and Processes\<close>

theory Stopped_Value_Integration
  imports "Doob_Convergence.Stopping_Time"
begin

text \<open>Integrability of stopped values and stopped processes, and the telescoping identity
  for differences of stopped values. These results bridge the gap between the existing
  AFP theories (Martingales, \<^verbatim>\<open>Doob_Convergence\<close>) and the optional stopping theorem.\<close>

context nat_sigma_finite_filtered_measure
begin

subsection \<open>Stopped value as a sum of indicators\<close>

text \<open>A stopped value with a bounded stopping time can be written as a finite sum of indicators.\<close>

lemma stopped_value_eq_sum:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> 'b :: real_vector"
  assumes \<tau>_st: "stopping_time \<tau>" and \<tau>_bnd: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<tau> \<omega> \<le> N"
  assumes \<omega>_in: "\<omega> \<in> space M"
  shows "stopped_value X \<tau> \<omega> = (\<Sum>i\<le>N. indicator {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> *\<^sub>R X i \<omega>)"
proof -
  have "stopped_value X \<tau> \<omega> = X (\<tau> \<omega>) \<omega>"
    by (simp add: stopped_value_def)
  also have "\<dots> = 1 *\<^sub>R X (\<tau> \<omega>) \<omega>" by (metis (full_types) scale_one)
  also have "\<dots> = indicator {\<omega> \<in> space M. \<tau> \<omega> = \<tau> \<omega>} \<omega> *\<^sub>R X (\<tau> \<omega>) \<omega> +
    (\<Sum>i \<in> {..N} - {\<tau> \<omega>}. indicator {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> *\<^sub>R X i \<omega>)"
    using \<omega>_in by (simp add: indicator_def)
  also have "\<dots> = (\<Sum>i\<le>N. indicator {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> *\<^sub>R X i \<omega>)"
    using \<omega>_in \<tau>_bnd[OF \<omega>_in]
    by (subst sum.remove [where x = "\<tau> \<omega>"]) simp_all
  finally show ?thesis .
qed

subsection \<open>Telescoping identity for stopped values\<close>

text \<open>The difference of stopped values can be expressed as a sum of indicator-weighted increments.
  This corresponds to \<^verbatim>\<open>stoppedValue_sub_eq_sum'\<close> in Mathlib.\<close>

lemma stopped_value_sub_eq_sum:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes \<tau>_st: "stopping_time \<tau>" and \<pi>_st: "stopping_time \<pi>"
    and le: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<tau> \<omega> \<le> \<pi> \<omega>"
    and bnd: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<pi> \<omega> \<le> N"
    and \<omega>_in: "\<omega> \<in> space M"
  shows "stopped_value X \<pi> \<omega> - stopped_value X \<tau> \<omega> =
    (\<Sum>i\<le>N. indicator {\<omega> \<in> space M. \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega>} \<omega> * (X (Suc i) \<omega> - X i \<omega>))"
proof -
  have "(\<Sum>i\<le>N. indicator {\<omega> \<in> space M. \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega>} \<omega> * (X (Suc i) \<omega> - X i \<omega>)) =
    (\<Sum>i\<in>{\<tau> \<omega>..<\<pi> \<omega>}. X (Suc i) \<omega> - X i \<omega>)"
    using \<omega>_in bnd[OF \<omega>_in] 
    by (intro sum.mono_neutral_cong_right) (auto simp: indicator_def)
  also have "\<dots> = X (\<pi> \<omega>) \<omega> - X (\<tau> \<omega>) \<omega>"
    using \<omega>_in le sum_Suc_diff' by fastforce
  finally show ?thesis by (simp add: stopped_value_def)
qed

text \<open>If each @{term "X i"} is integrable and the stopping time is bounded, then the stopped value
  is integrable. This corresponds to \<^verbatim>\<open>integrable_stoppedValue\<close> in Mathlib.\<close>

lemma integrable_stopped_value:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes \<tau>_st: "stopping_time \<tau>" and int_X: "\<And>i. integrable M (X i)"
    and \<tau>_bnd: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<tau> \<omega> \<le> N"
  shows "integrable M (stopped_value X \<tau>)"
proof -
  \<comment> \<open>Each indicator set is measurable\<close>
  have meas_eq: "\<And>i. {\<omega> \<in> space M. \<tau> \<omega> = i} \<in> sets M"
  proof -
    fix i :: nat
    have "Measurable.pred (F i) (\<lambda>\<omega>. \<tau> \<omega> = i)"
      by (rule stopping_time_measurable_eq[OF \<tau>_st]) simp_all
    then have "{\<omega> \<in> space M. \<tau> \<omega> = i} \<in> sets (F i)"
      by (metis predE subalg subalgebra_def)
    then show "{\<omega> \<in> space M. \<tau> \<omega> = i} \<in> sets M"
      using sets_F_subset[of i] by blast
  qed
  \<comment> \<open>Each summand is integrable\<close>
  have int_summand: "\<And>i. integrable M (\<lambda>\<omega>. indicat_real {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> * X i \<omega>)"
    by (simp add: int_X integrable_real_mult_indicator meas_eq mult.commute)
  \<comment> \<open>The sum is integrable\<close>
  have int_sum: "integrable M (\<lambda>\<omega>. \<Sum>i\<le>N. indicat_real {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> * X i \<omega>)"
    by (intro Bochner_Integration.integrable_sum) (auto intro: int_summand)
  \<comment> \<open>The stopped value agrees with the sum AE\<close>
  have eq: "AE \<omega> in M. (\<Sum>i\<le>N. indicat_real {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> * X i \<omega>) =
    stopped_value X \<tau> \<omega>"
    by (intro AE_I2) (simp add: stopped_value_eq_sum[OF \<tau>_st \<tau>_bnd])
  have eq_space: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow>
    stopped_value X \<tau> \<omega> = (\<Sum>i\<le>N. indicat_real {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> * X i \<omega>)"
    by (simp add: stopped_value_eq_sum[OF \<tau>_st \<tau>_bnd])
  \<comment> \<open>Measurability via @{thm measurable_cong} with the sum\<close>
  have meas_sum: "(\<lambda>\<omega>. \<Sum>i\<le>N. indicat_real {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> * X i \<omega>) \<in> borel_measurable M"
    using int_sum by (rule borel_measurable_integrable)
  have meas_sv: "stopped_value X \<tau> \<in> borel_measurable M"
    using measurable_cong[of M "stopped_value X \<tau>"
      "\<lambda>\<omega>. \<Sum>i\<le>N. indicat_real {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> * X i \<omega>" borel]
      eq_space meas_sum by auto
  \<comment> \<open>Transfer integrability via AE equality\<close>
  show ?thesis
    by (rule Bochner_Integration.integrable_cong_AE_imp[OF int_sum meas_sv eq])
qed

subsection \<open>Stopped process\<close>

text \<open>The stopped process @{text "X\<^sup>\<tau>"} is defined as @{text "X (min i \<tau>)"}.\<close>

definition stopped_process :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b" where
  "stopped_process X \<tau> i \<omega> \<equiv> X (min i (\<tau> \<omega>)) \<omega>"

lemma stopped_process_eq_stopped_value:
  "stopped_process X \<tau> i = stopped_value X (\<lambda>\<omega>. min i (\<tau> \<omega>))"
  unfolding stopped_process_def stopped_value_def by simp

lemma integrable_stopped_process:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "stopping_time \<tau>" "\<And>i. integrable M (X i)"
  shows "integrable M (stopped_process X \<tau> n)"
proof -
  have "stopping_time (\<lambda>\<omega>. min n (\<tau> \<omega>))"
    by (intro stopping_time_min stopping_time_const assms) simp
  with assms show ?thesis
    unfolding stopped_process_eq_stopped_value
    using integrable_stopped_value min.cobounded1 by blast
qed

end

end
