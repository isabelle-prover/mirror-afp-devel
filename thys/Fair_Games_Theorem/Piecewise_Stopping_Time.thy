section \<open>Piecewise Stopping Times\<close>

theory Piecewise_Stopping_Time
  imports Stopped_Value_Integration

begin

text \<open>Piecewise constant stopping times and their interaction with stopped values and integration.
  These are needed for the converse direction of the optional stopping theorem.\<close>

context nat_sigma_finite_filtered_measure
begin

subsection \<open>Piecewise constant stopping times\<close>

text \<open>Given @{term "i \<le> j"} and an @{term "F i"}-measurable set @{term S}, the function that
  returns @{term i} on @{term S} and @{term j} on its complement is a stopping time.
  This corresponds to \<^verbatim>\<open>isStoppingTime_piecewise_const\<close> in Mathlib.\<close>

lemma stopping_time_piecewise_const:
  assumes "i \<le> j" and S: "S \<in> sets (F i)"
  shows "stopping_time (\<lambda>\<omega>. if \<omega> \<in> S then i else j)"
proof (rule stopping_timeI)
  fix \<omega> assume "\<omega> \<in> space M"
  show "0 \<le> (if \<omega> \<in> S then i else j)" by simp
next
  fix t :: nat assume "0 \<le> t"
  have space_eq: "space (F t) = space M" by simp
  have top: "space M \<in> sets (F t)" using sets.top[of "F t"] by simp
  show "Measurable.pred (F t) (\<lambda>\<omega>. (if \<omega> \<in> S then i else j) \<le> t)"
    unfolding Measurable.pred_def
  proof -
    consider "j \<le> t" | "i \<le> t" "\<not> j \<le> t" | "\<not> i \<le> t"
      using \<open>i \<le> j\<close> by linarith
    then show "{\<omega> \<in> space (F t). (if \<omega> \<in> S then i else j) \<le> t} \<in> sets (F t)"
    proof cases
      case 1
      then have "{\<omega> \<in> space (F t). (if \<omega> \<in> S then i else j) \<le> t} = space (F t)"
        using \<open>i \<le> j\<close> by (auto simp: space_eq)
      then show ?thesis using top space_eq by simp
    next
      case 2
      then have "{\<omega> \<in> space (F t). (if \<omega> \<in> S then i else j) \<le> t} = S"
        using S sets.sets_into_space subset_antisym by fastforce
      then show ?thesis
        using S 2 sets_F_mono by force 
    next
      case 3
      then show ?thesis 
        using \<open>i \<le> j\<close> by (auto simp: Measurable.pred_def space_eq split: if_splits)
    qed
  qed
qed

text \<open>The stopped value at a piecewise constant stopping time decomposes into a piecewise function.
  This corresponds to \<^verbatim>\<open>stoppedValue_piecewise_const\<close> in Mathlib.\<close>

lemma stopped_value_piecewise_const:
  assumes "S \<subseteq> space M"
  shows "stopped_value X (\<lambda>\<omega>. if \<omega> \<in> S then i else j) = (\<lambda>\<omega>. if \<omega> \<in> S then X i \<omega> else X j \<omega>)"
  unfolding stopped_value_def by (simp add: if_distrib if_distribR)

subsection \<open>Integration over piecewise functions\<close>

text \<open>The integral of a piecewise function splits into integrals over the two pieces.
  This corresponds to \<^verbatim>\<open>integral_piecewise\<close> in Mathlib.\<close>

lemma piecewise_eq_indicator_sum:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "S \<in> sets M" "\<omega> \<in> space M"
  shows "(if \<omega> \<in> S then f \<omega> else g \<omega>) = indicat_real S \<omega> * f \<omega> + indicat_real (space M - S) \<omega> * g \<omega>"
  using \<open>\<omega> \<in> space M\<close> by (auto simp: indicator_def)

lemma integral_piecewise:
  fixes f g :: "'a \<Rightarrow> real"
  assumes S_meas: "S \<in> sets M" and int_f: "integrable M f" and int_g: "integrable M g"
  shows "(\<integral>\<omega>. (if \<omega> \<in> S then f \<omega> else g \<omega>) \<partial>M) =
    set_lebesgue_integral M S f + set_lebesgue_integral M (space M - S) g"
proof -
  let ?h = "\<lambda>\<omega>. indicat_real S \<omega> * f \<omega> + indicat_real (space M - S) \<omega> * g \<omega>"
  have eq_ae: "AE \<omega> in M. (if \<omega> \<in> S then f \<omega> else g \<omega>) = ?h \<omega>"
    by (rule AE_I2) (auto simp: indicator_def)
  have int_Sf: "integrable M (\<lambda>\<omega>. indicat_real S \<omega> * f \<omega>)"
    using integrable_mult_indicator[OF S_meas int_f]
    by (simp add: scaleR_conv_of_real)
  have int_Sg: "integrable M (\<lambda>\<omega>. indicat_real (space M - S) \<omega> * g \<omega>)"
    using integrable_mult_indicator[OF _ int_g] by (simp add: S_meas sets.Diff)
  have meas_if: "(\<lambda>\<omega>. if \<omega> \<in> S then f \<omega> else g \<omega>) \<in> borel_measurable M"
    by (intro measurable_If_set) (use int_f int_g S_meas in auto)
  have meas_h: "?h \<in> borel_measurable M"
    using int_Sf int_Sg by (intro borel_measurable_add) auto
  have "(\<integral>\<omega>. (if \<omega> \<in> S then f \<omega> else g \<omega>) \<partial>M) = (\<integral>\<omega>. ?h \<omega> \<partial>M)"
    by (rule integral_cong_AE[OF meas_if meas_h eq_ae])
  also have "\<dots> = (\<integral>\<omega>. indicat_real S \<omega> * f \<omega> \<partial>M) + (\<integral>\<omega>. indicat_real (space M - S) \<omega> * g \<omega> \<partial>M)"
    by (rule Bochner_Integration.integral_add[OF int_Sf int_Sg])
  also have "\<dots> = set_lebesgue_integral M S f + set_lebesgue_integral M (space M - S) g"
    unfolding set_lebesgue_integral_def by (simp add: scaleR_conv_of_real)
  finally show ?thesis .
qed

end

end
