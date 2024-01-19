section \<open>Probability Spaces\<close>

text \<open>Some additional results about probability spaces in addition to "HOL-Probability".\<close>

theory Probability_Ext
  imports
    "HOL-Probability.Stream_Space"
    Concentration_Inequalities.Bienaymes_Identity
    Universal_Hash_Families.Carter_Wegman_Hash_Family
    Frequency_Moments_Preliminary_Results
begin

text \<open>The following aliases are here to prevent possible merge-conflicts. The lemmas have been
moved to @{theory Concentration_Inequalities.Bienaymes_Identity} and/or
@{theory Concentration_Inequalities.Concentration_Inequalities_Preliminary}.\<close>

lemmas make_ext = forall_Pi_to_PiE
lemmas PiE_reindex = PiE_reindex

context prob_space
begin

lemmas indep_sets_reindex = indep_sets_reindex
lemmas indep_vars_cong_AE = indep_vars_cong_AE
lemmas indep_vars_reindex = indep_vars_reindex
lemmas variance_divide = variance_divide
lemmas covariance_def = covariance_def
lemmas real_prod_integrable = cauchy_schwartz(1)
lemmas covariance_eq = covariance_eq
lemmas covar_integrable = covar_integrable
lemmas sum_square_int = sum_square_int
lemmas var_sum_1 = bienaymes_identity
lemmas covar_self_eq = covar_self_eq
lemmas covar_indep_eq_zero = covar_indep_eq_zero
lemmas var_sum_2 = bienaymes_identity_2
lemmas var_sum_pairwise_indep = bienaymes_identity_pairwise_indep
lemmas indep_var_from_indep_vars = indep_var_from_indep_vars
lemmas var_sum_pairwise_indep_2 = bienaymes_identity_pairwise_indep_2
lemmas var_sum_all_indep = bienaymes_identity_full_indep

lemma pmf_mono:
  assumes "M = measure_pmf p"
  assumes "\<And>x. x \<in> P \<Longrightarrow> x \<in> set_pmf p \<Longrightarrow> x \<in> Q"
  shows "prob P \<le> prob Q"
proof -
  have "prob P = prob (P \<inter> (set_pmf p))"
    by (rule  measure_pmf_eq[OF assms(1)], blast)
  also have "... \<le> prob Q"
    using assms by (intro finite_measure.finite_measure_mono, auto)
  finally show ?thesis by simp
qed

lemma pmf_add:
  assumes "M = measure_pmf p"
  assumes  "\<And>x. x \<in> P \<Longrightarrow> x \<in> set_pmf p \<Longrightarrow> x \<in> Q \<or> x \<in> R"
  shows "prob P \<le> prob Q + prob R"
proof -
  have [simp]:"events = UNIV" by (subst assms(1), simp)
  have "prob P \<le> prob (Q \<union> R)"
    using assms by (intro pmf_mono[OF assms(1)], blast)
  also have "... \<le> prob Q + prob R"
    by (rule measure_subadditive, auto)
  finally show ?thesis by simp
qed

lemma pmf_add_2:
  assumes "M = measure_pmf p"
  assumes "prob {\<omega>. P \<omega>} \<le> r1"
  assumes "prob {\<omega>. Q \<omega>} \<le> r2"
  shows "prob {\<omega>. P \<omega> \<or> Q \<omega>} \<le> r1 + r2" (is "?lhs \<le> ?rhs")
proof -
  have "?lhs \<le> prob {\<omega>. P \<omega>} + prob {\<omega>. Q \<omega>}"
    by (intro pmf_add[OF assms(1)], auto)
  also have "... \<le> ?rhs"
    by (intro add_mono assms(2-3))
  finally show ?thesis
    by simp
qed

end

end
