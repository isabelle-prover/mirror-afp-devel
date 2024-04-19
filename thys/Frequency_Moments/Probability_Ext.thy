section \<open>Probability Spaces\<close>

text \<open>Some additional results about probability spaces in addition to "HOL-Probability".\<close>

theory Probability_Ext
  imports
    "HOL-Probability.Stream_Space"
    Concentration_Inequalities.Bienaymes_Identity
    Universal_Hash_Families.Carter_Wegman_Hash_Family
    Frequency_Moments_Preliminary_Results
begin

context prob_space
begin

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
