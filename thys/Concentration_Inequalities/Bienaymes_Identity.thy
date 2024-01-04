section \<open>Bienaym\'e's identity\<close>

text \<open>Bienaym\'e's identity~\cite[\S 17]{loeve1977} can be used to deduce the variance of a sum of
random variables, if their co-variance is known. A common use-case of the identity is the
computation of the variance of the mean of pair-wise independent variables.\<close>

theory Bienaymes_Identity
  imports Concentration_Inequalities_Preliminary
begin

context prob_space
begin

lemma variance_divide:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable M f"
  shows "variance (\<lambda>\<omega>. f \<omega> / r) = variance f / r^2"
  using assms
  by (subst Bochner_Integration.integral_divide[OF assms(1)])
    (simp add:diff_divide_distrib[symmetric] power2_eq_square algebra_simps)

definition covariance where
  "covariance f g = expectation (\<lambda>\<omega>. (f \<omega> - expectation f) * (g \<omega> - expectation g))"

lemma covariance_eq:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes "integrable M (\<lambda>\<omega>. f \<omega>^2)" "integrable M (\<lambda>\<omega>. g \<omega>^2)"
  shows "covariance f g = expectation (\<lambda>\<omega>. f \<omega> * g \<omega>) - expectation f * expectation g"
proof -
  have "integrable M f" using square_integrable_imp_integrable assms by auto
  moreover have "integrable M g" using square_integrable_imp_integrable assms by auto
  ultimately show ?thesis
    using assms cauchy_schwartz(1)[where M="M"]
    by (simp add:covariance_def algebra_simps prob_space)
qed

lemma covar_integrable:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes "integrable M (\<lambda>\<omega>. f \<omega>^2)" "integrable M (\<lambda>\<omega>. g \<omega>^2)"
  shows "integrable M (\<lambda>\<omega>. (f \<omega> - expectation f) * (g \<omega> - expectation g))"
proof -
  have "integrable M f" using square_integrable_imp_integrable assms by auto
  moreover have "integrable M g" using square_integrable_imp_integrable assms by auto
  ultimately show ?thesis using assms cauchy_schwartz(1)[where M="M"] by (simp add: algebra_simps)
qed

lemma sum_square_int:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  shows "integrable M (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)\<^sup>2)"
proof -
  have " integrable M (\<lambda>\<omega>. \<Sum>i\<in>I. \<Sum>j\<in>I. f j \<omega> * f i \<omega>)"
    using assms
    by (intro Bochner_Integration.integrable_sum cauchy_schwartz(1)[where M="M"], auto)
  thus ?thesis
    by (simp add:power2_eq_square sum_distrib_left sum_distrib_right)
qed

theorem bienaymes_identity:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  shows
    "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i \<in> I. (\<Sum>j \<in> I. covariance (f i) (f j)))"
proof -
  have a:"\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
    integrable M (\<lambda>\<omega>. (f i \<omega> - expectation (f i)) * (f j \<omega> - expectation (f j)))"
    using assms covar_integrable by simp
  have "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = expectation (\<lambda>\<omega>. (\<Sum>i\<in>I. f i \<omega> - expectation (f i))\<^sup>2)"
    using square_integrable_imp_integrable[OF assms(2,3)]
    by (simp add: Bochner_Integration.integral_sum  sum_subtractf)
  also have "... = expectation (\<lambda>\<omega>. (\<Sum>i \<in> I. (\<Sum>j \<in> I.
    (f i \<omega> - expectation (f i)) *  (f j \<omega> - expectation (f j)))))"
    by (simp add: power2_eq_square sum_distrib_right sum_distrib_left mult.commute)
  also have "... = (\<Sum>i \<in> I. (\<Sum>j \<in> I. covariance (f i) (f j)))"
    using a by (simp add: Bochner_Integration.integral_sum covariance_def)
  finally show ?thesis by simp
qed

lemma covar_self_eq:
  fixes f :: "'a \<Rightarrow> real"
  shows "covariance f f = variance f"
  by (simp add:covariance_def power2_eq_square)

lemma covar_indep_eq_zero:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "integrable M f"
  assumes "integrable M g"
  assumes "indep_var borel f borel g"
  shows "covariance f g = 0"
proof -
  have a:"indep_var borel ((\<lambda>t. t - expectation f) \<circ> f) borel ((\<lambda>t. t - expectation g) \<circ> g)"
    by (rule indep_var_compose[OF assms(3)], auto)

  have b:"expectation (\<lambda>\<omega>. (f \<omega> - expectation f) * (g \<omega> - expectation g)) = 0"
    using a assms by (subst indep_var_lebesgue_integral, auto simp add:comp_def prob_space)

  thus ?thesis by (simp add:covariance_def)
qed

lemma bienaymes_identity_2:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  shows "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) =
      (\<Sum>i \<in> I. variance (f i)) + (\<Sum>i \<in> I. \<Sum>j \<in> I - {i}. covariance (f i) (f j))"
proof -
  have "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i\<in>I. \<Sum>j\<in>I. covariance (f i) (f j))"
    by (simp add: bienaymes_identity[OF assms(1,2,3)])
  also have "... = (\<Sum>i\<in>I. covariance (f i) (f i) + (\<Sum>j\<in>I-{i}. covariance (f i) (f j)))"
    using assms by (subst sum.insert[symmetric], auto simp add:insert_absorb)
  also have "... = (\<Sum>i\<in>I. variance (f i)) +  (\<Sum>i \<in> I. (\<Sum>j\<in>I-{i}. covariance (f i) (f j)))"
    by (simp add: covar_self_eq[symmetric] sum.distrib)
  finally show ?thesis by simp
qed

theorem bienaymes_identity_pairwise_indep:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  assumes "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> indep_var borel (f i) borel (f j)"
  shows "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i \<in> I. variance (f i))"
proof -
  have "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I - {i} \<Longrightarrow> covariance (f i) (f j) = 0"
    using covar_indep_eq_zero assms(4) square_integrable_imp_integrable[OF assms(2,3)] by auto
  hence a:"(\<Sum>i \<in> I. \<Sum>j \<in> I - {i}. covariance (f i) (f j)) = 0"
    by simp
  thus ?thesis by (simp add: bienaymes_identity_2[OF assms(1,2,3)])
qed

lemma indep_var_from_indep_vars:
  assumes "i \<noteq> j"
  assumes "indep_vars (\<lambda>_. M') f {i, j}"
  shows "indep_var M' (f i) M' (f j)"
proof -
  have a:"inj (case_bool i j)" using assms(1)
    by (simp add: bool.case_eq_if inj_def)
  have b:"range (case_bool i j) = {i,j}"
    by (simp add: UNIV_bool insert_commute)
  have c:"indep_vars (\<lambda>_. M') f (range (case_bool i j))" using assms(2) b by simp

  have "True = indep_vars (\<lambda>x. M') (\<lambda>x. f (case_bool i j x)) UNIV"
    using indep_vars_reindex[OF a c]
    by (simp add:comp_def)
  also have "... = indep_vars (\<lambda>x. case_bool M' M' x) (\<lambda>x. case_bool (f i) (f j) x) UNIV"
    by (rule indep_vars_cong, auto simp:bool.case_distrib bool.case_eq_if)
  also have "... = ?thesis"
    by (simp add: indep_var_def)
  finally show ?thesis by simp
qed

lemma bienaymes_identity_pairwise_indep_2:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  assumes "\<And>J. J \<subseteq> I \<Longrightarrow> card J = 2 \<Longrightarrow> indep_vars (\<lambda> _. borel) f J"
  shows "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i \<in> I. variance (f i))"
  using assms(4)
  by (intro bienaymes_identity_pairwise_indep[OF assms(1,2,3)] indep_var_from_indep_vars, auto)

lemma bienaymes_identity_full_indep:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  assumes "indep_vars (\<lambda> _. borel) f I"
  shows "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i \<in> I. variance (f i))"
  by (intro bienaymes_identity_pairwise_indep_2[OF assms(1,2,3)] indep_vars_subset[OF assms(4)])
    auto

end

end
