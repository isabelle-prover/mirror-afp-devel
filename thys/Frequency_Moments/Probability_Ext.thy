section \<open>Probability Spaces\<close>

text \<open>Some additional results about probability spaces in addition to "HOL-Probability".\<close>

theory Probability_Ext
  imports
    "HOL-Probability.Stream_Space"
    Universal_Hash_Families.Carter_Wegman_Hash_Family
    Frequency_Moments_Preliminary_Results
begin

text \<open>Random variables that depend on disjoint sets of the components of a product space are
independent.\<close>

lemma make_ext: 
  assumes "\<And>x. P x = P (restrict x I)" 
  shows "(\<forall>x \<in> Pi I A. P x) = (\<forall>x \<in> PiE I A. P x)"
  using assms by (simp add:PiE_def Pi_def set_eq_iff, force)

lemma PiE_reindex:
  assumes "inj_on f I"
  shows "PiE I (A \<circ> f) = (\<lambda>a. restrict (a \<circ> f) I) ` PiE (f ` I) A" (is "?lhs = ?g ` ?rhs")
proof -
  have "?lhs \<subseteq> ?g` ?rhs"
  proof (rule subsetI)
    fix x
    assume a:"x \<in> Pi\<^sub>E I (A \<circ> f)"
    define y where y_def: "y = (\<lambda>k. if k \<in> f ` I then x (the_inv_into I f k) else undefined)"
    have b:"y \<in> PiE (f ` I) A" 
      using a assms the_inv_into_f_eq[OF assms]
      by (simp add: y_def PiE_iff extensional_def)
    have c: "x = (\<lambda>a. restrict (a \<circ> f) I) y"
      using a assms the_inv_into_f_eq extensional_arb
      by (intro ext, simp add:y_def PiE_iff, fastforce) 
    show "x \<in> ?g ` ?rhs" using b c by blast
  qed
  moreover have "?g ` ?rhs \<subseteq> ?lhs"
    by (rule image_subsetI, simp add:Pi_def PiE_def)
  ultimately show ?thesis by blast
qed

context prob_space
begin

lemma indep_sets_reindex:
  assumes "inj_on f I"
  shows "indep_sets A (f ` I) = indep_sets (\<lambda>i. A (f i)) I"
proof -
  have a:"\<And>J g. J \<subseteq> I \<Longrightarrow> (\<Prod>j \<in> f ` J. g j) = (\<Prod>j \<in> J. g (f j))"
    by (metis assms prod.reindex_cong subset_inj_on)

  have "J \<subseteq> I \<Longrightarrow> (\<Pi>\<^sub>E i \<in> J. A (f i)) = (\<lambda>a. restrict (a \<circ> f) J) ` PiE (f ` J) A" for J
    using assms inj_on_subset 
    by (subst PiE_reindex[symmetric]) auto

  hence b:"\<And>P J. J \<subseteq> I \<Longrightarrow>  (\<And>x. P x = P (restrict x J)) \<Longrightarrow> (\<forall>A' \<in> \<Pi>\<^sub>E i \<in> J. A (f i). P A') =  (\<forall>A'\<in>PiE (f ` J) A. P (A' \<circ> f))"
    by simp

  have c:"\<And>J. J \<subseteq> I \<Longrightarrow> finite (f ` J) = finite J" 
    by (meson assms finite_image_iff inj_on_subset)

  show ?thesis
    by (simp add:indep_sets_def all_subset_image a c)
     (simp add:make_ext b cong:restrict_cong)+
qed

lemma indep_vars_cong_AE:
  assumes "AE x in M. (\<forall>i \<in> I. X' i x = Y' i x)"
  assumes "indep_vars M' X' I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> random_variable (M' i) (Y' i)"
  shows "indep_vars M' Y' I"
proof (cases "I \<noteq> {}")
  case True

  have a: "AE x in M. (\<lambda>i\<in>I. Y' i x) = (\<lambda>i\<in>I. X' i x)"
    by (rule AE_mp[OF assms(1)], rule AE_I2, simp cong:restrict_cong)
  have b: "\<And>i. i \<in> I \<Longrightarrow> random_variable (M' i) (X' i)" 
    using assms(2) by (simp add:indep_vars_def2)
  have c: "\<And>x. x \<in> I \<Longrightarrow> AE xa in M. X' x xa = Y' x xa" 
    by (rule AE_mp[OF assms(1)], rule AE_I2, simp)

  have "distr M (Pi\<^sub>M I M') (\<lambda>x. \<lambda>i\<in>I. Y' i x) = distr M (Pi\<^sub>M I M') (\<lambda>x. \<lambda>i\<in>I. X' i x)"
    by (intro distr_cong_AE measurable_restrict a b assms(3)) auto
  also have "... =  Pi\<^sub>M I (\<lambda>i. distr M (M' i) (X' i))"
    using assms True b by (subst indep_vars_iff_distr_eq_PiM'[symmetric]) auto
  also have "... =  Pi\<^sub>M I (\<lambda>i. distr M (M' i) (Y' i))"
    by (intro PiM_cong distr_cong_AE c assms(3) b) auto
  finally have "distr M (Pi\<^sub>M I M') (\<lambda>x. \<lambda>i\<in>I. Y' i x) = Pi\<^sub>M I (\<lambda>i. distr M (M' i) (Y' i))"
    by simp

  thus ?thesis
    using True assms(3)
    by (subst indep_vars_iff_distr_eq_PiM') auto
next
  case False
  then show ?thesis
    by (simp add:indep_vars_def2 indep_sets_def)
qed

lemma indep_vars_reindex:
  assumes "inj_on f I"
  assumes "indep_vars M' X' (f ` I)"
  shows "indep_vars (M' \<circ> f) (\<lambda>k \<omega>. X' (f k) \<omega>) I"
  using assms by (simp add:indep_vars_def2 indep_sets_reindex)

lemma variance_divide:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable M f"
  shows "variance (\<lambda>\<omega>. f \<omega> / r) = variance f / r^2"
  using assms
  by (subst Bochner_Integration.integral_divide[OF assms(1)])
    (simp add:diff_divide_distrib[symmetric] power2_eq_square algebra_simps)

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

definition covariance where 
  "covariance f g = expectation (\<lambda>\<omega>. (f \<omega> - expectation f) * (g \<omega> - expectation g))"

lemma real_prod_integrable:
  fixes f g :: "'a \<Rightarrow> real"
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes sq_int: "integrable M (\<lambda>\<omega>. f \<omega>^2)" "integrable M (\<lambda>\<omega>. g \<omega>^2)"
  shows "integrable M (\<lambda>\<omega>. f \<omega> * g \<omega>)"
  unfolding integrable_iff_bounded
proof
  have "(\<integral>\<^sup>+ \<omega>. ennreal (norm (f \<omega> * g \<omega>)) \<partial>M)\<^sup>2 = (\<integral>\<^sup>+ \<omega>. ennreal \<bar>f \<omega>\<bar> * ennreal \<bar>g \<omega>\<bar> \<partial>M)\<^sup>2" 
    by (simp add: abs_mult ennreal_mult)
  also have "... \<le>  (\<integral>\<^sup>+ \<omega>. ennreal \<bar>f \<omega>\<bar>^2 \<partial>M) * (\<integral>\<^sup>+ \<omega>. ennreal \<bar>g \<omega>\<bar>^2 \<partial>M)"
    by (rule Cauchy_Schwarz_nn_integral, auto)
  also have "... < \<infinity>" 
    using sq_int by (auto simp: integrable_iff_bounded ennreal_power ennreal_mult_less_top)
  finally have "(\<integral>\<^sup>+ x. ennreal (norm (f x * g x)) \<partial>M)\<^sup>2 < \<infinity>" 
    by simp
  thus "(\<integral>\<^sup>+ x. ennreal (norm (f x * g x)) \<partial>M) < \<infinity>" 
    by (simp add: power_less_top_ennreal)
qed auto

lemma covariance_eq:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes "integrable M (\<lambda>\<omega>. f \<omega>^2)" "integrable M (\<lambda>\<omega>. g \<omega>^2)"
  shows "covariance f g = expectation (\<lambda>\<omega>. f \<omega> * g \<omega>) - expectation f * expectation g"
proof -
  have "integrable M f" using square_integrable_imp_integrable assms by auto
  moreover have "integrable M g" using square_integrable_imp_integrable assms by auto
  ultimately show ?thesis
    using assms real_prod_integrable
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
  ultimately show ?thesis using assms real_prod_integrable by (simp add: algebra_simps)
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
    by (intro Bochner_Integration.integrable_sum real_prod_integrable, auto)
  thus ?thesis
    by (simp add:power2_eq_square sum_distrib_left sum_distrib_right)
qed

lemma var_sum_1:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  shows 
    "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i \<in> I. (\<Sum>j \<in> I. covariance (f i) (f j)))"
proof -
  have a:"\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. (f i \<omega> - expectation (f i)) * (f j \<omega> - expectation (f j)))" 
    using assms covar_integrable by simp
  have "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = expectation (\<lambda>\<omega>. (\<Sum>i\<in>I. f i \<omega> - expectation (f i))\<^sup>2)"
    using square_integrable_imp_integrable[OF assms(2,3)]
    by (simp add: Bochner_Integration.integral_sum  sum_subtractf)
  also have "... = expectation (\<lambda>\<omega>. (\<Sum>i \<in> I. (\<Sum>j \<in> I. (f i \<omega> - expectation (f i)) *  (f j \<omega> - expectation (f j)))))"
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

lemma var_sum_2:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  shows "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = 
      (\<Sum>i \<in> I. variance (f i)) + (\<Sum>i \<in> I. \<Sum>j \<in> I - {i}. covariance (f i) (f j))"
proof -
  have "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i\<in>I. \<Sum>j\<in>I. covariance (f i) (f j))"
    by (simp add: var_sum_1[OF assms(1,2,3)])
  also have "... = (\<Sum>i\<in>I. covariance (f i) (f i) + (\<Sum>j\<in>I-{i}. covariance (f i) (f j)))"
    using assms by (subst sum.insert[symmetric], auto simp add:insert_absorb)
  also have "... = (\<Sum>i\<in>I. variance (f i)) +  (\<Sum>i \<in> I. (\<Sum>j\<in>I-{i}. covariance (f i) (f j)))"
    by (simp add: covar_self_eq[symmetric] sum.distrib)
  finally show ?thesis by simp
qed

lemma var_sum_pairwise_indep:
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
  thus ?thesis by (simp add: var_sum_2[OF assms(1,2,3)])
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

lemma var_sum_pairwise_indep_2:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  assumes "\<And>J. J \<subseteq> I \<Longrightarrow> card J = 2 \<Longrightarrow> indep_vars (\<lambda> _. borel) f J"
  shows "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i \<in> I. variance (f i))"
  using assms(4)
  by (intro var_sum_pairwise_indep[OF assms(1,2,3)] indep_var_from_indep_vars, auto)

lemma var_sum_all_indep:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  assumes "indep_vars (\<lambda> _. borel) f I"
  shows "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i \<in> I. variance (f i))"
  by (intro var_sum_pairwise_indep_2[OF assms(1,2,3)] indep_vars_subset[OF assms(4)],  auto)

end

end
