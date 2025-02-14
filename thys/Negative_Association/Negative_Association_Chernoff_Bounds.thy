section \<open>Chernoff-Hoeffding Bounds\<close>

text \<open>This section shows that all the well-known Chernoff-Hoeffding bounds hold also for
negatively associated random variables. The proofs follow the derivations by
Hoeffding~\cite{hoeffding1963}, as well as, Motwani and Raghavan~\cite[Ch. 4]{motwani1995}, with the
modification that the crucial steps, where the classic proofs use independence, are replaced with
the application of Property P2 for negatively associated RV's.\<close>

theory Negative_Association_Chernoff_Bounds
  imports
    Negative_Association_Definition
    Concentration_Inequalities.McDiarmid_Inequality
    Weighted_Arithmetic_Geometric_Mean.Weighted_Arithmetic_Geometric_Mean
begin

context prob_space
begin

context
  fixes I :: "'i set"
  fixes X :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes na_X: "neg_assoc X I"
  assumes fin_I: "finite I"
begin

private lemma transfer_to_clamped_vars:
  assumes "(\<forall>i\<in>I. AE \<omega> in M. X i \<omega> \<in> {a i..b i} \<and> a i \<le> b i)"
  assumes \<X>_def: "\<X> = (\<lambda>i. clamp (a i) (b i) \<circ> X i)"
  shows "neg_assoc \<X> I" (is "?A")
    and "\<And>i. i \<in> I \<Longrightarrow> expectation (\<X> i) = expectation (X i)"
    and "\<P>(\<omega> in M. (\<Sum>i \<in> I. X i \<omega>) \<le>\<ge>\<^bsub>\<eta>\<^esub> c) = \<P>(\<omega> in M. (\<Sum>i \<in> I. \<X> i \<omega>) \<le>\<ge>\<^bsub>\<eta>\<^esub> c)" (is "?C")
    and "\<And>i \<omega>. i \<in> I \<Longrightarrow> \<X> i \<omega> \<in> {a i..b i}"
    and "\<And>i S. i \<in> I \<Longrightarrow> bounded (\<X> i ` S)"
    and "\<And>i. i \<in> I \<Longrightarrow> expectation (\<X> i) \<in> {a i..b i}"
proof -
  note [measurable] = clamp_borel
  note rv_X = neg_assoc_imp_measurable[OF na_X]

  hence rv_\<X>: "random_variable borel (\<X> i)" if "i \<in> I" for i
    unfolding \<X>_def using rv_X[OF that] by measurable

  have a:"AE x in M. \<X> i x = X i x" if "i \<in> I" for i
    unfolding \<X>_def using clamp_eqI2 by (intro AE_mp[OF bspec[OF assms(1) that] AE_I2]) auto

  hence b:"AE x in M. (\<forall>i \<in> I. \<X> i x = X i x)"
    by (intro AE_finite_allI[OF fin_I]) simp

  show "?A"
    using a by (intro neg_assoc_cong[OF fin_I rv_\<X> na_X]) force+

  show "expectation (\<X> i) = expectation (X i)" if "i \<in> I" for i
    by (intro integral_cong_AE a rv_X rv_\<X> that)

  have "{\<omega> \<in> space M. (\<Sum>i\<in>I. X i \<omega>) \<le>\<ge>\<^bsub>\<eta>\<^esub> c} \<in> events" using rv_X by (cases \<eta>) simp_all
  moreover have "{\<omega> \<in> space M. (\<Sum>i\<in>I. \<X> i \<omega>) \<le>\<ge>\<^bsub>\<eta>\<^esub> c} \<in> events" using rv_\<X> by (cases \<eta>) simp_all
  ultimately show "?C" by (intro measure_eq_AE AE_mp[OF b AE_I2]) auto

  show c:"\<X> i \<omega> \<in> {a i..b i}" if "i \<in> I" for \<omega> i
    unfolding \<X>_def comp_def using assms(1) clamp_range that by simp

  show d:"bounded (\<X> i ` S)" if "i \<in> I" for S i
    using c[OF that] assms(2) bounded_clamp by blast

  show "expectation (\<X> i) \<in> {a i..b i}" if "i \<in> I" for i
    unfolding atLeastAtMost_iff using c[OF that]  rv_\<X>[OF that]
    by (intro conjI integral_ge_const integral_le_const AE_I2 integrable_bounded d[OF that]) auto
qed

lemma ln_one_plus_x_lower_bound:
  assumes "x \<ge> (0::real)"
  shows "2*x/(2+x) \<le> ln (1 + x)"
proof -
  define v where "v x = ln(1+x) - 2 * x/ (2+x) " for x :: real
  define v' where "v' x = 1/(1+x) - 4/(2+x)^2" for x :: real

  have v_deriv: "(v has_real_derivative (v' x)) (at x)" if "x \<ge> 0" for x
    using that unfolding v_def v'_def power2_eq_square by (auto intro!:derivative_eq_intros)
  have v_deriv_nonneg: "v' x \<ge> 0" if "x \<ge> 0" for x
    using that unfolding v'_def
    by (simp add:divide_simps power2_eq_square) (simp add:algebra_simps)

  have v_mono: "v x \<le> v y" if "x \<le> y" "x \<ge> 0" for x y
    using v_deriv v_deriv_nonneg that order_trans
    by (intro DERIV_nonneg_imp_nondecreasing[OF that(1)]) blast

  have "0 = v 0" unfolding v_def by simp
  also have "\<dots> \<le> v x" using v_mono assms by auto
  finally have "v x \<ge> 0" by simp
  thus ?thesis unfolding v_def by simp
qed

text \<open>Based on Theorem~4.1 by Motwani and Raghavan~\cite{motwani1995}.\<close>

theorem multiplicative_chernoff_bound_upper:
  assumes "\<delta> > 0"
  assumes "\<And>i. i \<in> I \<Longrightarrow> AE \<omega> in M. X i \<omega> \<in> {0..1}"
  defines "\<mu> \<equiv> (\<Sum>i \<in> I. expectation (X i))"
  shows "\<P>(\<omega> in M. (\<Sum>i \<in> I. X i \<omega>) \<ge> (1+\<delta>) * \<mu>) \<le> (exp \<delta>/((1+\<delta>) powr (1+\<delta>))) powr \<mu>" (is "?L \<le> ?R")
    and "\<P>(\<omega> in M. (\<Sum>i \<in> I. X i \<omega>) \<ge> (1+\<delta>) * \<mu>) \<le> exp (-(\<delta>^2) * \<mu> / (2+\<delta>))" (is "_ \<le> ?R1")
proof -
  define \<X> where "\<X> = (\<lambda>i. clamp 0 1 \<circ> X i)"
  have transfer_to_clamped_vars_assms: "(\<forall>i\<in>I. AE \<omega> in M. X i \<omega> \<in> {0 .. 1} \<and> 0 \<le> (1::real))"
    using assms(2) by auto
  note ttcv = transfer_to_clamped_vars[OF transfer_to_clamped_vars_assms \<X>_def]
  note [measurable] = neg_assoc_imp_measurable[OF ttcv(1)]

  define t where "t = ln (1+\<delta>)"
  have t_gt_0: "t > 0" using assms(1) unfolding t_def by simp

  let  ?h = "(\<lambda>x. 1 + (exp t - 1) * x)"

  note bounded' = integrable_bounded bounded_prod bounded_vec_mult_comp bounded_intros ttcv(5)

  have int: "integrable M (\<X> i)" if "i \<in> I" for i
    using that by (intro bounded') simp_all

  have " 2*\<delta> \<le> (2+\<delta>)* ln (1 + \<delta>)"
    using assms(1) ln_one_plus_x_lower_bound[OF less_imp_le[OF assms(1)]] by (simp add:field_simps)
  hence " (1+\<delta>)*(2*\<delta>) \<le> (1 + \<delta>) *(2+\<delta>)* ln (1 + \<delta>)" using assms(1) by simp
  hence a:"(\<delta> - (1 + \<delta>) * ln (1 + \<delta>)) \<le> - (\<delta>^2)/(2+\<delta>)"
    using assms(1) by (simp add:field_simps power2_eq_square)

  have \<mu>_ge_0: "\<mu> \<ge> 0" unfolding \<mu>_def using ttcv(2,6) by (intro sum_nonneg) auto

  note \<X>_prod_mono = has_int_thatD(2)[OF neg_assoc_imp_prod_mono[OF fin_I ttcv(1), where \<eta>="Fwd"]]

  have "?L = \<P>(\<omega> in M. (\<Sum>i \<in> I. \<X> i \<omega>) \<ge> (1+\<delta>) * \<mu>)" using ttcv(3)[where \<eta>="Rev"] by simp
  also have "\<dots> = \<P>(\<omega> in M. (\<Prod>i \<in> I. exp (t * \<X> i \<omega>)) \<ge> exp (t * (1+\<delta>) * \<mu>))"
    using t_gt_0 by (simp add: sum_distrib_left[symmetric] exp_sum[OF fin_I,symmetric])
  also have "\<dots> \<le> expectation (\<lambda>\<omega>. (\<Prod>i \<in> I. exp (t * \<X> i \<omega>))) / exp (t*(1+\<delta>)*\<mu>)"
    by (intro integral_Markov_inequality_measure[where A="{}"] bounded' AE_I2 prod_nonneg fin_I)
      simp_all
  also have "\<dots> \<le> (\<Prod>i \<in> I. expectation (\<lambda>\<omega>. exp (t*\<X> i \<omega>))) / exp (t*(1+\<delta>)*\<mu>)"
    using t_gt_0 by (intro divide_right_mono \<X>_prod_mono bounded' image_subsetI monotoneI) simp_all
  also have "\<dots> = (\<Prod>i \<in> I. expectation (\<lambda>\<omega>. exp ((1-\<X> i \<omega>) *\<^sub>R 0+  \<X> i \<omega> *\<^sub>R t))) / exp (t*(1+\<delta>)*\<mu>)"
    by (simp add:ac_simps)
  also have "\<dots> \<le> (\<Prod>i \<in> I. expectation (\<lambda>\<omega>. (1-\<X> i \<omega>) * exp 0 +  \<X> i \<omega> * exp t)) / exp (t*(1+\<delta>)*\<mu>)"
    using ttcv(4)
    by (intro divide_right_mono prod_mono integral_mono conjI bounded' convex_onD[OF exp_convex])
     simp_all
  also have "\<dots> = (\<Prod>i \<in> I. ?h (expectation (\<X> i))) / exp (t*(1+\<delta>)*\<mu>)"
    using int by (simp add:algebra_simps prob_space cong:prod.cong)
  also have "\<dots> \<le> (\<Prod>i \<in> I. exp((exp t-1)* expectation (\<X> i))) / exp (t*(1+\<delta>)*\<mu>)"
    using t_gt_0 ttcv(4)
    by (intro divide_right_mono prod_mono exp_ge_add_one_self conjI add_nonneg_nonneg
        mult_nonneg_nonneg) simp_all
  also have "\<dots> = exp ((exp t-1)* \<mu>) / exp (t*(1+\<delta>)*\<mu>)"
    unfolding exp_sum[OF fin_I, symmetric] \<mu>_def by (simp add:ttcv(2) sum_distrib_left)
  also have "\<dots> = exp (\<delta> * \<mu>) / exp ( ln (1+\<delta>)*(1+\<delta>) * \<mu>)"
     using assms(1) unfolding \<mu>_def t_def by (simp add:sum_distrib_left)
  also have "\<dots> = exp \<delta> powr \<mu> / exp ( ln(1+\<delta>)*(1+\<delta>)) powr \<mu>"
    unfolding powr_def by (simp add:ac_simps)
  also have "\<dots> = ?R" using assms(1) by (subst powr_divide) (simp_all add:powr_def)
  finally show "?L \<le> ?R" by simp
  also have "\<dots> =  exp (\<mu> * ln (exp \<delta> / exp ((1 + \<delta>) * ln (1 + \<delta>))))"
    using assms unfolding powr_def by simp
  also have "\<dots> = exp (\<mu> * (\<delta> - (1 + \<delta>) * ln (1 + \<delta>)))" by (subst ln_div) simp_all
  also have "\<dots> \<le> exp (\<mu> * (-(\<delta>^2)/(2+\<delta>)))"
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono a \<mu>_ge_0)
  also have "\<dots> = ?R1" by simp
  finally show "?L \<le> ?R1" by simp
qed

lemma ln_one_minus_x_lower_bound:
  assumes "x \<in> {(0::real)..<1}"
  shows "(x^2/2-x)/(1-x) \<le> ln (1 - x)"
proof -
  define v where "v x = ln(1-x) - (x^2/2-x) / (1-x) " for x :: real
  define v' where "v' x = -1/(1-x) - (-(x^2)/2+x-1)/((1-x)^2)" for x :: real

  have v_deriv: "(v has_real_derivative (v' x)) (at x)" if "x \<in> {0..<1}" for x
    using that unfolding v_def v'_def power2_eq_square
    by (auto intro!:derivative_eq_intros simp:algebra_simps)
  have v_deriv_nonneg: "v' x \<ge> 0" if "x \<ge> 0" for x
    using that unfolding v'_def by (simp add:divide_simps power2_eq_square)

  have v_mono: "v x \<le> v y" if "x \<le> y" "x \<ge> 0" "y < 1" for x y
    using v_deriv v_deriv_nonneg that unfolding atLeastLessThan_iff
    by (intro DERIV_nonneg_imp_nondecreasing[OF that(1)])
     (metis (mono_tags, opaque_lifting) Ico_eq_Ico ivl_subset linorder_not_le order_less_irrefl)

  have "0 = v 0" unfolding v_def by simp
  also have "\<dots> \<le> v x" using v_mono assms by auto
  finally have "v x \<ge> 0" by simp
  thus ?thesis unfolding v_def by simp
qed

text \<open>Based on Theorem~4.2 by Motwani and Raghavan~\cite{motwani1995}.\<close>

theorem multiplicative_chernoff_bound_lower:
  assumes "\<delta> \<in> {0<..<1}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> AE \<omega> in M. X i \<omega> \<in> {0..1}"
  defines "\<mu> \<equiv> (\<Sum>i \<in> I. expectation (X i))"
  shows "\<P>(\<omega> in M. (\<Sum>i \<in> I. X i \<omega>) \<le> (1-\<delta>)*\<mu>) \<le> (exp (-\<delta>)/(1-\<delta>) powr (1-\<delta>)) powr \<mu>" (is "?L \<le> ?R")
    and "\<P>(\<omega> in M. (\<Sum>i \<in> I. X i \<omega>) \<le> (1-\<delta>)*\<mu>) \<le> (exp (-(\<delta>^2)*\<mu>/2))" (is "_ \<le> ?R1")
proof -
  define \<X> where "\<X> = (\<lambda>i. clamp 0 1 \<circ> X i)"
  have transfer_to_clamped_vars_assms: "(\<forall>i\<in>I. AE \<omega> in M. X i \<omega> \<in> {0 .. 1} \<and> 0 \<le> (1::real))"
    using assms(2) by auto
  note ttcv = transfer_to_clamped_vars[OF transfer_to_clamped_vars_assms \<X>_def]
  note [measurable] = neg_assoc_imp_measurable[OF ttcv(1)]

  define t where "t = ln (1-\<delta>)"
  have t_lt_0: "t < 0" using assms(1) unfolding t_def by simp

  let  ?h = "(\<lambda>x. 1 + (exp t - 1) * x)"

  note bounded' = integrable_bounded bounded_prod bounded_vec_mult_comp bounded_intros ttcv(5)

  have \<mu>_ge_0: "\<mu> \<ge> 0" unfolding \<mu>_def using ttcv(2,6) by (intro sum_nonneg) auto

  have int: "integrable M (\<X> i)" if "i \<in> I" for i
    using that by (intro bounded') simp_all

  note \<X>_prod_mono = has_int_thatD(2)[OF neg_assoc_imp_prod_mono[OF fin_I ttcv(1), where \<eta>="Rev"]]

  have 0: "0 \<le> 1 + (exp t - 1) * expectation (\<X> i)" if "i \<in> I" for i
  proof -
    have "0 \<le> 1 + (exp t - 1) * 1" by simp
    also have "\<dots> \<le>  1 + (exp t - 1) * expectation (\<X> i)"
      using t_lt_0 ttcv(6)[OF that] by (intro add_mono mult_left_mono_neg) auto
    finally show ?thesis by simp
  qed

  have "\<delta> \<in> {0..<1}" using assms(1) by simp
  from ln_one_minus_x_lower_bound[OF this]
  have "\<delta>\<^sup>2 / 2 - \<delta>  \<le>  (1 - \<delta>) * ln (1 - \<delta>)" using assms(1) by (simp add:field_simps)
  hence 1: "- \<delta> - (1 - \<delta>) * ln (1 - \<delta>) \<le> - \<delta>\<^sup>2 / 2" by (simp add:algebra_simps)

  have "?L = \<P>(\<omega> in M. (\<Sum>i \<in> I. \<X> i \<omega>) \<le> (1-\<delta>) * \<mu>)" using ttcv(3)[where \<eta>="Fwd"] by simp
  also have "\<dots> = \<P>(\<omega> in M. (\<Prod>i \<in> I. exp (t * \<X> i \<omega>)) \<ge> exp (t * (1-\<delta>) * \<mu>))"
    using t_lt_0 by (simp add: sum_distrib_left[symmetric] exp_sum[OF fin_I,symmetric])
  also have "\<dots> \<le> expectation (\<lambda>\<omega>. (\<Prod>i \<in> I. exp (t * \<X> i \<omega>))) / exp (t*(1-\<delta>)*\<mu>)"
    by (intro integral_Markov_inequality_measure[where A="{}"] bounded' AE_I2 prod_nonneg fin_I)
      simp_all
  also have "\<dots> \<le> (\<Prod>i \<in> I. expectation (\<lambda>\<omega>. exp (t*\<X> i \<omega>))) / exp (t*(1-\<delta>)*\<mu>)"
    using t_lt_0 by (intro divide_right_mono \<X>_prod_mono bounded' image_subsetI monotoneI) simp_all
  also have "\<dots> = (\<Prod>i \<in> I. expectation (\<lambda>\<omega>. exp ((1-\<X> i \<omega>) *\<^sub>R 0+  \<X> i \<omega> *\<^sub>R t))) / exp (t*(1-\<delta>)*\<mu>)"
    by (simp add:ac_simps)
  also have "\<dots> \<le> (\<Prod>i \<in> I. expectation (\<lambda>\<omega>. (1-\<X> i \<omega>) * exp 0 +  \<X> i \<omega> * exp t)) / exp (t*(1-\<delta>)*\<mu>)"
    using ttcv(4)
    by (intro divide_right_mono prod_mono integral_mono conjI bounded' convex_onD[OF exp_convex])
     simp_all
  also have "\<dots> = (\<Prod>i \<in> I. ?h (expectation (\<X> i))) / exp (t*(1-\<delta>)*\<mu>)"
    using int by (simp add:algebra_simps prob_space cong:prod.cong)
  also have "\<dots> \<le> (\<Prod>i \<in> I. exp((exp t-1)* expectation (\<X> i))) / exp (t*(1-\<delta>)*\<mu>)"
    using 0 by (intro divide_right_mono prod_mono exp_ge_add_one_self conjI) simp_all
  also have "\<dots> = exp ((exp t-1)* \<mu>) / exp (t*(1-\<delta>)*\<mu>)"
    unfolding exp_sum[OF fin_I, symmetric] \<mu>_def by (simp add:ttcv(2) sum_distrib_left)
  also have "\<dots> = exp ((-\<delta>) * \<mu>) / exp ( ln (1-\<delta>)*(1-\<delta>) * \<mu>)"
     using assms(1) unfolding \<mu>_def t_def by (simp add:sum_distrib_left)
  also have "\<dots> = exp (-\<delta>) powr \<mu> / exp ( ln(1-\<delta>)*(1-\<delta>)) powr \<mu>"
    unfolding powr_def by (simp add:ac_simps)
  also have "\<dots> = ?R" using assms(1) by (subst powr_divide) (simp_all add:powr_def)
  finally show "?L \<le> ?R" by simp
  also have "\<dots> = exp (\<mu> * (- \<delta> - (1 - \<delta>) * ln (1 - \<delta>)))"
    using assms(1) unfolding powr_def by (simp add:ln_div)
  also have "\<dots> \<le> exp (\<mu> * (-(\<delta>^2) / 2 ))"
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono \<mu>_ge_0 1)
  finally show "?L \<le> ?R1" by (simp add:ac_simps)
qed

theorem multiplicative_chernoff_bound_two_sided:
  assumes "\<delta> \<in> {0<..<1}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> AE \<omega> in M. X i \<omega> \<in> {0..1}"
  defines "\<mu> \<equiv> (\<Sum>i \<in> I. expectation (X i))"
  shows "\<P>(\<omega> in M. \<bar>(\<Sum>i \<in> I. X i \<omega>) - \<mu>\<bar> \<ge> \<delta>*\<mu>) \<le> 2*(exp (-(\<delta>^2)*\<mu>/3))" (is "?L \<le> ?R")
proof -
  define \<X> where "\<X> = (\<lambda>i. clamp 0 1 \<circ> X i)"
  have transfer_to_clamped_vars_assms: "(\<forall>i\<in>I. AE \<omega> in M. X i \<omega> \<in> {0 .. 1} \<and> 0 \<le> (1::real))"
    using assms(2) by auto
  note ttcv = transfer_to_clamped_vars[OF transfer_to_clamped_vars_assms \<X>_def]

  have \<mu>_ge_0: "\<mu> \<ge> 0" unfolding \<mu>_def using ttcv(2,6) by (intro sum_nonneg) auto

  note [measurable] = neg_assoc_imp_measurable[OF na_X]

  have "?L = \<P>(\<omega> in M. (\<Sum>i\<in>I. X i \<omega>) \<ge> (1+\<delta>)*\<mu> \<or> (\<Sum>i\<in>I. X i \<omega>) \<le> (1-\<delta>)*\<mu>)" unfolding abs_real_def
    by (intro arg_cong[where f="prob"] Collect_cong) (auto simp:algebra_simps)
  also have "\<dots> =measure M({\<omega>\<in>space M.(\<Sum>i\<in>I. X i \<omega>)\<ge>(1+\<delta>)*\<mu>}\<union>{\<omega>\<in>space M. (\<Sum>i\<in>I. X i \<omega>)\<le>(1-\<delta>)*\<mu>})"
    by (intro arg_cong[where f="prob"]) auto
  also have "\<dots> \<le> \<P>(\<omega> in M. (\<Sum>i\<in>I. X i \<omega>) \<ge> (1+\<delta>)*\<mu>) + \<P>(\<omega> in M.(\<Sum>i\<in>I. X i \<omega>) \<le> (1-\<delta>)*\<mu> )"
    by (intro measure_Un_le) measurable
  also have "\<dots> \<le> exp (-(\<delta>^2)*\<mu>/(2+\<delta>)) + exp (-(\<delta>^2)*\<mu>/2)"
    unfolding \<mu>_def using assms(1,2)
    by (intro multiplicative_chernoff_bound_lower multiplicative_chernoff_bound_upper add_mono) auto
  also have "\<dots> \<le> exp (-(\<delta>^2)*\<mu>/3) + exp (-(\<delta>^2)*\<mu>/3)"
    using assms(1) \<mu>_ge_0 by (intro iffD2[OF exp_le_cancel_iff] add_mono divide_left_mono_neg) auto
  also have "\<dots> = ?R" by simp
  finally show ?thesis by simp
qed

lemma additive_chernoff_bound_upper_aux:
  assumes "\<And>i. i\<in>I \<Longrightarrow> AE \<omega> in M. X i \<omega> \<in> {0..1}" "I \<noteq> {}"
  defines "\<mu> \<equiv> (\<Sum>i\<in>I. expectation (X i)) / real (card I)"
  assumes "\<delta> \<in> {0<..<1-\<mu>}" "\<mu> \<in> {0<..<1}"
  shows "\<P>(\<omega> in M. (\<Sum>i\<in>I. X i \<omega>) \<ge> (\<mu>+\<delta>)*real (card I)) \<le> exp (-real (card I) * KL_div (\<mu>+\<delta>) \<mu>)"
    (is "?L \<le> ?R")
proof -
  define \<X> where "\<X> = (\<lambda>i. clamp 0 1 \<circ> X i)"
  have transfer_to_clamped_vars_assms: "(\<forall>i\<in>I. AE \<omega> in M. X i \<omega> \<in> {0..1} \<and> 0 \<le> (1::real))"
    using assms(1) by auto
  note ttcv = transfer_to_clamped_vars[OF transfer_to_clamped_vars_assms \<X>_def]
  note [measurable] = neg_assoc_imp_measurable[OF ttcv(1)]

  define t :: real where "t = ln ((\<mu>+\<delta>)/\<mu>) - ln ((1-\<mu>-\<delta>)/(1-\<mu>))"
  let ?h = "\<lambda>x. 1 + (exp t - 1) * x"
  let ?n = "real (card I)"

  have n_gt_0: "?n > 0" using assms(2) fin_I by auto

  have a: "(1 - \<mu> - \<delta>) > 0" "\<mu> > 0" "1 - \<mu> > 0" "\<mu> + \<delta> > 0"
    using assms(4,5) by auto

  have "ln ((1 - \<mu> - \<delta>) / (1 - \<mu>)) < 0" using a assms(4) by (intro ln_less_zero) auto
  moreover have "ln ((\<mu> + \<delta>) / \<mu>) > 0" using a assms(4) by (intro ln_gt_zero) auto
  ultimately have t_gt_0: "t > 0" unfolding t_def by simp

  note bounded' = integrable_bounded bounded_prod bounded_vec_mult_comp bounded_intros ttcv(5)

  note \<X>_prod_mono = has_int_thatD(2)[OF neg_assoc_imp_prod_mono[OF fin_I ttcv(1), where \<eta>="Fwd"]]

  have int: "integrable M (\<X> i)" if "i \<in> I" for i
    using that by (intro bounded') simp_all

  have 0: "0 \<le> 1 + (exp t - 1) * expectation (\<X> i)" if "i \<in> I" for i
    using t_gt_0 ttcv(6)[OF that] by (intro add_nonneg_nonneg mult_nonneg_nonneg) auto

  have "1 + (exp t - 1) * \<mu> = 1 + ((\<mu> + \<delta>) * (1 - \<mu>) / (\<mu> * (1 - \<mu> - \<delta>)) - 1) * \<mu>"
    using a unfolding t_def exp_diff by simp
  also have "\<dots> =  1 + (\<delta> / (\<mu> * (1 - \<mu> - \<delta>))) * \<mu>"
    using a by (subst divide_diff_eq_iff) (simp, simp add:algebra_simps)
  also have "\<dots> = (1-\<mu>-\<delta>)/(1-\<mu>-\<delta>) + (\<delta> / (1-\<mu>-\<delta>))" using a by simp
  also have "\<dots> = (1-\<mu>) / (1-\<mu>-\<delta>)"
    unfolding add_divide_distrib[symmetric] by (simp add:algebra_simps)
  also have "\<dots> = inverse ((1-\<mu>-\<delta>) / (1-\<mu>))" using a by simp
  also have "\<dots> = exp (ln (inverse ((1-\<mu>-\<delta>) / (1-\<mu>))))" using a by simp
  also have "\<dots> = exp (- ln((1-\<mu>-\<delta>) / (1-\<mu>)))" using a by (subst ln_inverse) (simp_all)
  finally have 1: "1 + (exp t - 1) * \<mu> = exp (- ln((1-\<mu>-\<delta>) / (1-\<mu>)))" by simp

  have "?L = \<P>(\<omega> in M. (\<Sum>i \<in> I. \<X> i \<omega>) \<ge> (\<mu>+\<delta>) * ?n)" using ttcv(3)[where \<eta>="Rev"] by simp
  also have "\<dots> = \<P>(\<omega> in M. (\<Prod>i \<in> I. exp (t * \<X> i \<omega>)) \<ge> exp (t * (\<mu>+\<delta>) * ?n))"
    using t_gt_0 by (simp add: sum_distrib_left[symmetric] exp_sum[OF fin_I,symmetric])
  also have "\<dots> \<le> expectation (\<lambda>\<omega>. (\<Prod>i \<in> I. exp (t * \<X> i \<omega>))) / exp (t * (\<mu>+\<delta>) * ?n)"
    by (intro integral_Markov_inequality_measure[where A="{}"] bounded' AE_I2 prod_nonneg fin_I)
      simp_all
  also have "\<dots> \<le> (\<Prod>i \<in> I. expectation (\<lambda>\<omega>. exp (t*\<X> i \<omega>))) / exp (t * (\<mu>+\<delta>) * ?n)"
    using t_gt_0 by (intro divide_right_mono \<X>_prod_mono bounded' image_subsetI monotoneI) simp_all
  also have "\<dots> = (\<Prod>i \<in> I. expectation (\<lambda>\<omega>. exp ((1-\<X> i \<omega>) *\<^sub>R 0 + \<X> i \<omega> *\<^sub>R t))) / exp (t*(\<mu>+\<delta>)*?n)"
    by (simp add:ac_simps)
  also have "\<dots> \<le> (\<Prod>i\<in>I. expectation (\<lambda>\<omega>. (1-\<X> i \<omega>)*exp 0 + \<X> i \<omega> * exp t)) / exp (t * (\<mu>+\<delta>) * ?n)"
    using ttcv(4)
    by (intro divide_right_mono prod_mono integral_mono conjI bounded' convex_onD[OF exp_convex])
     simp_all
  also have "\<dots> = (\<Prod>i \<in> I. ?h (expectation (\<X> i))) / exp (t * (\<mu>+\<delta>) * ?n)"
    using int by (simp add:algebra_simps prob_space cong:prod.cong)
  also have "\<dots> = (root (card I) (\<Prod>i\<in>I. 1+(exp t-1)*expectation (\<X> i)))^(card I) / exp (t*(\<mu>+\<delta>)*?n)"
    using n_gt_0
    by (intro arg_cong2[where f="(/)"] real_root_pow_pos2[symmetric] prod_nonneg refl 0) auto
  also have "\<dots> \<le> ((\<Sum>i \<in> I. 1 + (exp t - 1) * expectation (\<X> i)) / ?n)^ (card I) / exp (t*(\<mu>+\<delta>)*?n)"
    by (intro divide_right_mono power_mono arithmetic_geometric_mean[OF fin_I] real_root_ge_zero
        prod_nonneg 0) simp_all
  also have "\<dots> \<le> ((\<Sum>i \<in> I. 1 + (exp t - 1) * expectation (\<X> i)) / ?n) powr ?n / exp (t*(\<mu>+\<delta>)*?n)"
    using n_gt_0 0 by (subst powr_realpow') (auto intro!:sum_nonneg divide_nonneg_pos 0)
  also have "\<dots> \<le> ((\<Sum>i \<in> I. 1 + (exp t - 1) * expectation (X i)) / ?n) powr ?n / exp (t*(\<mu>+\<delta>)*?n)"
    using ttcv(2) by (simp cong:sum.cong)
  also have "\<dots> = (1 + (exp t - 1) * \<mu>) powr ?n / exp (t*(\<mu>+\<delta>)*?n)"
    using n_gt_0 unfolding \<mu>_def sum.distrib sum_distrib_left[symmetric] by (simp add:divide_simps)
  also have "\<dots> = (1 + (exp t - 1) * \<mu>) powr ?n / exp (t*(\<mu>+\<delta>)) powr ?n"
    unfolding powr_def by simp
  also have "\<dots> = ((1 + (exp t - 1) * \<mu>)/exp(t*(\<mu>+\<delta>))) powr ?n"
    using a t_gt_0 by (auto intro: powr_divide[symmetric] add_nonneg_nonneg mult_nonneg_nonneg)
  also have "\<dots> = (exp (- ln((1-\<mu>-\<delta>) / (1-\<mu>))) * exp( -(t * (\<mu>+\<delta>)))) powr ?n"
    unfolding 1 exp_minus inverse_eq_divide by simp
  also have "\<dots> = exp ( -ln((1 - \<mu>-\<delta>)/(1 - \<mu>))- t * (\<mu>+\<delta>)) powr ?n"
    unfolding exp_add[symmetric] by simp
  also have "\<dots> = exp ( -ln((1 - \<mu>-\<delta>)/(1 - \<mu>))- (ln ((\<mu>+\<delta>)/\<mu>) - ln ((1-\<mu>-\<delta>)/(1-\<mu>)))*(\<mu>+\<delta>)) powr ?n"
    using a unfolding t_def by (simp add:divide_simps)
  also have "\<dots> = exp( -KL_div (\<mu>+\<delta>) \<mu>) powr ?n"
    using a by (subst KL_div_eq) (simp_all add:field_simps)
  also have "\<dots> = ?R" unfolding powr_def by simp
  finally show ?thesis by simp
qed

lemma additive_chernoff_bound_upper_aux_2:
  assumes "\<And>i. i\<in>I \<Longrightarrow> AE \<omega> in M. X i \<omega> \<in> {0..1}" "I \<noteq> {}"
  defines "\<mu> \<equiv> (\<Sum>i\<in>I. expectation (X i)) / real (card I)"
  assumes "\<mu> \<in> {0<..<1}"
  shows "\<P>(\<omega> in M. (\<Sum>i\<in>I. X i \<omega>) \<ge> real (card I)) \<le> exp (-real (card I) * KL_div 1 \<mu>)"
    (is "?L \<le> ?R")
proof -
  define \<X> where "\<X> = (\<lambda>i. clamp 0 1 \<circ> X i)"
  have transfer_to_clamped_vars_assms: "(\<forall>i\<in>I. AE \<omega> in M. X i \<omega> \<in> {0..1} \<and> 0 \<le> (1::real))"
    using assms(1) by auto
  note ttcv = transfer_to_clamped_vars[OF transfer_to_clamped_vars_assms \<X>_def]
  note [measurable] = neg_assoc_imp_measurable[OF ttcv(1)]

  let ?n = "real (card I)"

  have n_gt_0: "?n > 0" using assms(2) fin_I by auto

  note bounded' = integrable_bounded bounded_prod bounded_vec_mult_comp bounded_intros ttcv(5)
    bounded_max

  note \<X>_prod_mono = has_int_thatD(2)[OF neg_assoc_imp_prod_mono[OF fin_I ttcv(1), where \<eta>="Fwd"]]

  have a2:"(\<Prod>i \<in> I. max 0 (\<X> i \<omega>)) \<ge> 1" if "(\<Sum>i \<in> I. \<X> i \<omega>) \<ge> ?n" for \<omega>
  proof -
    have "(\<Sum>i \<in> I. 1 - \<X> i \<omega>) \<le> 0" using that by (simp add:sum_subtractf)
    moreover have "(\<Sum>i \<in> I. 1 - \<X> i \<omega>) \<ge> 0" using ttcv(4) by (intro sum_nonneg) simp
    ultimately have "(\<Sum>i \<in> I. 1 - \<X> i \<omega>) = 0" by simp
    with iffD1[OF sum_nonneg_eq_0_iff[OF fin_I] this]
    have "\<forall>i \<in> I. 1 - \<X> i \<omega> = 0" using ttcv(4) by simp
    hence "\<X> i \<omega> = 1" if "i \<in> I" for i using that by auto
    thus ?thesis by (intro prod_ge_1) fastforce
  qed

  have "?L = \<P>(\<omega> in M. (\<Sum>i \<in> I. \<X> i \<omega>) \<ge> ?n)" using ttcv(3)[where \<eta>="Rev"] by simp
  also have "\<dots> \<le> \<P>(\<omega> in M. (\<Prod>i \<in> I. max 0 (\<X> i \<omega>)) \<ge> 1)"
    using a2 by (intro finite_measure_mono) auto
  also have "\<dots> \<le> expectation (\<lambda>\<omega>. (\<Prod>i \<in> I. max 0 (\<X> i \<omega>))) / 1"
    by (intro integral_Markov_inequality_measure[where A="{}"] bounded' AE_I2 prod_nonneg fin_I)
      auto
  also have "\<dots> \<le> (\<Prod>i \<in> I. expectation (\<lambda>\<omega>. max 0 (\<X> i \<omega>))) / 1"
    by (intro divide_right_mono \<X>_prod_mono bounded' image_subsetI monotoneI) simp_all
  also have "\<dots> \<le> (\<Prod>i \<in> I. expectation (\<X> i))" using ttcv(4) by simp
  also have "\<dots> = (root (card I) (\<Prod>i\<in>I. expectation (\<X> i)))^(card I) "
    using n_gt_0 ttcv(6) by (intro real_root_pow_pos2[symmetric] prod_nonneg refl) auto
  also have "\<dots> \<le> ((\<Sum>i \<in> I. expectation (\<X> i)) / ?n)^ (card I)"
    using ttcv(6) by (intro power_mono arithmetic_geometric_mean[OF fin_I] real_root_ge_zero
        prod_nonneg) auto
  also have "\<dots> \<le> ((\<Sum>i \<in> I. expectation (\<X> i)) / ?n) powr ?n"
    using n_gt_0 ttcv(6) by (subst powr_realpow') (auto intro!:sum_nonneg divide_nonneg_pos)
  also have "\<dots> \<le> \<mu> powr ?n" using ttcv(2) unfolding \<mu>_def by simp
  also have "\<dots> = ?R" using assms(4) unfolding powr_def by (subst KL_div_eq) (auto simp:ln_div)
  finally show ?thesis by simp
qed

text \<open>Based on Theorem~1 by Hoeffding~\cite{hoeffding1963}.\<close>

lemma additive_chernoff_bound_upper:
  assumes "\<And>i. i\<in>I \<Longrightarrow> AE \<omega> in M. X i \<omega> \<in> {0..1}" "I \<noteq> {}"
  defines "\<mu> \<equiv> (\<Sum>i\<in>I. expectation (X i)) / real (card I)"
  assumes "\<delta> \<in> {0..1-\<mu>}" "\<mu> \<in> {0<..<1}"
  shows "\<P>(\<omega> in M. (\<Sum>i\<in>I. X i \<omega>) \<ge> (\<mu>+\<delta>)*real (card I)) \<le> exp (-real (card I) * KL_div (\<mu>+\<delta>) \<mu>)"
    (is "?L \<le> ?R")
proof -
  note [measurable] = neg_assoc_imp_measurable[OF na_X]

  let ?n = "real (card I)"
  have n_gt_0: "?n > 0" using assms fin_I by auto

  note X_prod_mono = has_int_thatD(2)[OF neg_assoc_imp_prod_mono[OF fin_I na_X, where \<eta>="Fwd"]]

  have b:"AE x in M. (\<forall>i \<in> I. X i x \<in> {0..1})"
    using assms(1) by (intro AE_finite_allI[OF fin_I]) simp
  hence c:"AE x in M. (\<Sum>i\<in>I. 1 - X i x) \<ge> 0"
    by (intro AE_mp[OF b AE_I2] impI sum_nonneg) auto

  consider (i) "\<delta>=0" | (ii) "\<delta> \<in> {0<..<1-\<mu>}" | (iii) "1-\<mu>=\<delta>" using assms(4) by fastforce
  thus ?thesis
  proof (cases)
    case i
    hence "KL_div (\<mu>+\<delta>) \<mu> = 0" using assms(4,5) by (subst KL_div_eq) auto
    thus ?thesis by simp
  next
    case ii
    thus ?thesis unfolding \<mu>_def using assms by (intro additive_chernoff_bound_upper_aux) auto
  next
    case iii
    hence a:"\<mu>+\<delta>=1" by simp
    thus ?thesis unfolding a mult_1 unfolding \<mu>_def using assms
      by (intro additive_chernoff_bound_upper_aux_2) auto
  qed
qed

text \<open>Based on Theorem~2 by Hoeffding~\cite{hoeffding1963}.\<close>

lemma hoeffding_bound_upper:
  assumes "\<And>i. i\<in>I \<Longrightarrow> a i \<le> b i"
  assumes "\<And>i. i\<in>I \<Longrightarrow> AE \<omega> in M. X i \<omega> \<in> {a i..b i}"
  defines "n \<equiv> real (card I)"
  defines "\<mu> \<equiv> (\<Sum>i\<in>I. expectation (X i))"
  assumes "\<delta> \<ge> 0" "(\<Sum>i\<in>I. (b i - a i)^2) > 0"
  shows "\<P>(\<omega> in M. (\<Sum>i\<in>I. X i \<omega>) \<ge> \<mu> + \<delta> * n) \<le> exp (-2*(n*\<delta>)^2 / (\<Sum>i\<in>I. (b i - a i)^2))"
    (is "?L \<le> ?R")
proof (cases "\<delta>=0")
  case True thus ?thesis by simp
next
  case False
  define \<X> where "\<X> = (\<lambda>i. clamp (a i) (b i) \<circ> X i)"
  have transfer_to_clamped_vars_assms: "(\<forall>i\<in>I. AE \<omega> in M. X i \<omega> \<in> {a i.. b i} \<and> a i \<le> b i)"
    using assms(1,2) by auto
  note ttcv = transfer_to_clamped_vars[OF transfer_to_clamped_vars_assms \<X>_def]
  note [measurable] = neg_assoc_imp_measurable[OF ttcv(1)]

  define s where "s = (\<Sum>i\<in>I. (b i - a i)^2)"
  have s_gt_0: "s > 0" using assms unfolding s_def by auto

  have I_ne: "I \<noteq> {}" using assms(6) by auto

  have n_gt_0: "n > 0" using I_ne fin_I unfolding n_def by auto

  define t where "t = 4 * \<delta> * n / s"

  have t_gt_0: "t > 0" unfolding t_def using False n_gt_0 s_gt_0 assms by auto

  note bounded' = integrable_bounded bounded_prod bounded_vec_mult_comp bounded_intros ttcv(5)
  note \<X>_prod_mono = has_int_thatD(2)[OF neg_assoc_imp_prod_mono[OF fin_I ttcv(1), where \<eta>="Fwd"]]

  have int: "integrable M (\<X> i)" if "i \<in> I" for i
    using that by (intro bounded') simp_all

  define \<nu> where "\<nu> i = expectation (X i)" for i
  have 1: "expectation (\<lambda>x. \<X> i x - \<nu> i) = 0" if "i \<in> I" for i
    unfolding  \<nu>_def using int[OF that] ttcv(2)[OF that] by (simp add:prob_space)

  have "?L = \<P>(\<omega> in M. (\<Sum>i \<in> I. \<X> i \<omega>) \<ge> \<mu>+\<delta> * n)" using ttcv(3)[where \<eta>="Rev"] by simp
  also have "\<dots> = \<P>(\<omega> in M. (\<Sum>i \<in> I. \<X> i \<omega> - \<nu> i) \<ge> \<delta> * n)"
    using n_gt_0 unfolding \<mu>_def \<nu>_def by (simp add:algebra_simps sum_subtractf)
  also have "\<dots> = \<P>(\<omega> in M. (\<Prod>i \<in> I. exp (t * (\<X> i \<omega> - \<nu> i))) \<ge> exp (t * \<delta> * n))"
    using t_gt_0 by (simp add: sum_distrib_left[symmetric] exp_sum[OF fin_I,symmetric])
  also have "\<dots> \<le> expectation (\<lambda>\<omega>. (\<Prod>i \<in> I. exp (t * (\<X> i \<omega> - \<nu> i)))) / exp (t * \<delta> * n)"
    by (intro integral_Markov_inequality_measure[where A="{}"] bounded' AE_I2 prod_nonneg fin_I)
      simp_all
  also have "\<dots> \<le> (\<Prod>i \<in> I. expectation (\<lambda>\<omega>. exp (t*(\<X> i \<omega> - \<nu> i)))) / exp (t * \<delta> * n)"
    using t_gt_0 by (intro divide_right_mono \<X>_prod_mono bounded' image_subsetI monotoneI) simp_all
  also have "\<dots> \<le> (\<Prod>i \<in> I. exp (t^2 * ((b i - \<nu> i) - (a i-\<nu> i))\<^sup>2 / 8)) / exp (t*\<delta>*n)"
    using ttcv(4) 1
    by (intro divide_right_mono prod_mono conjI Hoeffdings_lemma_bochner t_gt_0 AE_I2) simp_all
  also have "\<dots>  = (\<Prod>i \<in> I. exp (t^2 * (b i - a i)\<^sup>2 / 8)) / exp (t*\<delta>*n)" by simp
  also have "\<dots> =  exp( (t^2/8)* (\<Sum>i \<in> I. (b i - a i)^2)) / exp (t*\<delta>*n)"
    unfolding exp_sum[OF fin_I, symmetric] by (simp add:algebra_simps sum_distrib_left)
  also have "\<dots> =  exp( (t^2/8)* s- t*\<delta>*n)"
    unfolding exp_diff s_def by simp
  also have "\<dots> = exp(-2 *(n*\<delta>)^2 / s)"
    using s_gt_0 unfolding t_def by (simp add:divide_simps power2_eq_square)
  also have "\<dots> = ?R" unfolding s_def by simp
  finally show ?thesis by simp
qed

end

text \<open>Dual and two-sided versions of Theorem 1 and 2 by Hoeffding~\cite{hoeffding1963}.\<close>

lemma additive_chernoff_bound_lower:
  assumes "neg_assoc X I" "finite I"
  assumes "\<And>i. i\<in>I \<Longrightarrow> AE \<omega> in M. X i \<omega> \<in> {0..1}" "I \<noteq> {}"
  defines "\<mu> \<equiv> (\<Sum>i\<in>I. expectation (X i)) / real (card I)"
  assumes "\<delta> \<in> {0..\<mu>}" "\<mu> \<in> {0<..<1}"
  shows "\<P>(\<omega> in M. (\<Sum>i\<in>I. X i \<omega>) \<le> (\<mu>-\<delta>)*real (card I)) \<le> exp (-real (card I) * KL_div (\<mu>-\<delta>) \<mu>)"
    (is "?L \<le> ?R")
proof -
  note [measurable] = neg_assoc_imp_measurable[OF assms(1)]

  have int[simp]: "integrable M (X i)" if "i \<in> I" for i
    using that by (intro integrable_const_bound[where B="1"] AE_mp[OF assms(3)[OF that] AE_I2]) auto
  have n_gt_0: "real (card I) > 0" using assms by auto

  hence 0: "(1-\<mu>) = (\<Sum>i\<in>I. expectation (\<lambda>\<omega>. 1 - X i \<omega>)) / real (card I)"
    unfolding \<mu>_def by (simp add:prob_space sum_subtractf divide_simps)
  have 1: " neg_assoc (\<lambda>i \<omega>. 1 - X i \<omega>) I"
    by (intro neg_assoc_compose_simple[OF assms(2,1), where \<eta>="Rev"]) (auto intro:antimonoI)

  have 2: "\<delta> \<le> (1 - (1 - \<mu>))" "\<delta> \<ge> 0" using assms by auto
  have 3: "1-\<mu> \<in> {0<..<1}" using assms by auto
  have "?L = \<P>(\<omega> in M. (\<Sum>i\<in>I. 1 - X i \<omega>) \<ge> ((1-\<mu>)+\<delta>)*real (card I))"
    by (simp add:sum_subtractf algebra_simps)
  also have "\<dots> \<le> exp (-real (card I) * KL_div ((1-\<mu>)+\<delta>) (1-\<mu>))"
    using assms(3) 1 2 3 unfolding 0 by (intro additive_chernoff_bound_upper assms(2,4)) auto
  also have "\<dots> = exp (-real (card I) * KL_div (1-(\<mu>-\<delta>)) (1-\<mu>))" by (simp add:algebra_simps)
  also have "\<dots> = ?R" using assms(6,7) by (subst KL_div_swap) (simp_all add:algebra_simps)
  finally show ?thesis by simp
qed

lemma hoeffding_bound_lower:
  assumes "neg_assoc X I" "finite I"
  assumes "\<And>i. i\<in>I \<Longrightarrow> a i \<le> b i"
  assumes "\<And>i. i\<in>I \<Longrightarrow> AE \<omega> in M. X i \<omega> \<in> {a i..b i}"
  defines "n \<equiv> real (card I)"
  defines "\<mu> \<equiv> (\<Sum>i\<in>I. expectation (X i))"
  assumes "\<delta> \<ge> 0" "(\<Sum>i\<in>I. (b i - a i)^2) > 0"
  shows "\<P>(\<omega> in M. (\<Sum>i\<in>I. X i \<omega>) \<le> \<mu>-\<delta>*n) \<le> exp (-2*(n*\<delta>)^2 / (\<Sum>i\<in>I. (b i - a i)^2))"
    (is "?L \<le> ?R")
proof -
  have 0: "-\<mu> = (\<Sum>i\<in>I. expectation (\<lambda>\<omega>. - X i \<omega>))" unfolding \<mu>_def by (simp add:sum_negf)
  have 1: "neg_assoc (\<lambda>i \<omega>. - X i \<omega>) I"
    by (intro neg_assoc_compose_simple[OF assms(2,1), where \<eta>="Rev"]) (auto intro:antimonoI)

  have "?L = \<P>(\<omega> in M. (\<Sum>i\<in>I. -X i \<omega>) \<ge> (-\<mu>)+\<delta>*n)" by (simp add:algebra_simps sum_negf)
  also have "\<dots> \<le>  exp (-2*(n*\<delta>)^2 / (\<Sum>i\<in>I. ((-a i) - (-b i))^2))"
    using assms(3,4,8) unfolding 0 n_def by (intro hoeffding_bound_upper[OF 1] assms(2,4,7)) auto
  also have "\<dots>=  ?R" by simp
  finally show ?thesis by simp
qed

lemma hoeffding_bound_two_sided:
  assumes "neg_assoc X I" "finite I"
  assumes "\<And>i. i\<in>I \<Longrightarrow> a i \<le> b i"
  assumes "\<And>i. i\<in>I \<Longrightarrow> AE \<omega> in M. X i \<omega> \<in> {a i..b i}" "I \<noteq> {}"
  defines "n \<equiv> real (card I)"
  defines "\<mu> \<equiv> (\<Sum>i\<in>I. expectation (X i))"
  assumes "\<delta> \<ge> 0" "(\<Sum>i\<in>I. (b i - a i)^2) > 0"
  shows "\<P>(\<omega> in M. \<bar>(\<Sum>i\<in>I. X i \<omega>)-\<mu>\<bar> \<ge> \<delta>*n) \<le> 2*exp (-2*(n*\<delta>)^2 / (\<Sum>i\<in>I. (b i - a i)^2))"
    (is "?L \<le> ?R")
proof -
  note [measurable] = neg_assoc_imp_measurable[OF assms(1)]

  have "?L = \<P>(\<omega> in M. (\<Sum>i\<in>I. X i \<omega>) \<ge> \<mu>+\<delta>*n \<or> (\<Sum>i\<in>I. X i \<omega>) \<le> \<mu>-\<delta>*n )"
    unfolding abs_real_def by (intro arg_cong[where f="prob"] Collect_cong) auto
  also have "\<dots> = measure M ({\<omega>\<in>space M. (\<Sum>i\<in>I. X i \<omega>)\<ge>\<mu>+\<delta>*n}\<union>{\<omega>\<in>space M. (\<Sum>i\<in>I. X i \<omega>)\<le>\<mu>-\<delta>*n})"
    by (intro arg_cong[where f="prob"]) auto
  also have "\<dots> \<le> \<P>(\<omega> in M. (\<Sum>i\<in>I. X i \<omega>) \<ge> \<mu>+\<delta>*n) + \<P>(\<omega> in M.(\<Sum>i\<in>I. X i \<omega>) \<le> \<mu>-\<delta>*n )"
    by (intro measure_Un_le) measurable
  also have "\<dots> \<le> exp (-2*(n*\<delta>)^2 / (\<Sum>i\<in>I. (b i-a i)^2)) + exp (-2*(n*\<delta>)^2 / (\<Sum>i\<in>I. (b i-a i)^2))"
    unfolding n_def \<mu>_def by (intro hoeffding_bound_lower hoeffding_bound_upper add_mono assms)
  also have "\<dots> = ?R" by simp
  finally show ?thesis by simp
qed

end

end