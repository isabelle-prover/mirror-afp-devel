theory MobiusGyrotrigonometry
  imports Main GammaFactor PoincareDisc MobiusGyroVectorSpace MoreComplex
begin

lemma m_gamma_h1:
  shows "\<ominus>\<^sub>m a \<oplus>\<^sub>m b = of_complex ((to_complex b - to_complex a) / (1 - cnj (to_complex a) * to_complex b))"
  by (metis Mobius_gyrocarrier'.of_carrier add_uminus_conv_diff complex_cnj_minus mult_minus_left ominus_m'_def ominus_m.rep_eq oplus_m'_def oplus_m.rep_eq uminus_add_conv_diff)
  
lemma m_gamma_h2:
  shows "(\<llangle>\<ominus>\<^sub>m a \<oplus>\<^sub>m b\<rrangle>)\<^sup>2 = 
         ((\<llangle>b\<rrangle>)\<^sup>2 + (\<llangle>a\<rrangle>)\<^sup>2 - (to_complex a) * cnj (to_complex b) - cnj (to_complex a) * (to_complex b)) /
         (1 - (to_complex a) * cnj (to_complex b) - cnj(to_complex a) * (to_complex b) + (\<llangle>a\<rrangle>)\<^sup>2 * (\<llangle>b\<rrangle>)\<^sup>2)"
proof-
  let ?a = "to_complex a" and ?b = "to_complex b"
  have "(?b - ?a) * cnj (?b - ?a) = (\<llangle>b\<rrangle>)\<^sup>2 + (\<llangle>a\<rrangle>)\<^sup>2 - ?a * cnj ?b - cnj ?a * ?b"
    by (simp add: cnj_cmod mult.commute norm_p.rep_eq right_diff_distrib')
  moreover 
  have "(1 - cnj ?a * ?b) * cnj (1 - cnj ?a * ?b) =
         1 - ?a * cnj ?b - cnj ?a * ?b + (\<llangle>a\<rrangle>)\<^sup>2 * (\<llangle>b\<rrangle>)\<^sup>2"
    by (smt (verit, ccfv_threshold) complex_cnj_cnj complex_cnj_diff complex_cnj_mult complex_mod_cnj complex_norm_square diff_add_eq diff_diff_eq2 left_diff_distrib mult.right_neutral mult_1 norm_mult norm_p.rep_eq power_mult_distrib right_diff_distrib)
  moreover
  have "(?b - ?a) * cnj (?b - ?a) /
        ((1 - cnj ?a * ?b) * cnj (1 - cnj ?a * ?b)) =
        \<llangle>\<ominus>\<^sub>m a \<oplus>\<^sub>m b\<rrangle> * \<llangle>\<ominus>\<^sub>m a \<oplus>\<^sub>m b\<rrangle> "
    using m_gamma_h1
    by (metis (no_types, lifting) Mobius_gyrocarrier'.gyronorm_def add.commute complex_cnj_divide complex_cnj_minus complex_norm_square mult_minus_left ominus_m'_def ominus_m.rep_eq oplus_m'_def oplus_m.rep_eq power2_eq_square times_divide_times_eq uminus_add_conv_diff)
  ultimately show ?thesis
    unfolding power2_eq_square
    by metis
qed

lemma m_gamma_h3:
  shows "1 - (\<llangle>\<ominus>\<^sub>m a \<oplus>\<^sub>m b\<rrangle>)\<^sup>2 =
        (1 - (\<llangle>b\<rrangle>)\<^sup>2 - (\<llangle>a\<rrangle>)\<^sup>2 +  (\<llangle>a\<rrangle>)\<^sup>2 * (\<llangle>b\<rrangle>)\<^sup>2) / 
        (1 - (to_complex a) * cnj (to_complex b) - cnj (to_complex a) * (to_complex b) + (\<llangle>a\<rrangle>)\<^sup>2 * (\<llangle>b\<rrangle>)\<^sup>2)" (is "?lhs = ?rhs")
proof-
  let ?a = "to_complex a" and ?b = "to_complex b"
  let ?nom = "(\<llangle>b\<rrangle>)\<^sup>2 + (\<llangle>a\<rrangle>)\<^sup>2 - ?a * cnj ?b - cnj ?a * ?b" 
  let ?den = "1 - ?a * cnj ?b - cnj ?a * ?b + (\<llangle>a\<rrangle>)\<^sup>2 * (\<llangle>b\<rrangle>)\<^sup>2"

  have "?den \<noteq> 0"
  proof-
    have "1 - cnj ?a * ?b \<noteq> 0"
      by (metis complex_mod_cnj less_irrefl mult_closed_for_unit_disc norm_lt_one norm_one norm_p.rep_eq right_minus_eq)
    moreover
    have "cnj (1 - cnj ?a * ?b) \<noteq> 0"
      using \<open>1 - cnj ?a * ?b \<noteq> 0\<close>
      by fastforce
    moreover
    have "cnj (1 - cnj ?a * ?b) = 1 - ?a * cnj ?b"
      by simp
    then have "?den = (1 - cnj ?a * ?b) * cnj (1 - cnj ?a * ?b)"
      unfolding power2_eq_square
      using complex_norm_square norm_p.rep_eq
      by (simp add: left_diff_distrib power2_eq_square right_diff_distrib)
    ultimately
    show ?thesis 
      by auto
  qed

  have "?lhs = 1 - ?nom/?den"
    using m_gamma_h2
    by simp
  also have "\<dots> = (?den - ?nom) / ?den"
    using \<open>?den \<noteq> 0\<close>
    by (simp add: field_simps)
  also have "\<dots> = (1 - (\<llangle>b\<rrangle>)\<^sup>2 - (\<llangle>a\<rrangle>)\<^sup>2 + (\<llangle>a\<rrangle>)\<^sup>2 * (\<llangle>b\<rrangle>)\<^sup>2) / ?den"
    by force
  finally show ?thesis
    .
qed

lift_definition gammma_factor_m :: "PoincareDisc \<Rightarrow> real" ("\<gamma>\<^sub>m") is gamma_factor
  .

lemma m_gamma_h4:
  shows "(\<gamma>\<^sub>m (\<ominus>\<^sub>m a \<oplus>\<^sub>m b))\<^sup>2  = 
         (1 - (to_complex a) * cnj (to_complex b) - cnj (to_complex a) * (to_complex b) + (\<llangle>a\<rrangle>)\<^sup>2 * (\<llangle>b\<rrangle>)\<^sup>2) / 
         (1 - (\<llangle>b\<rrangle>)\<^sup>2 - (\<llangle>a\<rrangle>)\<^sup>2 + (\<llangle>a\<rrangle>)\<^sup>2 * (\<llangle>b\<rrangle>)\<^sup>2)"
proof-
  have "(\<gamma>\<^sub>m (\<ominus>\<^sub>m a \<oplus>\<^sub>m b))\<^sup>2  =  1 / (1 - (\<llangle>\<ominus>\<^sub>m a \<oplus>\<^sub>m b\<rrangle>)\<^sup>2)"
  proof-
    have "\<llangle>\<ominus>\<^sub>m a \<oplus>\<^sub>m b\<rrangle> < 1" 
      using norm_lt_one by auto
    then show ?thesis  
      using gamma_factor_square_norm  norm_p.rep_eq
      by (metis gammma_factor_m.rep_eq)
  qed
  then show ?thesis
    using m_gamma_h3 by auto
qed

lemma m_gamma_equation:
  shows "(\<gamma>\<^sub>m (\<ominus>\<^sub>m a \<oplus>\<^sub>m b))\<^sup>2 = (\<gamma>\<^sub>m a)\<^sup>2 * (\<gamma>\<^sub>m b)\<^sup>2 * (1 - 2 * a \<cdot> b + (\<llangle>a\<rrangle>)\<^sup>2 * (\<llangle>b\<rrangle>)\<^sup>2)"
proof-
  let ?a = "to_complex a" and ?b = "to_complex b"
  have "2 * a \<cdot> b = ?a * cnj ?b + ?b * cnj ?a"
    using Mobius_gyrocarrier'.gyroinner_def two_inner_cnj by force
  then have "1 - 2 * a \<cdot>b + (\<llangle>a\<rrangle>)\<^sup>2 * (\<llangle>b\<rrangle>)\<^sup>2 = (1 - ?a * cnj ?b - ?b * cnj ?a + (\<llangle>a\<rrangle>)\<^sup>2 * (\<llangle>b\<rrangle>)\<^sup>2)"
    by simp

  moreover have "(\<gamma>\<^sub>m a)*(\<gamma>\<^sub>m a) = 1 / (1 - (\<llangle>a\<rrangle>)\<^sup>2)"
    by (metis gamma_factor_p_square_norm gammma_factor_m.rep_eq gammma_factor_p.rep_eq power2_eq_square)

  moreover have "(\<gamma>\<^sub>m b)*(\<gamma>\<^sub>m b) = 1 / (1 - (\<llangle>b\<rrangle>)\<^sup>2)"
    by (metis gamma_factor_p_square_norm gammma_factor_m_def gammma_factor_p_def power2_eq_square)
   
  moreover have "(1 / (1 - (\<llangle>a\<rrangle>)\<^sup>2)) * (1 / (1 - (\<llangle>b\<rrangle>)\<^sup>2)) = 1 / (1 - (\<llangle>a\<rrangle>)\<^sup>2 - (\<llangle>b\<rrangle>)\<^sup>2 + (\<llangle>a\<rrangle>)\<^sup>2 * (\<llangle>b\<rrangle>)\<^sup>2)"
    unfolding power2_eq_square
    by (simp add: field_simps)

  ultimately show ?thesis
    using m_gamma_h4 
    unfolding power2_eq_square
    by (smt (verit, del_insts) mult.commute mult_1 of_real_1 of_real_divide of_real_eq_iff of_real_mult times_divide_eq_left)
qed

lemma T8_25_help1:
   assumes "A t \<noteq> B t" "A t \<noteq> C t" "C t \<noteq> B t"
           "a = (\<llangle>Mobius_pre_gyrovector_space.get_a t\<rrangle>)\<^sup>2" "b = (\<llangle>Mobius_pre_gyrovector_space.get_b t\<rrangle>)\<^sup>2" "c = (\<llangle>Mobius_pre_gyrovector_space.get_c t\<rrangle>)\<^sup>2"
   shows "to_complex ((of_complex a) \<oplus>\<^sub>m (of_complex b) \<oplus>\<^sub>m (\<ominus>\<^sub>m (of_complex c))) =
          (a + b - c - a*b*c) / (1 + a*b - a*c - b*c)" (is "?lhs = ?rhs")
proof-
  have *: "norm a < 1" "norm b < 1" "norm c < 1"
    using assms
    by (simp add: norm_geq_zero norm_lt_one power_less_one_iff)+

  have **: "1 + a*b \<noteq> 0"
    using abs_inner_lt_1 * by fastforce

  have "(of_complex a) \<oplus>\<^sub>m (of_complex b) = of_complex ((cor a + cor b) / (1 + cnj a * b))"
    using *
    by (metis (mono_tags, lifting) Mobius_gyrocarrier'.of_carrier Mobius_gyrocarrier'.to_carrier mem_Collect_eq norm_of_real oplus_m'_def oplus_m.rep_eq real_norm_def)

  have "?lhs = 
        (((a + b) / (1 + cnj a * b)) - c) / (1 - cnj((a + b) / (1 + cnj a * b))*c)"
    using Mobius_gyrocarrier'.to_carrier * ominus_m'_def ominus_m.rep_eq oplus_m'_def oplus_m.rep_eq real_norm_def
    by auto
  also have "... = (((a + b) / (1 + a * b)) - c) / (1 - ((a + b) / (1 + a*b)) * c)"
    by simp
  also have "\<dots> = ((a + b - c - a*b*c) / (1 + a*b)) / ((1 + a*b - a*c - b*c) / (1+a*b))"
    using **
    by (simp add: field_simps)
  also have "\<dots> = ?rhs"
    using **
    by auto
  finally show ?thesis
    .
qed

lemma T8_25_help2:
  fixes t :: "PoincareDisc otriangle"
  assumes "(A t) \<noteq> (B t)" "(A t) \<noteq> (C t)" "(C t) \<noteq> (B t)"
          "a = \<llangle>Mobius_pre_gyrovector_space.get_a t\<rrangle>" "b = \<llangle>Mobius_pre_gyrovector_space.get_b t\<rrangle>" "c = \<llangle>Mobius_pre_gyrovector_space.get_c t\<rrangle>"
          "gamma = Mobius_pre_gyrovector_space.get_gamma t"
  shows "cos gamma = (a\<^sup>2 + b\<^sup>2 - c\<^sup>2 - (a*b*c)\<^sup>2) / (2 * a * b * (1 - c\<^sup>2))"
proof-
  let ?a = "Mobius_pre_gyrovector_space.get_a t" and ?b = "Mobius_pre_gyrovector_space.get_b t" and ?c = "Mobius_pre_gyrovector_space.get_c t"
  have "\<ominus>\<^sub>m ?a \<oplus>\<^sub>m ?b = gyr\<^sub>m (\<ominus>\<^sub>m (C t)) (B t) ?c"
    unfolding Mobius_pre_gyrovector_space.get_a_def Mobius_pre_gyrovector_space.get_b_def Mobius_pre_gyrovector_space.get_c_def
    by (metis gyr_PoincareDisc_def gyro_translation_2a gyroinv_PoincareDisc_def gyroplus_PoincareDisc_def)
  then have "\<llangle>\<ominus>\<^sub>m ?a \<oplus>\<^sub>m ?b\<rrangle> = \<llangle>?c\<rrangle>"
    by (simp add: mobius_gyroauto_norm)
  then have *: "\<gamma>\<^sub>m (\<ominus>\<^sub>m ?a \<oplus>\<^sub>m ?b) = \<gamma>\<^sub>m ?c"
    by (simp add: gamma_factor_def gammma_factor_m.rep_eq norm_p.rep_eq)
  then have abc: "(\<gamma>\<^sub>m (\<ominus>\<^sub>m ?a \<oplus>\<^sub>m ?b))\<^sup>2 = (\<gamma>\<^sub>m ?c)\<^sup>2"
    by presburger

  have "\<ominus>\<^sub>m (C t) \<oplus>\<^sub>m A t \<noteq> 0\<^sub>m"
    using assms
    by (simp add: Mobius_gyrogroup.gyro_equation_right)
  then have "b \<noteq> 0" 
    using assms
    unfolding Mobius_pre_gyrovector_space.get_b_def
    using gyroinv_PoincareDisc_def gyroplus_PoincareDisc_def
    by (simp add: Mobius_gyrocarrier'.gyronorm_def)

  have "\<ominus>\<^sub>m (C t) \<oplus>\<^sub>m B t \<noteq> 0\<^sub>m"
    using assms
    by (simp add: Mobius_gyrogroup.gyro_equation_right)
  then have "a \<noteq> 0" 
    using assms
    unfolding Mobius_pre_gyrovector_space.get_a_def
    using gyroinv_PoincareDisc_def gyroplus_PoincareDisc_def
    by (simp add: Mobius_gyrocarrier'.gyronorm_def)

  have "1 - c\<^sup>2 \<noteq> 0"
    using assms
    by (metis abs_norm_cancel dual_order.refl eq_iff_diff_eq_0 linorder_not_less norm_lt_one norm_p.rep_eq power2_eq_square real_sqrt_abs2 real_sqrt_one)

  have inner: "inner (to_complex ?a) (to_complex ?b) = a * b * cos gamma"
  proof-
    have "gamma = Mobius_pre_gyrovector_space.angle (C t) (A t) (B t)"
      using assms Mobius_pre_gyrovector_space.get_gamma_def
      by simp
    then have *: "gamma = arccos (inner (Mobius_pre_gyrovector_space.unit (\<ominus> (C t) \<oplus> A t)) (Mobius_pre_gyrovector_space.unit (\<ominus> (C t) \<oplus> B t)))"
      unfolding Mobius_pre_gyrovector_space.angle_def 
      by simp
    then have "cos gamma = inner (Mobius_pre_gyrovector_space.unit (\<ominus> (C t) \<oplus> A t)) (Mobius_pre_gyrovector_space.unit (\<ominus> (C t) \<oplus> B t))"
      using Mobius_pre_gyrovector_space.norm_inner_unit cos_arccos_abs
      by (metis real_norm_def)
    then have **: "cos gamma = (inner (Mobius_pre_gyrovector_space.unit ?a) (Mobius_pre_gyrovector_space.unit ?b))"
      using assms 
      unfolding Mobius_pre_gyrovector_space.get_a_def Mobius_pre_gyrovector_space.get_b_def
      by (simp add: inner_commute)
    
    have "cos(gamma) * a * b = inner (to_complex ?a) (to_complex (?b))"
      using ** \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close> assms
      unfolding Mobius_pre_gyrovector_space.unit_def
      by (metis (no_types, opaque_lifting) divide_inverse_commute inner_commute inner_scaleR_right mult.commute nonzero_mult_div_cancel_left times_divide_eq_right)
    then show ?thesis
      by (simp add: field_simps)
  qed

  have "(\<gamma>\<^sub>m (\<ominus>\<^sub>m ?a \<oplus>\<^sub>m ?b))\<^sup>2 = (\<gamma>\<^sub>m ?a)\<^sup>2 * (\<gamma>\<^sub>m ?b)\<^sup>2 * (1 - 2 * (inner (to_complex ?a) (to_complex ?b)) + (\<llangle>?a\<rrangle>)\<^sup>2 * (\<llangle>?b\<rrangle>)\<^sup>2)"
    using inner_p.rep_eq m_gamma_equation by presburger
  also have "\<dots> = (\<gamma>\<^sub>m ?a)\<^sup>2 * (\<gamma>\<^sub>m ?b)\<^sup>2 * (1 - 2 * a * b * cos(gamma) + (\<llangle>?a\<rrangle>)\<^sup>2 * (\<llangle>?b\<rrangle>)\<^sup>2)"
    using inner by simp
  finally have "(\<gamma>\<^sub>m (\<ominus>\<^sub>m ?a \<oplus>\<^sub>m ?b))\<^sup>2 / ((\<gamma>\<^sub>m ?a)\<^sup>2 * (\<gamma>\<^sub>m ?b)\<^sup>2) = 1 - 2 * a * b * cos(gamma) + (a\<^sup>2 * b\<^sup>2)"
    using gammma_factor_m_def gammma_factor_p_def assms by auto

  moreover

  have "(\<gamma>\<^sub>m (\<ominus>\<^sub>m ?a \<oplus>\<^sub>m ?b))\<^sup>2 / ((\<gamma>\<^sub>m ?a)\<^sup>2 * (\<gamma>\<^sub>m ?b)\<^sup>2) = ((1 - a\<^sup>2) * (1 - b\<^sup>2)) / (1 - c\<^sup>2)"
  proof-
    have "(\<gamma>\<^sub>m ?a)\<^sup>2  = 1 / (1 - a\<^sup>2)" "(\<gamma>\<^sub>m ?b)\<^sup>2  = 1 / (1 - b\<^sup>2)" "(\<gamma>\<^sub>m ?c)\<^sup>2  = 1 / (1 - c\<^sup>2)"
      using assms
      by (metis gamma_factor_p_square_norm gammma_factor_m_def gammma_factor_p_def)+
    then show ?thesis
      using abc
      by simp
  qed

  ultimately
  have "1 - 2 * a * b * cos(gamma) + (a\<^sup>2 * b\<^sup>2) = ((1 - a\<^sup>2) * (1 - b\<^sup>2)) / (1 - c\<^sup>2)"
    by simp
  then show ?thesis
    using \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close> \<open>1 - c\<^sup>2 \<noteq> 0\<close>
    unfolding power2_eq_square
    by (simp add: field_simps)
qed   

lemma T8_25_help3:
  fixes t :: "PoincareDisc otriangle"
  assumes "(A t) \<noteq> (B t)" "(A t) \<noteq> (C t)" "(C t) \<noteq> (B t)"
          "a = \<llangle>Mobius_pre_gyrovector_space.get_a t\<rrangle>" "b = \<llangle>Mobius_pre_gyrovector_space.get_b t\<rrangle>" "c = \<llangle>Mobius_pre_gyrovector_space.get_c t\<rrangle>"
          "gamma = Mobius_pre_gyrovector_space.get_gamma t"
          "beta_a = 1 / sqrt (1 + a\<^sup>2)" "beta_b = 1 / sqrt (1+b\<^sup>2)"
        shows "2 * beta_a\<^sup>2 * a * beta_b\<^sup>2 * b * cos gamma = (a\<^sup>2 + b\<^sup>2 - c\<^sup>2 - (a*b*c)\<^sup>2) / ((1 + a\<^sup>2) * (1 + b\<^sup>2) * (1-c\<^sup>2))"
proof-
  have "\<ominus>\<^sub>m (C t) \<oplus>\<^sub>m A t \<noteq> 0\<^sub>m"
    using assms
    by (simp add: Mobius_gyrogroup.gyro_equation_right)
  then have "b \<noteq> 0" 
    using assms
    unfolding Mobius_pre_gyrovector_space.get_b_def
    using gyroinv_PoincareDisc_def gyroplus_PoincareDisc_def
    by (simp add: Mobius_gyrocarrier'.gyronorm_def)
    
  have "\<ominus>\<^sub>m (C t) \<oplus>\<^sub>m B t \<noteq> 0\<^sub>m"
    using assms
    by (simp add: Mobius_gyrogroup.gyro_equation_right)
  then have "a \<noteq> 0" 
    using assms
    unfolding Mobius_pre_gyrovector_space.get_a_def
    using gyroinv_PoincareDisc_def gyroplus_PoincareDisc_def
    by (simp add: Mobius_gyrocarrier'.gyronorm_def)

  have "1 - c\<^sup>2 \<noteq> 0"
    using assms
    by (metis abs_norm_cancel dual_order.refl eq_iff_diff_eq_0 linorder_not_less norm_lt_one norm_p.rep_eq power2_eq_square real_sqrt_abs2 real_sqrt_one)

  have "cos gamma = (a\<^sup>2 + b\<^sup>2 - c\<^sup>2 - (a*b*c)\<^sup>2) / (2 * a * b * (1 - c\<^sup>2))"
    using T8_25_help2 assms 
    by auto
  then have "2 * a * b * cos gamma = (a\<^sup>2 + b\<^sup>2 - c\<^sup>2 - (a*b*c)\<^sup>2) / (1 - c\<^sup>2)"
    using \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close>
    by simp
  moreover have "(beta_a\<^sup>2) * (beta_b\<^sup>2)  = 1 / ((1 + a\<^sup>2) * (1 + b\<^sup>2))"
    using assms
    by (simp_all add: power2_eq_square)
  ultimately have "2 * beta_a\<^sup>2 * a * beta_b\<^sup>2 * b * cos gamma = ((a\<^sup>2 + b\<^sup>2 - c\<^sup>2 - (a*b*c)\<^sup>2) / (1 - c\<^sup>2)) * 1 / ((1 + a\<^sup>2) * (1 + b\<^sup>2))"
    by (simp add: field_simps)
  then show ?thesis
    using \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close> \<open>1 - c\<^sup>2 \<noteq> 0\<close>
    by simp
 qed


lemma T8_25_help4:
  fixes t :: "PoincareDisc otriangle"
  assumes "(A t) \<noteq> (B t)" "(A t) \<noteq> (C t)" "(C t) \<noteq> (B t)"
          "a = \<llangle>Mobius_pre_gyrovector_space.get_a t\<rrangle>" "b = \<llangle>Mobius_pre_gyrovector_space.get_b t\<rrangle>" "c = \<llangle>Mobius_pre_gyrovector_space.get_c t\<rrangle>"
          "gamma = Mobius_pre_gyrovector_space.get_gamma t"
          "beta_a = 1 / sqrt (1 + a\<^sup>2)" "beta_b = 1 / sqrt (1+b\<^sup>2)"
    shows "1 - 2 * beta_a\<^sup>2 * a * beta_b\<^sup>2 * b * cos gamma = 
          (1 + (a*b)\<^sup>2 - (a*c)\<^sup>2 - (b*c)\<^sup>2) / ((1 + a\<^sup>2) * (1 + b\<^sup>2) * (1-c\<^sup>2))"
proof-
  have "1 + a\<^sup>2 \<noteq> 0" "1 + b\<^sup>2 \<noteq> 0"
    by (metis power_one sum_power2_eq_zero_iff zero_neq_one)+

  have "1 - c\<^sup>2 \<noteq> 0"
    using assms
    by (metis eq_iff_diff_eq_0 norm_geq_zero norm_lt_one order_less_irrefl power2_eq_square real_sqrt_abs2 real_sqrt_mult_self real_sqrt_one real_sqrt_pow2)

  have "1 - 2 * beta_a\<^sup>2 * a * beta_b\<^sup>2 * b * cos gamma = 1 - (a\<^sup>2 + b\<^sup>2 - c\<^sup>2 - (a*b*c)\<^sup>2) / ((1 + a\<^sup>2) * (1 + b\<^sup>2) * (1-c\<^sup>2))" (is "?lhs = 1 - ?nom / ?den")  
    using T8_25_help3 assms
    by simp
  also have "\<dots> = (?den - ?nom) / ?den"
  proof-
    have "?den \<noteq> 0"
      using \<open>1 + a\<^sup>2 \<noteq> 0\<close> \<open>1 + b\<^sup>2 \<noteq> 0\<close> \<open>1 - c\<^sup>2 \<noteq> 0\<close>
      by simp
    then show ?thesis
      by (simp add: field_simps)
  qed
  finally show ?thesis
    by (simp add: field_simps)
qed

lemma T25_help5:
  fixes t :: "PoincareDisc otriangle"
  assumes "(A t) \<noteq> (B t)" "(A t) \<noteq> (C t)" "(C t) \<noteq> (B t)"
          "a = \<llangle>Mobius_pre_gyrovector_space.get_a t\<rrangle>" "b = \<llangle>Mobius_pre_gyrovector_space.get_b t\<rrangle>" "c = \<llangle>Mobius_pre_gyrovector_space.get_c t\<rrangle>"
          "gamma = Mobius_pre_gyrovector_space.get_gamma t"
          "beta_a = 1 / sqrt (1 + a\<^sup>2)" "beta_b = 1 / sqrt (1+b\<^sup>2)"
    shows "(2 * beta_a\<^sup>2 * a * beta_b\<^sup>2 * b * cos gamma)  / (1 - 2 * beta_a\<^sup>2 * a * beta_b\<^sup>2 * b * cos gamma) =
           to_complex ((of_complex (a\<^sup>2)) \<oplus>\<^sub>m (of_complex (b\<^sup>2)) \<oplus>\<^sub>m (\<ominus>\<^sub>m (of_complex (c\<^sup>2))))" (is "?lhs = ?rhs")
proof-
  let ?den = "(1+a\<^sup>2)*(1+b\<^sup>2)*(1-c\<^sup>2)"
  have *:"?den \<noteq> 0"
    using assms
    by (smt (verit, ccfv_threshold) divisors_zero norm_geq_zero norm_lt_one not_sum_power2_lt_zero pos2 power_less_one_iff)

  let ?nom1 = "a\<^sup>2 + b\<^sup>2 - c\<^sup>2 - (a*b*c)\<^sup>2" and ?nom2 = "1 + (a*b)\<^sup>2 - (a*c)\<^sup>2 - (b*c)\<^sup>2" 

  have "?rhs = ?nom1 / ?nom2" 
    using T8_25_help1[OF assms(1-3), of "a\<^sup>2" "b\<^sup>2" "c\<^sup>2"] assms
    by (simp add: power_mult_distrib)
  also have "\<dots> = (?nom1 / ?den) / (?nom2 / ?den)"
    using *
    by simp
  also have "\<dots> = (2 * beta_a\<^sup>2 * a * beta_b\<^sup>2 * b * cos gamma)  / (1 - 2 * beta_a\<^sup>2 * a * beta_b\<^sup>2 * b * cos gamma)"
    using T8_25_help3[OF assms] T8_25_help4[OF assms]
    by presburger
  finally show ?thesis
    by (simp add: cos_of_real)
qed


lemma T25_MobiusCosineLaw:
  fixes t :: "PoincareDisc otriangle"
  assumes "(A t) \<noteq> (B t)" "(A t) \<noteq> (C t)" "(C t) \<noteq> (B t)"
          "a = \<llangle>Mobius_pre_gyrovector_space.get_a t\<rrangle>" "b = \<llangle>Mobius_pre_gyrovector_space.get_b t\<rrangle>" "c = \<llangle>Mobius_pre_gyrovector_space.get_c t\<rrangle>"
          "gamma = Mobius_pre_gyrovector_space.get_gamma t"
          "beta_a = 1 / sqrt (1 + a\<^sup>2)" "beta_b = 1 / sqrt (1+b\<^sup>2)"
        shows "c\<^sup>2 = to_complex ((of_complex (a\<^sup>2)) \<oplus>\<^sub>m (of_complex (b\<^sup>2)) \<oplus>\<^sub>m (\<ominus>\<^sub>m (of_complex 
                (2 * beta_a\<^sup>2 * a * beta_b\<^sup>2 * b * cos(gamma) /
                (1 - 2 * beta_a\<^sup>2 * a * beta_b\<^sup>2 * b * cos gamma)))))"
proof-
  let ?a = "of_complex (a\<^sup>2)" and ?b = "of_complex (b\<^sup>2)" and ?c = "of_complex (c\<^sup>2)"
  have "norm (c\<^sup>2) < 1"
     using assms
     by (simp add: norm_geq_zero norm_lt_one power_less_one_iff)+
  then have "c\<^sup>2 = to_complex (?a \<oplus>\<^sub>m ?b \<oplus>\<^sub>m (\<ominus>\<^sub>m (?a \<oplus>\<^sub>m ?b \<oplus>\<^sub>m (\<ominus>\<^sub>m ?c))))"
    using Mobius_gyrocommutative_gyrogroup.gyroautomorphic_inverse  Mobius_gyrogroup.gyrominus_def Mobius_gyrogroup.gyro_inv_idem  Mobius_gyrogroup.oplus_ominus_cancel
    by (metis (mono_tags, lifting) Mobius_gyrocarrier'.to_carrier mem_Collect_eq norm_of_real real_norm_def)
  then show ?thesis
    using T25_help5 assms
    by auto
qed

abbreviation add_complex (infixl "\<oplus>\<^sub>m\<^sub>c" 100) where 
  "add_complex c1 c2 \<equiv> to_complex (of_complex c1 \<oplus>\<^sub>m of_complex c2)"

lemma T_MobiusPythagorean:
  fixes t :: "PoincareDisc otriangle"
  assumes "(A t) \<noteq> (B t)" "(A t) \<noteq> (C t)" "(C t) \<noteq> (B t)"
          "a = \<llangle>Mobius_pre_gyrovector_space.get_a t\<rrangle>" "b = \<llangle>Mobius_pre_gyrovector_space.get_b t\<rrangle>" "c = \<llangle>Mobius_pre_gyrovector_space.get_c t\<rrangle>"
          "gamma = Mobius_pre_gyrovector_space.get_gamma t" "gamma = pi / 2"
  shows "c\<^sup>2 = a\<^sup>2 \<oplus>\<^sub>m\<^sub>c b\<^sup>2"
  using assms T25_MobiusCosineLaw[OF assms(1-7)]
  by (metis (no_types, opaque_lifting) Mobius_gyrogroup.oplus_ominus_cancel cos_of_real_pi_half diff_self div_0 m_gamma_h1 mult.commute mult_zero_left of_real_divide of_real_numeral)

end
