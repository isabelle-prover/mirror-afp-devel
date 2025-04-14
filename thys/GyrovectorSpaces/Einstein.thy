theory Einstein
  imports Complex_Main GyroGroup GyroVectorSpace GyroVectorSpaceIsomorphism GammaFactor HOL.Real_Vector_Spaces
  MobiusGyroGroup MobiusGyroVectorSpace HOL.Transcendental
begin

text \<open>Einstein zero\<close>

definition ozero_e' :: "complex" where
  "ozero_e' = 0"

lift_definition ozero_e :: PoincareDisc  ("0\<^sub>e") is ozero_e'
  unfolding ozero_e'_def
  by simp

lemma ozero_e_ozero_m:
  shows "0\<^sub>e = 0\<^sub>m"
  using ozero_e'_def ozero_e_def ozero_m'_def ozero_m_def 
  by auto

text \<open>Einstein addition\<close>

definition oplus_e' :: "complex \<Rightarrow> complex \<Rightarrow> complex"  where
  "oplus_e' u v = (1 / (1 + inner u v)) *\<^sub>R (u + (1 / \<gamma> u) *\<^sub>R v + ((\<gamma> u / (1 + \<gamma> u)) * (inner u v)) *\<^sub>R u)"

lemma noroplus_m'_e:
  assumes "norm u < 1" "norm v <1"
  shows "norm (oplus_e' u v)^2 =
         1 / (1 + inner u v)^2 * (norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - (inner u v)^2))"
proof-
  let ?uv = "inner u v"
  let ?gu = "\<gamma> u / (1 + \<gamma> u)"

  have 1: "norm (oplus_e' u v)^2 = 
           norm (1 / (1 + ?uv))^2 * norm ((u + ((1 / \<gamma> u) *\<^sub>R v) + (?gu * ?uv) *\<^sub>R u))^2"  
    by (metis oplus_e'_def norm_scaleR power_mult_distrib real_norm_def)

  have 2: "norm (1 / (1 + ?uv))^2 =  1 / (1 + ?uv)^2"
    by (simp add: power_one_over)

  have "norm((u + ((1 / \<gamma> u) *\<^sub>R v) + (?gu * ?uv) *\<^sub>R u))^2 = 
        inner (u + (1 / \<gamma> u) *\<^sub>R v + (?gu * ?uv) *\<^sub>R u) 
              (u + (1 / \<gamma> u) *\<^sub>R v + (?gu * ?uv) *\<^sub>R u)"
    by (simp add: dot_square_norm)
  also have "\<dots> = 
        (norm u)^2 + 
        (norm ((1 / \<gamma> u) *\<^sub>R v))^2 + 
        (norm ((?gu * ?uv) *\<^sub>R u))^2 + 
        2 * inner u ((1 / \<gamma> u) *\<^sub>R v) + 
        2 * inner u ((?gu * ?uv) *\<^sub>R u) +
        2 * inner ((?gu * ?uv) *\<^sub>R u) ((1 / \<gamma> u) *\<^sub>R v)" (is "?lhs = ?a + ?b + ?c + ?d + ?e + ?f")
    by (smt (verit) inner_commute inner_right_distrib power2_norm_eq_inner)
  also have "\<dots> = (norm u)^2 + 
                  1 / (\<gamma> u)^2 * (norm v)^2 + 
                  ?gu^2 * (inner u v)^2 * (norm u)^2 +
                  2 / \<gamma> u * (inner u v) +
                  2 * ?gu * ?uv * (inner u u) +
                  2 * ?gu * ?uv * (1 / \<gamma> u) * (inner u v)"
  proof-
    have "?b = 1 / (\<gamma> u)^2 * (norm v)^2"
      by (simp add: power_divide)
    moreover
    have "?c = ?gu^2 * (inner u v)^2 * (norm u)^2"
      by (simp add: power2_eq_square)
    moreover
    have "?d = 2 / \<gamma> u * (inner u v)"
      using inner_scaleR_right
      by auto
    moreover
    have "?e = 2 * ?gu * ?uv * (inner u u)"
      using inner_scaleR_right
      by auto
    moreover
    have "?f = 2 * ?gu * ?uv * (1 / \<gamma> u) * (inner u v)"
      by force
    ultimately
    show ?thesis
      by presburger
  qed
  also have "\<dots> = 2 * inner u v + (inner u v)^2 + (norm u)^2 + (1 - (norm u)^2) * (norm v)^2"  (is "?a + ?b + ?c + ?d + ?e + ?f = ?rhs")
  proof-
    have "?a + ?b = (norm u)^2 + (1 - (norm u)^2) * (norm v)^2"
      using assms norm_square_gamma_factor
      by force

    moreover have "?d + ?e = 2 * inner u v" (is "?lhs = ?rhs")
    proof-
      have "?e = 2 * (\<gamma> u * (norm u)^2 / (1 + \<gamma> u)) * inner u v"
        by (simp add: dot_square_norm)
      moreover
      have "1 / \<gamma> u + \<gamma> u * (norm u)^2 / (1 + \<gamma> u) = 1"
        using assms(1) gamma_expression_eq_one_1
        by blast
      moreover
      have "?d + 2 * (\<gamma> u * (norm u)^2 / (1 + \<gamma> u)) * inner u v = 2 * inner u v * (1 / \<gamma> u + \<gamma> u * (norm u)^2 / (1 + \<gamma> u))"
        by (simp add: distrib_left)
      ultimately 
      show ?thesis
        by (metis mult.right_neutral)
    qed

    moreover

    have "?c + ?f = (inner u v)^2"
    proof-
      have "?c + ?f = ?gu^2 * (norm u)^2 * (inner u v)^2 + 2 * (1 / \<gamma> u) * ?gu * (inner u v)^2"
        by (simp add: mult.commute mult.left_commute power2_eq_square)
      then have "?c + ?f = ((\<gamma> u / (1 + \<gamma> u))^2 * (norm u)^2 + 2 * (1 / \<gamma> u) * (\<gamma> u / (1 + \<gamma> u))) * (inner u v)^2"
        by (simp add: ring_class.ring_distribs(2))
      moreover
      have "(\<gamma> u / (1 + \<gamma> u))^2 * (norm u)^2 + 2 * (1 / \<gamma> u) * (\<gamma> u / (1 + \<gamma> u)) = 1"
      proof -
        have "\<forall> (x::real) y n. (x / y) ^ n = x ^ n / y ^ n"
          by (simp add: power_divide)
        then show ?thesis
          using gamma_expression_eq_one_2[OF assms(1)]
          by fastforce
      qed
      ultimately
      show ?thesis
        by simp
    qed

    ultimately
    show ?thesis
      by auto
  qed
  also have "\<dots> = ((cmod (u + v))\<^sup>2 - ((cmod u)\<^sup>2 * (cmod v)\<^sup>2 - ?uv\<^sup>2))"
    unfolding dot_square_norm[symmetric]
    by (simp add: inner_commute inner_right_distrib field_simps)
  finally
  have 3: "norm ((u + ((1 / \<gamma> u) *\<^sub>R v) + (?gu * ?uv) *\<^sub>R u))^2 =
           norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - ?uv^2)"
    by simp

  show ?thesis
    using 1 2 3
    by simp
qed

lemma gamma_oplus_e':
  assumes "norm u < 1" "norm v < 1"
  shows "1 / sqrt(1 - norm (oplus_e' u v)^2) = \<gamma> u * \<gamma> v * (1 + inner u v)"
proof-
  let ?uv = "inner u v"

  have abs: "abs (1 + ?uv) = 1 + ?uv"
    using abs_inner_lt_1 assms by fastforce

  have "1 - norm (oplus_e' u v)^2 = 
        1 - 1 / (1 + ?uv)^2 * (norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - ?uv^2))"
    using assms noroplus_m'_e
    by presburger
  also have "\<dots> = ((1 + ?uv)^2 - (norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - ?uv^2))) /
                  (1 + ?uv)^2"
  proof-
    have "?uv \<noteq> -1"
      using abs_inner_lt_1[OF assms]
      by auto
    then have "(1 + ?uv)^2 \<noteq> 0"
      by auto
    then show ?thesis
      by (simp add: diff_divide_distrib)
  qed
  also have "\<dots> = (1 - (norm u)^2 - (norm v)^2 + (norm u)^2 * (norm v)^2) / (1 + ?uv)^2"
  proof-
    have "(1 + ?uv)^2  = 1 + 2*?uv + ?uv^2"
      by (simp add: power2_eq_square field_simps)
    moreover
    have "norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - ?uv^2) = 
         (norm u)^2 + 2*?uv + (norm v)^2 - (norm u)^2*(norm v)^2 + ?uv^2"
      by (smt (z3) dot_norm field_sum_of_halves)
    ultimately
    show ?thesis
      by auto
  qed
  finally have "1 / sqrt (1 - norm (oplus_e' u v)^2) = 
                1 / sqrt((1 - (norm u)^2 - (norm v)^2 + (norm u)^2*(norm v)^2) / (1 + ?uv)^2)"
    by simp
  then have 1: "1 / sqrt (1 - norm (oplus_e' u v)^2) = 
                (1 + ?uv) / sqrt (1 - (norm u)^2 - (norm v)^2 + (norm u)^2*(norm v)^2)"
    using abs
    by (simp add: real_sqrt_divide)

  have "\<gamma> u = 1 / sqrt(1 - (norm u)^2)" "\<gamma> v = 1 / sqrt(1 - (norm v)^2)"
    using assms
    by (metis gamma_factor_def)+
  then have "\<gamma> u * \<gamma> v = (1 / sqrt (1 - (norm u)^2)) * (1 / sqrt (1 - (norm v)^2))"
    by simp
  also have "\<dots> = 1 / sqrt ((1 - (norm u)^2) * (1 - (norm v)^2))"
    by (simp add: real_sqrt_mult)
  finally have 2: "\<gamma> u * \<gamma> v = 1 / sqrt ((1 - (norm u)^2 - (norm v)^2 + (norm u)^2*(norm v)^2))"
    by (simp add: field_simps power2_eq_square)

  show ?thesis
    using 1 2
    by (metis (no_types, lifting) mult_cancel_right1 times_divide_eq_left)
qed

lemma gamma_oplus_e'_not_zero:
  assumes "norm u < 1" "norm v < 1"
  shows "1 / sqrt(1 - norm(oplus_e' u v)^2) \<noteq> 0"
  using assms
  using gamma_oplus_e' gamma_factor_def gamma_factor_nonzero noroplus_m'_e
  by (smt (verit, del_insts) divide_eq_0_iff mult_eq_0_iff zero_eq_power2)

lemma oplus_e'_in_unit_disc:
  assumes "norm u < 1" "norm v < 1"
  shows "norm (oplus_e' u v) < 1"
proof-
  let ?uv = "inner u v"
  have "1 + ?uv > 0"
    using abs_inner_lt_1[OF assms]
    by fastforce
  then have "\<gamma> u * \<gamma> v * (1 + inner u v) > 0"
    using gamma_factor_positive[OF assms(1)] 
          gamma_factor_positive[OF assms(2)]
    by fastforce
  then have "0 < sqrt (1 - (cmod (oplus_e' u v))\<^sup>2)"
    using gamma_oplus_e'[OF assms] gamma_oplus_e'_not_zero[OF assms]
    by (metis zero_less_divide_1_iff)
  then have "(norm (oplus_e' u v))^2 < 1"
    using real_sqrt_gt_0_iff
    by simp
  then show ?thesis
    using real_less_rsqrt by force
qed

lemma gamma_factor_oplus_e':
  assumes "norm u < 1" "norm v < 1"
  shows "\<gamma> (oplus_e' u v) = (\<gamma> u) * (\<gamma> v) * (1 + inner u v)"
proof-
  have "\<gamma> (oplus_e' u v) = 1 / sqrt(1 - norm (oplus_e' u v)^2)"
    by (simp add: assms(1) assms(2) oplus_e'_in_unit_disc gamma_factor_def)
  then show ?thesis
    using assms
    using gamma_oplus_e' by force
qed

lift_definition oplus_e :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" (infixl "\<oplus>\<^sub>e" 100) is oplus_e'
  by (rule oplus_e'_in_unit_disc)

(* ------------------------------------------------------------------------------------- *)
  
definition ominus_e' :: "complex \<Rightarrow> complex" where
  "ominus_e' v = - v"                                      

lemma ominus_e'_in_unit_disc:
  assumes "norm z < 1"
  shows "norm (ominus_e' z) < 1"
  using assms
  unfolding ominus_e'_def
  by simp

lift_definition ominus_e :: "PoincareDisc \<Rightarrow> PoincareDisc" ("\<ominus>\<^sub>e") is ominus_e'
  using ominus_e'_in_unit_disc by blast

lemma ominus_e_ominus_m:
  shows "\<ominus>\<^sub>e a = \<ominus>\<^sub>m a"
  by (simp add: ominus_e'_def ominus_e_def ominus_m'_def ominus_m_def)

lemma ominus_e_scale:
  shows "k \<otimes> (\<ominus>\<^sub>e u) = \<ominus>\<^sub>e (k \<otimes> u)"
  using ominus_e_ominus_m ominus_m_scale by auto
  
(* ------------------------------------------------------------------------------------- *)

lemma gamma_factor_p_positive:
  shows "\<gamma>\<^sub>p a > 0"
  by transfer (simp add: gamma_factor_positive)

lemma gamma_factor_p_oplus_e:
  shows "\<gamma>\<^sub>p (u \<oplus>\<^sub>e v) = \<gamma>\<^sub>p u * \<gamma>\<^sub>p v * (1 + u \<cdot> v)"
  using gamma_factor_oplus_e' 
  by transfer blast

abbreviation \<gamma>\<^sub>2 :: "complex \<Rightarrow> real" where
  "\<gamma>\<^sub>2 u \<equiv> \<gamma> u / (1 + \<gamma> u)"

lemma norm_square_gamma_half_scale:
  assumes "norm u < 1"
  shows "(norm (\<gamma>\<^sub>2 u *\<^sub>R u))\<^sup>2 = (\<gamma> u - 1) / (1 + \<gamma> u)"
proof-
  have "(norm (\<gamma>\<^sub>2 u *\<^sub>R u))\<^sup>2 = (\<gamma>\<^sub>2 u)\<^sup>2 * (norm u)\<^sup>2"
    by (simp add: power2_eq_square)
  also have "\<dots> = (\<gamma>\<^sub>2 u)\<^sup>2 * ((\<gamma> u)\<^sup>2 - 1) / (\<gamma> u)\<^sup>2"
    using assms
    by (simp add: norm_square_gamma_factor')
  also have "\<dots> = (\<gamma> u)\<^sup>2 / (1 + \<gamma> u)\<^sup>2 * ((\<gamma> u)\<^sup>2 - 1) / (\<gamma> u)\<^sup>2"
    by (simp add: power_divide)
  also have "\<dots> = ((\<gamma> u)\<^sup>2 - 1) / (1 + \<gamma> u)\<^sup>2"
    using assms gamma_factor_positive 
    by fastforce
  also have "\<dots> = (\<gamma> u - 1) * (\<gamma> u + 1) / (1 + \<gamma> u)\<^sup>2"
    by (simp add: power2_eq_square square_diff_one_factored)
  also have "\<dots> = (\<gamma> u - 1) / (1 + \<gamma> u)"
    by (simp add: add.commute power2_eq_square)
  finally
  show ?thesis
    by simp
qed
  
lemma norm_half_square_gamma:
  assumes "norm u < 1"
  shows "(norm (half' u))\<^sup>2 = (\<gamma>\<^sub>2 u)\<^sup>2 * (cmod u)\<^sup>2"
  unfolding half'_def 
  using norm_square_gamma_half_scale assms
  by (smt (verit) divide_pos_pos gamma_factor_positive norm_scaleR power_mult_distrib)

lemma norm_half_square_gamma':
  assumes "cmod u < 1"
  shows "(norm (half' u))\<^sup>2 = (\<gamma> u - 1) / (1 + \<gamma> u)"
  using assms
  using half'_def norm_square_gamma_half_scale
  by auto

lemma inner_half_square_gamma:
  assumes "cmod u < 1" "cmod v < 1"
  shows "inner (half' u) (half' v) = \<gamma>\<^sub>2 u * \<gamma>\<^sub>2 v * inner u v"
  unfolding half'_def scaleR_conv_of_real
  by (metis inner_mult_left inner_mult_right mult.assoc)

lemma iso_me_help1:
  assumes "norm v < 1"
  shows "1 + (\<gamma> v - 1) / (1 + \<gamma> v) = 2 * \<gamma> v / (1 + \<gamma> v)"
proof-
  have "1 + \<gamma> v \<noteq> 0"
    using assms gamma_factor_positive
    by fastforce
  then show ?thesis 
    by (smt (verit, del_insts) diff_divide_distrib divide_self)
qed

lemma  iso_me_help2:
  assumes "norm v < 1"
  shows "1 - (\<gamma> v - 1) / (1 + \<gamma> v) = 2 / (1 + \<gamma> v)"
proof-
  have "1 + \<gamma> v \<noteq> 0"
    using assms gamma_factor_positive 
    by fastforce
  then show ?thesis 
    by (smt (verit, del_insts) diff_divide_distrib divide_self)
qed

lemma  iso_me_help3:
  assumes "norm v < 1" "norm u <1"
  shows "1 + ((\<gamma> v - 1) / (1 + \<gamma> v)) * ((\<gamma> u - 1) / (1 + \<gamma> u)) =
         2 * (1 + (\<gamma> u) * (\<gamma> v)) / ((1 + \<gamma> v) * (1 + \<gamma> u))" (is "?lhs = ?rhs")
proof-
  have *: "1 + \<gamma> v \<noteq> 0" "1 + \<gamma> u \<noteq> 0"
    using assms gamma_factor_positive by fastforce+
  have "(1 + \<gamma> v) * (1 + \<gamma> u) = 1 + (\<gamma> v) + (\<gamma> u) + (\<gamma> u)*(\<gamma> v)"
    by (simp add: field_simps)
  moreover 
  have "(\<gamma> v - 1) * (\<gamma> u - 1) =  (\<gamma> u)*(\<gamma> v) - (\<gamma> u) - (\<gamma> v) +1"
    by (simp add: field_simps)
  moreover 
  have "?lhs = ((1 + \<gamma> v) * (1 + \<gamma> u) + (\<gamma> u - 1) * (\<gamma> v - 1)) / ((1 + \<gamma> v) * (1 + \<gamma> u))"
    using *
    by (simp add: add_divide_distrib)
  ultimately show ?thesis 
    by (simp add: mult.commute)
qed

lemma half'_oplus_e':
  fixes u v :: complex
  assumes "cmod u < 1" "cmod v < 1"
  shows "half' (oplus_e' u v) = 
         \<gamma> u * \<gamma> v / (\<gamma> u * \<gamma> v * (1 + inner u v) + 1) * (u + (1 / \<gamma> u) * v + (\<gamma> u / (1 + \<gamma> u)) * inner u v * u)"
proof-
  have "half' (oplus_e' u v) = 
       \<gamma> u * \<gamma> v * (1 + inner u v) / (\<gamma> u * \<gamma> v * (1 + inner u v) + 1) *
       ((1 / (1 + inner u v)) * (u + (1 / \<gamma> u)*v + (\<gamma> u / (1 + \<gamma> u)) * inner u v * u))"
    unfolding half'_def
    unfolding gamma_factor_oplus_e'[OF assms] scaleR_conv_of_real
    unfolding oplus_e'_def scaleR_conv_of_real
    by simp
  then show ?thesis
    using assms
    by (smt (verit, best) ab_semigroup_mult_class.mult_ac(1) gamma_oplus_e' gamma_oplus_e'_not_zero inner_mult_left' inner_real_def mult.commute mult_eq_0_iff nonzero_mult_divide_mult_cancel_right2 of_real_1 of_real_divide of_real_mult real_inner_1_right times_divide_times_eq)
qed

lemma oplus_m'_half':
  fixes u v :: complex
  assumes "cmod u < 1" "cmod v < 1"
  shows "oplus_m' (half' u) (half' v) =
        (\<gamma> u * \<gamma> v / (\<gamma> u * \<gamma> v * (1 + inner u v) + 1)) * 
        (u + (1 / \<gamma> u) * v + (\<gamma> u / (1 + \<gamma> u) * inner u v) * u)"
proof-
  have *: "\<gamma> u \<noteq> 0" "\<gamma> v \<noteq> 0" "1 + \<gamma> u \<noteq> 0" "1 + \<gamma> v \<noteq> 0"
    using assms gamma_factor_positive 
    by fastforce+

  let ?den = "(1 + \<gamma> v) * (1 + \<gamma> u)"
  let ?DEN = "\<gamma> u * \<gamma> v * (1 + inner u v) + 1"
  let ?NOM = "u + (1 / \<gamma> u) * v + (\<gamma> u / (1 + \<gamma> u) * inner u v) * u"

  have **: "cmod (half' u) < 1" "cmod (half' v) < 1"
    using assms
    by (metis eq_onp_same_args half.rsp rel_fun_eq_onp_rel)+
  then have "oplus_m' (half' u) (half' v) = oplus_m'_alternative (half' u) (half' v)"
    by (simp add: oplus_m'_alternative)
  also have "\<dots> = ((2 * \<gamma>\<^sub>2 v + 2 * \<gamma>\<^sub>2 v * \<gamma>\<^sub>2 u * inner u v) * \<gamma>\<^sub>2 u * u  +  2 * \<gamma> v / ?den * v) /
                  (2 * \<gamma> u * \<gamma> v * inner u v / ?den + 2 * (1 + \<gamma> u * \<gamma> v) / ?den)"
  proof-
    have "(1 + 2 * inner (half' u) (half' v) + (norm (half' v))\<^sup>2) *\<^sub>R (half' u) = 
          (2 * \<gamma>\<^sub>2 v + 2 * \<gamma> v * \<gamma> u / ?den * inner u v) * \<gamma>\<^sub>2 u * u"
    proof-
      have *: "half' u = (\<gamma> u / (1 + \<gamma> u)) * u"
        by (simp add: half'_def scaleR_conv_of_real)
  
      have "1 + 2 * inner (half' u) (half' v) + (cmod (half' v))\<^sup>2 = 
            1 + 2 * (\<gamma>\<^sub>2 u * \<gamma>\<^sub>2 v * inner u v) + (\<gamma>\<^sub>2 v)\<^sup>2 * (cmod v)\<^sup>2"
        using inner_half_square_gamma norm_half_square_gamma assms
        by simp
      also have "\<dots> = 2 * \<gamma> v / (1 + \<gamma> v) + 2 * \<gamma> v * \<gamma> u / ?den * inner u v"
        using assms norm_half_square_gamma norm_square_gamma_half_scale[OF assms(2)] iso_me_help1[OF assms(2)] half'_def
        by (smt (verit, best) add_divide_distrib distrib_left inner_commute inner_left_distrib inner_real_def times_divide_times_eq)
      finally
      show ?thesis
        using *
        by (simp add: of_real_def)
    qed
    moreover
    have "(1 - (norm (half' u))\<^sup>2)   *\<^sub>R (half' v) = 
         ( 2 * (\<gamma> v) / ?den) * v"
    proof-
      have "(norm (half' u))\<^sup>2 = (\<gamma> u - 1) / (1 + \<gamma> u) "
        using assms(1) norm_half_square_gamma' by blast
      moreover have "1 - (\<gamma> u - 1) / (1 + \<gamma> u) = 2/  (1 + \<gamma> u)"
        using assms(1) iso_me_help2 by blast
      ultimately show ?thesis 
        by (simp add: half'_def mult.commute scaleR_conv_of_real)
    qed
     
    moreover
    have"1 + 2 * inner (half' u) (half' v) + (cmod (half' u))\<^sup>2 * (cmod (half' v))\<^sup>2 =
         2 * \<gamma> u * \<gamma> v * inner u v / ?den + 2 * (1 + \<gamma> u * \<gamma> v) / ?den"
      using assms inner_half_square_gamma iso_me_help3 norm_half_square_gamma'
      by (simp add: field_simps)
    ultimately
    show ?thesis
       unfolding oplus_m'_alternative_def
       by (simp add: mult.commute)
  qed
  also have "\<dots> = (2 * \<gamma> v * \<gamma> u * u + 2 * \<gamma> v * \<gamma> u * inner u v * \<gamma>\<^sub>2 u * u + 2 * \<gamma> v * v) / 
                  (2 * \<gamma> u * \<gamma> v * inner u v + (2 + 2 * \<gamma> u * \<gamma> v))"
  proof-
    have "1 / ?den \<noteq> 0"
      using *
      by simp
    moreover 
    have "(2 * \<gamma>\<^sub>2 v + 2 * \<gamma>\<^sub>2 v * \<gamma>\<^sub>2 u * inner u v) * \<gamma>\<^sub>2 u * u + 2 * \<gamma> v / ?den * v =
           (1 / ?den) * (2 * \<gamma> v * \<gamma> u * u + 2 * \<gamma> v * \<gamma> u * inner u v * \<gamma>\<^sub>2 u * u + 2 * \<gamma> v * v)"
      by (simp add: mult.commute ring_class.ring_distribs(1))
    moreover 
    have "2 * \<gamma> u * \<gamma> v * inner u v / ?den + 2 * (1 + \<gamma> u * \<gamma> v) / ?den =
          (1 / ?den) * (2 * \<gamma> u * \<gamma> v * inner u v + (2 + 2 * \<gamma> u * \<gamma> v))"
      by argo
    ultimately 
    show ?thesis
      by (smt (verit, ccfv_threshold) divide_divide_eq_left' division_ring_divide_zero eq_divide_eq inner_commute inner_real_def mult_eq_0_iff mult_eq_0_iff nonzero_mult_divide_mult_cancel_left nonzero_mult_divide_mult_cancel_left numeral_One of_real_1 of_real_1 of_real_divide of_real_inner_1 of_real_mult one_divide_eq_0_iff real_inner_1_right times_divide_times_eq)
  qed
  also have "\<dots> = 2 * (\<gamma> v * \<gamma> u * u + \<gamma> v * \<gamma> u * inner u v * \<gamma> u / (1 + \<gamma> u) * u + \<gamma> v * v) / (2 * ?DEN)"
    by (simp add: field_simps)
  also have "\<dots> = (\<gamma> v * \<gamma> u * u + \<gamma> v * \<gamma> u * inner u v * \<gamma> u / (1 + \<gamma> u) * u + \<gamma> v * v) / ?DEN"
    by (metis (no_types, opaque_lifting) nonzero_mult_divide_mult_cancel_left of_real_mult of_real_numeral zero_neq_numeral)
  also have "\<dots> = ((\<gamma> v * \<gamma> u) * u + (\<gamma> v * \<gamma> u) * (inner u v * \<gamma> u / (1 + \<gamma> u) * u) + (\<gamma> u * \<gamma> v) * (v / \<gamma> u)) / ?DEN"
    using \<open>\<gamma> u \<noteq> 0\<close>
    by simp
  also have "\<dots> = (\<gamma> v * \<gamma> u) * ?NOM / ?DEN"
  proof-
    have "(\<gamma> v * \<gamma> u) * u + (\<gamma> v * \<gamma> u) * (inner u v * \<gamma> u / (1 + \<gamma> u) * u) + (\<gamma> u * \<gamma> v) * (v / \<gamma> u) = (\<gamma> v * \<gamma> u) * ?NOM"
      by (simp add: field_simps)
    then show ?thesis
      by simp
  qed
  finally show ?thesis
    by simp
qed

lemma iso_me_oplus:
  shows "(1/2) \<otimes> (u \<oplus>\<^sub>e v) = ((1/2) \<otimes> u) \<oplus>\<^sub>m ((1/2) \<otimes> v)"
proof transfer
  fix u v
  assume *: "cmod u < 1" "cmod v < 1"
  have "otimes' (1 / 2) (oplus_e' u v) = half' (oplus_e' u v)"
    using half'[of "oplus_e' u v"] *
    unfolding otimes'_def
    using oplus_e'_in_unit_disc 
    by blast
  moreover
  have "otimes' (1 / 2) u = half' u" "otimes' (1 / 2) v = half' v"
    using half' *
    by auto
  moreover
  have "half' (oplus_e' u v) = oplus_m' (half' u) (half' v)"
    using * half'_oplus_e'[OF *] oplus_m'_half'[OF *]
    by simp
  ultimately
  show "otimes' (1 / 2) (oplus_e' u v) = oplus_m' (otimes' (1 / 2) u) (otimes' (1 / 2) v)"
    by simp
qed

lemma oplus_e_oplus_m:
  shows "u \<oplus>\<^sub>e v = 2 \<otimes> ((1/2) \<otimes> u \<oplus>\<^sub>m (1/2) \<otimes> v)"
  by (metis half iso_me_oplus otimes_2_half)

lemma iso_two_me_oplus:
  shows "2 \<otimes> (u \<oplus>\<^sub>m v) = (2 \<otimes> u) \<oplus>\<^sub>e (2 \<otimes> v)"
  by (metis Mobius_pre_gyrovector_space.double_half iso_me_oplus otimes_2_oplus_m)

lemma iso_two_me_ominus:
  shows "2 \<otimes> (\<ominus>\<^sub>m u) = \<ominus>\<^sub>e (2 \<otimes> u)"
  using ominus_e_ominus_m ominus_e_scale by auto

lemma iso_two_me_zero:
  shows "2 \<otimes> 0\<^sub>m = 0\<^sub>e"
  using Mobius_pre_gyrovector_space.times_zero gyrozero_PoincareDisc_def ozero_e_ozero_m
  by fastforce

lemma iso_two_me_bij:
  shows "bij (\<lambda> x::PoincareDisc. 2 \<otimes> x)"
  by (metis Mobius_pre_gyrovector_space.equation_solving bijI' half otimes_2_half)

definition gyr\<^sub>e::"PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" where
 "gyr\<^sub>e u v w = \<ominus>\<^sub>e (u \<oplus>\<^sub>e v) \<oplus>\<^sub>e (u \<oplus>\<^sub>e (v \<oplus>\<^sub>e w))"

(* ------------------------------------------------------------------------------------ *)

typedef PoincareDiscM = "UNIV::PoincareDisc set"
  by auto
setup_lifting type_definition_PoincareDiscM

lift_definition zero_M :: "PoincareDiscM" ("0\<^sub>M") is "0\<^sub>m" .

lift_definition ominus_M :: "PoincareDiscM \<Rightarrow> PoincareDiscM" ("\<ominus>\<^sub>M") is "(\<ominus>\<^sub>m)" .

lift_definition oplus_M :: "PoincareDiscM \<Rightarrow> PoincareDiscM \<Rightarrow> PoincareDiscM" (infixl "\<oplus>\<^sub>M" 100) is "(\<oplus>\<^sub>m)" .

lift_definition gyr_M :: "PoincareDiscM \<Rightarrow> PoincareDiscM \<Rightarrow> PoincareDiscM \<Rightarrow> PoincareDiscM" is "gyr\<^sub>m" .

lift_definition to_complex_M :: "PoincareDiscM \<Rightarrow> complex" is to_complex .

interpretation gyrogroupoid_M: gyrogroupoid zero_M oplus_M .

instantiation PoincareDiscM :: gyrogroupoid
begin
definition gyrozero_PoincareDiscM where "gyrozero_PoincareDiscM = 0\<^sub>M"
definition gyroplus_PoincareDiscM where "gyroplus_PoincareDiscM = oplus_M"
instance
  ..
end

instantiation PoincareDiscM :: gyrocommutative_gyrogroup
begin
definition gyroinv_PoincareDiscM where "gyroinv_PoincareDiscM = ominus_M"
definition gyr_PoincareDiscM where "gyr_PoincareDiscM = gyr_M"
instance proof
  fix a :: PoincareDiscM
  show "0\<^sub>g \<oplus> a = a"
    unfolding gyrozero_PoincareDiscM_def gyroplus_PoincareDiscM_def
    by transfer auto
next
  fix a :: PoincareDiscM
  show "\<ominus> a \<oplus> a = 0\<^sub>g"
    unfolding gyrozero_PoincareDiscM_def gyroplus_PoincareDiscM_def gyroinv_PoincareDiscM_def
    by transfer auto 
next
  fix a b z :: PoincareDiscM
  show "a \<oplus> (b \<oplus> z) = a \<oplus> b \<oplus> gyr a b z"
    unfolding gyroplus_PoincareDiscM_def gyr_PoincareDiscM_def
    by transfer (simp add: gyr_m_left_assoc)
next
  fix a b :: PoincareDiscM
  show "gyr a b = gyr (a \<oplus> b) b"
    unfolding gyroplus_PoincareDiscM_def gyr_PoincareDiscM_def
    using gyr_m_left_loop 
    by transfer auto
next
  fix a b :: PoincareDiscM
  show "gyroaut (gyr a b)"
    unfolding gyroplus_PoincareDiscM_def gyr_PoincareDiscM_def gyroaut_def bij_def inj_def surj_def
    by transfer (metis gyr_m_distrib gyr_m_inv)
next
  fix a b :: PoincareDiscM
  show "a \<oplus> b = gyr a b (b \<oplus> a)"
    unfolding gyroplus_PoincareDiscM_def gyr_PoincareDiscM_def
    by transfer (metis gyr_m_commute)
qed
end

typedef PoincareDiscE = "UNIV::PoincareDisc set"
  by auto
setup_lifting type_definition_PoincareDiscE

lift_definition zero_E :: "PoincareDiscE" ("0\<^sub>E") is "0\<^sub>e" .

lift_definition ominus_E :: "PoincareDiscE \<Rightarrow> PoincareDiscE" ("\<ominus>\<^sub>E") is "(\<ominus>\<^sub>e)" .

lift_definition oplus_E :: "PoincareDiscE \<Rightarrow> PoincareDiscE \<Rightarrow> PoincareDiscE" (infixl "\<oplus>\<^sub>E" 100) is "(\<oplus>\<^sub>e)" .

lift_definition gyr_E :: "PoincareDiscE \<Rightarrow> PoincareDiscE \<Rightarrow> PoincareDiscE \<Rightarrow> PoincareDiscE" is "gyr\<^sub>e" .

lift_definition to_complex_E :: "PoincareDiscE \<Rightarrow> complex" is to_complex .

lift_definition \<phi>\<^sub>M\<^sub>E :: "PoincareDiscM \<Rightarrow> PoincareDiscE" is "\<lambda> x::PoincareDisc. 2 \<otimes> x" .

interpretation Einstein_gyrogroup_iso:
  gyrogroup_isomorphism \<phi>\<^sub>M\<^sub>E zero_E oplus_E ominus_E
  rewrites 
  "Einstein_gyrogroup_iso.gyr' = gyr_E"
proof-
  show *: "gyrogroup_isomorphism \<phi>\<^sub>M\<^sub>E 0\<^sub>E (\<oplus>\<^sub>E) \<ominus>\<^sub>E"
  proof
    show "\<phi>\<^sub>M\<^sub>E 0\<^sub>g = 0\<^sub>E"
      unfolding gyrozero_PoincareDiscM_def
      by transfer (simp add: iso_two_me_zero)
  next
    fix a b
    show "\<phi>\<^sub>M\<^sub>E (a \<oplus> b) = \<phi>\<^sub>M\<^sub>E a \<oplus>\<^sub>E \<phi>\<^sub>M\<^sub>E b"
      unfolding gyroplus_PoincareDiscM_def
      by transfer (simp add: iso_two_me_oplus)
  next
    fix a
    show "\<phi>\<^sub>M\<^sub>E (\<ominus> a) = \<ominus>\<^sub>E (\<phi>\<^sub>M\<^sub>E a)"
      unfolding gyroinv_PoincareDiscM_def
      by transfer (simp add: iso_two_me_ominus)
  next
    show "bij \<phi>\<^sub>M\<^sub>E"
      unfolding bij_def
      by transfer (meson bij_betw_def iso_two_me_bij)
  qed

  show "gyrogroup_isomorphism.gyr' (\<oplus>\<^sub>E) \<ominus>\<^sub>E = gyr_E"
    unfolding gyrogroup_isomorphism.gyr'_def[OF *]
    by transfer (force simp add: gyr\<^sub>e_def)
qed


instantiation PoincareDiscE :: gyrogroupoid
begin
definition gyrozero_PoincareDiscE where "gyrozero_PoincareDiscE = 0\<^sub>E"
definition gyroplus_PoincareDiscE where "gyroplus_PoincareDiscE = oplus_E"
instance
  ..
end

instantiation PoincareDiscE :: gyrocommutative_gyrogroup
begin
definition gyroinv_PoincareDiscE where "gyroinv_PoincareDiscE = ominus_E"
definition gyr_PoincareDiscE where "gyr_PoincareDiscE = gyr_E"
instance proof
  fix a :: PoincareDiscE
  show "0\<^sub>g \<oplus> a = a"
    unfolding gyrozero_PoincareDiscE_def gyroplus_PoincareDiscE_def
    by simp
next
  fix a :: PoincareDiscE
  show "\<ominus> a \<oplus> a = 0\<^sub>g"
    unfolding gyrozero_PoincareDiscE_def gyroplus_PoincareDiscE_def gyroinv_PoincareDiscE_def
    by simp
next
  fix a b z :: PoincareDiscE
  show "a \<oplus> (b \<oplus> z) = a \<oplus> b \<oplus> gyr a b z"
    unfolding gyroplus_PoincareDiscE_def gyr_PoincareDiscE_def
    by (simp add: Einstein_gyrogroup_iso.gyro_left_assoc)
next
  fix a b :: PoincareDiscE
  show "gyr a b = gyr (a \<oplus> b) b"
    unfolding gyroplus_PoincareDiscE_def gyr_PoincareDiscE_def
    using Einstein_gyrogroup_iso.gyr_left_loop 
    by simp
next
  fix a b :: PoincareDiscE
  show "gyroaut (gyr a b)"
    unfolding gyr_PoincareDiscE_def
    by (metis Einstein_gyrogroup_iso.gyr_gyroaut gyroaut_def gyrogroupoid.gyroaut_def gyroplus_PoincareDiscE_def)
next
  fix a b :: PoincareDiscE
  show "a \<oplus> b = gyr a b (b \<oplus> a)"
    unfolding gyr_PoincareDiscE_def gyroplus_PoincareDiscE_def
    using Einstein_gyrogroup_iso.gyro_commute 
    by blast
qed

end

lift_definition scale_M :: "real \<Rightarrow> PoincareDiscM \<Rightarrow> PoincareDiscM" is "(\<otimes>)" .

lift_definition scale_E :: "real \<Rightarrow> PoincareDiscE \<Rightarrow> PoincareDiscE" is "(\<otimes>)" .


lemma gyrocarrier'M:
  shows "gyrocarrier' to_complex_M"
proof
  show "inj to_complex_M"
    by transfer simp
next
  show "to_complex_M 0\<^sub>g = 0"
    by (simp add: gyrozero_PoincareDiscM_def ozero_e_ozero_m ozero_m'_def ozero_m.rep_eq to_complex_M.abs_eq zero_M_def)
qed

lemma gyrocarrier_norms_embed'M:
  shows "gyrocarrier_norms_embed' to_complex_M"
proof
  show "cor ` gyrocarrier'.norms to_complex_M \<subseteq> gyrocarrier'.carrier to_complex_M"
    unfolding gyrocarrier'.norms_def[OF gyrocarrier'M]
    unfolding gyrocarrier'.gyronorm_def[OF gyrocarrier'M]
    unfolding gyrocarrier'.carrier_def[OF gyrocarrier'M]
    apply transfer
    using Mobius_gyrocarrier'.carrier_def Mobius_gyrocarrier_norms_embed'.norms_carrier norms
    by argo
next
  show "inj to_complex_M"
    using gyrocarrier'.inj_to_carrier gyrocarrier'M by auto
next
  show "to_complex_M 0\<^sub>g = 0"
    by (simp add: gyrocarrier'.to_carrier_zero gyrocarrier'M)
qed

lemma of_carrier_M:
  assumes "cmod z < 1"
  shows "gyrocarrier'.of_carrier to_complex_M z = Abs_PoincareDiscM (PoincareDisc.of_complex z)"
  using assms
  unfolding gyrocarrier'.of_carrier_def[OF gyrocarrier'M] to_complex_M.rep_eq
  by (metis (mono_tags, lifting) Rep_PoincareDiscM_inject f_inv_into_f mem_Collect_eq of_complex_inverse rangeI to_complex_M.abs_eq to_complex_M.rep_eq to_complex_inverse)

global_interpretation GCM: gyrocarrier_norms_embed' to_complex_M
  rewrites "GCM.norms = {x. abs x < 1}" and
           "GCM.reals = Abs_PoincareDiscM ` PoincareDisc.of_complex ` cor ` {x. \<bar>x\<bar> < 1}"
  defines of_complex_M = "gyrocarrier'.of_carrier to_complex_M"
proof-
  show *: "gyrocarrier_norms_embed' to_complex_M"
    using gyrocarrier_norms_embed'M
    by simp

  show norms: "gyrocarrier'.norms to_complex_M = {x. \<bar>x\<bar> < 1}"
    using to_complex
    unfolding gyrocarrier'.norms_def[OF gyrocarrier'M] gyrocarrier'.gyronorm_def[OF gyrocarrier'M]
    unfolding to_complex_M.rep_eq 
    by auto (metis (no_types, lifting) abs_eq_iff abs_norm_cancel mem_Collect_eq norm_of_real to_complex_M.abs_eq to_complex_M.rep_eq to_complex_cases)

  show "gyrocarrier_norms_embed'.reals to_complex_M = Abs_PoincareDiscM ` PoincareDisc.of_complex ` cor ` {x. \<bar>x\<bar> < 1}"
    using of_carrier_M
    unfolding gyrocarrier_norms_embed'.reals_def[OF gyrocarrier_norms_embed'M] norms
    by (smt (verit) Mobius_gyrocarrier_norms_embed'.norms_carrier image_cong image_image mem_Collect_eq subsetD)    
qed

lemma of_real'_M:
  assumes "abs x < 1"
  shows "GCM.of_real' x = Abs_PoincareDiscM (PoincareDisc.of_complex (cor x))"
  using assms
  by (simp add: GCM.of_real'_def of_carrier_M of_complex_M_def)

lemma to_real'_M:
  assumes "z \<in> GCM.reals"
  shows "GCM.to_real' z = Re (to_complex_M z)"
  using assms
  unfolding GCM.reals_def GCM.to_real'_def
  using GCM.norms_carrier
  by fastforce

lemma gyronorm_M_lt_1 [simp]:
  shows "abs (GCM.gyronorm a) < 1"
  using GCM.gyronorm_def to_complex to_complex_M.rep_eq by auto

lemma gyrocarrier'_norms_M [simp]:
  shows "gyrocarrier'.norms to_complex_M = GCM.norms"
  by (simp add: GCM.gyrocarrier'_axioms GCM.norms_def gyrocarrier'.norms_def)

lemma gyrocarrier_norms_embed'_reals_M [simp]:
  shows "gyrocarrier_norms_embed'.reals to_complex_M = GCM.reals"
  by (simp add: GCM.reals_def gyrocarrier_norms_embed'.reals_def gyrocarrier_norms_embed'M of_complex_M_def)

lemma gyrocarrier'E:
  shows "gyrocarrier' to_complex_E"
proof
  show "inj to_complex_E"
    by transfer simp
next
  show "to_complex_E 0\<^sub>g = 0"
    by (simp add: gyrozero_PoincareDiscE_def ozero_e_ozero_m ozero_m'_def ozero_m.rep_eq to_complex_E.abs_eq zero_E_def)
qed

lemma gyrocarrier_norms_embed'E:
  shows "gyrocarrier_norms_embed' to_complex_E"
proof
  show "inj to_complex_E"
    by transfer simp
next
  show "to_complex_E 0\<^sub>g = 0"
    by (simp add: gyrozero_PoincareDiscE_def ozero_e_ozero_m ozero_m'_def ozero_m.rep_eq to_complex_E.abs_eq zero_E_def)
next
  show "cor ` gyrocarrier'.norms to_complex_E \<subseteq> gyrocarrier'.carrier to_complex_E"
    unfolding gyrocarrier'.norms_def[OF gyrocarrier'E]
    unfolding gyrocarrier'.gyronorm_def[OF gyrocarrier'E]
    unfolding gyrocarrier'.carrier_def[OF gyrocarrier'E]
    apply transfer
    using Mobius_gyrocarrier'.carrier_def Mobius_gyrocarrier_norms_embed'.norms_carrier norms
    by argo
qed

lemma of_carrier_E:
  assumes "cmod z < 1"
  shows "gyrocarrier'.of_carrier to_complex_E z = Abs_PoincareDiscE (PoincareDisc.of_complex z)"
  using assms
  unfolding gyrocarrier'.of_carrier_def[OF gyrocarrier'E] to_complex_E.rep_eq
  by (metis (mono_tags, lifting) Rep_PoincareDiscE_inject f_inv_into_f mem_Collect_eq of_complex_inverse rangeI to_complex_E.abs_eq to_complex_E.rep_eq to_complex_inverse)

global_interpretation GCE: gyrocarrier_norms_embed' to_complex_E
  rewrites "GCE.norms = {x. abs x < 1}" and
           "GCE.reals = Abs_PoincareDiscE ` PoincareDisc.of_complex ` cor ` {x. \<bar>x\<bar> < 1}"
  defines of_complex_E = "gyrocarrier'.of_carrier to_complex_E"
proof-
  show *: "gyrocarrier_norms_embed' to_complex_E"
    using gyrocarrier_norms_embed'E
    by simp

  show norms: "gyrocarrier'.norms to_complex_E = {x. \<bar>x\<bar> < 1}"
    using to_complex
    unfolding gyrocarrier'.norms_def[OF gyrocarrier'E] gyrocarrier'.gyronorm_def[OF gyrocarrier'E]
    unfolding to_complex_E.rep_eq 
    by auto (metis (no_types, lifting) abs_eq_iff abs_norm_cancel mem_Collect_eq norm_of_real to_complex_E.abs_eq to_complex_E.rep_eq to_complex_cases)

  show "gyrocarrier_norms_embed'.reals to_complex_E = Abs_PoincareDiscE ` PoincareDisc.of_complex ` cor ` {x. \<bar>x\<bar> < 1}"
    using of_carrier_E
    unfolding gyrocarrier_norms_embed'.reals_def[OF *] norms
    by (smt (verit) Mobius_gyrocarrier_norms_embed'.norms_carrier image_cong image_image mem_Collect_eq subsetD)    
qed

lemma of_real'_E:
  assumes "abs x < 1"
  shows "GCE.of_real' x = Abs_PoincareDiscE (PoincareDisc.of_complex (cor x))"
  using assms
  by (simp add: GCE.of_real'_def of_carrier_E of_complex_E_def)

lemma to_real'_E:
  assumes "z \<in> GCE.reals"
  shows "GCE.to_real' z = Re (to_complex_E z)"
  using assms
  unfolding GCE.reals_def GCE.to_real'_def
  using GCE.norms_carrier
  by fastforce

lemma gyronorm_E_lt_1 [simp]:
  shows "abs (GCE.gyronorm a) < 1"
  using GCE.gyronorm_def to_complex to_complex_E.rep_eq by auto

lemma gyrocarrier'_norms_E [simp]:
  shows "gyrocarrier'.norms to_complex_E = GCE.norms"
  by (simp add: GCE.norms_def gyrocarrier'.norms_def gyrocarrier'E)

lemma gyrocarrier_norms_embed'_reals_E [simp]:
  shows "gyrocarrier_norms_embed'.reals to_complex_E = GCE.reals"
  by (simp add: GCE.reals_def gyrocarrier_norms_embed'.reals_def gyrocarrier_norms_embed'E of_complex_E_def)

lemma \<phi>reals_to_reals:
  shows "\<phi>\<^sub>M\<^sub>E ` gyrocarrier_norms_embed'.reals to_complex_M = gyrocarrier_norms_embed'.reals to_complex_E"
proof-
  have "\<phi>\<^sub>M\<^sub>E ` Abs_PoincareDiscM ` PoincareDisc.of_complex ` cor ` {x. \<bar>x\<bar> < 1} =
        Abs_PoincareDiscE ` PoincareDisc.of_complex ` cor ` {x. \<bar>x\<bar> < 1}"
  proof (transfer, safe)
    fix x::real
    assume "abs x < 1"
    then show "2 \<otimes> PoincareDisc.of_complex (cor x) \<in> (\<lambda>x. x) ` PoincareDisc.of_complex ` cor ` {x. \<bar>x\<bar> < 1}"
      by (smt (verit, del_insts) Mobius_gyrocarrier_norms_embed'.bij_reals_norms Mobius_gyrocarrier_norms_embed'_of_real' Mobius_gyrocarrier_norms_embed.otimes_reals bij_betw_imp_surj_on image_iff mem_Collect_eq)
  next
    fix x::real
    assume "abs x < 1"
    then show "PoincareDisc.of_complex (cor x) \<in> (\<otimes>) 2 ` (\<lambda>x. x) ` PoincareDisc.of_complex ` cor ` {x. \<bar>x\<bar> < 1}"
      by auto (smt (z3) Mobius_gyrocarrier'.of_carrier Mobius_gyrocarrier_norms_embed'.norms_carrier Mobius_gyrocarrier_norms_embed.otimes_reals Mobius_pre_gyrovector_space.double_half image_iff mem_Collect_eq of_complex_inverse subsetD)
  qed
  then show ?thesis
    by simp
qed

interpretation gyrocarrier_norms_embed_M: gyrocarrier_norms_embed to_complex_M scale_M
proof
  fix a b
  assume "a \<in> gyrocarrier_norms_embed'.reals to_complex_M" "b \<in> gyrocarrier_norms_embed'.reals to_complex_M"
  then show "a \<oplus> b \<in> gyrocarrier_norms_embed'.reals to_complex_M"
    by (smt (verit, del_insts) Abs_PoincareDiscM_inverse Mobius_gyrocarrier'.of_carrier Mobius_gyrocarrier_norms_embed'.norms_carrier Mobius_gyrocarrier_norms_embed.oplus_reals Rep_PoincareDiscM_inverse UNIV_I gyrocarrier_norms_embed'_reals_M gyroplus_PoincareDiscM_def gyroplus_PoincareDisc_def image_iff of_complex_inverse oplus_M.rep_eq subset_eq)
next
  fix a
  assume "a \<in> gyrocarrier_norms_embed'.reals to_complex_M"
  then show "\<ominus> a \<in> gyrocarrier_norms_embed'.reals to_complex_M"
    by (smt (verit, del_insts) Abs_PoincareDiscM_inverse Mobius_gyrocarrier'.of_carrier Mobius_gyrocarrier_norms_embed'.norms_carrier Mobius_gyrocarrier_norms_embed.oinv_reals  Rep_PoincareDiscM_inverse UNIV_I gyrocarrier_norms_embed'_reals_M gyroinv_PoincareDiscM_def  gyroinv_PoincareDisc_def image_iff of_complex_inverse ominus_M.rep_eq subset_eq)
next
  fix r a
  assume "a \<in> gyrocarrier_norms_embed'.reals to_complex_M"
  then show "scale_M r a \<in> gyrocarrier_norms_embed'.reals to_complex_M"
    by (smt (verit, del_insts) Abs_PoincareDiscM_inverse Mobius_gyrocarrier'.of_carrier Mobius_gyrocarrier_norms_embed'.norms_carrier Mobius_gyrocarrier_norms_embed.otimes_reals Rep_PoincareDiscM_inverse UNIV_I gyrocarrier_norms_embed'_reals_M image_iff of_complex_inverse scale_M.rep_eq subset_eq)
qed

interpretation pre_gyrovector_space_M: pre_gyrovector_space to_complex_M scale_M
proof
  fix u v a b
  show "GCM.gyroinner (gyr u v a) (gyr u v b) = GCM.gyroinner a b"
    unfolding GCM.gyroinner_def to_complex_M_def
    using GCM.gyroinner_def gyr_M.rep_eq gyr_PoincareDiscM_def inner_p.rep_eq moebius_gyroauto to_complex_M.rep_eq to_complex_M_def
    by force
next
  fix a
  show "scale_M 1 a = a"
    by (metis Mobius_pre_gyrovector_space.scale_1 Rep_PoincareDiscM_inject scale_M.rep_eq)
next
  fix r1 r2 a
  show "scale_M (r1 + r2) a = scale_M r1 a \<oplus> scale_M r2 a"
    by (metis Rep_PoincareDiscM_inject gyroplus_PoincareDiscM_def oplus_M.rep_eq otimes_oplus_m_distrib scale_M.rep_eq)
next
  fix r1 r2 a
  show "scale_M (r1 * r2) a = scale_M r1 (scale_M r2 a)"
    by (metis Rep_PoincareDiscM_inject otimes_assoc scale_M.rep_eq)
next
  fix r::real and a::PoincareDiscM
  assume "r \<noteq> 0" "a \<noteq> 0\<^sub>g"
  then show "to_complex_M (scale_M \<bar>r\<bar> a) /\<^sub>R GCM.gyronorm (scale_M r a) =
             to_complex_M a /\<^sub>R GCM.gyronorm a"
    using GCM.gyroinner_def to_complex_M_def
    by (metis Abs_PoincareDiscM_cases Abs_PoincareDiscM_inverse GCM.gyronorm_def GCM.to_carrier_zero Mobius_gyrocarrier'.gyronorm_def Mobius_gyrocarrier'.to_carrier_zero Mobius_pre_gyrovector_space.scale_prop1 scale_M.rep_eq to_complex_M.rep_eq to_complex_inverse)
next
  fix u v r a
  show "gyr u v (scale_M r a) = scale_M r (gyr u v a)"
    by (metis Mobius_pre_gyrovector_space.gyroauto_property Rep_PoincareDiscM_inject gyr_M.rep_eq gyr_PoincareDiscM_def gyr_PoincareDisc_def scale_M.rep_eq)
next
  fix r1 r2 v
  show "gyr (scale_M r1 v) (scale_M r2 v) = id"
    by (metis Rep_PoincareDiscM_inject eq_id_iff gyr_M.rep_eq gyr_PoincareDiscM_def gyr_m_gyrospace scale_M.rep_eq)
qed

interpretation gyrovector_space_norms_embed_M: gyrovector_space_norms_embed scale_M to_complex_M 
proof
  fix r a
  show "GCM.gyronorm (scale_M r a) = gyrocarrier_norms_embed_M.otimesR \<bar>r\<bar> (GCM.gyronorm a)"
    using GCM.gyroinner_def to_complex_M_def GCM.gyronorm_def 
    by (metis GCM.inj_on_of_real' GCM.norm_in_norms Mobius_gyrocarrier'.gyronorm_def Mobius_gyrocarrier_norms_embed'_of_real' Mobius_gyrocarrier_norms_embed.of_real'_otimesR Mobius_gyrovector_space.homogeneity gyrocarrier_norms_embed_M.of_real'_otimesR gyrocarrier_norms_embed_M.otimesR_norms gyronorm_M_lt_1 inj_onD of_real'_M scale_M.abs_eq scale_M.rep_eq to_complex_M.rep_eq)
next
  fix a b
  show "GCM.gyronorm (a \<oplus> b) \<le> GCM.oplusR (GCM.gyronorm a) (GCM.gyronorm b)"
    using to_complex_M_def GCM.gyronorm_def GCM.oplusR_def Mobius_gyrovector_space.gyrotriangle
    by (smt (z3) GCM.norm_in_norms Mobius_gyrocarrier'.gyronorm_def Mobius_gyrocarrier_norms_embed'_of_real'  to_complex_M.rep_eq GCM.norms_carrier GCM.of_real'_def Mobius_gyrocarrier_norms_embed'.gyrocarrier_norms_embed'_axioms Mobius_gyrocarrier_norms_embed'.to_real' gyrocarrier'.to_carrier gyrocarrier'M gyrocarrier_norms_embed'.oplusR_def gyrocarrier_norms_embed_M.of_real'_oplusR gyrocarrier_norms_embed_M.oplusR_norms gyroplus_PoincareDiscM_def gyroplus_PoincareDisc_def image_eqI o_def of_complex_M_def oplus_M.rep_eq subsetD to_complex_inverse)
qed

lemmas bij\<phi>\<^sub>M\<^sub>E = Einstein_gyrogroup_iso.\<phi>bij

lemma oplus\<phi>\<^sub>M\<^sub>E:
  shows "\<phi>\<^sub>M\<^sub>E (u \<oplus> v) = \<phi>\<^sub>M\<^sub>E u \<oplus> \<phi>\<^sub>M\<^sub>E v"
  unfolding gyroplus_PoincareDiscE_def gyroplus_PoincareDiscM_def
  apply transfer
  using iso_two_me_oplus 
  by auto

lemma scale\<phi>\<^sub>M\<^sub>E:
  shows "\<phi>\<^sub>M\<^sub>E (scale_M r u) = scale_E r (\<phi>\<^sub>M\<^sub>E u)"
  by transfer (metis mult.commute otimes_assoc)

lemma GCEoinvRMinus:
  assumes "a \<in> gyrocarrier'.norms to_complex_E"
  shows "GCE.oinvR a = - a"
proof-
  from assms have "abs a < 1" "abs (-a) < 1"
    by auto
  have "\<ominus> (GCE.of_real' a) = GCE.of_real' (- a)"
    unfolding of_real'_E[OF \<open>abs a < 1\<close>] of_real'_E[OF \<open>abs (-a) < 1\<close>]
    by (smt (verit, ccfv_SIG) \<open>\<bar>- a\<bar> < 1\<close> gyroinv_PoincareDiscE_def map_fun_apply mem_Collect_eq norm_of_real of_complex_inverse of_real_minus ominus_E.abs_eq ominus_e_ominus_m ominus_m'_def ominus_m_def)
  then show ?thesis
    unfolding GCE.oinvR_def
    using \<open>a \<in> gyrocarrier'.norms to_complex_E\<close>
    by auto
qed

lemma gyronorm\<phi>\<^sub>M\<^sub>E:
  shows "\<phi>\<^sub>M\<^sub>E (GCM.of_real' (GCM.gyronorm a)) = GCE.of_real' (GCE.gyronorm (\<phi>\<^sub>M\<^sub>E a))"
  unfolding of_real'_M[OF gyronorm_M_lt_1] of_real'_E[OF gyronorm_E_lt_1]
  unfolding GCM.gyronorm_def GCE.gyronorm_def
proof transfer
  fix a
  show "2 \<otimes> PoincareDisc.of_complex (cor (cmod (to_complex a))) =
          PoincareDisc.of_complex (cor (cmod (to_complex (2 \<otimes> a))))"
  proof-
    {
      fix a
      assume "cmod a < 1"
      moreover
      have "cmod (double' a) < 1"
        by (metis \<open>cmod a < 1\<close> double.rsp eq_onp_same_args rel_fun_eq_onp_rel)
      moreover
      have cmodcmod: "cmod (cor (cmod a)) < 1"
        using \<open>cmod a < 1\<close>
        by simp
      have "double' (cor (cmod a)) = cor (cmod (double' a))"
        using \<open>cmod a < 1\<close>
        unfolding cmod_double'[OF \<open>cmod a < 1\<close>]
        unfolding cmodcmod double'_def 
        unfolding double'_cmod[OF cmodcmod]
        by (simp add: scaleR_conv_of_real)
      ultimately
      have "PoincareDisc.of_complex (double' (to_complex (PoincareDisc.of_complex (cor (cmod a))))) =
            PoincareDisc.of_complex (cor (cmod (to_complex (PoincareDisc.of_complex (double' a)))))"
        by (simp add: of_complex_inverse)
    }
    note * = this
    show ?thesis
      unfolding double[symmetric] double_def
      by (simp, transfer, simp add: *)
  qed
qed

interpretation isoME'': gyrocarrier_isomorphism' to_complex_M to_complex_E \<phi>\<^sub>M\<^sub>E
  by unfold_locales

interpretation isoME': gyrocarrier_isomorphism to_complex_M to_complex_E \<phi>\<^sub>M\<^sub>E
proof
  show "bij \<phi>\<^sub>M\<^sub>E"
    using bij\<phi>\<^sub>M\<^sub>E by blast
next
  fix u v
  show "\<phi>\<^sub>M\<^sub>E (u \<oplus> v) = \<phi>\<^sub>M\<^sub>E u \<oplus> \<phi>\<^sub>M\<^sub>E v"
    using oplus\<phi>\<^sub>M\<^sub>E by auto
next
  fix a
  show "isoME''.\<phi>\<^sub>R (GCM.gyronorm a) = GCE.gyronorm (\<phi>\<^sub>M\<^sub>E a)"
    by (simp add: gyronorm\<phi>\<^sub>M\<^sub>E isoME''.\<phi>\<^sub>R_def)
next
  fix u v :: PoincareDiscM
  assume "u \<noteq> 0\<^sub>g" "v \<noteq> 0\<^sub>g"
  then show "inner (to_complex_E (\<phi>\<^sub>M\<^sub>E u) /\<^sub>R GCE.gyronorm (\<phi>\<^sub>M\<^sub>E u))
              (to_complex_E (\<phi>\<^sub>M\<^sub>E v) /\<^sub>R GCE.gyronorm (\<phi>\<^sub>M\<^sub>E v)) =
             inner (to_complex_M u /\<^sub>R GCM.gyronorm u) (to_complex_M v /\<^sub>R GCM.gyronorm v)"
    unfolding GCM.gyronorm_def GCE.gyronorm_def gyrozero_PoincareDiscM_def
  proof transfer
    fix u v
    assume "u \<noteq> 0\<^sub>m" "v \<noteq> 0\<^sub>m"
    then show "inner (to_complex (2 \<otimes> u) /\<^sub>R cmod (to_complex (2 \<otimes> u)))
                (to_complex (2 \<otimes> v) /\<^sub>R cmod (to_complex (2 \<otimes> v))) =
               inner (to_complex u /\<^sub>R cmod (to_complex u)) (to_complex v /\<^sub>R cmod (to_complex v))"
      unfolding double[symmetric]
    proof transfer
      fix u v
      assume "cmod u < 1" "u \<noteq> ozero_m'" "cmod v < 1" "v \<noteq> ozero_m'"
      have "(2 / (1 + (cmod u)\<^sup>2)) *\<^sub>R u /\<^sub>R (2 * cmod u / (1 + (cmod u)\<^sup>2)) = u /\<^sub>R cmod u"
        by (smt (verit, best) \<open>cmod u < 1\<close> cmod_double' divide_divide_eq_right double'_cmod double'_def inverse_eq_divide nonzero_mult_div_cancel_left norm_ge_zero norm_power norm_scaleR scaleR_scaleR times_divide_eq_left zero_less_divide_iff)
      moreover
      have "(2 / (1 + (cmod v)\<^sup>2)) *\<^sub>R v /\<^sub>R (2 * cmod v / (1 + (cmod v)\<^sup>2)) = v /\<^sub>R cmod v"
        by (smt (verit, best) \<open>cmod v < 1\<close> cmod_double' divide_divide_eq_right double'_cmod double'_def inverse_eq_divide nonzero_mult_div_cancel_left norm_ge_zero norm_power norm_scaleR scaleR_scaleR times_divide_eq_left zero_less_divide_iff)
      ultimately
      show "inner (double' u /\<^sub>R cmod (double' u)) (double' v /\<^sub>R cmod (double' v)) =
            inner (u /\<^sub>R cmod u) (v /\<^sub>R cmod v)"
        unfolding cmod_double'[OF \<open>cmod u < 1\<close>] cmod_double'[OF \<open>cmod v < 1\<close>]
        unfolding double'_def
        unfolding double'_cmod[OF \<open>cmod u < 1\<close>] double'_cmod[OF \<open>cmod v < 1\<close>]
        by metis
    qed
  qed
qed


interpretation PGVME: pre_gyrovector_space_isomorphism to_complex_M to_complex_E scale_M scale_E \<phi>\<^sub>M\<^sub>E
proof
  fix r u
  show "\<phi>\<^sub>M\<^sub>E (scale_M r u) = scale_E r (\<phi>\<^sub>M\<^sub>E u) "
    by (simp add: scale\<phi>\<^sub>M\<^sub>E)
qed

interpretation isoME_norms_embed': gyrocarrier_isomorphism_norms_embed' to_complex_M to_complex_E scale_M scale_E \<phi>\<^sub>M\<^sub>E
  ..

interpretation isoME_norms_embed: gyrocarrier_isomorphism_norms_embed to_complex_M to_complex_E scale_M scale_E \<phi>\<^sub>M\<^sub>E
  by (smt (verit, del_insts) GCE.to_real'_norm GCEoinvRMinus \<phi>reals_to_reals bij\<phi>\<^sub>M\<^sub>E gyrocarrier_isomorphism_norms_embed'.\<phi>\<^sub>R_def gyrocarrier_isomorphism_norms_embed.intro gyrocarrier_isomorphism_norms_embed_axioms_def gyronorm\<phi>\<^sub>M\<^sub>E isoME_norms_embed'.gyrocarrier_isomorphism_norms_embed'_axioms oplus\<phi>\<^sub>M\<^sub>E scale\<phi>\<^sub>M\<^sub>E)


interpretation isoME': gyrovector_space_isomorphism' to_complex_M to_complex_E scale_M scale_E \<phi>\<^sub>M\<^sub>E
  by (meson PGVME.pre_gyrovector_space_isomorphism_axioms \<phi>reals_to_reals gyrovector_space_isomorphism'.intro gyrovector_space_isomorphism'_axioms_def gyrovector_space_norms_embed_M.gyrovector_space_norms_embed_axioms isoME_norms_embed.GV'.gyrocarrier_norms_embed_axioms)

interpretation isoME: gyrovector_space_isomorphism to_complex_M to_complex_E scale_M scale_E \<phi>\<^sub>M\<^sub>E
proof
  fix a b
  assume "a \<in> gyrocarrier'.norms to_complex_M" "b \<in> gyrocarrier'.norms to_complex_M" "0 \<le> a" "a \<le> b"

  then have "a < 1" "b < 1"
    unfolding gyrocarrier'_norms_M
    by auto

  {
    fix x
    assume "x \<in> GCM.norms" "x \<ge> 0"
    then have "abs x < 1"
      by simp

    have "GCM.of_real' x \<in> GCM.reals"
      unfolding of_real'_M[OF \<open>abs x < 1\<close>]
      using \<open>abs x < 1\<close>
      by auto
    then have *: "\<phi>\<^sub>M\<^sub>E (GCM.of_real' x) \<in> GCE.reals"
      using \<phi>reals_to_reals gyrocarrier_norms_embed'_reals_E gyrocarrier_norms_embed'_reals_M image_eqI 
      by blast

    have "GCE.to_real' (\<phi>\<^sub>M\<^sub>E (GCM.of_real' x)) = tanh (2 * artanh x)"
      using \<open>abs x < 1\<close> \<open>0 \<le> x\<close>
    proof (subst to_real'_E[OF *], subst of_real'_M[OF \<open>abs x < 1\<close>], transfer)
      fix x :: real 
      assume "abs x < 1" "0 \<le> x"
      then have *: "otimes' 2 (cor x) \<in> {z. cmod z < 1}"
        using cmod_otimes' cmod_otimes'_k by auto
      moreover
      have "Im (otimes' 2 (cor x)) = 0"
        by (simp add: otimes'_def)
      ultimately
      show "Re (to_complex (2 \<otimes> PoincareDisc.of_complex (cor x))) = tanh (2 * artanh x)"
        unfolding otimes_def
        using of_complex_inverse[OF *] of_complex_inverse[of x] \<open>abs x < 1\<close> \<open>0 \<le> x\<close>
        using otimes'_k_tanh[of "cor x" 2]
        by (smt (verit, ccfv_SIG) Mobius_gyrocarrier'.of_carrier artanh_nonneg cmod_otimes' eq_onp_same_args mem_Collect_eq norm_of_real norm_p.abs_eq otimes.rep_eq otimes_def otimes_homogenity' tanh_0 tanh_real_less_iff)
    qed
  }
  note * = this
  show "isoME''.\<phi>\<^sub>R a \<le> isoME''.\<phi>\<^sub>R b"
    using \<open>a \<in> gyrocarrier'.norms to_complex_M\<close> \<open>b \<in> gyrocarrier'.norms to_complex_M\<close> \<open>0 \<le> a\<close> \<open>a \<le> b\<close> \<open>a < 1\<close> \<open>b < 1\<close> *[of a] *[of b] tanh_artanh_mono[of a b]
    unfolding isoME''.\<phi>\<^sub>R_def
    by simp
qed

end
