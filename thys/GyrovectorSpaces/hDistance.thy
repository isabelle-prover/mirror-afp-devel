theory hDistance
  imports MobiusGyroVectorSpace
begin

abbreviation distance_m_expr :: "complex \<Rightarrow> complex \<Rightarrow> real" where
  "distance_m_expr u v \<equiv> 1 + 2 * (cmod (u - v))\<^sup>2 / ((1 - (cmod u)\<^sup>2) * (1 - (cmod v)\<^sup>2))"

definition distance_m :: "complex \<Rightarrow> complex \<Rightarrow> real" where 
  "distance_m u v = arcosh (distance_m_expr u v)"

lemma arcosh_artanh_lemma:
  shows "(cmod (1 - cnj u * v))\<^sup>2 - (cmod (u - v))\<^sup>2 = (1 - (cmod u)\<^sup>2) * (1 - (cmod v)\<^sup>2)"
proof-
  have "cor ((cmod (1 - cnj u * v))\<^sup>2 - (cmod (u - v))\<^sup>2) = cor ((1 - (cmod u)\<^sup>2) * (1 - (cmod v)\<^sup>2))"
    unfolding of_real_diff of_real_mult complex_norm_square
    by (simp add: field_simps)
  then show ?thesis
    using of_real_eq_iff by blast
qed

lemma distance_m_expr_ge_1:
  fixes u v :: complex
  assumes "cmod u < 1" "cmod v < 1"
  shows "distance_m_expr u v \<ge> 1"
proof-
  have "(cmod (u-v))\<^sup>2 \<ge> 0"
    using zero_le_power2 by blast
  moreover
  have "(1 - (cmod u)\<^sup>2) *(1 - (cmod v)\<^sup>2) > 0"
    using assms
    using cmod_def by force
  ultimately 
  show ?thesis
    by simp
qed

lemma arcosh_artanh:
  fixes u v :: complex
  assumes "cmod u <1" "cmod v < 1"
  shows "arcosh (distance_m_expr u v) =
         2 * artanh (cmod ((u-v) / (1 - (cnj u)*v)))"
proof-
  let ?u = "1 - (cmod u)\<^sup>2" and ?v = "1 - (cmod v)\<^sup>2" and ?uv = "(cmod (u - v))\<^sup>2"

  have "arcosh (distance_m_expr u v) =
        ln (distance_m_expr u v + sqrt ((distance_m_expr u v)\<^sup>2 - 1))"
    using arcosh_real_def[OF distance_m_expr_ge_1[OF assms]]
    by simp
  also have "\<dots> = ln (((cmod (1 - cnj u * v))\<^sup>2 + 2 * cmod (1 - cnj u * v) * cmod (u - v) + ?uv) /
                      (?u * ?v))"
  proof-
    have "distance_m_expr u v = (?u * ?v + 2 * ?uv) / (?u * ?v)"
    proof-
      have "?u \<noteq> 0" "?v \<noteq> 0"
        using assms
        by (metis abs_norm_cancel order_less_irrefl real_sqrt_abs real_sqrt_one right_minus_eq)+  
      then show ?thesis 
        by (simp add: add_divide_distrib)
    qed
    then have *: "distance_m_expr u v = ((cmod (1 - cnj u * v))\<^sup>2 + ?uv) / (?u * ?v)"
      using assms 
      by (smt (verit, ccfv_SIG) arcosh_artanh_lemma)
   
    have "sqrt ((distance_m_expr u v)\<^sup>2 - 1) =
          sqrt (4 * (?uv / (?u * ?v)) + 4 * (?uv / (?u * ?v))\<^sup>2)"
      by (smt (verit, best) add_divide_distrib four_x_squared inner_real_def one_power2 power2_diff real_inner_1_right)
    also have "\<dots> = sqrt (4 * ?uv * (1 / (?u * ?v) + (cmod (u - v) / (?u * ?v))\<^sup>2))" (is "?lhs = sqrt (4 * ?A * ?B)")
      by (simp add: field_simps)
    also have "\<dots> = sqrt (4 * ?uv * (?u * ?v + ?uv) / (?u * ?v)\<^sup>2)"
    proof-
      have "?B = (?u * ?v + ?uv) / (?u * ?v)\<^sup>2"
        by (simp add: power_divide power2_eq_square add_divide_distrib)
      then show ?thesis
        by simp
    qed
    also have "\<dots> = 2 * cmod (u - v) * sqrt (?u * ?v + ?uv) / (?u * ?v)"
      using assms
      by (smt (verit, ccfv_SIG) four_x_squared mult_nonneg_nonneg norm_not_less_zero one_power2 power_mono real_root_divide real_root_mult real_sqrt_unique sqrt_def)
    also have "... = 2 * cmod (u - v) / (?u * ?v) * sqrt (?u * ?v + ?uv)"
      by simp
    finally have **: "sqrt ((distance_m_expr u v)\<^sup>2 - 1) =  
                      2 * cmod (u - v) * cmod (1 - cnj u * v) / (?u * ?v)"
      by (smt (verit, del_insts) arcosh_artanh_lemma norm_ge_zero real_sqrt_abs times_divide_eq_left)

    show ?thesis
      using * **
      by (smt (verit, best) add_divide_distrib power2_sum)
  qed
  also have "\<dots> = ln ((1 + cmod (u - v) / cmod (1 - cnj u * v)) /
                      (1 - cmod (u - v) / cmod (1 - cnj u * v)))" (is "?lhs = ln (?nom / ?den)")
  proof-
    have *: "?nom = (cmod (u - v) + cmod (1 - cnj u * v)) / cmod (1 - cnj u * v)"
      using assms
      by (metis (no_types, opaque_lifting) add_diff_cancel_left' add_divide_distrib complex_mod_cnj diff_diff_eq2 diff_zero divide_self_if mult_closed_for_unit_disc norm_eq_zero norm_one order_less_irrefl)
    then have **: "?den = (cmod (1 - cnj u * v) - cmod (u - v)) / cmod (1 - cnj u * v)"
      using assms
      by (smt (verit, ccfv_SIG) add_divide_distrib)
    have "?nom / ?den =
          (cmod (u - v) + cmod (1 - cnj u * v)) / (cmod (1 - cnj u * v) - cmod (u - v))"
      using * **
      by force
    also have "\<dots> = (cmod (1 - cnj u * v) + cmod (u - v))\<^sup>2 / (?u * ?v)" (is "?lhs = ?rhs")
    proof-
      let ?e = "cmod (1 - cnj u * v) + cmod (u - v)"
      have "?lhs = ?lhs * ?e/?e"
        by fastforce
      moreover
      have "(cmod (1 - cnj u * v) - cmod (u - v)) * ?e = ?u * ?v"
        using arcosh_artanh_lemma
        by (simp add: mult.commute power2_eq_square square_diff_square_factored)
      ultimately
      show ?thesis
        by (simp add: power2_eq_square)
    qed
    finally
    show ?thesis
      by (simp add: power2_eq_square field_simps)
  qed
  finally show ?thesis
    unfolding artanh_def
    by (simp add: norm_divide)
qed

definition distance_m_gyro :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> real" where
 "distance_m_gyro u v = 2 * artanh (Mobius_pre_gyrovector_space.distance u v)"

lemma distance_equiv:
  shows "distance_m_gyro u v = distance_m (to_complex u) (to_complex v)"
proof-
  have "(\<llangle>\<ominus>\<^sub>m u \<oplus>\<^sub>m v\<rrangle>) =
         (cmod ((to_complex u - to_complex v) / (1 - cnj (to_complex u) * (to_complex v))))"
    by transfer (simp add: oplus_m'_def ominus_m'_def norm_divide norm_minus_commute)
  then show ?thesis
  unfolding distance_m_gyro_def distance_m_def Mobius_pre_gyrovector_space.distance_def gyroinv_PoincareDisc_def gyroplus_PoincareDisc_def
  using arcosh_artanh norm_lt_one norm_p.rep_eq
  by force
qed

definition blaschke where
  "blaschke a z = (z - a) / (1 - cnj a * z)"

lemma
  fixes a z :: complex
  shows "blaschke a z  = oplus_m' (ominus_m' a) z"
  unfolding blaschke_def oplus_m'_def ominus_m'_def
  by (simp add: minus_divide_left)

end
