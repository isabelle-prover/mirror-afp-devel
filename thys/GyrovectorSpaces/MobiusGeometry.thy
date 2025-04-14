theory MobiusGeometry
  imports MobiusGyroVectorSpace
begin

lemma mobius_collinear_u0v':
  assumes "v \<noteq> 0\<^sub>m"
  shows "Mobius_pre_gyrovector_space.collinear u 0\<^sub>m v \<longleftrightarrow> (\<exists> k::real. to_complex u = k * (to_complex v))"
  unfolding Mobius_pre_gyrovector_space.collinear_def gyroplus_PoincareDisc_def gyroinv_PoincareDisc_def
  using assms
proof transfer
  fix v u
  assume "cmod v < 1" "cmod u < 1" "v \<noteq> ozero_m'"
  then have "v \<noteq> 0"
    unfolding ozero_m'_def
    by simp
  have "(\<exists>t. u = (otimes'_k t v) * v / cor (cmod v)) \<longleftrightarrow> (\<exists>k :: real. u = k * v)" (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume ?lhs
    then show ?rhs
      by (metis of_real_divide times_divide_eq_left)
  next
    assume ?rhs
    then obtain k::real where "u = k * v"
      by auto

    moreover

    have "abs (k * cmod v) < 1"
      by (metis \<open>cmod u < 1\<close> \<open>u = cor k * v\<close> abs_mult abs_norm_cancel norm_mult norm_of_real)

    have "artanh (cmod v) \<noteq> 0"
      using \<open>v \<noteq> 0\<close>
      by (simp add: \<open>cmod v < 1\<close> artanh_not_0)
    
    have "\<exists> t. (otimes'_k t v) / (cmod v) = k"
    proof-
      let ?t = "artanh(k * cmod v) / artanh (cmod v)"
      have "tanh (?t * artanh (cmod v)) = k * cmod v"
        using \<open>artanh (cmod v) \<noteq> 0\<close> tanh_artanh[of "k * cmod v"] \<open>abs (k * cmod v) < 1\<close>
        by (simp add: field_simps)
      then show ?thesis
        by (metis \<open>cmod v < 1\<close> \<open>v \<noteq> 0\<close> nonzero_mult_div_cancel_right norm_zero otimes'_k_tanh zero_less_norm_iff)
    qed
    ultimately
    show ?lhs
      by auto
  qed
  then show "(ozero_m' = v \<or> (\<exists>t. u = oplus_m' ozero_m' (otimes' t (oplus_m' (ominus_m' ozero_m') v)))) \<longleftrightarrow>
        (\<exists> k::real. u = k * v)"
    using \<open>v \<noteq> 0\<close>
    unfolding oplus_m'_def ozero_m'_def ominus_m'_def otimes'_def
    by simp
qed

lemma mobius_collinear_u0v:
  shows "Mobius_pre_gyrovector_space.collinear x 0\<^sub>m v \<longleftrightarrow> 
         v = 0\<^sub>m \<or> (\<exists> k::real. to_complex x = k * (to_complex v))"
  by (metis Mobius_pre_gyrovector_space.collinear_def mobius_collinear_u0v')

lemma mobius_between_0uv:
  shows "Mobius_pre_gyrovector_space.between 0\<^sub>m u v \<longleftrightarrow> 
         (\<exists> k::real. 0 \<le> k \<and> k \<le> 1 \<and> to_complex u = k * to_complex v)"
proof (cases "v = 0\<^sub>m")
  case True
  then show ?thesis
    using Mobius_pre_gyrovector_space.between_xyx[of "0\<^sub>m" u]
    by auto
next
  case False
  then show ?thesis
    unfolding Mobius_pre_gyrovector_space.between_def gyroplus_PoincareDisc_def gyrozero_PoincareDisc_def gyroinv_PoincareDisc_def
  proof (transfer)
    fix x y
    assume "cmod y < 1" "y \<noteq> ozero_m'" "cmod x < 1"
    then have "y \<noteq> 0"
      by (simp add: ozero_m'_def)

    have "(\<exists>t\<ge>0. t \<le> 1 \<and> x = cor (otimes'_k t y) * y / cor (cmod y)) =
          (\<exists>k\<ge>0. k \<le> 1 \<and> x = cor k * y)" (is "?lhs = ?rhs")
    proof
      assume ?lhs
      then obtain t where "0 \<le> t" "t \<le> 1" "x = (otimes'_k t y / cmod y) * y"
        by auto
      moreover
      have "0 \<le> otimes'_k t y / cmod y" 
        unfolding otimes'_k_tanh[OF \<open>cmod y < 1\<close>]
        using \<open>cmod y < 1\<close> \<open>t \<ge> 0\<close> tanh_artanh_nonneg 
        by auto
      moreover
      have "otimes'_k t y / cmod y \<le> 1"
        unfolding otimes'_k_tanh[OF \<open>cmod y < 1\<close>]
        using \<open>cmod y < 1\<close> \<open>y \<noteq> 0\<close> artanh_nonneg \<open>t \<le> 1\<close>
        by (smt (verit, best) divide_le_eq_1 mult_le_cancel_right2 norm_le_zero_iff strict_mono_less_eq tanh_artanh tanh_real_strict_mono)
      ultimately
      show ?rhs
        by auto
    next
      assume ?rhs
      then obtain k::real where "x = k * y"
        by auto

      moreover

      have "abs (k * cmod y) < 1"
        by (metis \<open>cmod x < 1\<close> \<open>x = cor k * y\<close> abs_mult abs_norm_cancel norm_mult norm_of_real)

      have "artanh (cmod y) \<noteq> 0"
        using \<open>y \<noteq> 0\<close>
        by (simp add: \<open>cmod y < 1\<close> artanh_not_0)
    
      have "\<exists> t. 0 \<le> t \<and> t \<le> 1 \<and> (otimes'_k t y) / (cmod y) = k"
      proof-
        let ?t = "artanh(k * cmod y) / artanh (cmod y)"
        have "tanh (?t * artanh (cmod y)) = k * cmod y"
          using \<open>artanh (cmod y) \<noteq> 0\<close> tanh_artanh[of "k * cmod y"] \<open>abs (k * cmod y) < 1\<close>
          by (simp add: field_simps)
        moreover
        have "?t \<ge> 0"
          using \<open>\<exists>k\<ge>0. k \<le> 1 \<and> x = cor k * y\<close> \<open>cmod y < 1\<close> \<open>x = cor k * y\<close> \<open>y \<noteq> 0\<close>
          by (smt (verit, ccfv_SIG)  artanh_nonneg calculation divide_eq_0_iff mult_right_cancel norm_le_zero_iff of_real_eq_iff tanh_real_nonneg_iff zero_le_mult_iff)
        moreover
        have "?t \<le> 1"
          using \<open>\<exists>k\<ge>0. k \<le> 1 \<and> x = cor k * y\<close> \<open>cmod y < 1\<close> \<open>x = cor k * y\<close> \<open>y \<noteq> 0\<close>
          by (smt (verit, ccfv_SIG)  artanh_monotone artanh_nonneg calculation(1) less_divide_eq_1 nonzero_divide_eq_eq of_real_eq_iff tanh_artanh_nonneg zero_less_norm_iff)
        ultimately show ?thesis
          by (metis \<open>cmod y < 1\<close> \<open>y \<noteq> 0\<close> nonzero_mult_div_cancel_right norm_zero otimes'_k_tanh zero_less_norm_iff)
      qed
      ultimately
      show ?lhs
        by auto
    qed
    then show "(\<exists>t\<ge>0. t \<le> 1 \<and>
                       x = oplus_m' ozero_m' (otimes' t (oplus_m' (ominus_m' ozero_m') y))) =
               (\<exists>k\<ge>0. k \<le> 1 \<and> x = cor k * y)"
      using \<open>y \<noteq> 0\<close>
      unfolding ozero_m'_def oplus_m'_def ominus_m'_def otimes'_def
      by simp
  qed
qed

(* ------------------------------------------------------------------- *)

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

definition distance\<^sub>m :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> real" where
 "distance\<^sub>m u v = 2 * artanh (Mobius_pre_gyrovector_space.distance u v)"

lemma distance\<^sub>m_equiv:
  shows "distance\<^sub>m u v = distance_m (to_complex u) (to_complex v)"
proof-
  have "(\<llangle>\<ominus>\<^sub>m u \<oplus>\<^sub>m v\<rrangle>) =
         (cmod ((to_complex u - to_complex v) / (1 - cnj (to_complex u) * (to_complex v))))"
    by transfer (simp add: oplus_m'_def ominus_m'_def norm_divide norm_minus_commute)
  then show ?thesis
  unfolding distance\<^sub>m_def distance_m_def Mobius_pre_gyrovector_space.distance_def gyroinv_PoincareDisc_def gyroplus_PoincareDisc_def
  using arcosh_artanh norm_lt_one norm_p.rep_eq
  by force
qed

definition cong\<^sub>m :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> bool" where
  "cong\<^sub>m a b c d \<longleftrightarrow> distance\<^sub>m a b = distance\<^sub>m c d"

end
