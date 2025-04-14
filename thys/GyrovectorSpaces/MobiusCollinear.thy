theory MobiusCollinear
  imports MobiusGyroVectorSpace 
begin

lemma collinear_0_proportional':
  assumes "v \<noteq> 0\<^sub>m"
  shows "Mobius_pre_gyrovector_space.collinear x 0\<^sub>m v \<longleftrightarrow> (\<exists> k::real. to_complex x = k * (to_complex v))"
  unfolding Mobius_pre_gyrovector_space.collinear_def gyroplus_PoincareDisc_def gyroinv_PoincareDisc_def
  using assms
proof transfer
  fix v x
  assume "cmod v < 1" "cmod x < 1" "v \<noteq> ozero_m'"
  then have "v \<noteq> 0"
    unfolding ozero_m'_def
    by simp
  have "(\<exists>t. x = (otimes'_k t v) * v / cor (cmod v)) \<longleftrightarrow> (\<exists>k :: real. x = k * v)" (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume ?lhs
    then show ?rhs
      by (metis of_real_divide times_divide_eq_left)
  next
    assume ?rhs
    then obtain k::real where "x = k * v"
      by auto

    moreover

    have "abs (k * cmod v) < 1"
      by (metis \<open>cmod x < 1\<close> \<open>x = cor k * v\<close> abs_mult abs_norm_cancel norm_mult norm_of_real)

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
  then show "(ozero_m' = v \<or> (\<exists>t. x = oplus_m' ozero_m' (otimes' t (oplus_m' (ominus_m' ozero_m') v)))) \<longleftrightarrow>
        (\<exists> k::real. x = k * v)"
    using \<open>v \<noteq> 0\<close>
    unfolding oplus_m'_def ozero_m'_def ominus_m'_def otimes'_def
    by simp
qed

lemma
  assumes "v \<noteq> 0\<^sub>m"
  shows "Mobius_pre_gyrovector_space.collinear x 0\<^sub>m v \<longleftrightarrow> to_complex x * cnj (to_complex v) = cnj (to_complex x) * to_complex v"
  using Mobius_gyrocarrier'.to_carrier_zero_iff assms cnj_mix_ex_real_k collinear_0_proportional' gyrozero_PoincareDisc_def
  by fastforce

lemma collinear_0_proportional:
  shows "Mobius_pre_gyrovector_space.collinear x 0\<^sub>m v \<longleftrightarrow> v = 0\<^sub>m \<or> (\<exists> k::real. to_complex x = k * (to_complex v))"
  by (metis Mobius_pre_gyrovector_space.collinear_def collinear_0_proportional')

lemma to_complex_0 [simp]:
  shows "to_complex 0\<^sub>m = 0"
  by transfer (simp add: ozero_m'_def)

lemma to_complex_0_iff [iff]:
  shows "to_complex x = 0 \<longleftrightarrow> x = 0\<^sub>m"
  by transfer (simp add: ozero_m'_def)

lemma mobius_between_0xy:
  shows "Mobius_pre_gyrovector_space.between 0\<^sub>m x y \<longleftrightarrow> 
         (\<exists> k::real. 0 \<le> k \<and> k \<le> 1 \<and> to_complex x = k * to_complex y)"
proof (cases "y = 0\<^sub>m")
  case True
  then show ?thesis
    using Mobius_pre_gyrovector_space.between_xyx[of "0\<^sub>m" x]
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

end
