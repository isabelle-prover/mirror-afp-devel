theory GammaFactor
  imports Complex_Main MoreComplex
begin

definition gamma_factor :: "'a::real_inner \<Rightarrow> real" ("\<gamma>") where
  "\<gamma> u = (if norm u < 1 then 
             1 / sqrt (1 - (norm u)\<^sup>2)
          else
             0)"

lemma gamma_factor_nonzero:
  assumes "norm u < 1"
  shows "1 / sqrt (1 - (norm u)\<^sup>2) \<noteq> 0"
  using assms square_norm_one by force

lemma gamma_factor_increasing:
  fixes t1 t2 ::real
  assumes "0 \<le> t2" "t2 < t1" "t1 < 1"
  shows "\<gamma> t2 < \<gamma> t1"
proof-
  have d: "cmod t1 = abs t1" "cmod t2 = abs t2"
    using norm_of_real 
    by blast+

  have "\<bar>t2\<bar> * \<bar>t2\<bar> < \<bar>t1\<bar> * \<bar>t1\<bar>"
    by (simp add: assms mult_strict_mono')
  then have "1 - \<bar>t1\<bar> * \<bar>t1\<bar> < 1 - \<bar>t2\<bar> * \<bar>t2\<bar>"
    by auto
  then have "sqrt (1 - \<bar>t1\<bar> * \<bar>t1\<bar>) < sqrt (1 - \<bar>t2\<bar> * \<bar>t2\<bar>)"
    using real_sqrt_less_iff 
    by blast
  then have "1 / sqrt (1 - \<bar>t2\<bar> * \<bar>t2\<bar>) < 1 / sqrt (1 - \<bar>t1\<bar> * \<bar>t1\<bar>)"
    using assms
    by (smt (z3) frac_less2 mult_less_cancel_right2 real_sqrt_gt_zero)

  moreover

  have "norm t1 < 1" "norm t2 < 1"
    using assms 
    by force+
  then have "\<gamma> t1 = 1 / sqrt(1 - (abs t1)^2)" "\<gamma> t2 = 1 / sqrt(1 - (abs t2)^2)"
    using assms d 
    unfolding gamma_factor_def
    by auto

  ultimately

  show ?thesis
    using d 
    by (metis power2_eq_square)
qed

lemma gamma_factor_increase_reverse:
  fixes t1 t2 :: real
  assumes "t1 \<ge> 0" "t1 < 1" "t2 \<ge> 0" "t2 < 1"
  assumes "\<gamma> t1 > \<gamma> t2"
  shows "t1 > t2"
  using assms
  by (smt (verit, best) gamma_factor_increasing)
  
lemma gamma_factor_u_normu:
  fixes u :: real
  assumes "0 \<le> u" "u \<le> 1"
  shows "\<gamma> u = \<gamma> (norm u)"
  unfolding gamma_factor_def
  by auto

lemma gamma_factor_positive:
  assumes "norm u < 1"
  shows "\<gamma> u > 0"
  using assms
  unfolding gamma_factor_def
  by (smt (verit, del_insts) divide_pos_pos norm_ge_zero power2_eq_square power2_nonneg_ge_1_iff real_sqrt_gt_0_iff)

lemma norm_square_gamma_factor:
  assumes "norm u < 1"
  shows "(norm u)^2 = 1 - 1 / (\<gamma> u)^2"
proof-
  have "\<gamma> u = 1 / sqrt (1 - (norm u)^2)"
    by (metis assms gamma_factor_def)
  then have "(\<gamma> u)^2 = 1 / (1 - (norm u)^2)"
    using assms
    by (metis abs_power2 gamma_factor_positive less_eq_real_def norm_ge_zero norm_power power2_eq_imp_eq real_norm_def real_sqrt_abs real_sqrt_divide real_sqrt_eq_1_iff real_sqrt_eq_iff)
  then show ?thesis 
    by auto
qed

lemma norm_square_gamma_factor':
  assumes "norm u < 1"
  shows "(norm u)^2 = ((\<gamma> u)^2 - 1) / (\<gamma> u)^2"
  using norm_square_gamma_factor[OF assms]
  by (metis assms diff_divide_distrib div_self gamma_factor_positive norm_not_less_zero norm_zero power_not_zero)


lemma gamma_factor_square_norm:
  assumes "norm u < 1"
  shows "(\<gamma> u)\<^sup>2 = 1 / (1 - (norm u)\<^sup>2)"
  by (smt (verit) assms gamma_factor_def gamma_factor_positive real_sqrt_divide real_sqrt_eq_iff real_sqrt_one real_sqrt_unique)

lemma gamma_expression_eq_one_1:
  assumes "norm u < 1" 
  shows "1 / \<gamma> u + (\<gamma> u * (norm u)^2) / (1 + \<gamma> u) = 1"
proof-
  have "\<gamma> u \<noteq> 0" "1 + \<gamma> u \<noteq> 0"
    using assms gamma_factor_positive 
    by fastforce+

  have "1 / \<gamma> u + \<gamma> u * (norm u)^2 / (1 + \<gamma> u) =
        (1 + \<gamma> u + (\<gamma> u)^2 * (norm u)^2) / (\<gamma> u * (1 + \<gamma> u))"
    using \<open>\<gamma> u \<noteq> 0\<close> \<open>1 + \<gamma> u \<noteq> 0\<close>
    by (metis (no_types, lifting) add_divide_distrib nonzero_divide_mult_cancel_right nonzero_mult_divide_mult_cancel_left numeral_One power_add_numeral2 power_one_right semiring_norm(2))
  also have "\<dots> = (1 + \<gamma> u + (\<gamma> u)^2 * (1 - 1 / ((\<gamma> u)^2))) / (\<gamma> u * (1 + \<gamma> u))"
    by (simp add: assms norm_square_gamma_factor)
  also have "\<dots> = (1 + \<gamma> u + (\<gamma> u)^2 - 1) / (\<gamma> u * (1 + \<gamma> u))"
    by (simp add: Rings.ring_distribs(4))
  also have "... = (\<gamma> u * (1 + \<gamma> u)) / (\<gamma> u * (1 + \<gamma> u))"
    by (simp add: power2_eq_square ring_class.ring_distribs(1))
  finally show ?thesis
    using \<open>\<gamma> u \<noteq> 0\<close> \<open>1 + \<gamma> u \<noteq> 0\<close>
    by (metis div_by_1 divide_divide_eq_right eq_divide_eq_1)
qed

lemma gamma_expression_eq_one_2:
  assumes "norm u < 1"
  shows "((\<gamma> u)^2 * (norm u)^2) / (1 + \<gamma> u)^2 + (2 * \<gamma> u) / (\<gamma> u * (1 + \<gamma> u)) = 1"
proof-
  have *: "\<gamma> u \<noteq> 0" "1 + \<gamma> u \<noteq> 0"
    using assms gamma_factor_positive
    by force+

  have "((\<gamma> u)^2 * (norm u)^2) / (1 + \<gamma> u)^2 + (2 * \<gamma> u) / (\<gamma> u * (1 + \<gamma> u)) = 
        ((\<gamma> u)^2 * (1 - 1 / (\<gamma> u)^2)) / (1 + \<gamma> u)^2 + (2 * \<gamma> u) / (\<gamma> u * (1 + \<gamma> u))"
    using norm_square_gamma_factor[OF assms]
    by presburger
  also have "\<dots> = ((\<gamma> u)^2 - 1) / (1 + \<gamma> u)^2 + (2 * \<gamma> u) / (\<gamma> u * (1 + \<gamma> u))"
    using \<open>\<gamma> u \<noteq> 0\<close>
    by (simp add: right_diff_distrib)
  also have "\<dots> = (\<gamma> u * ((\<gamma> u)^2 - 1)) / (\<gamma> u * (1 + \<gamma> u)^2) + (2 * \<gamma> u * (1 + \<gamma> u)) / (\<gamma> u * (1 + \<gamma> u)^2)"
    using \<open>\<gamma> u \<noteq> 0\<close>
    by (simp add: mult.commute power2_eq_square)
  also have "\<dots> = (\<gamma> u * ((\<gamma> u)^2 - 1) + 2 * \<gamma> u * (1 + \<gamma> u)) / (\<gamma> u * (1 + \<gamma> u)^2)"
    by argo
  also have "\<dots> = ((\<gamma> u)^3 + \<gamma> u + 2 * (\<gamma> u)^2) / (\<gamma> u * (1 + \<gamma> u)^2)"
    by (simp add: power2_eq_square power3_eq_cube right_diff_distrib ring_class.ring_distribs(1))
  also have "\<dots> = (\<gamma> u * (1 + \<gamma> u) ^ 2) / (\<gamma> u * (1 + \<gamma> u)^2)"
    by (simp add: field_simps power2_eq_square power3_eq_cube)
  finally show ?thesis 
    using *
    by simp
qed


end