theory HyperbolicFunctions
imports HOL.Transcendental
begin

lemma artanh_abs_tanh:
  fixes x::real
  shows "artanh (abs (tanh x)) = abs x"
proof (cases "x \<ge> 0")
  case True
  then show ?thesis 
    by (simp add: artanh_tanh_real)
next
  case False
  then show ?thesis
    by (metis artanh_tanh_real tanh_real_abs)
qed

lemma artanh_nonneg:
  fixes x :: real
  assumes "0 \<le> x" "x < 1"
  shows "artanh x \<ge> 0"
proof-
  have "(1+x)/(1-x) \<ge> 1/(1-x)"
    by (metis assms add_0 add_increasing2 divide_right_mono le_diff_eq less_eq_real_def)
  moreover have "1/(1-x) \<ge> 1"
    using assms 
    by simp
  moreover have "artanh x = 1/2*ln((1+x)/(1-x))"
    by (simp add: artanh_def)
  moreover have "ln((1+x)/(1-x))\<ge>0"
    using calculation(1) calculation(2) by fastforce
  moreover have "((artanh x)\<ge>0)"
    using calculation(3) calculation(4) by linarith
  moreover have "(0\<le>x \<and> x<1)\<longrightarrow> ((artanh x)\<ge>0)"
    using calculation by blast
  ultimately 
  show ?thesis 
    by blast
qed

lemma artanh_not_0:
  fixes x :: real
  assumes "x > 0" "x < 1"
  shows "artanh x \<noteq> 0"
  using assms
  by (simp add: artanh_def)

lemma tanh_not_0:
  fixes x :: real
  assumes "x > 0" "x < 1"
  shows "tanh x \<noteq> 0"
  using assms
  by simp

lemma tanh_monotone:
  fixes x y :: real
  assumes "x > y"
  shows "tanh x > tanh y"
  using assms
  by simp

lemma artanh_monotone1:
  fixes x::real
  assumes "x \<ge> 0" "x < 1" "y \<ge> 0" "y < 1" "x \<le> y"
  shows "(1+x) / (1-x) \<le> (1+y) / (1-y)"
  using assms
  by (smt (verit, best) frac_less)

lemma artanh_monotone2:
  fixes x::real
  assumes "x\<ge>0" "x<1" "y\<ge>0" "y<1" "x\<le>y"
  shows "ln ((1+x)/(1-x)) \<le> ln((1+y)/(1-y))"
  using artanh_monotone1 assms(1) assms(4) assms(5) by force
  
lemma artanh_monotone:
  fixes x y :: real
  assumes "x \<ge> 0" "x < 1" "0 \<le> y" "y < 1" 
  assumes "x \<le> y"
  shows "artanh x \<le> artanh y"
proof-
  have "artanh x = 1/2 * ln((1+x)/(1-x))"
    by (simp add: artanh_def)
  moreover have "artanh y = (1/2) * ln((1+y)/(1-y))"
    by (simp add: artanh_def)
  ultimately show ?thesis 
    using assms artanh_monotone2
    by (simp add: artanh_def)
qed

lemma tanh_artanh_nonneg:
  fixes x r :: real
  assumes "r \<ge> 0" "x \<ge> 0" "x < 1"
  shows "tanh (r * artanh x) \<ge> 0"
  using assms
  by (simp add: artanh_nonneg)

lemma tanh_artanh_mono:
  fixes x y :: real
  assumes "0 \<le> x" "x < 1" "0 \<le> y" "y < 1"
  assumes "x \<le> y"
  shows "tanh (2 * artanh x) \<le> tanh (2 * artanh y)"
  using assms
  using artanh_monotone
  by auto

lemma tanh_def':
  fixes x :: real
  shows "tanh x = (exp (2*x) - 1) / (exp (2*x) + 1)"
  unfolding tanh_def sinh_def cosh_def
  by (metis cosh_def exp_gt_zero exp_of_nat_mult ln_unique of_nat_numeral sinh_def tanh_def tanh_ln_real)

lemma tanh_artanh:
  fixes x :: real
  assumes "-1 < x" "x < 1"
  shows "tanh (artanh x) = x"
  using assms
  unfolding artanh_def tanh_def'
  by (simp add: field_simps)

end