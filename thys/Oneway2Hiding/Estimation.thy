theory Estimation

imports Complex_Main

begin
section \<open>Auxiliary lemma: Estimation\<close>

text \<open>For the proof of the mixed state O2H, we need an auxiliary lemma on the square roots of sums.\<close>

lemma abc_ineq:
  assumes "a\<ge>0" "b\<ge>0" "c\<ge>0" "\<bar>sqrt a - sqrt b\<bar> \<le> sqrt c"
  shows "a + b \<le> c + 2 * sqrt (a * b)"
proof -
  have "\<bar>sqrt a - sqrt b\<bar>^2 \<le> sqrt c ^2" using assms by (simp add: sqrt_ge_absD)
  then show ?thesis by (auto simp add: algebra_simps power2_diff assms real_sqrt_mult)
qed

lemma two_ab_ineq:
  assumes "a\<ge>0" "b\<ge>0"
  shows "2 * sqrt (a * b) \<le> a + b"
proof -
  have "0 \<le> (sqrt a - sqrt b)^2" by auto
  then show ?thesis by (auto simp add: algebra_simps power2_diff assms real_sqrt_mult)
qed

lemma sqrt_estimate_real:
  assumes fin_M: "finite M" 
    and pos_t: "\<forall>x\<in>M. t x \<ge> (0::real)" 
    and pos_u: "\<forall>x\<in>M. u x \<ge> (0::real)" 
    and pos_v: "\<forall>x\<in>M. v x \<ge> (0::real)" 
    and pos_a: "\<forall>x\<in>M. a x \<ge> (0::real)"
    and ineq:  "\<forall>x\<in>M. \<bar> sqrt (t x) - sqrt (u x)\<bar> \<le> sqrt (v x)"
  shows "\<bar>sqrt (\<Sum>x\<in>M. a x * t x) - sqrt (\<Sum>x\<in>M. a x * u x)\<bar> \<le> sqrt (\<Sum>x\<in>M. a x * v x)"
  using assms proof (induction M)
  case empty
  then show ?case by auto
next
  case (insert y N)
  define tN where "tN = (\<Sum>x\<in>N. a x * t x)"
  have pos_tN[simp]: "0 \<le> tN" unfolding tN_def by (simp add: insert.prems(1) insert.prems(4) sum_nonneg)
  define uN where "uN = (\<Sum>x\<in>N. a x * u x)"
  have pos_uN[simp]: "0 \<le> uN" unfolding uN_def by (simp add: insert.prems(2) insert.prems(4) sum_nonneg)
  define vN where "vN = (\<Sum>x\<in>N. a x * v x)"
  have pos_vN[simp]: "0 \<le> vN" unfolding vN_def by (simp add: insert.prems(3) insert.prems(4) sum_nonneg)
  have ineqN: "\<bar>sqrt tN - sqrt uN\<bar> \<le> sqrt vN"
    by (simp add: insert.prems(1,4) insert(3,5,6,8) tN_def uN_def vN_def)
  have 2: "tN + uN \<le> vN + 2 * sqrt (tN * uN)" 
    by (intro abc_ineq)(auto simp add: ineqN)
  have "a y \<ge> 0" using insert by auto
  have "3a": "t y + u y \<le> v y + 2 * sqrt (t y * u y)" by (intro abc_ineq) (auto simp add: insert)
  have 3: "a y * t y + a y * u y \<le> a y * v y + 2 * a y * sqrt (t y * u y)"
    by (use mult_left_mono[OF "3a" \<open>a y \<ge> 0\<close>] in \<open>auto simp add: algebra_simps\<close>)
  have 5: "sqrt ((tN + a y * t y) * (uN + a y * u y)) \<ge> sqrt (tN * uN) + a y * sqrt (t y * u y)"
  proof -
    have "(sqrt (tN * uN) + a y * sqrt (t y * u y)) ^2 = tN * uN + (a y)^2 * t y * u y 
      + 2 * a y * sqrt (tN * uN * t y * u y)"
      by (auto simp add: algebra_simps power2_sum insert real_sqrt_mult[symmetric])
    also have "\<dots> = tN * uN + (a y)^2 * t y * u y + 2 * sqrt ((a y)^2 * tN * uN * t y * u y)"
      by (auto simp add: real_sqrt_mult \<open>a y \<ge> 0\<close>)
    also have "\<dots> = tN * uN + (a y)^2 * t y * u y + 2 * sqrt ((a y * tN * u y) * (a y * uN * t y))"
      by (auto simp add: algebra_simps power2_eq_square)
    also have "\<dots> \<le> tN * uN + (a y)^2 * t y * u y + a y * tN * u y + a y * uN * t y"
      using two_ab_ineq[of "a y * tN * u y" "a y * uN * t y"] by (auto simp add: insert)
    also have "\<dots> = sqrt ((tN + a y * t y) * (uN + a y * u y))^2" using real_sqrt_pow2 
      by (auto simp add: insert algebra_simps power2_eq_square)
    finally show ?thesis by (simp add: \<open>0 \<le> a y\<close> insert(4,5) real_le_rsqrt)
  qed
  have "\<bar>sqrt (\<Sum>x\<in>insert y N. a x * t x) - sqrt (\<Sum>x\<in>insert y N. a x * u x)\<bar> = 
    \<bar>sqrt (tN + a y * t y) - sqrt (uN + a y * u y)\<bar>"
    by (subst sum.insert[OF insert(1,2)])+ (auto simp add: tN_def uN_def algebra_simps)
  also have "\<dots> \<le> sqrt (vN + a y * v y)"
  proof -
    have "\<bar>sqrt (tN + a y * t y) - sqrt (uN + a y * u y)\<bar>^2 = 
      tN + a y * t y + uN + a y * u y - 2 * sqrt((tN + a y * t y) * (uN + a y * u y))" 
      by (auto simp add: algebra_simps power2_diff insert real_sqrt_mult[symmetric])
    also have "\<dots> \<le> vN + a y * v y + 2 * sqrt(tN * uN) + 2* a y * sqrt (t y * u y) - 
      2 * sqrt ((tN + a y * t y) * (uN + a y * u y))"
      using 2 3 by auto
    finally have "\<bar>sqrt (tN + a y * t y) - sqrt (uN + a y * u y)\<bar>^2 \<le> vN + a y * v y" 
      using 5 by auto
    then show ?thesis using real_le_rsqrt by blast
  qed
  also have "\<dots> = sqrt (\<Sum>x\<in>insert y N. a x * v x)"
    by (subst sum.insert[OF insert(1,2)]) (auto simp add: vN_def)
  finally show ?case by linarith
qed



end