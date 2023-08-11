section \<open> Technical Lemmas \<close>
text \<open>We show three lemmas used in the proof of both main theorems.\<close>

theory Polygonal_Number_Theorem_Lemmas
  imports "Three_Squares.Three_Squares"

begin

subsection \<open> Lemma 1.10 in \cite{nathanson1996} \<close>
text \<open>This lemma is split into two parts. We modify the proof given in \cite{nathanson1996} slightly as we require the second result to hold for $l=2$ in the proof of Legendre's polygonal number theorem.\<close>

theorem interval_length_greater_than_four:
  fixes m N L :: real
  assumes "m \<ge> 3"
  assumes "N \<ge> 2*m"
  assumes "L = (2/3 + sqrt (8*N/m - 8)) - (1/2 + sqrt (6*N/m - 3))"
  shows "N \<ge> 108*m \<Longrightarrow> L > 4" 

proof -
  assume asm: "N \<ge> 108*m"
  show "L > 4"
    proof -
      define x :: real where "x = N / m"
      define l :: real where "l = 4"
      define l_0 :: real where "l_0 = 4 - 1/6"
      have 0: "x \<ge> 2" unfolding x_def using assms(2)
        by (metis assms(1) divide_right_mono dual_order.trans linorder_le_cases mult.commute mult_1 nonzero_mult_div_cancel_left numeral_le_one_iff semiring_norm(70) zero_le_square)
      have 1: "L = sqrt (8*x - 8) - sqrt (6*x - 3) + 1/6" by (auto simp add: x_def assms(3))
      hence 2: "L > l \<longleftrightarrow> sqrt (8*x - 8) > sqrt (6*x - 3) + l_0" unfolding l_0_def l_def by auto
      have 3: "sqrt (8*x - 8) > sqrt (6*x - 3) + l_0 \<longleftrightarrow> 2*x - l_0^2 - 5 > 2*l_0 * sqrt (6*x - 3)"
      proof
        assume "sqrt (8*x - 8) > sqrt (6*x - 3) + l_0"
        hence "(sqrt (8*x - 8))^2 > (sqrt (6*x - 3) + l_0)^2" 
          using l_0_def asm by (smt (verit, ccfv_SIG) "0" divide_less_eq_1_pos one_power2 pos2 power_mono_iff real_less_rsqrt)
        hence "8*x - 8 > 6*x - 3 + l_0^2 + 2*l_0* sqrt (6*x - 3)"
          by (smt (verit, del_insts) "0" power2_sum real_sqrt_pow2_iff)
        thus "2*x - l_0^2 - 5 > 2*l_0* sqrt (6*x - 3)" by auto
      next
        assume "2*x - l_0^2 - 5 > 2*l_0* sqrt (6*x - 3)"
        hence "8*x - 8 > 6*x - 3 + l_0^2 + 2*l_0* sqrt (6*x - 3)" by auto
        hence "(sqrt (8*x - 8))^2 > (sqrt (6*x - 3) + l_0)^2"
          by (smt (verit, best) 0 power2_sum real_sqrt_pow2_iff)
        thus "sqrt (8*x - 8) > sqrt (6*x - 3) + l_0"
          using 0 real_less_rsqrt by force 
      qed
      have "2*x - l_0^2 - 5 > 2*l_0* sqrt (6*x - 3) \<longleftrightarrow> 4*x*(x - (7*l_0^2 + 5)) + (l_0^2 + 5)^2 + 12*l_0^2 > 0"
      proof
        assume "2*x - l_0^2 - 5 > 2*l_0* sqrt (6*x - 3)"
        hence "(2*x - l_0^2 - 5)^2 > (2*l_0* sqrt (6*x - 3))^2"
          by (smt (verit, del_insts) "0" asm l_0_def le_divide_eq_1_pos less_1_mult one_power2 pos2 power_mono_iff sqrt_le_D)
        thus "4*x*(x - (7*l_0^2 + 5)) + (l_0^2 + 5)^2 + 12*l_0^2 > 0"
          using 0 by (simp add: algebra_simps power2_eq_square power4_eq_xxxx)
      next
        assume "4*x*(x - (7*l_0^2 + 5)) + (l_0^2 + 5)^2 + 12*l_0^2 > 0"
        hence "(2*x - l_0^2 - 5)^2 > (2*l_0* sqrt (6*x - 3))^2"
          using 0 by (simp add: algebra_simps power2_eq_square power4_eq_xxxx)
        from assms(1) have "m > 0" by auto
        hence "2*x \<ge> 2*108"
          using x_def asm by (simp add: le_divide_eq)
        hence "2*x - l_0^2 - 5 \<ge> 2*108 - (4-1/6)*(4-1/6) - 5" unfolding l_0_def by (auto simp add: power2_eq_square)
        hence "2*x - l_0^2 - 5 > 0" by auto
        thus "2*x - l_0^2 - 5 > 2*l_0* sqrt (6*x - 3)"
          using \<open>(2*x - l_0^2 - 5)^2 > (2*l_0* sqrt (6*x - 3))^2\<close> using power2_less_imp_less by fastforce
      qed
      from assms(1) have "m > 0" by auto
      hence "x \<ge> 108" using x_def asm by (simp add: le_divide_eq)
      have "7*(4-1/6)*(4-1/6) + 5 < (108::real)" by simp
      hence "7*l_0^2 + 5 < 108" unfolding l_0_def by (auto simp add: power2_eq_square)
      hence "x \<ge> 7*l_0^2 + 5" using \<open>108 \<le> x\<close> by auto
      hence "4*x*(x - (7*l_0^2 + 5)) + (l_0^2 + 5)^2 + 12*l_0^2 > 0"
        by (smt (verit) mult_nonneg_nonneg power2_less_eq_zero_iff zero_le_power2)
      thus ?thesis
        using "2" "3" \<open>(2 * l_0 * sqrt (6 * x - 3) < 2 * x - l_0\<^sup>2 - 5) = (0 < 4 * x * (x - (7 * l_0\<^sup>2 + 5)) + (l_0\<^sup>2 + 5)\<^sup>2 + 12 * l_0\<^sup>2)\<close> l_def by blast
    qed
  qed

theorem interval_length_greater_than_lm:
  fixes m N :: real
  fixes L l :: real
  assumes "m \<ge> 3"
  assumes "N \<ge> 2*m"
  assumes "L = (2/3 + sqrt (8*N/m - 8)) - (1/2 + sqrt (6*N/m - 3))"
  shows "l \<ge> 2 \<and> N \<ge> 7*l^2*m^3 \<Longrightarrow> L > l*m"

proof -
  assume asm: "l \<ge> 2 \<and> N \<ge> 7*l^2*m^3"
  show "L > l*m"
  proof -
    from asm have asm1: "l \<ge> 2" and asm2: "N \<ge> 7*l^2*m^3" by auto
    define x :: real where "x = N / m"
    define l_0 :: real where "l_0 = l*m - 1/6" 
    have "l_0 > 0" using l_0_def asm1 assms(1)
      by (smt (verit, ccfv_threshold) le_divide_eq_1 mult_le_cancel_left2 of_int_le_1_iff)
    have 0: "x \<ge> 2" using x_def assms(1,2) by (simp add: pos_le_divide_eq)
    have 1: "L = sqrt (8*x - 8) - sqrt (6*x - 3) + 1/6" by (auto simp add: x_def assms(3))
    hence 2: "L > l*m \<longleftrightarrow> sqrt (8*x - 8) > sqrt (6*x - 3) + l_0" by (auto simp add: l_0_def)
    have 3: "sqrt (8*x - 8) > sqrt (6*x - 3) + l_0 \<longleftrightarrow> 2*x - l_0^2 - 5 > 2*l_0 * sqrt (6*x - 3)"
    proof
      assume "sqrt (8*x - 8) > sqrt (6*x - 3) + l_0"
      hence "(sqrt (8*x - 8))^2 > (sqrt (6*x - 3) + l_0)^2" 
        using l_0_def asm1 by (smt (verit, best) \<open>0 < l_0\<close> real_le_lsqrt real_sqrt_four real_sqrt_less_iff real_sqrt_pow2_iff)
      hence "8*x - 8 > 6*x - 3 + l_0^2 + 2* l_0 * sqrt (6*x - 3)"
        by (smt (verit, del_insts) "0" power2_sum real_sqrt_pow2_iff)
      thus "2*x - l_0^2 - 5 > 2*l_0 * sqrt (6*x - 3)" by auto
    next
      assume "2*x - l_0^2 - 5 > 2*l_0 * sqrt (6*x - 3)"
      hence "8*x - 8 > 6*x - 3 + l_0^2 + 2*l_0 * sqrt (6*x - 3)" by auto
      hence "(sqrt (8*x - 8))^2 > (sqrt (6*x - 3) + l_0)^2"
        by (smt (verit, del_insts) "0" power2_sum real_sqrt_pow2_iff)
      thus "sqrt (8*x - 8) > sqrt (6*x - 3) + l_0"
        using 0 real_less_rsqrt by force 
    qed
    have "2*x - l_0^2 - 5 > 2*l_0 * sqrt (6*x - 3) \<longleftrightarrow> 4*x*(x - (7*l_0^2 + 5)) + (l_0^2 + 5)^2 + 12*l_0^2 > 0"
    proof
      assume "2*x - l_0^2 - 5 > 2*l_0 * sqrt (6*x - 3)"
      have "(2*x - l_0^2 - 5)^2 > (2*l_0 * sqrt (6*x - 3))^2"
        using \<open>0 < l_0\<close> by (smt (verit, ccfv_SIG) 0 \<open>2 * l_0 * sqrt (6 * x - 3) < 2 * x - l_0\<^sup>2 - 5\<close> pos2 power_strict_mono real_sqrt_ge_zero zero_le_mult_iff)
      thus "4*x*(x - (7*l_0^2 + 5)) + (l_0^2 + 5)^2 + 12*l_0^2 > 0"
        using 0 by (simp add: algebra_simps power2_eq_square power4_eq_xxxx)
    next
      assume "4*x*(x - (7*l_0^2 + 5)) + (l_0^2 + 5)^2 + 12*l_0^2 > 0"
      hence "(2*x - l_0^2 - 5)^2 > (2*l_0 * sqrt (6*x - 3))^2"
        using 0 by (simp add: algebra_simps power2_eq_square power4_eq_xxxx)
      have "m > 0" using assms(1) by simp
      hence "x \<ge> 7*l^2*m^2" 
        unfolding x_def using asm2 assms(1)
        by (simp add: mult_imp_le_div_pos power2_eq_square power3_eq_cube)
      hence 4: "2*x - l_0^2 - 5 \<ge> 14*l^2*m^2 - (l*m-1/6)^2 - 5" 
        by (simp add: x_def l_0_def power2_eq_square)
      have "(l*m-(1/6::real))^2 = (l*m)^2 - l*m/3 + (1/36::real)"
        apply (simp add: power2_eq_square)
        by argo
      hence "14*l^2*m^2 - (l*m-1/6)^2 - 5 = 14*l^2*m^2 - l^2*m^2 + l*m/3 - 1/36 - 5"
        using 4 by (auto simp add: power2_eq_square)
      hence "14*l^2*m^2 - l^2*m^2 + l*m/3 - 1/36 - 5 = 13*l^2*m^2  + l*m/3 - 1/36 - 5" by argo
      from asm1 assms(1) have 5: "l*m/3 > 0" by simp
      have "l > 0" using asm1 by auto 
      hence "l*l \<ge> 2*2" using asm1 mult_mono' zero_le_numeral by blast
      have "m > 0" using assms(1) by auto
      hence "m*m \<ge> 3*3"
        by (metis assms(1) less_eq_real_def mult_le_less_imp_less zero_less_numeral)
      hence "13*m*m - 1 \<ge> 13*3*3-1" by simp
      have "3*3 > (0::real)" by auto
      hence "13*l*l*m*m \<ge>(13::real)*2*2*3*3" using \<open>l*l \<ge> 2*2\<close> asm1
        by (meson \<open>0 < l\<close> \<open>0 < m\<close> assms(1) less_eq_real_def mult_mono split_mult_pos_le zero_le_numeral)
      hence "13*l^2*m^2  + l*m/3 - 1/36 - 5 \<ge> 13*2*2*3*3-1/36-(5::real)"
        using 5 by (auto simp add: power2_eq_square)
      have "13*3*3*3*3-1/36-(5::real) > 0" by auto
      hence "2*x - l_0^2 - 5 > 0"
        using "4" \<open>13 * 2 * 2 * 3 * 3 - 1 / 36 - 5 \<le> 13 * l\<^sup>2 * m\<^sup>2 + l * m / 3 - 1 / 36 - 5\<close> \<open>14 * l\<^sup>2 * m\<^sup>2 - (l * m - 1 / 6)\<^sup>2 - 5 = 14 * l\<^sup>2 * m\<^sup>2 - l\<^sup>2 * m\<^sup>2 + l * m / 3 - 1 / 36 - 5\<close> by force
      thus "2*x - l_0^2 - 5 > 2*l_0 * sqrt (6*x - 3)"
        by (smt (verit) \<open>(2 * l_0 * sqrt (6 * x - 3))\<^sup>2 < (2 * x - l_0\<^sup>2 - 5)\<^sup>2\<close> power_mono)
    qed
    have "(1/6)^2 * (36::real) = 1" by (auto simp add: power2_eq_square)
    from assms(1) have "m > 0" by auto
    hence "x \<ge> 7*l^2*m^2" unfolding x_def using asm2
      by (simp add: pos_le_divide_eq power2_eq_square power3_eq_cube)
    from asm1 have "l > 0" by auto
    from assms(1) asm1 \<open>m > 0\<close> \<open>l > 0\<close> have "l*m \<ge> 2*(3::real)"
      by (metis mult_less_cancel_right mult_mono verit_comp_simplify1(1) verit_comp_simplify1(3) zero_le_numeral)
    hence "-2*7*l*m/6 + 7*(1/6)*(1/6) + 5 < (0::real)" by simp
    hence "7*l^2*m^2 > 7*l_0^2 + (5::real)" unfolding l_0_def
      apply (auto simp add: power2_eq_square)
      by argo
    hence "x \<ge> 7*l_0^2 + 5"
      using \<open>7 * l\<^sup>2 * m\<^sup>2 \<le> x\<close> by linarith
    hence "4*x*(x - (7*l_0^2 + 5)) + (l_0^2 + 5)^2 + 12*l_0^2 > 0"
      by (smt (verit) mult_nonneg_nonneg power2_less_eq_zero_iff zero_le_power2)
    thus ?thesis
      using "2" "3" \<open>(2 * l_0 * sqrt (6 * x - 3) < 2 * x - l_0\<^sup>2 - 5) = (0 < 4 * x * (x - (7 * l_0\<^sup>2 + 5)) + (l_0\<^sup>2 + 5)\<^sup>2 + 12 * l_0\<^sup>2)\<close> by fastforce
  qed
qed

lemmas interval_length_greater_than_2m [simp] = interval_length_greater_than_lm [where l=2, simplified]

subsection \<open> Lemma 1.11 in \cite{nathanson1996} \<close>

text \<open> We show Lemma 1.11 in \cite{nathanson1996} which is also known as Cauchy's Lemma.\<close>

theorem Cauchy_lemma:
  fixes m N a b r :: real
  assumes "m \<ge> 3" "N \<ge> 2*m"
  and "0 \<le> a" "0 \<le> b" "0 \<le> r" "r < m"
  and "N = m*(a - b)/2 + b + r"
  and "1/2 + sqrt (6*N/m - 3) \<le> b \<and> b \<le> 2/3 + sqrt (8*N/m - 8)"
  shows "b^2 < 4*a \<and> 3*a < b^2 + 2*b + 4"

proof-
  from assms have asm1: "1/2 + sqrt (6*N/m - 3) \<le> b" and asm2: "b \<le> 2/3 + sqrt (8*N/m - 8)" by auto
  have "N - b - r = m*(a - b)/2" using assms(7) by simp
  hence "a = (N - b - r)*2/m + b" using assms(1) by simp
  hence "a = b - 2/m * b + 2 * (N - r)/m"
    apply (simp add: algebra_simps)
    by (smt (verit, del_insts) add_divide_distrib)
  hence a: "a = b*(1 - 2/m) + 2*(N - r)/m"
    by (simp add: right_diff_distrib')
  have "b^2 < 4*a"
  proof -
    from a have 0: "b^2 - 4*a = b^2 - 4*(1 - 2/m)*b - 8*(N-r)/m" by simp
    have "3/m \<le> 1" using assms(1) by simp
    hence 1: "2/3 \<le> 2*(1 - 2/m)" by simp
    have "N/m - 1 < N/m - r/m" using assms(1,6) by simp
    hence "sqrt(8*(N/m - 1)) < sqrt (8*((N - r)/m))" by (simp add: diff_divide_distrib)
    hence 2: "sqrt(8*N/m - 8) < sqrt (8*((N - r)/m))" by simp
    have "2/3 + sqrt (8*N/m - 8) < 2*(1 - 2/m) + sqrt (8*((N-r)/m))"
      using 1 2 by linarith
    hence "b < 2*(1-2/m) + sqrt (8*(N - r)/m)" using asm2 by simp
    hence 3: "b < 2*(1-2/m) + sqrt (4*(1-2/m)^2 + 8*(N - r)/m)"
      by (smt (verit, best) power2_less_0 real_sqrt_le_iff)
    define r1 where "r1 = 2*(1-2/m) - sqrt (4*(1-2/m)^2 + 8*(N - r)/m)"
    define r2 where "r2 = 2*(1-2/m) + sqrt (4*(1-2/m)^2 + 8*(N - r)/m)"

    have "r1*r2 = (2*(1-2/m) - sqrt (4*(1-2/m)^2 + 8*(N - r)/m))*(2*(1-2/m) + sqrt (4*(1-2/m)^2 + 8*(N - r)/m))"
      using r1_def r2_def by simp
    hence "r1*r2 = 2*(1-2/m)*(2*(1-2/m) + sqrt (4*(1-2/m)^2 + 8*(N - r)/m)) - 
sqrt (4*(1-2/m)^2 + 8*(N - r)/m)*(2*(1-2/m) + sqrt (4*(1-2/m)^2 + 8*(N - r)/m))" 
      by (simp add: Rings.ring_distribs(3)) 
    hence "r1*r2 = (2*(1-2/m))^2+2*(1-2/m)* sqrt (4*(1-2/m)^2 + 8*(N - r)/m) - 2*(1-2/m)* sqrt (4*(1-2/m)^2 + 8*(N - r)/m)
- (sqrt (4*(1-2/m)^2 + 8*(N - r)/m))^2" by (simp add: distrib_left power2_eq_square)
    hence "r1*r2 = (2*(1-2/m))^2 -(sqrt (4*(1-2/m)^2 + 8*(N - r)/m))^2" by simp

    hence "r1 * r2  = 4*(1-2/m)^2 - 4*(1-2/m)^2 - 8*(N - r)/m"
      using assms(1) assms(2) assms(6) four_x_squared
      by (smt (verit) divide_nonneg_nonneg real_sqrt_pow2_iff zero_compare_simps(12))
    hence r1_times_r2:"r1*r2 = -8*(N-r)/m" by linarith

    have "(b-r1)*(b-r2) = b*(b-r2) - r1*(b-r2)" using cross3_simps(28) by blast
    hence "(b-r1)*(b-r2) = b^2-b*r2-b*r1+r1*r2" by (simp add: power2_eq_square right_diff_distrib)
    hence "(b-r1)*(b-r2) = b^2-b*(2*(1-2/m) + sqrt (4*(1-2/m)^2 + 8*(N - r)/m))-b*(2*(1-2/m) - sqrt (4*(1-2/m)^2 + 8*(N - r)/m))+r1*r2"
      using r1_def r2_def by simp
    hence "(b-r1)*(b-r2) = b^2-b*2*(1-2/m)-b* sqrt (4*(1-2/m)^2 + 8*(N - r)/m)-b*(2*(1-2/m) - sqrt (4*(1-2/m)^2 + 8*(N - r)/m)) +r1*r2" 
      by (simp add: distrib_left)
    hence "(b-r1)*(b-r2) = b^2-b*2*(1-2/m)-b* sqrt (4*(1-2/m)^2 + 8*(N - r)/m)-b*2*(1-2/m)+b* sqrt (4*(1-2/m)^2 + 8*(N - r)/m)+r1*r2"
      by (simp add: Rings.ring_distribs(4))
    hence "(b-r1)*(b-r2) = b^2-b*4*(1-2/m)+r1*r2" by simp
    hence "(b-r1)*(b-r2) = b^2 - 4*(1 - 2/m)*b - 8*(N-r)/m" using r1_times_r2
      by (simp add: \<open>r1 * r2 = 4 * (1 - 2 / m)\<^sup>2 - 4 * (1 - 2 / m)\<^sup>2 - 8 * (N - r) / m\<close>)
    hence "b^2 - 4*(1 - 2/m)*b - 8*(N-r)/m < 0" using 3 assms(4)
      by (smt (verit, del_insts) \<open>r1 * r2 = 4 * (1 - 2 / m)\<^sup>2 - 4 * (1 - 2 / m)\<^sup>2 - 8 * (N - r) / m\<close> assms(1) assms(2) assms(6) divide_pos_pos mult_nonneg_nonneg mult_pos_neg r2_def)
    thus ?thesis using 0 by simp
  qed
  have "3*a < b^2 + 2*b + 4"
  proof - 
    from a have 4: "b^2 + 2*b + 4 - 3*a = b^2 - (1-6/m)*b - (6*(N-r)/m - 4)" by argo
    have 5: "1/2 > 1/2 - 3/m" using assms(1) by simp
    hence "1/2 - 3/m < 1" by linarith
    also have "1/2 - 3/m > -1" using assms(1)
      by (smt (verit) divide_le_0_1_iff less_divide_eq_1_pos)
    hence "(1/2 - 3/m)^2 < 1" 
      by (metis (no_types, opaque_lifting) calculation less_eq_real_def power2_eq_1_iff square_le_1 verit_comp_simplify1(3))
    hence 6: "sqrt (6*N/m - 3) > sqrt ((1/2 - 3/m)^2 + 6*N/m - 4)" using assms(1) by simp
    from asm1 5 6 have "b > (1/2 - 3/m) + sqrt ((1/2 - 3/m)^2 + 6*N/m - 4)" by linarith
    hence 7: "b > (1/2 - 3/m) + sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4)"
      by (smt (verit, ccfv_SIG) assms(1) assms(5) divide_right_mono real_sqrt_le_mono)
    define s1 where "s1 = (1/2 - 3/m) - sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4)"
    define s2 where "s2 = (1/2 - 3/m) + sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4)"
    have "s1* s2=(1/2-3/m)*((1/2 - 3/m) + sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4))- 
sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4)*((1/2 - 3/m) + sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4))"
      using s1_def s2_def Rings.ring_distribs(3) by blast
    hence "s1* s2= (1/2-3/m)^2+(1/2-3/m)* sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4)- 
sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4)*((1/2 - 3/m) + sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4))"
      by (simp add: nat_distrib(2) power2_eq_square)
    hence "s1* s2= (1/2-3/m)^2+(1/2-3/m)* sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4)-
(1/2-3/m)* sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4) - (sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4))^2"
      by (smt (verit, ccfv_SIG) Groups.mult_ac(2) Rings.ring_distribs(3) power2_eq_square)
    hence 8:"s1* s2=(1/2-3/m)^2- (sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4))^2" by simp
    from assms(1,6) have "-r/m > -1" by simp
    hence "-6*r/m > -6" by simp
    hence "12 - 4 - 6*r/m > 0" by simp
    hence "12*m/m - 6*r/m - 4 > 0" using assms(1) by simp
    hence "6*(2*m - r)/m - 4 > 0" by argo
    hence "6*(N - r)/m - 4 > 0" using assms(1,2)
      by (smt (verit, best) divide_right_mono)
    hence "s1 * s2 = (1/2 - 3/m)^2 - (1/2 - 3/m)^2 - 6*(N - r)/m + 4" using 8
      by (smt (verit) real_sqrt_pow2_iff zero_le_power2)

    have "(b-s1)*(b-s2) = b*(b-s2) - s1*(b-s2)" using cross3_simps(28) by blast
    hence "(b-s1)*(b-s2) = b^2-b* s2-b* s1+s1* s2" by (simp add: power2_eq_square right_diff_distrib)
    hence "(b-s1)*(b-s2) = b^2-b*((1/2 - 3/m) + sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4))-b*((1/2 - 3/m) - sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4))
+ s1* s2" using s1_def s2_def by simp
    hence "(b-s1)*(b-s2) = b^2-b*(1/2 - 3/m)-b* sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4)-b*((1/2 - 3/m) - sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4))
+ s1* s2" by (simp add: nat_distrib(2))
    hence "(b-s1)*(b-s2) = b^2-b*(1/2 - 3/m)-b* sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m - 4)-b*(1/2 - 3/m)+b* sqrt ((1/2 - 3/m)^2 + 6*(N - r)/m-4)+s1* s2"
      by (smt (verit, ccfv_SIG) nat_distrib(2))
    hence "(b-s1)*(b-s2) = b^2-2*b*(1/2 - 3/m)+s1* s2" by simp
    hence "(b-s1)*(b-s2) = b^2-2*b*(1/2 - 3/m)+ (1/2 - 3/m)^2 - (1/2 - 3/m)^2 - 6*(N - r)/m + 4"
      using \<open>s1 * s2 = (1 / 2 - 3 / m)\<^sup>2 - (1 / 2 - 3 / m)\<^sup>2 - 6 * (N - r) / m + 4\<close> by fastforce
    hence "(b-s1)*(b-s2) = b^2-2*b*(1/2-3/m)- 6*(N - r)/m + 4" by simp
    hence "(b-s1)*(b-s2) = b^2-b*(1-6/m)- 6*(N - r)/m + 4" by simp
    hence "(b-s1)*(b-s2) = b^2-b*(1-6/m)- (6*(N - r)/m - 4)" by simp
    hence "b^2 - (1-6/m)*b - (6*(N-r)/m - 4) > 0" using 7 by (smt (verit, del_insts) "8" Groups.mult_ac(2) 
\<open>s1 * s2 = (1 / 2 - 3 / m)\<^sup>2 - (1 / 2 - 3 / m)\<^sup>2 - 6 * (N - r) / m + 4\<close> real_sqrt_ge_0_iff s1_def s2_def zero_compare_simps(8) zero_le_power2)
    thus ?thesis using 4 by simp
  qed
  show ?thesis by (simp add: \<open>3 * a < b\<^sup>2 + 2 * b + 4\<close> \<open>b\<^sup>2 < 4 * a\<close>)
qed

lemmas Cauchy_lemma_r_eq_zero = Cauchy_lemma [where r=0, simplified]

subsection \<open> Lemma 1.12 in \cite{nathanson1996} \<close>

lemma not_one:
  fixes a b :: nat
  assumes "a\<ge>1"
  assumes "b\<ge>1"
  assumes "\<exists>k1 :: nat. a = 2*k1+1"
  assumes "\<exists>k2 :: nat. b = 2*k2+1"
  assumes "b^2 < 4*a"
  shows "4*a-b^2 \<noteq> 1"

proof 
  assume "4*a-b^2 = 1"
  hence "b^2 = 4*a-1" by auto
  hence "b^2 mod 4 = (4*a-1) mod 4" by auto
  have "(4*a-1) mod 4 = 3 mod 4" using assms(1) by (simp add: mod_diff_eq_nat)
  hence "b^2 mod 4 = 3" using \<open>b^2 = 4*a-1\<close> mod_less by presburger
  thus "False" using assms by (metis One_nat_def eq_numeral_Suc insert_iff nat.simps(3)
 power_two_mod_four pred_numeral_simps(3) singletonD)
qed


lemma not_two:
  fixes a b :: nat
  assumes "a\<ge>1"
  assumes "b\<ge>1"
  assumes "\<exists>k1 :: nat. a = 2*k1+1"
  assumes 1:"\<exists>k2 :: nat. b = 2*k2+1"
  assumes "b^2 < 4*a"
  shows "4*a-b^2 \<noteq> 2"

proof
  assume "4*a-b^2=2"
  hence "b^2=4*a-2" by auto
  from 1 have 2: "\<not> 2 dvd b^2" by auto
  have "2 dvd (4*a-2)" by auto
  thus "False" using \<open>b^2=4*a-2\<close> 2 by auto
qed

text \<open>The following lemma shows that given odd positive integers $x,y,z$ and $b$, where $x \geq y \geq z$, we may pick 
a suitable integer $u$ where $u = z$ or $u = -z$, such that $b+x+y+u \equiv 0 \pmod{4}$.\<close>

lemma suit_z:
  fixes b x y z :: nat
  assumes "odd b \<and> odd x \<and> odd y \<and> odd z"
  assumes "x\<ge>y \<and> y\<ge>z"
  shows "\<exists> u :: int. (u=z \<or> u=-z) \<and> (b+x+y+u) mod 4 = 0" 

proof -
  from assms have 0: "(b+x+y) mod 4 = 1 \<or> (b+x+y) mod 4 = 3" by (metis dvd_refl even_add 
even_even_mod_4_iff landau_product_preprocess(53) mod_exhaust_less_4)
  from assms have 1: "z mod 4 = 1 \<or> z mod 4 = 3" by (metis dvd_0_right dvd_refl
 even_even_mod_4_iff mod_exhaust_less_4)

  have c1:"\<exists>u1::int. (u1=z \<or> u1=-z) \<and> (b+x+y+u1) mod 4 = 0" 
    if asm1:"(b+x+y) mod 4 = 1 \<and> z mod 4 = 3"
  proof -
    from asm1 have 2:"(b+x+y+z) mod 4 = 0" by (metis add_num_simps(1) add_num_simps(7)
 mod_add_eq mod_self numeral_plus_one one_plus_numeral_commute)
    define u1 :: int where "u1=z"
    show "\<exists>u1::int. (u1=z \<or> u1=-z) \<and> (b+x+y+u1) mod 4 = 0" using "2" u1_def
      by (metis Num.of_nat_simps(4) of_nat_0 of_nat_numeral zmod_int)
  qed

  have c2:"\<exists>u2::int.(u2=z \<or> u2=-z) \<and> (b+x+y+u2) mod 4 = 0" 
    if asm2:"(b+x+y) mod 4 = 1 \<and> z mod 4 = 1"
  proof -
    from asm2 have 3:"(b+x+y-z) mod 4 = 0" 
      by (metis assms(2) mod_eq_0_iff_dvd mod_eq_dvd_iff_nat trans_le_add2)
    define u2::int where "u2=-z"
    show "\<exists>u2::int.(u2=z \<or> u2=-z) \<and> (b+x+y+u2) mod 4 = 0" using "3" u2_def 
      by (metis Num.of_nat_simps(2) asm2 mod_0
 mod_add_cong more_arith_simps(4) of_nat_numeral zmod_int)
  qed

  have c3:"\<exists>u3::int.(u3=z \<or> u3=-z) \<and> (b+x+y+u3) mod 4 = 0" 
    if asm3:"(b+x+y) mod 4 = 3 \<and> z mod 4 = 1"
  proof -
    from asm3 have 4: "(b+x+y+z) mod 4 = 0" by (metis add_num_simps(1) add_num_simps(7)
 mod_add_eq mod_self numeral_plus_one)
    define u3::int where "u3=z"
    show "\<exists>u3::int.(u3=z \<or> u3=-z) \<and> (b+x+y+u3) mod 4 = 0" using "4" u3_def
      by (metis Num.of_nat_simps(4) of_nat_0 of_nat_numeral zmod_int)
  qed

  have c4:"\<exists>u4::int.(u4=z \<or> u4=-z) \<and> (b+x+y+u4) mod 4 = 0" 
    if asm4:"(b+x+y) mod 4 = 3 \<and> z mod 4 = 3"
  proof -
    from asm4 have 5: "(b+x+y-z) mod 4 = 0" 
      by (metis assms(2) mod_eq_0_iff_dvd mod_eq_dvd_iff_nat trans_le_add2)
    define u4::int where "u4=-z"
    show "\<exists>u4::int.(u4=z \<or> u4=-z) \<and> (b+x+y+u4) mod 4 = 0" using "5" u4_def by (metis asm4 mod_0
 mod_add_cong more_arith_simps(4) of_nat_numeral zmod_int)
  qed

  show ?thesis using assms 0 1 c1 c2 c3 c4 by auto
qed

lemma four_terms_bin_exp_allsum:
  fixes b s t u v :: int
  assumes "b = s+t+u+v"
  shows "b^2 =  t^2+u^2+s^2+v^2+2*t*u+2 * s * v + 2*t * s + 2*t * v +2*u * s +2*u * v"

proof -
  from assms have "b^2 = (t+u)^2+(s+v)^2+2*(t+u)*(s+v)" by (smt (verit, best) power2_sum)  
  hence b_simp1:"b^2 = (t^2+u^2+2*t*u) + (s^2+v^2+2 * s * v)+2*(t+u)*(s+v)" 
    by (simp add: power2_sum)
  have "2*(t+u)*(s+v) =  2*t * s + 2*t * v +2*u * s +2*u * v"
    using int_distrib(1) int_distrib(2) by force
  from this b_simp1 have b_expression:"b^2 = t^2+u^2+s^2+v^2+2*t*u+2 * s * v + 
2*t * s + 2*t * v +2*u * s +2*u * v" by auto
  thus ?thesis by auto
qed

lemma four_terms_bin_exp_twodiff:
  fixes b s t u v :: int
  assumes "b = s+t-u-v"
  shows "b^2 =  t^2+u^2+s^2+v^2-2*t*u-2 * s * v + 2*t * s - 2*t * v -2*u * s +2*u * v"

proof -
  from assms have "b^2 = (s-u)^2+(t-v)^2+2*(s-u)*(t-v)" by (smt (verit, best) power2_sum) 
  hence b_simp1:"b^2 = s^2+u^2-2 * s *u + t^2+v^2 - 2 * t * v + 2*(s-u)*(t-v)"
    by (simp add: power2_diff)
  have "2*(s-u)*(t-v) = 2* s * t - 2* s * v - 2*u*t+2*u * v" 
    by (simp add: Rings.ring_distribs(3) Rings.ring_distribs(4))
  from this b_simp1 have b_expression: "b^2 =  t^2+u^2+s^2+v^2-2*t*u-2 * s * v + 
2*t * s - 2*t * v -2*u * s +2*u * v" by auto
  thus ?thesis by auto
qed

text\<open>If a quadratic with positive leading coefficient is always non-negative, its discriminant is
non-positive.\<close>

lemma qua_disc:
  fixes a b c :: real
  assumes "a>0"
  assumes "\<forall>x::real. a*x^2+b*x+c \<ge>0"
  shows "b^2 - 4*a*c \<le> 0"

proof -
  from assms have 0:"\<forall>x::real. (a*x^2+b*x+c)/a \<ge>0" by simp
  from assms have 1:"\<forall>x::real.(b*x+c)/a = b/a*x+c/a" by (simp add: add_divide_distrib)
  from assms have "\<forall>x::real.(a*x^2+b*x+c)/a = x^2+(b*x+c)/a" by (simp add: is_num_normalize(1))
  from 1 this have "\<forall>x::real.(a*x^2+b*x+c)/a = x^2+b/a*x+c/a" by simp
  hence atleastzero:"\<forall>x::real. x^2+b/a*x+c/a \<ge>0" using 0 by simp

  from assms have 2:"\<forall>x::real. x^2+b/a*x+c/a = x^2+2*b/(2*a)*x+c/a+b^2/(4*a^2)-b^2/(4*a^2)" by simp
  have simp1:"\<forall>x::real.(x+b/(2*a))^2 = x^2+2*b/(2*a)*x+(b/(2*a))^2" by (simp add: power2_sum)
  have "(b/(2*a))^2 = b^2/(4*a^2)" by (metis four_x_squared power_divide)
  hence "\<forall>x::real. x^2+b/a*x+c/a = (x+b/(2*a))^2+c/a-b^2/(4*a^2)" using 2 simp1 by auto
  hence "\<forall>x::real. (x+b/(2*a))^2+c/a-b^2/(4*a^2) \<ge>0" using atleastzero by presburger
  hence 3:"\<forall>x::real. b^2/(4*a^2)-c/a\<le>(x+b/(2*a))^2" by (smt (verit, del_insts))
  have "\<exists>x::real. (x+b/(2*a))^2=0" by (metis diff_add_cancel power_zero_numeral)
  hence "b^2/(4*a^2)-c/a\<le>0" using 3 by metis
  hence 4:"4*a^2*(b^2/(4*a^2)-c/a)\<le>0" using assms by (simp add: mult_nonneg_nonpos)
  have 5:"4*a^2*b^2/(4*a^2) = b^2" using assms by simp
  have 6:"4*a^2*c/a = 4*a*c" using assms by (simp add: power2_eq_square)
  show ?thesis using 4 5 6 assms by (simp add: Rings.ring_distribs(4))
qed

text\<open>The following lemma shows for any point on a 3D sphere with radius $a$, the sum of its coordinates 
lies between $\sqrt{3a}$ and $-\sqrt{3a}$.\<close>

lemma three_terms_Cauchy_Schwarz:
  fixes x y z a :: real
  assumes "a > 0"
  assumes "x^2+y^2+z^2 = a"
  shows "(x+y+z)\<ge>-sqrt(3*a) \<and> (x+y+z)\<le>sqrt(3*a)"

proof -
  have 1:"\<forall>t::real. (t*x+1)^2 = t^2*x^2+1+2*t*x" by (simp add: power2_sum power_mult_distrib)
  have 2:"\<forall>t::real. (t*y+1)^2 = t^2*y^2+1+2*t*y" by (simp add: power2_sum power_mult_distrib)
  have 3:"\<forall>t::real. (t*z+1)^2 = t^2*z^2+1+2*t*z" by (simp add: power2_sum power_mult_distrib)
  from 1 2 3 have 4:"\<forall>t::real.(t*x+1)^2+(t*y+1)^2+(t*z+1)^2 = t^2*x^2+1+2*t*x + t^2*y^2+1+2*t*y +
t^2*z^2+1+2*t*z" by auto

  have "\<forall>t::real. t^2*x^2+t^2*y^2=t^2*(x^2+y^2)" by (simp add: nat_distrib(2))
  hence 5:"\<forall>t::real. t^2*x^2+t^2*y^2+t^2*z^2=t^2*(x^2+y^2+z^2)" by (metis nat_distrib(2))
  have 6:"\<forall>t::real. 2*t*x+2*t*y+2*t*z = t*2*(x+y+z)" by (simp add: Groups.mult_ac(2) distrib_right)
  from 4 5 6 have "\<forall>t::real.(t*x+1)^2+(t*y+1)^2+(t*z+1)^2 = t^2*(x^2+y^2+z^2)+ t*2*(x+y+z)+3" 
    by (smt (verit, best))
  hence "\<forall>t::real. t^2*(x^2+y^2+z^2)+ t*2*(x+y+z)+3 \<ge>0" by (metis add_nonneg_nonneg zero_le_power2)
  hence "(2*(x+y+z))^2 - 12*(x^2+y^2+z^2)\<le>0" using qua_disc
    by (smt (z3) power2_diff power2_sum power_zero_numeral sum_squares_bound)
  hence "12*(x^2+y^2+z^2)\<ge>4*(x+y+z)^2" by (simp add: four_x_squared)
  hence "3*a\<ge>(x+y+z)^2" using assms by auto
  thus ?thesis by (smt (verit, del_insts) real_sqrt_abs real_sqrt_le_iff)
qed

text\<open>We adapt the lemma above through changing the types for the convenience of our proof.\<close>

lemma three_terms_Cauchy_Schwarz_nat_ver:
  fixes x y z a :: nat
  assumes "a>0"
  assumes "x^2+y^2+z^2 = a"
  shows "(x+y+z)\<ge>-sqrt(3*a) \<and> (x+y+z)\<le>sqrt(3*a)"

proof -
  have fac1:"real(x+y+z) = real x + real y + real z" by auto
  have fac2: "3*(real a) = real(3*a)" by auto
  thus ?thesis using fac1 three_terms_Cauchy_Schwarz fac2 by (smt (verit) assms(1) assms(2) nat_less_real_le of_nat_0_le_iff of_nat_add of_nat_power)
qed

text\<open>This theorem is Lemma 1.12 in \cite{nathanson1996}, which shows for odd positive integers $a$ and $b$ 
satisfying certain properties, there exist four non-negative integers $s,t,u$ and $v$ such that 
$a = s^2+t^2+u^2+v^2$ and $b = s+t+u+v$. We use the Three Squares Theorem AFP entry \cite{Three_Squares-AFP}.\<close>

theorem four_nonneg_int_sum:
  fixes a b :: nat
  assumes "a\<ge>1"
  assumes "b\<ge>1"
  assumes "odd a"
  assumes "odd b"
  assumes 3:"b^2 < 4*a"
  assumes "3*a < b^2+2*b+4"
  shows "\<exists>s t u v :: int. s \<ge> 0 \<and> t \<ge> 0 \<and> u \<ge> 0 \<and> v \<ge> 0 \<and> a = s^2 + t^2 + u^2 + v^2 \<and>
 b = s+t+u+v"

proof -
  from assms have 0:"\<exists>k1 :: nat. a = 2*k1+1" by (meson oddE)
  from assms have 1:"\<exists>k2 :: nat. b = 2*k2+1" by (meson oddE)
  from 0 have "4*a mod 8 = 4" by auto
  hence 2:"8 dvd (4*a-4)" by (metis dvd_minus_mod)

  obtain k2 where "b = 2*k2+1" using 1 by auto
  have "2 dvd k2*(k2+1)" by auto
  hence "8 dvd 4*k2*(k2+1)" by (metis ab_semigroup_mult_class.mult_ac(1) 
        mult_2_right nat_mult_dvd_cancel_disj numeral_Bit0)
  hence "b^2 mod 8 = 1" using 1 by (metis One_nat_def Suc_0_mod_numeral(2) assms(4)
        square_mod_8_eq_1_iff unique_euclidean_semiring_class.cong_def)
  hence "8 dvd (b^2-1)" by (metis dvd_minus_mod)
  from 2 this have "8 dvd ((4*a-4)-(b^2-1))" using dvd_diff_nat by blast
  from assms 0 1 and this have 7:"8 dvd ((4*a-b^2)-3)" by auto
  from assms 0 1 have 5:"4*a-b^2\<noteq>1" using not_one by auto
  from assms 0 1 have 6:"4*a-b^2\<noteq>2" using not_two by auto
  from 3 5 6 have "4*a-b^2 \<ge> 3" by auto
  from this 7 have 8:"(4*a-b^2) mod 8 = 3" using mod_nat_eqI by presburger

  obtain j k l where ints:"odd j \<and> odd k \<and> odd l \<and> (4*a-b^2) = j^2+k^2+l^2"
    using 8 odd_three_squares_using_mod_eight by presburger
  define x where "x = sort[j,k,l] ! 2"
  define y where "y = sort[j,k,l] ! 1"
  define z where "z = sort[j,k,l] ! 0"

  have "x^2+y^2+z^2 = sum_list (map (\<lambda>x. x^2) [j,k,l])" using x_def y_def z_def by auto
  from this ints have a_and_b:"(4*a-b^2) = x^2+y^2+z^2" by auto

  have size:"x\<ge>y \<and> y\<ge>z" using x_def y_def z_def by auto
  have x_par:"x = j \<or> x = k \<or> x = l" using x_def by auto
  have y_par:"y = j \<or> y = k \<or> y = l" using y_def by auto
  have z_par:"z = j \<or> z = k \<or> z = l" using z_def by auto
  hence parity:"odd x \<and> odd y \<and> odd z" using ints x_par y_par z_par by fastforce
  from "1" have b_par:"odd b" by auto

  obtain w::int where w_def:"(w=z \<or> w=-z) \<and> (b+x+y+w) mod 4 = 0" (*This is the \pm z in proof*)
    using suit_z size parity b_par by presburger

  from parity have fac1:"(int z) mod 4 = 3 \<or> (int z) mod 4 = 1" by presburger
  from parity have fac2:"-z mod 4 = 3 \<or> -z mod 4 = 1" by presburger
  from w_def have fac3:"w mod 4 = 3 \<or> w mod 4 = 1" using fac1 fac2 by auto

  have s_int:"4 dvd (b+x+y+w)" using b_par parity fac3 w_def by presburger
  have b_x_int:"2 dvd (b+x)" using b_par parity by presburger
  have b_y_int:"2 dvd (b+y)" using b_par parity by presburger
  have b_w_int:"2 dvd (b+w)" using b_par fac3 by presburger

  obtain s::int where s_def:"s = (b+x+y+w) div 4" using s_int by fastforce
  obtain t::int where t_def:"t = (b+x) div 2 - s" using s_int b_x_int by blast
  obtain u::int where u_def:"u = (b+y) div 2 - s" using s_int b_y_int by blast
  obtain v::int where v_def:"v = (b+w) div 2 - s" using s_int b_w_int by blast

  from t_def s_def have t_simp1:"t = (2*b+2*x) div 4 - (b+x+y+w) div 4" by auto
  have t_simp2:"(2* b+2* x) - (b+x+y+w) = b+x-y-w" using size by auto
  hence t_expre:"t = (b+x-y-w) div 4" using t_simp1 by (smt (verit, ccfv_SIG) add_num_simps(1) 
div_plus_div_distrib_dvd_right numeral_Bit0 of_nat_numeral one_plus_numeral s_int 
unique_euclidean_semiring_with_nat_class.of_nat_div)
  from b_x_int have "4 dvd (2*b+2*x)"
    by (metis distrib_left_numeral mult_2_right nat_mult_dvd_cancel_disj numeral_Bit0)
  hence four_div_tn:"4 dvd (b+x-y-w)" using s_int t_simp2 by presburger

  have " (b+x) div 2 +  (b+y) div 2 = (2*b+x+y) div 2"
    by (smt (verit, best) Groups.add_ac(2) b_y_int div_plus_div_distrib_dvd_right 
left_add_twice nat_arith.add2)
  hence threesum:"t + u + s = (2*b+x+y) div 2 - s" using t_def u_def by auto

  have "2 dvd (x+y)" using parity by auto
  hence "(2*b+x+y) div 2 + (b+w) div 2 = (2*b+b+x+y+w) div 2"
    by (smt (verit, ccfv_threshold) Num.of_nat_simps(4) b_w_int div_plus_div_distrib_dvd_right
 landau_product_preprocess(4) numerals(1) of_nat_1 one_plus_numeral
 unique_euclidean_semiring_with_nat_class.of_nat_div)

  hence "t+u+s+v = (2*b+b+x+y+w) div 2 -s -s" using v_def threesum by auto
  hence foursum0:"t+u+s+v = (2*b+b+x+y+w) div 2 - (b+x+y+w) div 4 - (b+x+y+w) div 4" 
    using s_def by auto
  have foursum1:"(b+x+y+w) div 4 + (b+x+y+w) div 4 = (b+x+y+w) div 2" 
    using div_mult_swap s_int by auto
  have "(2*b+b+x+y+w) div 2 - (b+x+y+w) div 2 = (2*b) div 2" by auto
  hence "t+u+s+v = (2*b) div 2" using foursum0 foursum1 by linarith
  hence second:"t+u+s+v = b" by auto

  from a_and_b have "4*a = x^2+y^2+z^2+b^2"
    by (metis Nat.add_diff_assoc2 add_diff_cancel_right' assms(5) less_or_eq_imp_le)
  hence "a = (x^2+y^2+z^2+b^2) div 4" using parity b_par by auto

  from second have b_expresion:"b^2 = t^2+u^2+s^2+v^2+2*t*u+2* s * v + 
2*t* s + 2*t * v +2*u * s +2*u * v" using four_terms_bin_exp_allsum
    by (metis is_num_normalize(1) nat_arith.add2 of_nat_power)

  define sn where sn_def:"sn = b+x+y+w" (*Numerator of s*)
  from sn_def s_def have sn_nume: "4* s = sn" by (metis dvd_div_mult_self mult.commute s_int)
  from sn_def have sn_sqr:"sn^2 = b^2+x^2+y^2+w^2+2* b * x+2* b * y+2*b*w+2*x*y+2*x*w+2*y*w" 
    using four_terms_bin_exp_allsum w_def by auto
  hence s_pen:"16* s^2 = b^2+x^2+y^2+w^2+2*b*x+2*b*y+2*b*w+2*x*y+2*x*w+2*y*w" using sn_nume by auto
  have "4 dvd sn" using s_int sn_def by auto
  hence "16 dvd sn^2" by auto
  hence s_sqr_expression:"s^2=(b^2+x^2+y^2+w^2+2*b*x+2*b*y+2*b*w+2*x*y+2*x*w+2*y*w) div 16" 
    using sn_sqr s_pen by auto

  define tn where tn_def:"tn = b+x-y-w" (*Numerator of t*)
  from tn_def t_expre size four_div_tn have tn_nume: "4* t = tn"
    by (metis dvd_div_mult_self mult.commute)
  from size assms have "b+x-y > 0" by auto
  hence "tn = int b + int x - int y -w" using tn_def by auto
  from this have tn_sqr:"tn^2 = b^2+x^2+y^2+w^2+2*b*x-2*b*y-2*b*w-2*x*y-2*x*w+2*y*w"
    using four_terms_bin_exp_twodiff w_def by auto
  hence t_pen:"16*t^2 = b^2+x^2+y^2+w^2+2*b*x-2*b*y-2*b*w-2*x*y-2*x*w+2*y*w" using tn_nume by auto
  have "16 dvd tn^2" using tn_def four_div_tn by auto
  hence t_sqr_expression:"t^2=(b^2+x^2+y^2+w^2+2*b*x-2*b*y-2*b*w-2*x*y-2*x*w+2*y*w) div 16"
    using tn_sqr t_pen by auto
 
  from size s_def t_expre w_def have sgeqt:"s\<ge>t" by auto
  from size s_def t_def u_def have tgequ:"t\<ge>u" by auto
  from size s_def u_def v_def w_def have ugeqv:"u\<ge>v" by auto

  from assms(6) have "12*a < 4*b^2+8*b+16" by auto
  hence "12*a-3*b^2 < b^2+8*b+16" by auto
  hence "12*a-3*b^2 < (b+4)^2" 
    by (smt (z3) add.commute add.left_commute mult_2 numeral_Bit0 power2_eq_square power2_sum)
  hence mid_ineq:"sqrt(12*a-3*b^2) < b+4" 
    by (meson of_nat_0_le_iff of_nat_power_less_of_nat_cancel_iff real_less_lsqrt)

  define ab::nat where ab_def:"ab = 4*a-b^2"
  from assms ab_def have nonneg_ab:"ab>0" by auto
  from a_and_b ab_def have sum_of_sqrs:"x^2+y^2+z^2 = ab" by auto
  from this nonneg_ab have "x^2+y^2+z^2>0" by auto
  from this sum_of_sqrs three_terms_Cauchy_Schwarz_nat_ver have "x+y+z \<le> sqrt(3*ab)" by auto
  hence left_ineq:"x+y+z \<le> sqrt(3*(4*a-b^2))" using ab_def by auto
  have "sqrt(3*(4*a-b^2)) = sqrt(12*a-3*b^2)" by (simp add: diff_mult_distrib2)
  from left_ineq mid_ineq this have "x+y+z < b+4" by auto
  hence num_bound:"int b- x- y- z > -4" by auto

  define vn where vn_def:"vn = int b+w-x-y"
  from num_bound vn_def w_def have vn_bound:"vn > -4" by auto
  from w_def have four_div_sn:"4 dvd (int b +x+y+w)" by auto
  from parity have "4 dvd (int 2*x+2*y)" 
    by (metis Num.of_nat_simps(5) \<open>even (x + y)\<close> distrib_left int_dvd_int_iff 
nat_mult_dvd_cancel_disj num_double numeral_mult of_nat_add of_nat_numeral)
  hence "4 dvd (int b +x+y+w - 2*x - 2*y)" using four_div_sn
    by (smt (verit) Num.of_nat_simps(5) dvd_add_left_iff)
  hence "4 dvd vn" using vn_def by presburger

  from v_def s_def have "v = (int 2*b + 2*w) div 4 - (int b + x + y + w) div 4" by auto
  hence v_expre:"v = (int b-x-y+w) div 4" using four_div_sn by fastforce
  hence "v = vn div 4" using vn_def by auto
  hence "v \<ge> 0" using vn_bound four_div_sn using \<open>4 dvd vn\<close> by fastforce
  hence stuv_nonneg:" s \<ge> 0 \<and> t \<ge> 0 \<and> u \<ge> 0 \<and> v \<ge> 0 " using sgeqt tgequ ugeqv by linarith

  from vn_def have vn_sqr:"vn^2 = b^2+x^2+y^2+w^2 - 2*b*x-2*b*y+2*b*w+2*x*y-2*x*w-2*y*w" 
    using four_terms_bin_exp_twodiff w_def by auto
  from \<open>v = vn div 4\<close> have vn_is_num:"v^2 = vn^2 div 16" using \<open>4 dvd vn\<close> by fastforce
  hence "16 dvd vn^2" using v_def using \<open>4 dvd vn\<close> by fastforce
  from vn_is_num vn_sqr have 
  v_sqr_expression:"v^2=(b^2+x^2+y^2+w^2-2*b*x-2*b*y+2*b*w+2*x*y-2*x*w-2*y*w) div 16" by auto
  
  define un where un_def:"un = int b+y-x-w"
  from parity w_def have "even (x+w)" by auto
  from this parity have "4 dvd (int 2*x+2*w)" 
    by (metis distrib_left even_numeral mult_2_right mult_dvd_mono numeral_Bit0 of_nat_numeral)
  hence "4 dvd (int b +x+y+w - 2*x-2*w)" using four_div_sn
    by (smt (verit) Num.of_nat_simps(5) dvd_add_left_iff)
  hence "4 dvd un" using un_def by presburger

  from u_def s_def have "u = (int 2*b+2*y) div 4 - (int b + x + y + w) div 4" by auto
  hence u_expre:"u = (int b-x+y-w) div 4" using four_div_sn by fastforce
  hence "u = un div 4" using un_def by auto
  from un_def have un_sqr:"un^2 = b^2+x^2+y^2+w^2+2*b*y-2*b*x-2*b*w-2*y*x-2*y*w+2*x*w"
    using four_terms_bin_exp_twodiff w_def by auto
  from \<open>u = un div 4\<close> have un_is_num:"u^2 = un^2 div 16" using \<open>4 dvd un\<close> by fastforce
  hence "16 dvd un^2" using u_def using \<open>4 dvd un\<close> by fastforce
  from un_is_num un_sqr have
  u_sqr_expression:"u^2 = (b^2+x^2+y^2+w^2+2*b*y-2*b*x-2*b*w-2*y*x-2*y*w+2*x*w) div 16" by auto
  
  from u_sqr_expression v_sqr_expression have
  uv_simp1:"u^2+v^2 = (int b^2+x^2+y^2+w^2-2*b*x-2*b*y+2*b*w+2*x*y-2*x*w-2*y*w) div 16 + 
  (int b^2+x^2+y^2+w^2+2*b*y-2*b*x-2*b*w-2*y*x-2*y*w+2*x*w) div 16" by auto
  have uv_simp2:"(int b^2+x^2+y^2+w^2-2*b*x-2*b*y+2*b*w+2*x*y-2*x*w-2*y*w)+
  (int b^2+x^2+y^2+w^2+2*b*y-2*b*x-2*b*w-2*y*x-2*y*w+2*x*w)=
  (int 2*b^2+2*x^2+2*y^2+2*w^2-4*b*x-4*y*w)" by auto
  hence "16 dvd (int 2*b^2+2*x^2+2*y^2+2*w^2-4*b*x-4*y*w)" by (smt (verit) \<open>16 dvd un\<^sup>2\<close> \<open>16 dvd vn\<^sup>2\<close>
 dvd_add_right_iff of_nat_power un_sqr vn_sqr zadd_int_left)
  hence usqr_plus_vsqr:"u^2+v^2 = (int 2*b^2+2*x^2+2*y^2+2*w^2-4*b*x-4*y*w) div 16" 
    using uv_simp1 uv_simp2 by (smt (verit, ccfv_threshold) Num.of_nat_simps(4) Num.of_nat_simps(5)
 \<open>16 dvd vn\<^sup>2\<close> div_plus_div_distrib_dvd_right power2_eq_square vn_sqr)

  have allsum0:"s^2+t^2+u^2+v^2 = (sn^2+tn^2+un^2+vn^2) div 16" using \<open>16 dvd vn\<^sup>2\<close> \<open>16 dvd sn\<^sup>2\<close> 
\<open>16 dvd un\<^sup>2\<close> \<open>16 dvd tn\<^sup>2\<close> s_sqr_expression t_sqr_expression u_sqr_expression v_sqr_expression
sn_sqr tn_sqr un_sqr vn_sqr by (metis add.commute div_plus_div_distrib_dvd_left)
  have allsum1:"(sn^2+tn^2+un^2+vn^2) = (int 4*b^2+4*x^2+4*y^2+4*w^2)" 
    using sn_sqr tn_sqr un_sqr vn_sqr by auto
  have "16 dvd (sn^2+tn^2+un^2+vn^2)" 
    by (simp add: \<open>16 dvd sn\<^sup>2\<close> \<open>16 dvd tn\<^sup>2\<close> \<open>16 dvd un\<^sup>2\<close> \<open>16 dvd vn\<^sup>2\<close>) 
  hence "16 dvd 4*(int b^2+x^2+y^2+w^2)" using allsum1 by auto
  hence "4 dvd (int b^2+x^2+y^2+w^2)" by presburger
  from allsum1 have "s^2+t^2+u^2+v^2 = (int 4*b^2+4*x^2+4*y^2+4*w^2) div 16" 
    using allsum0 by presburger
  hence "s^2+t^2+u^2+v^2 = 4*(int b^2+x^2+y^2+w^2) div 16" by simp
  hence allsum2:"s^2+t^2+u^2+v^2 = (int b^2+x^2+y^2+w^2) div 4" by simp

  from a_and_b have "4*a = int b^2+x^2+y^2+w^2" using w_def
    using \<open>4 * a = x\<^sup>2 + y\<^sup>2 + z\<^sup>2 + b\<^sup>2\<close> by fastforce
  hence first:"a = s^2+t^2+u^2+v^2" using allsum2 by linarith

  show ?thesis using first second stuv_nonneg by (smt (verit, best))
qed
end