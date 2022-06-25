section \<open>Simplied Version of Gordeev's Proof for Monotone Circuits\<close>

subsection \<open>Setup of Global Assumptions and Proofs of Approximations\<close>

theory Assumptions_and_Approximations
imports 
  "HOL-Real_Asymp.Real_Asymp"
  Stirling_Formula.Stirling_Formula
  Preliminaries
begin

locale first_assumptions =
  fixes l p k :: nat
  assumes l2: "l > 2" 
  and pl: "p > l" 
  and kp: "k > p" 
begin

lemma k2: "k > 2" using pl l2 kp by auto
lemma p: "p > 2" using pl l2 kp by auto
lemma k: "k > l" using pl l2 kp by auto

definition "m = k^4"

lemma km: "k < m"
  using power_strict_increasing_iff[of k 1 4] k2 unfolding m_def by auto

lemma lm: "l + 1 < m" using km k by simp

lemma m2: "m > 2" using k2 km by auto  

lemma mp: "m > p" using km k kp by simp

definition "L = fact l * (p - 1) ^ l"

lemma kml: "k \<le> m - l" 
proof -
  have "k \<le> k * k - k" using k2 by (cases k, auto)
  also have "\<dots> \<le> (k * k) * 1 - l" using k by simp
  also have "\<dots> \<le> (k * k) * (k * k) - l"
    by (intro diff_le_mono mult_left_mono, insert k2, auto)
  also have "(k * k) * (k * k) = m" unfolding m_def by algebra
  finally show ?thesis .
qed
end

locale second_assumptions = first_assumptions +
  assumes kl2: "k = l^2" 
  and l8: "l \<ge> 8" 
begin

lemma Lm: "L \<ge> m" 
proof -
  have "m \<le> l ^ l" 
    unfolding L_def m_def
    unfolding kl2 power_mult[symmetric]
    by (intro power_increasing, insert l8, auto)
  also have "\<dots> \<le> (p - 1) ^ l" 
    by (rule power_mono, insert pl, auto)
  also have "\<dots> \<le> fact l * (p - 1) ^ l" by simp
  also have "\<dots> \<le> L" unfolding L_def by simp
  finally show ?thesis .
qed

lemma Lp: "L > p" using Lm mp by auto

lemma L3: "L > 3" using p Lp by auto
end

definition "eps = 1/(1000 :: real)" 
lemma eps: "eps > 0" unfolding eps_def by simp

definition L0 :: nat where 
  "L0 = (SOME l0. \<forall>l\<ge>l0. 1 / 3 < (1 + - 1 / real l) ^ l)" 

definition M0 :: nat where 
  "M0 = (SOME y. \<forall> x. x \<ge> y \<longrightarrow> (root 8 (real x) * log 2 (real x) + 1) / real x powr (1 / 8 + eps) \<le> 1)" 

definition L0' :: nat where
  "L0' = (SOME l0. \<forall> n \<ge> l0. 6 * (real n)^16 * fact n < real (n\<^sup>2 ^ 4) powr (1 / 8 * real (n\<^sup>2 ^ 4) powr (1 / 8)))" 

definition L0'' :: nat where "L0'' = (SOME l0. \<forall> l \<ge> l0. real l * log 2 (real (l\<^sup>2 ^ 4)) + 1 < real (l\<^sup>2))" 

lemma L0'': assumes "l \<ge> L0''" shows "real l * log 2 (real (l\<^sup>2 ^ 4)) + 1 < real (l\<^sup>2)"
proof -
  have "(\<lambda> l :: nat. (real l * log 2 (real (l\<^sup>2 ^ 4)) + 1) / real (l\<^sup>2)) \<longlonglongrightarrow> 0" by real_asymp
  from LIMSEQ_D[OF this, of 1] obtain l0
    where "\<forall>l\<ge>l0. \<bar>1 + real l * log 2 (real l ^ 8)\<bar> / (real l)\<^sup>2 < 1" by (auto simp: field_simps)
  hence "\<forall> l \<ge> max 1 l0. real l * log 2 (real (l\<^sup>2 ^ 4)) + 1 < real (l\<^sup>2)" 
    by (auto simp: field_simps)
  hence "\<exists> l0. \<forall> l \<ge> l0. real l * log 2 (real (l\<^sup>2 ^ 4)) + 1 < real (l\<^sup>2)" by blast
  from someI_ex[OF this, folded L0''_def, rule_format, OF assms]  
  show ?thesis .
qed

definition M0' :: nat where
  "M0' = (SOME x0. \<forall> x \<ge> x0. real x powr (2 / 3) \<le> x powr (3 / 4) - 1)" 

locale third_assumptions = second_assumptions + 
  assumes pllog: "l * log 2 m \<le> p" "real p \<le> l * log 2 m + 1" 
    and L0: "l \<ge> L0" 
    and L0': "l \<ge> L0'" 
    and M0': "m \<ge> M0'" 
    and M0: "m \<ge> M0" 
begin

lemma approximation1: 
  "(real (k - 1)) ^ (m - l) * prod (\<lambda> i. real (k - 1 - i)) {0..<l}
   > (real (k - 1)) ^ m / 3" 
proof -
have "real (k - 1) ^ (m - l) * (\<Prod>i = 0..<l. real (k - 1 - i)) =
    real (k - 1) ^ m *
    (inverse (real (k - 1)) ^ l * (\<Prod>i = 0..<l. real (k - 1 - i)))"
    by (subst power_diff_conv_inverse, insert k2 lm, auto)
  also have "\<dots> > (real (k - 1)) ^ m * (1/3)" 
  proof (rule mult_strict_left_mono)
    define f where "f l = (1  + (-1) / real l) ^ l" for l 
    define e1 :: real where "e1 = exp (- 1)" 
    define lim :: real where "lim = 1 / 3" 
    from tendsto_exp_limit_sequentially[of "-1", folded f_def]
    have f: "f \<longlonglongrightarrow> e1" by (simp add: e1_def)
    have "lim < (1 - 1 / real 6) ^ 6" unfolding lim_def by code_simp
    also have " \<dots> \<le> exp (- 1)" 
      by (rule exp_ge_one_minus_x_over_n_power_n, auto)
    finally have "lim < e1" unfolding e1_def by auto
    with f have "\<exists> l0. \<forall> l. l \<ge> l0 \<longrightarrow> f l > lim"
      by (metis eventually_sequentially order_tendstoD(1))
    from someI_ex[OF this[unfolded f_def lim_def], folded L0_def] L0
    have fl: "f l > 1/3" unfolding f_def by auto
    define start where "start = inverse (real (k - 1)) ^ l * (\<Prod>i = 0..<l. real (k - 1 - i))" 
    have "uminus start
      = uminus (prod (\<lambda> _. inverse (real (k - 1))) {0..<l} * prod (\<lambda> i. real (k - 1 - i)) {0 ..< l})" 
      by (simp add: start_def)
    also have "\<dots> = uminus (prod (\<lambda> i. inverse (real (k - 1)) * real (k - 1 - i)) {0..<l})" 
      by (subst prod.distrib, simp)
    also have "\<dots> \<le> uminus (prod (\<lambda> i. inverse (real (k - 1)) * real (k - 1 - (l - 1))) {0..<l})" 
      unfolding neg_le_iff_le
      by (intro prod_mono conjI mult_left_mono, insert k2 l2, auto intro!: diff_le_mono2)
    also have "\<dots> = uminus ((inverse (real (k - 1)) * real (k - l)) ^ l)" by simp
    also have "inverse (real (k - 1)) * real (k - l) = inverse (real (k - 1)) * ((real (k - 1)) - (real l - 1))" 
      using l2 k2 k by simp
    also have "\<dots> = 1 - (real l - 1) / (real (k - 1))" using l2 k2 k 
      by (simp add: field_simps)
    also have "real (k - 1) = real k - 1" using k2 by simp
    also have "\<dots> = (real l - 1) * (real l + 1)" unfolding kl2 of_nat_power
      by (simp add: field_simps power2_eq_square)
    also have "(real l - 1) / \<dots> = inverse (real l + 1)" 
      using l2 by (smt (verit, best) divide_divide_eq_left' divide_inverse nat_1_add_1 nat_less_real_le nonzero_mult_div_cancel_left of_nat_1 of_nat_add)     
    also have "- ((1 - inverse (real l + 1)) ^ l) \<le> - ((1 - inverse (real l)) ^ l)" 
      unfolding neg_le_iff_le 
      by (intro power_mono, insert l2, auto simp: field_simps)
    also have "\<dots> < - (1/3)" using fl unfolding f_def by (auto simp: field_simps)
    finally have start: "start > 1 / 3" by simp
    thus "inverse (real (k - 1)) ^ l * (\<Prod>i = 0..<l. real (k - 1 - i)) > 1/3" 
      unfolding start_def by simp
  qed (insert k2, auto)
  finally show ?thesis by simp
qed

lemma approximation2: fixes s :: nat
  assumes "m choose k \<le> s * L\<^sup>2 * (m - l - 1 choose (k - l - 1))" 
  shows "((m - l) / k)^l / (6 * L^2) < s" 
proof -
  let ?r = real
  define q where "q = (?r (L\<^sup>2) * ?r (m - l - 1 choose (k - l - 1)))" 
  have q: "q > 0" unfolding q_def
    by (insert L3 km, auto)
  have "?r (m choose k) \<le> ?r (s * L\<^sup>2 * (m - l - 1 choose (k - l - 1)))" 
    unfolding of_nat_le_iff using assms by simp
  hence "m choose k \<le> s * q" unfolding q_def by simp
  hence *: "s \<ge> (m choose k) / q" using q by (metis mult_imp_div_pos_le)
  have "(((m - l) / k)^l / (L^2)) / 6 < ((m - l) / k)^l / (L^2) / 1" 
    by (rule divide_strict_left_mono, insert m2 L3 lm k, auto intro!: mult_pos_pos divide_pos_pos zero_less_power)
  also have "\<dots> =  ((m - l) / k)^l / (L^2)" by simp
  also have "\<dots> \<le> ((m choose k) / (m - l - 1 choose (k - l - 1))) / (L^2)" 
  proof (rule divide_right_mono)
    define b where "b = ?r (m - l - 1 choose (k - l - 1))" 
    define c where "c = (?r k)^l" 
    have b0: "b > 0" unfolding b_def using km l2 by simp
    have c0: "c > 0" unfolding c_def using k by auto
    define aim where "aim = (((m - l) / k)^l \<le> (m choose k) / (m - l - 1 choose (k - l - 1)))" 
    have "aim \<longleftrightarrow> ((m - l) / k)^l \<le> (m choose k) / b" unfolding b_def aim_def by simp
    also have "\<dots> \<longleftrightarrow> b * ((m - l) / k)^l \<le> (m choose k)" using b0
      by (simp add: mult.commute pos_le_divide_eq)
    also have "\<dots> \<longleftrightarrow> b * (m - l)^l / c \<le> (m choose k)" 
      by (simp add: power_divide c_def)
    also have "\<dots> \<longleftrightarrow> b * (m - l)^l \<le> (m choose k) * c" using c0 b0
      by (auto simp add: mult.commute pos_divide_le_eq)
    also have "(m choose k) = fact m / (fact k * fact (m - k))" 
      by (rule binomial_fact, insert km, auto)
    also have "b = fact (m - l - 1) / (fact (k - l - 1) * fact (m - l - 1 - (k - l - 1)))" unfolding b_def
      by (rule binomial_fact, insert k km, auto)
    finally have "aim \<longleftrightarrow>
          fact (m - l - 1) / fact (k - l - 1) * (m - l) ^ l / fact (m - l - 1 - (k - l - 1))
       \<le> (fact m / fact k) * (?r k)^l / fact (m - k)" unfolding c_def by simp 
    also have "m - l - 1 - (k - l - 1) = m - k" using l2 k km by simp
    finally have "aim \<longleftrightarrow>
          fact (m - l - 1) / fact (k - l - 1) * ?r (m - l) ^ l 
        \<le> fact m / fact k * ?r k ^ l" unfolding divide_le_cancel using km by simp
    also have "\<dots> \<longleftrightarrow> (fact (m - (l + 1)) * ?r (m - l) ^ l)  * fact k            
                     \<le> (fact m / k) * (fact (k - (l + 1)) * (?r k * ?r k ^ l))"
      using k2
      by (simp add: field_simps)
    also have "\<dots>" 
    proof (intro mult_mono)
      have "fact k \<le> fact (k - (l + 1)) * (?r k ^ (l + 1))"
        by (rule fact_approx_minus, insert k, auto)
      also have "\<dots> = (fact (k - (l + 1)) * ?r k ^ l)  * ?r k" by simp
      finally show "fact k \<le> fact (k - (l + 1)) * (?r k * ?r k ^ l)" by (simp add: field_simps)
      have "fact (m - (l + 1)) * real (m - l) ^ l \<le> fact m / k \<longleftrightarrow>
        (fact (m - (l + 1)) * ?r k) * real (m - l) ^ l \<le> fact m" using k2 by (simp add: field_simps)
      also have "\<dots>" 
      proof -
        have "(fact (m - (l + 1)) * ?r k) * ?r (m - l) ^ l \<le>
              (fact (m - (l + 1)) * ?r (m - l)) * ?r (m - l) ^ l" 
          by (intro mult_mono, insert kml, auto)
        also have "((fact (m - (l + 1)) * ?r (m - l)) * ?r (m - l) ^ l) = 
              (fact (m - (l + 1)) * ?r (m - l) ^ (l + 1))" by simp
        also have "\<dots> \<le> fact m" 
          by (rule fact_approx_upper_minus, insert km k, auto)
        finally show "fact (m - (l + 1)) * real k * real (m - l) ^ l \<le> fact m" .
      qed
      finally show "fact (m - (l + 1)) * real (m - l) ^ l \<le> fact m / k"  .
    qed auto
    finally show "((m - l) / k)^l \<le> (m choose k) / (m - l - 1 choose (k - l - 1))" 
      unfolding aim_def .
  qed simp
  also have "\<dots> = (m choose k) / q" 
    unfolding q_def by simp
  also have "\<dots> \<le> s" using q * by metis
  finally show "((m - l) / k)^l / (6 * L^2) < s" by simp
qed

lemma approximation3: fixes s :: nat
  assumes "(k - 1)^m / 3 < (s * (L\<^sup>2 * (k - 1) ^ m)) / 2 ^ (p - 1)" 
  shows "((m - l) / k)^l / (6 * L^2) < s" 
proof -
  define A where "A = real (L\<^sup>2 * (k - 1) ^ m)" 
  have A0: "A > 0" unfolding A_def using L3 k2 m2 by simp
  from mult_strict_left_mono[OF assms, of "2 ^ (p - 1)"]
  have "2^(p - 1) * (k - 1)^m / 3 < s * A" 
    by (simp add: A_def)
  from divide_strict_right_mono[OF this, of A] A0
  have "2^(p - 1) * (k - 1)^m / 3 / A < s"
    by simp
  also have "2^(p - 1) * (k - 1)^m / 3 / A = 2^(p - 1) / (3 * L^2)"
    unfolding A_def using k2 by simp
  also have "\<dots> = 2^p / (6 * L^2)" using p by (cases p, auto)
  also have "2^p = 2 powr p" 
    by (simp add: powr_realpow)
  finally have *: "2 powr p / (6 * L\<^sup>2) < s" .
  have "m ^ l = m powr l" using m2 l2 powr_realpow by auto
  also have "\<dots> = 2 powr (log 2 m * l)" 
    unfolding powr_powr[symmetric] 
    by (subst powr_log_cancel, insert m2, auto)
  also have "\<dots> = 2 powr (l * log 2 m)" by (simp add: ac_simps)
  also have "\<dots> \<le> 2 powr p" 
    by (rule powr_mono, insert pllog, auto)
  finally have "m ^ l \<le> 2 powr p" .
  from divide_right_mono[OF this, of "6 * L\<^sup>2"] *
  have "m ^ l / (6 * L\<^sup>2) < s" by simp
  moreover have "((m - l) / k)^l / (6 * L^2) \<le> m^l / (6 * L^2)" 
  proof (rule divide_right_mono, unfold of_nat_power, rule power_mono)
    have "real (m - l) / real k \<le> real (m - l) / 1" 
      using k2 lm by (intro divide_left_mono, auto)
    also have "\<dots> \<le> m" by simp
    finally show "(m - l) / k \<le> m" by simp
  qed auto
  ultimately show ?thesis by simp
qed

lemma identities: "k = root 4 m" "l = root 8 m" 
proof -
  let ?r = real
  have "?r k ^ 4 = ?r m" unfolding m_def by simp
  from arg_cong[OF this, of "root 4"] 
  show km_id: "k = root 4 m" by (simp add: real_root_pos2)
  have "?r l ^ 8 = ?r m" unfolding m_def using kl2 by simp
  from arg_cong[OF this, of "root 8"] 
  show lm_id: "l = root 8 m" by (simp add: real_root_pos2)
qed

lemma identities2: "root 4 m = m powr (1/4)" "root 8 m = m powr (1/8)" 
  by (subst root_powr_inverse, insert m2, auto)+

  
lemma appendix_A_1: assumes "x \<ge> M0'" shows "x powr (2/3) \<le> x powr (3/4) - 1" 
proof -
  have "(\<lambda> x. x powr (2/3) / (x powr (3/4) - 1)) \<longlonglongrightarrow> 0" 
    by real_asymp
  from LIMSEQ_D[OF this, of 1, simplified] obtain x0 :: nat where 
    sub: "x \<ge> x0 \<Longrightarrow> x powr (2 / 3) / \<bar>x powr (3/4) - 1\<bar> < 1" for x 
    by (auto simp: field_simps)
  have "(\<lambda> x :: real. 2 / (x powr (3/4))) \<longlonglongrightarrow> 0"  
    by real_asymp
  from LIMSEQ_D[OF this, of 1, simplified] obtain x1 :: nat where
    sub2: "x \<ge> x1 \<Longrightarrow> 2 / x powr (3 / 4) < 1" for x by auto
  {
    fix x
    assume x: "x \<ge> x0" "x \<ge> x1" "x \<ge> 1"  
    define a where "a = x powr (3/4) - 1" 
    from sub[OF x(1)] have small: "x powr (2 / 3) / \<bar>a\<bar> \<le> 1" 
      by (simp add: a_def)
    have 2: "2 \<le> x powr (3/4)" using sub2[OF x(2)] x(3) by simp
    hence a: "a > 0" by (simp add: a_def)
    from mult_left_mono[OF small, of a] a
    have "x powr (2 / 3) \<le> a"
      by (simp add: field_simps)
    hence "x powr (2 / 3) \<le> x powr (3 / 4) - 1" unfolding a_def by simp
  }
  hence "\<exists> x0 :: nat. \<forall> x \<ge> x0. x powr (2 / 3) \<le> x powr (3 / 4) - 1" 
    by (intro exI[of _ "max x0 (max x1 1)"], auto)
  from someI_ex[OF this, folded M0'_def, rule_format, OF assms]
  show ?thesis .
qed


lemma appendix_A_2: "(p - 1)^l < m powr ((1 / 8 + eps) * l)" 
proof -
  define f where "f (x :: nat) = (root 8 x * log 2 x + 1) / (x powr (1/8 + eps))" for x
  have "f \<longlonglongrightarrow> 0" using eps unfolding f_def by real_asymp
  from LIMSEQ_D[OF this, of 1]
  have ex: "\<exists> x. \<forall> y. y  \<ge> x \<longrightarrow> f y \<le> 1" by fastforce
  have lim: "root 8 m * log 2 m + 1 \<le> m powr (1 / 8 + eps)" 
    using someI_ex[OF ex[unfolded f_def], folded M0_def, rule_format, OF M0] m2
    by (simp add: field_simps)
  define start where "start = real (p - 1)^l" 
  have "(p - 1)^l < p ^ l" 
    by (rule power_strict_mono, insert p l2, auto)
  hence "start < real (p ^ l)"
    using start_def of_nat_less_of_nat_power_cancel_iff by blast
  also have "\<dots> = p powr l" 
    by (subst powr_realpow, insert p, auto)
  also have "\<dots> \<le> (l * log 2 m + 1) powr l" 
    by (rule powr_mono2, insert pllog, auto)
  also have "l = root 8 m" unfolding identities by simp
  finally have "start < (root 8 m * log 2 m + 1) powr root 8 m" 
    by (simp add: identities2)
  also have "\<dots> \<le> (m powr (1 / 8 + eps)) powr root 8 m" 
    by (rule powr_mono2[OF _ _ lim], insert m2, auto)
  also have "\<dots> = m powr ((1 / 8 + eps) * l)" unfolding powr_powr identities ..
  finally show ?thesis unfolding start_def by simp
qed

lemma appendix_A_3: "6 * real l^16 * fact l < m powr (1 / 8 * l)"
proof -
  define f where "f = (\<lambda>n. 6 * (real n)^16 * (sqrt (2 * pi * real n) * (real n / exp 1) ^ n))" 
  define g where "g = (\<lambda> n. 6 * (real n)^16 * (sqrt (2 * 4 * real n) * (real n / 2) ^ n))"
  define h where "h = (\<lambda> n. ((real (n\<^sup>2 ^ 4) powr (1 / 8 * (real (n\<^sup>2 ^ 4)) powr (1/8)))))" 
  have e: "2 \<le> (exp 1 :: real)" using exp_ge_add_one_self[of 1] by simp
  from fact_asymp_equiv
  have 1: "(\<lambda> n. 6 * (real n)^16 * fact n / h n) \<sim>[sequentially] (\<lambda> n. f n / h n)" unfolding f_def
    by (intro asymp_equiv_intros)
  have 2: "f n \<le> g n" for n unfolding f_def g_def 
    by (intro mult_mono power_mono divide_left_mono real_sqrt_le_mono, insert pi_less_4 e, auto) 
  have 2: "abs (f n / h n) \<le> abs (g n / h n)" for n
    unfolding abs_le_square_iff power2_eq_square
    by (intro mult_mono divide_right_mono 2, auto simp: h_def f_def g_def)
  have 2: "abs (g n / h n) < e \<Longrightarrow> abs (f n / h n) < e" for n e using 2[of n] by simp
  have "(\<lambda>n. g n / h n) \<longlonglongrightarrow> 0"
    unfolding g_def h_def by real_asymp
  from LIMSEQ_D[OF this] 2
  have "(\<lambda>n. f n / h n) \<longlonglongrightarrow> 0" 
    by (intro LIMSEQ_I, fastforce)
  with 1 have "(\<lambda>n. 6 * (real n)^16 * fact n / h n) \<longlonglongrightarrow> 0"
    using tendsto_asymp_equiv_cong by blast
  from LIMSEQ_D[OF this, of 1] obtain n0 where 3: "n \<ge> n0 \<Longrightarrow> norm (6 * (real n)^16 * fact n / h n) < 1" for n by auto
  {
    fix n
    assume n: "n \<ge> max 1 n0" 
    hence hn: "h n > 0" unfolding h_def by auto
    from n have "n \<ge> n0" by simp
    from 3[OF this] have "6 * n ^ 16 * fact n / abs (h n) < 1" by auto
    with hn have "6 * (real n) ^ 16 * fact n < h n" by simp
  }
  hence "\<exists> n0. \<forall> n. n \<ge> n0 \<longrightarrow> 6 * n ^ 16 * fact n < h n" by blast
  from someI_ex[OF this[unfolded h_def], folded L0'_def, rule_format, OF L0']
  have "6 * real l^16 * fact l < real (l\<^sup>2 ^ 4) powr (1 / 8 * real (l\<^sup>2 ^ 4) powr (1 / 8))" by simp
  also have "\<dots> = m powr (1 / 8 * l)" using identities identities2 kl2
    by (metis m_def) 
  finally show ?thesis .
qed

lemma appendix_A_4: "12 * L^2 \<le> m powr (m powr (1 / 8) * 0.51)" 
proof -
  let ?r = real
  define Lappr where "Lappr = m * m * fact l * p ^ l / 2" 
  have "L = (fact l * (p - 1) ^ l)" unfolding L_def by simp
  hence "?r L \<le> (fact l * (p - 1) ^ l)" by linarith
  also have "\<dots> = (1 * ?r (fact l)) * (?r (p - 1) ^ l)" by simp 
  also have "\<dots> \<le> ((m * m / 2) * ?r (fact l)) * (?r (p - 1) ^ l)" 
    by (intro mult_right_mono, insert m2, cases m; cases "m - 1", auto)
  also have "\<dots> = (6 * real (m * m) * fact l) * (?r (p - 1) ^ l) / 12" by simp
  also have "real (m * m) = real l^16" unfolding m_def unfolding kl2 by simp
  also have "(6 * real l^16 * fact l) * (?r (p - 1) ^ l) / 12
    \<le> (m powr (1 / 8 * l) * (m powr ((1 / 8 + eps) * l))) / 12" 
    by (intro divide_right_mono mult_mono, insert appendix_A_2 appendix_A_3, auto)   
  also have "\<dots> = (m powr (1 / 8 * l + (1 / 8 + eps) * l)) / 12" 
    by (simp add: powr_add)
  also have "1 / 8 * l + (1 / 8 + eps) * l = l * (1/4 + eps)" by (simp add: field_simps)
  also have "l = m powr (1/8)" unfolding identities identities2 ..
  finally have LL: "?r L \<le> m powr (m powr (1 / 8) * (1 / 4 + eps)) / 12" .
  from power_mono[OF this, of 2]
  have "L^2 \<le> (m powr (m powr (1 / 8) * (1 / 4 + eps)) / 12)^2" 
    by simp
  also have "\<dots> = (m powr (m powr (1 / 8) * (1 / 4 + eps)))^2 / 144" 
    by (simp add: power2_eq_square)
  also have "\<dots> = (m powr (m powr (1 / 8) * (1 / 4 + eps) * 2)) / 144" 
    by (subst powr_realpow[symmetric], (use m2 in force), unfold powr_powr, simp)
  also have "\<dots> = (m powr (m powr (1 / 8) * (1 / 2 + 2 * eps))) / 144" 
    by (simp add: algebra_simps)
  also have "\<dots> \<le> (m powr (m powr (1 / 8) * 0.51)) / 144" 
    by (intro divide_right_mono powr_mono mult_left_mono, insert m2, auto simp: eps_def)
  finally have "L^2 \<le> m powr (m powr (1 / 8) * 0.51) / 144" by simp
  from mult_left_mono[OF this, of 12]
  have "12 * L^2 \<le> 12 * m powr (m powr (1 / 8) * 0.51) / 144" by simp
  also have "\<dots> = m powr (m powr (1 / 8) * 0.51) / 12" by simp
  also have "\<dots> \<le> m powr (m powr (1 / 8) * 0.51) / 1" 
    by (rule divide_left_mono, auto)
  finally show ?thesis by simp
qed

lemma approximation4: fixes s :: nat
  assumes "s > ((m - l) / k)^l / (6 * L^2)" 
  shows "s > 2 * k powr (4 / 7 * sqrt k)" 
proof -
  let ?r = real
  have diff: "?r (m - l) = ?r m - ?r l" using lm by simp
  have "m powr (2/3) \<le> m powr (3/4) - 1" using appendix_A_1[OF M0'] by auto
  also have "\<dots> \<le> (m - m powr (1/8)) / m powr (1/4)"
    unfolding diff_divide_distrib
    by (rule diff_mono, insert m2, auto simp: divide_powr_uminus powr_mult_base powr_add[symmetric],
      auto simp: powr_minus_divide intro!: ge_one_powr_ge_zero)
  also have "\<dots> = (m - root 8 m) / root 4 m" using m2
    by (simp add: root_powr_inverse)
  also have "\<dots> = (m - l) / k" unfolding identities diff by simp
  finally have "m powr (2/3) \<le> (m - l) / k" by simp
  from power_mono[OF this, of l]
  have ineq1: "(m powr (2 / 3)) ^ l \<le> ((m - l) / k) ^ l"  using m2 by auto
  have "(m powr (l / 7)) \<le> (m powr (2 / 3 * l - l * 0.51))" 
    by (intro powr_mono, insert m2, auto)
  also have "\<dots> = (m powr (2 / 3)) powr l / (m powr (m powr (1 / 8) * 0.51))" 
    unfolding powr_diff powr_powr identities identities2 by simp
  also have "\<dots> = (m powr (2 / 3)) ^ l / (m powr (m powr (1 / 8) * 0.51))" 
    by (subst powr_realpow, insert m2, auto)
  also have "\<dots> \<le> (m powr (2 / 3)) ^ l / (12 * L\<^sup>2)" 
    by (rule divide_left_mono[OF appendix_A_4], insert L3 m2, auto intro!: mult_pos_pos)
  also have "\<dots> = (m powr (2 / 3)) ^ l / (?r 12 * L\<^sup>2)" by simp
  also have "\<dots> \<le> ((m - l) / k) ^ l / (?r 12 * L\<^sup>2)" 
    by (rule divide_right_mono[OF ineq1], insert L3, auto)
  also have "\<dots> < s / 2" using assms by simp
  finally have "2 * m powr (real l / 7) < s" by simp
  also have "m powr (real l / 7) = m powr (root 8 m / 7)" 
    unfolding identities by simp
  finally have "s > 2 * m powr (root 8 m / 7)" by simp
  also have "root 8 m = root 2 k" using m2 
    by (metis identities(2) kl2 of_nat_0_le_iff of_nat_power pos2 real_root_power_cancel)
  also have "?r m = k powr 4" unfolding m_def by simp
  also have "(k powr 4) powr ((root 2 k) / 7)
     = k powr (4 * (root 2 k) / 7)" unfolding powr_powr by simp
  also have "\<dots> = k powr (4 / 7 * sqrt k)" unfolding sqrt_def by simp
  finally show "s > 2 * k powr (4 / 7 * sqrt k)" .
qed

end

end