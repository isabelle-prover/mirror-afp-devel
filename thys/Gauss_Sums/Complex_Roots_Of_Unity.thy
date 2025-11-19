(*
  File:     Complex_Roots_Of_Unity.thy
  Authors:  Rodrigo Raya, EPFL; Manuel Eberl, TUM

  Complex roots of unity (exp(2i\<pi>/n)) and sums over them.
*)
theory Complex_Roots_Of_Unity
imports
  "HOL-Analysis.Analysis"
  Periodic_Arithmetic
begin

section \<open>Complex roots of unity\<close>

definition 
  "unity_root k n = cis (2 * pi * of_int n / of_nat k)"

lemma 
  unity_root_k_0 [simp]: "unity_root k 0 = 1" and
  unity_root_0_n [simp]: "unity_root 0 n = 1"
  unfolding unity_root_def by simp+

lemma unity_root_conv_exp: 
  "unity_root k n = exp (of_real (2*pi*n/k) * \<i>)"
  unfolding unity_root_def 
  by (subst cis_conv_exp,subst mult.commute,blast)

lemma unity_root_mod: 
  "unity_root k (n mod int k) = unity_root k n"
proof (cases "k = 0")
  case True then show ?thesis by simp
next
  case False
  obtain q :: int where q_def: "n = q*k + (n mod k)" 
    using div_mult_mod_eq[symmetric] by blast
  have "n / k = q + (n mod k) / k"
  proof (auto simp add: divide_simps False)
    have "real_of_int n = real_of_int (q*k + (n mod k))"
      using q_def by simp
    also have "\<dots> = real_of_int q * real k + real_of_int (n mod k)"
      using of_int_add of_int_mult by simp
    finally show "real_of_int n = real_of_int q * real k + real_of_int (n mod k)" 
      by blast
  qed
  then have "(2*pi*n/k) = 2*pi*q + (2*pi*(n mod k)/k)"
    using False by (auto simp add: field_simps)
  then have "(2*pi*n/k)*\<i> = 2*pi*q*\<i> + (2*pi*(n mod k)/k)*\<i>" (is "?l = ?r1 + ?r2")
    by (auto simp add: algebra_simps)
  then have "exp ?l = exp ?r2"
    using exp_plus_2pin by (simp add: exp_add mult.commute)
  then show ?thesis 
    using unity_root_def unity_root_conv_exp by simp
qed

lemma unity_root_cong:
  assumes "[m = n] (mod int k)"
  shows   "unity_root k m = unity_root k n"
proof -
  from assms have "m mod int k = n mod int k"
    by (auto simp: cong_def)
  hence "unity_root k (m mod int k) = unity_root k (n mod int k)"
    by simp
  thus ?thesis by (simp add: unity_root_mod)
qed

lemma unity_root_mod_nat: 
  "unity_root k (nat (n mod int k)) = unity_root k n"
proof (cases k)
  case (Suc l)
  then have "n mod int k \<ge> 0" by auto
  show ?thesis 
    unfolding int_nat_eq 
    by (simp add: \<open>n mod int k \<ge> 0\<close> unity_root_mod)
qed auto

lemma unity_root_eqD:
 assumes gr: "k > 0"
 assumes eq: "unity_root k i = unity_root k j"
 shows "i mod k = j mod k"
proof - 
  let ?arg1 = "(2*pi*i/k)* \<i>"
  let ?arg2 = "(2*pi*j/k)* \<i>"
  from eq unity_root_conv_exp have "exp ?arg1 = exp ?arg2" by simp
  from this exp_eq 
  obtain n :: int where "?arg1 = ?arg2 +(2*n*pi)*\<i>" by blast
  then have e1: "?arg1 - ?arg2 = 2*n*pi*\<i>" by simp
  have e2: "?arg1 - ?arg2 = 2*(i-j)*(1/k)*pi*\<i>"
    by (auto simp add: algebra_simps)
  from e1 e2 have "2*n*pi*\<i> = 2*(i-j)*(1/k)*pi*\<i>" by simp
  then have "2*n*k*pi*\<i> = 2*(i-j)*pi*\<i>"
    by (simp add: divide_simps \<open>k > 0\<close>)(simp add: field_simps)
  then have "2*n*k = 2*(i-j)"
    by (meson complex_i_not_zero mult_cancel_right of_int_eq_iff of_real_eq_iff pi_neq_zero)
  then have "n*k = i-j" by auto
  then show ?thesis by Groebner_Basis.algebra
qed

lemma unity_root_eq_1_iff:
  fixes k n :: nat
  assumes "k > 0" 
  shows "unity_root k n = 1 \<longleftrightarrow> k dvd n"
proof -
  have "unity_root k n = exp ((2*pi*n/k) * \<i>)"
    by (simp add: unity_root_conv_exp)
  also have "exp ((2*pi*n/k)* \<i>) = 1 \<longleftrightarrow> k dvd n"
    using complex_root_unity_eq_1[of k n] assms
    by (auto simp add: algebra_simps)
  finally show ?thesis by simp
qed

lemma unity_root_nonzero [simp]: "unity_root n k \<noteq> 0"
  by (auto simp: unity_root_def)

lemma unity_root_pow: "unity_root k n ^ m = unity_root k (n * m)"
  using unity_root_def
  by (simp add: Complex.DeMoivre mult.commute algebra_split_simps(6))

lemma unity_root_add: "unity_root k (m + n) = unity_root k m * unity_root k n"
  by (simp add: unity_root_conv_exp add_divide_distrib algebra_simps exp_add)

lemma unity_root_uminus: "unity_root k (-m) = cnj (unity_root k m)"
  unfolding unity_root_conv_exp exp_cnj by simp

lemma inverse_unity_root: "inverse (unity_root k m) = cnj (unity_root k m)" 
  unfolding unity_root_conv_exp exp_cnj by (simp add: field_simps exp_minus)

lemma unity_root_diff: "unity_root k (m - n) = unity_root k m * cnj (unity_root k n)"
  using unity_root_add[of k m "-n"] by (simp add: unity_root_uminus)

lemma unity_root_eq_1_iff_int:
  fixes k :: nat and n :: int
  assumes "k > 0" 
  shows "unity_root k n = 1 \<longleftrightarrow> k dvd n"
proof (cases "n \<ge> 0")
  case True
  obtain n' where "n = int n'" 
    using zero_le_imp_eq_int[OF True] by blast
  then show ?thesis 
    using unity_root_eq_1_iff[OF \<open>k > 0\<close>, of n'] of_nat_dvd_iff by blast
next
  case False
  then have "-n \<ge> 0" by auto
  have "unity_root k n = inverse (unity_root k (-n))"
    unfolding inverse_unity_root by (simp add: unity_root_uminus)
  then have "(unity_root k n = 1) = (unity_root k (-n) = 1)" 
    by simp
  also have "(unity_root k (-n) = 1) = (k dvd (-n))"
    using unity_root_eq_1_iff[of k "nat (-n)",OF \<open>k > 0\<close>] False 
          int_dvd_int_iff[of k "nat (-n)"] nat_0_le[OF \<open>-n \<ge> 0\<close>] by auto
  finally show ?thesis by simp
qed

lemma unity_root_eq_1 [simp]: "int k dvd n \<Longrightarrow> unity_root k n = 1"
  by (cases "k = 0") (auto simp: unity_root_eq_1_iff_int)

lemma unity_periodic_arithmetic:
  "periodic_arithmetic (unity_root k) k" 
  unfolding periodic_arithmetic_def 
proof
  fix n
  have "unity_root k (n + k) = unity_root k ((n+k) mod k)"
    using unity_root_mod[of k] zmod_int by presburger
  also have "unity_root k ((n+k) mod k) = unity_root k n" 
    using unity_root_mod zmod_int by auto
  finally show "unity_root k (n + k) = unity_root k n" by simp
qed

lemma unity_periodic_arithmetic_mult:
  "periodic_arithmetic (\<lambda>n. unity_root k (m * int n)) k"
  unfolding periodic_arithmetic_def
proof 
  fix n
  have "unity_root k (m * int (n + k)) = 
        unity_root k (m*n + m*k)"
    by (simp add: algebra_simps)
  also have "\<dots> = unity_root k (m*n)"
    using unity_root_mod[of k "m * int n"] unity_root_mod[of k "m * int n + m * int k"] 
          mod_mult_self3 by presburger
  finally show "unity_root k (m * int (n + k)) =
             unity_root k (m * int n)" by simp
qed

lemma unity_root_periodic_arithmetic_mult_minus:
  shows "periodic_arithmetic (\<lambda>i. unity_root k (-int i*int m)) k" 
  unfolding periodic_arithmetic_def
proof 
  fix n 
  have "unity_root k (-(n + k) * m) = cnj (unity_root k (n*m+k*m))" 
    by (simp add: ring_distribs unity_root_diff unity_root_add unity_root_uminus)
  also have "\<dots> = cnj (unity_root k (n*m))"
    using mult_period[of "unity_root k" k m] unity_periodic_arithmetic[of k]
    unfolding periodic_arithmetic_def by presburger
  also have "\<dots> = unity_root k (-n*m)"
    by (simp add: unity_root_uminus)
  finally show "unity_root k (-(n + k) * m) = unity_root k (-n*m)"
    by simp
qed

lemma unity_div:
 fixes a :: int and d :: nat
 assumes "d dvd k"
 shows "unity_root k (a*d) = unity_root (k div d) a" 
proof -
  have 1: "(2*pi*(a*d)/k) = (2*pi*a)/(k div d)"
    using Suc_pred assms by (simp add: divide_simps, fastforce)   
  have "unity_root k (a*d) = exp ((2*pi*(a*d)/k)* \<i>)"
    using unity_root_conv_exp by simp
  also have "\<dots> = exp (((2*pi*a)/(k div d))* \<i>)"
    using 1 by simp
  also have "\<dots> = unity_root (k div d) a"
    using unity_root_conv_exp by simp
  finally show ?thesis by simp
qed

lemma unity_div_num:
  assumes "k > 0" "d > 0" "d dvd k"
  shows "unity_root k (x * (k div d)) = unity_root d x"
  using assms dvd_div_mult_self unity_div by auto


section \<open>Geometric sums of roots of unity\<close>

text\<open>
  Apostol calls these `geometric sums', which is a bit too generic. We therefore decided
  to refer to them as `sums of roots of unity'.
\<close>
definition "unity_root_sum k n = (\<Sum>m<k. unity_root k (n * of_nat m))"

lemma unity_root_sum_0_left [simp]: "unity_root_sum 0 n = 0" and
      unity_root_sum_0_right [simp]: "k > 0 \<Longrightarrow> unity_root_sum k 0 = k" 
  unfolding unity_root_sum_def by simp_all

text \<open>Theorem 8.1\<close>
theorem unity_root_sum:
  fixes k :: nat and n :: int
  assumes gr: "k \<ge> 1"
  shows "k dvd n \<Longrightarrow> unity_root_sum k n = k"
    and "\<not>k dvd n \<Longrightarrow> unity_root_sum k n = 0"
proof -
  assume dvd: "k dvd n"
  let ?x = "unity_root k n"
  have unit: "?x = 1" using dvd gr unity_root_eq_1_iff_int by auto
  have exp: "?x^m = unity_root k (n*m)" for m using unity_root_pow by simp
  have "unity_root_sum k n = (\<Sum>m<k. unity_root k (n*m))" 
    using unity_root_sum_def by simp 
  also have "\<dots> = (\<Sum>m<k. ?x^m)" using exp by auto
  also have "\<dots> = (\<Sum>m<k. 1)" using unit by simp
  also have "\<dots> = k" using gr by (induction k, auto)
  finally show "unity_root_sum k n = k" by simp
next
  assume dvd: "\<not>k dvd n"
  let ?x = "unity_root k n"
  have "?x \<noteq> 1" using dvd gr unity_root_eq_1_iff_int by auto
  have "(?x^k - 1)/(?x - 1) = (\<Sum>m<k. ?x^m)"
    using geometric_sum[of ?x k, OF \<open>?x \<noteq> 1\<close>] by auto
  then have sum: "unity_root_sum k n = (?x^k - 1)/(?x - 1)"
    using unity_root_sum_def unity_root_pow by simp
  have "?x^k = 1" 
    using gr unity_root_eq_1_iff_int unity_root_pow by simp
  then show "unity_root_sum k n = 0" using sum by auto
qed

corollary unity_root_sum_periodic_arithmetic: 
 "periodic_arithmetic (unity_root_sum k) k"
  unfolding periodic_arithmetic_def
proof 
  fix n 
  show "unity_root_sum k (n + k) = unity_root_sum k n"
    by (cases "k = 0"; cases "k dvd n") (auto simp add: unity_root_sum)
qed

lemma unity_root_sum_nonzero_iff:
  fixes r :: int
  assumes "k \<ge> 1" and "r \<in> {-k<..<k}"
  shows "unity_root_sum k r \<noteq> 0 \<longleftrightarrow> r = 0"
proof
  assume "unity_root_sum k r \<noteq> 0"
  then have "k dvd r" using unity_root_sum assms by blast
  then show "r = 0" using assms(2) 
    using dvd_imp_le_int by force
next
  assume "r = 0"
  then have "k dvd r" by auto
  then have "unity_root_sum k r = k" 
    using assms(1) unity_root_sum by blast
  then show "unity_root_sum k r \<noteq> 0" using assms(1) by simp
qed

lemma cyclotomic_poly_conv_prod_unity_root:
  fixes n :: nat
  assumes n: "n > 0"
  defines "w \<equiv> (\<lambda>k. unity_root n (int k))"
  shows   "Polynomial.monom 1 n - 1 = (\<Prod>k<n. [:-w k, 1:])" (is "?lhs = ?rhs")
proof (rule ccontr)
  assume neq: "?lhs \<noteq> ?rhs"
  have "?lhs = Polynomial.monom 1 n + (-1)"
    by simp
  also have "degree \<dots> = n"
    by (subst degree_add_eq_left) (use n in \<open>auto simp: degree_monom_eq\<close>)
  finally have deg1: "degree ?lhs = n" .

  have "poly.coeff (?lhs - ?rhs) n = 0"
  proof -
    have "poly.coeff ?rhs n = lead_coeff ?rhs"
      by (simp add: degree_prod_sum_eq)
    also have "\<dots> = 1"
      by (subst lead_coeff_prod) auto
    finally show ?thesis
      using n by simp
  qed
  moreover have "?lhs - ?rhs \<noteq> 0"
    using neq by simp
  ultimately have "degree (?lhs - ?rhs) \<noteq> n"
    by (metis leading_coeff_0_iff)
  moreover have "degree (?lhs - ?rhs) \<le> n"
    by (rule degree_diff_le) (use deg1 in \<open>auto simp: degree_prod_sum_eq\<close>)
  ultimately have "degree (?lhs - ?rhs) < n"
    by linarith

  have root1: "poly ?lhs (w k) = 0" for k
    using \<open>n > 0\<close> by (simp add: w_def poly_monom unity_root_pow)
  have root2: "poly ?rhs (w k) = 0" if "k < n" for k
    using that by (auto simp: poly_prod)

  have "inj_on w {..<n}"
    using n by (auto simp: inj_on_def w_def dest!: unity_root_eqD)
  hence "card {..<n} = card (w ` {..<n})"
    by (subst card_image) auto
  also have "card (w ` {..<n}) \<le> card {z. poly (?lhs - ?rhs) z = 0}"
    by (intro card_mono poly_roots_finite) (use neq root1 root2 in auto)
  also have "card {z. poly (?lhs - ?rhs) z = 0} \<le> degree (?lhs - ?rhs)"
    by (rule card_poly_roots_bound) (use neq in auto)
  also have "\<dots> < n"
    by fact
  finally show False
    by simp
qed

lemma cyclotomic_poly_conv_prod_unity_root':
  fixes n :: nat
  assumes n: "n > 0"
  defines "w \<equiv> (\<lambda>k. unity_root n (int k))"
  shows   "1 - Polynomial.monom 1 n = (\<Prod>k<n. [:1, -w k:])" (is "?lhs = ?rhs")
proof -
  define A where "A = insert 0 (w ` {..<n})"
  have card_A: "card A = Suc n"
  proof -
    have "card A = Suc (card (w ` {..<n}))"
      unfolding A_def by (subst card.insert) (auto simp: w_def)
    also have "card (w ` {..<n}) = n"
      by (subst card_image) (use n in \<open>auto simp: inj_on_def w_def dest!: unity_root_eqD\<close>)
    finally show ?thesis .
  qed

  show ?thesis
  proof (rule poly_eqI_degree)
    have "degree (1 - Polynomial.monom 1 n :: complex poly) \<le> n"
      by (intro degree_diff_le) (auto simp: degree_monom_eq)
    thus "degree (1 - Polynomial.monom 1 n :: complex poly) < card A"
      by (simp add: card_A)
  next
    have "degree (\<Prod>k<n. [:1, - w k:]) \<le> n"
      by (rule order.trans[OF degree_prod_sum_le]) (auto simp: w_def)
    thus "degree (\<Prod>k<n. [:1, - w k:]) < card A"
      by (simp add: card_A)
  next
    fix x assume x: "x \<in> A"
    have "poly (1 - Polynomial.monom 1 n) (w k) = 0" for k
      by (simp add: poly_monom w_def unity_root_pow)
    moreover have "poly (1 - Polynomial.monom 1 n :: complex poly) 0 = 1"
      using n by (simp add: poly_monom power_0_left)
    moreover have "poly (\<Prod>k<n. [:1, -w k:]) (w k) = 0" if k: "k < n" for k
    proof -
      define k' where "k' = (if k = 0 then 0 else n - k)"
      have "w k * w k' = 1" "k' < n" using n k
        by (auto simp: k'_def w_def simp flip: unity_root_add intro!: unity_root_eq_1)
      thus ?thesis
        using that by (auto simp: poly_prod )
    qed
    moreover have "poly (\<Prod>k<n. [:1, -w k:]) 0 = 1"
      by (simp add: poly_prod)
    ultimately show "poly (1 - Polynomial.monom 1 n) x = poly (\<Prod>k<n. [:1, - w k:]) x"
      using x by (auto simp: A_def)
  qed
qed

end