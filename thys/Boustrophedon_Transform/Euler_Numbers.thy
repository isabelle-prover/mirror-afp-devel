section \<open>Euler numbers\<close>
theory Euler_Numbers
  imports Tangent_Numbers Secant_Numbers
begin

text \<open>
  Euler numbers and Euler polynomials are very similar to Bernoulli numbers and
  Bernoulli polynomials. They are closely related to the secant numbers -- and thereby
  also to the zigzag numbers (which are, confusingly, also sometimes referred to as
  ``Euler numbers'').~\oeiscite{A122045}

  Our definition of Euler numbers follows the convention in Mathematica
  (where they are called \texttt{EulerE[n]}) and ProofWiki: Let $S_n$ denote the secant numbers.
  Then:
  \[\mathcal{E}_{2n} = (-1)^n S_n \hskip3em \mathcal{E}_{2n+1} = 0\]
  such that in particular:
  \[\sum_{n=0}^\infty {\mathcal{E}_n}{n!} x^n = \sech x = \frac{1}{\cosh x}\]
  That is, the exponential generating function of the $\mathcal{E}_n$ is the
  hyperbolic secant.
\<close>
definition euler_number :: "nat \<Rightarrow> int" where
  "euler_number n = (if odd n then 0 else (-1) ^ (n div 2) * secant_number (n div 2))"

lemma euler_number_odd: "euler_number (2 * n) = (-1) ^ n * secant_number n"
  by (auto simp: euler_number_def)

lemma secant_number_conv_euler_number: "secant_number n = (-1) ^ n * euler_number (2 * n)"
  by (auto simp: euler_number_def)

lemma euler_number_odd_eq_0: "odd n \<Longrightarrow> euler_number n = 0"
  by (simp add: euler_number_def)

lemma euler_number_odd_numeral [simp]: "euler_number (numeral (Num.Bit1 n)) = 0"
  by (subst euler_number_odd_eq_0) auto

lemma euler_number_Suc_0 [simp]: "euler_number (Suc 0) = 0"
  by (subst euler_number_odd_eq_0) auto

lemma euler_number_0 [simp]: "euler_number 0 = 1"
  and euler_number_2 [simp]: "euler_number 2 = -1"
  by (simp_all add: euler_number_def secant_number_conv_aux secant_number_aux_def
                    secant_poly.simps(2) numeral_2_eq_2 Let_def pderiv_pCons)

lemma fps_nth_sech_conv_of_rat_fps_nth_sech:
  "fps_nth (fps_sech (1 :: 'a :: field_char_0)) n = of_rat (fps_nth (fps_sech (1 :: rat)) n)"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n = 0")
    case False
    hence "fps_nth (fps_sech (1 :: 'a :: field_char_0)) n = 
            -(\<Sum>i = 0..<n. fps_sech 1 $ i * fps_cosh 1 $ (n - i))"
      by (simp add: fps_sech_def fps_nth_inverse)
    also have "(\<Sum>i = 0..<n. fps_sech (1::'a) $ i * fps_cosh 1 $ (n - i)) =
               (\<Sum>i = 0..<n. of_rat (fps_sech 1 $ i) * fps_cosh 1 $ (n - i))"
      by (intro sum.cong arg_cong2[of _ _ _ _ "(*)"] less.IH refl) auto
    also have "-\<dots> = of_rat (-(\<Sum>i = 0..<n. fps_sech 1 $ i * fps_cosh 1 $ (n - i)))"
      by (simp add: fps_cosh_def of_rat_sum of_rat_mult of_rat_divide 
                    of_rat_add of_rat_power of_rat_minus)
    also have "-(\<Sum>i = 0..<n. fps_sech 1 $ i * fps_cosh 1 $ (n - i)) = fps_nth (fps_sech (1::rat)) n"
      using False by (simp add: fps_sech_def fps_nth_inverse)
    finally show ?thesis .
  qed auto
qed

lemma exponential_generating_function_euler_numbers:
  "Abs_fps (\<lambda>n. of_int (euler_number n) / fact n :: 'a :: field_char_0) = fps_sech 1"
proof (rule fps_ext)
  fix n :: nat
  have "fps_sech 1 = fps_sec 1 oo (fps_const \<i> * fps_X)"
    by (simp add: fps_sech_conv_sec)
  also have "fps_nth \<dots> n = \<i> ^ n * fps_nth (fps_sec 1) n"
    by (subst fps_nth_compose_linear) auto
  also have "fps_nth (fps_sec (1::complex)) n = 
               (if even n then of_nat (secant_number (n div 2)) / fact n else 0)"
    by (auto elim!: evenE simp: fps_nth_sec fps_nth_sec_odd)
  also have "\<i> ^ n * \<dots> = (euler_number n / fact n)"
    by (auto simp: euler_number_def)
  finally have *: "fps_nth (fps_sech (1 :: complex)) n = euler_number n / fact n"
    by simp

  have "of_rat (of_int (euler_number n) / fact n) = of_int (euler_number n) / fact n"
    by (simp add: of_rat_divide)
  also have "\<dots> = fps_nth (fps_sech (1::complex)) n"
    by (simp add: *)
  also have "\<dots> = of_rat (fps_sech 1 $ n)"
    by (subst fps_nth_sech_conv_of_rat_fps_nth_sech) auto
  finally have "fps_sech (1::rat) $ n = of_int (euler_number n) / fact n"
    unfolding of_rat_eq_iff ..

  have "fps_nth (fps_sech (1::'a)) n = of_rat (fps_sech 1 $ n)"
    by (subst fps_nth_sech_conv_of_rat_fps_nth_sech) auto
  also have "fps_sech (1::rat) $ n = of_int (euler_number n) / fact n"
    by fact
  also have "of_rat \<dots> = of_int (euler_number n) / fact n"
    by (simp add: of_rat_divide)
  finally show "fps_nth (Abs_fps (\<lambda>n. of_int (euler_number n) / fact n :: 'a :: field_char_0)) n = 
                  fps_nth (fps_sech 1) n"
    by simp
qed

text \<open>
  From the above, it easily follows that the sum over the Euler numbers 
  $\mathcal{E}_0$ to $\mathcal{E}_n$ weighted by binomial coefficients vanishes.
\<close>
theorem sum_binomial_euler_number_eq_0:
  assumes n: "n > 0" "even n"
  shows   "(\<Sum>k\<le>n. int (n choose k) * euler_number k) = 0"
proof -
  have "Abs_fps (\<lambda>n. euler_number n / fact n) * fps_cosh 1 = 1"
    unfolding exponential_generating_function_euler_numbers fps_sech_def
    by (rule inverse_mult_eq_1) auto
  hence "fps_nth (Abs_fps (\<lambda>n. euler_number n / fact n) * fps_cosh 1) n = fps_nth 1 n"
    by (rule arg_cong)
  hence "0 = fact n * (\<Sum>i=0..n. real_of_int (euler_number i) * 
                        (if even n = even i then 1 / fact (n - i) else 0) / fact i)"
    using n by (simp add: fps_eq_iff fps_mult_nth fps_nth_cosh cong: if_cong)
  also have "\<dots> = (\<Sum>i=0..n. real_of_int (euler_number i) * 
                        (if even n = even i then 1 / fact (n - i) else 0) / fact i * fact n)"
    by (simp add: sum_distrib_left sum_distrib_right mult_ac)
  also have "\<dots> = (\<Sum>i=0..n. real (n choose i) * euler_number i)"
    using n by (intro sum.cong) (auto simp: euler_number_odd_eq_0 binomial_fact mult_ac)
  also have "\<dots> = real_of_int (\<Sum>i\<le>n. int (n choose i) * euler_number i)"
    by (simp add: atLeast0AtMost)
  finally show ?thesis
    by linarith
qed

text \<open>
  This in particular gives us the following full-history recurrence for $\mathcal{E}_n$
  that is reminiscent of the Bernoulli numbers:
\<close>
corollary euler_number_rec:
  assumes n: "n > 0" "even n"
  shows   "euler_number n = -(\<Sum>k<n. int (n choose k) * euler_number k)"
proof -
  have "(\<Sum>k\<le>n. int (n choose k) * euler_number k) = 0"
    by (rule sum_binomial_euler_number_eq_0) fact+
  also have "{..n} = insert n {..<n}"
    by auto
  also have "(\<Sum>k\<in>\<dots>. int (n choose k) * euler_number k) = 
               euler_number n + (\<Sum>k<n. int (n choose k) * euler_number k)"
    by (subst sum.insert) (use n in auto)
  finally show ?thesis
    by linarith
qed

lemma euler_number_rec':
  "euler_number n =
     (if n = 0 then 1 else if odd n then 0 else -(\<Sum>k<n. int (n choose k) * euler_number k))"
  using euler_number_rec[of n] by (auto simp: euler_number_odd_eq_0)

lemma tangent_number_conv_euler_number:
  assumes n: "n > 0"
  defines "E \<equiv> euler_number"
  shows   "int (tangent_number n) = 
             (-1) ^ Suc n * (\<Sum>k\<le>2*n-2. int ((2*n-2) choose k) * E k * E (2*n-k-2))"
proof -
  have "int (tangent_number n) =
          (\<Sum>k<n. int (((2 * n - 2) choose (2*k)) * secant_number k * secant_number (n - k - 1)))"
    using n by (subst tangent_number_conv_secant_number) auto
  also have "\<dots> = (\<Sum>k<n. ((2 * n - 2) choose (2*k)) * (-1)^(n - 1) * E (2*k) * E (2*(n-k-1)))"
    by (rule sum.cong) (simp_all add: E_def euler_number_def flip: power_add)
  also have "\<dots> = (-1)^(n-1) * (\<Sum>k<n. ((2 * n - 2) choose (2*k)) * E (2*k) * E (2*(n - k - 1)))"
    by (simp add: sum_distrib_left sum_distrib_right mult_ac)
  also have "(-1)^(n-1) = ((-1)^Suc n :: int)"
    using n by (cases n) auto
  also have "(\<Sum>k<n. ((2 * n - 2) choose (2*k)) * E (2*k) * E (2*(n - k - 1))) =
             (\<Sum>k | k \<le> 2 * n - 2 \<and> even k. ((2 * n - 2) choose k) * E k * E (2 * n - 2 - k))"
    by (rule sum.reindex_bij_witness[of _ "\<lambda>k. k div 2" "\<lambda>k. 2 * k"])
       (use n in \<open>auto simp: diff_mult_distrib2\<close>)
  also have "\<dots> = (\<Sum>k\<le>2*n-2. ((2 * n - 2) choose k) * E k * E (2 * n - 2 - k))"
    by (rule sum.mono_neutral_left) (auto simp: E_def euler_number_odd_eq_0)
  finally show ?thesis 
    by simp
qed


section \<open>Euler polynomials\<close>

subsection \<open>Definition and basic properties\<close>

text \<open>
  Similarly to Bernoulli polynomials, one can also define Euler polynomials based on
  Euler numbers:
\<close>
definition euler_poly :: "nat \<Rightarrow> 'a :: field_char_0 \<Rightarrow> 'a" where
  "euler_poly n x = (\<Sum>k\<le>n. of_int ((n choose k) * euler_number k) / 2 ^ k * (x - 1/2) ^ (n - k))"

definition Euler_poly :: "nat \<Rightarrow> 'a :: field_char_0 poly" where
  "Euler_poly n =
     (\<Sum>k\<le>n. Polynomial.smult (of_int (int (n choose k) * euler_number k) / 2 ^ k) 
               ((Polynomial.monom 1 1 - [:1/2:]) ^ (n - k)))"

lemma lead_coeff_Euler_poly [simp]: "poly.coeff (Euler_poly n) n = 1"
proof -
  define P :: "nat \<Rightarrow> 'a poly" where "P = (\<lambda>k. (Polynomial.monom 1 1 - [:1 / 2:]) ^ (n - k))"
  have "poly.coeff (Euler_poly n :: 'a poly) n = 
          (\<Sum>k\<le>n. of_nat (n choose k) * of_int (euler_number k) * poly.coeff (P k) n / 2 ^ k)"
    unfolding Euler_poly_def by (simp add: coeff_sum P_def)
  also have "\<dots> = (\<Sum>k\<in>{0}. of_nat (n choose k) * of_int (euler_number k) * poly.coeff (P k) n / 2 ^ k)"
  proof (intro sum.mono_neutral_right ballI, goal_cases)
    case (3 k)
    have "degree (P k) = n - k"
      unfolding P_def by (simp add: monom_altdef degree_power_eq)
    with 3 have "poly.coeff (P k) n = 0"
      by (intro coeff_eq_0) auto
    thus ?case
      by simp
  qed auto
  also have "\<dots> = lead_coeff ([:- (1 / 2), 1:] ^ n)"
    by (simp add: P_def monom_altdef degree_power_eq)
  also have "\<dots> = 1"
    by (subst lead_coeff_power) auto
  finally show "poly.coeff (Euler_poly n :: 'a poly) n = 1" .
qed

lemma degree_Euler_poly [simp]: "degree (Euler_poly n) = n"
proof (rule antisym)
  show "degree (Euler_poly n) \<le> n"
    unfolding Euler_poly_def
    by (intro degree_sum_le) (auto simp: degree_power_eq monom_altdef)
  show "degree (Euler_poly n) \<ge> n"
    by (rule le_degree) simp
qed 

lemma poly_Euler_poly [simp]: "poly (Euler_poly n) = euler_poly n"
  by (rule ext) (simp add: Euler_poly_def poly_sum euler_poly_def poly_monom)

lemma euler_poly_onehalf:
  "euler_poly n (1 / 2) = (of_int (euler_number n) / 2 ^ n :: 'a :: field_char_0)"
proof -
  have "euler_poly n (1 / 2) =
          (\<Sum>k\<le>n. of_nat (n choose k) * of_int (euler_number k) * (0::'a) ^ (n - k) / 2 ^ k)"
    by (simp add: euler_poly_def)
  also have "\<dots> = (\<Sum>k\<in>{n}. of_int (euler_number n) / 2 ^ k)"
    by (rule sum.mono_neutral_cong_right) auto
  also have "\<dots> = of_int (euler_number n) / 2 ^ n"
    by simp
  finally show ?thesis .
qed

lemma Euler_poly_0 [simp]: "Euler_poly 0 = 1"
  and Euler_poly_1: "Euler_poly 1 = [:-(1 / 2), 1:]"
  and Euler_poly_2: "Euler_poly 2 = [:0, - 1, 1:]"
  using euler_number_2 
  by (simp_all add: Euler_poly_def monom_altdef numeral_2_eq_2 del: euler_number_2)

text \<open>
  Like Bernoulli polynomials, the Euler polynomials are an Appell sequence, i.e.\ 
  they satisfy $\mathcal{E}_n'(x) = n\mathcal{E}_{n-1}(x)$:
\<close>
lemma pderiv_Euler_poly: "pderiv (Euler_poly n) = of_nat n * Euler_poly (n - 1)"
proof (cases "n = 0")
  case False
  define m where "m = n - 1"
  have n: "n = Suc m"
    using False by (auto simp: m_def)
  define E where "E = euler_number"
  define X where "X = Polynomial.monom (1::'a) 1"
  write Polynomial.smult (infixl "*\<^sub>p" 69)
  have "pderiv (Euler_poly n) =
          (\<Sum>i\<le>n. Polynomial.smult (of_nat (Suc m choose i) * 
              of_int (E i * (n-i)) / 2^i) ((X - [:1/2:]) ^ (n - Suc i)))"
    using False
    by (simp add: Euler_poly_def pderiv_sum pderiv_smult pderiv_diff pderiv_power pderiv_monom
                  X_def E_def m_def mult_ac)
  also have "\<dots> = (\<Sum>i\<le>m. Polynomial.smult (of_nat (Suc m choose i) * 
                     of_int (E i * (n-i)) / 2^i) ((X - [:1/2:]) ^ (n - Suc i)))"
    by (rule sum.mono_neutral_right) (use False in \<open>auto simp: m_def\<close>)
  also have "\<dots> = (\<Sum>i\<le>m. of_nat n * (of_nat (m choose i) * 
                     of_int (E i) / 2 ^ i *\<^sub>p (X - [:1 / 2:]) ^ (m - i)))"
    by (intro sum.cong refl, subst of_nat_binomial_Suc) (use False in \<open>auto simp: m_def\<close>)
  also have "\<dots> = Polynomial.smult (of_nat n) (Euler_poly (n - 1))"
    by (simp add: Euler_poly_def smult_sum2 m_def E_def X_def mult_ac of_nat_poly)
  finally show ?thesis
    by (simp add: of_nat_poly)
qed auto


lemma continuous_on_euler_poly [continuous_intros]:
  fixes f :: "'a :: topological_space \<Rightarrow> 'b :: {real_normed_field, field_char_0}"
  assumes "continuous_on A f"
  shows   "continuous_on A (\<lambda>x. euler_poly n (f x))"
  unfolding poly_Euler_poly [symmetric] by (intro continuous_on_poly assms)

lemma continuous_euler_poly [continuous_intros]:
  fixes f :: "'a :: t2_space \<Rightarrow> 'b :: {real_normed_field, field_char_0}"
  assumes "continuous F f"
  shows   "continuous F (\<lambda>x. euler_poly n (f x))"
  unfolding poly_Euler_poly [symmetric] by (rule continuous_poly [OF assms])

lemma tendsto_euler_poly [tendsto_intros]:
  fixes f :: "'a :: t2_space \<Rightarrow> 'b :: {real_normed_field, field_char_0}"
  assumes "(f \<longlongrightarrow> c) F"
  shows   "((\<lambda>x. euler_poly n (f x)) \<longlongrightarrow> euler_poly n c) F"
  unfolding poly_Euler_poly [symmetric] by (rule tendsto_intros assms)+

lemma has_field_derivative_euler_poly [derivative_intros]:
  assumes "(f has_field_derivative f') (at x within A)"
  shows   "((\<lambda>x. euler_poly n (f x)) has_field_derivative
             (of_nat n * f' * euler_poly (n - 1) (f x))) (at x within A)"
  unfolding poly_Euler_poly [symmetric]
  by (rule derivative_eq_intros assms)+ (simp_all add: pderiv_Euler_poly)


text \<open>
  The exponential generating function of the Euler polynomials is:
  \[\sum_{n=0}^\infty \frac{\mathcal{E}_n(x)}{n!} t^n =
      \sech(t/2)e^{(x-\frac{1}{2})t} =
      \frac{2 e^{xt}}{e^t + 1}\]
\<close>
theorem exponential_generating_function_euler_poly:
  "Abs_fps (\<lambda>n. euler_poly n x / fact n :: 'a :: field_char_0) = 
     fps_sech (1 / 2) * fps_exp (x - 1 / 2)"
  "Abs_fps (\<lambda>n. euler_poly n x / fact n) =
     2 * fps_exp x / (fps_exp 1 + 1)"
proof -
  define E where "E = (\<lambda>c. fps_to_fls (fps_exp (c :: 'a)))"
  have [simp]: "E c \<noteq> 0" for c
    by (auto simp: E_def)
  have "Abs_fps (\<lambda>n. euler_poly n x / fact n :: 'a) =
          Abs_fps (\<lambda>n. (1/2)^n * of_int (euler_number n) / fact n) * 
          Abs_fps (\<lambda>n. (x - 1 / 2) ^ n / fact n)"
    by (simp add: euler_poly_def fps_eq_iff sum_divide_distrib binomial_fact fps_mult_nth
                  field_simps atLeast0AtMost)
  also have "Abs_fps (\<lambda>n. (1/2)^n * of_int (euler_number n) / fact n :: 'a) =
             Abs_fps (\<lambda>n. of_int (euler_number n) / fact n) oo (fps_const (1/2) * fps_X)"
    unfolding fps_compose_linear by simp
  also have "\<dots> = fps_sech (1 / 2)"
    unfolding exponential_generating_function_euler_numbers by simp
  also have "Abs_fps (\<lambda>n. (x - 1 / 2) ^ n / fact n) = fps_exp (x - 1 / 2)"
    by (simp add: fps_exp_def)
  finally show "Abs_fps (\<lambda>n. euler_poly n x / fact n :: 'a :: field_char_0) = 
                  fps_sech (1 / 2) * fps_exp (x - 1 / 2)" .

  also {
    have "fps_to_fls (fps_sech (1 / 2) * fps_exp (x - 1 / 2)) = 
            2 * E x / (E (1/2) * (E (1/2) + 1 / E (1/2)))"
      using fps_exp_add_mult[of x "-1/2"]
      by (simp add: fps_sech_def fps_cosh_def fls_times_fps_to_fls fls_inverse_const
            fps_exp_neg E_def divide_simps flip: fls_inverse_fps_to_fls fls_const_divide_const)
    also have "E (1/2) * (E (1/2) + 1 / E (1/2)) = E (1/2) ^ 2 + 1"
      by (simp add: algebra_simps power2_eq_square)
    also have "E (1 / 2) ^ 2 = E 1"
      by (simp add: E_def fps_exp_power_mult flip: fps_to_fls_power)
    also have "2 * E x / (E 1 + 1) = fps_to_fls (2 * fps_exp x / (fps_exp 1 + 1))"
      by (simp add: E_def fls_times_fps_to_fls flip: fls_divide_fps_to_fls)
    finally have "fps_sech (1 / 2) * fps_exp (x - 1 / 2) =
                  2 * fps_exp x / (fps_exp 1 + 1)"
      by (simp only: fps_to_fls_eq_iff)
  }
  finally show "Abs_fps (\<lambda>n. euler_poly n x / fact n) =
                  2 * fps_exp x / (fps_exp 1 + 1)" .
qed

text \<open>
  We also show the corresponding fact for Bernoulli theorems, namely
  \[\sum_{n\geq 0} \frac{\mathcal B_n(x)}{n!} t^n = \frac{t e^{tx}}{e^t - 1}\]
\<close>
theorem exponential_generating_function_bernpoly:
  fixes x :: "'a :: {field_char_0, real_normed_field}"
  shows "Abs_fps (\<lambda>n. bernpoly n x / fact n) = fps_X * fps_exp x / (fps_exp 1 - 1)"
proof -
  define E where "E = (\<lambda>c. fps_to_fls (fps_exp (c :: 'a)))"
  have [simp]: "E c \<noteq> 0" for c
    by (auto simp: E_def)
  have [simp]: "subdegree (1 - fps_exp (1 :: 'a)) = 1"
    by (rule subdegreeI) auto
  have "Abs_fps (\<lambda>n. bernpoly n x / fact n :: 'a) = bernoulli_fps * fps_exp x"
    unfolding fps_times_def
    by (simp add: bernpoly_def fps_eq_iff sum_divide_distrib binomial_fact
                  field_simps atLeast0AtMost)
  also have "\<dots> = fps_X * fps_exp x / (fps_exp 1 - 1)"
    unfolding bernoulli_fps_def by (subst fps_divide_times2) auto
  finally show ?thesis .
qed


(* TODO: Move t+ Bernoulli *)
definition Bernpoly :: "nat \<Rightarrow> 'a :: {real_algebra_1, field_char_0} poly" where
  "Bernpoly n = poly_of_list (map (\<lambda>k. of_nat (n choose k) * of_real (bernoulli (n - k))) [0..<Suc n])"

lemma coeff_Bernpoly:
  "poly.coeff (Bernpoly n) k = of_nat (n choose k) * of_real (bernoulli (n - k))"
  by (simp add: Bernpoly_def nth_default_def del: upt_Suc)

lemma degree_Bernpoly [simp]: "degree (Bernpoly n) = n"
proof (rule antisym)
  show "degree (Bernpoly n) \<le> n"
    by (rule degree_le) (auto simp: coeff_Bernpoly)
  show "degree (Bernpoly n) \<ge> n"
    by (rule le_degree) (auto simp: coeff_Bernpoly)
qed

lemma lead_coeff_Bernpoly [simp]: "poly.coeff (Bernpoly n) n = 1"
  by (subst coeff_Bernpoly) auto

lemma poly_Bernpoly [simp]: "poly (Bernpoly n) x = bernpoly n x"
proof -
  have "poly (Bernpoly n) x = (\<Sum>i\<le>n. of_nat (n choose i) * of_real (bernoulli (n - i)) * x ^ i)"
    by (simp add: poly_altdef coeff_Bernpoly)
  also have "\<dots> = bernpoly n x"
    unfolding bernpoly_def
    by (rule sum.reindex_bij_witness[of _ "\<lambda>i. n - i" "\<lambda>i. n - i"]) 
       (auto simp flip: binomial_symmetric)
  finally show ?thesis .
qed
(* END TODO *)



text \<open>
  The following two recurrences allow computing Bernoulli and Euler polynomials recursively.
\<close>
(* TODO: Move to Bernoulli *)
theorem bernpoly_recurrence:
  fixes x :: "'a :: {field_char_0, real_normed_field}"
  assumes n: "n > 0"
  shows "(\<Sum>s<n. of_nat (n choose s) * bernpoly s x) = of_nat n * x ^ (n - 1)"
proof -
  define F where "F = Abs_fps (\<lambda>n. bernpoly n x / fact n)"
  have F_eq: "F = fps_X * fps_exp x / (fps_exp 1 - 1)"
    unfolding F_def exponential_generating_function_bernpoly ..

  have "(\<Sum>s<n. of_nat (n choose s) * bernpoly s x / fact n) =
          fps_nth (F * (fps_exp 1 - 1)) n"
    unfolding F_def fps_mult_nth by (rule sum.mono_neutral_cong_left) (auto simp: binomial_fact)
  also have "F * (fps_exp 1 - 1) = fps_X * fps_exp x"
    unfolding F_eq by (metis bernoulli_fps_aux dvd_mult2 dvd_mult_div_cancel dvd_triv_right mult.commute)
  also have "fps_nth \<dots> n = x ^ (n - 1) / fact (n - 1)"
    using n by simp
  finally have "(\<Sum>s<n. of_nat (n choose s) * bernpoly s x) = x ^ (n - 1) * (fact n / fact (n - 1))"
    by (simp add: field_simps flip: sum_divide_distrib)
  also have "fact n / fact (n - 1) = (of_nat n :: 'a)"
    using \<open>n > 0\<close> by (subst fact_binomial [symmetric]) auto
  finally show "(\<Sum>s<n. of_nat (n choose s) * bernpoly s x) = of_nat n * x ^ (n - 1)"
    by (simp add: mult.commute)
qed

corollary bernpoly_recurrence':
  fixes x :: "'a :: {field_char_0, real_normed_field}"
  shows "bernpoly n x = x ^ n - (\<Sum>s<n. of_nat (Suc n choose s) * bernpoly s x) / of_nat (Suc n)"
proof -
  have "(\<Sum>s<Suc n. of_nat (Suc n choose s) * bernpoly s x) = of_nat (Suc n) * x ^ n"
    by (subst bernpoly_recurrence) auto
  also have "(\<Sum>s<Suc n. of_nat (Suc n choose s) * bernpoly s x) =
               of_nat (Suc n) * bernpoly n x + (\<Sum>s<n. of_nat (Suc n choose s) * bernpoly s x)"
    by simp
  finally have "of_nat (Suc n) * bernpoly n x =
                  of_nat (Suc n) * x ^ n - (\<Sum>s<n. of_nat (Suc n choose s) * bernpoly s x)"
    by (simp add: algebra_simps)
  thus "bernpoly n x = x ^ n - (\<Sum>s<n. of_nat (Suc n choose s) * bernpoly s x) / of_nat (Suc n)"
    by (simp add: field_simps del: of_nat_Suc)
qed

theorem Bernpoly_recurrence:
  assumes "n > 0"
  shows   "(\<Sum>s<n. Polynomial.smult (of_nat (n choose s)) (Bernpoly s)) =
             Polynomial.monom (of_nat n :: 'a :: {field_char_0, real_normed_field}) (n - 1)"
    (is "?lhs = ?rhs")
proof -
  have "poly ?lhs x = poly ?rhs x" for x
    using bernpoly_recurrence[of n x] assms by (simp add: poly_sum poly_monom)
  thus "?lhs = ?rhs"
    by blast
qed

theorem Bernpoly_recurrence':
  shows   "Bernpoly n = Polynomial.monom (1 :: 'a :: {field_char_0, real_normed_field}) n - 
             Polynomial.smult (1 / of_nat (Suc n))
               (\<Sum>s<n. Polynomial.smult (of_nat (Suc n choose s)) (Bernpoly s))"
    (is "?lhs = ?rhs")
proof -
  have "poly ?lhs x = poly ?rhs x" for x
    using bernpoly_recurrence'[of n x] by (simp add: poly_sum poly_monom)
  thus "?lhs = ?rhs"
    by blast
qed
(* END TODO *)


theorem euler_poly_recurrence:
  fixes x :: "'a :: {field_char_0}"
  shows "euler_poly n x = x ^ n - (\<Sum>s<n. of_nat (n choose s) * euler_poly s x) / 2"
proof -
  define F where "F = Abs_fps (\<lambda>n. euler_poly n x / fact n)"
  have F_eq: "F = 2 * fps_exp x / (fps_exp 1 + 1)"
    unfolding F_def exponential_generating_function_euler_poly(2) ..

  have "2 * euler_poly n x / fact n +
            (\<Sum>s<n. (if s = n then 2 else 1) * of_nat (n choose s) * euler_poly s x / fact n) =
          (\<Sum>s\<in>insert n {..<n}. (if s = n then 2 else 1) * of_nat (n choose s) * euler_poly s x / fact n)"
    by (subst sum.insert) auto
  also have "insert n {..<n} = {..n}"
    by auto
  also have "(\<Sum>s<n. (if s = n then 2 else 1) * of_nat (n choose s) * euler_poly s x / fact n) =
             (\<Sum>s<n. of_nat (n choose s) * euler_poly s x / fact n)"
    by (rule sum.cong) auto
  also have "(\<Sum>s\<le>n. (if s = n then 2 else 1) * of_nat (n choose s) * euler_poly s x / fact n) =
          fps_nth (F * (fps_exp 1 + 1)) n"
    unfolding F_def fps_mult_nth by (rule sum.mono_neutral_cong_left) (auto simp: binomial_fact)
  also have "F * (fps_exp 1 + 1) = 2 * fps_exp x"
    unfolding F_eq  by (subst fps_divide_unit) auto
  also have "fps_nth \<dots> n = 2 * x ^ n / fact n"
    by simp
  finally show "euler_poly n x = x ^ n - (\<Sum>s<n. of_nat (n choose s) * euler_poly s x) / 2"
    by (simp add: field_simps flip: sum_divide_distrib)
qed

theorem Euler_poly_recurrence:
  "Euler_poly n = (Polynomial.monom 1 n :: 'a :: field_char_0 poly) - 
     Polynomial.smult (1/2) (\<Sum>s<n. Polynomial.smult (of_nat (n choose s)) (Euler_poly s))"
    (is "_ = ?rhs")
proof -
  have "poly (Euler_poly n) x = poly ?rhs x" for x
  proof -
    have "poly (Euler_poly n) x = euler_poly n x"
      by simp
    also have "\<dots> = poly ?rhs x"
      by (subst euler_poly_recurrence) (simp_all add: poly_monom poly_sum)
    finally show "poly (Euler_poly n) x = poly ?rhs x" .
  qed
  thus "Euler_poly n = ?rhs"
    by blast
qed

lemma euler_poly_1_even:
  assumes "even n" "n > 1"
  shows   "euler_poly n 1 = 0"
proof -
  have "euler_poly n 1 = of_int (\<Sum>k\<le>n. int (n choose k) * (euler_number k)) / 2 ^ n"
    by (simp add: euler_poly_def power_diff field_simps flip: sum_divide_distrib)
  also have "(\<Sum>k\<le>n. int (n choose k) * (euler_number k)) = 0"
    by (rule sum_binomial_euler_number_eq_0) (use assms in auto)
  finally show ?thesis
    by simp
qed


subsection \<open>Addition and reflection theorems\<close>

text \<open>
  The Euler polynomials satisfy the following addition theorem:
  \[\mathcal{E}_n(x+y) = \sum_{k=0}^n {n\choose k} \mathcal{E}_k(x) y^{n-k}\]
\<close>
theorem euler_poly_addition:
  "euler_poly n (x + y) = (\<Sum>k\<le>n. of_nat (n choose k) * euler_poly k x * y ^ (n - k))"
proof -
  define E where "E = (\<lambda>k. of_int (euler_number k) :: 'a)"
  have "euler_poly n (x + y) =
          (\<Sum>k\<le>n. of_nat (n choose k) * E k * (x + y - 1 / 2) ^ (n - k) / 2 ^ k)"
    by (simp add: euler_poly_def E_def)
  also have "\<dots> = (\<Sum>k\<le>n. of_nat (n choose k) * E k *
                    (\<Sum>i\<le>n-k. of_nat (n - k choose i) * (x - 1/2) ^ i * y ^ (n - k - i)) / 2 ^ k)"
  proof (rule sum.cong, goal_cases)
    case (2 k)
    have "((x - 1 / 2) + y) ^ (n - k) = 
            (\<Sum>i\<le>n-k. of_nat (n - k choose i) * (x - 1/2) ^ i * y ^ (n - k - i))"
      by (subst binomial_ring) auto
    thus ?case
      by (simp add: algebra_simps)
  qed auto
  also have "\<dots> = (\<Sum>(k,i)\<in>(SIGMA k:{..n}. {..n-k}).
                    of_nat (n choose k) * E k * of_nat (n - k choose i) * 
                    (x - 1/2) ^ i * y ^ (n - k - i) / 2 ^ k)"
    by (simp add: sum_distrib_left sum_distrib_right sum_divide_distrib mult_ac sum.Sigma)
  also have "\<dots> = (\<Sum>(k,i)\<in>(SIGMA k:{..n}. {..k}).
                    of_nat (n choose k) * E i * of_nat (k choose i) *
                    (x - 1/2) ^ (k - i) * y ^ (n - k) / 2 ^ i)"
    by (rule sum.reindex_bij_witness[of _ "\<lambda>(k,i). (i, k - i)" "\<lambda>(k, i). (i + k, k)"])
       (auto simp: binomial_fact algebra_simps)
  also have "\<dots> = (\<Sum>k\<le>n. of_nat (n choose k) * euler_poly k x * y ^ (n - k))"
    by (simp add: euler_poly_def E_def sum_distrib_left sum_distrib_right 
                  sum_divide_distrib mult_ac sum.Sigma)
  finally show ?thesis .
qed

text \<open>
  The Bernoulli polynomials actually satisfy an analogous theorem.
\<close>
(* TODO: move to Bernoulli entry *)
theorem bernpoly_addition:
  fixes x y :: "'a :: {field_char_0, real_normed_field}"
  shows "bernpoly n (x + y) = (\<Sum>k\<le>n. of_nat (n choose k) * bernpoly k x * y ^ (n - k))"
proof -
  define B where "B = (\<lambda>k. of_real (bernoulli k) :: 'a)"
  have "bernpoly n (x + y) =
          (\<Sum>k\<le>n. of_nat (n choose k) * B k * (x + y) ^ (n - k))"
    by (simp add: bernpoly_def B_def)
  also have "\<dots> = (\<Sum>k\<le>n. of_nat (n choose k) * B k *
                    (\<Sum>i\<le>n-k. of_nat (n - k choose i) * x ^ i * y ^ (n - k - i)))"
  proof (rule sum.cong, goal_cases)
    case (2 k)
    have "(x + y) ^ (n - k) = 
            (\<Sum>i\<le>n-k. of_nat (n - k choose i) * x ^ i * y ^ (n - k - i))"
      by (subst binomial_ring) auto
    thus ?case
      by (simp add: algebra_simps)
  qed auto
  also have "\<dots> = (\<Sum>(k,i)\<in>(SIGMA k:{..n}. {..n-k}).
                    of_nat (n choose k) * B k * of_nat (n - k choose i) * 
                    x ^ i * y ^ (n - k - i))"
    by (simp add: sum_distrib_left sum_distrib_right sum_divide_distrib mult_ac sum.Sigma)
  also have "\<dots> = (\<Sum>(k,i)\<in>(SIGMA k:{..n}. {..k}).
                    of_nat (n choose k) * B i * of_nat (k choose i) *
                    x ^ (k - i) * y ^ (n - k))"
    by (rule sum.reindex_bij_witness[of _ "\<lambda>(k,i). (i, k - i)" "\<lambda>(k, i). (i + k, k)"])
       (auto simp: binomial_fact algebra_simps)
  also have "\<dots> = (\<Sum>k\<le>n. of_nat (n choose k) * bernpoly k x * y ^ (n - k))"
    by (simp add: bernpoly_def B_def sum_distrib_left sum_distrib_right 
                  sum_divide_distrib mult_ac sum.Sigma)
  finally show ?thesis .
qed

theorem euler_poly_reflect:
  "euler_poly n (1 - x) = (-1) ^ n * euler_poly n x"
proof -
  have "(-1) ^ n * euler_poly n x =
          (\<Sum>k\<le>n. of_nat (n choose k) * of_int (euler_number k) *
                    ((-1) ^ n * ((x - 1 / 2)) ^ (n - k)) / 2 ^ k)"
    unfolding sum_distrib_left euler_poly_def
    by (intro sum.cong) (simp_all add: mult_ac)
  also have "\<dots> = (\<Sum>k\<le>n. of_nat (n choose k) * of_int (euler_number k) *
                    ((-1) ^ (n - k) * (x - 1 / 2) ^ (n - k)) / 2 ^ k)"
    by (intro sum.cong) (auto simp: uminus_power_if euler_number_odd_eq_0)
  also have "\<dots> = (\<Sum>k\<le>n. of_nat (n choose k) * of_int (euler_number k) *
                    (1 / 2 - x) ^ (n - k) / 2 ^ k)"
    unfolding power_mult_distrib [symmetric] by simp
  also have "\<dots> = euler_poly n (1 - x)"
    by (simp add: euler_poly_def)
  finally show ?thesis ..
qed

theorem euler_poly_forward_sum: "euler_poly n x + euler_poly n (x + 1) = 2 * x ^ n"
proof -
  have "Abs_fps (\<lambda>n. euler_poly n x / fact n) + Abs_fps (\<lambda>n. euler_poly n (x + 1) / fact n) =
          2 * fps_exp x / (fps_exp 1 + 1) + fps_exp 1 * (2 * fps_exp x) / (fps_exp 1 + 1)"
    unfolding exponential_generating_function_euler_poly(2) fps_exp_add_mult
    by (simp add: mult_ac)
  also have "fps_exp 1 * (2 * fps_exp x) / (fps_exp 1 + 1) =
               fps_exp 1 * (2 * fps_exp x / (fps_exp 1 + 1))"
    by (subst fps_divide_times) auto
  also have "2 * fps_exp x / (fps_exp 1 + 1) + fps_exp 1 * (2 * fps_exp x / (fps_exp 1 + 1)) =
             (fps_exp 1 + 1) * (2 * fps_exp x / (fps_exp 1 + 1))"
    by Groebner_Basis.algebra
  also have "\<dots> = 2 * fps_exp x"
    by simp
  also have "fps_nth \<dots> n = 2 * x ^ n / fact n"
    by simp
  finally show ?thesis
    by (simp add: field_simps)
qed

lemma euler_poly_plus1: "euler_poly n (x + 1) = -euler_poly n x + 2 * x ^ n"
  using euler_poly_forward_sum[of n x] by (simp add: algebra_simps)

lemma euler_poly_minus:
  "(-1) ^ n * euler_poly n (-x) = -euler_poly n x + 2 * x ^ n"
  using euler_poly_reflect[of n "-x"] euler_poly_plus1[of n "x"]
  by (simp add: algebra_simps)

text \<open>
  As an analogon of Faulhaber's formula for sums of the form $x^k + (x+1)^k + \ldots$,
  we can express an alternating sum of the form $x^k - (x+1)^k + (x+2)^k + \ldots$ in terms
  of the $k$-th Euler polynomial.
\<close>
corollary alternating_power_sum_conv_euler_poly:
  "(\<Sum>i<k. (-1) ^ i * (x + of_nat i) ^ n) =
     (euler_poly n x - (-1) ^ k * euler_poly n (x + of_nat k)) / 2"
proof -
  define E :: "'a \<Rightarrow> 'a" where "E = euler_poly n"
  have "(\<Sum>i<k. (-1) ^ i * (x + of_nat i) ^ n) = (E x - (-1) ^ k * E (x + of_nat k)) / 2"
  proof (induction k)
    case (Suc k)
    have "(\<Sum>i<Suc k. (-1) ^ i * (x + of_nat i) ^ n) =
            (\<Sum>i<k. (-1) ^ i * (x + of_nat i) ^ n) + (-1) ^ k * (x + of_nat k) ^ n"
      by simp
    also have "(\<Sum>i<k. (-1) ^ i * (x + of_nat i) ^ n) = (E x - (-1) ^ k * E (x + of_nat k)) / 2"
      by (rule Suc.IH)
    also have "(x + of_nat k) ^ n = (E (x + of_nat k) + E (x + of_nat (Suc k))) / 2"
      using euler_poly_forward_sum[of n "x + of_nat k"] by (simp add: E_def add_ac)
    finally show ?case
      by (simp add: diff_divide_distrib add_divide_distrib ring_distribs)
  qed auto
  thus ?thesis
    by (simp add: E_def)
qed


subsection \<open>Multiplication theorems\<close>

text \<open>
  For any positive integer $m$, the Bernoulli polynomials satisfy:
  \[\mathcal {B}_n(mx) = m^{n-1} \sum_{k=0}^{m-1} \mathcal {B}_n(x + k/m)\]
\<close>
theorem bernpoly_mult:
  fixes x :: "'a :: {real_normed_field, field_char_0}"
  assumes m: "m > 0"
  shows   "bernpoly n (of_nat m * x) =
             of_nat m powi (int n - 1) * (\<Sum>k<m. bernpoly n (x + of_nat k / of_nat m))"
proof -
  define F where "F = (\<lambda>c (x::'a). Abs_fps (\<lambda>n. bernpoly n (of_nat c * x) / fact n))"
  have F_eq: "F c x = fps_X * fps_exp (of_nat c * x) / (fps_exp 1 - 1)" for c x
    by (simp add: F_def exponential_generating_function_bernpoly fps_exp_power_mult)
  define E where "E = (\<lambda>c::'a. fps_to_fls (fps_exp c))"
  have E_add: "E (c + c') = E c * E c'" for c c'
    by (simp add: E_def fps_exp_add_mult fls_times_fps_to_fls)
  have E_power: "E c ^ m = E (of_nat m * c)" for c m
    by (simp add: E_def fps_exp_power_mult flip: fps_to_fls_power)
  have minus_one_power_fps: "(-1)^k = fps_const ((-1::'a) ^ k)" for k
    by (simp flip: fps_const_power fps_const_neg)
  have fls_neqI: "F \<noteq> G" if "fls_nth F 0 \<noteq> fls_nth G 0" for F G :: "'a fls"
    using that by metis
  have fls_neqI': "F \<noteq> G" if "fls_nth F 1 \<noteq> fls_nth G 1" for F G :: "'a fls"
    using that by metis
  have fps_neqI: "F \<noteq> G" if "fps_nth F 0 \<noteq> fps_nth G 0" for F G :: "'a fps"
    using that by metis
  have [simp]: "fls_nth (E c) n = c ^ (nat n) / fact (nat n)" if "n \<ge> 0" for c n
    using that by (auto simp: E_def)
  have [simp]: "subdegree (1 - fps_exp 1 :: 'a fps) = 1"
    by (rule subdegreeI) auto

  have "fps_to_fls (of_nat m * F m x -fps_compose (\<Sum>k<m. F 1 (x + of_nat k / of_nat m)) (of_nat m * fps_X)) =
          of_nat m * (fls_X * E (of_nat m * x)) / (E 1 - 1) -
         (\<Sum>k<m. of_nat m * (fls_X * E (of_nat m * x + of_nat k)) / (E (of_nat m) - 1))"
    unfolding F_eq using m
    by (simp add: fls_times_fps_to_fls flip: fps_of_nat fls_compose_fps_to_fls)
       (simp add: fls_times_fps_to_fls fps_to_fls_sum fps_to_fls_power fps_shift_to_fls E_def 
                  mult.assoc fls_compose_fps_divide fls_compose_fps_diff fls_compose_fps_mult  
                  fls_compose_fps_power ring_distribs
             flip: fps_of_nat fls_divide_fps_to_fls fls_of_nat)
  also have "(\<Sum>k<m. of_nat m * (fls_X * E (of_nat m * x + of_nat k)) / (E (of_nat m) - 1)) =
             of_nat m * fls_X * E x ^ m * (\<Sum>i<m. E 1 ^ i) / (E (of_nat m) - 1)"
    by (simp add: sum_divide_distrib sum_distrib_left sum_distrib_right 
                  algebra_simps E_power E_add power_minus')
  also have "(\<Sum>i<m. E 1 ^ i) =  (1 - E 1 ^ m) / (1 - E 1)"
    by (subst sum_gp_strict) (use \<open>m > 0\<close> in \<open>auto simp: fls_neqI'\<close>)
  also have "E (of_nat m) = E 1 ^ m"
    by (simp add: E_power)
  also have "of_nat m * fls_X * E x ^ m * ((1 - E 1 ^ m) / (1 - E 1)) / (E 1 ^ m - 1) = 
             -of_nat m * fls_X * E x ^ m / (1 - E 1)"
    using m by (simp add: divide_simps fls_neqI fls_neqI' E_power) (auto simp: algebra_simps)
  also have "\<dots> = of_nat m * fls_X * E x ^ m / (E 1 - 1)"
    by (simp add: field_simps fls_neqI')
  also have "of_nat m * (fls_X * E (of_nat m * x)) / (E 1 - 1) - 
             of_nat m * fls_X * E x ^ m / (E 1 - 1) = 0"
    by (simp add: E_power)
  also have "fls_nth \<dots> n = 0"
    by simp
  finally have "of_nat m * bernpoly n (of_nat m * x) =
                 of_nat m ^ n * (\<Sum>k<m. bernpoly n (x + of_nat k / of_nat m))"
    by (simp add: F_def minus_one_power_fps fps_sum_nth fps_nth_compose_linear nat_add_distrib
                  mult.assoc flip: fps_of_nat sum_divide_distrib)
  also have "of_nat m ^ n = (of_nat m * of_nat m powi (int n - 1) :: 'a)"
    using \<open>m > 0\<close> by (subst power_int_diff) auto
  finally show ?thesis
    using \<open>m > 0\<close> by simp
qed

text \<open>
  The corresponding theorem for the Euler polynomials is more complicated. For odd positive
  integers $m$, we have following still very simple theorem:
  \[\mathcal {E}_n(mx) = m^n \sum_{k=0}^{m-1} (-1)^k \mathcal {E}_n(x + k/m)\]
\<close>
theorem euler_poly_mult_odd:
  assumes "odd m"
  shows   "euler_poly n (of_nat m * x) =
             of_nat m ^ n * (\<Sum>k<m. (-1) ^ k * euler_poly n (x + of_nat k / of_nat m))"
proof -
  define F where "F = (\<lambda>c (x::'a). Abs_fps (\<lambda>n. euler_poly n (of_nat c * x) / fact n))"
  have F_eq: "F c x = 2 * fps_exp x ^ c / (fps_exp 1 + 1)" for c x
    by (simp add: F_def exponential_generating_function_euler_poly(2) fps_exp_power_mult)
  define E where "E = (\<lambda>c::'a. fps_to_fls (fps_exp c))"
  have E_add: "E (c + c') = E c * E c'" for c c'
    by (simp add: E_def fps_exp_add_mult fls_times_fps_to_fls)
  have E_power: "E c ^ m = E (of_nat m * c)" for c m
    by (simp add: E_def fps_exp_power_mult flip: fps_to_fls_power)
  have minus_one_power_fps: "(-1)^k = fps_const ((-1::'a) ^ k)" for k
    by (simp flip: fps_const_power fps_const_neg)
  have fls_neqI: "F \<noteq> G" if "fls_nth F 0 \<noteq> fls_nth G 0" for F G :: "'a fls"
    using that by metis
  have fps_neqI: "F \<noteq> G" if "fps_nth F 0 \<noteq> fps_nth G 0" for F G :: "'a fps"
    using that by metis
  have [simp]: "fls_nth (E c) n = c ^ (nat n) / fact (nat n)" if "n \<ge> 0" for c n
    using that by (auto simp: E_def)

  have "F m x - fps_compose (\<Sum>k<m. (-1)^k * F 1 (x + of_nat k / of_nat m)) (of_nat m * fps_X) =
          2 * fps_exp x ^ m / (fps_exp 1 + 1) - 
            (\<Sum>k<m. (-1)^k * (2 * fps_exp (of_nat m * x + of_nat k) / (fps_exp (of_nat m) + 1)))"
    unfolding exponential_generating_function_euler_poly(2)
    by (simp add: fps_exp_power_mult F_eq fps_compose_sum_distrib
                  fps_compose_mult_distrib fps_compose_divide_distrib fps_compose_add_distrib
                  fps_compose_uminus fps_neqI ring_distribs flip: fps_compose_power fps_of_nat)
  also have "fps_to_fls \<dots> = 
               2 * E x ^ m / (E 1 + 1) -
               (\<Sum>k<m. (-1)^k * (2 * E (of_nat m * x + of_nat k)) / (E (of_nat m) + 1))"
    by (simp add: fls_times_fps_to_fls fps_to_fls_power E_def
             flip: fls_divide_fps_to_fls )
  also have "\<dots> = 2 * (E x ^ m / (E 1 + 1) - E x ^ m * (\<Sum>k<m. (-E 1) ^ k) / (E (of_nat m) + 1))"
    by (simp add: diff_divide_distrib sum_distrib_left sum_distrib_right mult_ac E_add E_power
                  power_minus' flip: sum_divide_distrib)
  also have "(\<Sum>k<m. (-E 1) ^ k) = (1 - (-E 1) ^ m) / (1 + E 1)"
    by (subst sum_gp_strict) (auto simp: fls_neqI)
  also have "\<dots> = (1 + E 1 ^ m) / (1 + E 1)"
    using \<open>odd m\<close> by (auto simp: uminus_power_if)
  also have "E 1 ^ m = E (of_nat m)"
    using \<open>odd m\<close> by (auto simp: E_power)
  also have "2 * (E x ^ m / (E 1 + 1) - E x ^ m * ((1 + E (of_nat m)) / (1 + E 1)) / (E (of_nat m) + 1)) = 0"
    by (simp add: divide_simps add_ac fls_neqI)
  also have "fls_nth \<dots> n = 0"
    by simp
  finally show ?thesis
    by (simp add: F_def fps_sum_nth fps_compose_linear minus_one_power_fps
             flip: fps_of_nat sum_divide_distrib)
qed

text \<open>
  For even positive $m$ on the other hand, we have the following:
  \[\mathcal {E}_n(mx) = -\frac{2m^n}{n+1} \sum_{k=0}^{m-1} (-1)^k \mathcal{B}_{n+1}(x + k/m)\]
\<close>
theorem euler_poly_mult_even:
  fixes x :: "'a :: {real_normed_field, field_char_0}"
  assumes m: "even m" "m > 0"
  shows   "euler_poly n (of_nat m * x) =
             -2 * of_nat m ^ n / of_nat (Suc n) * 
               (\<Sum>k<m. (-1) ^ k * bernpoly (Suc n) (x + of_nat k / of_nat m))"
proof -
  define F where "F = (\<lambda>c (x::'a). Abs_fps (\<lambda>n. euler_poly n (of_nat c * x) / fact n))"
  define G where "G = (\<lambda>c (x::'a). Abs_fps (\<lambda>n. bernpoly n (of_nat c * x) / fact n))"
  have *: "(-1) ^ k = fps_const ((-1)^k :: 'a)" for k
    by auto
  have F_eq: "F c x = 2 * fps_exp x ^ c / (fps_exp 1 + 1)" for c x
    by (simp add: F_def exponential_generating_function_euler_poly(2) fps_exp_power_mult)
  have G_eq: "G c x = fps_X * fps_exp (of_nat c * x) / (fps_exp 1 - 1)" for c x
    by (simp add: G_def exponential_generating_function_bernpoly fps_exp_power_mult)
  define E where "E = (\<lambda>c::'a. fps_to_fls (fps_exp c))"
  have E_add: "E (c + c') = E c * E c'" for c c'
    by (simp add: E_def fps_exp_add_mult fls_times_fps_to_fls)
  have E_power: "E c ^ m = E (of_nat m * c)" for c m
    by (simp add: E_def fps_exp_power_mult flip: fps_to_fls_power)
  have minus_one_power_fps: "(-1)^k = fps_const ((-1::'a) ^ k)" for k
    by (simp flip: fps_const_power fps_const_neg)
  have fls_neqI: "F \<noteq> G" if "fls_nth F 0 \<noteq> fls_nth G 0" for F G :: "'a fls"
    using that by metis
  have fls_neqI': "F \<noteq> G" if "fls_nth F 1 \<noteq> fls_nth G 1" for F G :: "'a fls"
    using that by metis
  have fps_neqI: "F \<noteq> G" if "fps_nth F 0 \<noteq> fps_nth G 0" for F G :: "'a fps"
    using that by metis
  have [simp]: "fls_nth (E c) n = c ^ (nat n) / fact (nat n)" if "n \<ge> 0" for c n
    using that by (auto simp: E_def)
  have [simp]: "subdegree (1 - fps_exp 1 :: 'a fps) = 1"
    by (rule subdegreeI) auto

  have "fps_to_fls (fps_X * of_nat m * F m x + 2 * fps_compose (\<Sum>k<m. (-1)^k * (G 1 (x + of_nat k / of_nat m))) (of_nat m * fps_X)) =
          fls_X * (of_nat m * (2 * E x ^ m / (E 1 + 1))) +
          2 * (\<Sum>i<m. (-1) ^ i * of_nat m * fls_X * E (of_nat m * x + of_nat i) / (E (of_nat m) - 1))"
    unfolding F_eq G_eq using m
    by (simp add: fls_times_fps_to_fls flip: fps_of_nat fls_compose_fps_to_fls)
       (simp add: fls_times_fps_to_fls fps_to_fls_sum fps_to_fls_power fps_shift_to_fls E_def 
                  mult.assoc fls_compose_fps_divide fls_compose_fps_diff fls_compose_fps_mult 
                  fls_compose_fps_power ring_distribs
             flip: fps_of_nat fls_divide_fps_to_fls fls_of_nat)
  also have "(\<Sum>i<m. (-1) ^ i * of_nat m * fls_X * E (of_nat m * x + of_nat i) / (E (of_nat m) - 1)) =
             of_nat m * fls_X * E x ^ m * (\<Sum>i<m. (-E 1) ^ i) / (E (of_nat m) - 1)"
    by (simp add: sum_divide_distrib sum_distrib_left sum_distrib_right 
                  algebra_simps E_power E_add power_minus')
  also have "(\<Sum>i<m. (-E 1) ^ i) = (1 - (-E 1) ^ m) / (1 + E 1)"
    by (subst sum_gp_strict) (auto simp: fls_neqI)
  also have "1 - (-E 1) ^ m = 1 - E 1 ^ m"
    using \<open>even m\<close> by auto
  also have "E (of_nat m) = E 1 ^ m"
    by (simp add: E_power)
  also have "of_nat m * fls_X * E x ^ m * ((1 - E 1 ^ m) / (1 + E 1)) / (E 1 ^ m - 1) = 
             -of_nat m * fls_X * E x ^ m / (1 + E 1)"
    using m by (simp add: divide_simps fls_neqI fls_neqI' E_power) (auto simp: algebra_simps)
  also have "fls_X * (of_nat m * (2 * E x ^ m / (E 1 + 1))) + 
               2 * (- of_nat m * fls_X * E x ^ m / (1 + E 1)) = 0"
    by (simp add: algebra_simps)
  also have "fls_nth \<dots> (Suc n) = 0"
    by simp
  finally have "0 = (of_nat m * euler_poly n (of_nat m * x) / fact n) +
                  2 * (of_nat m * (of_nat m ^ n * 
                    (\<Sum>k<m. (-1) ^ k * bernpoly (Suc n) (x + of_nat k / of_nat m)))) / 
                      ((1 + of_nat n) * fact n)"
    by (simp add: F_def G_def * fps_sum_nth fps_nth_compose_linear nat_add_distrib
                  mult.assoc flip: fps_of_nat sum_divide_distrib)
  also have "\<dots> = of_nat m / fact n * (euler_poly n (of_nat m * x) + 
                    2 * of_nat m ^ n / of_nat (Suc n) * 
                    (\<Sum>k<m. (-1) ^ k * bernpoly (Suc n) (x + of_nat k / of_nat m)))"
    by (simp add: algebra_simps)
  finally show ?thesis
    using m by (simp add: add_eq_0_iff)
qed

text \<open>
  The Euler polynomials can be written as the difference of two Bernoulli polynomials.
\<close>
corollary euler_poly_conv_bernpoly:
  fixes x :: "'a :: {real_normed_field, field_char_0}"
  assumes m: "even m" "m > 0"
  shows "euler_poly n x = 
           2 / of_nat (Suc n) * (bernpoly (Suc n) x - 2 ^ Suc n * bernpoly (Suc n) (x / 2))"
proof -
  have "euler_poly n x = -(2^Suc n * (bernpoly (Suc n) (x / 2) - 
          bernpoly (Suc n) (x / 2 + 1 / 2)) / of_nat (Suc n))"
    using euler_poly_mult_even[of 2 n "x/2"]
    by (simp add: numeral_2_eq_2)
  also have "\<dots> = 2 / of_nat (Suc n) * (2^n * bernpoly (Suc n) (x/2 + 1/2) - 2^n * bernpoly (Suc n) (x/2))"
    by (simp del: of_nat_Suc add: field_simps)
  also have "2^n * bernpoly (Suc n) (x/2 + 1/2) - 2^n * bernpoly (Suc n) (x/2) = 
             bernpoly (Suc n) x - 2 ^ Suc n * bernpoly (Suc n) (x / 2)"
    using bernpoly_mult[of 2 "Suc n" "x/2"]
    by (simp add: numeral_2_eq_2 ring_distribs)
  finally show ?thesis .
qed


subsection \<open>Computing Bernoulli polynomials\<close>
(* TODO: move this section to Bernoulli *)

definition binomial_row :: "nat \<Rightarrow> 'a :: semiring_1 list" where
  "binomial_row n = map (\<lambda>k. of_nat (n choose k)) [0..<Suc n]"

lemma length_binomial_row [simp]: "length (binomial_row n) = Suc n"
  by (simp add: binomial_row_def del: upt_Suc)

lemma nth_binomial_row [simp]: "k \<le> n \<Longrightarrow> binomial_row n ! k = of_nat (n choose k)"
  by (simp add: binomial_row_def del: upt_Suc)

definition pascal_step :: "'a :: semiring_1 list \<Rightarrow> 'a list" where
  "pascal_step xs = map2 (+) (xs @ [0]) (0 # xs)"

lemma pascal_step_correct [simp]:
  "pascal_step (binomial_row n) = binomial_row (Suc n)"
  by (rule nth_equalityI)
     (auto simp: pascal_step_def binomial_row_def nth_Cons nth_append add.commute
                 not_less less_Suc_eq binomial_eq_0
           simp del: upt_Suc split: nat.splits)


primrec Bernpolys_aux :: "nat list \<Rightarrow> 'a :: {field_char_0, real_normed_field} poly list \<Rightarrow> nat \<Rightarrow> 'a poly list" where
  "Bernpolys_aux cs xs 0 = xs"
| "Bernpolys_aux cs xs (Suc k) =
     (let n = length xs;
          p = Polynomial.monom 1 n - Polynomial.smult (1 / of_nat (Suc n))
                (\<Sum>(p,c)\<leftarrow>zip xs (drop 2 cs). Polynomial.smult (of_nat c) p)
      in Bernpolys_aux (pascal_step cs) (p # xs) k)"

lemma length_Bernpolys_aux [simp]: "length (Bernpolys_aux cs xs n) = length xs + n"
  by (induction n arbitrary: xs cs) (simp_all add: Let_def)

lemma Bernpolys_aux_correct:
  "Bernpolys_aux (binomial_row (Suc n)) (map Bernpoly (rev [0..<n])) m = map Bernpoly (rev [0..<m+n])"
proof (induction m arbitrary: n)
  case (Suc m n)
  define xs :: "'a poly list" where "xs = map Bernpoly (rev [0..<n])"
  define cs :: "nat list" where "cs = binomial_row (Suc n)"
  define S where "S = (\<Sum>(p,c)\<leftarrow>zip xs (drop 2 cs). Polynomial.smult (of_nat c) p)"
  define q where "q = Polynomial.monom 1 n - Polynomial.smult (1 / of_nat (Suc n)) S"
  have [simp]: "length xs = n"
    by (simp add: xs_def)

  have "Bernpolys_aux cs (map Bernpoly (rev [0..<n]) :: 'a poly list) (Suc m) = 
          Bernpolys_aux (binomial_row (Suc (Suc n))) (q # xs) m"
    by (simp del: upt_Suc add: q_def S_def xs_def cs_def)
  also have "q # xs = map Bernpoly (rev [0..<Suc n])"
  proof -
    have "q = Polynomial.monom 1 n - Polynomial.smult (1 / of_nat (Suc n)) S"
      by (simp add: q_def)
    also have "S = (\<Sum>s<n. Polynomial.smult (of_nat (Suc n choose (s+2))) (xs ! s))"
      unfolding S_def
      by (subst sum.list_conv_set_nth) (simp_all add: atLeast0LessThan cs_def del: upt_Suc)
    also have "\<dots> = (\<Sum>s<n. Polynomial.smult (of_nat (Suc n choose (s+2))) (Bernpoly (n - Suc s)))"
      by (intro sum.cong) (auto simp: xs_def rev_nth)
    also have "\<dots> = (\<Sum>s<n. Polynomial.smult (of_nat (Suc n choose (Suc n - s))) (Bernpoly s))"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>s. n - Suc s" "\<lambda>s. n - Suc s"])
         (auto simp del: binomial_Suc_Suc)
    also have "\<dots> = (\<Sum>s<n. Polynomial.smult (of_nat (Suc n choose s)) (Bernpoly s))"
      by (intro sum.cong refl, subst binomial_symmetric) (auto simp del: binomial_Suc_Suc)
    also have "Polynomial.monom 1 n - Polynomial.smult (1 / of_nat (Suc n)) \<dots> = Bernpoly n"
      using Bernpoly_recurrence' [symmetric, of n] by simp
    finally show ?thesis
      by (simp add: xs_def)
  qed
  also have "Bernpolys_aux (binomial_row (Suc (Suc n))) \<dots> m = map Bernpoly (rev [0..<m + Suc n])"
    by (rule Suc.IH)
  finally show ?case
    by (simp del: upt_Suc add: cs_def)
qed auto

text \<open>
  The following function recursively computes a list of the Bernoulli polynomials 
  $B_0, \ldots, B_{n-1}$.
\<close>
definition Bernpolys :: "nat \<Rightarrow> 'a :: {field_char_0, real_normed_field} poly list" 
  where "Bernpolys n = rev (Bernpolys_aux [1, 1] [] n)"

lemma length_Bernpolys [simp]: "length (Bernpolys n) = n"
  by (simp add: Bernpolys_def)

lemma Bernpolys_correct: "Bernpolys n = map Bernpoly [0..<n]"
  using Bernpolys_aux_correct[of 0 n, where ?'a = 'a]
  by (simp add: Bernpolys_def rev_swap binomial_row_def flip: rev_map)

lemma Bernpoly_code [code]: "Bernpoly n = hd (Bernpolys_aux [1, 1] [] (Suc n))"
  using Bernpolys_aux_correct[of 0 "Suc n", where ?'a = 'a]
  by (simp flip: rev_map add: hd_rev last_map binomial_row_def del: Bernpolys_aux.simps)


primrec bernpoly_aux :: "nat list \<Rightarrow> 'a :: {field_char_0, real_normed_field} list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "bernpoly_aux cs ys 0 x = ys"
| "bernpoly_aux cs ys (Suc k) x =
     (let n = length ys;
          y = x ^ n - (\<Sum>(y,c)\<leftarrow>zip ys (drop 2 cs). of_nat c * y) / of_nat (Suc n)
      in bernpoly_aux (pascal_step cs) (y # ys) k x)"

lemma length_bernpoly_aux [simp]: "length (bernpoly_aux cs xs n x) = length xs + n"
  by (induction n arbitrary: xs cs) (simp_all add: Let_def)

lemma bernpoly_aux_correct:
  "bernpoly_aux cs (map (\<lambda>p. poly p x) ps) n x = 
     map (\<lambda>p. poly p x) (Bernpolys_aux cs ps n)"
  by (rule sym, induction n arbitrary: ps cs)
     (simp_all add: Let_def poly_sum_list poly_monom o_def case_prod_unfold zip_map1
               del: upt_Suc of_nat_Suc)

lemma bernpoly_code [code]:
  "bernpoly n x = hd (bernpoly_aux [1, 1] [] (Suc n) x)"
proof -
  have "length (Bernpolys_aux [1, 1] ([] :: 'a poly list) (Suc n)) \<noteq> 0"
    by (subst length_Bernpolys_aux) auto
  hence "Bernpolys_aux [1, 1] ([] :: 'a poly list) (Suc n) \<noteq> []"
    by (subst (asm) length_0_conv)
  thus ?thesis
    unfolding poly_Bernpoly [symmetric] Bernpoly_code
    using bernpoly_aux_correct[of "[1, 1]" x "[]" "Suc n"]
    by (simp add: hd_map del: Bernpolys_aux.simps bernpoly_aux.simps)
qed


subsection \<open>Computing Euler polynomials\<close>

primrec Euler_polys_aux :: "nat list \<Rightarrow> 'a :: field_char_0 poly list \<Rightarrow> nat \<Rightarrow> 'a poly list" where
  "Euler_polys_aux cs xs 0 = xs"
| "Euler_polys_aux cs xs (Suc k) =
     (let n = length xs;
          p = Polynomial.monom 1 n - Polynomial.smult (1/2)
                (\<Sum>(p,c)\<leftarrow>zip xs (tl cs). Polynomial.smult (of_nat c) p)
      in Euler_polys_aux (pascal_step cs) (p # xs) k)"

lemma length_Euler_polys_aux [simp]: "length (Euler_polys_aux cs xs n) = length xs + n"
  by (induction n arbitrary: xs cs) (simp_all add: Let_def)

lemma Euler_polys_aux_correct:
  "Euler_polys_aux (binomial_row n) (map Euler_poly (rev [0..<n])) m = map Euler_poly (rev [0..<m+n])"
proof (induction m arbitrary: n)
  case (Suc m n)
  define xs :: "'a poly list" where "xs = map Euler_poly (rev [0..<n])"
  define S where "S = (\<Sum>(p,c)\<leftarrow>zip xs (tl (binomial_row n)). Polynomial.smult (of_nat c) p)"
  define q where "q = Polynomial.monom 1 n - Polynomial.smult (1/2) S"
  have [simp]: "length xs = n"
    by (simp add: xs_def)

  have "Euler_polys_aux (binomial_row n) (map Euler_poly (rev [0..<n]) :: 'a poly list) (Suc m) = 
          Euler_polys_aux (binomial_row (Suc n)) (q # xs) m"
    by (simp del: upt_Suc add: q_def S_def xs_def)
  also have "q # xs = map Euler_poly (rev [0..<Suc n])"
  proof -
    have "q = Polynomial.monom 1 n - Polynomial.smult (1/2) S"
      by (simp add: q_def)
    also have "S = (\<Sum>s<n. Polynomial.smult (of_nat (n choose Suc s)) (xs ! s))" unfolding S_def
      by (subst sum.list_conv_set_nth) (simp_all add: atLeast0LessThan nth_tl del: upt_Suc)
    also have "\<dots> = (\<Sum>s<n. Polynomial.smult (of_nat (n choose Suc s)) (Euler_poly (n - Suc s)))"
      by (intro sum.cong) (auto simp: xs_def rev_nth)
    also have "\<dots> = (\<Sum>s<n. Polynomial.smult (of_nat (n choose (n - s))) (Euler_poly s))"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>s. n - Suc s" "\<lambda>s. n - Suc s"]) auto
    also have "\<dots> = (\<Sum>s<n. Polynomial.smult (of_nat (n choose s)) (Euler_poly s))"
      by (intro sum.cong refl, subst binomial_symmetric) auto
    also have "Polynomial.monom 1 n - Polynomial.smult (1/2) \<dots> = Euler_poly n"
      by (rule Euler_poly_recurrence [symmetric])
    finally show ?thesis
      by (simp add: xs_def)
  qed
  also have "Euler_polys_aux (binomial_row (Suc n)) \<dots> m = map Euler_poly (rev [0..<m + Suc n])"
    by (rule Suc.IH)
  finally show ?case 
    by (simp del: upt_Suc)
qed auto

text \<open>
  The following function recursively computes a list of the Euler polynomials 
  $E_0, \ldots, E_{n-1}$.
\<close>
definition Euler_polys :: "nat \<Rightarrow> 'a :: field_char_0 poly list" 
  where "Euler_polys n = rev (Euler_polys_aux [1] [] n)"

lemma length_Euler_polys [simp]: "length (Euler_polys n) = n"
  by (simp add: Euler_polys_def)

lemma Euler_polys_correct: "Euler_polys n = map Euler_poly [0..<n]"
  using Euler_polys_aux_correct[of 0 n, where ?'a = 'a]
  by (simp add: Euler_polys_def rev_swap binomial_row_def flip: rev_map)

lemma Euler_poly_code [code]: "Euler_poly n = hd (Euler_polys_aux [1] [] (Suc n))"
  using Euler_polys_aux_correct[of 0 "Suc n", where ?'a = 'a]
  by (simp flip: rev_map add: hd_rev last_map binomial_row_def del: Euler_polys_aux.simps)


primrec euler_poly_aux :: "nat list \<Rightarrow> 'a :: {field_char_0, real_normed_field} list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "euler_poly_aux cs ys 0 x = ys"
| "euler_poly_aux cs ys (Suc k) x =
     (let n = length ys;
          y = x ^ n - (\<Sum>(y,c)\<leftarrow>zip ys (tl cs). of_nat c * y) / 2
      in euler_poly_aux (pascal_step cs) (y # ys) k x)"

lemma length_euler_poly_aux [simp]: "length (euler_poly_aux cs xs n x) = length xs + n"
  by (induction n arbitrary: xs cs) (simp_all add: Let_def)

lemma euler_poly_aux_correct:
  "euler_poly_aux cs (map (\<lambda>p. poly p x) ps) n x = map (\<lambda>p. poly p x) (Euler_polys_aux cs ps n)"
  by (rule sym, induction n arbitrary: ps cs)
     (simp_all add: Let_def poly_sum_list poly_monom o_def case_prod_unfold zip_map1
               del: upt_Suc of_nat_Suc)

lemma euler_poly_code [code]:
  "euler_poly n x = hd (euler_poly_aux [1] [] (Suc n) x)"
proof -
  have "length (Euler_polys_aux [1] ([] :: 'a poly list) (Suc n)) \<noteq> 0"
    by (subst length_Euler_polys_aux) auto
  hence "Euler_polys_aux [1] ([] :: 'a poly list) (Suc n) \<noteq> []"
    by (subst (asm) length_0_conv)
  thus ?thesis
    unfolding poly_Euler_poly [symmetric] Euler_poly_code
    using euler_poly_aux_correct[of "[1]" x "[]" "Suc n"]
    by (simp add: hd_map del: Euler_polys_aux.simps euler_poly_aux.simps)
qed

end