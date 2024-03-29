(*
  File:     Kummers_Congruence/Irregular_Primes_Infinite.thy
  Author:   Manuel Eberl, University of Innsbruck

  Proof of the infinitude of irregular primes
*)
section \<open>Infinitude of irregular primes\<close>
theory Irregular_Primes_Infinite
  imports Regular_Primes
begin

text \<open>
  One consequence of Kummer's congruence is that there are infinitely many irregular primes.
  We shall derive this here.
\<close>

(* TODO Move *)
lemma zeta_real_gt_1:
  assumes "x > 1"
  shows   "Re (zeta (of_real x)) > 1"
proof -
  have *: "(\<lambda>n. Re (complex_of_nat (Suc n) powr -of_real x)) sums (Re (zeta x))"
    using assms by (intro sums_Re sums_zeta) auto
  have **: "(Re (zeta x) - (1 + Re (2 powr -of_real x))) \<ge> 0"
  proof (rule sums_le)
    show "(\<lambda>n. Re (complex_of_nat (n+3) powr -of_real x)) sums (Re (zeta x) - (1 + Re (2 powr -of_real x)))"
      using sums_split_initial_segment[OF *, of 2] by (simp add: eval_nat_numeral)
    show "(\<lambda>_. 0) sums (0 :: real)"
      by simp
  next
    fix n :: nat
    have "complex_of_nat (n + 3) powr -complex_of_real x = of_real (real (n + 3) powr -x)"
      by (subst powr_of_real [symmetric]) auto
    also have "Re \<dots> = real (n + 3) powr -x"
      by simp
    also have "\<dots> \<ge> 0"
      by simp
    finally show "Re (complex_of_nat (n + 3) powr -complex_of_real x) \<ge> 0" .
  qed

  have "0 < Re (of_real (2 powr -x))"
    by simp
  also have "complex_of_real (2 powr -x) = 2 powr -complex_of_real x"
    by (subst powr_of_real [symmetric]) auto
  also have "Re (2 powr -of_real x) \<le> Re (zeta x) - 1"
    using ** by simp
  finally show ?thesis
    by linarith
qed

lemma zeta_real_gt_1':
  assumes "Re s > 1" "s \<in> \<real>"
  shows   "Re (zeta s) > 1"
  using assms by (elim Reals_cases) (auto simp: zeta_real_gt_1)

lemma bernoulli_even_conv_zeta:
  "complex_of_real (bernoulli (2*n)) = (-1)^Suc n * 2 * fact (2*n) / (2*pi)^(2*n) * zeta (2 * of_nat n)"
  by (subst zeta_even_nat[of n]) (auto simp: field_simps)

lemma bernoulli_even_conv_zeta':
  "bernoulli (2*n) = (-1)^Suc n * 2 * fact (2*n) / (2*pi)^(2*n) * Re (zeta (2 * of_nat n))"
proof -
  have "complex_of_real (bernoulli (2*n)) = (-1)^Suc n * 2 * fact (2*n) / (2*pi)^(2*n) * zeta (2 * of_nat n)"
    by (rule bernoulli_even_conv_zeta)
  also have "\<dots> = of_real ((-1)^Suc n * 2 * fact (2*n) / (2*pi)^(2*n) * Re (zeta (2 * of_nat n)))"
    using zeta_real'[of "2 * of_nat n"] by simp
  finally show ?thesis
    by (subst (asm) of_real_eq_iff)
qed

lemma abs_bernoulli_even_conv_zeta:
  assumes "even n" "n > 0"
  shows   "\<bar>bernoulli n\<bar> = 2 * fact n / (2*pi)^n * Re (zeta (of_nat n))"
proof -
  from assms obtain k where n: "n = 2 * k"
    by (elim evenE)
  show ?thesis
    using zeta_real_gt_1'[of n] assms(2) unfolding n bernoulli_even_conv_zeta'
    by (simp add: abs_mult)
qed
(* END TODO *)

lemma abs_bernoulli_over_n_ge_2:
  assumes "n \<ge> 23" "even n"
  shows   "\<bar>bernoulli n / n\<bar> \<ge> 2"
proof -
  have "2 * real n \<le> 2 * real n * 1"
    by simp
  also have "\<dots> \<le> 2 * (fact n / (2*pi)^n) * Re (zeta n)"
    using fact_ge_2pi_power[OF assms(1)] assms(1)
    by (intro mult_left_mono mult_mono less_imp_le[OF zeta_real_gt_1']) (auto simp: field_simps)
  also have "\<dots> = abs (bernoulli n)"
    using assms by (subst abs_bernoulli_even_conv_zeta) auto
  finally show ?thesis
    using assms(1) by (simp add: field_simps)
qed

lemma infinite_irregular_primes_aux:
  assumes "finite P" "\<forall>p\<in>P. irregular_prime p" "37 \<in> P"
  shows   "\<exists>p. irregular_prime p \<and> p \<notin> P"
proof -
  define n where "n = (\<Prod>p\<in>P. p - 1)"
  have nz: "(\<Prod>p\<in>P. p - 1) \<noteq> 0"
    using assms by (subst prod_zero_iff) (auto simp: irregular_prime_def)
  define N where "N = bernoulli_num"
  define D where "D = bernoulli_denom"

  have "37 - 1 dvd (\<Prod>p\<in>P. p - 1)"
    by (rule dvd_prodI) (use assms in auto)
  hence "n \<ge> 36"
    unfolding n_def using nz by (intro dvd_imp_le) auto
  have "even n"
    unfolding n_def using assms by (auto simp: even_prod_iff intro!: bexI[of _ 37])
  have [simp]: "N n \<noteq> 0"
    using \<open>even n\<close> by (auto simp: N_def bernoulli_num_eq_0_iff)

  have "abs (bernoulli n / n) > 1"
  proof -
    have "1 < (2 :: real)"
      by simp
    also have "\<dots> \<le> abs (bernoulli n / n)"
      by (rule abs_bernoulli_over_n_ge_2) (use \<open>even n\<close> \<open>n \<ge> 36\<close> in auto)
    finally show ?thesis .
  qed

  obtain p where p: "prime p" "qmultiplicity (int p) (bernoulli_rat n / of_nat n) > 0"
  proof -
    obtain a b where ab: "quotient_of (bernoulli_rat n / of_nat n) = (a, b)"
      using prod.exhaust by blast
    have "b > 0"
      using ab quotient_of_denom_pos by blast
    have eq': "of_int a / of_int b = (bernoulli_rat n / of_nat n :: rat)"
      using ab quotient_of_div by simp
    also have "(of_rat \<dots> :: real) = bernoulli n / n"
      by (simp add: of_rat_divide bernoulli_rat_conv_bernoulli)
    finally have eq: "real_of_rat (rat_of_int a / rat_of_int b) = bernoulli n / real n" .

    have [simp]: "a \<noteq> 0"
      using eq \<open>abs (bernoulli n / n) > 1\<close> by auto
    moreover have "\<not>is_unit a "
    proof
      assume "is_unit a"
      hence "abs (bernoulli n / n) = 1 / of_int b"
        unfolding eq [symmetric] using \<open>b > 0\<close> by (simp add: of_rat_divide flip: of_int_abs)
      also have "\<dots> \<le> 1"
        using \<open>b > 0\<close> by simp
      finally show False
        using \<open>abs (bernoulli n / n) > 1\<close> by simp
    qed
    ultimately obtain p' where p': "prime p'" "p' dvd a"
      using prime_divisor_exists by blast
    define p where "p = nat p'"
    from p' have p: "prime p" "int p dvd a"
      unfolding p_def by (auto intro: prime_ge_0_int)

    show ?thesis
    proof (rule that[of p])
      from p have "multiplicity p a \<ge> 1"
        by (intro multiplicity_geI) auto
      moreover have "coprime a b"
        using ab quotient_of_coprime by auto
      hence "\<not>p dvd b"
        using ab p by (meson not_coprimeI not_prime_unit prime_nat_int_transfer)
      hence "multiplicity p b = 0"
        by (intro not_dvd_imp_multiplicity_0) auto
      ultimately show "qmultiplicity (int p) (bernoulli_rat n / of_nat n) > 0"
        using \<open>b > 0\<close> p unfolding eq'[symmetric] by (subst qmultiplicity_divide_of_int) auto
    qed fact+
  qed
  hence "qmultiplicity p (of_int (N n) / of_int (int (D n * n))) > 0"
    by (simp add: N_def D_def bernoulli_rat_def)
  hence "multiplicity (int p) (N n) > 0"
    unfolding bernoulli_rat_def using p
    by (subst (asm) qmultiplicity_divide_of_int)
       (use \<open>n \<ge> 36\<close> \<open>even n\<close> in \<open>simp_all add: N_def D_def bernoulli_num_eq_0_iff\<close>)
  hence "p dvd N n"
    using not_dvd_imp_multiplicity_0 by fastforce
    
  have "\<not>(p - 1) dvd n"
  proof
    assume "(p - 1) dvd n"
    hence "p dvd D n"
      using p(1) \<open>even n\<close> \<open>n \<ge> 36\<close> unfolding D_def by (subst prime_dvd_bernoulli_denom_iff) auto
    hence "\<not>p dvd N n" unfolding N_def D_def
      using coprime_bernoulli_num_denom[of n] p(1)
      by (metis coprime_def int_dvd_int_iff not_prime_unit of_nat_1)
    with \<open>p dvd N n\<close> show False
      by contradiction
  qed
  hence "p \<notin> P" "p \<noteq> 2"
    unfolding n_def using assms by auto
  hence "p > 2"
    using prime_gt_1_nat[OF \<open>prime p\<close>] by linarith
  hence "odd p"
    using prime_odd_nat[of p] \<open>prime p\<close> by auto

  define r where "r = n mod (p - 1)"
  have "even (n - n div (p - 1) * (p - 1))"
    using \<open>p > 2\<close> \<open>odd p\<close> \<open>even n\<close> by (subst even_diff_nat) auto
  also have "\<dots> = r"
    unfolding r_def by (rule minus_div_mult_eq_mod)
  finally have "even r" .

  have "irregular_prime p"
  proof (rule irregular_primeI)
    have "r > 0" "r < p - 1"
      using p prime_gt_1_nat[of p] \<open>\<not>(p - 1) dvd n\<close>
      unfolding r_def by (auto intro!: pos_mod_bound Nat.gr0I)
    moreover from \<open>even r\<close> and \<open>prime p\<close> have "r \<noteq> 1" "r \<noteq> p - 2"
      using \<open>odd p\<close> \<open>p > 2\<close> by auto
    ultimately have "r \<ge> 2" "r \<le> p - 3"
      by linarith+
    thus "r \<in> {2..p-3}"
      by auto

    have "bernoulli_rat r / of_nat r = (0 :: rat) \<or> 
            qmultiplicity p (bernoulli_rat r / of_nat r) > 0"
    proof (rule qcong_qmultiplicity_pos_transfer)
      show "qmultiplicity p (bernoulli_rat n / of_nat n) > 0"
        using p by simp
    next
      have "[n = r] (mod (p - 1))"
        by (auto simp: Cong.cong_def r_def)
      thus "[bernoulli_rat n / of_nat n = bernoulli_rat r / of_nat r] (qmod p)"
        using p(1) \<open>even n\<close> \<open>even r\<close> \<open>n \<ge> _\<close> \<open>r > 0\<close> \<open>\<not>(p-1) dvd n\<close> unfolding D_def N_def
        by (intro kummer_congruence'_prime) auto
    qed
    moreover have "bernoulli_rat r / of_nat r \<noteq> (0 :: rat)"
      using \<open>even r\<close> \<open>r > 0\<close> by (auto simp: bernoulli_rat_eq_0_iff)
    ultimately have "qmultiplicity p (bernoulli_rat r / of_nat r) > 0"
      by simp
    hence "qmultiplicity p (of_int (N r) / of_int (int (D r * r))) > 0"
      by (simp add: bernoulli_rat_def N_def D_def)
    hence "multiplicity (int p) (N r) > 0"
      by (subst (asm) qmultiplicity_divide_of_int)
         (use \<open>r > 0\<close> \<open>even r\<close> \<open>prime p\<close> in \<open>simp_all add: N_def D_def bernoulli_num_eq_0_iff\<close>)
    hence "p dvd N r"
      using not_dvd_imp_multiplicity_0 by fastforce
    thus "p dvd bernoulli_num r"
      by (simp add: N_def)
  qed (use p \<open>p \<noteq> 2\<close> \<open>even r\<close> in auto)
  with \<open>p \<notin> P\<close> show ?thesis
    by blast
qed

theorem infinite_irregular_primes: "infinite {p. irregular_prime p}"
proof
  assume "finite {p. irregular_prime p}"
  hence "\<exists>p. irregular_prime p \<and> p \<notin> {p. irregular_prime p}"
    by (rule infinite_irregular_primes_aux) (use irregular_prime_37 in auto)
  thus False
    by simp
qed

end