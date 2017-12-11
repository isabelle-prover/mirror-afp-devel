(*
    File:      More_Totient.thy
    Author:    Manuel Eberl, TU München
    
    Additional properties of Euler's totient function
*)
section \<open>Euler's $\phi$ function\<close>
theory More_Totient
  imports
    Moebius_Mu
    "HOL-Number_Theory.Number_Theory"
begin
  
lemma fds_totient_times_zeta: 
  "fds (\<lambda>n. of_nat (totient n) :: 'a :: comm_semiring_1) * fds_zeta = fds of_nat"
proof
  fix n :: nat assume n: "n > 0"
  have "fds_nth (fds (\<lambda>n. of_nat (totient n)) * fds_zeta) n = 
          dirichlet_prod (\<lambda>n. of_nat (totient n)) (\<lambda>_. 1) n"
    by (simp add: fds_nth_mult)
  also from n have "\<dots> = fds_nth (fds of_nat) n"
    by (simp add: fds_nth_fds dirichlet_prod_def totient_divisor_sum of_nat_sum [symmetric]
             del: of_nat_sum)
  finally show "fds_nth (fds (\<lambda>n. of_nat (totient n)) * fds_zeta) n = fds_nth (fds of_nat) n" .
qed

lemma fds_totient_times_zeta': "fds totient * fds_zeta = fds id"
  using fds_totient_times_zeta[where 'a = nat] by simp
  
lemma fds_totient: "fds (\<lambda>n. of_nat (totient n)) = fds of_nat * fds moebius_mu"
proof -
  have "fds (\<lambda>n. of_nat (totient n)) * fds_zeta * fds moebius_mu = fds of_nat * fds moebius_mu"
    by (simp add: fds_totient_times_zeta)
  also have "fds (\<lambda>n. of_nat (totient n)) * fds_zeta * fds moebius_mu = 
               fds (\<lambda>n. of_nat (totient n))"
    by (simp only: mult.assoc fds_zeta_times_moebius_mu mult_1_right)
  finally show ?thesis .
qed

lemma totient_conv_moebius_mu:
  "int (totient n) = dirichlet_prod moebius_mu int n"
proof (cases "n = 0")
  case False
  show ?thesis
    by (rule moebius_inversion)
       (insert False, simp_all add: of_nat_sum [symmetric] totient_divisor_sum del: of_nat_sum)
qed simp_all

interpretation totient: multiplicative_function totient
proof -
  have "multiplicative_function int" by standard simp_all
  hence "multiplicative_function (dirichlet_prod moebius_mu int)"
    by (intro multiplicative_dirichlet_prod moebius_mu.multiplicative_function_axioms)
  also have "dirichlet_prod moebius_mu int = (\<lambda>n. int (totient n))" 
    by (simp add: fun_eq_iff totient_conv_moebius_mu)
  finally show "multiplicative_function totient" by (rule multiplicative_function_of_natD)
qed

lemma totient_conv_moebius_mu':
  assumes "n > (0::nat)"
  shows   "real (totient n) = real n * (\<Sum>d | d dvd n. moebius_mu d / real d)"
proof -
  have "real (totient n) = of_int (int (totient n))" by simp
  also have "int (totient n) = (\<Sum>d | d dvd n. moebius_mu d * int (n div d))"
    using totient_conv_moebius_mu by (simp add: dirichlet_prod_def assms)
  also have "real_of_int (\<Sum>d | d dvd n. moebius_mu d * int (n div d)) =
               (\<Sum>d | d dvd n. moebius_mu d * real (n div d))" by simp
  also have "\<dots> = (\<Sum>d | d dvd n. real n * moebius_mu d / real d)"
    by (rule sum.cong) (simp_all add: field_char_0_class.of_nat_div)
  also have "\<dots> = real n * (\<Sum>d | d dvd n. moebius_mu d / real d)"
    by (simp add: sum_distrib_left)
  finally show ?thesis .
qed

lemma totient_prime_power_Suc:
  assumes "prime p"
  shows   "totient (p ^ Suc n) = p ^ Suc n - p ^ n"
proof -
  have "totient (p ^ Suc n) = p ^ Suc n - card (op * p ` {0<..p ^ n})"
    unfolding totient_def totatives_prime_power_Suc[OF assms]
    by (subst card_Diff_subset) (insert assms, auto simp: prime_gt_0_nat)
  also from assms have "card (op * p ` {0<..p^n}) = p ^ n"
    by (subst card_image) (auto simp: inj_on_def)
  finally show ?thesis .
qed

interpretation totient: multiplicative_function' totient "\<lambda>p k. p ^ k - p ^ (k - 1)" "\<lambda>p. p - 1"
proof
  fix p k :: nat assume "prime p" "k > 0"
  thus "totient (p ^ k) = p ^ k - p ^ (k - 1)" 
    by (cases k) (simp_all add: totient_prime_power_Suc del: power_Suc)
qed simp_all

end
