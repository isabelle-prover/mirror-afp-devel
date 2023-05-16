(*  Title:      Three_Squares/Residues_Properties.thy
    Author:     Anton Danilkin
*)

section \<open>Properties of residues, congruences,
         quadratic residues and the Legendre symbol\<close>

theory Residues_Properties
  imports "HOL-Number_Theory.Quadratic_Reciprocity"
begin

subsection \<open>Properties of residues and congruences\<close>

lemma mod_diff_eq_nat:
  fixes a b m :: nat
  assumes "a \<ge> b"
  shows "(a - b) mod m = (m + (a mod m) - (b mod m)) mod m"
proof cases
  assume "m = 0"
  thus ?thesis by auto
next
  assume 0: "m \<noteq> 0"
  have "(a - b) mod m = nat (int (a - b) mod int m)"
    unfolding nat_mod_as_int by blast
  also have "... = nat ((int a - int b) mod int m)"
    using assms by (simp add: of_nat_diff)
  also have "... = nat ((int a mod int m - int b mod int m) mod int m)"
    using mod_diff_eq by metis
  also have "... = nat ((int a mod int m + (int m - int b mod int m)) mod int m)"
    by (metis add.left_commute add_uminus_conv_diff mod_add_self1)
  also have "... = nat ((int (nat (int a mod int m)) +
                         (int m - int b mod int m)) mod int m)"
    by (metis nat_int of_nat_mod)
  also have "... = nat ((int (nat (int a mod int m)) +
                         int (m - nat (int b mod int m))) mod int m)"
    by (metis 0 less_eq_nat.simps(1) mod_less_divisor
              nat_int nat_less_le of_nat_diff zmod_int)
  also have "... = nat (int (m + nat (int a mod int m) -
                             nat (int b mod int m)) mod int m)"
    by (metis 0 Nat.add_diff_assoc add.commute bot_nat_0.not_eq_extremum
              mod_less_divisor nat_less_le nat_mod_as_int of_nat_add)
  also have "... = (m + (a mod m) - (b mod m)) mod m"
    unfolding nat_mod_as_int by blast
  finally show ?thesis .
qed

lemma prime_invertible_int:
  fixes a p :: int
  assumes "prime p"
  assumes "\<not> p dvd a"
  shows "\<exists>b. [a * b = 1] (mod p)"
  using assms coprime_commute coprime_iff_invertible_int prime_imp_coprime by blast

lemma power_cong:
  fixes x y a m :: nat
  assumes "coprime a m"
  assumes "[x = y] (mod totient m)"
  shows "[a ^ x = a ^ y] (mod m)"
proof -
  obtain k :: int where 0: "x + totient m * k = y"
    using assms by (metis cong_iff_lin cong_int_iff)
  show ?thesis
  proof cases
    assume "k \<ge> 0"
    hence "x + totient m * nat k = y"
      using 0 by (metis int_eq_iff nat_int_add of_nat_mult)
    hence "[a ^ x * (a ^ totient m) ^ nat k = a ^ y] (mod m)"
      unfolding cong_def by (metis power_add power_mult)
    hence "[a ^ x * (a ^ totient m mod m) ^ nat k = a ^ y] (mod m)"
      unfolding cong_def by (metis mod_mult_right_eq power_mod)
    hence "[a ^ x * (1 mod m) ^ nat k = a ^ y] (mod m)"
      using euler_theorem[OF assms(1)] unfolding cong_def by argo
    hence "[a ^ x * 1 ^ nat k = a ^ y] (mod m)"
      unfolding cong_def by (metis mod_mult_right_eq power_mod)
    thus "[a ^ x = a ^ y] (mod m)" by auto
  next
    assume "\<not> k \<ge> 0"
    hence "x = y + totient m * nat (- k)"
      using 0
      by (smt (verit) int_nat_eq nat_int nat_minus_as_int of_nat_add of_nat_mult
                      right_diff_distrib')
    hence "[a ^ x = a ^ y * (a ^ totient m) ^ nat (- k)] (mod m)"
      unfolding cong_def by (metis power_add power_mult)
    hence "[a ^ x = a ^ y * (a ^ totient m mod m) ^ nat (- k)] (mod m)"
      unfolding cong_def by (metis mod_mult_right_eq power_mod)
    hence "[a ^ x = a ^ y * (1 mod m) ^ nat (- k)] (mod m)"
      using euler_theorem[OF assms(1)] unfolding cong_def by argo
    hence "[a ^ x = a ^ y * 1 ^ nat (- k)] (mod m)"
      unfolding cong_def by (metis mod_mult_right_eq power_mod)
    thus "[a ^ x = a ^ y] (mod m)" by auto
  qed
qed

lemma power_cong_alt:
  fixes x a m :: nat
  assumes "coprime a m"
  shows "a ^ x mod m = a ^ (x mod totient m) mod m"
  using power_cong[OF assms] cong_def cong_mod_left by blast

subsection \<open>Properties of quadratic residues\<close>

lemma QuadRes_cong:
  fixes a b p :: int
  assumes "[a = b] (mod p)"
  assumes "QuadRes p a"
  shows "QuadRes p b"
  using assms cong_trans unfolding QuadRes_def by blast

lemma QuadRes_mult:
  fixes a b p :: int
  assumes "QuadRes p a"
  assumes "QuadRes p b"
  shows "QuadRes p (a * b)"
  using assms
  unfolding QuadRes_def
  by (metis cong_mult mult.assoc mult.commute power2_eq_square)

lemma QuadRes_inv:
  fixes a b p :: int
  assumes "prime p"
  assumes "[a * b = 1] (mod p)"
  assumes "QuadRes p a"
  shows "QuadRes p b"
proof -
  have 0: "\<not> p dvd a"
    using assms
    by (metis cong_dvd_iff dvd_mult2 not_prime_unit)
  obtain x where 1: "[x\<^sup>2 = a] (mod p)" using assms unfolding QuadRes_def by blast
  have "\<not> p dvd x" using 0 1 assms cong_dvd_iff pos2 prime_dvd_power_iff by blast
  then obtain y where "[x * y = 1] (mod p)"
    using assms prime_invertible_int by blast
  hence 2: "[(x * y)\<^sup>2 = 1] (mod p)" using cong_pow by fastforce
  have "[x\<^sup>2 * b = 1] (mod p)" using 1 assms cong_scalar_right cong_trans by blast
  hence "[y\<^sup>2 * (x\<^sup>2 * b) = y\<^sup>2 * 1] (mod p)" using cong_scalar_left by blast
  hence "[(x * y)\<^sup>2 * b = y\<^sup>2] (mod p)" by (simp add: algebra_simps)
  hence "[b = y\<^sup>2] (mod p)"
    using 2
    by (metis cong_def cong_scalar_left mult.commute mult.right_neutral)
  hence "[y\<^sup>2 = b] (mod p)" by (rule cong_sym)
  thus ?thesis unfolding QuadRes_def by blast
qed

subsection \<open>Properties of the Legendre symbol\<close>

lemma Legendre_cong:
  fixes a b p :: int
  assumes "[a = b] (mod p)"
  shows "Legendre a p = Legendre b p"
  using assms QuadRes_cong[of a b p] QuadRes_cong[of b a p]
  unfolding Legendre_def cong_def
  by auto

lemma Legendre_one:
  fixes p :: int
  assumes "p > 2"
  shows "Legendre 1 p = 1"
  using assms
  by (smt (verit) Legendre_def QuadRes_def cong_def
                  cong_less_imp_eq_int one_power2)

lemma Legendre_minus_one:
  fixes p :: int
  assumes "prime p"
  assumes "p > 2"
  shows "Legendre (- 1) p = 1 \<longleftrightarrow> [p = 1] (mod 4)"
proof -
  have "Legendre (- 1) p = 1 \<longleftrightarrow> [Legendre (- 1) p = 1] (mod p)"
    using assms
    by (metis Legendre_def QuadRes_def cong_0_iff cong_def not_prime_unit
              one_power2)
  also have "... \<longleftrightarrow> [(- 1) ^ ((nat p - 1) div 2) = 1] (mod p)"
    using assms euler_criterion[of "nat p" "- 1"]
    by (smt (verit) cong_def nat_0_le nat_one_as_int of_nat_add one_add_one
                    prime_int_nat_transfer zless_nat_eq_int_zless)
  also have "... \<longleftrightarrow> ((- 1 :: int) ^ ((nat p - 1) div 2)) = 1"
    using assms
    by (simp add: cong_iff_dvd_diff minus_one_power_iff zdvd_not_zless)
  also have "... \<longleftrightarrow> even ((nat p - 1) div 2)" by (simp add: minus_one_power_iff)
  also have "... \<longleftrightarrow> 4 dvd (nat p - 1)"
    using assms
    by (metis One_nat_def add_Suc_right div_dvd_div even_Suc even_diff_nat
              even_numeral even_of_nat group_cancel.rule0 nat_0_le
              numeral_Bit0_div_2 prime_int_nat_transfer prime_odd_int)
  also have "... \<longleftrightarrow> [p = 1] (mod 4)"
    using assms
    unfolding cong_iff_dvd_diff int_dvd_int_iff[symmetric]
    by (simp add: int_ops)
  finally show ?thesis .
qed

lemma Legendre_minus_one_alt:
  fixes p :: int
  assumes "prime p"
  assumes "p > 2"
  shows "Legendre (- 1) p = (if [p = 1] (mod 4) then 1 else - 1)"
  using assms Legendre_minus_one[OF assms]
  unfolding Legendre_def cong_def
  by (auto simp add: zmod_minus1)

lemma Legendre_two:
  fixes p :: int
  assumes "prime p"
  assumes "p > 2"
  shows "Legendre 2 p = 1 \<longleftrightarrow> [p = 1] (mod 8) \<or> [p = 7] (mod 8)"
proof -
  let ?n = "(p - 1) div 2 - (p - 1) div 4"
  have "odd p" using assms prime_odd_int by blast
  hence 0: "(\<exists>k. p = 8 * k + 1) \<or> (\<exists>k. p = 8 * k + 3) \<or>
            (\<exists>k. p = 8 * k + 5) \<or> (\<exists>k. p = 8 * k + 7)"
    by presburger
  have 1: "(j + 8 * k) div 4 = j div 4 + 2 * k" for k j :: int by linarith
  have 2: "GAUSS (nat p) 2"
    using assms unfolding GAUSS_def cong_def by auto
  have "Legendre 2 p = (- 1) ^ card (GAUSS.E (nat p) 2)"
    using assms GAUSS.gauss_lemma[OF 2] by auto
  also have "... = (- 1) ^ card
      ((\<lambda>k. k mod p) ` (*) 2 ` {0<..(p - 1) div 2} \<inter> {(p - 1) div 2<..})"
    unfolding GAUSS.E_def[OF 2] GAUSS.C_def[OF 2]
              GAUSS.B_def[OF 2] GAUSS.A_def[OF 2]
    by (simp add: algebra_simps)
  also have "... = (- 1) ^ card
      ((*) 2 ` {0<..(p - 1) div 2} \<inter> {(p - 1) div 2<..})"
    by (rule arg_cong[of _ _ "\<lambda>A. (- 1) ^ card (A \<inter> {(p - 1) div 2<..})"]; force)
  also have "... = (- 1) ^ card
      {k \<in> (*) 2 ` {0<..(p - 1) div 2}. k > (p - 1) div 2}"
    by (rule arg_cong[of _ _ "\<lambda>A. (- 1) ^ card A"]; blast)
  also have "... = (- 1) ^ card {k \<in> {0<..(p - 1) div 2}. 2 * k > (p - 1) div 2}"
    apply (rule arg_cong[of _ _ "\<lambda>n. (- 1) ^ n"])
    apply (rule card_bij_eq[where ?f = "\<lambda>k. k div 2" and ?g = "(*) 2"])
    subgoal unfolding inj_on_def by auto
    subgoal by auto
    subgoal by (simp add: inj_on_mult)
    subgoal by auto
    subgoal by (rule finite_Collect_conjI; auto)
    subgoal by (rule finite_Collect_conjI; auto)
    done
  also have "... = (- 1) ^ card {k \<in> {0<..(p - 1) div 2}. k > (p - 1) div 4}"
    by (rule arg_cong[of _ _ "\<lambda>f. (- 1) ^ card {k \<in> {0<..(p - 1) div 2}. f k}"];
        auto)
  also have "... = (- 1) ^ card {(p - 1) div 4<..(p - 1) div 2}"
    by (rule arg_cong[of _ _ "\<lambda>A. (- 1) ^ card A"]; fastforce)
  also have "... = (- 1) ^ (nat ?n)" by auto
  finally have "Legendre 2 p = 1 \<longleftrightarrow> even ?n"
    unfolding minus_one_power_iff
    by (simp add: assms even_nat_iff prime_gt_0_int zdiv_mono2)
  also have "... \<longleftrightarrow> [p = 1] (mod 8) \<or> [p = 7] (mod 8)" unfolding cong_def
    using 0 by (auto simp add: 1)
  finally show ?thesis .
qed

lemma Legendre_two_alt:
  fixes p :: int
  assumes "prime p"
  assumes "p > 2"
  shows "Legendre 2 p = (if [p = 1] (mod 8) \<or> [p = 7] (mod 8) then 1 else - 1)"
  using assms Legendre_two[OF assms]
  unfolding Legendre_def cong_def
  by (auto simp add: zmod_minus1)

lemma Legendre_mult:
  fixes a b p :: int
  assumes "prime p"
  shows "Legendre (a * b) p = Legendre a p * Legendre b p"
proof cases
  assume 0: "p = 2"
  have 1: "QuadRes p = (\<lambda>x. True)" using 0
    by (metis QuadRes_def add_0 cong_iff_dvd_diff even_add odd_one power_one
              power_zero_numeral uminus_add_conv_diff)
  thus ?thesis using 0 unfolding 1 Legendre_def cong_0_iff by auto
next
  assume "p \<noteq> 2"
  hence 2: "p > 2" using assms by (simp add: order_less_le prime_ge_2_int)
  have "[Legendre a p = a ^ ((nat p - 1) div 2)] (mod p)"
       "[Legendre b p = b ^ ((nat p - 1) div 2)] (mod p)"
       "[Legendre (a * b) p = (a * b) ^ ((nat p - 1) div 2)] (mod p)"
    using 2 assms euler_criterion[of "nat p" a]
                  euler_criterion[of "nat p" b]
                  euler_criterion[of "nat p" "a * b"]
    by auto
  hence 3: "[Legendre (a * b) p = Legendre a p * Legendre b p] (mod p)"
    by (smt (verit, best) cong_mult cong_sym cong_trans power_mult_distrib)
  have 4: "{Legendre a p, Legendre b p, Legendre (a * b) p} \<subseteq> {-1, 0, 1}"
    unfolding Legendre_def by auto
  show ?thesis using 2 3 4 by (auto simp add: cong_iff_dvd_diff zdvd_not_zless)
qed

lemma Legendre_power:
  fixes a :: int
  fixes n :: nat
  fixes p :: int
  assumes "prime p"
  assumes "p > 2"
  shows "Legendre (a ^ n) p = (Legendre a p) ^ n"
proof (induct n)
  case 0
  thus ?case using assms Legendre_one by auto
next
  case (Suc n)
  thus ?case using assms Legendre_mult by auto
qed

lemma Legendre_prod:
  fixes A :: "'a set"
  fixes f :: "'a \<Rightarrow> int"
  fixes p :: int
  assumes "prime p"
  assumes "p > 2"
  shows "Legendre (prod f A) p = (\<Prod>x\<in>A. Legendre (f x) p)"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  thus ?case using assms Legendre_one by auto
next
  case empty
  thus ?case using assms Legendre_one by auto
next
  case (insert x F)
  thus ?case using assms Legendre_mult by auto
qed

lemma Legendre_equal:
  fixes p q :: int
  assumes "prime p" "prime q"
  assumes "p > 2" "q > 2"
  assumes "p \<noteq> q"
  assumes "[p = 1] (mod 4) \<or> [q = 1] (mod 4)"
  shows "Legendre p q = Legendre q p"
proof -
  have 0: "even (p - 1)" "even (q - 1)" using assms prime_odd_int by auto
  have 1: "((p - 1) div 2) * ((q - 1) div 2) = (p - 1) * (q - 1) div 4"
    using 0 by fastforce
  have 2: "{Legendre p q, Legendre q p} \<subseteq> {-1, 0, 1}"
    unfolding Legendre_def by auto
  have "Legendre p q * Legendre q p =
        (- 1) ^ nat (((p - 1) div 2) * ((q - 1) div 2))"
    using assms Quadratic_Reciprocity_int[of p q]
    by fastforce
  also have "... = (- 1) ^ nat ((p - 1) * (q - 1) div 4)" unfolding 1 by rule
  also have "... = 1"
    using 0 assms even_nat_iff
    unfolding minus_one_power_iff cong_iff_dvd_diff
    by auto
  finally show ?thesis using 2 by auto
qed

lemma Legendre_opposite:
  fixes p q :: int
  assumes "prime p" "prime q"
  assumes "p > 2" "q > 2"
  assumes "p \<noteq> q"
  assumes "[p = 3] (mod 4) \<and> [q = 3] (mod 4)"
  shows "Legendre p q = - Legendre q p"
proof -
  have 0: "even (p - 1)" "even (q - 1)" using assms prime_odd_int by auto
  have 1: "((p - 1) div 2) * ((q - 1) div 2) = (p - 1) * (q - 1) div 4"
    using 0 by fastforce
  have "[p - 1 = 2] (mod 4) \<and> [q - 1 = 2] (mod 4)"
    using assms
    unfolding cong_iff_dvd_diff
    by auto
  hence "odd ((p - 1) * (q - 1) div 4)"
    using assms 0 1
    by (metis bits_div_by_1 cong_dvd_iff dvd_div_iff_mult evenE even_mult_iff
              even_numeral nonzero_mult_div_cancel_left numeral_One odd_one
              zdiv_numeral_Bit0 zero_neq_numeral)
  hence 2: "odd (nat ((p - 1) * (q - 1) div 4))"
    using assms even_nat_iff pos_imp_zdiv_nonneg_iff by fastforce
  have 3: "{Legendre p q, Legendre q p} \<subseteq> {-1, 0, 1}"
    unfolding Legendre_def by auto
  have "Legendre p q * Legendre q p =
        (- 1) ^ nat (((p - 1) div 2) * ((q - 1) div 2))"
    using assms Quadratic_Reciprocity_int[of p q]
    by fastforce
  also have "... = (- 1) ^ nat ((p - 1) * (q - 1) div 4)" unfolding 1 by rule
  also have "... = - 1"
    using 2 3
    unfolding minus_one_power_iff
    by auto
  finally show ?thesis using 3 by auto
qed

end
