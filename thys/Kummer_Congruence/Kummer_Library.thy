(*
  File:     Kummer_Congruence/Kummer_Library.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>Preliminary facts\<close>
theory Kummer_Library
imports
  "HOL-Number_Theory.Number_Theory"
  "Bernoulli.Bernoulli_Zeta"
begin

subsection \<open>Miscellaneous facts\<close>

lemma fact_ge_monomial:
  fixes k :: "'a :: {linordered_semidom, semiring_char_0}"
  assumes "n \<ge> n0" "fact n0 \<ge> c * k ^ n0" "of_nat n0 \<ge> k" "k \<ge> 0"
  shows   "fact n \<ge> c * k ^ n"
proof -
  have "fact n = (\<Prod>i=1..n. of_nat i :: 'a)"
    by (simp add: fact_prod)
  also have "{1..n} = {1..n0} \<union> {n0<..n}"
    using assms by auto
  also have "(\<Prod>i\<in>\<dots>. of_nat i :: 'a) = (\<Prod>i=1..n0. of_nat i) * (\<Prod>i\<in>{n0<..n}. of_nat i)"
    by (subst prod.union_disjoint) auto
  also have "(\<Prod>i=1..n0. of_nat i :: 'a) = fact n0"
    by (simp add: fact_prod)
  also have "fact n0 * (\<Prod>i\<in>{n0<..n}. of_nat i :: 'a) \<ge> c * k ^ n0 * (\<Prod>i\<in>{n0<..n}. k)"
    using assms by (intro mult_mono prod_mono conjI order.trans[OF assms(3)]) auto
  also have "(\<Prod>i\<in>{n0<..n}. k) = k ^ (n - n0)"
    using \<open>n \<ge> n0\<close> by simp
  also have "c * k ^ n0 * k ^ (n - n0) = c * (k ^ n0 * k ^ (n - n0))"
    by (simp add: algebra_simps)
  also have "k ^ n0 * k ^ (n - n0) = k ^ n"
    using \<open>n \<ge> n0\<close> by (simp flip: power_add)
  finally show ?thesis .
qed

lemma fact_ge_2pi_power:
  assumes "n \<ge> 23"
  shows   "fact n \<ge> (2 * pi) ^ n * n"
proof -
  define m where "m = n - 1"
  have n_eq: "n = Suc m"
    using assms by (simp add: m_def)
  have "m \<ge> 22"
    using assms by (simp add: n_eq)
  hence *: "fact m \<ge> 8 * (8 ^ m :: real)"
    by (rule fact_ge_monomial) (simp_all add: fact_numeral)

  have "(2 * pi) ^ n \<le> (2 * 4) ^ n"
    by (intro power_mono mult_left_mono less_imp_le[OF pi_less_4]) auto
  also have "\<dots> = 8 * 8 ^ m"
    by (simp add: n_eq)
  also have "\<dots> \<le> fact m"
    using \<open>m \<ge> 22\<close> by (rule fact_ge_monomial) (simp_all add: fact_numeral)
  also have "fact m = fact n / n"
    by (simp add: n_eq)
  finally show ?thesis
    using assms by (simp add: field_simps)
qed

lemma Rats_power_int: "x \<in> \<rat> \<Longrightarrow> x powi n \<in> \<rat>"
  by (auto simp: power_int_def)

lemma coprimeI_via_bezout:
  fixes x y :: "'a :: algebraic_semidom"
  assumes "a * x + b * y = 1"
  shows   "coprime x y"
  by (metis assms coprime_def dvd_add dvd_mult)

lemma quotient_of_eqI:
  assumes "coprime a b" "b > 0" "x = of_int a / of_int b"
  shows   "quotient_of x = (a, b)"
  using Fract_of_int_quotient assms(1) assms(2) assms(3) normalize_stable quotient_of_Fract
  by simp

lemma quotient_of_of_nat [simp]: "quotient_of (of_nat n) = (int n, 1)"
  by (intro quotient_of_eqI) auto

lemma quotient_of_of_int [simp]: "quotient_of (of_int n) = (n, 1)"
  by (intro quotient_of_eqI) auto

lemma quotient_of_fraction_conv_normalize:
  "quotient_of (of_int a / of_int b) = Rat.normalize (a, b)"
  using Fract_of_int_quotient quotient_of_Fract by presburger

lemma dvd_imp_div_dvd: "(b :: 'a :: algebraic_semidom) dvd a \<Longrightarrow> a div b dvd a"
  by (metis dvd_mult_div_cancel dvd_triv_right)

lemma dvd_rat_normalize:
  assumes "b \<noteq> 0"
  shows   "fst (Rat.normalize (a, b)) dvd a" "snd (Rat.normalize (a, b)) dvd b"
  using assms by (auto simp: Rat.normalize_def Let_def intro!: dvd_imp_div_dvd)

lemma of_int_div: "b dvd a \<Longrightarrow> of_int (a div b) = of_int a / (of_int b :: 'a :: field_char_0)"
  by (elim dvdE) auto

lemma coprime_lcm_left: 
  fixes a b c :: "'a :: semiring_gcd"
  shows "coprime a c \<Longrightarrow> coprime b c \<Longrightarrow> coprime (lcm a b) c"
  by (meson coprime_divisors coprime_mult_left_iff dvd_refl dvd_triv_left dvd_triv_right lcm_least)

lemma coprime_Lcm_left:
  fixes x y :: "'a :: semiring_Gcd"
  assumes "finite A" "\<And>x. x \<in> A \<Longrightarrow> coprime x y"
  shows   "coprime (Lcm A) y"
  using assms by (induction rule: finite_induct) (auto intro: coprime_lcm_left)

lemma coprimeI_by_prime_factors:
  fixes x y :: "'a :: factorial_semiring"
  assumes "\<And>p. p \<in> prime_factors x \<Longrightarrow> \<not>p dvd y"
  assumes "x \<noteq> 0"
  shows   "coprime x y"
  using assms by (smt (verit, best) coprimeI dvd_0_right dvd_trans prime_divisor_exists prime_factorsI)

lemma multiplicity_int: "multiplicity (int p) (int n) = multiplicity p n"
proof -
  have "{k. p ^ k dvd n} = {k. int p ^ k dvd int n}"
    by (intro Collect_cong) (auto simp flip: of_nat_power)
  thus ?thesis
    by (simp add: multiplicity_def)
qed

lemma squarefree_int_iff [simp]: "squarefree (int n) \<longleftrightarrow> squarefree n"
proof (cases "n = 0")
  case True
  thus ?thesis by auto
next
  case False
  show ?thesis
  proof
    assume "squarefree n"
    thus "squarefree (int n)"
      apply (subst squarefree_factorial_semiring, use False in \<open>simp; fail\<close>)
      apply (subst (asm) squarefree_factorial_semiring, use False in \<open>simp; fail\<close>)
      by (metis nat_dvd_iff nat_power_eq prime_int_nat_transfer zero_le_power_eq)
  next
    assume "squarefree (int n)"
    thus "squarefree n"
      apply (subst squarefree_factorial_semiring, use False in \<open>simp; fail\<close>)
      apply (subst (asm) squarefree_factorial_semiring, use False in \<open>simp; fail\<close>)
      by (metis of_nat_dvd_iff of_nat_power prime_nat_int_transfer)
  qed
qed

lemma squarefree_imp_multiplicity_prime_le_1:
  "squarefree n \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> prime p \<Longrightarrow> multiplicity p n \<le> 1"
  using squarefree_factorial_semiring''[of n] by auto

lemma residue_primroot_is_generator':
  assumes "m > 1" and "residue_primroot m g"
  shows   "bij_betw (\<lambda>i. g ^ i mod m) {1..totient m} (totatives m)"
  unfolding bij_betw_def
proof
  show "inj_on (\<lambda>i. g ^ i mod m) {1..totient m}"
  proof (rule inj_onI)
    fix i j assume ij: "i \<in> {1..totient m}" "j \<in> {1..totient m}" "g ^ i mod m = g ^ j mod m"
    hence "[g ^ i = g ^ j] (mod m)"
      by (simp add: Cong.cong_def)
    also have "?this \<longleftrightarrow> [i = j] (mod totient m)"
      using assms by (subst order_divides_expdiff) (auto simp: residue_primroot_def)
    also have "\<dots> \<longleftrightarrow> [int i = int j] (mod int (totient m))"
      by (simp add: cong_int_iff)
    also have "\<dots> \<longleftrightarrow> int (totient m) dvd (int i - int j)"
      by (rule cong_iff_dvd_diff)
    finally have dvd: "int (totient m) dvd \<bar>int i - int j\<bar>"
      by simp
    show "i = j"
    proof (rule ccontr)
      assume "i \<noteq> j"
      with dvd have "int (totient m) \<le> \<bar>int i - int j\<bar>"
        by (intro zdvd_imp_le) auto
      moreover have "\<bar>int i - int j\<bar> < totient m"
        using ij by auto
      ultimately show False
        by simp
    qed
  qed
next
  show "(\<lambda>i. g ^ i mod m) ` {1..totient m} = totatives m"
  proof safe
    fix x assume "x \<in> totatives m"
    also have "totatives m = (\<lambda>i. g ^ i mod m) ` {..<totient m}"
      using residue_primroot_is_generator[OF assms] unfolding bij_betw_def by blast 
    finally obtain i where i: "i < totient m" "g ^ i mod m = x"
      by auto
    have "coprime g m"
      using assms by (auto simp: residue_primroot_def coprime_commute)
    hence "g ^ totient m mod m = g ^ 0 mod m"
      using euler_theorem[of g m] by (auto simp: Cong.cong_def)
    with i have "x = g ^ (if i = 0 then totient m else i) mod m" 
                "(if i = 0 then totient m else i) \<in> {1..totient m}"
      by auto
    thus "x \<in> (\<lambda>i. g ^ i mod m) ` {1..totient m}"
      by blast
  qed (use assms in \<open>auto simp: power_in_totatives residue_primroot_def\<close>)
qed

subsection \<open>Facts about congruence\<close>

lemma cong_modulus_mono:
  assumes "[a = b] (mod m)" "m' dvd m"
  shows   "[a = b] (mod m')"
  using assms by (metis mod_mod_cancel unique_euclidean_semiring_class.cong_def)

lemma cong_pow_totient:
  fixes x x' n k k' :: nat
  assumes "[x = x'] (mod n)" "[k = k'] (mod totient n)" "coprime x n"
  shows   "[x ^ k = x' ^ k'] (mod n)"
proof -
  have "[k = k'] (mod ord n x)"
    by (rule cong_modulus_mono[OF assms(2)])
       (use assms in \<open>auto intro!: order_divides_totient simp: coprime_commute\<close>)
  hence "[x ^ k = x ^ k'] (mod n)"
    by (subst order_divides_expdiff) (use assms in \<open>auto simp: coprime_commute\<close>)
  also have "[x ^ k' = x' ^ k'] (mod n)"
    by (intro cong_pow assms)
  finally show ?thesis .
qed

lemma cong_modulus_power:
  assumes "[a = b] (mod (n ^ k))" "k > 0"
  shows   "[a = b] (mod n)"
  using assms(1) by (rule cong_modulus_mono) (use assms(2) in auto)

lemma cong_mult_cancel:
  assumes "[n * a = n * b] (mod (n * m))" "n \<noteq> 0"
  shows   "[a = b] (mod m)"
  using assms by (auto simp: Cong.cong_def)

lemma cong_mult_square:
  assumes "[a = 0] (mod n)" "[b = b'] (mod n)"
  shows   "[a * b = a * b'] (mod (n\<^sup>2))"
  using assms by (auto simp: Cong.cong_def power2_eq_square intro: mod_mult_cong elim!: dvdE)

lemma sum_reindex_bij_betw_cong:
  assumes "\<And>a. a \<in> S \<Longrightarrow> i (j a) = a"
  assumes "\<And>a. a \<in> S \<Longrightarrow> j a \<in> T"
  assumes "\<And>b. b \<in> T \<Longrightarrow> j (i b) = b"
  assumes "\<And>b. b \<in> T \<Longrightarrow> i b \<in> S"
  assumes "\<And>a. a \<in> S \<Longrightarrow> [h (j a) = g a] (mod m)"
  shows   "[sum g S = sum h T] (mod m)"
proof -
  have "[sum g S = (\<Sum>x\<in>S. g x mod m)] (mod m)"
    by (intro cong_sum) (auto simp: Cong.cong_def)
  also have "(\<Sum>x\<in>S. g x mod m) = (\<Sum>x\<in>T. h x mod m)"
    using assms by (intro sum.reindex_bij_witness[of _ i j]) (auto simp: Cong.cong_def)
  also have "[\<dots> = sum h T] (mod m)"
    by (intro cong_sum) (auto simp: Cong.cong_def)
  finally show ?thesis .
qed

lemma power_mult_cong:
  fixes a b :: "'a :: unique_euclidean_ring"
  assumes "[a = b] (mod n^k)" and "k' \<le> k + l"
  shows   "[n^l * a = n^l * b] (mod n^k')"
proof (cases "k' \<ge> k")
  case True
  have "n^(k'-k) * n^k dvd n^l * (a - b)"
    by (intro mult_dvd_mono le_imp_power_dvd) (use assms in \<open>auto simp: cong_iff_dvd_diff\<close>)
  also have "n^(k'-k) * n^k = n ^ k'"
    using True by (simp flip: power_add)
  finally show ?thesis
    by (simp add: cong_iff_dvd_diff algebra_simps)
next
  case False
  have "n ^ k' dvd n ^ k"
    using False by (intro le_imp_power_dvd) auto
  also have "[n^l * a = n^l * b] (mod n^k)"
    by (intro cong_mult cong_refl assms)
  hence "n ^ k dvd (n^l * a - n^l * b)"
    by (simp add: cong_iff_dvd_diff)
  finally show ?thesis
    by (simp add: cong_iff_dvd_diff)
qed

lemma residue_primroot_power_cong_neg1:
  fixes x :: nat and p :: nat
  assumes "prime p" "p \<noteq> 2" "residue_primroot p x"
  shows   "[int x ^ ((p - 1) div 2) = -1] (mod p)"
proof -
  have "x > 0"
    using assms by (intro Nat.gr0I) auto
  from assms have "p > 2"
    using prime_gt_1_nat[of p] by auto
  hence "odd p"
    using assms by (intro prime_odd_nat) auto
  have cong_1_iff: "[int x ^ k = 1] (mod p) \<longleftrightarrow> (p - 1) dvd k" for k
    using assms
    by (metis cong_int_iff of_nat_1 of_nat_power ord_divides residue_primroot.cases totient_prime)

  have "[int x ^ ((p - 1) div 2) = 1] (mod p) \<or> [int x ^ ((p - 1) div 2) = -1] (mod p)"
  proof (rule cong_square)
    have "int x ^ ((p - 1) div 2) * int x ^ ((p - 1) div 2) = (int x ^ ((p - 1) div 2)) ^ 2"
      by (simp add: power2_eq_square)
    also have "\<dots> = int x ^ ((p - 1) div 2 * 2)"
      by (simp add: power_mult)
    also have "(p - 1) div 2 * 2 = p - 1"
      using \<open>odd p\<close> by auto
    also have "[int x ^ (p - 1) = 1] (mod p)"
      by (subst cong_1_iff) auto
    finally show "[int x ^ ((p - 1) div 2) * int x ^ ((p - 1) div 2) = 1] (mod p)" .
  qed (use assms \<open>x > 0\<close> in auto)
  moreover have "\<not>p - 1 dvd (p - 1) div 2"
  proof
    assume "p - 1 dvd (p - 1) div 2"
    hence "p - 1 \<le> (p - 1) div 2"
      using assms \<open>odd p\<close> \<open>p > 2\<close> by (intro dvd_imp_le) (auto elim!: dvdE)
    also have "\<dots> < (p - 1)"
      by (rule div_less_dividend) (use \<open>p > 2\<close> in auto)
    finally show False
      by simp
  qed
  hence "[int x ^ ((p - 1) div 2) \<noteq> 1] (mod p)"
    by (subst cong_1_iff) auto
  ultimately show ?thesis
    by auto
qed

lemma cong_mod_left: "[a = b] (mod p) \<Longrightarrow> [a mod p = b] (mod p)"
  by auto

lemma cong_mod_right: "[a = b] (mod p) \<Longrightarrow> [a = b mod p] (mod p)"
  by auto

lemma cong_mod: "[a = b] (mod p) \<Longrightarrow> [a mod p = b mod p] (mod p)"
  by auto


subsection \<open>Modular inverses\<close>

definition modular_inverse where
  "modular_inverse p n = fst (bezout_coefficients n p) mod p"

lemma cong_modular_inverse1:
  assumes "coprime n p"
  shows   "[n * modular_inverse p n = 1] (mod p)"
proof -
  have "[fst (bezout_coefficients n p) * n + snd (bezout_coefficients n p) * p =
         modular_inverse p n * n + 0] (mod p)"
    unfolding modular_inverse_def by (intro cong_add cong_mult) (auto simp: Cong.cong_def)
  also have "fst (bezout_coefficients n p) * n + snd (bezout_coefficients n p) * p = gcd n p"
    by (simp add: bezout_coefficients_fst_snd)
  also have "\<dots> = 1"
    using assms by simp
  finally show ?thesis
    by (simp add: cong_sym mult_ac)
qed

lemma cong_modular_inverse2:
  assumes "coprime n p"
  shows   "[modular_inverse p n * n = 1] (mod p)"
  using cong_modular_inverse1[OF assms] by (simp add: mult.commute)

lemma coprime_modular_inverse [simp, intro]:
  fixes n :: "'a :: {euclidean_ring_gcd,unique_euclidean_semiring}"
  assumes "coprime n p"
  shows   "coprime (modular_inverse p n) p"
  using cong_modular_inverse1[OF assms] assms
  by (meson cong_imp_coprime cong_sym coprime_1_left coprime_mult_left_iff)

lemma modular_inverse_int_nonneg: "p > 0 \<Longrightarrow> modular_inverse p (n :: int) \<ge> 0"
  by (simp add: modular_inverse_def)

lemma modular_inverse_int_less: "p > 0 \<Longrightarrow> modular_inverse p (n :: int) < p"
  by (simp add: modular_inverse_def)

lemma modular_inverse_int_eqI:
  fixes x y :: int
  assumes "y \<in> {0..<m}" "[x * y = 1] (mod m)"
  shows   "modular_inverse m x = y"
proof -
  from assms have "coprime x m"
    using cong_gcd_eq by force
  have "[modular_inverse m x * 1 = modular_inverse m x * (x * y)] (mod m)"
    by (rule cong_sym, intro cong_mult assms cong_refl)
  also have "modular_inverse m x * (x * y) = (modular_inverse m x * x) * y"
    by (simp add: mult_ac)
  also have "[\<dots> = 1 * y] (mod m)"
    using \<open>coprime x m\<close> by (intro cong_mult cong_refl cong_modular_inverse2)
  finally have "[modular_inverse m x = y] (mod m)"
    by simp
  thus "modular_inverse m x = y"
    using assms by (simp add: Cong.cong_def modular_inverse_def)
qed

lemma modular_inverse_1 [simp]:
  assumes "m > (1 :: int)"
  shows   "modular_inverse m 1 = 1"
  by (rule modular_inverse_int_eqI) (use assms in auto)

lemma modular_inverse_int_mult:
  fixes x y :: int
  assumes "coprime x m" "coprime y m" "m > 0"
  shows "modular_inverse m (x * y) = (modular_inverse m y * modular_inverse m x) mod m"
proof (rule modular_inverse_int_eqI)
  show "modular_inverse m y * modular_inverse m x mod m \<in> {0..<m}"
    using assms by auto
next
  have "[x * y * (modular_inverse m y * modular_inverse m x mod m) =
         x * y * (modular_inverse m y * modular_inverse m x)] (mod m)"
    by (intro cong_mult cong_refl) auto
  also have "x * y * (modular_inverse m y * modular_inverse m x) =
             (x * modular_inverse m x) * (y * modular_inverse m y)"
    by (simp add: mult_ac)
  also have "[\<dots> = 1 * 1] (mod m)"
    by (intro cong_mult cong_modular_inverse1 assms)
  finally show "[x * y * (modular_inverse m y * modular_inverse m x mod m) = 1] (mod m)"
    by simp
qed

lemma bij_betw_int_remainders_mult:
  fixes a n :: int
  assumes a: "coprime a n"
  shows   "bij_betw (\<lambda>m. a * m mod n) {1..<n} {1..<n}"
proof -
  define a' where "a' = modular_inverse n a"

  have *: "a' * (a * m mod n) mod n = m \<and> a * m mod n \<in> {1..<n}"
    if a: "[a * a' = 1] (mod n)" and m: "m \<in> {1..<n}" for m a a' :: int
  proof
    have "[a' * (a * m mod n) = a' * (a * m)] (mod n)"
      by (intro cong_mult cong_refl) (auto simp: Cong.cong_def)
    also have "a' * (a * m) = (a * a') * m"
      by (simp add: mult_ac)
    also have "[(a * a') * m = 1 * m] (mod n)"
      unfolding a'_def by (intro cong_mult cong_refl) (use a in auto)
    finally show "a' * (a * m mod n) mod n = m"
      using m by (simp add: Cong.cong_def)
  next
    have "coprime a n"
      using a coprime_iff_invertible_int by auto
    hence "\<not>n dvd (a * m)"
      using m by (simp add: coprime_commute coprime_dvd_mult_right_iff zdvd_not_zless)
    hence "a * m mod n > 0"
      using m order_le_less by fastforce
    thus "a * m mod n \<in> {1..<n}"
      using m by auto
  qed

  have "[a * a' = 1] (mod n)" "[a' * a = 1] (mod n)"
    unfolding a'_def by (rule cong_modular_inverse1 cong_modular_inverse2; fact)+
  from this[THEN *] show ?thesis
    by (intro bij_betwI[of _ _ _ "\<lambda>m. a' * m mod n"]) auto
qed


subsection \<open>Facts about Bernoulli numbers\<close>

(* TODO: it might be better to generalise the type of "bernoulli" in the library. *)
definition bernoulli_rat :: "nat \<Rightarrow> rat"
  where "bernoulli_rat n = of_int (bernoulli_num n) / of_int (bernoulli_denom n)"

bundle bernoulli_syntax
begin
notation bernoulli_rat (\<open>\<B>\<close>)
end

bundle no_bernoulli_syntax
begin
no_notation bernoulli_rat (\<open>\<B>\<close>)
end

lemma bernoulli_num_eq_0_iff: "bernoulli_num n = 0 \<longleftrightarrow> odd n \<and> n \<noteq> 1"
proof -
  have "bernoulli_num n = 0 \<longleftrightarrow> real_of_int (bernoulli_num n) / real (bernoulli_denom n) = 0"
    by auto
  also have "real_of_int (bernoulli_num n) / real (bernoulli_denom n) = bernoulli n"
    by (rule bernoulli_conv_num_denom [symmetric])
  also have "bernoulli n = 0 \<longleftrightarrow> odd n \<and> n \<noteq> 1"
    by (rule bernoulli_zero_iff)
  finally show ?thesis .
qed

lemma bernoulli_num_odd_eq_0: "odd k \<Longrightarrow> k \<noteq> 1 \<Longrightarrow> bernoulli_num k = 0"
  by (simp add: bernoulli_num_def bernoulli_odd_eq_0)

lemma prime_dvd_bernoulli_denom_iff:
  assumes "prime p" "even k" "k > 0"
  shows   "p dvd bernoulli_denom k \<longleftrightarrow> (p - 1) dvd k"
proof -
  have fin: "finite {p. prime p \<and> p - Suc 0 dvd k}"
    by (rule finite_subset[of _ "{..k+1}"]) (use assms in \<open>auto dest!: dvd_imp_le\<close>)
  have "bernoulli_denom k = \<Prod>{p. prime p \<and> p - 1 dvd k}"
    unfolding bernoulli_denom_def using assms by auto
  also have "p dvd \<dots> \<longleftrightarrow> (p - 1) dvd k"
    using assms fin primes_dvd_imp_eq by (subst prime_dvd_prod_iff) auto
  finally show ?thesis .
qed

lemma bernoulli_num_denom_eqI:
  assumes "bernoulli k = of_int a / of_nat b" "coprime a b" "b > 0"
  shows   "bernoulli_num k = a" "bernoulli_denom k = b"
proof -
  have "bernoulli k = of_rat (of_int (bernoulli_num k) / of_nat (bernoulli_denom k))"
    by (simp add: bernoulli_conv_num_denom of_rat_divide)
  also have "bernoulli k = of_rat (of_int a / of_nat b)"
    by (simp add: assms(1) of_rat_divide)
  finally have *: "of_int (bernoulli_num k) / of_nat (bernoulli_denom k) = (of_int a / of_nat b :: rat)"
    by simp

  have "quotient_of (of_int (bernoulli_num k) / of_nat (bernoulli_denom k)) =
          (bernoulli_num k, int (bernoulli_denom k))"    
    by (intro quotient_of_eqI coprime_bernoulli_num_denom) (auto simp: bernoulli_denom_pos)
  also note *
  also have "quotient_of (of_int a / of_nat b) = (a, int b)"
    by (intro quotient_of_eqI) (use assms in auto)
  finally show "bernoulli_num k = a" "bernoulli_denom k = b"
    by simp_all
qed

lemma bernoulli_rat_eq_0_iff: "bernoulli_rat n = 0 \<longleftrightarrow> odd n \<and> n \<noteq> 1"
  by (auto simp: bernoulli_rat_def bernoulli_num_eq_0_iff)

lemma bernoulli_rat_odd_eq_0: "odd n \<Longrightarrow> n \<noteq> 1 \<Longrightarrow> bernoulli_rat n = 0"
  by (auto simp: bernoulli_rat_def bernoulli_num_odd_eq_0)

lemma bernoulli_rat_conv_bernoulli: "of_rat (bernoulli_rat n) = bernoulli n"
  unfolding bernoulli_rat_def by (simp add: bernoulli_conv_num_denom of_rat_divide)

lemma quotient_of_bernoulli_rat [simp]:
  "quotient_of (bernoulli_rat n) = (bernoulli_num n, int (bernoulli_denom n))"
  unfolding bernoulli_rat_def
  by (rule quotient_of_eqI) (auto intro: bernoulli_denom_pos coprime_bernoulli_num_denom)

end