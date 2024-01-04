(*
  File:      Perfect_Fields/Perfect_Field_Library.thy
  Authors:   Katharina Kreuzer (TU München)
             Manuel Eberl (University of Innsbruck)

  A few auxiliary results, most of which should probably be moved to 
  the distribution.
*)

theory Perfect_Field_Library
imports
  "HOL-Computational_Algebra.Computational_Algebra"
  "Berlekamp_Zassenhaus.Finite_Field"
begin

(* TODO: Orphan instance! Move! *)
instance bool :: prime_card
  by standard auto

(* TODO: replace in library *)
theorem (in comm_semiring_1) binomial_ring:
  "(a + b :: 'a)^n = (\<Sum>k\<le>n. (of_nat (n choose k)) * a^k * b^(n-k))"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have decomp: "{0..n+1} = {0} \<union> {n + 1} \<union> {1..n}"
    by auto
  have decomp2: "{0..n} = {0} \<union> {1..n}"
    by auto
  have "(a + b)^(n+1) = (a + b) * (\<Sum>k\<le>n. of_nat (n choose k) * a^k * b^(n - k))"
    using Suc.hyps by simp
  also have "\<dots> = a * (\<Sum>k\<le>n. of_nat (n choose k) * a^k * b^(n-k)) +
      b * (\<Sum>k\<le>n. of_nat (n choose k) * a^k * b^(n-k))"
    by (rule distrib_right)
  also have "\<dots> = (\<Sum>k\<le>n. of_nat (n choose k) * a^(k+1) * b^(n-k)) +
      (\<Sum>k\<le>n. of_nat (n choose k) * a^k * b^(n - k + 1))"
    by (auto simp add: sum_distrib_left ac_simps)
  also have "\<dots> = (\<Sum>k\<le>n. of_nat (n choose k) * a^k * b^(n + 1 - k)) +
      (\<Sum>k=1..n+1. of_nat (n choose (k - 1)) * a^k * b^(n + 1 - k))"
    by (simp add: atMost_atLeast0 sum.shift_bounds_cl_Suc_ivl Suc_diff_le field_simps del: sum.cl_ivl_Suc)
  also have "\<dots> = b^(n + 1) +
      (\<Sum>k=1..n. of_nat (n choose k) * a^k * b^(n + 1 - k)) + (a^(n + 1) +
      (\<Sum>k=1..n. of_nat (n choose (k - 1)) * a^k * b^(n + 1 - k)))"
      using sum.nat_ivl_Suc' [of 1 n "\<lambda>k. of_nat (n choose (k-1)) * a ^ k * b ^ (n + 1 - k)"]
    by (simp add: sum.atLeast_Suc_atMost atMost_atLeast0)
  also have "\<dots> = a^(n + 1) + b^(n + 1) +
      (\<Sum>k=1..n. of_nat (n + 1 choose k) * a^k * b^(n + 1 - k))"
    by (auto simp add: field_simps sum.distrib [symmetric] choose_reduce_nat)
  also have "\<dots> = (\<Sum>k\<le>n+1. of_nat (n + 1 choose k) * a^k * b^(n + 1 - k))"
    using decomp by (simp add: atMost_atLeast0 field_simps)
  finally show ?case
    by simp
qed

(* taken from Berlekamp_Zassenhaus *)
lemma prime_not_dvd_fact:
assumes kn: "k < n" and prime_n: "prime n"
shows "\<not> n dvd fact k"
  using kn leD prime_dvd_fact_iff prime_n by auto

(* taken from Berlekamp_Zassenhaus *)
lemma dvd_choose_prime:
assumes kn: "k < n" and k: "k \<noteq> 0" and n: "n \<noteq> 0" and prime_n: "prime n"
shows "n dvd (n choose k)"
proof -
  have "n dvd (fact n)" by (simp add: fact_num_eq_if n)
  moreover have "\<not> n dvd (fact k * fact (n-k))"
  proof (rule ccontr, safe)
    assume "n dvd fact k * fact (n - k)"
    hence "n dvd fact k \<or> n dvd fact (n - k)" using prime_dvd_mult_eq_nat[OF prime_n] by simp
    moreover have "\<not> n dvd (fact k)" by (rule prime_not_dvd_fact[OF kn prime_n])
    moreover have "\<not> n dvd fact (n - k)" using  prime_not_dvd_fact[OF _ prime_n] kn k by simp
    ultimately show False by simp
  qed
  moreover have "(fact n::nat) = fact k * fact (n-k) * (n choose k)"
    using binomial_fact_lemma kn by auto
  ultimately show ?thesis using prime_n
    by (auto simp add: prime_dvd_mult_iff)
qed

lemma CHAR_not_1 [simp]: "CHAR('a :: {semiring_1, zero_neq_one}) \<noteq> Suc 0"
  by (metis One_nat_def of_nat_1 of_nat_CHAR zero_neq_one)

lemma (in idom) CHAR_not_1' [simp]: "CHAR('a) \<noteq> Suc 0"
  using local.of_nat_CHAR by fastforce

lemma semiring_char_mod_ring [simp]:
  "CHAR('n :: nontriv mod_ring) = CARD('n)"
proof (rule CHAR_eq_posI)
  fix x assume "x > 0" "x < CARD('n)"
  thus "of_nat x \<noteq> (0 :: 'n mod_ring)"
    by transfer auto
qed auto

lemma of_nat_eq_iff_cong_CHAR:
  "of_nat x = (of_nat y :: 'a :: semiring_1_cancel) \<longleftrightarrow> [x = y] (mod CHAR('a))"
proof (induction x y rule: linorder_wlog)
  case (le x y)
  define z where "z = y - x"
  have [simp]: "y = x + z"
    using le by (auto simp: z_def)
  have "(CHAR('a) dvd z) = [x = x + z] (mod CHAR('a))"
    by (metis \<open>y = x + z\<close> cong_def le mod_eq_dvd_iff_nat z_def)
  thus ?case
    by (simp add: of_nat_eq_0_iff_char_dvd)
qed (simp add: eq_commute cong_sym_eq)   

lemma (in ring_1) of_int_eq_0_iff_char_dvd:
  "(of_int n = (0 :: 'a)) = (int CHAR('a) dvd n)"
proof (cases "n \<ge> 0")
  case True
  hence "(of_int n = (0 :: 'a)) \<longleftrightarrow> (of_nat (nat n)) = (0 :: 'a)"
    by auto
  also have "\<dots> \<longleftrightarrow> CHAR('a) dvd nat n"
    by (subst of_nat_eq_0_iff_char_dvd) auto
  also have "\<dots> \<longleftrightarrow> int CHAR('a) dvd n"
    using True by presburger
  finally show ?thesis .
next
  case False
  hence "(of_int n = (0 :: 'a)) \<longleftrightarrow> -(of_nat (nat (-n))) = (0 :: 'a)"
    by auto
  also have "\<dots> \<longleftrightarrow> CHAR('a) dvd nat (-n)"
    by (auto simp: of_nat_eq_0_iff_char_dvd)
  also have "\<dots> \<longleftrightarrow> int CHAR('a) dvd n"
    using False dvd_nat_abs_iff[of "CHAR('a)" n] by simp
  finally show ?thesis .
qed

lemma (in ring_1) of_int_eq_iff_cong_CHAR:
  "of_int x = (of_int y :: 'a) \<longleftrightarrow> [x = y] (mod int CHAR('a))"
proof -
  have "of_int x = (of_int y :: 'a) \<longleftrightarrow> of_int (x - y) = (0 :: 'a)"
    by auto
  also have "\<dots> \<longleftrightarrow> (int CHAR('a) dvd x - y)"
    by (rule of_int_eq_0_iff_char_dvd)
  also have "\<dots> \<longleftrightarrow> [x = y] (mod int CHAR('a))"
    by (simp add: cong_iff_dvd_diff)
  finally show ?thesis .
qed

lemma finite_imp_CHAR_pos:
  assumes "finite (UNIV :: 'a set)"
  shows   "CHAR('a :: semiring_1_cancel) > 0"
proof -
  have "\<exists>n\<in>UNIV. infinite {m \<in> UNIV. of_nat m = (of_nat n :: 'a)}"
  proof (rule pigeonhole_infinite)
    show "infinite (UNIV :: nat set)"
      by simp
    show "finite (range (of_nat :: nat \<Rightarrow> 'a))"
      by (rule finite_subset[OF _ assms]) auto
  qed
  then obtain n :: nat where "infinite {m \<in> UNIV. of_nat m = (of_nat n :: 'a)}"
    by blast
  hence "\<not>({m \<in> UNIV. of_nat m = (of_nat n :: 'a)} \<subseteq> {n})"
    by (intro notI) (use finite_subset in blast)
  then obtain m where "m \<noteq> n" "of_nat m = (of_nat n :: 'a)"
    by blast
  hence "[m = n] (mod CHAR('a))"
    by (simp add: of_nat_eq_iff_cong_CHAR)
  hence "CHAR('a) \<noteq> 0"
    using \<open>m \<noteq> n\<close> by (intro notI) auto
  thus ?thesis
    by simp
qed

lemma CHAR_dvd_CARD: "CHAR('a :: ring_1) dvd CARD('a)"
proof (cases "CARD('a) = 0")
  case False
  hence [intro]: "CHAR('a) > 0"
    by (simp add: card_eq_0_iff finite_imp_CHAR_pos)    
  define G where "G = \<lparr> carrier = (UNIV :: 'a set), monoid.mult = (+), one = (0 :: 'a) \<rparr>"
  define H where "H = (of_nat ` {..<CHAR('a)} :: 'a set)"
  interpret group G
  proof (rule groupI)
    fix x assume x: "x \<in> carrier G"
    show "\<exists>y\<in>carrier G. y \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub>"
      by (intro bexI[of _ "-x"]) (auto simp: G_def)
  qed (auto simp: G_def add_ac)

  interpret subgroup H G
  proof
    show "\<one>\<^bsub>G\<^esub> \<in> H"
      using False unfolding G_def H_def
      by (intro image_eqI[of _ _ 0]) auto
  next
    fix x y :: 'a
    assume "x \<in> H" "y \<in> H"
    then obtain x' y' where [simp]: "x = of_nat x'" "y = of_nat y'"
      by (auto simp: H_def)
    have "x + y = of_nat ((x' + y') mod CHAR('a))"
      by (auto simp flip: of_nat_add simp: of_nat_eq_iff_cong_CHAR)
    moreover have "(x' + y') mod CHAR('a) < CHAR('a)"
      using H_def \<open>y \<in> H\<close> by fastforce
    ultimately show "x \<otimes>\<^bsub>G\<^esub> y \<in> H"
      by (auto simp: H_def G_def intro!: imageI)
  next
    fix x :: 'a
    assume x: "x \<in> H"
    then obtain x' where [simp]: "x = of_nat x'" and x': "x' < CHAR('a)"
      by (auto simp: H_def)
    have "CHAR('a) dvd x' + (CHAR('a) - x') mod CHAR('a)"
      by (metis x' dvd_eq_mod_eq_0 le_add_diff_inverse mod_add_right_eq mod_self order_less_imp_le)
    hence "x + of_nat ((CHAR('a) - x') mod CHAR('a)) = 0"
      by (auto simp flip: of_nat_add simp: of_nat_eq_0_iff_char_dvd)
    moreover from this have "inv\<^bsub>G\<^esub> x = of_nat ((CHAR('a) - x') mod CHAR('a))"
      by (intro inv_equality) (auto simp: G_def add_ac)
    moreover have "of_nat ((CHAR('a) - x') mod CHAR('a)) \<in> H"
      unfolding H_def using \<open>CHAR('a) > 0\<close> by (intro imageI) auto
    ultimately show "inv\<^bsub>G\<^esub> x \<in> H" by force
  qed (auto simp: G_def H_def)

  have "card H dvd card (rcosets\<^bsub>G\<^esub> H) * card H"
    by simp
  also have "card (rcosets\<^bsub>G\<^esub> H) * card H = Coset.order G"
  proof (rule lagrange_finite)
    show "finite (carrier G)"
      using False card_ge_0_finite by (auto simp: G_def)
  qed (fact is_subgroup)
  finally have "card H dvd CARD('a)"
    by (simp add: Coset.order_def G_def)
  also have "card H = card {..<CHAR('a)}"
    unfolding H_def by (intro card_image inj_onI) (auto simp: of_nat_eq_iff_cong_CHAR cong_def)
  finally show "CHAR('a) dvd CARD('a)"
    by simp
qed auto

lemma (in idom) prime_CHAR_semidom:
  assumes "CHAR('a) > 0"
  shows   "prime CHAR('a)"
proof -
  have False if ab: "a \<noteq> 1" "b \<noteq> 1" "CHAR('a) = a * b" for a b
  proof -
    from assms ab have "a > 0" "b > 0"
      by (auto intro!: Nat.gr0I)    
    have "of_nat (a * b) = (0 :: 'a)"
      using ab by (metis of_nat_CHAR)
    also have "of_nat (a * b) = (of_nat a :: 'a) * of_nat b"
      by simp
    finally have "of_nat a * of_nat b = (0 :: 'a)" .
    moreover have "of_nat a * of_nat b \<noteq> (0 :: 'a)"
      using ab \<open>a > 0\<close> \<open>b > 0\<close>
      by (intro no_zero_divisors) (auto simp: of_nat_eq_0_iff_char_dvd)
    ultimately show False
      by contradiction
  qed
  moreover have "CHAR('a) > 1"
    using assms CHAR_not_1' by linarith
  ultimately have "prime_elem CHAR('a)"
    by (intro irreducible_imp_prime_elem) (auto simp: Factorial_Ring.irreducible_def)
  thus ?thesis
    by auto
qed


text \<open>
  Characteristics are preserved by typical functors (polynomials, power series, Laurent series):
\<close>
lemma semiring_char_poly [simp]: "CHAR('a :: comm_semiring_1 poly) = CHAR('a)"
  by (rule CHAR_eqI) (auto simp: of_nat_poly of_nat_eq_0_iff_char_dvd)

lemma semiring_char_fps [simp]: "CHAR('a :: comm_semiring_1 fps) = CHAR('a)"
  by (rule CHAR_eqI) (auto simp flip: fps_of_nat simp: of_nat_eq_0_iff_char_dvd)

(* TODO Move *)
lemma fls_const_eq_0_iff [simp]: "fls_const c = 0 \<longleftrightarrow> c = 0"
  using fls_const_0 fls_const_nonzero by blast

lemma semiring_char_fls [simp]: "CHAR('a :: comm_semiring_1 fls) = CHAR('a)"
  by (rule CHAR_eqI) (auto simp: fls_of_nat of_nat_eq_0_iff_char_dvd fls_const_nonzero)

lemma irreducible_power_iff [simp]:
  "irreducible (p ^ n) \<longleftrightarrow> irreducible p \<and> n = 1"
proof
  assume *: "irreducible (p ^ n)"
  have [simp]: "\<not>p dvd 1"
  proof
    assume "p dvd 1"
    hence "p ^ n dvd 1"
      by (metis dvd_power_same power_one)
    with * show False
      by auto
  qed

  consider "n = 0" | "n = 1" | "n > 1"
    by linarith
  thus "irreducible p \<and> n = 1"
  proof cases
    assume "n > 1"
    hence "p ^ n = p * p ^ (n - 1)"
      by (cases n) auto
    with * \<open>\<not> p dvd 1\<close> have "p ^ (n - 1) dvd 1"
      using irreducible_multD by blast
    with \<open>\<not>p dvd 1\<close> and \<open>n > 1\<close> have False
      by (meson dvd_power dvd_trans zero_less_diff)
    thus ?thesis ..
  qed (use * in auto)
qed auto

lemma pderiv_monom:
  "pderiv (Polynomial.monom c n) = of_nat n * Polynomial.monom c (n - 1)"
proof (cases n)
  case (Suc n)
  show ?thesis
    unfolding monom_altdef Suc pderiv_smult pderiv_power_Suc pderiv_pCons
    by (simp add: of_nat_poly)
qed (auto simp: monom_altdef)

lemma uminus_CHAR_2 [simp]:
  assumes "CHAR('a :: ring_1) = 2"
  shows   "-(x :: 'a) = x"
proof -
  have "x + x = 2 * x"
    by (simp add: mult_2)
  also have "2 = (0 :: 'a)"
    using assms by (metis of_nat_CHAR of_nat_numeral)
  finally show ?thesis
    by (simp add: add_eq_0_iff2)
qed

lemma minus_CHAR_2 [simp]:
  assumes "CHAR('a :: ring_1) = 2"
  shows   "(x - y :: 'a) = x + y"
  using uminus_CHAR_2[of y] assms by simp

lemma minus_power_prime_CHAR:
  assumes "p = CHAR('a :: {ring_1})" "prime p"
  shows "(-x :: 'a) ^ p = -(x ^ p)"
proof (cases "p = 2")
  case False
  have "prime p"
    using assms by blast
  with False have "odd p"
    using primes_dvd_imp_eq two_is_prime_nat by blast
  thus ?thesis
    by simp
qed (use assms in auto)

end