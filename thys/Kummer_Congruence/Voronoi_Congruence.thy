(*
  File:     Kummer_Congruence/Voronoi_Congruence.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>The Voronoi congruence\<close>
theory Voronoi_Congruence
  imports Kummer_Library Rat_Congruence
begin

unbundle bernoulli_syntax

lemma sum_of_powers_mod_prime:
  assumes p: "prime p"
  shows   "[(\<Sum>x=1..<p. int x ^ m) = (if (p - 1) dvd m then -1 else 0)] (mod p)"
proof -
  obtain g where g: "residue_primroot p g"
    using assms prime_gt_1_nat prime_primitive_root_exists by auto
  have "coprime g p"
    using g by (auto simp: residue_primroot_def coprime_commute)
  have bij: "bij_betw (\<lambda>i. g ^ i mod p) {..<p-1} {0<..<p}"
    using residue_primroot_is_generator[OF _ g] p
    by (simp add: totient_prime totatives_prime prime_gt_Suc_0_nat)
  have "(\<Sum>x=1..<p. int x ^ m) = (\<Sum>x\<in>{0<..<p}. int x ^ m)"
    by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>i<p-1. int (g ^ i mod p) ^ m)"
    by (subst sum.reindex_bij_betw[OF bij, symmetric]) auto
  also have "[\<dots> = (\<Sum>i<p-1. int (g ^ i) ^ m)] (mod p)"
    by (intro cong_sum cong_pow cong_int) auto
  also have "(\<Sum>i<p-1. int (g ^ i) ^ m) = (\<Sum>i<p-1. int (g ^ m) ^ i)"
    by (simp flip: power_mult add: mult.commute)
  also have "[\<dots> = (\<Sum>i<p-1. int (g ^ m mod p) ^ i)] (mod p)"
    by (intro cong_sum cong_pow cong_int) auto
  also have "[(\<Sum>i<p-1. int (g ^ m mod p) ^ i) = (if (p - 1) dvd m then -1 else 0)] (mod p)"
  proof (cases "(p - 1) dvd m")
    case True
    have "[(\<Sum>i<p-1. int (g ^ m mod p) ^ i) = (\<Sum>i<p-1. int (g ^ 0) ^ i)] (mod p)"
      using \<open>coprime g p\<close> p True
      by (intro cong_sum cong_pow cong_pow_totient cong_mod_left cong_refl cong_int)
         (auto simp: cong_0_iff totient_prime)
    also have "(\<Sum>i<p-1. int (g ^ 0) ^ i) = int p - 1"
      using prime_gt_1_nat[OF p] by (simp add: of_nat_diff)
    also have "[int p - 1 = 0 - 1] (mod int p)"
      by (intro cong_diff) (auto simp: Cong.cong_def)
    finally show ?thesis
      using True by auto
  next
    case False
    have not_cong: "[g ^ m \<noteq> 1] (mod p)"
      using False g by (metis assms ord_divides residue_primroot_def totient_prime)
    hence neq1: "g ^ m mod p \<noteq> 1"
      using prime_gt_1_nat[OF p] by (auto simp: Cong.cong_def)
    have "real_of_int (int (\<Sum>i<p-1. (g ^ m mod p) ^ i)) = (\<Sum>i<p-1. real (g ^ m mod p) ^ i)"
      by simp
    also have "\<dots> = (1 - real (g ^ m mod p) ^ (p - 1)) / (1 - real (g ^ m mod p))"
      using prime_gt_1_nat[OF p] neq1 by (subst sum_gp_strict) (auto simp: of_nat_diff)
    finally have "real_of_int (int (\<Sum>i<p-1. (g ^ m mod p) ^ i)) * (1 - real (g ^ m mod p)) =
                  1 - real (g ^ m mod p) ^ (p - 1)"
      using neq1 by (simp add: field_simps)
    also have "real_of_int (int (\<Sum>i<p-1. (g ^ m mod p) ^ i)) * (1 - real (g ^ m mod p)) =
               real_of_int ((\<Sum>i<p-1. int (g ^ m mod p) ^ i) * (1 - int (g ^ m mod p)))"
      by simp
    also have "1 - real (g ^ m mod p) ^ (p - 1) = real_of_int (1 - int (g ^ m mod p) ^ (p - 1))"
      by simp
    finally have "(\<Sum>i<p-1. int (g ^ m mod p) ^ i) * (1 - int (g ^ m mod p)) = 1 - int (g ^ m mod p) ^ (p - 1)"
      by linarith
    also have "[1 - int (g ^ m mod p) ^ (p - 1) = 1 - int (g ^ m) ^ (p - 1)] (mod p)"
      by (intro cong_diff cong_int cong_pow) auto
    also have "int (g ^ m) ^ (p - 1) = int ((g ^ (p - 1)) ^ m)"
      by (simp flip: power_mult add: mult.commute)
    also have "[1 - int ((g ^ (p - 1)) ^ m) = 1 - int ((g ^ 0) ^ m)] (mod p)"
      using \<open>coprime g p\<close> p
      by (intro cong_diff cong_int cong_pow_totient cong_refl)
         (auto simp: Cong.cong_def totient_prime)
    finally have "[(\<Sum>i<p-1. int (g ^ m mod p) ^ i) * (1 - int (g ^ m mod p)) = 0] (mod p)"
      by simp
    hence "p dvd (\<Sum>i<p-1. int (g ^ m mod p) ^ i) * (1 - int (g ^ m mod p))"
      by (simp add: cong_0_iff)
    moreover from not_cong have "\<not>p dvd (1 - int (g ^ m mod p))"
      by (metis of_nat_1 cong_iff_dvd_diff mod_mod_trivial nat_int of_nat_mod Cong.cong_def)
    ultimately have "p dvd (\<Sum>i<p-1. int (g ^ m mod p) ^ i)"
      using p by (subst (asm) prime_dvd_mult_iff) auto
    thus ?thesis
      using False by (simp add: Cong.cong_def)
  qed
  finally show ?thesis .
qed

lemma sum_of_powers_mod_prime':
  fixes p m :: nat
  assumes p: "prime p" "\<not>(p - 1) dvd m"
  shows   "[(\<Sum>x=1..<p. x ^ m) = 0] (mod p)"
proof -
  have "[(\<Sum>x=1..<p. int x ^ m) = int 0] (mod p)"
    using sum_of_powers_mod_prime[of p m] assms by simp
  also have "(\<Sum>x=1..<p. int x ^ m) = int (\<Sum>x=1..<p. x ^ m)"
    by simp
  finally show ?thesis
    using cong_int_iff by blast
qed

lemma voronoi_congruence_aux1:
  assumes "prime p" "j \<ge> 4"
  shows   "multiplicity p (j + 1) \<le> (if p \<in> {2, 3} then 1 else 0) + j - 2"
proof (cases "p \<in> {2, 3}")
  case True
  have "multiplicity p (j + 1) < j"
  proof (rule multiplicity_lessI)
    have "2 ^ (n + 2) > n + 3" for n
      by (induction n) auto
    from this[of "j - 2"] have "j + 1 < 2 ^ j"
      using assms(2) by (simp del: power_Suc add: Suc_diff_Suc eval_nat_numeral)
    also have "2 ^ j \<le> p ^ j"
      using True by (intro power_mono) auto
    finally have "p ^ j > j + 1" .
    thus "\<not>p ^ j dvd j + 1"
      using dvd_imp_le by force 
  qed (use assms in auto)
  with True show ?thesis
    by simp
next
  case False
  have "p \<noteq> 0" "p \<noteq> 1" "p \<noteq> 4"
    using assms by auto
  with False have "p \<ge> 5"
    by force
  have "multiplicity p (j + 1) < j - 1"
  proof (rule multiplicity_lessI)
    have "5 ^ (n + 1) > n + 3" for n
      by (induction n) auto
    from this[of "j - 2"] have "j + 1 < 5 ^ (j - 1)"
      using assms(2) by (simp del: power_Suc add: Suc_diff_Suc eval_nat_numeral)
    also have "5 ^ (j - 1) \<le> p ^ (j - 1)"
      using \<open>p \<ge> 5\<close> by (intro power_mono) auto
    finally have "p ^ (j - 1) > j + 1" .
    thus "\<not>p ^ (j - 1) dvd j + 1"
      using dvd_imp_le by force 
  qed (use assms in auto)
  with False show ?thesis
    by simp
qed

context
  fixes S :: "nat \<Rightarrow> nat \<Rightarrow> nat" and D :: "nat \<Rightarrow> nat" and N :: "nat \<Rightarrow> int"
  defines "S \<equiv> (\<lambda>k n. \<Sum>r<n. r ^ k)"
  defines "N \<equiv> bernoulli_num" and "D \<equiv> bernoulli_denom"
begin

lemma voronoi_congruence_aux2:
  fixes k n :: nat
  assumes k: "even k" "k \<ge> 2" and n: "n > 0"
  shows   "real (S k n) = (\<Sum>j\<le>k. real (k choose j) / real (j + 1) * bernoulli (k - j) * real (n ^ (j + 1)))"
proof -
  have "real (S k n) = (\<Sum>r\<le>n-1. real r ^ k)"
    using n unfolding S_def of_nat_sum by (intro sum.cong) auto
  also have "\<dots> = (bernpoly (Suc k) (real n) - bernoulli (Suc k)) / (real k + 1)"
    using n by (subst sum_of_powers) (auto simp: of_nat_diff)
  also have "bernoulli (Suc k) = 0"
    using k by (intro bernoulli_odd_eq_0) auto
  also have "(bernpoly (Suc k) (real n) - 0) / (real k + 1) =
                bernpoly (Suc k) (real n) / real (k + 1)"
    by simp
  also have "bernpoly (Suc k) (real n) / real (k + 1) = (\<Sum>j\<le>Suc k. (Suc k choose j) / (k + 1) * bernoulli (Suc k - j) * n ^ j)"
    by (subst bernpoly_altdef)
       (auto simp: sum_divide_distrib sum_distrib_left sum_distrib_right field_simps simp del: of_nat_Suc)
  also have "\<dots> = (\<Sum>j=1..Suc k. (Suc k choose j) / (k+1) * bernoulli (Suc k - j) * n ^ j)"
    using k by (intro sum.mono_neutral_right) (auto simp: not_le simp: bernoulli_odd_eq_0)
  also have "\<dots> = (\<Sum>j\<le>k. (Suc k choose Suc j) / (k+1) * bernoulli (k - j) * n ^ (j + 1))"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>j. j+1" "\<lambda>j. j-1"]) (auto simp: of_nat_diff)
  also have "\<dots> = (\<Sum>j\<le>k. (k choose j) / (j+1) * bernoulli (k - j) * n ^ (j + 1))"
  proof (intro sum.cong refl, goal_cases)
    case (1 j)
    have "real (Suc j * (Suc k choose Suc j)) = real (Suc k * (k choose j))"
      by (subst Suc_times_binomial_eq) (simp add: mult_ac)
    thus ?case
      unfolding of_nat_mult by (simp add: field_simps del: of_nat_Suc binomial_Suc_Suc)
  qed
  finally show ?thesis .
qed

lemma voronoi_congruence_aux3:
  fixes k n :: nat
  assumes k: "even k" "k \<ge> 2" and n: "n > 0"
  shows   "[D k * S k n = N k * n] (mod (n^2))"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  define A :: "nat \<Rightarrow> rat"
    where "A = (\<lambda>j. of_nat (k choose j) * of_int (N (k - j)) / of_nat (D (k - j)) * of_nat n powi (int j - 1) / of_nat (Suc j))"
  have "real (S k n) = (\<Sum>j\<le>k. real (k choose j) / real (j + 1) * bernoulli (k - j) * real (n ^ (j + 1)))"
    by (rule voronoi_congruence_aux2) fact+
  also have "\<dots> = (\<Sum>j\<le>k. of_rat (A j) * n\<^sup>2)"
    unfolding A_def using n
    by (intro sum.cong)
       (auto simp: power_int_diff power2_eq_square N_def D_def bernoulli_conv_num_denom 
                   of_rat_mult of_rat_divide field_simps of_rat_power simp del: of_nat_Suc)
  also have "\<dots> = (\<Sum>j\<le>k. of_rat (A j)) * real (n ^ 2)"
    by (simp add: sum_distrib_right)
  also have "(\<Sum>j\<le>k. of_rat (A j)) = (\<Sum>j\<in>insert 0 {1..k}. of_rat (A j))"
    using k by (intro sum.cong) auto
  also have "\<dots> = of_rat (A 0) + (\<Sum>j=1..k. of_rat (A j))"
    by (subst sum.insert) auto
  also have "of_rat (A 0) = bernoulli k / n"
    using n by (auto simp: A_def bernoulli_conv_num_denom N_def D_def field_simps
                           of_rat_mult of_rat_divide)
  also have "(bernoulli k / n + (\<Sum>j=1..k. of_rat (A j))) * real (n ^ 2) =
             real n * bernoulli k + (\<Sum>j=1..k. of_rat (A j)) * real (n ^ 2)"
    using n by (simp add: field_simps power2_eq_square)
  finally have eq1: "real (S k n) = real n * bernoulli k + (\<Sum>j=1..k. of_rat (A j)) * real (n ^ 2)" .

  have "\<exists>ab. coprime (fst ab) (snd ab) \<and> coprime (snd ab) (int n) \<and> snd ab > 0 \<and>
          6 * A j = of_int (fst ab) / of_int (snd ab)" (is "\<exists>ab. ?P j ab") if j: "j \<in> {1..k}" for j
  proof (cases "A j = 0")
    case True
    thus ?thesis
      by (intro exI[of _ "(0, 1)"]) auto
  next
    case False
    obtain a b :: int where ab: "coprime a b" "b > 0" "6 * A j = of_int a / of_int b"
      by (metis Fract_of_int_quotient Rat_cases)
    have *: "qmultiplicity p (6 * A j) \<ge> 0" if p: "prime p" "p dvd n" for p
    proof -
      consider "j = 1" | "j = 2" | "j = k - 1" | "odd j" "j \<noteq> k - 1" | "j \<ge> 3" "even j"
        using j by force
      thus ?thesis
      proof cases
        assume [simp]: "j = 1"
        show ?thesis
        proof (cases "k = 2")
          case False
          have "(of_rat (6 * A j) :: real) = 3 * real k * bernoulli (k - 1)"
            by (simp add: A_def N_def D_def of_rat_mult of_rat_divide bernoulli_conv_num_denom)      
          also have "bernoulli (k - 1) = 0"
            using k False by (subst bernoulli_odd_eq_0) auto
          finally show ?thesis
            by simp
        next
          case [simp]: True
          have "qmultiplicity (int p) (6 * A j) = qmultiplicity (int p) 3"
            by (simp add: A_def N_def D_def bernoulli_num_def floor_minus)
          also have "\<dots> \<ge> 0"
            by auto
          finally show ?thesis .
        qed
      next
        assume [simp]: "j = 2"
        have "6 * A j = rat_of_int (2 * n * (k choose 2) * N (k - 2)) / rat_of_int (D (k - 2))"
          by (simp add: A_def)
        also have "qmultiplicity (int p) \<dots> =
                     int (multiplicity (int p) (2 * int n * int (k choose 2) * N (k - 2))) -
                     int (multiplicity (int p) (D (k - 2)))" using k n p
          by (subst qmultiplicity_divide_of_int) (auto simp: D_def N_def bernoulli_num_eq_0_iff)
        also have "\<dots> \<ge> int 1 - int 1"
        proof (intro diff_mono; unfold of_nat_le_iff)
          show "multiplicity (int p) (2 * int n * int (k choose 2) * N (k - 2)) \<ge> 1"
            using k n j p by (intro multiplicity_geI) (auto simp: N_def bernoulli_num_eq_0_iff)
        next
          show "multiplicity (int p) (D (k - 2)) \<le> 1" using p
            by (intro squarefree_imp_multiplicity_prime_le_1)
               (auto simp: D_def squarefree_bernoulli_denom)
        qed
        finally show ?thesis
          by simp
      next
        assume [simp]: "j = k - 1"
        have "6 * A j = -rat_of_nat (3 * n ^ (k - 2))"
          using k binomial_symmetric[of 1 k, symmetric]
          by (auto simp: A_def D_def N_def bernoulli_num_def floor_minus of_nat_diff
                         power_int_def nat_diff_distrib)
        also have "qmultiplicity (int p) \<dots> \<ge> 0"
          unfolding qmultiplicity_minus by (subst qmultiplicity_of_nat) auto
        finally show ?thesis .
      next
        assume "odd j" "j \<noteq> k - 1"
        with k j have "odd (k - j)" "k - j \<noteq> 1"
          by auto
        hence "6 * A j = 0"
          by (auto simp: A_def bernoulli_num_odd_eq_0 N_def)
        thus ?thesis
          by simp
      next
        assume "j \<ge> 3" "even j"
        with j have j: "j \<in> {3..k}"
          by auto
        have "6 * A j = rat_of_int (6 * int (k choose j) * N (k - j) * n ^ (j - 1)) /
                        rat_of_int (int (D (k - j)) * int (j + 1))"
          using j by (simp add: A_def power_int_def nat_diff_distrib algebra_simps)
        also have "qmultiplicity p \<dots> =
                     int (multiplicity (int p) (6 * int (k choose j) * N (k - j) * n ^ (j - 1))) -
                     int (multiplicity (int p) (int (D (k - j)) * int (j + 1)))" using k n p j \<open>even j\<close>
          by (subst qmultiplicity_divide_of_int) (auto simp: D_def N_def bernoulli_num_eq_0_iff)
        also have "\<dots> \<ge> ((if p \<in> {2,3} then 1 else 0) + int j - 1) - ((if p \<in> {2,3} then 1 else 0) + int j - 1)"
        proof (intro diff_mono, goal_cases)
          case 1
          have "multiplicity (int p) (6 * int (k choose j) * N (k - j) * int (n ^ (j - 1))) =
                multiplicity (int p) (6 * (int (k choose j) * N (k - j) * int (n ^ (j - 1))))"
            by (simp add: mult_ac)
          also have "multiplicity (int p) (6 * (int (k choose j) * N (k - j) * int (n ^ (j - 1)))) =
                  multiplicity (int p) (2 * 3) + multiplicity (int p) (int (k choose j) * N (k - j) * int (n ^ (j - 1)))"
            using k n p j \<open>even j\<close>
            by (subst prime_elem_multiplicity_mult_distrib) (auto simp: N_def bernoulli_num_eq_0_iff)
          also have "multiplicity (int p) (2 * 3) = (if p \<in> {2, 3} then 1 else 0)"
            using p by (subst prime_elem_multiplicity_mult_distrib) (auto simp: multiplicity_prime_prime)
          finally have "multiplicity (int p) (6 * int (k choose j) * N (k - j) * int (n ^ (j - 1))) =
                        (if p \<in> {2, 3} then 1 else 0) + 
                        multiplicity (int p) (int (k choose j) * N (k - j) * int (n ^ (j - 1)))" .
          moreover have "p ^ (j - 1) dvd n ^ (j - 1)"
            using p by (intro dvd_power_same)
          hence "multiplicity (int p) (int (k choose j) * N (k - j) * int (n ^ (j - 1))) \<ge> j - 1"
            using j k n \<open>even j\<close> p by (intro multiplicity_geI) (auto simp: N_def bernoulli_num_eq_0_iff)
          hence "int (multiplicity (int p) (int (k choose j) * N (k - j) * int (n ^ (j - 1)))) \<ge> int j - 1"
            using \<open>j \<ge> 3\<close> by linarith
          ultimately show ?case
            by simp
        next
          case 2
          have "multiplicity (int p) (int (D (k - j)) * int (j + 1)) =
                multiplicity (int p) (int (D (k - j))) + multiplicity (int p) (int (j + 1))"
            using p by (subst prime_elem_multiplicity_mult_distrib) (auto simp: D_def)
          moreover have "multiplicity (int p) (int (D (k - j))) \<le> 1" using p
            by (intro squarefree_imp_multiplicity_prime_le_1)
               (auto simp: D_def squarefree_bernoulli_denom)
          moreover have "multiplicity (int p) (int (j + 1)) \<le> (if p \<in> {2, 3} then 1 else 0) + j - 2"
            by (subst multiplicity_int, rule voronoi_congruence_aux1)
               (use p j \<open>even j\<close> in auto)
          hence "int (multiplicity (int p) (int (j + 1))) \<le> (if p \<in> {2, 3} then 1 else 0) + int j - 2"
            using j by auto
          ultimately show ?case
            using \<open>j \<ge> 3\<close> by linarith
        qed
        finally show ?thesis
          by simp
      qed
    qed
    have "coprime b n"
    proof (subst coprime_commute, rule coprimeI_by_prime_factors)
      fix p assume p: "p \<in> prime_factors (int n)"
      hence "p > 0"
        by (auto simp: in_prime_factors_iff prime_gt_0_int)
      hence "qmultiplicity (nat p) (rat_of_int a / rat_of_int b) \<ge> 0"
        using *[of "nat p"] p unfolding ab by (auto simp: in_prime_factors_iff nat_dvd_iff)
      thus "\<not>p dvd b"
        using ab False \<open>p > 0\<close> p by (subst (asm) qmultiplicity_nonneg_iff) auto
    qed (use n in auto)
    with ab show ?thesis
      by (intro exI[of _ "(a, b)"]) auto
  qed
  then obtain f where f: "\<And>j. j \<in> {1..k} \<Longrightarrow> ?P j (f j)" 
    by metis

  define B :: int where "B = Lcm ((snd \<circ> f) ` {1..k})"
  have B: "coprime B n"
    unfolding B_def using f by (auto intro!: coprime_Lcm_left)
  define b' where "b' = (\<lambda>j. B div snd (f j))"
  define T where "T = (\<Sum>j=1..k. fst (f j) * b' j)"

  have "real_of_int (B * int (D k * S k n)) =
         real_of_int B * (real (D k) * bernoulli k) * real n +
         real (D k) / 6 * (\<Sum>j=1..k. real_of_rat (6 * A j * of_int B)) * real n ^ 2"
    unfolding of_int_mult of_nat_mult of_int_of_nat_eq
    by (subst eq1) (simp_all add: algebra_simps of_rat_mult sum_distrib_left)
  also have "real (D k) * bernoulli k = real_of_int (N k)"
    by (simp add: bernoulli_conv_num_denom N_def D_def)
  also have "(\<Sum>j=1..k. real_of_rat (6 * A j * of_int B)) = T"
    unfolding T_def of_int_sum
  proof (intro sum.cong refl, goal_cases)
    case j: (1 j)
    have "6 * A j = of_int (fst (f j)) / of_int (snd (f j))"
      using f[OF j] by auto
    also have "\<dots> * of_int B = of_int (fst (f j)) * (of_int B / of_int (snd (f j)))"
      by simp
    also have "of_int B / of_int (snd (f j)) = (of_int (B div snd (f j)) :: rat)"
      by (subst of_int_div) (use j in \<open>auto simp: B_def\<close>)
    finally show ?case
      by (simp add: of_rat_mult b'_def)
  qed
  also have "real (D k) / 6 = real (D k div 6)"
    by (subst real_of_nat_div) (use k in \<open>auto intro!: six_divides_bernoulli_denom simp: D_def\<close>)
  also have "of_int B * of_int (N k) * real n + real (D k div 6) * of_int T * (real n)\<^sup>2 =
             of_int (B * N k * int n + int (D k div 6) * T * int n ^ 2)"
    by (simp add: algebra_simps)
  finally have "B * int (D k * S k n) = B * N k * int n + int (D k div 6) * T * int n ^ 2"
    by linarith
  hence "[B * int (D k * S k n) = B * N k * int n + int (D k div 6) * T * int n ^ 2] (mod (int n ^ 2))"
    by simp
  also have "[B * N k * int n + int (D k div 6) * T * int n ^ 2 =
              B * N k * int n + int (D k div 6) * T * 0] (mod (int n ^ 2))"
    by (intro cong_add cong_mult cong_refl) (auto simp: Cong.cong_def)
  finally have "[B * int (D k * S k n) = B * (N k * int n)] (mod (int n)\<^sup>2)"
    by (simp add: mult_ac)
  hence "[int (D k * S k n) = N k * int n] (mod (int n)\<^sup>2)"
    by (subst (asm) cong_mult_lcancel) (use B in auto)
  thus ?thesis
    by simp
qed

text \<open>
  Proposition 9.5.20
\<close>
theorem voronoi_congruence:
  fixes k n :: nat and a :: int
  assumes k: "even k" "k \<ge> 2" and n: "n > 0" and a: "coprime a n"
  shows   "[(a^k-1) * N k = k * a^(k-1) * D k * (\<Sum>m=1..<n. m^(k-1) * ((m * a) div n))] (mod n)"
proof -
  define a' where "a' = modular_inverse (int n) a"
  define q r where "q = (\<lambda>m. (a * m) div n)" and "r = (\<lambda>m. (a * m) mod n)"

  have "S k n = (\<Sum>m=1..<n. m ^ k)"
    using k unfolding S_def by (intro sum.mono_neutral_right) auto
  hence "a ^ k * S k n = (\<Sum>m=1..<n. (a * m) ^ k)"
    by (simp add: sum_distrib_left power_mult_distrib)
  also have "[(\<Sum>m=1..<n. (a * m) ^ k) = (\<Sum>m=1..<n. r m ^ k + k * q m * n * (m * a) ^ (k - 1))] (mod n\<^sup>2)"
  proof (rule cong_sum)
    fix m :: nat
    have "[(\<Sum>j\<le>k. int (k choose j) * (q m * n) ^ j * r m ^ (k - j)) = 
           (\<Sum>j\<le>k. if j > 1 then 0 else (k choose j) * q m ^ j * r m ^ (k - j) * n ^ j)] (mod (n\<^sup>2))"
    proof (intro cong_sum, goal_cases)
      case (1 j)
      have dvd: "int n ^ 2 dvd int n ^ j" if "j > 1" for j
        using that by (intro le_imp_power_dvd) auto
      have eq: "int (k choose j) * (q m * n) ^ j * r m ^ (k - j) =
                 int (k choose j) * q m ^ j * r m ^ (k - j) * n ^ j"
        using 1 by (simp add: algebra_simps flip: power_add)
      have "[int (k choose j) * q m ^ j * r m ^ (k - j) * n ^ j = 
                  (if j > 1 then 0 else int (k choose j) * q m ^ j * r m ^ (k - j) * n ^ j)] (mod (n\<^sup>2))"
        using dvd by (auto simp: cong_0_iff)
      thus ?case
        by (simp only: eq)
    qed
    also have "(\<Sum>j\<le>k. if j > 1 then 0 else (k choose j) * q m ^ j * r m ^ (k - j) * n ^ j) =
               (\<Sum>j\<in>{0,1}. (k choose j) * q m ^ j * r m ^ (k - j) * n ^ j)"
      using k by (intro sum.mono_neutral_cong_right) auto
    also have "\<dots> = r m ^ k + (k * q m * n) * r m ^ (k-1)"
      by simp
    also have "[(k * q m * n) * (q m * 0 + r m) ^ (k-1) =
                 (k * q m * n) * (q m * n + r m) ^ (k-1)] (mod (int n)\<^sup>2)"
      by (intro cong_mult_square cong_pow cong_add cong_mult cong_refl) (auto simp: Cong.cong_def)
    hence "[r m ^ k + (k * q m * n) * r m ^ (k-1) =
              r m ^ k + (k * q m * n) * (q m * n + r m) ^ (k-1)] (mod n\<^sup>2)"
      by (intro cong_add) simp_all
    also have "q m * n + r m = (m * a)"
      by (simp add: q_def r_def)
    also have "(\<Sum>j\<le>k. int (k choose j) * (q m * n) ^ j * r m ^ (k - j)) = (q m * n + r m) ^ k"
      by (rule binomial_ring [symmetric])
    also have "q m * n + r m = a * m"
      by (simp add: q_def r_def)
    finally show "[(a * m) ^ k = r m ^ k + k * q m * n * (m * a) ^ (k - 1)] (mod n\<^sup>2)" .
  qed
  also have "(\<Sum>m=1..<n. r m ^ k + k * q m * n * (m * a) ^ (k - 1)) =
             (\<Sum>m=1..<n. r m ^ k) + n * k * a^(k-1) * (\<Sum>m=1..<n. q m * m^(k-1))"
    by (simp add: sum.distrib sum_distrib_left sum_distrib_right mult_ac power_mult_distrib)
  also have "(\<Sum>m=1..<n. r m ^ k) = (\<Sum>m=1..<int n. r m ^ k)"
    by (intro sum.reindex_bij_witness[of _ nat int]) auto
  also have "\<dots> = (\<Sum>m=1..<int n. m ^ k)"
    by (rule sum.reindex_bij_betw)
       (use a bij_betw_int_remainders_mult[of a] in \<open>simp_all add: r_def\<close>)
  also have "\<dots> = of_nat (\<Sum>m=1..<n. m ^ k)"
    unfolding of_nat_sum by (intro sum.reindex_bij_witness[of _ int nat]) auto 
  also have "(\<Sum>m=1..<n. m ^ k) = S k n"
    using k unfolding S_def by (intro sum.mono_neutral_left) auto
  finally have "[a ^ k * S k n - S k n =
                  (S k n + n * k * a^(k-1) * (\<Sum>m=1..<n. q m * m^(k-1))) - S k n] (mod n\<^sup>2)"
    by (intro cong_diff cong_refl)
  hence "[D k * (n * k * a^(k-1) * (\<Sum>m=1..<n. q m * m^(k-1))) = D k * ((a^k-1) * S k n)] (mod n\<^sup>2)"
    by (intro cong_mult[OF cong_refl]) (simp_all add: algebra_simps cong_sym_eq)
  also have "D k * ((a^k-1) * S k n) = (a^k-1) * (D k * S k n)"
    by (simp add: algebra_simps)
  also have "[(a^k-1) * (D k * S k n) = (a^k-1) * (N k * int n)] (mod n\<^sup>2)"
    using k n by (intro cong_mult cong_refl voronoi_congruence_aux3)
  finally have "[n * (k * a^(k-1) * D k * (\<Sum>m=1..<n. q m * m^(k-1))) = n * ((a^k-1) * N k)] (mod n\<^sup>2)"
    by (simp add: mult_ac)
  hence "[k * a^(k-1) * D k * (\<Sum>m=1..<n. q m * m^(k-1)) = (a^k-1) * N k] (mod n)"
    unfolding power2_eq_square of_nat_mult by (rule cong_mult_cancel) (use n in auto)
  thus ?thesis
    by (simp add: mult_ac cong_sym_eq q_def)
qed

corollary voronoi_congruence':
  fixes k p :: nat and a :: int
  assumes k: "even k" "k \<ge> 2" and p: "prime p" "\<not>(p - 1) dvd k" and a: "\<not>p dvd a" "[a ^ k \<noteq> 1] (mod p)"
  shows   "[\<B> k = of_int (k * a^(k-1)) / of_int (a^k - 1) *
                    of_int (\<Sum>m=1..<p. m^(k-1) * ((m * a) div p))] (qmod p)"
proof -
  have "\<not>p dvd D k"
    using p k by (auto simp: D_def prime_dvd_bernoulli_denom_iff)
  hence "coprime p (D k)"
    using p prime_imp_coprime by blast
  moreover have "\<not>p dvd (a ^ k - 1)"
    using a cong_iff_dvd_diff by blast
  hence "coprime p (a ^ k - 1)"
    using p prime_imp_coprime by (metis prime_nat_int_transfer)
  moreover have "coprime p a"
    using p prime_imp_coprime a by (metis prime_nat_int_transfer)
  ultimately have "[of_int (N k) / of_int (D k) = 
         of_int (int k * a ^ (k-1) * (\<Sum>m=1..<p. int m^(k-1) * (int m * a div p))) / of_int (a ^ k - 1)] (qmod p)"
    using assms voronoi_congruence[of k p a]
    by (subst qcong_fraction_iff) (auto simp: D_def coprime_commute prime_gt_0_nat mult_ac)
  thus ?thesis
    by (simp add: bernoulli_rat_def mult_ac N_def D_def of_rat_divide)
qed

corollary voronoi_congruence_harvey:
  fixes k p :: nat and c a :: int and h :: "nat \<Rightarrow> rat"
  assumes k: "even k" "k \<in> {2..p-3}" and p: "prime p" "p \<ge> 5" and c: "c \<in> {0<..<p}" "[c^k \<noteq> 1] (mod p)"
  assumes a: "[a * c = 1] (mod p)"
  defines "h \<equiv> (\<lambda>m. of_int (m - c * ((a * m) mod p)) / of_int p + of_int (c - 1) / 2)"
  shows   "[\<B> k = rat_of_nat k / rat_of_int (1 - c ^ k) * (\<Sum>m=1..<p. rat_of_nat m^(k-1) * h m)] (qmod p)"
proof -
  have [simp]: "p \<noteq> 0"
    using p by auto
  have "odd p"
    using p by (intro prime_odd_nat) auto
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  have [simp]: "D k > 0"
    by (auto simp: D_def bernoulli_denom_pos)
  have "\<not>(p - 1) dvd k"
    using k p by (auto dest!: dvd_imp_le)
  hence [simp]: "coprime (D k) p"
    by (subst coprime_commute, intro prime_imp_coprime)
       (use p k in \<open>auto simp: D_def prime_dvd_bernoulli_denom_iff\<close>)
  have "\<not>p dvd c"
    using c p by (auto dest!: zdvd_imp_le)
  hence "coprime c p"
    using p prime_imp_coprime[of p c] by (auto simp: coprime_commute)
  have "coprime a p"
    using a coprime_iff_invertible_int by auto
  define n where "n = (c * a - 1) div p"
  have "[c * a = 1] (mod p)"
    using a by (simp add: mult_ac)
  hence "p dvd (c * a - 1)"
    by (simp add: cong_iff_dvd_diff)
  hence n: "c * a = n * p + 1"
    unfolding n_def by auto

  have "[c * a = 1] (mod int p)"
    using a by (simp add: mult_ac)
  hence "[(1 ^ k - c ^ k) * N k = ((c * a) ^ k - c ^ k) * N k] (mod p)"
    by (intro cong_mult cong_diff cong_refl cong_pow) (auto simp: cong_sym_eq)
  also have "((c * a) ^ k - c ^ k) * N k = c ^ k * (a ^ k - 1) * N k"
    by (simp add: algebra_simps)
  also have "[(a^k-1) * N k = k * a^(k-1) * D k * (\<Sum>m=1..<p. m^(k-1) * (m * a div p))] (mod p)"
    by (rule voronoi_congruence) (use k p \<open>coprime a p\<close> in auto)
  hence "[c ^ k * ((a^k-1) * N k) = 
          c ^ k * (k * a^(k-1) * D k * (\<Sum>m=1..<p. m^(k-1) * (m * a div p)))] (mod p)"
    by (rule cong_mult[OF cong_refl])
  hence "[c ^ k * (a^k-1) * N k = 
          k * (c ^ k * a^(k-1)) * D k * (\<Sum>m=1..<p. m^(k-1) * (m * a div p))] (mod p)"
    by (simp add: mult_ac)
  also have "c ^ k * a ^ (k - 1) = c * (c * a) ^ (k - 1)"
    using k by (cases k) (auto simp: algebra_simps)
  also have "[k * (c * (c * a) ^ (k-1)) * D k * (\<Sum>m=1..<p. m^(k-1) * (m * a div p)) =
              k * (c * 1 ^ (k-1)) * D k * (\<Sum>m=1..<p. m^(k-1) * (m * a div p))] (mod p)"
    by (intro cong_mult cong_pow cong_refl cong_modular_inverse1) (use a in \<open>simp_all add: mult_ac\<close>)
  also have "k * (c * 1 ^ (k-1)) * D k * (\<Sum>m=1..<p. m^(k-1) * (m * a div p)) =
             D k * (k * (\<Sum>m=1..<p. m^(k-1) * c * (m * a div p)))"
    by (simp add: algebra_simps sum_distrib_left sum_distrib_right)
  finally have "[of_int ((1 - c ^ k) * N k) =
                 of_int (D k * k * (\<Sum>m=1..<p. m^(k-1) * c * (m * a div p)))] (qmod p)"
    using p by (intro cong_imp_qcong) (auto simp: mult_ac prime_gt_1_nat)
  hence "[of_int (1 - c ^ k) * of_int (N k) / of_int (D k) =
                 of_int k * (\<Sum>m=1..<p. of_nat m^(k-1) * (of_int c * of_int (m * a div p)))] (qmod p)"
    using p by (subst qcong_divide_of_int_left_iff) (auto simp: mult_ac)
  also have "(\<Sum>m=1..<p. of_nat m^(k-1) * (of_int c * of_int (m * a div p))) = 
             (\<Sum>m=1..<p. of_nat m^(k-1) * h m + of_int n * of_nat m^k - of_int (c - 1) / 2 * of_nat m^(k-1))"
  proof (intro sum.cong, goal_cases)
    case (2 m)
    have *: "(m * a) div p * p = m * a - ((m * a) mod p)"
      by (metis minus_mod_eq_div_mult)
    have "c * ((m * a) div p * p) = c * a * m - c * ((m * a) mod p)"
      by (subst *) (simp_all add: algebra_simps)
    also have "c * a = n * p + 1"
      by fact
    finally have **: "c * ((m * a) div p) * p = n * m * p + m - c * ((m * a) mod p)"
      by (simp add: algebra_simps)
    have "of_int (c * ((m * a) div p)) = of_int (n * m * p + m - c * ((m * a) mod p)) / (of_int p :: rat)"
      by (subst ** [symmetric]) auto
    also have "\<dots> = h m + of_int (n * m) - of_int (c - 1) / 2"
      by (simp add: h_def field_simps)
    finally have ***: "of_int c * of_int (m * a div p) = h m + of_int (n * m) - of_int (c - 1) / 2"
      by simp
    have "of_nat m^(k-1) * (of_int c * of_int (m * a div p)) =
           of_nat m^(k-1) * h m + of_int n * of_nat (m * m^(k-1)) - of_int (c - 1) / 2 * of_nat m^(k-1)"
      by (subst ***) (auto simp: algebra_simps)
    also have "m * m ^ (k - 1) = m ^ k"
      using k by (cases k) auto
    finally show ?case
      by simp
  qed auto
  also have "\<dots> = (\<Sum>m=1..<p. of_nat m^(k-1) * h m) + of_int n * of_int (int (\<Sum>m=1..<p. m ^ k)) - 
                    of_int (c-1) / 2 * of_int (int (\<Sum>m=1..<p. m^(k-1)))"
    by (simp add: sum.distrib sum_subtractf sum_distrib_left sum_distrib_right)
  also have "(\<Sum>m=1..<p. m ^ k) = S k p"
    using k unfolding S_def by (intro sum.mono_neutral_left) auto
  also have "(\<Sum>m=1..<p. m ^ (k - 1)) = S (k - 1) p"
    using k unfolding S_def by (intro sum.mono_neutral_left) auto
  also have "[of_int k * ((\<Sum>m=1..<p. of_nat m^(k-1) * h m) + of_int n * of_int (int (S k p)) - 
                    of_int (c-1) / 2 * of_int (int (S (k-1) p))) =
              of_int k * ((\<Sum>m=1..<p. of_nat m^(k-1) * h m) + of_int n * of_int (int 0) - 
                    of_int (c-1) / 2 * of_int (int 0))] (qmod p)"
  proof (intro qcong_mult qcong_add qcong_diff cong_imp_qcong qcong_sum qcong_pow qcong_refl cong_int cong_refl)
    have "quotient_of (rat_of_int (c - 1) / 2) = (if even c then c - 1 else c div 2, if even c then 2 else 1)"
      using c by (intro quotient_of_eqI) (auto elim!: oddE)
    thus "coprime (snd (quotient_of (rat_of_int (c - 1) / 2))) (int p)"
      using \<open>odd p\<close> by auto
  next
    fix m assume m: "m \<in> {1..<p}"
    have "[int m - c * (a * int m mod int p) = int m - c * (a * int m)] (mod p)"
      by (intro cong_diff cong_mult cong_refl) auto
    also have "c * (a * int m) = (c * a) * int m"
      by (simp add: mult_ac)
    also have "[int m - (c * a) * int m = int m - 1 * int m] (mod p)"
      using a by (intro cong_diff cong_mult cong_refl) (auto simp: mult_ac)
    finally have "p dvd int m - c * (a * int m mod int p)"
      by (simp add: cong_0_iff)
    then obtain d where d: "int m - c * (a * int m mod int p) = int p * d"
      by (elim dvdE)

    have "h m = of_int (int m - c * (a * int m mod int p)) / of_nat p + of_int (c - 1) / 2"
      by (auto simp: h_def)
    also note d
    also have "rat_of_int (int p * d) / of_nat p = of_int d"
      by simp
    finally have h_eq: "h m = Rat.Fract (2 * d + c - 1) 2"
      by (auto simp: Rat.Fract_of_int_quotient)

    have "snd (quotient_of (h m)) dvd 2"
      unfolding h_eq quotient_of_Fract using dvd_rat_normalize(2) by simp
    with \<open>prime p\<close> \<open>odd p\<close> have "\<not>p dvd snd (quotient_of (h m))"
      by (metis dvd_trans int_dvd_int_iff of_nat_numeral primes_dvd_imp_eq two_is_prime_nat)
    show "coprime (snd (quotient_of (h m))) (int p)"
      by (subst coprime_commute, rule prime_imp_coprime)
         (use p \<open>\<not>p dvd snd (quotient_of (h m))\<close> in auto)
  next
    have *: "[S k p = 0] (mod p)" if "\<not>(p - 1) dvd k" for k
    proof -
      have "k > 0"
        using that by (intro Nat.gr0I) auto
      hence "S k p = (\<Sum>m=1..<p. m ^ k)"
        unfolding S_def by (intro sum.mono_neutral_right) auto
      thus ?thesis
        using sum_of_powers_mod_prime'[of p k] that p by simp
    qed
    show "[S k p = 0] (mod p)"
      using k by (intro *) (auto dest!: dvd_imp_le)
    show "[S (k - 1) p = 0] (mod p)"
      using k by (intro *) (auto dest!: dvd_imp_le)
  qed (use p in \<open>auto simp: prime_gt_1_nat\<close>)
  finally have "[rat_of_int (1 - c ^ k) * rat_of_int (N k) / rat_of_int (int (D k)) =
                 rat_of_nat k * (\<Sum>m=1..<p. rat_of_nat m^(k-1) * h m)] (qmod p)"
    by simp
  moreover have "\<not>p dvd (1 - c ^ k)"
    using c by (auto simp: cong_iff_dvd_diff dvd_diff_commute)
  hence "coprime (1 - c ^ k) (int p)"
    using prime_imp_coprime[of p "1 - c ^ k"] p by (auto simp: coprime_commute)
  ultimately have "[rat_of_int (N k) / rat_of_int (int (D k)) =
                    rat_of_nat k * (\<Sum>m=1..<p. rat_of_nat m^(k-1) * h m) / rat_of_int (1 - c ^ k)] (qmod p)"
    using c by (subst qcong_divide_of_int_right_iff) (auto simp: mult_ac)
  thus ?thesis
    by (simp add: bernoulli_rat_def mult_ac N_def D_def)
qed

corollary voronoi_congruence_harvey':
  fixes k p :: nat and g :: nat and h :: "nat \<Rightarrow> rat" and a :: int
  assumes k: "even k" "k \<in> {2..p-3}" and p: "prime p" "p \<ge> 5"
  assumes g: "residue_primroot p g" "g \<in> {0<..<p}"
  assumes a: "[a * int g = 1] (mod int p)"
  defines "h' \<equiv> (\<lambda>m. rat_of_int (int m mod p - g * ((a * m) mod p)) / of_int p + of_int (int g - 1) / 2)"
  shows   "[\<B> k = 2 * of_nat k / of_int (1 - int g ^ k) *
                    (\<Sum>i=1..(p-1) div 2. of_nat (g^(i*(k-1))) * h' (g^i))] (qmod int p)"
proof -
  define h :: "nat \<Rightarrow> rat" where "h = (\<lambda>m. of_int (m - g * ((a * m) mod p)) / of_int p + of_int (int g - 1) / 2)"
  define m1 where "m1 = g ^ ((p - 1) div 2)"
  have cong_m1: "[int m1 = - 1] (mod int p)"
    unfolding m1_def using residue_primroot_power_cong_neg1[of p g] g p by simp
  from p have [simp]: "p \<noteq> 0"
    by auto
  from p have "odd p"
    by (intro prime_odd_nat) auto
  from g have "coprime g p"
    by (auto simp: residue_primroot_def coprime_commute)
  have "coprime a p"
    using a coprime_iff_invertible_int by auto
  have "\<not>(p - 1) dvd k"
    using k p by (auto dest!: dvd_imp_le)

  have neq1: "[int g ^ k \<noteq> 1] (mod p)"
  proof -
    have "[int g ^ k = 1] (mod p) \<longleftrightarrow> [g ^ k = 1] (mod p)"
      using cong_int_iff by force
    also have "[g ^ k = 1] (mod p) \<longleftrightarrow> ord p g dvd k"
      by (rule ord_divides)
    also have "ord p g = totient p"
      using g(1) unfolding residue_primroot_def by blast
    also have "\<dots> = p - 1"
      using p by (simp add: totient_prime)
    finally show ?thesis
      using \<open>\<not>(p - 1) dvd k\<close> by simp
  qed

  have coprime_h': "coprime (snd (quotient_of (h' (g ^ i)))) (int p)" for i
  proof -
    define b where "b = (int (g ^ i) mod p - int g * (a * int (g ^ i) mod int p)) div p"
    have "[int g * (a * int (g ^ i) mod int p) = int g * (a * int (g ^ i))] (mod p)"
      by (intro cong_mult cong_refl) auto
    also have "int g * (a * int (g ^ i)) = int g * a * int (g ^ i)"
      by (simp add: mult_ac)
    also have "[\<dots> = 1 * int (g ^ i) mod p] (mod p)"
      by (intro cong_mult cong_mod_right) (use a in \<open>auto simp: mult_ac\<close>)
    finally have "p dvd (int (g ^ i) mod p - int g * (a * int (g ^ i) mod int p))"
      by (simp add: cong_iff_dvd_diff dvd_diff_commute)
    hence b: "(int (g ^ i) mod p - int g * (a * int (g ^ i) mod int p)) = p * b"
      unfolding b_def by simp

    have "h' (g ^ i) = Rat.Fract (2 * b + int g - 1) 2"
      unfolding h'_def b by (simp add: field_simps Rat.Fract_of_int_quotient)
    also have "snd (quotient_of \<dots>) dvd 2"
      unfolding quotient_of_Fract by (simp add: dvd_rat_normalize(2))
    finally have "\<not>p dvd snd (quotient_of (h' (g ^ i)))" using \<open>odd p\<close>
      by (metis assms(3) dvd_trans int_dvd_int_iff of_nat_numeral primes_dvd_imp_eq two_is_prime_nat)
    with p show ?thesis
      using prime_imp_coprime coprime_commute prime_nat_int_transfer by metis
  qed

  have bij: "bij_betw (\<lambda>i. g ^ i mod p) {1..p-1} {0<..<p}"
    using residue_primroot_is_generator'[of p g] g p
    by (simp add: totient_prime totatives_prime prime_gt_Suc_0_nat)

  have "[\<B> k = of_nat k / of_int (1 - int g ^ k) * (\<Sum>m=1..<p. of_nat m ^ (k-1) * h m)] (qmod p)"
    unfolding h_def by (rule voronoi_congruence_harvey) (use k p g neq1 a in simp_all)
  also have "(\<Sum>m\<in>{1..<p}. of_nat m ^ (k-1) * h m) = (\<Sum>m\<in>{0<..<p}. of_nat m ^ (k-1) * h (m mod p))"
    by (intro sum.cong) auto
  also have "(\<Sum>m\<in>{0<..<p}. of_nat m ^ (k-1) * h (m mod p)) =
             (\<Sum>i=1..p-1. of_nat (g^i mod p) ^ (k-1) * h (g^i mod p mod p))"
    using bij by (intro sum.reindex_bij_betw [symmetric])
  also have "\<dots> = (\<Sum>i=1..p-1. of_nat (g^i mod p) ^ (k-1) * h (g^i mod p))"
    by simp
  also have "\<dots> = (\<Sum>i=1..p-1. of_nat (g^i mod p) ^ (k-1) * h' (g^i))"
  proof (intro sum.cong, goal_cases)
    case (2 i)
    have "h' (g ^ i) - h (g ^ i mod p mod p) =
            of_nat g * of_int (a * int (g ^ i mod p) mod int p -  a * int (g ^ i) mod int p) / of_int p"
      unfolding h_def h'_def by (simp add: field_simps flip: of_nat_power of_nat_mod)
    also have "[a * int (g ^ i mod p) = a * int (g ^ i)] (mod p)"
      by (intro cong_mult) (auto simp flip: of_nat_power of_nat_mod intro!: cong_int)
    hence "a * int (g ^ i mod p) mod int p = a * int (g ^ i) mod int p"
      by (auto simp: Cong.cong_def)
    finally show ?case
      by simp
  qed auto
  also have "{1..p-1} = {1..(p-1) div 2} \<union> {(p-1) div 2<..p-1}"
    by auto
  also have "(\<Sum>i\<in>\<dots>. of_nat (g^i mod p) ^ (k-1) * h' (g^i)) =
             (\<Sum>i=1..(p-1) div 2. of_nat (g^i mod p) ^ (k-1) * h' (g^i)) +
             (\<Sum>i\<in>{(p-1) div 2<..p-1}. of_nat (g^i mod p) ^ (k-1) * h' (g^i))"
    by (subst sum.union_disjoint) auto
  also have "(\<Sum>i\<in>{(p-1) div 2<..p-1}. of_nat (g^i mod p) ^ (k-1) * h' (g^i)) =
             (\<Sum>i=1..(p-1) div 2. of_nat (g^(i + (p-1) div 2) mod p) ^ (k-1) * h' (g^(i + (p-1) div 2)))"
    using \<open>odd p\<close>
    by (intro sum.reindex_bij_witness[of _ "\<lambda>i. i + (p-1) div 2" "\<lambda>i. i - (p-1) div 2"])
       (auto elim!: oddE)
  also have "[rat_of_nat k / rat_of_int (1 - int g ^ k) *
                ((\<Sum>i=1..(p-1) div 2. of_nat (g^i mod p) ^ (k-1) * h' (g^i)) + \<dots>) = 
              rat_of_nat k / rat_of_int (1 - int g ^ k) * (
                (\<Sum>i=1..(p-1) div 2. of_nat (g^(i*(k-1))) * h' (g^i)) +
                (\<Sum>i=1..(p-1) div 2. (-of_int (g^(i*(k-1)))) * (-h' (g^i))))] (qmod p)"
  proof (intro qcong_divide_of_int qcong_add qcong_sum qcong_refl qcong_mult)
    fix i :: nat
    have "rat_of_int (int (g ^ (i + (p - 1) div 2) mod p) ^ (k - 1)) =
          of_int ((int g ^ i * m1 mod p) ^ (k - 1))"
      by (simp add: power_add m1_def flip: of_nat_power of_nat_mult of_nat_mod)
    also have "[\<dots> = of_int (- (int g ^ (i * (k - 1))))] (qmod p)"
    proof (intro cong_imp_qcong)
      have "[(int g ^ i * int m1 mod int p) ^ (k - 1) = (int g ^ i * (-1)) ^ (k - 1)] (mod p)"
        by (intro cong_mult cong_pow cong_mod_left cong_refl cong_m1)
      also have "(int g ^ i * (-1)) ^ (k - 1) = -(int g ^ (i * (k - 1)))"
        using k by (simp add: power_minus' flip: power_mult)
      finally show "[(int g ^ i * m1 mod p) ^ (k - 1) = -(int g ^ (i * (k - 1)))] (mod p)" .
    qed (use p in auto)
    finally show "[rat_of_nat (g ^ (i + (p - 1) div 2) mod p) ^ (k - 1) = 
                   -(rat_of_int (int (g ^ (i * (k - 1)))))] (qmod int p)" 
      by simp
  next
    fix i :: nat
    have "[int g ^ i * int m1 = int g ^ i * (-1)] (mod p)"
      by (intro cong_mult cong_m1 cong_refl)
    hence "(int g ^ i * int m1 mod p) = -(int g ^ i) mod p"
      by (simp add: Cong.cong_def)
    also have nz: "int g ^ i mod p \<noteq> 0" using \<open>coprime g p\<close>
      by (metis assms(3) cong_cong_mod_int cong_imp_coprime cong_int_iff cong_refl
                coprime_common_divisor_nat coprime_power_left_iff mod_self of_nat_power
                power_0 power_one_right prime_factor_nat prime_power_inj zero_neq_one)
    hence "-(int g ^ i) mod p = int p - (int g ^ i mod p)"
      by (subst zmod_zminus1_eq_if) auto
    finally have eq1: "int g ^ i * int m1 mod int p = int p - int g ^ i mod int p" .

    have "[a * (int g ^ i * int m1) = a * (int g ^ i * (-1))] (mod p)"
      by (intro cong_mult cong_m1 cong_refl)
    hence "(a * (int g ^ i * int m1)) mod p = -(a * int g ^ i) mod p"
      by (simp add: Cong.cong_def)
    also have "(a * int g ^ i) mod p \<noteq> 0" using \<open>coprime a p\<close>
      by (metis nz coprime_commute mod_mod_trivial mult_mod_cancel_left mult_not_zero)
    hence "-(a * int g ^ i) mod p = int p - (a * int g ^ i mod p)"
      by (subst zmod_zminus1_eq_if) auto
    finally have eq2: "a * (int g ^ i * int m1) mod int p = int p - a * int g ^ i mod int p"
      by (simp add: mult_ac)

    have "h' (g ^ (i + (p - 1) div 2)) = h' (g ^ i * m1)"
      by (simp add: power_add m1_def)
    also have "\<dots> = of_int (int p - (int g ^ i mod int p) - int g * (int p - a * int g ^ i mod int p)) /
                     rat_of_nat p + (rat_of_nat g - 1) / 2"
      by (simp add: h'_def eq1 eq2)
    also have "\<dots> = -h' (g ^ i)"
      by (simp add: h'_def field_simps)
    finally have "h' (g ^ (i + (p - 1) div 2)) = - h' (g ^ i)"
      by simp
    moreover have "coprime (snd (quotient_of (- h' (g ^ i)))) (int p)"
      by (metis calculation coprime_h')
    ultimately show "[h' (g ^ (i + (p - 1) div 2)) = -h' (g ^ i)] (qmod int p)"
      by (auto intro!: qcong_refl)
  next
    fix i :: nat
    show "[rat_of_nat (g ^ i mod p) ^ (k - 1) = rat_of_nat (g ^ (i * (k - 1)))] (qmod int p)"
      unfolding of_nat_power [symmetric]
    proof (rule cong_imp_qcong_of_nat)
      have "[(g ^ i mod p) ^ (k - 1) = (g ^ i) ^ (k - 1)] (mod p)"
        by (intro cong_pow) auto
      also have "(g ^ i) ^ (k - 1) = g ^ (i * (k - 1))"
        by (simp add: power_mult)
      finally show "[(g ^ i mod p) ^ (k - 1) = g ^ (i * (k - 1))] (mod p)" .
    qed (use \<open>p \<ge> 5\<close> in auto)
  next
    fix i :: nat
    show "coprime (snd (quotient_of (h' (g ^ i)))) (int p)"
      using coprime_h'[of i] by auto
  next
    show "coprime (1 - int g ^ k) (int p)"
      by (meson assms(3) cong_iff_dvd_diff dvd_diff_commute neq1 residues_prime.intro
            residues_prime.p_coprime_right_int)
    thus "1 - int g ^ k \<noteq> 0"
      using \<open>p \<ge> 5\<close> by fastforce
    thus "1 - int g ^ k \<noteq> 0" .
  qed (use \<open>p \<ge> 5\<close> in auto)
  finally show ?thesis
    by (simp add: mult_ac)
qed

unbundle no_bernoulli_syntax

end

end