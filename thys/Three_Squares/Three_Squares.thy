(*  Title:      Three_Squares/Three_Squares.thy
    Author:     Anton Danilkin
    Author:     Loïc Chevalier
*)

section \<open>Legendre's three squares theorem and its consequences\<close>

theory Three_Squares
  imports "Dirichlet_L.Dirichlet_Theorem" Residues_Properties Quadratic_Forms
begin

subsection \<open>Legendre's three squares theorem\<close>

definition quadratic_residue_alt :: "int \<Rightarrow> int \<Rightarrow> bool" where
"quadratic_residue_alt m a = (\<exists>x y. x\<^sup>2 - a = y * m)"

lemma quadratic_residue_alt_equiv: "quadratic_residue_alt = QuadRes"
  unfolding quadratic_residue_alt_def QuadRes_def
  by (metis cong_iff_dvd_diff cong_modulus_mult dvdE dvd_refl mult.commute)

lemma sq_nat_abs: "(nat \<bar>v\<bar>)\<^sup>2 = nat (v\<^sup>2)"
  by (simp add: nat_power_eq[symmetric])

text \<open>Lemma 1.7 from @{cite nathanson1996}.\<close>

lemma three_squares_using_quadratic_residue:
  fixes n d' :: nat
  assumes "n \<ge> 2"
  assumes "d' > 0"
  assumes "QuadRes (d' * n - 1) (- d')"
  shows "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2"
proof -
  define a where "a \<equiv> d' * n - 1"
  from assms(3) obtain x y where "x\<^sup>2 + int d' = y * int a"
    unfolding a_def quadratic_residue_alt_equiv[symmetric]
              quadratic_residue_alt_def
    by auto
  hence Hxy: "x\<^sup>2 + d' = y * a" by auto
  have "y \<ge> 1"
    using assms Hxy
    unfolding a_def
    by (smt (verit) bot_nat_0.not_eq_extremum mult_le_0_iff of_nat_0_le_iff
                    of_nat_le_0_iff power2_eq_square zero_le_square)
  moreover from Hxy have Hxy\<^sub>2: "d' = y * a - x\<^sup>2" by (simp add: algebra_simps)
  define M where "M \<equiv> mat3 y x 1 x a 0 1 0 n"
  moreover have Msym: "mat_sym M"
    unfolding mat3_sym_def M_def mat3.sel
    by simp
  moreover have Mdet_eq_1: "mat_det M = 1"
  proof -
    have "mat_det M = (y * a - x\<^sup>2) * n - a"
      unfolding mat3_det_def M_def mat3.sel power2_eq_square
      by (simp add: algebra_simps)
    also have "... = int d' * n - a" unfolding Hxy\<^sub>2 by simp
    also have "... = 1" unfolding a_def using assms int_ops by force
    finally show ?thesis .
  qed
  moreover have "mat_det (mat2 y x x a) > 0"
    using Hxy\<^sub>2 assms
    unfolding mat2_det_def power2_eq_square
    by simp
  ultimately have "qf_positive_definite M"
    by (auto simp add: lemma_1_3(4))
  hence "M ~ 1"
    using Msym and Mdet_eq_1
    by (simp add: qf3_det_one_equiv_canonical)
  moreover have "M $$ vec3 0 0 1 = n"
    unfolding M_def qf3_app_def mat3_app_def vec3_dot_def mat3.sel vec3.sel
    by (simp add: algebra_simps)
  hence "n \<in> range (($$) M)" by (metis rangeI)
  ultimately have "n \<in> range (($$) (1 :: mat3))"
    using qf3_equiv_preserves_range by simp
  then obtain u :: vec3 where "1 $$ u = n"
    by auto
  hence "<u | u> = n"
    unfolding qf3_app_def mat3_app_def one_mat3_def
    by simp
  hence "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. int n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2"
    unfolding vec3_dot_def power2_eq_square by metis
  hence "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. n = (nat \<bar>x\<^sub>1\<bar>)\<^sup>2 + (nat \<bar>x\<^sub>2\<bar>)\<^sup>2 + (nat \<bar>x\<^sub>3\<bar>)\<^sup>2"
    unfolding sq_nat_abs
    apply (simp add: nat_add_distrib[symmetric])
    apply (metis nat_int)
    done
  thus "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2" by blast
qed

lemma prime_linear_combination:
  fixes a m :: nat
  assumes "m > 1"
  assumes "coprime a m"
  obtains j :: nat where "prime (a + m * j) \<and> j \<noteq> 0"
proof -
  assume 0: "\<And>j. prime (a + m * j) \<and> j \<noteq> 0 \<Longrightarrow> thesis"

  have 1: "infinite {p. prime p \<and> [p = a] (mod m)}"
    using assms
    by (rule Dirichlet_Theorem.residues_nat.Dirichlet[unfolded residues_nat_def])

  have 2: "finite {j. prime (nat (int a + int m * j)) \<and> j \<le> 0}"
    apply (rule finite_subset[of _ "{- (int a) div (int m)..0}"])
    subgoal
      apply (rule subsetI)
      subgoal for j
      proof -
        assume 1: "j \<in> {j. prime (nat (int a + int m * j)) \<and> j \<le> 0}"
        have "int a + int m * j \<ge> 0" using 1 prime_ge_0_int by force
        hence "int m * j \<ge> - int a" by auto
        hence "j \<ge> (- int a) div int m"
          using assms 1
          by (smt (verit) unique_euclidean_semiring_class.cong_def
                          coprime_crossproduct_nat coprime_iff_invertible_int
                          coprime_int_iff int_distrib(3) int_ops(2) int_ops(7)
                          mem_Collect_eq mult_cancel_right1 zdiv_mono1
                          nonzero_mult_div_cancel_left of_nat_0_eq_iff
                          of_nat_le_0_iff prime_ge_2_int prime_nat_iff_prime)
        thus "j \<in> {- (int a) div (int m)..0}" using 1 by auto
      qed
      done
    subgoal by blast
    done

  have "{p. prime p \<and> [p = a] (mod m)} =
        {p. prime p \<and> (\<exists>j. int p = int a + int m * j)}"
    unfolding cong_sym_eq[of _ a]
    unfolding cong_int_iff[symmetric] cong_iff_lin
    ..
  also have "... = {p. prime p \<and> (\<exists>j. p = nat (int a + int m * j))}"
    by (metis (opaque_lifting) nat_int nat_eq_iff
                               prime_ge_0_int prime_nat_iff_prime)
  also have "... = (\<lambda>j. nat (int a + int m * j)) `
                   {j. prime (nat (int a + int m * j))}"
    by blast
  finally have "infinite ((\<lambda>j. nat (int a + int m * j)) `
                          {j. prime (nat (int a + int m * j))})"
    using 1 by metis
  hence "infinite {j. prime (nat (int a + int m * j))}"
    using finite_imageI by blast
  hence "infinite ({j. prime (nat (int a + int m * j))} -
                   {j. prime (nat (int a + int m * j)) \<and> j \<le> 0})"
    using 2 Diff_infinite_finite by blast
  hence "infinite {j. prime (nat (int a + int m * j)) \<and> j > 0}"
    by (rule back_subst[of infinite]; auto)
  hence "infinite (int ` {j. prime (nat (int a + int m * j)) \<and> j \<noteq> (0 :: nat)})"
    apply (rule back_subst[of infinite])
    unfolding image_def using zero_less_imp_eq_int apply auto
    done
  hence "infinite {j. prime (nat (int a + int m * j)) \<and> (j :: nat) \<noteq> 0}"
    using finite_imageI by blast
  hence "infinite {j. prime (a + m * j) \<and> j \<noteq> 0}"
    apply (rule back_subst[of infinite])
    apply (auto simp add: int_ops nat_plus_as_int)
    done
  thus thesis using 0 not_finite_existsD by blast
qed

text \<open>Lemma 1.8 from @{cite nathanson1996}.\<close>

lemma three_squares_using_mod_four:
  fixes n :: nat
  assumes "n mod 4 = 2"
  shows "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2"
proof -
  have "n > 1" using assms by auto
  have "coprime (n - 1) (4 * n)"
    by (smt (verit, del_insts) Suc_pred assms bot_nat_0.not_eq_extremum
                               coprime_commute coprime_diff_one_right_nat
                               coprime_mod_right_iff coprime_mult_left_iff
                               diff_Suc_1 mod_Suc mod_mult_self1_is_0 mult_0_right
                               numeral_2_eq_2 zero_neq_numeral)
  then obtain j where H_j:
      "prime ((n - 1) + (4 * n) * j) \<and> j \<noteq> 0"
    using prime_linear_combination[of "4 * n" "n - 1"] \<open>n > 1\<close> by auto
  have "j > 0" using H_j by blast

  define d' where "d' \<equiv> 4 * j + 1"
  define p where "p \<equiv> d' * n - 1"
  have "prime p"
    unfolding p_def d'_def
    using conjunct1[OF H_j] apply (rule back_subst[of prime])
    using \<open>n > 1\<close> apply (simp add: algebra_simps nat_minus_as_int nat_plus_as_int)
    done
  have "p mod 4 = 1"
    unfolding p_def
    apply (subst mod_diff_eq_nat)
    subgoal unfolding d'_def using \<open>n > 1\<close> \<open>j > 0\<close> by simp
    subgoal
      apply (subst mod_mult_eq[symmetric])
      unfolding assms d'_def apply simp
      done
    done
  have "d' * n mod 4 = 2"
    using assms p_def d'_def \<open>p mod 4 = 1\<close>
    by (metis mod_mult_cong mod_mult_self4 nat_mult_1)
  hence "d' mod 4 = 1" using assms by (simp add: d'_def)

  have "QuadRes p (- d')"
  proof -
    have d'_expansion: "d' = (\<Prod>q\<in>prime_factors d'. q ^ multiplicity q d')"
      using prime_factorization_nat unfolding d'_def by auto

    have "odd d'" unfolding d'_def by simp
    hence d'_prime_factors_odd: "q \<in> prime_factors d' \<Longrightarrow> odd q" for q
      by fastforce

    have d'_prime_factors_gt_2: "q \<in> prime_factors d' \<Longrightarrow> q > 2" for q
      using d'_prime_factors_odd
      by (metis even_numeral in_prime_factors_imp_prime
                order_less_le prime_ge_2_nat)

    have "[p = - 1] (mod d')"
      unfolding p_def cong_iff_dvd_diff apply simp
      using \<open>n > 1\<close> apply (smt (verit) Suc_as_int Suc_pred add_gr_0 d'_def
                                       dvd_nat_abs_iff dvd_triv_left
                                       less_numeral_extra(1) mult_pos_pos
                                       of_nat_less_0_iff order_le_less_trans
                                       zero_less_one_class.zero_le_one)
      done
    hence d'_prime_factors_2_p_mod:
        "q \<in> prime_factors d' \<Longrightarrow> [p = - 1] (mod q)" for q
      by (rule cong_dvd_modulus; auto)

    have "d' mod 4 = (\<Prod>q\<in>prime_factors d'. q ^ multiplicity q d') mod 4"
      using d'_expansion by argo
    also have "... = (\<Prod>q\<in>prime_factors d'. (q mod 4) ^ multiplicity q d') mod 4"
      apply (subst mod_prod_eq[symmetric])
      apply (subst power_mod[symmetric])
      apply (subst mod_prod_eq)
      apply blast
      done
    also have "... = (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 4)}.
                      (q mod 4) ^ multiplicity q d') mod 4"
      apply (rule arg_cong[of _ _ "\<lambda>x. x mod 4"])
      apply (rule prod.mono_neutral_right)
      subgoal by blast
      subgoal by blast
      subgoal
        unfolding unique_euclidean_semiring_class.cong_def
        apply (rule ballI)
        using d'_prime_factors_odd apply simp
        apply (metis One_nat_def dvd_0_right even_even_mod_4_iff
                     even_numeral mod_exhaust_less_4)
        done
      done
    also have "... = (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 4)}.
                      ((int q) mod 4) ^ multiplicity q d') mod 4"
      by (simp add: int_ops)
    also have "... = (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 4)}.
                      ((- 1) mod 4) ^ multiplicity q d') mod 4"
      apply (rule arg_cong[of _ _ "\<lambda>x. x mod 4"])
      apply (rule prod.cong[OF refl])
      unfolding unique_euclidean_semiring_class.cong_def nat_mod_as_int apply simp
      apply (metis nat_int of_nat_mod of_nat_numeral)
      done
    also have "... = (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 4)}.
                      (- 1) ^ multiplicity q d') mod 4"
      apply (subst mod_prod_eq[symmetric])
      apply (subst power_mod)
      apply (subst mod_prod_eq)
      apply blast
      done
    finally have "[\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 4)}.
            (- 1) ^ multiplicity q d' = 1 :: int] (mod 4)"
      using \<open>d' mod 4 = 1\<close>
      by (simp add: unique_euclidean_semiring_class.cong_def)
    hence prod_prime_factors_minus_one:
        "(\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 4)}.
          (- 1) ^ multiplicity q d') = (1 :: int)"
      unfolding power_sum[symmetric]
      unfolding minus_one_power_iff unique_euclidean_semiring_class.cong_def
      by presburger

    have "p > 2" using \<open>prime p\<close> \<open>p mod 4 = 1\<close> nat_less_le prime_ge_2_nat by force

    have d'_prime_factors_Legendre:
      "q \<in> prime_factors d' \<Longrightarrow>
       Legendre p q = Legendre q p" for q
    proof -
      assume "q \<in> prime_factors d'"
      have "prime q" using \<open>q \<in> prime_factors d'\<close> by blast
      have "q > 2" using d'_prime_factors_gt_2 \<open>q \<in> prime_factors d'\<close> by blast
      show "Legendre p q = Legendre q p"
        using \<open>prime p\<close> \<open>p > 2\<close> \<open>p mod 4 = 1\<close>
              \<open>prime q\<close> \<open>q > 2\<close> Legendre_equal[of p q]
        unfolding unique_euclidean_semiring_class.cong_def
        using zmod_int[of p 4]
        by auto
    qed

    have "Legendre (- d') p = Legendre (- 1) p * Legendre d' p"
      using \<open>prime p\<close> Legendre_mult[of p "- 1" d'] by auto
    also have "... = Legendre d' p"
      using \<open>prime p\<close> \<open>p > 2\<close> \<open>p mod 4 = 1\<close> Legendre_minus_one[of p]
      unfolding unique_euclidean_semiring_class.cong_def nat_mod_as_int
      by auto
    also have "... = (\<Prod>q\<in>prime_factors d'. Legendre (q ^ multiplicity q d') p)"
      apply (subst d'_expansion)
      using \<open>prime p\<close> \<open>p > 2\<close> Legendre_prod[of p] apply auto
      done
    also have "... = (\<Prod>q\<in>prime_factors d'. (Legendre q p) ^ multiplicity q d')"
      using \<open>prime p\<close> \<open>p > 2\<close> Legendre_power by auto
    also have "... = (\<Prod>q\<in>prime_factors d'. (Legendre p q) ^ multiplicity q d')"
      using d'_prime_factors_Legendre by auto
    also have "... = (\<Prod>q\<in>prime_factors d'.
                      (Legendre (- 1) q) ^ multiplicity q d')"
      apply (rule prod.cong[OF refl])
      using d'_prime_factors_2_p_mod apply (metis Legendre_cong)
      done
    also have "... = (\<Prod>q\<in>prime_factors d'.
                      (if [q = 1] (mod 4) then 1 else - 1) ^ multiplicity q d')"
      apply (rule prod.cong[OF refl])
      subgoal for q
        using Legendre_minus_one_alt[of q] d'_prime_factors_gt_2[of q]
        by (smt (verit) cong_int_iff in_prime_factors_iff int_eq_iff_numeral
                        less_imp_of_nat_less numeral_Bit0 numeral_One of_nat_1
                        prime_nat_int_transfer)
      done
    also have "... = (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 4)}.
                      (if [q = 1] (mod 4) then 1 else - 1) ^ multiplicity q d')"
      apply (rule prod.mono_neutral_right)
      subgoal by blast
      subgoal by blast
      subgoal
        unfolding unique_euclidean_semiring_class.cong_def
        apply (rule ballI)
        using d'_prime_factors_odd apply simp
        apply (metis One_nat_def dvd_0_right even_even_mod_4_iff
                     even_numeral mod_exhaust_less_4)
        done
      done
    also have "... = (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 4)}.
                      (- 1) ^ multiplicity q d')"
      by (rule prod.cong[OF refl];
          simp add: unique_euclidean_semiring_class.cong_def)
    also have "... = 1" using prod_prime_factors_minus_one .
    finally show "QuadRes p (- d')"
      unfolding Legendre_def
      by (metis one_neq_neg_one one_neq_zero)
  qed
  thus "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2"
    using \<open>n > 1\<close> three_squares_using_quadratic_residue[of n d']
    unfolding d'_def p_def
    by auto
qed

lemma three_mod_eight_power_iff:
  fixes n :: nat
  shows "(3 :: int) ^ n mod 8 = (if even n then 1 else 3)"
proof (induction n)
  case 0
  thus ?case by auto
next
  case (Suc n)
  thus ?case
    apply (cases "even n")
    subgoal
      using mod_mult_left_eq[of 3 8 "3 ^ n"] apply simp
      apply presburger
      done
    subgoal
      using mod_mult_left_eq[of 3 8 "3 * 3 ^ n"] apply simp
      apply presburger
      done
    done
qed

text \<open>Lemma 1.9 from @{cite nathanson1996}.\<close>

lemma three_squares_using_mod_eight:
  fixes n :: nat
  assumes "n mod 8 \<in> {1, 3, 5}"
  shows "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2"
proof cases
  assume "n = 1"
  hence "n = 1\<^sup>2 + 0\<^sup>2 + 0\<^sup>2" unfolding power2_eq_square by auto
  thus "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2" by blast
next
  assume "n \<noteq> 1"
  hence "n > 1" using assms by auto

  have H_n:
    "(n mod 8 = 1 \<Longrightarrow> P) \<Longrightarrow>
     (n mod 8 = 3 \<Longrightarrow> P) \<Longrightarrow>
     (n mod 8 = 5 \<Longrightarrow> P) \<Longrightarrow> P" for P
    using assms by auto

  define c :: nat where "c \<equiv> if n mod 8 = 3 then 1 else 3"
  have "c * n \<ge> 1" unfolding c_def using \<open>n > 1\<close> by auto

  obtain k where H_k: "2 * k = c * n - 1"
    using H_n
    unfolding c_def
    by (smt (verit, ccfv_threshold) dvd_mod even_mult_iff even_numeral
                                    odd_numeral odd_one odd_two_times_div_two_nat)
  have k_mod_4: "k mod 4 = (if n mod 8 = 5 then 3 else 1)" (is "k mod 4 = ?v")
  proof -
    have "c * n mod 8 = (if n mod 8 = 5 then 7 else 3)"
    using H_n
    proof cases
      assume "n mod 8 = 1"
      have "3 * n mod 8 = 3"
        using \<open>n mod 8 = 1\<close> mod_mult_right_eq[of 3 n 8]
        by auto
      thus ?thesis unfolding c_def using \<open>n mod 8 = 1\<close> by auto
    next
      assume "n mod 8 = 3"
      thus ?thesis unfolding c_def by auto
    next
      assume "n mod 8 = 5"
      have "3 * n mod 8 = 7"
        using \<open>n mod 8 = 5\<close> mod_mult_right_eq[of 3 n 8]
        by auto
      thus ?thesis unfolding c_def using \<open>n mod 8 = 5\<close> by auto
    qed
    hence "2 * k mod 8 = (if n mod 8 = 5 then 6 else 2)"
      unfolding H_k using \<open>c * n \<ge> 1\<close> mod_diff_eq_nat by simp
    hence "2 * (k mod 4) = 2 * ?v" by (simp add: mult_mod_right)
    thus ?thesis by simp
  qed

  have "coprime k (4 * n)"
    using k_mod_4 H_k \<open>c * n \<ge> 1\<close>
    by (metis One_nat_def coprime_Suc_left_nat coprime_commute
              coprime_diff_one_right_nat coprime_mod_left_iff
              coprime_mult_right_iff mult_2_right numeral_2_eq_2 numeral_3_eq_3
              numeral_Bit0 order_less_le_trans zero_less_one zero_neq_numeral)
  then obtain j where H_j:
      "prime (k + (4 * n) * j) \<and> j \<noteq> 0"
    using prime_linear_combination[of k "n - 1"] \<open>n > 1\<close>
    by (metis One_nat_def Suc_leI bot_nat_0.not_eq_extremum mult_is_0
              nat_1_eq_mult_iff nat_less_le prime_linear_combination
              zero_neq_numeral)
  have "j > 0" using H_j by blast

  define p where "p \<equiv> k + (4 * n) * j"
  have "prime p"
    unfolding p_def
    using conjunct1[OF H_j] apply (rule back_subst[of prime])
    apply (simp add: int_ops nat_plus_as_int)
    done
  have "[p = k] (mod 4 * n)"
    unfolding p_def unique_euclidean_semiring_class.cong_def by auto

  have "p > 2"
    using \<open>prime p\<close> \<open>[p = k] (mod 4 * n)\<close> \<open>coprime k (4 * n)\<close>
    by (metis cong_dvd_iff cong_dvd_modulus_nat coprime_common_divisor_nat
              dvd_mult2 even_numeral le_neq_implies_less odd_one prime_ge_2_nat)

  define d' where "d' \<equiv> 8 * j + c"
  have "d' > 1" unfolding d'_def using \<open>j > 0\<close> by simp
  have H_2_p: "2 * p = d' * n - 1"
    unfolding p_def d'_def
    using \<open>c * n \<ge> 1\<close> H_k
    by (smt (verit, del_insts) Nat.add_diff_assoc add.commute
                               add_mult_distrib mult.commute mult_2 numeral_Bit0)

  have "QuadRes p (- d')"
  proof -
    have d'_expansion: "d' = (\<Prod>q\<in>prime_factors d'. q ^ multiplicity q d')"
      using \<open>j > 0\<close> prime_factorization_nat unfolding d'_def by auto

    have "odd d'" unfolding c_def d'_def by simp
    hence d'_prime_factors_odd: "q \<in> prime_factors d' \<Longrightarrow> odd q" for q
      by fastforce

    have d'_prime_factors_gt_2: "q \<in> prime_factors d' \<Longrightarrow> q > 2" for q
      using d'_prime_factors_odd
      by (metis even_numeral in_prime_factors_imp_prime
                order_less_le prime_ge_2_nat)

    have "[2 * p = - 1] (mod d')"
      using \<open>n > 1\<close> \<open>d' > 1\<close>
      unfolding H_2_p cong_iff_dvd_diff
      by (simp add: int_ops less_1_mult order_less_imp_not_less)
    hence d'_prime_factors_2_p_mod:
        "q \<in> prime_factors d' \<Longrightarrow> [2 * p = - 1] (mod q)" for q
      by (rule cong_dvd_modulus; auto)

    have "q \<in> prime_factors d' \<Longrightarrow> coprime (2 * int p) q" for q
      using d'_prime_factors_2_p_mod
      by (metis cong_imp_coprime cong_sym coprime_1_left
                coprime_minus_left_iff mult_2 of_nat_add)
    hence d'_prime_factors_coprime:
        "q \<in> prime_factors d' \<Longrightarrow> coprime (int p) q" for q
      using d'_expansion by auto

    have Legendre_using_quadratic_reciprocity:
      "Legendre (- d') p =
       (\<Prod>q\<in>prime_factors d'. (Legendre p q) ^ multiplicity q d')"
    proof cases
      assume "n mod 8 \<in> {1, 3}"

      have "k mod 4 = 1" using \<open>n mod 8 \<in> {1, 3}\<close> k_mod_4 by auto
      hence "p mod 4 = 1"
        using \<open>[p = k] (mod 4 * n)\<close>
        by (metis unique_euclidean_semiring_class.cong_def cong_modulus_mult_nat)
      hence "[int p = 1] (mod 4)"
        by (metis cong_mod_left cong_refl int_ops(2) int_ops(3) of_nat_mod)

      have d'_prime_factors_Legendre:
        "q \<in> prime_factors d' \<Longrightarrow>
         Legendre p q = Legendre q p" for q
      proof -
        assume "q \<in> prime_factors d'"
        have "prime q" using \<open>q \<in> prime_factors d'\<close> by blast
        have "q > 2" using d'_prime_factors_gt_2 \<open>q \<in> prime_factors d'\<close> by blast
        show "Legendre p q = Legendre q p"
          using \<open>prime p\<close> \<open>p > 2\<close> \<open>[int p = 1] (mod 4)\<close>
                \<open>prime q\<close> \<open>q > 2\<close> Legendre_equal[of p q]
          by auto
      qed

      have "Legendre (- d') p = Legendre (- 1) p * Legendre d' p"
        using \<open>prime p\<close> Legendre_mult[of p "- 1" d'] by auto
      also have "... = Legendre d' p"
        using \<open>prime p\<close> \<open>p > 2\<close> \<open>[int p = 1] (mod 4)\<close> Legendre_minus_one
        by auto
      also have "... = (\<Prod>q\<in>prime_factors d'. Legendre (q ^ multiplicity q d') p)"
        apply (subst d'_expansion)
        using \<open>prime p\<close> \<open>p > 2\<close> Legendre_prod[of p] apply auto
        done
      also have "... = (\<Prod>q\<in>prime_factors d'. (Legendre q p) ^ multiplicity q d')"
        using \<open>prime p\<close> \<open>p > 2\<close> Legendre_power by auto
      also have "... = (\<Prod>q\<in>prime_factors d'. (Legendre p q) ^ multiplicity q d')"
        using d'_prime_factors_Legendre by auto
      finally show ?thesis .
    next
      assume "n mod 8 \<notin> {1, 3}"
      hence "n mod 8 = 5" using assms by auto

      have "[p = 3] (mod 4)"
        using \<open>n mod 8 = 5\<close> k_mod_4 \<open>[p = k] (mod 4 * n)\<close>
        by (metis cong_mod_right cong_modulus_mult_nat)
      have "[d' = 3] (mod 8)"
        using \<open>n mod 8 = 5\<close>
        unfolding d'_def c_def cong_iff_dvd_diff
        by (simp add: unique_euclidean_semiring_class.cong_def)
      have "[d' = - 1] (mod 4)"
        using \<open>[d' = 3] (mod 8)\<close> cong_modulus_mult[of d' 3 4 2]
        unfolding unique_euclidean_semiring_class.cong_def nat_mod_as_int
        by auto

      have d'_prime_factors_cases:
        "q \<in> prime_factors d' \<Longrightarrow>
         multiplicity q d' = 0 \<or> [q = 1] (mod 4) \<or> [q = 3] (mod 4)" for q
      proof -
        assume "q \<in> prime_factors d'"
        consider "[q = 0] (mod 4)"
               | "[q = 1] (mod 4)"
               | "[q = 2] (mod 4)"
               | "[q = 3] (mod 4)"
          unfolding unique_euclidean_semiring_class.cong_def by (simp; linarith)
        thus "multiplicity q d' = 0 \<or> [q = 1] (mod 4) \<or> [q = 3] (mod 4)"
        proof cases
          assume "[q = 0] (mod 4)"
          hence False
            using d'_prime_factors_odd \<open>q \<in> prime_factors d'\<close>
            by (meson cong_0_iff dvd_trans even_numeral)
          thus "multiplicity q d' = 0 \<or> [q = 1] (mod 4) \<or> [q = 3] (mod 4)"
            by blast
        next
          assume "[q = 1] (mod 4)"
          thus "multiplicity q d' = 0 \<or> [q = 1] (mod 4) \<or> [q = 3] (mod 4)"
            by blast
        next
          assume "[q = 2] (mod 4)"
          hence "q = 2"
            using d'_prime_factors_odd \<open>q \<in> prime_factors d'\<close>
            by (metis unique_euclidean_semiring_class.cong_def
                      dvd_mod_iff even_numeral)
          thus "multiplicity q d' = 0 \<or> [q = 1] (mod 4) \<or> [q = 3] (mod 4)"
            by (simp add: \<open>odd d'\<close> not_dvd_imp_multiplicity_0)
        next
          assume "[q = 3] (mod 4)"
          thus "multiplicity q d' = 0 \<or> [q = 1] (mod 4) \<or> [q = 3] (mod 4)"
            by blast
        qed
      qed

      have "d' = (\<Prod>q\<in>{q\<in>prime_factors d'. True}. q ^ multiplicity q d')"
        using d'_expansion by auto
      also have "... = (\<Prod>q\<in>{q\<in>prime_factors d'.
                        multiplicity q d' = 0 \<or> [q = 1] (mod 4) \<or> [q = 3] (mod 4)}.
                        q ^ multiplicity q d')"
        using d'_prime_factors_cases by meson
      also have "... = (\<Prod>q\<in>{q\<in>prime_factors d'. multiplicity q d' = 0} \<union>
                        {q\<in>prime_factors d'. [q = 1] (mod 4) \<or>
                        [q = 3] (mod 4)}. q ^ multiplicity q d')"
        by (rule prod.cong; blast)
      also have "... = (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 1] (mod 4) \<or>
                        [q = 3] (mod 4)}. q ^ multiplicity q d')"
        by (rule prod.mono_neutral_left[symmetric]; auto)
      also have "... = (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 1] (mod 4)} \<union>
                            {q\<in>prime_factors d'. [q = 3] (mod 4)}.
                        q ^ multiplicity q d')"
        by (rule prod.cong; blast)
      also have "... = (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 1] (mod 4)}.
                        q ^ multiplicity q d') *
                       (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
                        q ^ multiplicity q d')"
        by (rule prod.union_disjoint;
            auto simp add: unique_euclidean_semiring_class.cong_def)
      finally have d'_expansion_mod_4:
        "d' = (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 1] (mod 4)}.
               q ^ multiplicity q d') *
              (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
               q ^ multiplicity q d')" .

      have "int d' mod 4 = int ((\<Prod>q\<in>{q\<in>prime_factors d'. [q = 1] (mod 4)}.
                                 q ^ multiplicity q d') *
                                (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
                                 q ^ multiplicity q d') mod 4)"
        using d'_expansion_mod_4
        by presburger
      also have "... = ((\<Prod>q\<in>{q\<in>prime_factors d'. [q = 1] (mod 4)}.
                         ((q mod 4) ^ multiplicity q d') mod 4) mod 4) *
                       ((\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
                         ((q mod 4) ^ multiplicity q d') mod 4) mod 4) mod 4"
        unfolding mod_mult_eq mod_prod_eq power_mod ..
      also have "... = int (((\<Prod>q\<in>{q\<in>prime_factors d'. [q = 1] (mod 4)}.
                              (1 ^ multiplicity q d') mod 4) mod 4) *
                            ((\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
                              (3 ^ multiplicity q d') mod 4) mod 4) mod 4)"
        unfolding unique_euclidean_semiring_class.cong_def by auto
      also have "... = ((\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
                         (((int 3) mod 4) ^ multiplicity q d') mod 4) mod 4) mod 4"
        by (simp add: int_ops)
      also have "... = ((\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
                         (((- 1) mod 4) ^ multiplicity q d') mod 4) mod 4) mod 4"
        by auto
      also have "... = (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
                        ((- 1) ^ multiplicity q d')) mod 4"
        unfolding power_mod mod_prod_eq mod_mod_trivial ..
      finally have "[d' = \<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
                          ((- 1) ^ multiplicity q d')] (mod 4)"
        unfolding unique_euclidean_semiring_class.cong_def .
      hence "[\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
              ((- 1) ^ multiplicity q d') = - 1 :: int] (mod 4)"
        using \<open>[d' = - 1] (mod 4)\<close>
        unfolding unique_euclidean_semiring_class.cong_def
        by argo
      hence prod_d'_prime_factors_q_3_mod_4_minus_one:
          "(\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
            ((- 1) ^ multiplicity q d')) = (- 1 :: int)"
        unfolding power_sum[symmetric]
        unfolding minus_one_power_iff unique_euclidean_semiring_class.cong_def
        by auto

      have d'_prime_factors_q_1_mod_4_Legendre:
        "q \<in> prime_factors d' \<Longrightarrow>
         [q = 1] (mod 4) \<Longrightarrow>
         Legendre p q = Legendre q p" for q
      proof -
        assume "q \<in> prime_factors d'"
        assume "[q = 1] (mod 4)"
        have "prime q" using \<open>q \<in> prime_factors d'\<close> by blast
        have "q > 2" using d'_prime_factors_gt_2 \<open>q \<in> prime_factors d'\<close> by blast
        show "Legendre p q = Legendre q p"
          using \<open>prime p\<close> \<open>p > 2\<close> \<open>[p = 3] (mod 4)\<close> \<open>[q = 1] (mod 4)\<close>
                \<open>prime q\<close> \<open>q > 2\<close> Legendre_equal[of p q]
          unfolding unique_euclidean_semiring_class.cong_def
          using zmod_int[of q 4]
          by auto
      qed

      have d'_prime_factors_q_3_mod_4_Legendre:
        "q \<in> prime_factors d' \<Longrightarrow>
         [q = 3] (mod 4) \<Longrightarrow>
         Legendre p q = - Legendre q p" for q
      proof -
        assume "q \<in> prime_factors d'"
        assume "[q = 3] (mod 4)"
        have "prime q" using \<open>q \<in> prime_factors d'\<close> by blast
        have "q > 2" using d'_prime_factors_gt_2 \<open>q \<in> prime_factors d'\<close> by blast
        have "p \<noteq> q"
          using d'_prime_factors_coprime[of q] \<open>q \<in> prime_factors d'\<close> \<open>prime p\<close>
          by auto
        show "Legendre p q = - Legendre q p"
          using \<open>prime p\<close> \<open>p > 2\<close> \<open>[p = 3] (mod 4)\<close> \<open>[q = 3] (mod 4)\<close>
                \<open>prime q\<close> \<open>q > 2\<close> \<open>p \<noteq> q\<close> Legendre_opposite[of p q]
          unfolding unique_euclidean_semiring_class.cong_def
          using zmod_int[of p 4] zmod_int[of q 4]
          by fastforce
      qed

      have d'_prime_factors_q_0_2_mod_4:
          "q \<in> prime_factors d' \<Longrightarrow>
           ([q = 0] (mod 4) \<or> [q = 2] (mod 4)) \<Longrightarrow>
           Legendre p q = 1" for q
        unfolding unique_euclidean_semiring_class.cong_def
        using d'_prime_factors_odd mod_mod_cancel[of 2 4 q]
        by fastforce

      have "Legendre (- d') p = Legendre (- 1) p * Legendre d' p"
        using \<open>prime p\<close> Legendre_mult[of p "- 1" d'] by auto
      also have "... = - Legendre d' p"
        using \<open>prime p\<close> \<open>p > 2\<close> \<open>[p = 3] (mod 4)\<close> Legendre_minus_one[of p]
        unfolding unique_euclidean_semiring_class.cong_def nat_mod_as_int
        by (auto simp add: cong_0_iff Legendre_def)
      also have "... = - (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 1] (mod 4)}.
                          (Legendre q p) ^ multiplicity q d') *
                         (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
                          (Legendre q p) ^ multiplicity q d')"
        apply (subst d'_expansion_mod_4)
        using \<open>prime p\<close> \<open>p > 2\<close> Legendre_mult[of p]
              Legendre_prod[of p "\<lambda>q. q ^ multiplicity q d'"] Legendre_power[of p]
        apply simp
        done
      also have "... = - (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 1] (mod 4)}.
                          (Legendre p q) ^ multiplicity q d') *
                         (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
                          (- Legendre p q) ^ multiplicity q d')"
        using d'_prime_factors_q_1_mod_4_Legendre
              d'_prime_factors_q_3_mod_4_Legendre
        by auto
      also have "... = - (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 1] (mod 4)}.
                          (Legendre p q) ^ multiplicity q d') *
                         (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
                          (Legendre p q * (- 1)) ^ multiplicity q d')"
        by auto
      also have "... = - (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 1] (mod 4)}.
                          (Legendre p q) ^ multiplicity q d') *
                         (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
                          (Legendre p q) ^ multiplicity q d') *
                         (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
                          (- 1) ^ multiplicity q d')"
        unfolding power_mult_distrib prod.distrib by auto
      also have "... = (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 1] (mod 4)}.
                        (Legendre p q) ^ multiplicity q d') *
                       (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
                        (Legendre p q) ^ multiplicity q d')"
        unfolding prod_d'_prime_factors_q_3_mod_4_minus_one by auto
      also have "... = (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 0] (mod 4)}.
                        (Legendre p q) ^ multiplicity q d') *
                       (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 1] (mod 4)}.
                        (Legendre p q) ^ multiplicity q d') *
                       (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 2] (mod 4)}.
                        (Legendre p q) ^ multiplicity q d') *
                       (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 3] (mod 4)}.
                        (Legendre p q) ^ multiplicity q d')"
        using d'_prime_factors_q_0_2_mod_4 by auto
      also have "... = (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 0] (mod 4)} \<union>
                            {q\<in>prime_factors d'. [q = 1] (mod 4)}.
                        (Legendre p q) ^ multiplicity q d') *
                       (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 2] (mod 4)} \<union>
                            {q\<in>prime_factors d'. [q = 3] (mod 4)}.
                        (Legendre p q) ^ multiplicity q d')"
        using prod.union_disjoint[of "{q\<in>prime_factors d'. [q = 0] (mod 4)}"
                                     "{q\<in>prime_factors d'. [q = 1] (mod 4)}"
                                     "\<lambda>q. (Legendre p (int q)) ^
                                          multiplicity q d'"]
              prod.union_disjoint[of "{q\<in>prime_factors d'. [q = 2] (mod 4)}"
                                     "{q\<in>prime_factors d'. [q = 3] (mod 4)}"
                                     "\<lambda>q. (Legendre p (int q)) ^
                                          multiplicity q d'"]
        by (fastforce simp add: unique_euclidean_semiring_class.cong_def)
      also have "... = (\<Prod>q\<in>({q\<in>prime_factors d'. [q = 0] (mod 4)} \<union>
                             {q\<in>prime_factors d'. [q = 1] (mod 4)}) \<union>
                            ({q\<in>prime_factors d'. [q = 2] (mod 4)} \<union>
                             {q\<in>prime_factors d'. [q = 3] (mod 4)}).
                        (Legendre p q) ^ multiplicity q d')"
        by (rule prod.union_disjoint[symmetric];
            auto simp add: unique_euclidean_semiring_class.cong_def)
      also have "... = (\<Prod>q\<in>{q\<in>prime_factors d'.
                             [q = 0] (mod 4) \<or> [q = 1] (mod 4) \<or>
                             [q = 2] (mod 4) \<or> [q = 3] (mod 4)}.
                        (Legendre p q) ^ multiplicity q d')"
        by (rule prod.cong; auto)
      also have "... = (\<Prod>q\<in>prime_factors d'. (Legendre p q) ^ multiplicity q d')"
        by (rule prod.cong;
            auto simp add: unique_euclidean_semiring_class.cong_def)
      finally show ?thesis .
    qed

    have "q \<in> prime_factors d' \<Longrightarrow> Legendre 4 q = 1" for q
    proof -
      assume "q \<in> prime_factors d'"
      have "q dvd 4 \<Longrightarrow> q \<le> 4" by (simp add: dvd_imp_le)
      hence "q dvd 4 \<Longrightarrow> q \<in> {0, 1, 2, 3, 4}" by auto
      hence "q dvd 4 \<Longrightarrow> q \<in> {1, 2, 4}" by auto
      hence "\<not> q dvd 4" using \<open>q \<in> prime_factors d'\<close> d'_prime_factors_odd[of q]
        by (metis empty_iff even_numeral in_prime_factors_imp_prime
                  insert_iff not_prime_1)
      hence "\<not> int q dvd 4" by presburger
      thus "Legendre 4 q = 1"
        unfolding Legendre_def QuadRes_def cong_0_iff power2_eq_square
        by (metis cong_refl mult_2 numeral_Bit0)
    qed
    hence "Legendre (- d') p = (\<Prod>q\<in>prime_factors d'.
           (Legendre (2 * 2) q * Legendre p q) ^ multiplicity q d')"
      using Legendre_using_quadratic_reciprocity by auto
    also have "... = (\<Prod>q\<in>prime_factors d'.
                      (Legendre 2 q * Legendre (2 * p) q) ^ multiplicity q d')"
      apply (rule prod.cong[OF refl])
      using d'_prime_factors_gt_2 Legendre_mult in_prime_factors_imp_prime
      by (metis int_ops(7) of_nat_numeral prime_nat_int_transfer mult.assoc)
    also have "... = (\<Prod>q\<in>prime_factors d'.
                      (Legendre 2 q * Legendre (- 1) q) ^ multiplicity q d')"
      apply (rule prod.cong[OF refl])
      using d'_prime_factors_2_p_mod Legendre_cong
      unfolding unique_euclidean_semiring_class.cong_def
      apply metis
      done
    also have "... = (\<Prod>q\<in>prime_factors d'.
                      ((if [q = 1] (mod 8) \<or> [q = 7] (mod 8) then 1 else - 1) *
                       (if [q = 1] (mod 4) then 1 else - 1)) ^ multiplicity q d')"
      apply (rule prod.cong[OF refl])
      subgoal for q
        apply (rule arg_cong2[of _ _ _ _ "\<lambda>a b. (a * b) ^ multiplicity q d'"])
        subgoal
          using Legendre_two_alt[of q] d'_prime_factors_gt_2[of q]
          unfolding unique_euclidean_semiring_class.cong_def nat_mod_as_int
          by force
        subgoal
          using Legendre_minus_one_alt[of q] d'_prime_factors_gt_2[of q]
          unfolding unique_euclidean_semiring_class.cong_def nat_mod_as_int
          by force
        done
      done
    also have "... = (\<Prod>q\<in>prime_factors d'.
                      ((if [q = 5] (mod 8) \<or> [q = 7] (mod 8) then - 1 else 1)) ^
                       multiplicity q d')"
      apply (rule prod.cong)
      subgoal by blast
      subgoal for q
        apply (rule arg_cong[of _ _ "\<lambda>a. a ^ multiplicity q d'"])
        unfolding unique_euclidean_semiring_class.cong_def apply (simp; presburger)
        done
      done
    also have "... = (\<Prod>q\<in>prime_factors d'.
                      (if [q = 5] (mod 8) \<or> [q = 7] (mod 8)
                       then (- 1) ^ multiplicity q d' else 1))"
      by (rule prod.cong; auto)
    also have "... = (\<Prod>q\<in>{q\<in>prime_factors d'. [q = 5] (mod 8) \<or> [q = 7] (mod 8)}.
                      (- 1) ^ multiplicity q d')"
      using prod.inter_filter[symmetric] by fast
    also have "... = (- 1) ^ (\<Sum>q\<in>{q\<in>prime_factors d'.
                                   [q = 5] (mod 8) \<or> [q = 7] (mod 8)}.
                              multiplicity q d')"
      by (simp add: power_sum)
    finally have Legendre_using_sum:
      "Legendre (- d') p =
         (- 1) ^ (\<Sum>q\<in>{q\<in>prime_factors d'. [q = 5] (mod 8) \<or> [q = 7] (mod 8)}.
                  multiplicity q d')" .

    have "[\<Sum>q\<in>{q\<in>prime_factors d'. [q = 5] (mod 8) \<or> [q = 7] (mod 8)}.
           multiplicity q d' = 0] (mod 2)"
    proof -
      have "d' = (\<Prod>q\<in>{q \<in> prime_factors d'.
                       [q = 1] (mod 8) \<or> [q = 3] (mod 8) \<or>
                       [q = 5] (mod 8) \<or> [q = 7] (mod 8)}. q ^ multiplicity q d')"
        apply (subst d'_expansion)
        apply (rule prod.cong)
        subgoal
          apply (rule Set.set_eqI)
          subgoal for q
            apply (rule iffI)
            subgoal
              using d'_prime_factors_odd[of q]
              unfolding unique_euclidean_semiring_class.cong_def
              apply simp
              apply presburger
              done
            subgoal by blast
            done
          done
        subgoal by blast
        done
      also have "... = (\<Prod>q\<in>({q \<in> prime_factors d'. [q = 1] (mod 8)} \<union>
                             {q \<in> prime_factors d'. [q = 3] (mod 8)}) \<union>
                            ({q \<in> prime_factors d'. [q = 5] (mod 8)} \<union>
                             {q \<in> prime_factors d'. [q = 7] (mod 8)}).
                        q ^ multiplicity q d')"
        by (rule prod.cong; auto)
      also have "... = (\<Prod>q\<in>({q \<in> prime_factors d'. [q = 1] (mod 8)} \<union>
                             {q \<in> prime_factors d'. [q = 3] (mod 8)}).
                        q ^ multiplicity q d') *
                       (\<Prod>q\<in>({q \<in> prime_factors d'. [q = 5] (mod 8)} \<union>
                             {q \<in> prime_factors d'. [q = 7] (mod 8)}).
                        q ^ multiplicity q d')"
        by (rule prod.union_disjoint;
            force simp add: unique_euclidean_semiring_class.cong_def)
      also have "... = (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 1] (mod 8)}.
                        q ^ multiplicity q d') *
                       (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 8)}.
                        q ^ multiplicity q d') *
                       (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 5] (mod 8)}.
                        q ^ multiplicity q d') *
                       (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 7] (mod 8)}.
                        q ^ multiplicity q d')"
        using prod.union_disjoint[of "{q\<in>prime_factors d'. [q = 1] (mod 8)}"
                                     "{q\<in>prime_factors d'. [q = 3] (mod 8)}"
                                     "\<lambda>q. q ^ multiplicity q d'"]
              prod.union_disjoint[of "{q\<in>prime_factors d'. [q = 5] (mod 8)}"
                                     "{q\<in>prime_factors d'. [q = 7] (mod 8)}"
                                     "\<lambda>q. q ^ multiplicity q d'"]
        by (force simp add: unique_euclidean_semiring_class.cong_def)
      finally have "int (d' mod 8) = (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 1] (mod 8)}.
                                      q ^ multiplicity q d') *
                                     (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 8)}.
                                      q ^ multiplicity q d') *
                                     (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 5] (mod 8)}.
                                      q ^ multiplicity q d') *
                                     (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 7] (mod 8)}.
                                      q ^ multiplicity q d') mod 8"
        by auto
      also have "... = ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 1] (mod 8)}.
                         q ^ multiplicity q d') mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 8)}.
                         q ^ multiplicity q d') mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 5] (mod 8)}.
                         q ^ multiplicity q d') mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 7] (mod 8)}.
                         q ^ multiplicity q d') mod 8) mod 8"
        by (metis (no_types, lifting) mod_mult_eq mod_mod_trivial)
      also have "... = ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 1] (mod 8)}.
                         (q ^ multiplicity q d') mod 8) mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 8)}.
                         (q ^ multiplicity q d') mod 8) mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 5] (mod 8)}.
                         (q ^ multiplicity q d') mod 8) mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 7] (mod 8)}.
                         (q ^ multiplicity q d') mod 8) mod 8) mod 8"
        unfolding mod_prod_eq ..
      also have "... = ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 1] (mod 8)}.
                         ((q mod 8) ^ multiplicity q d') mod 8) mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 8)}.
                         ((q mod 8) ^ multiplicity q d') mod 8) mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 5] (mod 8)}.
                         ((q mod 8) ^ multiplicity q d') mod 8) mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 7] (mod 8)}.
                         ((q mod 8) ^ multiplicity q d') mod 8) mod 8) mod 8"
        unfolding power_mod ..
      also have "... = ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 1] (mod 8)}.
                         (((int q) mod 8) ^ multiplicity q d') mod 8) mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 8)}.
                         (((int q) mod 8) ^ multiplicity q d') mod 8) mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 5] (mod 8)}.
                         (((int q) mod 8) ^ multiplicity q d') mod 8) mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 7] (mod 8)}.
                         (((int q) mod 8) ^ multiplicity q d') mod 8) mod 8) mod 8"
        by (simp add: int_ops)
      also have "... = ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 1] (mod 8)}.
                         ((1 mod 8) ^ multiplicity q d') mod 8) mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 8)}.
                         ((3 mod 8) ^ multiplicity q d') mod 8) mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 5] (mod 8)}.
                         (((- 3) mod 8) ^ multiplicity q d') mod 8) mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 7] (mod 8)}.
                         (((- 1) mod 8) ^ multiplicity q d') mod 8) mod 8) mod 8"
        unfolding cong_int_iff[symmetric] unique_euclidean_semiring_class.cong_def
        by auto
      also have "... = ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 1] (mod 8)}.
                         (1 ^ multiplicity q d') mod 8) mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 8)}.
                         (3 ^ multiplicity q d') mod 8) mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 5] (mod 8)}.
                         ((- 3) ^ multiplicity q d') mod 8) mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 7] (mod 8)}.
                         ((- 1) ^ multiplicity q d') mod 8) mod 8) mod 8"
        unfolding power_mod ..
      also have "... = ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 1] (mod 8)}.
                         1 ^ multiplicity q d') mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 8)}.
                         3 ^ multiplicity q d') mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 5] (mod 8)}.
                         (- 3) ^ multiplicity q d') mod 8) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 7] (mod 8)}.
                         (- 1) ^ multiplicity q d') mod 8) mod 8"
        unfolding mod_prod_eq ..
      also have "... = (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 1] (mod 8)}.
                        1 ^ multiplicity q d') *
                       (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 8)}.
                        3 ^ multiplicity q d') *
                       (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 5] (mod 8)}.
                        (- 3) ^ multiplicity q d') *
                       (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 7] (mod 8)}.
                        (- 1) ^ multiplicity q d') mod 8"
        by (metis (no_types, lifting) mod_mult_eq mod_mod_trivial)
      also have "... = (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 8)}.
                        3 ^ multiplicity q d') *
                       (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 5] (mod 8)}.
                        (- 3) ^ multiplicity q d') *
                       (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 7] (mod 8)}.
                        (- 1) ^ multiplicity q d') mod 8"
        by auto
      also have "... = (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 8)}.
                        3 ^ multiplicity q d') *
                       (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 5] (mod 8)}.
                        3 ^ multiplicity q d' * (- 1) ^ multiplicity q d') *
                       (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 7] (mod 8)}.
                        (- 1) ^ multiplicity q d') mod 8"
        unfolding power_mult_distrib[symmetric] by auto
      also have "... = ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 8)}.
                         3 ^ multiplicity q d') *
                        (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 5] (mod 8)}.
                         3 ^ multiplicity q d')) *
                       ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 5] (mod 8)}.
                         (- 1) ^ multiplicity q d') *
                        (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 7] (mod 8)}.
                         (- 1) ^ multiplicity q d')) mod 8"
        unfolding prod.distrib by (simp add: algebra_simps)
      also have "... = ((\<Prod>q\<in>{q \<in> prime_factors d'. [q = 3] (mod 8)} \<union>
                             {q \<in> prime_factors d'. [q = 5] (mod 8)}.
                         3 ^ multiplicity q d') *
                        (\<Prod>q\<in>{q \<in> prime_factors d'. [q = 5] (mod 8)} \<union>
                             {q \<in> prime_factors d'. [q = 7] (mod 8)}.
                         (- 1) ^ multiplicity q d')) mod 8"
        apply (subst
          prod.union_disjoint[of "{q\<in>prime_factors d'. [q = 5] (mod 8)}"
                                 "{q\<in>prime_factors d'. [q = 7] (mod 8)}"
                                 "\<lambda>q. (- 1) ^ multiplicity q d'"]
        )
        apply ((force simp add: unique_euclidean_semiring_class.cong_def)+)[3]
        apply (subst
          prod.union_disjoint[of "{q\<in>prime_factors d'. [q = 3] (mod 8)}"
                                 "{q\<in>prime_factors d'. [q = 5] (mod 8)}"
                                 "\<lambda>q. 3 ^ multiplicity q d'"]
        )
        apply ((force simp add: unique_euclidean_semiring_class.cong_def)+)[3]
        apply blast
        done
      also have "... = ((\<Prod>q\<in>{q \<in> prime_factors d'.
                              [q = 3] (mod 8) \<or> [q = 5] (mod 8)}.
                         3 ^ multiplicity q d') *
                        (\<Prod>q\<in>{q \<in> prime_factors d'.
                              [q = 5] (mod 8) \<or> [q = 7] (mod 8)}.
                         (- 1) ^ multiplicity q d')) mod 8"
        by (rule arg_cong2[of _ _ _ _ "\<lambda>A B. ((\<Prod>q\<in>A. _ q) * (\<Prod>q\<in>B. _ q)) mod 8"];
            auto)
      also have "... = (((\<Prod>q\<in>{q \<in> prime_factors d'.
                               [q = 3] (mod 8) \<or> [q = 5] (mod 8)}.
                          3 ^ multiplicity q d') mod 8) *
                        ((\<Prod>q\<in>{q \<in> prime_factors d'.
                               [q = 5] (mod 8) \<or> [q = 7] (mod 8)}.
                          (- 1) ^ multiplicity q d') mod 8)) mod 8"
        unfolding mod_mult_eq ..
      also have "... = ((3 ^ (\<Sum>q\<in>{q \<in> prime_factors d'.
                                   [q = 3] (mod 8) \<or> [q = 5] (mod 8)}.
                              multiplicity q d') mod 8) *
                        ((- 1) ^ (\<Sum>q\<in>{q \<in> prime_factors d'.
                                       [q = 5] (mod 8) \<or> [q = 7] (mod 8)}.
                                  multiplicity q d') mod 8)) mod 8"
        unfolding power_sum ..
      also have "... =
          int (case ((\<Sum>q\<in>{q \<in> prime_factors d'.
                           [q = 3] (mod 8) \<or> [q = 5] (mod 8)}.
                      multiplicity q d') mod 2,
                     (\<Sum>q\<in>{q \<in> prime_factors d'.
                           [q = 5] (mod 8) \<or> [q = 7] (mod 8)}.
                      multiplicity q d') mod 2) of
                 (0    , 0    ) \<Rightarrow> 1
               | (0    , Suc 0) \<Rightarrow> 7
               | (Suc 0, 0    ) \<Rightarrow> 3
               | (Suc 0, Suc 0) \<Rightarrow> 5)" (is "_ = int ?d'_mod_8")
        unfolding three_mod_eight_power_iff minus_one_power_iff
        by (simp; simp add: odd_iff_mod_2_eq_one)
      finally have d'_mod_8: "d' mod 8 = ?d'_mod_8"by linarith

      have "[d' = 1] (mod 8) \<or> [d' = 3] (mod 8)"
        unfolding d'_def c_def unique_euclidean_semiring_class.cong_def
        using assms
        by auto
      hence "?d'_mod_8 = 1 \<or> ?d'_mod_8 = 3"
        unfolding unique_euclidean_semiring_class.cong_def d'_mod_8 by auto
      thus ?thesis
        unfolding unique_euclidean_semiring_class.cong_def
        by (smt (z3) Collect_cong One_nat_def cong_exp_iff_simps(11)
                     even_mod_2_iff even_numeral nat.case(2) numeral_eq_iff
                     numerals(1) old.nat.simps(4) parity_cases prod.simps(2)
                     semiring_norm(84))
    qed
    hence "Legendre (- d') p = 1"
      using Legendre_using_sum
      unfolding minus_one_power_iff cong_0_iff
      by argo
    thus "QuadRes p (- d')"
      unfolding Legendre_def
      by (metis one_neq_neg_one one_neq_zero)
  qed

  from \<open>QuadRes p (- d')\<close> obtain x\<^sub>0 y where "x\<^sub>0\<^sup>2 - (- d') = y * (int p)"
    unfolding quadratic_residue_alt_equiv[symmetric]
              quadratic_residue_alt_def
    by auto
  hence "(int p) dvd (x\<^sub>0\<^sup>2 - - d')" by simp

  define x :: int where "x \<equiv> if odd x\<^sub>0 then x\<^sub>0 else (x\<^sub>0 + p)"

  have "even (4 * int n * j)" by simp
  moreover have "odd k" using \<open>coprime k (4 * n)\<close> by auto
  ultimately have "odd (int p)" unfolding p_def by simp

  have "odd x" unfolding x_def using \<open>odd (int p)\<close> by auto

  have "QuadRes (2 * p) (- d')"
  unfolding quadratic_residue_alt_equiv[symmetric]
            quadratic_residue_alt_def
  proof -
    have "2 dvd (x\<^sup>2 - - d')" unfolding d'_def c_def using \<open>odd x\<close> by auto
    moreover from \<open>(int p) dvd (x\<^sub>0\<^sup>2 - - d')\<close>
    have "(int p) dvd (x\<^sup>2 - - d')"
      unfolding x_def power2_eq_square
      apply (simp add: algebra_simps)
      unfolding add.assoc[symmetric, of d' "x\<^sub>0 * x\<^sub>0"]
      apply auto
      done
    moreover have "coprime 2 (int p)" using \<open>odd (int p)\<close> by auto
    ultimately have "(int (2 * p)) dvd (x\<^sup>2 - - d')" by (simp add: divides_mult)
    hence "(x\<^sup>2 - - d') mod (int (2 * p)) = 0" by simp
    hence "\<exists>y. x\<^sup>2 - - d' = int (2 * p) * y" by (simp add: zmod_eq_0D)
    hence "\<exists>y. x\<^sup>2 - - d' = y * int (2 * p)" by (simp add: algebra_simps)
    thus "\<exists>x y. x\<^sup>2 - - d' = y * int (2 * p)" by (rule exI[where ?x=x])
  qed

  have "n \<ge> 2" using \<open>1 < n\<close> by auto
  moreover have "0 < nat d'" unfolding d'_def using \<open>j > 0\<close> by simp
  moreover have "QuadRes (int (nat d' * n - 1)) (- d')"
    using \<open>d' > 1\<close> H_2_p \<open>QuadRes (2 * p) (- d')\<close> by (simp add: int_ops)
  ultimately show "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2"
    using three_squares_using_quadratic_residue[of n "nat d'"]
    by auto
qed

lemma power_two_mod_eight:
  fixes n :: nat
  shows "n\<^sup>2 mod 8 \<in> {0, 1, 4}"
proof -
  have 0: "n\<^sup>2 mod 8 = (n mod 8)\<^sup>2 mod 8"
    unfolding power2_eq_square by (simp add: mod_mult_eq)
  have "n mod 8 \<in> {0, 1, 2, 3, 4, 5, 6, 7}" by auto
  hence "(n mod 8)\<^sup>2 mod 8 \<in> {0, 1, 4}"
    unfolding power2_eq_square by auto
  thus "n\<^sup>2 mod 8 \<in> {0, 1, 4}" unfolding 0 .
qed

lemma power_two_mod_four:
  fixes n :: nat
  shows "n\<^sup>2 mod 4 \<in> {0, 1}"
  using power_two_mod_eight[of n] mod_mod_cancel[of 4 8 "n\<^sup>2"] by auto

text \<open>Theorem 1.4 from @{cite nathanson1996}.\<close>

theorem three_squares_iff:
  fixes n :: nat
  shows "(\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2) \<longleftrightarrow> (\<nexists>a k. n = 4 ^ a * (8 * k + 7))"
proof
  assume "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2"
  then obtain x\<^sub>1 x\<^sub>2 x\<^sub>3 where 0: "n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2" by blast
  show "\<nexists>a k. n = 4 ^ a * (8 * k + 7)"
  proof
    assume "\<exists>a k. n = 4 ^ a * (8 * k + 7)"
    then obtain a k where 1: "n = 4 ^ a * (8 * k + 7)" by blast
    from 0 1 show False
    proof (induction a arbitrary: n x\<^sub>1 x\<^sub>2 x\<^sub>3 rule: nat.induct)
      fix n x\<^sub>1 x\<^sub>2 x\<^sub>3 :: nat
      assume 2: "n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2"
      assume "n = 4 ^ 0 * (8 * k + 7)"
      hence 3: "n mod 8 = 7" unfolding 1 by auto
      have "(x\<^sub>1\<^sup>2 mod 8 + x\<^sub>2\<^sup>2 mod 8 + x\<^sub>3\<^sup>2 mod 8) mod 8 = 7"
        unfolding 2 3[symmetric]
        by (meson mod_add_cong mod_mod_trivial)
      thus False
        using power_two_mod_eight[of x\<^sub>1]
              power_two_mod_eight[of x\<^sub>2]
              power_two_mod_eight[of x\<^sub>3]
        by auto
    next
      fix a' n x\<^sub>1 x\<^sub>2 x\<^sub>3 :: nat
      assume 4: "\<And>n' x\<^sub>1' x\<^sub>2' x\<^sub>3' :: nat.
                 n' = x\<^sub>1'\<^sup>2 + x\<^sub>2'\<^sup>2 + x\<^sub>3'\<^sup>2 \<Longrightarrow> n' = 4 ^ a' * (8 * k + 7) \<Longrightarrow> False"
      assume 5: "n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2"
      assume "n = 4 ^ Suc a' * (8 * k + 7)"
      hence "n = 4 * (4 ^ a' * (8 * k + 7))" (is "n = 4 * ?m") by auto
      hence 6: "4 * ?m = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2" unfolding 5 by auto
      have "(x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2) mod 4 = 0" using 6 by presburger
      hence "((x\<^sub>1\<^sup>2 mod 4) + (x\<^sub>2\<^sup>2 mod 4) + (x\<^sub>3\<^sup>2 mod 4)) mod 4 = 0"
        by presburger
      hence "x\<^sub>1\<^sup>2 mod 4 = 0 \<and> x\<^sub>2\<^sup>2 mod 4 = 0 \<and> x\<^sub>3\<^sup>2 mod 4 = 0"
        using power_two_mod_four[of x\<^sub>1]
              power_two_mod_four[of x\<^sub>2]
              power_two_mod_four[of x\<^sub>3]
        by (auto; presburger)
      hence "even x\<^sub>1 \<and> even x\<^sub>2 \<and> even x\<^sub>3"
        by (metis dvd_0_right even_even_mod_4_iff even_power)
      hence "4 * ?m = 4 * ((x\<^sub>1 div 2)\<^sup>2 + (x\<^sub>2 div 2)\<^sup>2 + (x\<^sub>3 div 2)\<^sup>2)"
        unfolding 6 by fastforce
      hence "?m = (x\<^sub>1 div 2)\<^sup>2 + (x\<^sub>2 div 2)\<^sup>2 + (x\<^sub>3 div 2)\<^sup>2" by auto
      thus False using 4 by blast
    qed
  qed
next
  assume 7: "\<nexists>a k. n = 4 ^ a * (8 * k + 7)"
  show "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2"
  proof cases
    assume "n = 0"
    thus "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2" by auto
  next
    assume 8: "n \<noteq> 0"
    have "n > 0 \<Longrightarrow> \<exists>a m. n = 4 ^ a * m \<and> \<not> 4 dvd m"
    proof (induction n rule: less_induct)
      fix n :: nat
      assume 9: "\<And>n'. n' < n \<Longrightarrow> n' > 0 \<Longrightarrow> \<exists>a' m'. n' = 4 ^ a' * m' \<and> \<not> 4 dvd m'"
      assume 10: "n > 0"
      show "\<exists>a m. n = 4 ^ a * m \<and> \<not> 4 dvd m"
      proof cases
        assume 11: "4 dvd n"
        have "n div 4 < n" "n div 4 > 0" using 10 11 by auto
        then obtain a' m' where 12: "n div 4 = 4 ^ a' * m' \<and> \<not> 4 dvd m'"
          using 9 by blast
        have "n = 4 ^ (Suc a') * m' \<and> \<not> 4 dvd m'"
          using 11 12 by auto
        thus "\<exists>a m. n = 4 ^ a * m \<and> \<not> 4 dvd m" by blast
      next
        assume "\<not> 4 dvd n"
        hence "n = 4 ^ 0 * n \<and> \<not> 4 dvd n" by auto
        thus "\<exists>a m. n = 4 ^ a * m \<and> \<not> 4 dvd m" by blast
      qed
    qed
    then obtain a m where 13: "n = 4 ^ a * m" "\<not> 4 dvd m" using 8 by auto
    have 14: "m mod 8 \<noteq> 7"
    proof
      assume "m mod 8 = 7"
      then obtain k where "m = 8 * k + 7" by (metis div_mod_decomp mult.commute)
      hence "n = 4 ^ a * (8 * k + 7)" unfolding 13 by blast
      thus False using 7 by blast
    qed
    have "m mod 4 = 2 \<or> m mod 8 \<in> {1, 3, 5, 7}"
      using 13 by (simp; presburger)
    hence "m mod 4 = 2 \<or> m mod 8 \<in> {1, 3, 5}"
      using 14 by blast
    hence "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. m = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2"
      using three_squares_using_mod_four three_squares_using_mod_eight
      by blast
    hence "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. n = (2 ^ a * x\<^sub>1)\<^sup>2 + (2 ^ a * x\<^sub>2)\<^sup>2 + (2 ^ a * x\<^sub>3)\<^sup>2"
      unfolding 13 power2_eq_square
      unfolding mult.assoc[of "2 ^ a"]
      unfolding mult.commute[of "2 ^ a"]
      unfolding mult.assoc
      unfolding power_add[symmetric]
      unfolding mult_2[symmetric]
      unfolding power_mult
      unfolding mult.assoc[symmetric]
      unfolding add_mult_distrib[symmetric]
      unfolding mult.commute[of "4 ^ a"]
      by simp
    thus "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2" by blast
  qed
qed

text \<open>Theorem 1.5 from @{cite nathanson1996}.\<close>

theorem odd_three_squares_using_mod_eight:
  fixes n :: nat
  assumes "n mod 8 = 3"
  shows "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. odd x\<^sub>1 \<and> odd x\<^sub>2 \<and> odd x\<^sub>3 \<and> n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2"
proof -
  obtain x\<^sub>1 x\<^sub>2 x\<^sub>3 where 0: "n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2"
    using assms three_squares_using_mod_eight by blast
  have "(x\<^sub>1\<^sup>2 mod 8 + x\<^sub>2\<^sup>2 mod 8 + x\<^sub>3\<^sup>2 mod 8) mod 8 = 3"
    unfolding 0 assms[symmetric]
    by (meson mod_add_cong mod_mod_trivial)
  hence "x\<^sub>1\<^sup>2 mod 8 = 1 \<and> x\<^sub>2\<^sup>2 mod 8 = 1 \<and> x\<^sub>3\<^sup>2 mod 8 = 1"
    using power_two_mod_eight[of x\<^sub>1]
          power_two_mod_eight[of x\<^sub>2]
          power_two_mod_eight[of x\<^sub>3]
    by auto
  hence "odd x\<^sub>1 \<and> odd x\<^sub>2 \<and> odd x\<^sub>3"
    by (metis dvd_mod even_numeral even_power odd_one pos2)
  hence "odd x\<^sub>1 \<and> odd x\<^sub>2 \<and> odd x\<^sub>3 \<and> n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2" using 0 by blast
  thus "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. odd x\<^sub>1 \<and> odd x\<^sub>2 \<and> odd x\<^sub>3 \<and> n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2" by blast
qed

subsection \<open>Consequences\<close>

lemma four_decomposition:
  fixes n :: nat
  shows "\<exists>x y z. n = x\<^sup>2 + y\<^sup>2 + z\<^sup>2 + z"
proof -
  have "(4 * n + 1) mod 8 \<in> {1, 3, 5}" by (simp; presburger)
  then obtain x y z where 0: "4 * n + 1 = x\<^sup>2 + y\<^sup>2 + z\<^sup>2"
    using three_squares_using_mod_eight by blast
  hence 1: "1 = (x\<^sup>2 + y\<^sup>2 + z\<^sup>2) mod 4"
    by (metis Suc_0_mod_numeral(2) Suc_eq_plus1 mod_add_left_eq
              mod_mult_self1_is_0)
  show ?thesis
  proof cases
    assume "even x"
    then obtain x' where H_x: "x = 2 * x'" by blast
    show ?thesis
    proof cases
      assume "even y"
      then obtain y' where H_y: "y = 2 * y'" by blast
      show ?thesis
      proof cases
        assume "even z"
        then obtain z' where H_z: "z = 2 * z'" by blast
        show ?thesis using 1 unfolding H_x H_y H_z by auto
      next
        assume "odd z"
        then obtain z' where H_z: "z = 2 * z' + 1" using oddE by blast
        have "n = x'\<^sup>2 + y'\<^sup>2 + z'\<^sup>2 + z'"
          using 0 unfolding H_x H_y H_z power2_eq_square by auto
        thus ?thesis by blast
      qed
    next
      assume "odd y"
      then obtain y' where H_y: "y = 2 * y' + 1" using oddE by blast
      show ?thesis
      proof cases
        assume "even z"
        then obtain z' where H_z: "z = 2 * z'" by blast
        have "n = x'\<^sup>2 + z'\<^sup>2 + y'\<^sup>2 + y'"
          using 0 unfolding H_x H_y H_z power2_eq_square by auto
        thus ?thesis by blast
      next
        assume "odd z"
        then obtain z' where H_z: "z = 2 * z' + 1" using oddE by blast
        show ?thesis
          using 1
          unfolding H_x H_y H_z power2_eq_square
          by (metis dvd_mod even_add even_mult_iff even_numeral odd_one)
      qed
    qed
  next
    assume "odd x"
    then obtain x' where H_x: "x = 2 * x' + 1" using oddE by blast
    show ?thesis
    proof cases
      assume "even y"
      then obtain y' where H_y: "y = 2 * y'" by blast
      show ?thesis
      proof cases
        assume "even z"
        then obtain z' where H_z: "z = 2 * z'" by blast
        have "n = y'\<^sup>2 + z'\<^sup>2 + x'\<^sup>2 + x'"
          using 0 unfolding H_x H_y H_z power2_eq_square by auto
        thus ?thesis by blast
      next
        assume "odd z"
        then obtain z' where H_z: "z = 2 * z' + 1" using oddE by blast
        show ?thesis
          using 1
          unfolding H_x H_y H_z power2_eq_square
          by (metis dvd_mod even_add even_mult_iff even_numeral odd_one)
      qed
    next
      assume "odd y"
      then obtain y' where H_y: "y = 2 * y' + 1" using oddE by blast
      show ?thesis
      proof cases
        assume "even z"
        then obtain z' where H_z: "z = 2 * z'" by blast
        show ?thesis
          using 1
          unfolding H_x H_y H_z power2_eq_square
          by (metis dvd_mod even_add even_mult_iff even_numeral odd_one)
      next
        assume "odd z"
        then obtain z' where H_z: "z = 2 * z' + 1" using oddE by blast
        show ?thesis
          using 1
          unfolding H_x H_y H_z power2_eq_square
          by (simp add: mod_add_eq[symmetric])
      qed
    qed
  qed
qed

theorem four_decomposition_int:
  fixes n :: int
  shows "(\<exists>x y z. n = x\<^sup>2 + y\<^sup>2 + z\<^sup>2 + z) \<longleftrightarrow> n \<ge> 0"
proof
  assume "\<exists>x y z. n = x\<^sup>2 + y\<^sup>2 + z\<^sup>2 + z"
  then obtain x y z where 0: "n = x\<^sup>2 + y\<^sup>2 + z\<^sup>2 + z" by blast
  show "n \<ge> 0"
    unfolding 0 power2_eq_square
    by (smt (verit) div_pos_neg_trivial mult_le_0_iff
                    nonzero_mult_div_cancel_right sum_squares_ge_zero)
next
  assume "n \<ge> 0"
  thus "\<exists>x y z. n = x\<^sup>2 + y\<^sup>2 + z\<^sup>2 + z"
    using four_decomposition[of "nat n"]
    by (smt (verit) int_eq_iff int_plus of_nat_power)
qed

theorem four_squares:
  fixes n :: nat
  shows "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3 x\<^sub>4. n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2 + x\<^sub>4\<^sup>2"
proof cases
  assume "\<exists>a k. n = 4 ^ a * (8 * k + 7)"
  then obtain a k where "n = 4 ^ a * (8 * k + 7)" by blast
  hence 0: "n = 4 ^ a * (8 * k + 6) + (2 ^ a)\<^sup>2"
    by (metis add_mult_distrib left_add_mult_distrib mult.commute mult_numeral_1
        numeral_Bit0 numeral_plus_numeral power2_eq_square power_mult_distrib
        semiring_norm(5))
  have "\<nexists>a' k'. 4 ^ a * (8 * k + 6) = 4 ^ a' * (8 * k' + 7)"
  proof
    assume "\<exists>a' k'. 4 ^ a * (8 * k + 6) = 4 ^ a' * (8 * k' + 7)"
    then obtain a' k' where 1: "4 ^ a * (8 * k + 6) = 4 ^ a' * (8 * k' + 7)"
      by blast
    show False
    proof (cases rule: linorder_cases[of a a'])
      assume "a < a'"
      hence 2: "a' = a + (a' - a)" "a' - a > 0" by auto
      have 3: "4 ^ a * (8 * k + 6) = 4 ^ a * 4 ^ (a' - a) * (8 * k' + 7)"
        using 1 2 by (metis power_add)
      have "2 = (8 * k + 6) mod 4" by presburger
      also have "... = (4 ^ (a' - a) * (8 * k' + 7)) mod 4" using 3 by auto
      also have "... = 0" using 2 by auto
      finally show False by auto
    next
      assume "a = a'"
      hence "8 * k + 6 = 8 * k' + 7" using 1 by auto
      thus False by presburger
    next
      assume "a > a'"
      hence 4: "a = a' + (a - a')" "a - a' > 0" by auto
      have 5: "4 ^ a' * 4 ^ (a - a') * (8 * k + 6) = 4 ^ a' * (8 * k' + 7)"
        using 1 4 by (metis power_add)
      have "0 = (4 ^ (a - a') * (8 * k + 6)) mod 4" using 4 by auto
      also have "... = (8 * k' + 7) mod 4" using 5 by auto
      also have "... = 3" by presburger
      finally show False by auto
    qed
  qed
  then obtain x\<^sub>1 x\<^sub>2 x\<^sub>3 where "4 ^ a * (8 * k + 6) = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2"
    using three_squares_iff by blast
  thus "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3 x\<^sub>4. n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2 + x\<^sub>4\<^sup>2" unfolding 0 by auto
next
  assume "\<nexists>a k. n = 4 ^ a * (8 * k + 7)"
  hence "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2" using three_squares_iff by blast
  thus "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3 x\<^sub>4. n = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2 + x\<^sub>4\<^sup>2" by (metis zero_power2 add_0)
qed

end
