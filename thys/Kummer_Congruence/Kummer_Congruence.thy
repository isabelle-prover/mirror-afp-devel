(*
  File:     Kummer_Congruence/Kummer_Congruence.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>Kummer's Congruence\<close>
theory Kummer_Congruence
  imports Voronoi_Congruence
begin

unbundle bernoulli_syntax

context
  fixes S :: "nat \<Rightarrow> nat \<Rightarrow> nat" and D :: "nat \<Rightarrow> nat" and N :: "nat \<Rightarrow> int"
  defines "S \<equiv> (\<lambda>k n. \<Sum>r<n. r ^ k)"
  defines "N \<equiv> bernoulli_num" and "D \<equiv> bernoulli_denom"
begin

text \<open>
  Auxiliary lemma for Proposition 9.5.23: if $k$ is even and $(p-1) \nmid k$, then
  $\nu_p(N_k) \geq \nu_p(k)$.
\<close>
lemma multiplicity_prime_bernoulli_num_ge:
  fixes p k :: nat
  assumes p: "prime p" "\<not>(p - 1) dvd k" and k: "even k"
  shows   "multiplicity p (N k) \<ge> multiplicity p k"
proof (cases "k \<ge> 2")
  case True
  define e where "e = multiplicity p k"
  define k' where "k' = k div p ^ e"
  obtain a where a: "residue_primroot p a"
    using \<open>prime p\<close> prime_primitive_root_exists[of p] prime_gt_1_nat[of p] by auto

  have "[(int a^k-1) * N k = k * int a ^ (k-1) * D k * (\<Sum>m=1..<p^e. m^(k-1) * (m * int a div p^e))] (mod p^e)"
    unfolding D_def N_def
  proof (rule voronoi_congruence)
    show "coprime (int a) (int (p ^ e))"
      using a p unfolding residue_primroot_def by (auto simp: coprime_commute)
  qed (use p True k prime_gt_0_nat[of p] in auto)
  also have "p ^ e dvd k"
    unfolding e_def by (simp add: multiplicity_dvd)
  hence "[k * int a ^ (k - 1) * D k * (\<Sum>m=1..<p^e. m^(k-1) * (m * int a div p^e)) = 0] (mod (p ^ e))"
    by (subst cong_0_iff) auto
  finally have "[(int a ^ k - 1) * N k = 0] (mod int (p ^ e))" .
  moreover have "coprime (int a ^ k - 1) (int p)"
  proof -
    have "[a ^ k = 1] (mod p) \<longleftrightarrow> (ord p a dvd k)"
      by (rule ord_divides)
    also have "ord p a = p - 1"
      using a p by (simp add: residue_primroot_def totient_prime)
    finally have "[a ^ k \<noteq> 1] (mod p)"
      using p by simp
    hence "[int (a ^ k) \<noteq> int 1] (mod int p)"
      using cong_int_iff by blast
    hence "\<not>int p dvd int a ^ k - 1"
      unfolding cong_iff_dvd_diff by auto
    thus "coprime (int a ^ k - 1) (int p)"
      using \<open>prime p\<close> by (simp add: coprime_commute prime_imp_coprime)
  qed
  ultimately have "[N k = 0] (mod int (p ^ e))"
    by (metis cong_mult_rcancel coprime_power_right_iff mult.commute mult_zero_left of_nat_power)
  hence "p ^ e dvd N k"
    by (simp add: cong_iff_dvd_diff)
  thus "multiplicity p (N k) \<ge> e"
    using p k by (intro multiplicity_geI) (auto simp: N_def bernoulli_num_eq_0_iff)
next
  case False
  with assms have "k = 0"
    by auto
  thus ?thesis by auto
qed

text \<open>
  Proposition 9.5.23: if $k$ is even and $(p-1)\nmid k$, then $B_k / k$ is $p$-integral.
\<close>
lemma bernoulli_k_over_k_is_p_integral:
  fixes p k :: nat
  assumes p: "prime p" "\<not>(p - 1) dvd k" and k: "k \<noteq> 1"
  shows   "qmultiplicity p (\<B> k / of_nat k) \<ge> 0"
proof -
  consider "odd k" | "k = 0" | "even k" "k \<ge> 2"
    by fastforce
  hence "qmultiplicity p (of_int (N k) / of_int (D k * k)) \<ge> 0"
  proof cases
    assume k: "odd k"
    hence "bernoulli_num k = 0" using \<open>k \<noteq> 1\<close>
      by (subst bernoulli_num_eq_0_iff) auto
    thus ?thesis by (auto simp: N_def)
  next
    assume k: "even k" "k \<ge> 2"
    from k have [simp]: "N k \<noteq> 0" "D k > 0"
      by (auto simp: N_def D_def bernoulli_num_eq_0_iff intro!: Nat.gr0I)
    have "qmultiplicity p (of_int (N k) / of_int (k * D k)) =
            int (multiplicity p (N k)) - int (multiplicity p (k * D k))" using k p
      by (subst qmultiplicity_divide_of_int) (auto simp: multiplicity_int simp del: of_nat_mult)
    also have "multiplicity p (k * D k) = multiplicity p k + multiplicity p (D k)"
      using p k by (subst prime_elem_multiplicity_mult_distrib) auto
    also have "multiplicity p (D k) = 0"
      using p k by (intro not_dvd_imp_multiplicity_0) (auto simp: prime_dvd_bernoulli_denom_iff D_def)
    also have "int (multiplicity (int p) (N k)) - int (multiplicity p k + 0) \<ge> 0"
      using multiplicity_prime_bernoulli_num_ge[of p k] k p by auto
    finally show ?thesis by (simp add: mult_ac)
  qed auto
  also have "of_int (N k) / of_int (D k * k) = bernoulli_rat k / of_nat k"
    by (simp add: bernoulli_rat_def N_def D_def)
  finally show ?thesis .
qed


lemma kummer_congruence_aux:
  fixes k p a :: nat
  assumes k: "even k" "k \<ge> 2" and p: "\<not>(p - 1) dvd k" "prime p"
  assumes a: "\<not>p dvd a"
  assumes s: "s \<ge> multiplicity p k"
  shows "[of_int ((1 - int p^(k-1)) * (int a^k - 1)) * \<B> k / of_nat k =
            of_int (int a^(k-1) *
              (\<Sum>m\<in>{m\<in>{1..<p^(s+e)}. \<not>p dvd m}. m^(k-1) * (int m * a div p ^ (e + s))))] (qmod p^e)"
proof (cases "e > 0")
  case e: True
  from p have "p > 0"
    by (auto intro!: Nat.gr0I)
  have [simp]: "D k > 0"
    by (auto simp: D_def bernoulli_denom_pos)
  define s' where "s' = multiplicity p k"

  define k1 where "k1 = k div p ^ s'"
  have "p ^ s' dvd k"
    by (simp add: multiplicity_dvd' s'_def)
  hence k_eq: "k = k1 * p ^ s'"
    by (simp add: k1_def)
  have "coprime k1 p" unfolding k1_def s'_def using p
    by (metis coprime_commute dvd_0_right multiplicity_decompose not_prime_unit prime_imp_coprime)
  have "k1 > 0"
    using k by (intro Nat.gr0I) (auto simp: k_eq)

  define N' where "N' = N k div p^s'"
  have "multiplicity p (N k) \<ge> s'"
    using s s'_def p k multiplicity_prime_bernoulli_num_ge[of p k] by linarith
  hence "p^s' dvd N k"
    by (simp add: multiplicity_dvd')
  hence N_eq: "N k = N' * p^s'"
    by (simp add: N'_def)
  have "coprime a p"
    using a p coprime_commute prime_imp_coprime by blast

  have "\<not>p dvd D k"
    unfolding D_def using k p by (subst prime_dvd_bernoulli_denom_iff) auto
  hence "coprime (D k) p"
    using p coprime_commute prime_imp_coprime by blast

  have cong1: "[(int a ^ k - 1) * N' =
                 k1 * a ^ (k-1) * D k * (\<Sum>m=1..<p^(s+e). (m^(k-1)) * (int m * a div p^(s+e)))]
               (mod int p ^ e)" for e
  proof -
    have "[(int a ^ k - 1) * N k = 
           k * a ^ (k - 1) * D k * (\<Sum>m = 1..<p^(s+e). (m^(k-1)) * (int m * a div p^(s+e)))] (mod p^(s+e))"
      using voronoi_congruence[of k "p^(s+e)" a] k \<open>p > 0\<close> \<open>coprime a p\<close> unfolding D_def N_def
      by (simp_all add: residue_primroot_def coprime_commute)
    also have "N k = N' * p ^ s'"
      by (simp add: N_eq)
    also have "k * a ^ (k - 1) = k1 * p ^ s' * a ^ (k - 1)"
      by (simp add: k_eq)
    finally have "[int p ^ s' * ((int a ^ k - 1) * N') = 
                   int p ^ s' * (k1 * a ^ (k-1) * D k * (\<Sum>m=1..<p^(s+e). (m^(k-1)) * (int m * a div p^(s+e))))]
                  (mod (int p ^ s * int p ^ e))"
      by (simp add: mult_ac power_add)
    hence "[int p ^ s' * ((int a ^ k - 1) * N') = 
                   int p ^ s' * (k1 * a ^ (k-1) * D k * (\<Sum>m=1..<p^(s+e). (m^(k-1)) * (int m * a div p^(s+e))))]
                  (mod (int p ^ s' * int p ^ e))"
      by (rule cong_modulus_mono) (use s in \<open>auto simp: le_imp_power_dvd s'_def\<close>)
    thus ?thesis
      by (rule cong_mult_cancel) (use p in auto)
  qed

  have cong2:
    "[int p^(k-1) * ((int a ^ k - 1) * N') =
      int p^(k-1) * (k1 * a ^ (k-1) * D k * (\<Sum>m=1..<p^(s+(e-1)). (m^(k-1)) * (int m * a div p^(s+(e-1)))))]
        (mod int p ^ e)"
    by (rule power_mult_cong[OF cong1]) (use k in auto)

  define M1 where "M1 = {m\<in>{1..<p^(s+e)}. \<not>p dvd m}"
  define M2 where "M2 = {m\<in>{1..<p^(s+e)}. p dvd m}"
  define M2' where "M2' = {1..<p^(e+s-1)}"

  have "(\<Sum>m=1..<p^(s+e). (m^(k-1)) * (int m * a div p^(s+e))) =
        (\<Sum>m\<in>M1\<union>M2. (m^(k-1)) * (int m * a div p^(s+e)))"
    by (intro sum.cong) (auto simp: M1_def M2_def)
  also have "\<dots> = (\<Sum>m\<in>M1. (m^(k-1)) * (int m * a div p^(s+e))) +
                  (\<Sum>m\<in>M2. (m^(k-1)) * (int m * a div p^(s+e)))"
    by (intro sum.union_disjoint) (auto simp: M1_def M2_def)
  also have "(\<Sum>m\<in>M2. (m^(k-1)) * (int m * a div p^(s+e))) =
             (\<Sum>m\<in>M2'. ((p*m)^(k-1)) * (int m * a div p^(s+e-1)))"
    using e p prime_gt_1_nat[of p]
    by (intro sum.reindex_bij_witness[of _ "\<lambda>m. p*m" "\<lambda>m. m div p"]; cases e)
       (auto simp: M2_def M2'_def add_ac elim!: dvdE)
  also have "\<dots> = p^(k-1) * (\<Sum>m\<in>M2'. (m^(k-1)) * (int m * a div p^(s+e-1)))"
    by (simp add: sum_distrib_left sum_distrib_right power_mult_distrib mult_ac)
  finally have sum_eq:
     "(\<Sum>m=1..<p^(s+e). (m^(k-1)) * (int m * a div p^(s+e))) =
        (\<Sum>m\<in>M1. (m^(k-1)) * (int m * a div p^(s+e))) +
        p^(k-1) * (\<Sum>m\<in>M2'. (m^(k-1)) * (int m * a div p^(s+e-1)))" .

  
  have "[(1 - int p^(k-1)) * (int a^k - 1) * N' =
         k1 * a ^ (k-1) * D k * (
            (\<Sum>m=1..<p^(s+e). (m^(k-1)) * (int m * a div p^(s+e))) - 
            int p^(k-1) * (\<Sum>m=1..<p^(s+(e-1)). (m^(k-1)) * (int m * a div p^(s+(e-1)))))]
    (mod p^e)"
    using cong_diff[OF cong1[of e] cong2] by (simp add: algebra_simps)
  also have "(\<Sum>m=1..<p^(s+e). (m^(k-1)) * (int m * a div p^(s+e))) - 
               int p^(k-1) * (\<Sum>m=1..<p^(s+(e-1)). (m^(k-1)) * (int m * a div p^(s+(e-1)))) =
             (\<Sum>m\<in>M1. int m ^ (k - Suc 0) * (int m * int a div int p ^ (e + s)))"
    using e by (subst sum_eq) (simp_all add: M2'_def add_ac)
  finally have cong:
     "[(1 - int p^(k-1)) * (int a^k - 1) * N' =
         k1 * a^(k-1) * D k * (\<Sum>m\<in>M1. m^(k-1) * (int m * a div p ^ (e + s)))] (mod p^e)"
    by simp

  have "int p ^ e > 1"
    using p e by (metis of_nat_1 of_nat_less_iff one_less_power prime_gt_1_nat)
  hence "[of_int ((1 - int p^(k-1)) * (int a^k - 1)) * of_int N' =
            of_nat (k1 * D k) * of_int (int a^(k-1) * (\<Sum>m\<in>M1. m^(k-1) * (int m * a div p ^ (e + s))))] (qmod p^e)"
    using cong_imp_qcong[OF cong] by (simp add: mult_ac)
  hence "[of_int ((1 - int p^(k-1)) * (int a^k - 1)) * of_int N' / of_nat (k1 * D k) =
            of_int (int a^(k-1) * (\<Sum>m\<in>M1. m^(k-1) * (int m * a div p ^ (e + s))))] (qmod p^e)"
    using \<open>coprime k1 p\<close> \<open>coprime (D k) p\<close> \<open>k1 > 0\<close> p
    by (subst qcong_divide_of_nat_left_iff) (auto simp: mult_ac prime_gt_0_nat)
  hence "[of_int ((1 - int p^(k-1)) * (int a^k - 1)) * (of_int N' / of_nat (k1 * D k)) =
            of_int (int a^(k-1) * (\<Sum>m\<in>M1. m^(k-1) * (int m * a div p ^ (e + s))))] (qmod p^e)"
    by simp
  also have "of_int N' / of_nat (k1 * D k) = of_int (N k) / (of_nat (k * D k) :: rat)"
    unfolding N_eq unfolding k_eq using p by simp
  finally show ?thesis
    by (simp add: M1_def bernoulli_rat_def N_def D_def mult_ac)
qed auto

theorem kummer_congruence:
  fixes k k' p :: nat
  assumes k: "even k" "k \<ge> 2" and k': "even k'" "k' \<ge> 2" and p: "\<not>(p - 1) dvd k" "prime p"
  assumes cong: "[k = k'] (mod totient (p ^ e))"
  shows   "[(of_nat p^(k-1)-1) * \<B> k / of_nat k =
            (of_nat p^(k'-1)-1) * \<B> k' / of_nat k'] (qmod (p^e))"
proof (cases "e > 0")
  case e: True
  from p have [simp]: "p \<noteq> 0"
    by auto
  obtain a where a: "residue_primroot p a"
    using \<open>prime p\<close> prime_primitive_root_exists[of p] prime_gt_1_nat[of p] by auto
  define s where "s = max (multiplicity p k) (multiplicity p k')"
  have "\<not>p dvd a"
    using a p unfolding residue_primroot_def
    by (metis coprime_absorb_right coprime_commute not_prime_unit)
  have "coprime a p"
    using a by (auto simp: residue_primroot_def coprime_commute)

  have cong': "[k = k'] (mod (p - 1) * (p ^ (e - 1)))"
    using p cong e by (simp add: totient_prime_power mult_ac)
  hence "[k = k'] (mod (p - 1))"
    using cong_modulus_mult_nat by blast
  with \<open>\<not>(p - 1) dvd k\<close> have "\<not>(p - 1) dvd k'"
    using cong_dvd_iff by blast
  have "int p ^ e > 1"
    using p e by (metis of_nat_1 of_nat_less_iff one_less_power prime_gt_1_nat)

  define M1 where "M1 = {m\<in>{1..<p^(s+e)}. \<not>p dvd m}"
  have M1: "coprime m p" if "m \<in> M1" for m
    using prime_imp_coprime[of p m] that p by (auto simp: coprime_commute M1_def)

  have coprime: "coprime (snd (quotient_of (\<B> k' / of_nat k'))) (int p)"
    by (rule qmultiplicity_prime_nonneg_imp_coprime_denom [OF bernoulli_k_over_k_is_p_integral])
       (use k' p \<open>\<not>(p-1) dvd k'\<close> in auto)

  have "[of_int ((1 - int p^(k-1)) * (int a^k - 1)) * \<B> k / of_nat k =
         of_int (int a^(k-1) * (\<Sum>m\<in>M1. int m^(k-1) * (int m * a div p ^ (e + s))))] (qmod p^e)"
    unfolding M1_def using p \<open>\<not>p dvd a\<close> k
    by (intro kummer_congruence_aux) (auto simp: s_def)
  also have "of_int (int a^(k-1) * (\<Sum>m\<in>M1. int m^(k-1) * (int m * a div p ^ (e + s)))) =
             of_int (int (a^(k-1)) * (\<Sum>m\<in>M1. int (m^(k-1)) * (int m * a div p ^ (e + s))))"
    by simp
  also have "[\<dots> = of_int (int (a^(k'-1)) * (\<Sum>m\<in>M1. int (m^(k'-1)) * (int m * a div p ^ (e + s))))] (qmod p^e)"
    using \<open>int p ^ e > 1\<close> \<open>coprime a p\<close> k k' cong p M1
    by (intro cong_imp_qcong cong_mult cong_sum cong_int cong_refl cong_pow_totient cong_diff_nat)
       (auto simp: M1_def)
  also have "of_int (int (a^(k'-1)) * (\<Sum>m\<in>M1. int (m^(k'-1)) * (int m * a div p ^ (e + s)))) =
             of_int (int a^(k'-1) * (\<Sum>m\<in>M1. int m^(k'-1) * (int m * a div p ^ (e + s))))"
    by simp
  also have "[\<dots> = of_int ((1 - int p^(k'-1)) * (int a^k' - 1)) * \<B> k' / of_nat k'] (qmod p^e)"
    unfolding M1_def
    by (rule qcong_sym, rule kummer_congruence_aux)
       (use p \<open>\<not>p dvd a\<close> k' \<open>\<not>(p - 1) dvd k'\<close> in \<open>auto simp: s_def\<close>)
  also have "of_int ((1 - int p^(k'-1)) * (int a^k' - 1)) * \<B> k' / of_nat k' =
             of_int ((1 - int p^(k'-1)) * (int (a^k') - 1)) * (\<B> k' / of_nat k')"
    by simp
  also have "[of_int ((1 - int p^(k'-1)) * (int (a^k') - 1)) * (\<B> k' / of_nat k') =
              of_int ((1 - int p^(k'-1)) * (int (a^k) - 1)) * (\<B> k' / of_nat k')] (qmod p^e)"
    using \<open>int p ^ e > 1\<close> k k' cong p \<open>coprime a p\<close> coprime
    by (intro qcong_mult qcong_refl cong_imp_qcong cong_mult cong_refl cong_diff cong_int
              cong_pow_totient cong_diff_nat)
       (auto simp: cong_sym_eq mult_ac prime_gt_0_nat)
  finally have "[of_int (int a ^ k - 1) * (of_int (1-int p ^ (k-1)) * \<B> k / of_nat k) = 
                 of_int (int a ^ k - 1) * (of_int (1-int p ^ (k'-1)) * \<B> k' / of_nat k')] (qmod int (p ^ e))"
    by (simp add: mult_ac)
  hence "[of_int (1-int p ^ (k-1)) * \<B> k / of_nat k = 
          of_int (1-int p ^ (k'-1)) * \<B> k' / of_nat k'] (qmod int (p ^ e))"
  proof (rule qcong_mult_of_int_cancel_left)
    have "[a ^ k \<noteq> 1] (mod p)"
      using a p(1) assms(6) by (metis ord_divides residue_primroot_def totient_prime)
    hence *: "\<not>int p dvd (int a ^ k - 1)"
      by (simp add: cong_altdef_nat')
    from * show "int a ^ k - 1 \<noteq> 0"
      by (intro notI) auto
    from * show "coprime (int a ^ k - 1) (int (p ^ e))"
      using p prime_imp_coprime[of p "int a ^ k - 1"] by (auto simp: coprime_commute)
  qed (use p in \<open>auto simp: prime_gt_0_nat\<close>)
  from qcong_minus[OF this] show ?thesis
    unfolding minus_divide_left minus_mult_left minus_diff_eq of_int_minus [symmetric]
    by (simp add: mult_ac)
qed auto

corollary kummer_congruence':
  assumes kk': "even k" "even k'" "k \<ge> e+1" "k' \<ge> e+1" 
  assumes cong: "[k = k'] (mod totient (p ^ e))"
  assumes p: "prime p" "\<not>(p-1) dvd k"
  shows   "[\<B> k / of_nat k = \<B> k' / of_nat k'] (qmod (p^e))"
proof (cases "e > 0")
  case e: True
  define z :: "nat \<Rightarrow> rat" where "z = (\<lambda>k. \<B> k / of_nat k)"
  have "1 < int p ^ e"
    by (metis assms(6) e of_nat_1 less_imp_of_nat_less one_less_power prime_nat_iff)
  have ge2: "k \<ge> 2" "k' \<ge> 2"
    using kk' by auto

  have cong': "[k = k'] (mod (p - 1) * (p ^ (e - 1)))"
    using p cong e by (simp add: totient_prime_power mult_ac)
  hence "[k = k'] (mod (p - 1))"
    using cong_modulus_mult_nat by blast
  with \<open>\<not>(p - 1) dvd k\<close> have "\<not>(p - 1) dvd k'"
    using cong_dvd_iff by blast

  have coprime: "coprime (snd (quotient_of (z l))) (int p)" if "l \<in> {k, k'}" for l
  proof (rule qmultiplicity_prime_nonneg_imp_coprime_denom)
    have "qmultiplicity (int p) (\<B> l / of_nat l) \<ge> 0"
      by (rule bernoulli_k_over_k_is_p_integral)  (use p kk' that \<open>\<not>(p - 1) dvd k'\<close> in auto)
    thus "qmultiplicity (int p) (z l) \<ge> 0"
      by (simp add: z_def)
  qed (use p in auto)

  have "[of_int (0 - 1) * z k = of_int (int p ^ (k-1) - 1) * z k] (qmod (p ^ e))"
    using \<open>int p ^ e > 1\<close> kk' coprime[of k] p
    by (intro qcong_mult cong_imp_qcong qcong_refl cong_diff cong_refl)
       (auto simp: Cong.cong_def mod_eq_0_iff_dvd prime_gt_0_nat intro!: le_imp_power_dvd)
  also have "[of_int (int p ^ (k-1) - 1) * z k = of_int (int p ^ (k'-1) - 1) * z k'] (qmod (p ^ e))"
    unfolding z_def using kummer_congruence[of k k' p e] kk' cong p ge2 by simp
  also have "[of_int (int p ^ (k'-1) - 1) * z k' = of_int (0 - 1) * z k'] (qmod (p ^ e))"
    using \<open>int p ^ e > 1\<close> kk' coprime[of k'] p
    by (intro qcong_mult cong_imp_qcong qcong_refl cong_diff cong_refl)
       (auto simp: Cong.cong_def mod_eq_0_iff_dvd prime_gt_0_nat intro!: le_imp_power_dvd)
  finally show ?thesis
    by (simp add: z_def qcong_minus_minus_iff)
qed auto

corollary kummer_congruence'_prime:
  assumes kk': "even k" "even k'" "k > 0" "k' > 0" 
  assumes cong: "[k = k'] (mod (p - 1))"
  assumes p: "prime p" "\<not>(p-1) dvd k"
  shows   "[\<B> k / of_nat k = \<B> k' / of_nat k'] (qmod p)"
proof -
  from kk' have "k \<ge> 2" "k' \<ge> 2"
    by auto
  thus ?thesis
    using kummer_congruence'[of k k' 1 p] assms by (auto simp: totient_prime)
qed

end

unbundle no bernoulli_syntax

end