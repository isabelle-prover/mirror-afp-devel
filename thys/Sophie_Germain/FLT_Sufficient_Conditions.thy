
(* Author: Benoît Ballenghien, Université Paris-Saclay, CNRS, ENS Paris-Saclay, LMF *)

(*<*)
theory FLT_Sufficient_Conditions
  imports SG_Preliminaries Fermat3_4.Fermat4
begin
  (*>*)



section \<open>Sufficient Conditions for FLT\<close>

text \<open>Recall that FLT stands for ``Fermat's Last Theorem''.
      FLT states that there is no nontrivial integer solutions to the equation
      \<^term>\<open>(x :: int) ^ n + y ^ n = z ^ n\<close> for any natural number \<^term>\<open>(2 :: int) < n\<close>.
      as soon as the natural number \<open>n\<close> is greater than \<^term>\<open>2 :: nat\<close>.
      More formally: \<^term>\<open>(2 :: nat) < n \<Longrightarrow> \<nexists>x y z :: int. x ^ n + y ^ n = z ^ n\<close>.
      We give here some sufficient conditions.\<close>

subsection \<open>Coprimality\<close>

text \<open>We first notice that it is sufficient to prove FLT for integers
      \<open>x\<close>, \<open>y\<close> and \<open>z\<close> that are (setwise) \<^const>\<open>coprime\<close>.\<close>

lemma (in semiring_Gcd) FLT_setwise_coprime_reduction :
  assumes \<open>x ^ n + y ^ n = z ^ n\<close> \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close> \<open>z \<noteq> 0\<close>
  defines \<open>d \<equiv> Gcd {x, y, z}\<close>
  shows \<open>(x div d) ^ n + (y div d) ^ n = (z div d) ^ n\<close> \<open>x div d \<noteq> 0\<close>
    \<open>y div d \<noteq> 0\<close> \<open>z div d \<noteq> 0\<close> \<open>Gcd {x div d, y div d, z div d} = 1\<close>
proof -
  have \<open>d dvd x\<close> \<open>d dvd y\<close> \<open>d dvd z\<close> by (unfold d_def, rule Gcd_dvd; simp)+
  thus \<open>x div d \<noteq> 0\<close> \<open>y div d \<noteq> 0\<close> \<open>z div d \<noteq> 0\<close>
    by (simp_all add: \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close> \<open>z \<noteq> 0\<close> dvd_div_eq_0_iff)

  have \<open>{x div d, y div d, z div d} = (\<lambda>n. n div d) ` {x, y, z}\<close> by blast
  thus \<open>Gcd {x div d, y div d, z div d} = 1\<close>
    by (metis GCD_div_Gcd_is_one \<open>x div d \<noteq> 0\<close> d_def div_by_0)

  from  \<open>x ^ n + y ^ n = z ^ n\<close> show \<open>(x div d) ^ n + (y div d) ^ n = (z div d) ^ n\<close>
    by (metis \<open>d dvd x\<close> \<open>d dvd y\<close> \<open>d dvd z\<close> div_add div_power dvd_power_same)
qed

corollary (in semiring_Gcd) FLT_for_coprime_is_sufficient : 
  \<open>\<nexists>x y z. x \<noteq> 0 \<and> y \<noteq> 0 \<and> z \<noteq> 0 \<and> Gcd {x, y, z} = 1 \<and> x ^ n + y ^ n = z ^ n \<Longrightarrow>
   \<nexists>x y z. x \<noteq> 0 \<and> y \<noteq> 0 \<and> z \<noteq> 0 \<and> x ^ n + y ^ n = z ^ n\<close>
  by (metis (no_types) FLT_setwise_coprime_reduction)

\<comment> \<open>These very generic lemmas are of course working for integers.\<close>
lemma \<open>OFCLASS(int, semiring_Gcd_class)\<close> by intro_classes



text \<open>This version involving congruences will be useful later.\<close>

lemma FLT_setwise_coprime_reduction_mod_version :
  fixes x y z :: int
  assumes \<open>x ^ n + y ^ n = z ^ n\<close> \<open>[x \<noteq> 0] (mod m)\<close> \<open>[y \<noteq> 0] (mod m)\<close> \<open>[z \<noteq> 0] (mod m)\<close>
  defines \<open>d \<equiv> Gcd {x, y, z}\<close>
  shows \<open>(x div d) ^ n + (y div d) ^ n = (z div d) ^ n\<close> \<open>[x div d \<noteq> 0] (mod m)\<close>
    \<open>[y div d \<noteq> 0] (mod m)\<close> \<open>[z div d \<noteq> 0] (mod m)\<close> \<open>Gcd {x div d, y div d, z div d} = 1\<close>
proof -
  have \<open>d dvd x\<close> \<open>d dvd y\<close> \<open>d dvd z\<close> by (unfold d_def, rule Gcd_dvd; simp)+
  show \<open>[x div d \<noteq> 0] (mod m)\<close>
    by (metis \<open>d dvd x\<close> assms(2) cong_0_iff dvd_mult dvd_mult_div_cancel)
  show \<open>[y div d \<noteq> 0] (mod m)\<close>
    by (metis \<open>d dvd y\<close> assms(3) cong_0_iff dvd_mult dvd_mult_div_cancel)
  show \<open>[z div d \<noteq> 0] (mod m)\<close>
    by (metis \<open>d dvd z\<close> assms(4) cong_0_iff dvd_mult dvd_mult_div_cancel)

  have \<open>{x div d, y div d, z div d} = (\<lambda>n. n div d) ` {x, y, z}\<close> by blast
  thus \<open>Gcd {x div d, y div d, z div d} = 1\<close>
    by (metis GCD_div_Gcd_is_one \<open>[x div d \<noteq> 0] (mod m)\<close> cong_refl d_def div_by_0)

  from  \<open>x ^ n + y ^ n = z ^ n\<close> show \<open>(x div d) ^ n + (y div d) ^ n = (z div d) ^ n\<close>
    by (metis \<open>d dvd x\<close> \<open>d dvd y\<close> \<open>d dvd z\<close> div_plus_div_distrib_dvd_right div_power dvd_power_same)
qed



text \<open>Actually, it is sufficient to prove FLT for integers
      \<open>x\<close>, \<open>y\<close> and \<open>z\<close> that are pairwise \<^const>\<open>coprime\<close>\<close>

lemma (in semiring_Gcd) FLT_setwise_coprime_imp_pairwise_coprime :
  \<open>coprime x y\<close> if \<open>n \<noteq> 0\<close> \<open>x ^ n + y ^ n = z ^ n\<close> \<open>Gcd {x, y, z} = 1\<close>
proof (rule ccontr)
  assume \<open>\<not> coprime x y\<close>
  with is_unit_gcd obtain d where \<open>\<not> is_unit d\<close> \<open>d dvd x\<close> \<open>d dvd y\<close> by blast
  from \<open>d dvd x\<close> \<open>d dvd y\<close> have \<open>d ^ n dvd x ^ n\<close> \<open>d ^ n dvd y ^ n\<close>
    by (simp_all add: dvd_power_same)
  moreover from calculation \<open>x ^ n + y ^ n = z ^ n\<close> have \<open>d ^ n dvd z ^ n\<close>
    by (metis dvd_add_right_iff)
  moreover from \<open>Gcd {x, y, z} = 1\<close> have \<open>Gcd {x ^ n, y ^ n, z ^ n} = 1\<close>
    by (simp add: gcd_exp_weak)
  ultimately have \<open>is_unit (d ^ n)\<close> by (metis Gcd_2 Gcd_insert gcd_greatest)
  with \<open>\<not> is_unit d\<close> show False by (metis is_unit_power_iff \<open>n \<noteq> 0\<close>)
qed



subsection \<open>Odd prime Exponents\<close>

text \<open>From \<^session>\<open>Fermat3_4\<close>, FLT is already proven for \<^term>\<open>n = (4 :: nat)\<close>.
      Using this, we can prove that it is sufficient to
      prove FLT for \<^const>\<open>odd\<close> \<^const>\<open>prime\<close> exponents.\<close>

lemma (in semiring_1_no_zero_divisors) FLT_exponent_reduction :
  assumes \<open>x ^ n + y ^ n = z ^ n\<close> \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close> \<open>z \<noteq> 0\<close> \<open>p dvd n\<close>
  shows \<open>(x ^ (n div p)) ^ p + (y ^ (n div p)) ^ p = (z ^ (n div p)) ^ p\<close>
    \<open>x ^ (n div p) \<noteq> 0\<close> \<open>y ^ (n div p) \<noteq> 0\<close> \<open>z ^ (n div p) \<noteq> 0\<close>
proof -
  from power_not_zero[OF \<open>x \<noteq> 0\<close>] show \<open>x ^ (n div p) \<noteq> 0\<close> .
  from power_not_zero[OF \<open>y \<noteq> 0\<close>] show \<open>y ^ (n div p) \<noteq> 0\<close> .
  from power_not_zero[OF \<open>z \<noteq> 0\<close>] show \<open>z ^ (n div p) \<noteq> 0\<close> .

  from \<open>p dvd n\<close> have * : \<open>n = (n div p) * p\<close> by simp
  from \<open>x ^ n + y ^ n = z ^ n\<close>
  show \<open>(x ^ (n div p)) ^ p + (y ^ (n div p)) ^ p = (z ^ (n div p)) ^ p\<close>
    by (subst (asm) (1 2 3) "*") (simp add: power_mult)
qed

lemma \<open>OFCLASS(int, semiring_1_no_zero_divisors_class)\<close> by intro_classes



lemma odd_prime_or_four_factorE :
  fixes n :: nat assumes \<open>2 < n\<close>
  obtains p where \<open>p dvd n\<close> \<open>odd p\<close> \<open>prime p\<close> | \<open>4 dvd n\<close>
proof -
  assume hyp1 : \<open>p dvd n \<Longrightarrow> odd p \<Longrightarrow> prime p \<Longrightarrow> thesis\<close> for p
  assume hyp2 : \<open>4 dvd n \<Longrightarrow> thesis\<close>

  show thesis
  proof (cases \<open>\<exists>p. p dvd n \<and> odd p \<and> prime p\<close>)
    from hyp1 show \<open>\<exists>p. p dvd n \<and> odd p \<and> prime p \<Longrightarrow> thesis\<close> by blast
  next
    assume \<open>\<nexists>p. p dvd n \<and> odd p \<and> prime p\<close>
    hence \<open>p \<in> prime_factors n \<Longrightarrow> p = 2\<close> for p
      by (metis in_prime_factors_iff primes_dvd_imp_eq two_is_prime_nat)
    then obtain k where \<open>prime_factorization n = replicate_mset k 2\<close>
      by (metis set_mset_subset_singletonD singletonI subsetI)
    hence \<open>n = 2 ^ k\<close> by (subst prod_mset_prime_factorization_nat[symmetric])
        (use assms in simp_all)
    with \<open>2 < n\<close> have \<open>1 < k\<close> by (metis nat_power_less_imp_less pos2 power_one_right)
    with \<open>n = 2 ^ k\<close> have \<open>4 dvd n\<close>
      by (metis Suc_leI dvd_power_iff_le numeral_Bit0_eq_double
          power.simps(2) power_one_right verit_comp_simplify1(2))
    with hyp2 show thesis by blast
  qed
qed



text \<open>Finally, proving FLT for odd prime exponents is sufficient.\<close>

corollary FLT_for_odd_prime_exponents_is_sufficient : 
  \<open>\<nexists>x y z :: int. x \<noteq> 0 \<and> y \<noteq> 0 \<and> z \<noteq> 0 \<and> x ^ n + y ^ n = z ^ n\<close> if \<open>2 < n\<close>
  and odd_prime_FLT :
  \<open>\<And>p. odd p \<Longrightarrow> prime p \<Longrightarrow>
        \<nexists>x y z :: int.  x \<noteq> 0 \<and> y \<noteq> 0 \<and> z \<noteq> 0 \<and> x ^ p + y ^ p = z ^ p\<close>
proof (rule ccontr)
  assume \<open>\<not> (\<nexists>x y z :: int. x \<noteq> 0 \<and> y \<noteq> 0 \<and> z \<noteq> 0 \<and> x ^ n + y ^ n = z ^ n)\<close>
  then obtain x y z :: int
    where \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close> \<open>z \<noteq> 0\<close> \<open>x ^ n + y ^ n = z ^ n\<close> by blast
  from odd_prime_or_four_factorE \<open>2 < n\<close>
  consider p where \<open>p dvd n\<close> \<open>odd p\<close> \<open>prime p\<close> | \<open>4 dvd n\<close> by blast
  thus False
  proof cases
    fix p assume \<open>p dvd n\<close> \<open>odd p\<close> \<open>prime p\<close>
    from FLT_exponent_reduction [OF \<open>x ^ n + y ^ n = z ^ n\<close> \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close> \<open>z \<noteq> 0\<close> \<open>p dvd n\<close>]
      odd_prime_FLT[OF \<open>odd p\<close> \<open>prime p\<close>]
    show False by blast
  next
    assume \<open>4 dvd n\<close>
    from fermat_mult4[OF \<open>x ^ n + y ^ n = z ^ n\<close> \<open>4 dvd n\<close>] \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close> \<open>z \<noteq> 0\<close>
    show False by (metis mult_eq_0_iff)
  qed
qed



(*<*)
end
  (*>*)