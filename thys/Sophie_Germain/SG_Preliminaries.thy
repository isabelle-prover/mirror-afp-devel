
(* Author: Benoît Ballenghien, Université Paris-Saclay, CNRS, ENS Paris-Saclay, LMF *)

(*<*)
theory SG_Preliminaries
  imports "HOL-Number_Theory.Number_Theory" Wlog.Wlog
begin
  (*>*)



section \<open>Preliminaries\<close>

subsection \<open>Coprimality\<close>

text \<open>We start with this useful elimination rule: when \<open>a\<close> and \<open>b\<close> are
      not \<^const>\<open>coprime\<close> and are not both equal to \<^term>\<open>0 :: 'a :: factorial_semiring_gcd\<close>,
      there exists some common \<^const>\<open>prime\<close> factor.\<close>

lemma (in factorial_semiring_gcd) not_coprime_nonzeroE :
  \<open>\<lbrakk>\<not> coprime a b; a \<noteq> 0 \<or> b \<noteq> 0; \<And>p. prime p \<Longrightarrow> p dvd a \<Longrightarrow> p dvd b \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  by (metis gcd_eq_0_iff gcd_greatest_iff is_unit_gcd prime_divisor_exists)



text \<open>Still referring to the notion of \<^const>\<open>coprime\<close> (but generalized to a set),
      we prove that when \<^term>\<open>Gcd A \<noteq> 0\<close>, the elements of \<^term>\<open>{a div Gcd A |a. a \<in> A}\<close>
      are setwise \<^const>\<open>coprime\<close>.\<close>

lemma (in semiring_Gcd) GCD_div_Gcd_is_one :
  \<open>(GCD a \<in> A. a div Gcd A) = 1\<close> if \<open>Gcd A \<noteq> 0\<close>
proof (rule ccontr)
  assume \<open>(GCD a\<in>A. a div Gcd A) \<noteq> 1\<close>
  then obtain d where \<open>\<not> is_unit d\<close> \<open>\<forall>a\<in>A. d dvd (a div Gcd A)\<close>
    by (metis (no_types, lifting) Gcd_dvd associated_eqI
        image_eqI normalize_1 normalize_Gcd one_dvd)
  from \<open>\<forall>a\<in>A. d dvd (a div Gcd A)\<close> have \<open>\<forall>a\<in>A. d * Gcd A dvd a\<close>
    by (meson Gcd_dvd dvd_div_iff_mult \<open>Gcd A \<noteq> 0\<close>)
  with Gcd_greatest have \<open>d * Gcd A dvd Gcd A\<close> by blast
  with \<open>\<not> is_unit d\<close> show False by (metis div_self dvd_mult_imp_div that)
qed



subsection \<open>Power\<close>

text \<open>Now we want to characterize the fact of admitting an \<open>n\<close>-th root
      with a condition on the \<^const>\<open>multiplicity\<close> of each prime factor.\<close>

lemma exists_nth_root_iff :
  \<open>(\<exists>x. normalize y = x ^ n) \<longleftrightarrow> (\<forall>p\<in>prime_factors y. n dvd multiplicity p y)\<close>
  if \<open>y \<noteq> 0\<close> for y :: \<open>'a :: factorial_semiring_multiplicative\<close>
proof (rule iffI)
  show \<open>\<exists>x. normalize y = x ^ n \<Longrightarrow> \<forall>p\<in>prime_factors y. n dvd multiplicity p y\<close>
  proof (elim exE, rule ballI)
    fix x p assume \<open>normalize y = x ^ n\<close> and \<open>p \<in> prime_factors y\<close>
    hence \<open>p \<in> prime_factors x\<close>
      by (metis prime_factorization_normalize empty_iff power_0 prime_factorization_1
          prime_factors_power set_mset_empty zero_less_iff_neq_zero)
    with \<open>normalize y = x ^ n\<close> show \<open>n dvd multiplicity p y\<close>
      by (metis dvd_def in_prime_factors_iff multiplicity_normalize_right
          normalization_semidom_class.prime_def prime_elem_multiplicity_power_distrib)
  qed
next
  assume * : \<open>\<forall>p\<in>prime_factors y. n dvd multiplicity p y\<close>
  define f where \<open>f p \<equiv> multiplicity p y div n\<close> for p
  have \<open>normalize y = (\<Prod>p\<in>prime_factors y. p ^ multiplicity p y)\<close>
    by (fact prod_prime_factors[OF \<open>y \<noteq> 0\<close>, symmetric])
  also have \<open>\<dots> = (\<Prod>p\<in>prime_factors y. p ^ (f p * n))\<close>
    by (rule prod.cong[OF refl]) (simp add: "*" f_def)
  also have \<open>\<dots> = (\<Prod>p\<in>prime_factors y. p ^ f p) ^ n\<close>
    by (simp add: power_mult prod_power_distrib)
  finally show \<open>\<exists>x. normalize y = x ^ n\<close> ..
qed



text \<open>We use this result to obtain the following elimination rule.\<close>

corollary prod_is_some_powerE :
  fixes a b :: \<open>'a :: factorial_semiring_multiplicative\<close>
  assumes \<open>coprime a b\<close> and \<open>a * b = x ^ n\<close>
  obtains \<alpha> where \<open>normalize a = \<alpha> ^ n\<close>
proof (cases \<open>a = 0\<close>)
  from \<open>a * b = x ^ n\<close> show \<open>(\<And>\<alpha>. normalize a = \<alpha> ^ n \<Longrightarrow> thesis) \<Longrightarrow> a = 0 \<Longrightarrow> thesis\<close> by simp
next
  assume \<open>a \<noteq> 0\<close> and hyp : \<open>normalize a = \<alpha> ^ n \<Longrightarrow> thesis\<close> for \<alpha>
  from \<open>a \<noteq> 0\<close> have \<open>\<exists>\<alpha>. normalize a = \<alpha> ^ n\<close>
  proof (rule exists_nth_root_iff[THEN iffD2, rule_format])
    fix p assume \<open>p \<in> prime_factors a\<close>
    with \<open>a * b = x ^ n\<close> have \<open>p dvd x\<close>
      by (metis dvd_mult2 in_prime_factors_iff prime_dvd_power)
    hence \<open>p ^ n dvd x ^ n\<close> by (simp add: dvd_power_same)
    with \<open>p \<in> prime_factors a\<close> \<open>a * b = x ^ n\<close> have \<open>n dvd multiplicity p (x ^ n)\<close>
      by (metis dvd_triv_left gcd_nat.extremum in_prime_factors_iff multiplicity_unit_left
          multiplicity_zero not_dvd_imp_multiplicity_0 power_0_left
          prime_elem_multiplicity_power_distrib prime_imp_prime_elem)
    also from \<open>p \<in> prime_factors a\<close> \<open>coprime a b\<close> \<open>a * b = x ^ n\<close>
    have \<open>multiplicity p (x ^ n) = multiplicity p a\<close>
      by (metis (no_types, opaque_lifting) add.right_neutral coprime_0_right_iff coprime_def
          in_prime_factors_iff normalization_semidom_class.prime_def prime_factorization_empty_iff
          prime_elem_multiplicity_eq_zero_iff prime_elem_multiplicity_mult_distrib)
    finally show \<open>n dvd multiplicity p a\<close> .
  qed
  with hyp show thesis by blast
qed



subsection \<open>Sophie Germain Prime\<close>

text \<open>Finally, we introduce Sophie Germain primes.\<close>

definition SophGer_prime :: \<open>nat \<Rightarrow> bool\<close> (\<open>SG\<close>)
  where \<open>SG p \<equiv> odd p \<and> prime p \<and> prime (2 * p + 1)\<close>

lemma SophGer_primeI : \<open>odd p \<Longrightarrow> prime p \<Longrightarrow> prime (2 * p + 1) \<Longrightarrow> SG p\<close>
  unfolding SophGer_prime_def by simp

lemma SophGer_primeD : \<open>odd p\<close> \<open>prime p\<close> \<open>prime (2 * p + 1)\<close> if \<open>SG p\<close>
  using that unfolding SophGer_prime_def by simp_all


text \<open>We can easily compute Sophie Germain primes less than \<^term>\<open>2000 :: nat\<close>.\<close>

value \<open>[p. p \<leftarrow> [0..2000], SG (nat p)]\<close>



context fixes p assumes \<open>SG p\<close> begin

local_setup \<open>Local_Theory.map_background_naming (Name_Space.mandatory_path "SG_simps")\<close>

lemma nonzero : \<open>p \<noteq> 0\<close> using \<open>SG p\<close> by (simp add: odd_pos SophGer_primeD(1))

lemma pos : \<open>0 < p\<close> using nonzero by blast

lemma ge_3 : \<open>3 \<le> p\<close>
  by (metis \<open>SG p\<close> SophGer_prime_def gcd_nat.order_iff_strict not_less_eq_eq
      numeral_2_eq_2 numeral_3_eq_3 order_antisym_conv prime_ge_2_nat)

lemma ge_7 : \<open>7 \<le> 2 * p + 1\<close> using ge_3 by auto


lemma notcong_zero :
  \<open>[- 3 \<noteq> 0 :: int] (mod 2 * p + 1)\<close> \<open>[- 1 \<noteq> 0 :: int] (mod 2 * p + 1)\<close>
  \<open>[  1 \<noteq> 0 :: int] (mod 2 * p + 1)\<close> \<open>[  3 \<noteq> 0 :: int] (mod 2 * p + 1)\<close>
  using SophGer_primeD(2)[OF \<open>SG p\<close>] 
  by (simp_all add: cong_def zmod_zminus1_not_zero prime_nat_iff'')

lemma notcong_p :
  \<open>[- 1 \<noteq> p :: int] (mod 2 * p + 1)\<close>
  \<open>[  0 \<noteq> p :: int] (mod 2 * p + 1)\<close>
  \<open>[  1 \<noteq> p :: int] (mod 2 * p + 1)\<close>
  using SophGer_primeD(2)[OF \<open>SG p\<close>]
  by (auto simp add: pos cong_def zmod_zminus1_eq_if)


lemma p_th_power_mod_q :
  \<open>[m ^ p = 1] (mod 2 * p + 1) \<or> [m ^ p = - 1] (mod 2 * p + 1)\<close>
  if \<open>\<not> 2 * p + 1 dvd m\<close> for m :: int
proof -
  wlog \<open>0 < m\<close> generalizing m keeping that
    by (cases \<open>0 < - m\<close>)
      (metis (no_types, opaque_lifting) \<open>\<not> 2 * p + 1 dvd m\<close> add.inverse_inverse
        cong_minus_minus_iff dvd_minus_iff hypothesis uminus_power_if,
        use \<open>\<not> 2 * p + 1 dvd m\<close> \<open>\<not> 0 < m\<close> in auto)

  with \<open>\<not> 2 * p + 1 dvd m\<close> obtain n where \<open>m = int n\<close> \<open>\<not> 2 * p + 1 dvd n\<close>
    by (metis int_dvd_int_iff pos_int_cases)
  from \<open>0 < m\<close> have \<open>0 < m ^ p\<close> by simp

  have \<open>[m ^ (2 * p) = n ^ (2 * p)] (mod 2 * p + 1)\<close> by (simp add: \<open>m = int n\<close>)
  moreover have \<open>[n ^ (2 * p) = 1] (mod 2 * p + 1)\<close>
    by (metis SophGer_prime_def \<open>SG p\<close> \<open>\<not> 2 * p + 1 dvd n\<close> add_implies_diff fermat_theorem)
  ultimately have \<open>[m ^ (2 * p) = 1] (mod 2 * p + 1)\<close> by (metis cong_def int_ops(2) zmod_int)
  also have \<open>m ^ (2 * p) = m ^ p * m ^ p\<close> by (simp add: mult_2 power_add)
  finally have \<open>[m ^ p * m ^ p = 1] (mod 2 * p + 1)\<close> .
  thus \<open>[m ^ p = 1] (mod 2 * p + 1) \<or> [m ^ p = - 1] (mod 2 * p + 1)\<close>
    by (meson SophGer_primeD(3) \<open>0 < m ^ p\<close> \<open>SG p\<close> cong_square prime_nat_int_transfer)
qed



end



subsection \<open>Fermat's little Theorem for Integers\<close>

lemma fermat_theorem_int :
  \<open>[a ^ (p - 1) = 1] (mod p)\<close> if \<open>prime p\<close> and \<open>\<not> p dvd a\<close>
  for p :: nat and a :: int
proof (cases a)
  show \<open>a = int n \<Longrightarrow> [a ^ (p - 1) = 1] (mod p)\<close> for n
    by (metis cong_int_iff fermat_theorem int_dvd_int_iff of_nat_1 of_nat_power that)
next
  fix n assume \<open>a = - int (Suc n)\<close>
  from \<open>prime p\<close> have \<open>p = 2 \<or> odd p\<close>
    by (metis prime_prime_factor two_is_prime_nat)
  thus \<open>[a ^ (p - 1) = 1] (mod p)\<close>
  proof (elim disjE)
    assume \<open>p = 2\<close>
    with \<open>\<not> p dvd a\<close> have \<open>[a = 1] (mod p)\<close> by (simp add: cong_iff_dvd_diff)
    with \<open>p = 2\<close> show \<open>[a ^ (p - 1) = 1] (mod p)\<close> by simp
  next
    assume \<open>odd p\<close>
    hence \<open>even (p - 1)\<close> by simp
    hence \<open>a ^ (p - 1) = (int (Suc n)) ^ (p - 1)\<close>
      by (metis \<open>a = - int (Suc n)\<close> uminus_power_if)
    also have \<open>[\<dots> = 1] (mod p)\<close>
      by (metis \<open>a = - int (Suc n)\<close> cong_int_iff dvd_minus_iff
          fermat_theorem int_dvd_int_iff of_nat_1 of_nat_power that)
    finally show \<open>[a ^ (p - 1) = 1] (mod p)\<close> .
  qed
qed
  

(*<*)
end
  (*>*)