(*
  File:   Squarefree_Nat.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  The unique decomposition of a natural number into a squarefree part and a square.
*)

section {* Squarefree decomposition of natural numbers *}
theory Squarefree_Nat
imports
  Main
  "~~/src/HOL/Number_Theory/Number_Theory"
  Prime_Harmonic_Misc
begin

text \<open>
  The squarefree part of a natural number is the set of all prime factors that appear 
  with odd multiplicity. The square part, correspondingly, is what remains after dividing
  by the squarefree part.
\<close>
definition squarefree_part :: "nat \<Rightarrow> nat set" where
  "squarefree_part n = {p\<in>prime_factors n. odd (multiplicity p n)}"

definition square_part :: "nat \<Rightarrow> nat" where
  "square_part n = (if n = 0 then 0 else (\<Prod>p\<in>prime_factors n. p ^ (multiplicity p n div 2)))"

lemma squarefree_part_0 [simp]: "squarefree_part 0 = {}"
  by (simp add: squarefree_part_def)

lemma square_part_0 [simp]: "square_part 0 = 0"
  by (simp add: square_part_def)

lemma squarefree_decompose: "\<Prod>(squarefree_part n) * square_part n ^ 2 = n"
proof (cases "n = 0")
  case False
  def A \<equiv> "squarefree_part n" and s \<equiv> "square_part n"
  have "(\<Prod>A) = (\<Prod>p\<in>A. p ^ (multiplicity p n mod 2))"
    by (intro setprod.cong) (auto simp: A_def squarefree_part_def elim!: oddE)
  also have "\<dots> = (\<Prod>p\<in>prime_factors n. p ^ (multiplicity p n mod 2))"
    by (intro setprod.mono_neutral_left) (auto simp: A_def  squarefree_part_def)
  also from False have "\<dots> * s^2 = n"
    by (simp add: s_def square_part_def setprod.distrib [symmetric] power_add [symmetric] 
                  power_mult [symmetric] prime_factorization_nat [symmetric] algebra_simps
                  setprod_power_distrib)
  finally show "\<Prod>A * s^2 = n" .
qed simp

lemma squarefree_part_pos [simp]: "\<Prod>(squarefree_part n) > 0"
  using prime_gt_0_nat unfolding squarefree_part_def by auto

lemma squarefree_part_subset [intro]: "squarefree_part n \<subseteq> prime_factors n"
  unfolding squarefree_part_def by auto

lemma squarefree_part_finite [simp]: "finite (squarefree_part n)"
  by (rule finite_subset[OF squarefree_part_subset]) simp

lemma squarefree_part_dvd [simp]: "\<Prod>(squarefree_part n) dvd n"
  by (subst (2) squarefree_decompose [of n, symmetric]) simp

lemma squarefree_part_dvd' [simp]: "p \<in> squarefree_part n \<Longrightarrow> p dvd n"
  by (rule dvd_setprodD[OF _ squarefree_part_dvd]) simp_all

lemma square_part_dvd [simp]: "square_part n ^ 2 dvd n"
  by (subst (2) squarefree_decompose [of n, symmetric]) simp

lemma square_part_dvd' [simp]: "square_part n dvd n"
  by (subst (2) squarefree_decompose [of n, symmetric]) simp

lemma squarefree_part_le: "p \<in> squarefree_part n \<Longrightarrow> p \<le> n"
  by (cases "n = 0") (simp_all add: dvd_imp_le)

lemma square_part_le: "square_part n \<le> n"
  by (cases "n = 0") (simp_all add: dvd_imp_le)

lemma square_part_pos [simp]: "n > 0 \<Longrightarrow> square_part n > 0"
  unfolding square_part_def using prime_gt_0_nat by (auto simp: prime_factors_altdef2_nat)

lemma multiplicity_squarefree_part:
  "multiplicity p (\<Prod>(squarefree_part n)) = (if p \<in> squarefree_part n then 1 else 0)"
  using squarefree_part_subset[of n]
  by (intro multiplicity_prod_prime_powers_nat') auto

text \<open>
  The squarefree part really is square, its only square divisor is 1.
\<close>
lemma square_dvd_squarefree_part_iff:
  "x^2 dvd \<Prod>(squarefree_part n) \<longleftrightarrow> x = 1"
proof (rule iffI, rule multiplicity_eq_nat)
  assume dvd: "x^2 dvd \<Prod>(squarefree_part n)"
  hence "x \<noteq> 0" using squarefree_part_subset[of n] prime_gt_0_nat by (intro notI) auto
  thus x: "x > 0" by simp
  
  fix p assume p: "prime p"
  from p x have "2 * multiplicity p x = multiplicity p (x^2)" 
    by (simp add: multiplicity_power_nat)
  also from dvd have "\<dots> \<le> multiplicity p (\<Prod>(squarefree_part n))"
    by (intro dvd_multiplicity_nat) simp_all
  also have "\<dots> \<le> 1" using multiplicity_squarefree_part[of p n] by simp
  finally show "multiplicity p x = multiplicity p 1" by simp
qed simp_all


lemma squarefree_decomposition_unique1:
  assumes "squarefree_part m = squarefree_part n"
  assumes "square_part m = square_part n"
  shows   "m = n"
  by (subst (1 2) squarefree_decompose [symmetric]) (simp add: assms)

lemma squarefree_decomposition_unique2:
  assumes n: "n > 0"
  assumes decomp: "n = (\<Prod>A2 * s2^2)"
  assumes prime: "\<And>x. x \<in> A2 \<Longrightarrow> prime x"
  assumes fin: "finite A2"
  assumes s2_nonneg: "s2 \<ge> 0"
  shows "A2 = squarefree_part n" and "s2 = square_part n"
proof -
  def A1 \<equiv> "squarefree_part n" and s1 \<equiv> "square_part n"
  have "finite A1" unfolding A1_def by simp
  note fin = \<open>finite A1\<close> \<open>finite A2\<close>

  have "A1 \<subseteq> prime_factors n" unfolding A1_def using squarefree_part_subset .
  note subset = this prime

  have "\<Prod>A1 > 0" "\<Prod>A2 > 0" using subset(1)  prime_gt_0_nat 
    by (auto intro!: setprod_pos dest: prime simp: prime_factors_altdef2_nat)
  from n have "s1 > 0" unfolding s1_def by simp
  from assms have "s2 \<noteq> 0" by (intro notI) simp
  hence "s2 > 0" by simp
  note pos = \<open>\<Prod>A1 > 0\<close> \<open>\<Prod>A2 > 0\<close> \<open>s1 > 0\<close> \<open>s2 > 0\<close>

  have eq': "multiplicity p s1 = multiplicity p s2" 
            "multiplicity p (\<Prod>A1) = multiplicity p (\<Prod>A2)" 
    if   p: "prime p" for p
  proof -
    def m \<equiv> "multiplicity p"
    from decomp have "m (\<Prod>A1 * s1^2) = m (\<Prod>A2 * s2^2)" unfolding A1_def s1_def
      by (simp add: A1_def s1_def squarefree_decompose)
    with p pos have eq: "m (\<Prod>A1) + 2 * m s1 = m (\<Prod>A2) + 2 * m s2"
      by (simp add: m_def multiplicity_product_nat multiplicity_power_nat)
    moreover from fin subset have "m (\<Prod>A1) \<le> 1" "m (\<Prod>A2) \<le> 1" unfolding m_def
      by ((subst multiplicity_prod_prime_powers_nat', auto)[])+
    ultimately show "m s1 = m s2" by linarith
    with eq show "m (\<Prod>A1) = m (\<Prod>A2)" by simp
  qed
  
  show "s2 = square_part n"
    by (rule multiplicity_eq_nat) (insert pos eq'(1), auto simp: s1_def)
  have "\<Prod>A2 = \<Prod>(squarefree_part n)"
    by (rule multiplicity_eq_nat) (insert pos eq'(2), auto simp: A1_def)
  with fin subset show "A2 = squarefree_part n" unfolding A1_def
    by (intro setprod_prime_eq) auto
qed

lemma squarefree_decomposition_unique2':
  assumes decomp: "(\<Prod>A1 * s1^2) = (\<Prod>A2 * s2^2 :: nat)"
  assumes fin: "finite A1" "finite A2"
  assumes subset: "\<And>x. x \<in> A1 \<Longrightarrow> prime x" "\<And>x. x \<in> A2 \<Longrightarrow> prime x"
  assumes pos: "s1 > 0" "s2 > 0"
  defines "n \<equiv> \<Prod>A1 * s1^2"
  shows "A1 = A2" "s1 = s2"
proof -
  from pos have n: "n > 0" using prime_gt_0_nat 
    by (auto simp: n_def intro!: setprod_pos dest: subset)
  have "A1 = squarefree_part n" "s1 = square_part n" 
    by ((rule squarefree_decomposition_unique2[of n A1 s1], insert assms n, simp_all)[])+
  moreover have "A2 = squarefree_part n" "s2 = square_part n" 
    by ((rule squarefree_decomposition_unique2[of n A2 s2], insert assms n, simp_all)[])+
  ultimately show "A1 = A2" "s1 = s2" by simp_all
qed

end