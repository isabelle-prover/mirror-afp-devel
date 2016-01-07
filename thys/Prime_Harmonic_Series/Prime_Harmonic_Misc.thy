(*
  File:   Prime_Harmonic_Misc.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

*)

section {* Auxiliary lemmas *}
theory Prime_Harmonic_Misc
imports
  Complex_Main
  "~~/src/HOL/Number_Theory/Number_Theory" 
begin

lemma listsum_nonneg: "\<forall>x\<in>set xs. x \<ge> 0 \<Longrightarrow> listsum xs \<ge> (0 :: 'a :: ordered_ab_group_add)"
  by (induction xs) auto

lemma setsum_telescope':
  assumes "m \<le> n"
  shows   "(\<Sum>k = Suc m..n. f k - f (Suc k)) = f (Suc m) - (f (Suc n) :: 'a :: ab_group_add)"
  by (rule dec_induct[OF assms]) (simp_all add: algebra_simps)

lemma dvd_setprodI:
  assumes "finite A" "x \<in> A"
  shows   "f x dvd setprod f A"
proof -
  from assms have "setprod f A = f x * setprod f (A - {x})" 
    by (intro setprod.remove) simp_all
  thus ?thesis by simp
qed

lemma dvd_setprodD: "finite A \<Longrightarrow> setprod f A dvd x \<Longrightarrow> a \<in> A \<Longrightarrow> f a dvd x"
  by (erule dvd_trans[OF dvd_setprodI])

lemma multiplicity_power_nat: 
  "prime p \<Longrightarrow> n > 0 \<Longrightarrow> multiplicity p (n ^ k :: nat) = k * multiplicity p n"
  by (induction k) (simp_all add: multiplicity_product_nat)

lemma multiplicity_prod_prime_powers_nat':
  "finite S \<Longrightarrow> \<forall>p\<in>S. prime p \<Longrightarrow> multiplicity p (\<Prod>S) = (if p \<in> S then 1 else 0)"
  using multiplicity_prod_prime_powers_nat[where f = "\<lambda>_. 1"] by simp

lemma setprod_prime_subset:
  assumes "finite A" "finite B"
  assumes "\<And>x. x \<in> A \<Longrightarrow> prime (x::nat)"
  assumes "\<And>x. x \<in> B \<Longrightarrow> prime x"
  assumes "\<Prod>A dvd \<Prod>B"
  shows   "A \<subseteq> B"
proof
  fix x assume x: "x \<in> A"
  from assms(4)[of 0] have "0 \<notin> B" by auto
  with assms have nonzero: "\<forall>z\<in>B. z \<noteq> 0" by (intro ballI notI) auto

  from x assms have "1 = multiplicity x (\<Prod>A)"
    by (subst multiplicity_prod_prime_powers_nat') simp_all
  also from assms nonzero have "\<dots> \<le> multiplicity x (\<Prod>B)" by (intro dvd_multiplicity_nat) auto
  finally have "multiplicity x (\<Prod>B) > 0" by simp
  moreover from assms x have "prime x" by simp
  ultimately show "x \<in> B" using assms(2,4)
    by (subst (asm) multiplicity_prod_prime_powers_nat') (simp_all split: split_if_asm)
qed

lemma setprod_prime_eq:
  assumes "finite A" "finite B" "\<And>x. x \<in> A \<Longrightarrow> prime (x::nat)" "\<And>x. x \<in> B \<Longrightarrow> prime x" "\<Prod>A = \<Prod>B"
  shows   "A = B"
  using assms by (intro equalityI setprod_prime_subset) simp_all

lemma ln_ln_nonneg:
  assumes x: "x \<ge> (3 :: real)"
  shows   "ln (ln x) \<ge> 0"
proof -
  have "exp 1 \<le> (3::real)" by (rule  exp_le)
  hence "ln (exp 1) \<le> ln (3 :: real)" by (subst ln_le_cancel_iff) simp_all
  also from x have "\<dots> \<le> ln x" by (subst ln_le_cancel_iff) simp_all
  finally have "ln 1 \<le> ln (ln x)" using x by (subst ln_le_cancel_iff) simp_all
  thus ?thesis by simp
qed

end