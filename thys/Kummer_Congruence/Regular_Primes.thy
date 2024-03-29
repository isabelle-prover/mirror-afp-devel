(*
  File:     Kummer_Congruence/Regular_Primes.thy
  Author:   Manuel Eberl, University of Innsbruck

  Definition of regular primes
*)
section \<open>Regular primes\<close>
theory Regular_Primes
  imports Kummer_Congruence Zeta_Function.Zeta_Function
begin

(* TODO: all of this could be moved to the Bernoulli entry *)
definition regular_prime :: "nat \<Rightarrow> bool" where
  "regular_prime p \<longleftrightarrow> prime p \<and> (p = 2 \<or> (\<forall>k\<in>{2..p-3}. even k \<longrightarrow> \<not>p dvd bernoulli_num k))"

definition irregular_prime :: "nat \<Rightarrow> bool" where
  "irregular_prime p \<longleftrightarrow> prime p \<and> (p \<noteq> 2 \<and> (\<exists>k\<in>{2..p-3}. even k \<and> p dvd bernoulli_num k))"

lemma irregular_primeI:
  assumes "prime p" "p \<noteq> 2" "p dvd bernoulli_num k" "even k" "k \<in> {2..p-3}"
  shows   "irregular_prime p"
  unfolding irregular_prime_def using assms by blast

lemma bernoulli_32: "bernoulli 32 = -7709321041217 / 510"
  by (simp add: eval_bernpoly)

text \<open>
  The smallest irregular prime is 37.
\<close>
lemma irregular_prime_37: "irregular_prime 37"
proof -
  have "(-217) * 7709321041217 + 3280240521459 * 510 = (1 :: int)"
    by simp
  hence "coprime 7709321041217 (510 :: int)"
    by (rule coprimeI_via_bezout)    
  hence "bernoulli_num 32 = -7709321041217"
    using bernoulli_num_denom_eqI(1)[of 32 "-7709321041217" "510"] bernoulli_32 by simp
  thus ?thesis
    by (intro irregular_primeI[of _ 32]) simp_all
qed

text \<open>
  Irregularity of primes can be certified relatively easily with the code generator:
\<close>

experiment
begin

lemma irregular_59: "irregular_prime 59"
proof (rule irregular_primeI)
  show "int 59 dvd bernoulli_num 44"
    by eval
qed auto

lemma irregular_67: "irregular_prime 67"
proof (rule irregular_primeI)
  show "int 67 dvd bernoulli_num 58"
    by eval
qed auto

end

end