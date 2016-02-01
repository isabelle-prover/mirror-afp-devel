
(* Authors: Amine Chaieb & Florian Haftmann, TU Muenchen with contributions by Lukas Bulwahn *)

section {* Stirling numbers of first and second kind *}

theory Stirling
imports Binomial
begin

subsection {* Stirling numbers of the second kind *}

fun Stirling :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "Stirling 0 0 = 1"
| "Stirling 0 (Suc k) = 0"
| "Stirling (Suc n) 0 = 0"
| "Stirling (Suc n) (Suc k) = Suc k * Stirling n (Suc k) + Stirling n k"

lemma Stirling_1 [simp]:
  "Stirling (Suc n) (Suc 0) = 1"
  by (induct n) simp_all

lemma Stirling_less [simp]:
  "n < k \<Longrightarrow> Stirling n k = 0"
  by (induct n k rule: Stirling.induct) simp_all

lemma Stirling_same [simp]:
  "Stirling n n = 1"
  by (induct n) simp_all

lemma Stirling_2_2:
  "Stirling (Suc (Suc n)) (Suc (Suc 0)) = 2 ^ Suc n - 1"
proof (induct n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have "Stirling (Suc (Suc (Suc n))) (Suc (Suc 0)) =
    2 * Stirling (Suc (Suc n)) (Suc (Suc 0)) + Stirling (Suc (Suc n)) (Suc 0)" by simp
  also have "\<dots> = 2 * (2 ^ Suc n - 1) + 1"
    by (simp only: Suc Stirling_1)
  also have "\<dots> = 2 ^ Suc (Suc n) - 1"
  proof -
    have "(2::nat) ^ Suc n - 1 > 0" by (induct n) simp_all
    then have "2 * ((2::nat) ^ Suc n - 1) > 0" by simp
    then have "2 \<le> 2 * ((2::nat) ^ Suc n)" by simp
    with add_diff_assoc2 [of 2 "2 * 2 ^ Suc n" 1]
      have "2 * 2 ^ Suc n - 2 + (1::nat) = 2 * 2 ^ Suc n + 1 - 2" .
    then show ?thesis by (simp add: nat_distrib)
  qed
  finally show ?case by simp
qed

lemma Stirling_2:
  "Stirling (Suc n) (Suc (Suc 0)) = 2 ^ n - 1"
  using Stirling_2_2 by (cases n) simp_all

subsection {* Stirling numbers of the first kind *}

fun stirling :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "stirling 0 0 = 1"
| "stirling 0 (Suc k) = 0"
| "stirling (Suc n) 0 = 0"
| "stirling (Suc n) (Suc k) = n * stirling n (Suc k) + stirling n k"

lemma stirling_less [simp]:
  "n < k \<Longrightarrow> stirling n k = 0"
  by (induct n k rule: stirling.induct) simp_all

lemma stirling_same [simp]:
  "stirling n n = 1"
  by (induct n) simp_all

lemma stirling_Suc_n_1:
  "stirling (Suc n) (Suc 0) = fact n"
  by (induct n) auto

lemma stirling_Suc_n_n:
  shows "stirling (Suc n) n = Suc n choose 2"
by (induct n) (auto simp add: numerals(2))

lemma stirling_Suc_n_2:
  assumes "n \<ge> Suc 0"
  shows "stirling (Suc n) 2 = (\<Sum>k=1..n. fact n div k)"
using assms
proof (induct n)
  case 0 from this show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases n)
    case 0 from this show ?thesis by (simp add: numerals(2))
  next
    case Suc
    from this have geq1: "Suc 0 \<le> n" by simp
    find_theorems "_ dvd (fact _)"
    have "stirling (Suc (Suc n)) 2 = Suc n * stirling (Suc n) 2 + stirling (Suc n) (Suc 0)"
      by (simp only: stirling.simps(4)[of "Suc n"] numerals(2))
    also have "... = Suc n * (\<Sum>k=1..n. fact n div k) + fact n"
      using Suc.hyps[OF geq1]
      by (simp only: stirling_Suc_n_1 of_nat_fact of_nat_add of_nat_mult)
    also have "... = Suc n * (\<Sum>k=1..n. fact n div k) + Suc n * fact n div Suc n"
      by (metis nat.distinct(1) nonzero_mult_divide_cancel_left)
    also have "... = (\<Sum>k=1..n. fact (Suc n) div k) + fact (Suc n) div Suc n"
      by (simp add: setsum_right_distrib div_mult_swap dvd_fact)
    also have "... = (\<Sum>k=1..Suc n. fact (Suc n) div k)" by simp
    finally show ?thesis .
  qed
qed

lemma of_nat_stirling_Suc_n_2:
  assumes "n \<ge> Suc 0"
  shows "(of_nat (stirling (Suc n) 2)::'a::field_char_0) = fact n * (\<Sum>k=1..n. (1 / of_nat k))"
using assms
proof (induct n)
  case 0 from this show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases n)
    case 0 from this show ?thesis by (auto simp add: numerals(2))
  next
    case Suc
    from this have geq1: "Suc 0 \<le> n" by simp
    have "(of_nat (stirling (Suc (Suc n)) 2)::'a) =
      of_nat (Suc n * stirling (Suc n) 2 + stirling (Suc n) (Suc 0))"
      by (simp only: stirling.simps(4)[of "Suc n"] numerals(2))
    also have "... = of_nat (Suc n) * (fact n * (\<Sum>k = 1..n. 1 / of_nat k)) + fact n"
      using Suc.hyps[OF geq1]
      by (simp only: stirling_Suc_n_1 of_nat_fact of_nat_add of_nat_mult)
    also have "... = fact (Suc n) * (\<Sum>k = 1..n. 1 / of_nat k) + fact (Suc n) * (1 / of_nat (Suc n))"
      using of_nat_neq_0 by auto
    also have "... = fact (Suc n) * (\<Sum>k = 1..Suc n. 1 / of_nat k)"
      by (simp add: distrib_left)
    finally show ?thesis .
  qed
qed

lemma setsum_stirling:
  "(\<Sum>k\<le>n. stirling n k) = fact n"
proof (induct n)
  case 0
  from this show ?case by simp
next
  case (Suc n)
  have "(\<Sum>k\<le>Suc n. stirling (Suc n) k) = stirling (Suc n) 0 + (\<Sum>k\<le>n. stirling (Suc n) (Suc k))"
    by (simp only: setsum_atMost_Suc_shift)
  also have "\<dots> = (\<Sum>k\<le>n. stirling (Suc n) (Suc k))" by simp
  also have "\<dots> = (\<Sum>k\<le>n. n * stirling n (Suc k) + stirling n k)" by simp
  also have "\<dots> = n * (\<Sum>k\<le>n. stirling n (Suc k)) + (\<Sum>k\<le>n. stirling n k)"
    by (simp add: setsum.distrib setsum_right_distrib)
  also have "\<dots> = n * fact n + fact n"
  proof -
    have "n * (\<Sum>k\<le>n. stirling n (Suc k)) = n * ((\<Sum>k\<le>Suc n. stirling n k) - stirling n 0)"
      by (metis add_diff_cancel_left' setsum_atMost_Suc_shift)
    also have "\<dots> = n * (\<Sum>k\<le>n. stirling n k)" by (cases n) simp+
    also have "\<dots> = n * fact n" using Suc.hyps by simp
    finally have "n * (\<Sum>k\<le>n. stirling n (Suc k)) = n * fact n" .
    moreover have "(\<Sum>k\<le>n. stirling n k) = fact n" using Suc.hyps .
    ultimately show ?thesis by simp
  qed
  also have "\<dots> = fact (Suc n)" by simp
  finally show ?case .
qed

end
