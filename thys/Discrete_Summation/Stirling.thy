
(* Authors: Amine Chaieb & Florian Haftmann, TU Muenchen *)

header {* Stirling numbers of first and second kind *}

theory Stirling
imports Main
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

end
