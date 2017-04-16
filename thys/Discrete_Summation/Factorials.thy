
(* Authors: Amine Chaieb & Florian Haftmann, TU Muenchen with a contribution by Lukas Bulwahn *)

section {* Falling factorials *}

theory Factorials
  imports Complex_Main "~~/src/HOL/Library/Stirling"
begin

lemma pochhammer_0 [simp]: -- \<open>TODO move\<close>
  "pochhammer 0 n = (0::nat)" if "n > 0"
  using that by (simp add: pochhammer_prod)

definition ffact :: "nat \<Rightarrow> 'a::comm_semiring_1_cancel \<Rightarrow> 'a"
  where "ffact n a = pochhammer (a + 1 - of_nat n) n"

lemma ffact_0 [simp]:
  "ffact 0 = (\<lambda>x. 1)"
  by (simp add: fun_eq_iff ffact_def)

lemma ffact_Suc:
  "ffact (Suc n) a = a * ffact n (a - 1)"
    for a :: "'a :: comm_ring_1"
  by (simp add: ffact_def pochhammer_prod prod.atLeast0_lessThan_Suc algebra_simps)

lemma ffact_Suc_rev:
  "ffact (Suc n) a = (a - of_nat n) * ffact n a"
    for a :: "'a :: comm_ring_1"
proof (induct n arbitrary: a)
  case 0
  then show ?case
    by (simp add: ffact_Suc)
next
  case (Suc n a)
  moreover have "- 2 + a = (a - 1) - 1"
    by simp
  ultimately have hyp:
    "ffact (Suc n) (a - 1) = (a - 1 - of_nat n) * ffact n (a - 1)"
    by (simp only:)
  have "ffact (Suc (Suc n)) a = a * ffact (Suc n) (a - 1)"
    by (simp add: ffact_Suc)
  also have "\<dots> = a * (ffact n (a - 1) * (a - of_nat (n + 1)))"
    by (simp only: hyp) (simp add: algebra_simps)
  also have "\<dots> = ffact (Suc n) a * (a - of_nat (Suc n))"
    by (simp add: algebra_simps ffact_Suc)
  finally have "ffact (Suc (Suc n)) a = ffact (Suc n) a * (a - of_nat (Suc n))" .
  then show ?case by (simp add: mult.commute)
qed

lemma ffact_nat_triv:
  "ffact n m = 0" if "m < n"
  using that by (simp add: ffact_def)

lemma ffact_Suc_nat:
  "ffact (Suc n) m = m * ffact n (m - 1)"
    for m :: nat
proof (cases "n \<le> m")
  case True
  then show ?thesis
    by (simp add: ffact_def pochhammer_prod algebra_simps prod.atLeast0_lessThan_Suc)
next
  case False
  then have "m < n"
    by simp
  then show ?thesis
    by (simp add: ffact_nat_triv)
qed
     
lemma fact_div_fact_ffact:
  "fact n div fact m = ffact (n - m) n" if "m \<le> n"
proof -
  from that have "fact n = ffact (n - m) n * fact m"
    by (simp add: ffact_def pochhammer_product pochhammer_fact)
  moreover have "fact m dvd (fact n :: nat)"
    using that by (rule fact_dvd)
  ultimately show ?thesis
    by simp
qed
      
lemma ffact_fact:
  "ffact n (of_nat n) = (of_nat (fact n) :: 'a :: comm_ring_1)"
  by (induct n) (simp_all add: algebra_simps ffact_Suc)

lemma ffact_add_diff_assoc:
  "(a - of_nat n) * ffact n a + of_nat n * ffact n a = a * ffact n a"
    for a :: "'a :: comm_ring_1"
  by (simp add: algebra_simps)

lemma mult_ffact:
  "a * ffact n a = ffact (Suc n) a + of_nat n * ffact n a"
    for a :: "'a :: comm_ring_1"
proof -
  have "ffact (Suc n) a + of_nat n * (ffact n a) = (a - of_nat n) * (ffact n a) + of_nat n * (ffact n a)"
    using ffact_Suc_rev [of n] by auto
  also have "\<dots> = a * ffact n a" using ffact_add_diff_assoc by (simp add: algebra_simps)
  finally show ?thesis by simp
qed

lemma of_nat_ffact:
  "of_nat (ffact n m) = ffact n (of_nat m :: 'a :: comm_ring_1)"
proof (induct n arbitrary: m)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  show ?case
  proof (cases m)
    case 0
    then show ?thesis
      by (simp add: ffact_Suc_nat ffact_Suc)
  next
    case (Suc m)
    with Suc.hyps show ?thesis
      by (simp add: algebra_simps ffact_Suc_nat ffact_Suc)
  qed
qed
      
lemma of_int_ffact:
  "of_int (ffact n k) = ffact n (of_int k :: 'a :: comm_ring_1)"
proof (induct n arbitrary: k)
  case 0 then show ?case by simp
next
  case (Suc n k)
  then have "of_int (ffact n (k - 1)) = ffact n (of_int (k - 1) :: 'a)" .
  then show ?case
    by (simp add: ffact_Suc_nat ffact_Suc)
qed


text {* Conversion of natural potences into falling factorials and back *}

lemma monomial_ffact:
  "a ^ n = (\<Sum>k = 0..n. of_nat (Stirling n k) * ffact k a)"
    for a :: "'a :: comm_ring_1"
proof (induct n)
  case 0 then show ?case by simp
next
  case (Suc n)
  then have "a ^ Suc n = a * (\<Sum>k = 0..n. of_nat (Stirling n k) * ffact k a)"
    by simp
  also have "\<dots> = (\<Sum>k = 0..n. of_nat (Stirling n k) * (a * ffact k a))"
    by (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> = (\<Sum>k = 0..n. of_nat (Stirling n k) * ffact (Suc k) a) +
    (\<Sum>k = 0..n. of_nat (Stirling n k) * (of_nat k * ffact k a))"
    by (simp add: sum.distrib algebra_simps mult_ffact)
  also have "\<dots> = (\<Sum>k = 0.. Suc n. of_nat (Stirling n k) * ffact (Suc k) a) +
    (\<Sum>k = 0..Suc n. of_nat ((Suc k) * (Stirling n (Suc k))) * (ffact (Suc k) a))"
  proof -
    have "(\<Sum>k = 0..n. of_nat (Stirling n k) * (of_nat k * ffact k a)) =
      (\<Sum>k = 0..n+2. of_nat (Stirling n k) * (of_nat k * ffact k a))" by simp
    also have "\<dots> = (\<Sum>k = Suc 0 .. Suc (Suc n). of_nat (Stirling n k) * (of_nat k * ffact k a)) "
      by (simp only: sum_head_Suc [of 0 "n + 2"]) simp
    also have "\<dots> = (\<Sum>k = 0 .. Suc n. of_nat (Stirling n (Suc k)) * (of_nat (Suc k) * ffact (Suc k) a))"
      by (simp only: image_Suc_atLeastAtMost sum_shift_bounds_cl_Suc_ivl)
    also have "\<dots> = (\<Sum>k = 0 .. Suc n. of_nat ((Suc k) * Stirling n (Suc k)) * ffact (Suc k) a)"
      by (simp only: of_nat_mult algebra_simps)
    finally have "(\<Sum>k = 0..n. of_nat (Stirling n k) * (of_nat k * ffact k a)) =
      (\<Sum>k = 0..Suc n. of_nat (Suc k * Stirling n (Suc k)) * ffact (Suc k) a)"
      by simp
    then show ?thesis by simp
  qed
  also have "\<dots> = (\<Sum>k = 0..n. of_nat (Stirling (Suc n) (Suc k)) * ffact (Suc k) a)"
    by (simp add: algebra_simps sum.distrib)
  also have "\<dots> = (\<Sum>k = Suc 0..Suc n. of_nat (Stirling (Suc n) k) * ffact k a)"
    by (simp only: image_Suc_atLeastAtMost sum_shift_bounds_cl_Suc_ivl)
  also have "\<dots> = (\<Sum>k = 0..Suc n. of_nat (Stirling (Suc n) k) * ffact k a)"
    by (simp only: sum_head_Suc [of "0" "Suc n"]) simp
  finally show ?case by simp
qed

lemma ffact_monomial:
  "ffact n a = (\<Sum>k = 0..n. (- 1) ^ (n - k) * of_nat (stirling n k) * a ^ k)"
    for a :: "'a :: comm_ring_1"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  then have "ffact (Suc n) a = (a - of_nat n) * (\<Sum>k = 0..n. (- 1) ^ (n - k) * of_nat (stirling n k) * a ^ k)"
    by (simp add: ffact_Suc_rev)
  also have "\<dots> = (\<Sum>k = 0..n. (- 1) ^ (n - k) * of_nat (stirling n k) * a ^ (Suc k)) +
    (\<Sum>k = 0..n. (- 1) * (- 1) ^ (n - k) * of_nat (n * (stirling n k)) * a ^ k)"
    by (simp only: diff_conv_add_uminus distrib_right) (simp add: sum_distrib_left field_simps)
  also have "\<dots> = (\<Sum>k = 0..n. (- 1) ^ (Suc n - Suc k) * of_nat (stirling n k) * a ^ Suc k) +
  (\<Sum>k = 0..n. (- 1) ^ (Suc n - Suc k) * of_nat (n * stirling n (Suc k)) * a ^ Suc k)"
  proof -
    have "(\<Sum>k = 0..n. (- 1) * (- 1) ^ (n - k) * of_nat (n * stirling n k) * a ^ k) =
      (\<Sum>k = 0..n. (- 1) ^ (Suc n - k) * of_nat (n * stirling n k) * a ^ k)"
      by (simp add: Suc_diff_le)
    also have "\<dots> = (\<Sum>k = Suc 0..Suc n. (- 1) ^ (Suc n - k) * of_nat (n * stirling n k) * a ^ k)"
      by (simp add: sum_head_Suc) (cases n; simp)
    also have "\<dots> = (\<Sum>k = 0..n. (- 1) ^ (Suc n - Suc k) * of_nat (n * stirling n (Suc k)) * a ^ Suc k)"
      by (simp only: sum_shift_bounds_cl_Suc_ivl)
    finally show ?thesis by simp
  qed
  also have "\<dots> = (\<Sum>k = 0..n. (- 1) ^ (Suc n - Suc k) * of_nat (n * stirling n (Suc k) + stirling n k) * a ^ Suc k)"
    by (simp add: sum.distrib algebra_simps)
  also have "\<dots> = (\<Sum>k = 0..n. (- 1) ^ (Suc n - Suc k) * of_nat (stirling (Suc n) (Suc k)) * a ^ Suc k)"
    by (simp only: stirling.simps)
  also have "\<dots> = (\<Sum>k = Suc 0..Suc n. (- 1) ^ (Suc n - k) * of_nat (stirling (Suc n) k) * a ^ k)"
    by (simp only: sum_shift_bounds_cl_Suc_ivl)
  also have "\<dots> = (\<Sum>k = 0..Suc n. (- 1) ^ (Suc n - k) * of_nat (stirling (Suc n) k) * a ^ k)"
    by (simp add: sum_head_Suc)
  finally show ?case .
qed

end
