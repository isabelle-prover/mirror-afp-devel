
(* Authors: Amine Chaieb & Florian Haftmann, TU Muenchen *)

header {* Falling factorials *}

theory Factorials
imports Complex_Main Stirling
begin

primrec ffact :: "nat \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a"
where
  "ffact 0 a = 1"
| "ffact (Suc n) a = a * ffact n (a - 1)"

lemma ffact_0 [simp]:
  "ffact 0 = (\<lambda>x. 1)"
  by (simp add: fun_eq_iff)

lemma ffact_fact:
  "ffact n (of_nat n) = of_nat (fact n)"
  by (induct n) (simp_all add: algebra_simps of_nat_mult)

lemma ffact_Suc:
  "ffact (Suc n) a = (a - of_nat n) * ffact n a"
proof (induct n arbitrary: a)
  case 0 thus ?case by simp
next
  case (Suc n a)
  moreover have "-2 + a = (a - 1) - 1"
    by simp
  ultimately have hyp:
    "ffact (Suc n) (a - 1) = (a - 1 - of_nat n) * ffact n (a - 1)"
    by (simp only:)
  have "ffact (Suc (Suc n)) a = a * ffact (Suc n) (a - 1)" by simp
  also have "\<dots> = a * (ffact n (a - 1) * (a - of_nat (n + 1)))"
    by (simp only: hyp) (simp add: algebra_simps)
  also have "\<dots> = ffact (Suc n) a * (a - of_nat (Suc n))" by (simp add: algebra_simps)
  finally have "ffact (Suc (Suc n)) a = ffact (Suc n) a * (a - of_nat (Suc n))" .
  then show ?case by (simp add: mult_commute)
qed

lemma ffact_add_diff_assoc:
  "(a - of_nat n) * ffact n a + of_nat n * ffact n a = a * ffact n a"
  by (simp add: algebra_simps)

lemma mult_ffact:
  "a * ffact n a = ffact (Suc n) a + of_nat n * ffact n a"
proof -
  have "ffact (Suc n) a + of_nat n * (ffact n a) = (a - of_nat n) * (ffact n a) + of_nat n * (ffact n a)"
    using ffact_Suc [of n] by auto
  also have "\<dots> = a * ffact n a" using ffact_add_diff_assoc by (simp add: algebra_simps)
  finally show ?thesis by simp
qed

lemma of_int_ffact:
  "of_int (ffact n k) = ffact n (of_int k)"
proof (induct n arbitrary: k)
  case 0 then show ?case by simp
next
  case (Suc n k) then have "of_int (ffact n (k - 1)) = ffact n (of_int (k - 1) :: 'a)" .
  then show ?case by simp
qed


text {* Conversion of natural potences into falling factorials *}

lemma monomial_ffact:
  "a ^ n = (\<Sum>k = 0..n. of_nat (Stirling n k) * ffact k a)"
proof (rule sym, induct n)
  case 0 then show ?case by simp
next
  case (Suc n) 
  then have "a ^ Suc n = a * (\<Sum>k = 0..n. of_nat (Stirling n k) * ffact k a)" 
    by simp
  also have "\<dots> = (\<Sum>k = 0..n. of_nat (Stirling n k) * (a * ffact k a))"
    by (simp add: setsum_right_distrib algebra_simps)
  also have "\<dots> = (\<Sum>k = 0..n. of_nat (Stirling n k) * ffact (Suc k) a) +
    (\<Sum>k = 0..n. of_nat (Stirling n k) * (of_nat k * ffact k a))" 
    by (simp add: setsum_addf algebra_simps mult_ffact)
  also have "\<dots> = (\<Sum>k = 0.. Suc n. of_nat (Stirling n k) * ffact (Suc k) a) + 
    (\<Sum>k = 0..Suc n. of_nat ((Suc k) * (Stirling n (Suc k))) * (ffact (Suc k) a))"
  proof -
    have "(\<Sum>k = 0..n. of_nat (Stirling n k) * (of_nat k * ffact k a)) =
      (\<Sum>k = 0..n+2. of_nat (Stirling n k) * (of_nat k * ffact k a))" by simp
    also have "\<dots> = (\<Sum>k = Suc 0 .. Suc (Suc n). of_nat (Stirling n k) * (of_nat k * ffact k a)) "
      by (simp only: setsum_head_Suc [of 0 "n + 2"]) simp
    also have "\<dots> = (\<Sum>k = 0 .. Suc n. of_nat (Stirling n (Suc k)) * (of_nat (Suc k) * ffact (Suc k) a))"
      by (simp only: image_Suc_atLeastAtMost setsum_shift_bounds_cl_Suc_ivl)
    also have "\<dots> = (\<Sum>k = 0 .. Suc n. of_nat ((Suc k) * Stirling n (Suc k)) * ffact (Suc k) a)"
      by (simp only: of_nat_mult algebra_simps)
    finally have "(\<Sum>k = 0..n. of_nat (Stirling n k) * (of_nat k * ffact k a)) = 
      (\<Sum>k = 0..Suc n. of_nat (Suc k * Stirling n (Suc k)) * ffact (Suc k) a)" 
      by simp
    then show ?thesis by simp
  qed
  also have "\<dots> = (\<Sum>k = 0..n. of_nat (Stirling (Suc n) (Suc k)) * ffact (Suc k) a)"
    by (simp add: algebra_simps setsum_addf)
  also have "\<dots> = (\<Sum>k = Suc 0..Suc n. of_nat (Stirling (Suc n) k) * ffact k a)"
    by (simp only: image_Suc_atLeastAtMost setsum_shift_bounds_cl_Suc_ivl)
  also have "\<dots> = (\<Sum>k = 0..Suc n. of_nat (Stirling (Suc n) k) * ffact k a)"
    by (simp only: setsum_head_Suc [of "0" "Suc n"]) simp
  finally show ?case by simp
qed

end

