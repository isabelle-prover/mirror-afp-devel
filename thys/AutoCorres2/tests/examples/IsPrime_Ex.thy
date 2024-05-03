(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory IsPrime_Ex
imports
  "AutoCorres2_Main.AutoCorres_Main"
  "HOL-Computational_Algebra.Primes"
begin

(* Parse the input file. *)
install_C_file "is_prime.c"

(* Abstract the input file. *)
autocorres [unsigned_word_abs = is_prime_linear is_prime] "is_prime.c"

context is_prime_all_impl begin
thm is_prime'_def is_prime_linear'_def
end

definition
  "partial_prime p (n :: nat) \<equiv>
        (1 < p \<and> (\<forall>i \<in> {2 ..< min p n}. \<not> i dvd p))"

lemma partial_prime_ge [simp]:
     "\<lbrakk> p' \<ge> p \<rbrakk> \<Longrightarrow> partial_prime p p' = prime p"
  by (clarsimp simp: partial_prime_def prime_nat_iff' min_def)

lemma divide_self_plus_one [simp]: "(x dvd Suc x) = (x = 1)"
  apply (case_tac "x = 0", simp)
  apply (case_tac "x = 1", simp)
  apply (clarsimp simp: dvd_def)
  apply (case_tac "k = 0", simp)
  apply (case_tac "k = 1", simp)
  apply (subgoal_tac "x * 2 \<le> x * k")
   apply (subgoal_tac "Suc x < x * 2")
    apply simp
   apply clarsimp
  apply clarsimp
  done

lemma partial_prime_Suc [simp]:
  "partial_prime p (Suc n)
              = (partial_prime p n \<and> (1 < n \<and> Suc n < p \<longrightarrow> \<not> n dvd p))"
   apply (clarsimp simp: partial_prime_def min_def atLeastLessThanSuc not_le)
  apply (case_tac "p = Suc n")
   apply (clarsimp simp: atLeastLessThanSuc)
  apply fastforce
  done

lemma mod_to_dvd:
   "(n mod i \<noteq> 0) = (\<not> i dvd (n :: nat))"
  by (clarsimp simp: dvd_eq_mod_eq_0)

lemma prime_of_product [simp]: "prime ((a::nat) * b) = ((a = 1 \<and> prime b) \<or> (prime a \<and> b = 1))"
  by (metis mult.commute mult.right_neutral prime_product)

lemma partial_prime_2 [simp]: "(partial_prime a 2) = (a > 1)"
  by (clarsimp simp: partial_prime_def)

definition [simp]:
  "is_prime_linear_inv n i s \<equiv> (1 < i \<and> 1 < n \<and> i \<le> n \<and> partial_prime n i)"


theorem (in ts_definition_is_prime_linear) is_prime_correct:
    "n \<le> UINT_MAX \<Longrightarrow> is_prime_linear' n \<bullet> s \<lbrace> \<lambda>r _. (r \<noteq> Result 0) \<longleftrightarrow> prime n \<rbrace>"
  unfolding is_prime_linear'_def
  apply (runs_to_vcg)
  subgoal 
    by (simp add: prime_nat_iff')
  subgoal
    apply (simp add:)
  apply (rule runs_to_whileLoop_exn [
      where I="\<lambda>Exn e \<Rightarrow> (\<lambda>s. (0 < e) = prime n) | Result r \<Rightarrow> (\<lambda>s. is_prime_linear_inv n r s)"
                  and R="measure (\<lambda>(r, s). n - r)"])
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal
      by runs_to_vcg auto
    done
  done



lemma not_prime:
    "\<lbrakk> \<not> prime (a :: nat); a > 1 \<rbrakk> \<Longrightarrow> \<exists>x y. x * y = a \<and> 1 < x \<and> 1 < y \<and> x * x \<le> a"
  apply (clarsimp simp: prime_nat_iff dvd_def)
  apply (case_tac "m > k")
   apply (metis Suc_lessD Suc_lessI less_imp_le_nat mult.commute nat_0_less_mult_iff nat_mult_less_cancel_disj)
  apply fastforce
  done

lemma sqrt_prime:
  "\<lbrakk> a * a > n; \<forall>x<a. (x dvd n) = (x = Suc 0 \<or> x = n); 1 < n \<rbrakk> \<Longrightarrow> prime n"
  apply (rule ccontr)
  apply (drule not_prime)
   apply clarsimp
  apply (metis dvd_triv_right less_le_trans mult.commute mult_le_cancel2
           One_nat_def less_eq_nat.simps(1) less_not_refl2
           mult_eq_self_implies_10 not_less)
  done

lemma partial_prime_sqr:
     "\<lbrakk> n * n > p \<rbrakk> \<Longrightarrow> partial_prime p n = prime p"
  apply (case_tac "n \<ge> p")
   apply clarsimp
  apply (case_tac "partial_prime p n")
   apply clarsimp
   apply (erule sqrt_prime)
    apply (clarsimp simp: partial_prime_def)
    apply (case_tac "x = 0", simp)
    apply (case_tac "x = 1", simp)
    apply (frule_tac x=x in bspec)
     apply (clarsimp simp: min_def)
    apply clarsimp
   apply (clarsimp simp: not_le partial_prime_def)
  apply (case_tac "p = 0", simp)
  apply (case_tac "p = 1", simp)
  apply (auto simp: not_le partial_prime_def min_def prime_nat_iff')
  done

definition "SQRT_UINT_MAX \<equiv> 65536 :: nat"

lemma uint_max_factor [simp]:
  "UINT_MAX = SQRT_UINT_MAX * SQRT_UINT_MAX - 1"
  by (clarsimp simp: UINT_MAX_def SQRT_UINT_MAX_def)

lemma prime_dvd:
    "\<lbrakk> prime (p::nat) \<rbrakk> \<Longrightarrow> (r dvd p) = (r = 1 \<or> r = p)"
  by (fastforce simp: prime_nat_iff)

definition is_prime_inv
  where [simp]: "is_prime_inv n i s \<equiv> (1 < i \<and> i \<le> n \<and> i \<le> SQRT_UINT_MAX \<and> i * i \<le> SQRT_UINT_MAX * SQRT_UINT_MAX \<and> partial_prime n i)"

lemma nat_leE: "\<lbrakk> (a::nat) \<le> b; a < b \<Longrightarrow> R; a = b \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  apply atomize_elim
    apply clarsimp
  done

lemma sqr_less_mono [simp]:
    "((i::nat) * i < j * j) = (i < j)"
  by (metis (full_types) le0 less_not_refl3 linorder_neqE_nat
        mult_strict_mono' order.strict_trans)

lemma [simp]: "(a - b < a - c) = ((b::nat) > c \<and> c < a)"
  by arith

declare mult_le_mono [intro]

lemma sqr_le_sqr_minus_1 [simp]:
    "\<lbrakk> b \<noteq> 0 \<rbrakk> \<Longrightarrow> (a * a \<le> b * b - Suc 0) = (a < b)"
  by (simp add: nat_le_Suc_less)

lemma Suc_USHORT_MAX [simp]: "Suc USHORT_MAX = SQRT_UINT_MAX"
  by (simp add: USHORT_MAX_def SQRT_UINT_MAX_def)

theorem (in ts_definition_is_prime) is_prime_faster_correct:
  notes times_nat.simps(2) [simp del] mult_Suc_right [simp del]
  shows "n \<le> UINT_MAX \<Longrightarrow> is_prime' n \<bullet> s \<lbrace> \<lambda>r s. (r \<noteq> Result 0) \<longleftrightarrow> prime n \<rbrace>"
  unfolding is_prime'_def
  apply (runs_to_vcg)
  subgoal
    by (simp add: prime_nat_iff')
  subgoal
    apply simp
    apply (rule runs_to_whileLoop_exn [
      where I="\<lambda>Exn e \<Rightarrow> (\<lambda>s. (0 < e) = prime n) | Result r \<Rightarrow> (\<lambda>s. is_prime_inv n r s)"
                  and R="measure (\<lambda>(r, s). (Suc n) * (Suc n) - r * r)"])
    subgoal by simp
    subgoal
      by (simp add: SQRT_UINT_MAX_def)
    subgoal 
      apply simp
      using partial_prime_sqr by fastforce
    subgoal by simp
    subgoal
      apply runs_to_vcg 
      apply auto
      using le_Suc_eq by force
    done
  done

end


