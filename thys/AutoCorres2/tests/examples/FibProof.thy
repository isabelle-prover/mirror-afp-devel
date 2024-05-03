(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
(*
A story of AutoCorres and recursion.

To do:
-- prove SIMPL total correctness
-- remove (* slow *) steps
-- remove word32 metis (or wait for word lifting...)
-- fix wp to support recursive fib'
-- Isar style proof?
*)

theory FibProof
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

(*
 * The venerable Fibonacci function.
 *)
fun fibo :: "nat \<Rightarrow> nat" where
  "fibo 0 = 0" |
  "fibo (Suc 0) = Suc 0" |
  "fibo (Suc (Suc n)) = fibo n + fibo (Suc n)"
declare fibo.simps [simp del]

lemma fibo_alt_def: "fibo n = (if n = 0 then 0 else if n = 1 then 1 else fibo (n - 1) + fibo (n - 2))"
  apply (induct n rule: less_induct)
  apply (rename_tac n, case_tac n, simp add: fibo.simps)
  apply (rename_tac n1, case_tac n1, simp add: fibo.simps)
  apply (simp add: fibo.simps)
  done

lemma fibo_mono_Suc: "fibo n \<le> fibo (Suc n)"
  by (simp add: fibo_alt_def)
lemma fibo_mono: "a \<le> b \<Longrightarrow> fibo a \<le> fibo b"
  by (metis mono_iff_le_Suc mono_def fibo_mono_Suc)

lemma fibo_mono_strict: "n \<ge> 2 \<Longrightarrow> fibo n < fibo (Suc n)"
  apply (case_tac n, simp)
  apply (rename_tac n', subgoal_tac "fibo (Suc 0) \<le> fibo n'")
   apply (simp add: fibo.simps)
  apply (simp add: fibo_mono)
  done

lemma fiboI: "\<lbrakk> a + 1 = b; b + 1 = c \<rbrakk> \<Longrightarrow> fibo a + fibo b = fibo c"
  by (auto simp: fibo.simps)

(*
 * We write two versions in C, and compare correctness proofs on the
 * SIMPL and AutoCorres embeddings.
 *)


(*
 * C arithmetic is done using `unsigned', which is translated as `word32'.
 * So, it is much easier to prove that the C code implements this function,
 * which is not quite the same function as fibo.
 *)
function fibo32 :: "word32 \<Rightarrow> word32" where
  "fibo32 n = (if n = 0 then 0 else if n = 1 then 1 else fibo32 (n - 1) + fibo32 (n - 2))"
apply auto
done
termination fibo32
  by (relation "measure (\<lambda>x. unat x)", (simp|unat_arith)+)
declare fibo32.simps [simp del]

lemma fibo32_0 [simp]: "fibo32 0 = 0"
  by (subst fibo32.simps) auto

lemma fibo32_1 [simp]: "fibo32 1 = 1"
  by (subst fibo32.simps) auto

(*
 * But we really want to say that the C code does implement fibo
 * (at least up till 2971215073 < 2^32)...
 *)
lemma fibo_greater: "(6 + n) < fibo (6 + n)"
  apply (induct n)
   apply eval
  apply (subst add_Suc_right)+
  apply (subgoal_tac "Suc (6 + n) \<le> fibo (6 + n)")
   apply (subgoal_tac "fibo (6 + n) < fibo (Suc (6 + n))")
    apply simp
   apply (rule fibo_mono_strict)
   apply simp
  apply simp
  done
lemma fibo_greater': "n \<ge> 6 \<Longrightarrow> n < fibo n"
  by (metis le_iff_add fibo_greater)
lemma unat_word32_plus: "unat x + unat y < 2^32 \<Longrightarrow> unat x + unat y = unat (x + y :: word32)"
  by (metis len32 unat_of_nat_len word_arith_nat_add)

(* ... so we should say that too. *)
lemma fibo32_is_fibo: "fibo n < 2^32 \<Longrightarrow> fibo n = unat (fibo32 (of_nat n))"
  apply (induct n rule: less_induct)
  apply (subst fibo32.simps)
  apply (subst fibo_alt_def)
  apply (rename_tac n, case_tac "n = 0", simp)
  apply (case_tac "n = 1", simp)
  apply (subgoal_tac "n < 2^32"
                     "fibo (n - 1) + fibo (n - 2) < 2^32"
                     "of_nat n \<noteq> (0 :: word32)"
                     "of_nat n \<noteq> (1 :: word32)"
                     "fibo (n - 1) < 2^32"
                     "fibo (n - 2) < 2^32"
                     "fibo (n - 1) = unat (fibo32 (of_nat (n - 1)))"
                     "fibo (n - 2) = unat (fibo32 (of_nat (n - 2)))")
          apply (fastforce intro: unat_word32_plus)
         apply (metis diff_less gr0I zero_less_numeral)
        apply (metis diff_less gr0I zero_less_one)
       apply simp
      apply simp
     apply (metis len32 unat_1 unat_of_nat_len)
    apply (metis len32 unat_0 unat_of_nat_len)
   apply (metis fibo_alt_def)
  apply (case_tac "n < 6")
   apply simp
  apply (subgoal_tac "n < fibo n")
   apply simp
  apply (simp add: fibo_greater')
done

(* A helper for the SIMPL proofs later. *)
lemma fibo32_rec: "\<lbrakk> a < a + 2; b = a + 1; c = a + 2 \<rbrakk> \<Longrightarrow> fibo32 a + fibo32 b = fibo32 c"
  apply (subst(3) fibo32.simps)
  apply simp
  apply safe
     apply unat_arith
    apply (metis not_le overflow_plus_one_self word_n1_ge word_not_simps(1))
   apply (metis word_not_simps(1))
  apply (simp add: field_simps)
  done



(* First we invoke CParser to translate the C code to SIMPL. *)
install_C_file "fib.c"


context fib_simpl begin
(* fib_linear\<^bsub>C\<^esub> is the linear-time implementation. *)
thm fib_linear_body_def
(* fib\<^bsub>C\<^esub> is the pretty (inefficient) recursive implementation. *)
thm fib_body_def
(* First, let us prove that they implement fibo32. *)
end

(* First, the linear version. *)
lemma (in fib_linear_impl) fib_linear_simpl_spec:
"\<Gamma> \<turnstile> {s. s = t}
     \<acute>ret' :== CALL fib_linear(\<acute>n)
     \<lbrace> (\<acute>ret' = fibo32 \<^bsup>t\<^esup>n) \<rbrace>"
  (* We have not annotated the code yet, so we cannot apply vcg usefully. *)
  (* First we expand the function call and defer the overall precondition. *)
  apply vcg_step
   defer
   (* Now we annotate the loop with the correct invariant and termination measure. *)
   apply (subst whileAnno_def)
   apply (subst whileAnno_def [symmetric,
     where I=" \<lbrace> \<acute>a = fibo32 (\<^bsup>t\<^esup>n - \<acute>n) \<and> \<acute>n \<le> \<^bsup>t\<^esup>n \<and> (\<acute>n \<noteq> 0 \<longrightarrow> (\<acute>b = fibo32 (\<^bsup>t\<^esup>n + 1 - \<acute>n))) \<rbrace>"
     and V="measure (\<lambda>s. unat (\<^bsup>s\<^esup>n))"])
   apply vcg
  (* It is mostly word arithmetic from here on. *)
    apply (simp add: scast_def field_simps)
    apply clarsimp
    apply (case_tac "n = 0")
     apply clarsimp
    apply (case_tac "n = 1")
     apply (rename_tac n1, subgoal_tac "n1 = 1")
      apply simp
     apply unat_arith
    apply (rename_tac n1, case_tac "n1 = 1")
     apply simp
    apply clarsimp
    apply safe
       apply (metis linear word_must_wrap)
      apply (rule fibo32_rec)
        (* unat_arith is too slow for this subgoal *)
        apply (subst word_less_nowrapI'[where k = 2 and z = "-1"])
           apply (subgoal_tac "n1 \<ge> 2")
            apply (metis word_n1_ge word_sub_le_iff word_sub_mono)
           apply unat_arith
          apply simp
         apply simp
        apply simp
       apply (simp add: field_simps)+
done

(* And the recursive version. *)


lemma (in fib_impl) fib_simpl_spec: "\<forall>n. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<lbrace>\<acute>n=n\<rbrace>  PROC fib(\<acute>n,\<acute>ret') \<lbrace>\<acute>ret' = fibo32 n\<rbrace>"
  apply (hoare_rule HoareTotal.ProcRec1[where r = "measure (\<lambda>(s, d). unat \<^bsup>s\<^esup>n)"])
  supply fibo32_0 [simp del]
  supply fibo32_1 [simp del]
  apply vcg
  apply (subst fibo32.simps, simp)
  apply (subst fibo32.simps, simp)
  apply (subst fibo32.simps[where n = n])
  apply unat_arith
  done

(*
 * We need to temporarily leave the local context to run autocorres.
 * Normally, we would run autocorres immediately after install_C_file.
 *)


autocorres [unsigned_word_abs = fib_linear, ts_rules=nondet] "fib.c"

context fib_all_impl begin

thm fib_linear'_def
thm fib'.simps fib'.simps[unfolded fun_app_def, folded One_nat_def]
thm call_fib'_def call_fib'_def[simplified]
end

(*
 * fib_linear\<^bsub>C\<^esub> has been lifted to fib_linear', using the option monad.
 * The option monad expresses programs that read the heap
 * and may fail. fib_linear\<^bsub>C\<^esub> does not read the heap, but its loop
 * might fail to terminate, so it cannot be a simple HOL function.
 *
 * Note that arithmetic in fib_linear' has been converted to type @{typ nat}.
 * This conversion is enabled by the word_abs option.
 * fib_linear' still matches the C code as long as calculations do not wrap around;
 * AutoCorres inserts an extra guard to ensure this.
 *)


(* Here we prove that fib_linear' implements fibo, assuming that
 * no calculations wrap around. *)

lemma (in ts_definition_fib_linear) fib_linear'_correct: 
  assumes bound: "fibo (Suc n) < UINT_MAX" shows "fib_linear' n \<bullet> s \<lbrace>\<lambda>Res r t. t = s \<and> r = fibo n\<rbrace>"
  unfolding fib_linear'_def
  supply runs_to_whileLoop_res  [where I = "\<lambda>(a, b, i) t. t=s \<and> i \<le> n \<and> a = fibo (n - i) \<and> (i \<noteq> 0 \<longrightarrow> (b = fibo (n - i + 1)))" and 
      R="measure (\<lambda>((_, _, i),_). i)", runs_to_vcg]
  apply (runs_to_vcg)
        apply (simp_all add: fibo.simps field_simps Suc_diff_le)
  subgoal
    using bound
    by (smt (verit, ccfv_SIG) diff_diff_cancel diff_is_0_eq diff_less_mono 
        fibo.simps(3) fibo_mono less_nat_zero_code nat_le_linear not_less_eq_eq)
  done


context ts_definition_fib
begin
thm fib'.simps (* Just a reminder *)
end

(*
 * Like fib_linear\<^bsub>C\<^esub>, fib\<^bsub>C\<^esub> is lifted to the option monad. If the measure parameter
 * is too small, fib' will fail instead of giving the result that would be
 * returned by fib\<^bsub>C\<^esub>.
 *)

(*
 * AutoCorres also generates a \<^bitalic>measure function\<^eitalic> for fib'. This function is
 * used to generate the measure parameter anywhere fib' is called. For example,
 *
 *   void call_fib(void) { fib(42); }
 *
 * is translated to:
 *)


thm nat_less_induct
thm word_induct_less 
thm measure_induct[where f="\<lambda>x. x::'a::len word"]

lemma (in ts_definition_fib)
  shows "fib' n \<bullet> s \<lbrace>\<lambda>Res r t. t = s \<and> r = fibo32 n\<rbrace>"
proof (induction n arbitrary: rule: measure_induct[where f="\<lambda>x. x::'a::len word"])
  case (1 n)
  note hyp = 1 [rule_format]
  show ?case 
  proof (cases "n=0")
    case True
    then show ?thesis apply (subst fib'.simps)
      apply runs_to_vcg
      apply (simp)
      done
  next
    case False
    note nonzero = False
    show ?thesis
    proof (cases "n=1")
      case True
      from True nonzero
      show ?thesis apply (subst fib'.simps)
        apply runs_to_vcg
         apply (simp_all)
        done
    next
      case False

      have hyp1[runs_to_vcg]: "fib' (n - 1) \<bullet> s \<lbrace>\<lambda>Res r t. t = s \<and> r = fibo32 (n - 1)\<rbrace>"
        apply (rule hyp)
        using nonzero by unat_arith

      have hyp2[runs_to_vcg]: "fib' (n - 2) \<bullet> s \<lbrace>\<lambda>Res r t. t = s \<and> r = fibo32 (n - 2)\<rbrace>"
        apply (rule hyp)
        using False nonzero
        by unat_arith


      from False nonzero
      show ?thesis apply (subst fib'.simps)
        apply runs_to_vcg
        subgoal by simp
        subgoal apply (simp add: fibo32.simps)
          done
        done
    qed
  qed
qed

end

