(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Simple
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin


(* Parse the input file. *)
install_C_file "simple.c"

(* Abstract the input file. *)

autocorres [ ts_force pure = max, ts_force nondet = gcd, unsigned_word_abs = gcd ] "simple.c"



context simple_all_corres begin
(* Generated theorems and proofs. *)
thm max'_def max'_ac_corres
thm gcd'_def gcd'_ac_corres
end

(* Show generated "max'" function matches in-built "max". *)
lemma (in ts_definition_max) "max' a b = max a b"
  unfolding max'_def max_def
  by (rule refl)

lemmas runs_to_whileLoop2 =  runs_to_whileLoop_res' [split_tuple C and B arity: 2]

(* Show "gcd'" calculates the gcd. *)
lemma (in ts_definition_gcd) gcd_wp: "gcd' a b \<bullet> s \<lbrace>\<lambda>r t. t = s \<and> r = Result (gcd a b)\<rbrace>"
  unfolding gcd'_def
  apply runs_to_vcg
  apply (subst runs_to_whileLoop2 [where
     I="\<lambda>(a', b') t. t = s \<and> gcd a b = gcd a' b'"
     and R="measure (\<lambda>((a', b'), s). a')"])
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal 
    apply simp
    apply (metis gcd.commute gcd_red_nat)
    done
  subgoal by simp
  done


lemma (in ts_definition_gcd) gcd_to_return [simp]:
    "gcd' a b = return (gcd a b)"
  apply (subst runs_to_always_progress_to_gets [where v="\<lambda>_. gcd a b"])
  subgoal by (rule gcd_wp)
  subgoal 
    unfolding gcd'_def
    by (intro always_progress_intros)
  subgoal 
    apply (simp add: gets_to_return)
    done
  done

end
