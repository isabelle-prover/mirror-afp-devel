(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory Plus_Ex
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "plus.c"
autocorres [ts_force nondet = plus2] "plus.c"

context ts_definition_plus begin

thm plus'_def
(* 3 + 2 should be 5 *)
lemma "plus' 3 2 = 5"
  unfolding plus'_def
  by eval

(* plus does what it says on the box *)
lemma plus_correct: "plus' a b = a + b"
  unfolding plus'_def
  apply (rule refl)
  done

end

(* Compare pre-lifting to post-lifting *)
context plus_all_corres 
begin
thm plus2_body_def
thm plus2'_def
end

lemmas runs_to_whileLoop2 =  runs_to_whileLoop_res' [split_tuple C and B arity: 2]

(* plus2 does what it says on the box *)
lemma (in ts_definition_plus2) plus2_correct: "plus2' a b \<bullet> s \<lbrace> \<lambda>r s. r = Result (a + b)\<rbrace>"
  unfolding plus2'_def
  apply (runs_to_vcg)
  apply (rule runs_to_whileLoop2 [
    where I="\<lambda>(a', b') s. a' + b' = a + b"
      and R="measure (\<lambda>((a', b'), s). unat b')"])
     by (auto simp: not_less measure_unat)

(* plus2 does what it says on plus's box *)
lemma (in plus_all_impl) plus2_is_plus: "plus2' a b \<bullet> s\<lbrace> \<lambda>r s. r = Result (plus' a b )\<rbrace>"
  unfolding plus'_def
  supply plus2_correct[runs_to_vcg]
  apply runs_to_vcg
  done

(* Prove plus2 with no failure *)
lemma (in ts_definition_plus2) plus2_valid:"plus2' a b \<bullet> s \<lbrace> \<lambda>r s. r = Result (a + b) \<rbrace>"
  unfolding plus2'_def
  apply (runs_to_vcg)
  apply (rule runs_to_whileLoop2 [
    where I="\<lambda>(a', b') s. a' + b' = a + b"
      and R="measure (\<lambda>((a', b'), s). unat b')"])
  by (auto simp: not_less measure_unat)

end

