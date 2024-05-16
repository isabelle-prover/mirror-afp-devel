(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Tests for handling Spec constructs emitted by the C parser.
 *)
theory Test_Spec_Translation
imports "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "test_spec_translation.c" [ghostty="nat"]

autocorres [ts_rules = nondet] "test_spec_translation.c"

context test_spec_translation_simpl begin
thm abort_body_def
thm ghost_upd_body_def
thm abort_body_def
end
context test_spec_translation_all_impl begin

thm ghost_upd'_def

(* Check that our translation did honour the given spec. *)
(*
lemma validNF_spec[runs_to_vcg]:
  "(\<exists>t. (s, t) \<in> f) \<Longrightarrow> (\<forall>t. (s, t) \<in> f \<longrightarrow> P () t) \<Longrightarrow>spec f \<bullet> s \<lbrace>P\<rbrace>"

  by (clarsimp simp: validNF_def NonDetMonad.valid_def no_fail_def spec_def)
*)
(* We don't know what this function does, but it's guaranteed to modify only "reg". *)
thm magic_body_def magic'_def

lemma magic'_wp[runs_to_vcg]:
  "P s \<Longrightarrow>  magic' x \<bullet> s \<lbrace>\<lambda>_ s. \<exists>x. P (s\<lparr>reg_'' := x\<rparr>)\<rbrace>"
  apply (unfold magic'_def)
  apply runs_to_vcg
   apply (cases s; fastforce)+
  done


(* This function is annotated with an assertion. *)
thm call_magic_body_def call_magic'_def

lemma call_magic'_wp:
  "of_int x < (42 :: 32 signed word) \<Longrightarrow>
   P s \<Longrightarrow>  call_magic' x \<bullet> s \<lbrace>\<lambda>_ s. \<exists>x. P (s\<lparr>reg_'' := x\<rparr>)\<rbrace>"
  apply (unfold call_magic'_def)
  apply runs_to_vcg
  done


(* This function is guaranteed to fail. *)
thm abort'_def abort_spec_def

lemma abort'_spec:
  "abort' = fail"
  apply (simp add: abort'_def)
  done

end

end
