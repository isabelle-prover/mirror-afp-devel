(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Verification challenge by Norihisa Suzuki, posed in
 * "Automatic verification of programs with complex data structures", 1976.
 *)

theory Suzuki
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "suzuki.c"
autocorres [heap_abs_syntax] "suzuki.c"

context suzuki_impl
begin
thm suzuki_body_def
lemma
  "\<Gamma> \<turnstile>
     \<lbrace>distinct [\<acute>w, \<acute>x, \<acute>y, \<acute>z] \<and> (\<forall>p \<in> {\<acute>w, \<acute>x, \<acute>y, \<acute>z}. c_guard p)\<rbrace>
       Call suzuki.suzuki
     \<lbrace>\<acute>ret' = 4 \<comment> \<open>Return value\<close>\<rbrace>"
  apply vcg
  oops
end

context ts_definition_suzuki
begin
thm suzuki'_def
(* AutoCorres's heap abstraction makes the memory model much simpler. *)
lemma
  "distinct [w, x, y, z] \<Longrightarrow> (\<forall>p \<in> {w, x, y, z}.  ptr_valid (heap_typing s0) p) \<Longrightarrow>
     (suzuki' w x y z) \<bullet> s0
   \<lbrace>\<lambda>rv s. rv = Result 4 \<and> \<comment> \<open>Return value\<close>
           (\<exists>w' x' y' z'. s = s0[w := w'][x := x'][y := y'][z := z']) \<comment> \<open>Frame\<close>\<rbrace>"
  apply (unfold suzuki'_def)
  apply runs_to_vcg

  (* Return value, guards *)
     apply (simp_all add: fun_upd_apply)
  (* Frame rule *)
  (* fixme: heap_abs_simps is still incomplete; need to unfold heap wrappers instead *)
  apply (clarsimp simp:
          update_node_def
          update_node_next_def
          update_node_data_def
                        o_def fun_upd_apply)
  apply (blast intro: lifted_globals.fold_congs)
  done

end

end
