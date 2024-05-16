(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Swap_Ex
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin


(* Parse the input file. *)
install_C_file  "swap.c"

(* Abstract the input file. *)
autocorres "swap.c"

context ts_definition_swap begin

(* Direct proof on the heap. *)
lemma
  fixes a :: "word32 ptr" and b :: "word32 ptr"
  shows "ptr_valid (heap_typing s) a \<Longrightarrow> heap_w32 s a = x
           \<Longrightarrow> ptr_valid (heap_typing s) b \<Longrightarrow> heap_w32 s b = y \<Longrightarrow>
           swap' a b \<bullet> s
        \<lbrace> \<lambda>r s. heap_w32 s a = y \<and> heap_w32 s b = x \<rbrace>"
  apply (unfold swap'_def)
  apply runs_to_vcg
  apply (auto simp: fun_upd_apply upd_fun_def)
  done

end

end
