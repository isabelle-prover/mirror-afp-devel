(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Kmalloc
imports "AutoCorres2_Main.AutoCorres_Main"
begin


(* No proof here, just testing the parser. *)

consts
  KMC :: addr
  ptr_retyps :: "nat \<Rightarrow> addr \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc"

install_C_file "kmalloc.c"

autocorres [phase=L2] "kmalloc.c"
autocorres [no_heap_abs = free sep_free sep_alloc] "kmalloc.c"

context kmalloc_all_corres begin
thm l1_alloc'_def
thm l1_opt_alloc'_def


(* C parser output. *)
thm alloc_body_def
thm sep_alloc_body_def
thm free_body_def
thm sep_free_body_def

(* Abstracted output. *)
thm alloc'_def \<comment> \<open>lifted into split heap\<close>
thm sep_alloc'_def \<comment> \<open>not lifted: remains in monolithic byte-level heap\<close>
thm free'_def \<comment> \<open>not lifted: remains in monolithic byte-level heap\<close>
thm sep_free'_def \<comment> \<open>not lifted: remains in monolithic byte-level heap\<close>

end

end
