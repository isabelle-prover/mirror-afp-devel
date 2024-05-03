(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Alloc_Ex
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin


(* Parse the input file. *)
include_C_file "alloc.h" for "alloc.c"
install_C_file  "alloc.c"

autocorres "alloc.c"

context alloc_all_impl begin

(* Bodies of translated functions. *)
thm max'_def
thm align_up'_def
thm alloc'_def
thm dealloc'_def
thm add_mem_pool'_def
thm init_allocator'_def

end

end
