(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory kmalloc0
imports "AutoCorres2.CTranslation" "MachineWords"
begin

(* no proof here, just testing the parser *)

consts
  KMC :: word32
  ptr_retyps :: "nat \<Rightarrow> machine_word \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc"

install_C_file "kmalloc0.c"

context kmalloc0_simpl begin

thm alloc_body_def
thm free_body_def

end

end
