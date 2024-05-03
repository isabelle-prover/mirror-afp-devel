(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory fnptr_large_array
  imports 
    AutoCorres2_Main.AutoCorres_Main
begin

install_C_file "fnptr_large_array.c"

autocorres fnptr_large_array.c
text \<open>\<close>
  \<comment> \<open>optimized performance of \<open>AutoCorresUtil.dyn_call_split_simp_sidecondition_tac\<close> with 
  @{ML Array_Selectors.array_selectors} enabled by default in @{command install_C_file}: takes about 60s\<close>

end