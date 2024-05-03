(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Str2Long
  imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "str2long.c"
autocorres "str2long.c"

context ts_definition_str2long begin

(* When passed a finite string, str2long never fails *)
lemma "
        str2long' str \<bullet> s
      \<lbrace>\<lambda>_ _. True\<rbrace>"
  unfolding str2long'_def
  apply runs_to_vcg
  (* Need whileLoop invariant preconditions and friends *)
  oops

end
end
