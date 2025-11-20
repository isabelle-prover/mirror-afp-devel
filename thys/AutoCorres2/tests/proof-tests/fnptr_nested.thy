(*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory fnptr_nested
  imports 
    (*  AutoCorres2.CTranslation *)
    AutoCorres2_Main.AutoCorres_Main
  keywords
    "named_bindings" :: thy_decl
begin

install_C_file "fnptr_nested.c"

autocorres [no_body = f3 f4] "fnptr_nested.c"
thm final_defs
end