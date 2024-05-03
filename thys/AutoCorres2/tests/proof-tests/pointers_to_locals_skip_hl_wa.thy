(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
theory pointers_to_locals_skip_hl_wa imports "AutoCorres2_Main.AutoCorres_Main" 
begin

install_C_file "pointers_to_locals_skip_hl_wa.c"
autocorres [
  skip_heap_abs,
  skip_word_abs
] "pointers_to_locals_skip_hl_wa.c"

context ts_corres_g
begin
thm ts_def
end
end