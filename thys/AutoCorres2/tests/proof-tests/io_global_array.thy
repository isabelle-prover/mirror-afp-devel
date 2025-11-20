(*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory io_global_array
  imports 
    AutoCorres2_Main.AutoCorres_Main
begin

install_C_file "io_global_array.c"
init-autocorres [in_out_parameters=,in_out_globals=f g] "io_global_array.c"
autocorres "io_global_array.c"

thm final_defs


end