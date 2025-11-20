(*
 * Copyright (c) 2025 Apple Inc. All rights reserved. 
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory io_for_break
imports AutoCorres2_Main.AutoCorres_Main
begin

install_C_file "io_for_break.c"

init-autocorres [
  in_out_parameters = f(x:"in_out") 
] "io_for_break.c"


autocorres "io_for_break.c"

thm final_defs
end


