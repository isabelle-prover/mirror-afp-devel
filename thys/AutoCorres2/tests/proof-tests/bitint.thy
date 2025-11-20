(*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory bitint
  imports
    AutoCorres2_Main.AutoCorres_Main 
begin

declare [[ML_print_depth=1000, c_parser_feedback_level=1, c_parser_builtin_constant_p_constant_only=false]]
install_C_file "bitint.c"

autocorres "bitint.c"

thm final_defs
end