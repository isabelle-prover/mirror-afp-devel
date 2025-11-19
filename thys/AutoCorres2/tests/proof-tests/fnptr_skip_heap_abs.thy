(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory fnptr_skip_heap_abs
imports AutoCorres2_Main.AutoCorres_Main
begin


declare [[c_parser_feedback_level=0, ML_print_depth=1000]]
install_C_file "fnptr.c"

autocorres [no_body = g unop binop binop_u, skip_heap_abs, ts_rules = exit, ts_force_known_functions = exit
] fnptr.c

context fnptr_global_addresses
begin
thm ts_def
thm \<P>_defs
thm final_defs
end
thm l1_g'_def
thm l2_g'_def
thm wa_g'_def
thm ts.g'_def
end