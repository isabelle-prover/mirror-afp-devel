(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory fnptr_skip_heap_abs_skip_word_abs
imports AutoCorres2_Main.AutoCorres_Main
begin

install_C_file "fnptr_skip_heap_abs_skip_word_abs.c"
autocorres [no_body = g unop binop binop_u, skip_heap_abs, skip_word_abs,ts_force exit = voidcaller, ts_rules = exit] fnptr_skip_heap_abs_skip_word_abs.c


end