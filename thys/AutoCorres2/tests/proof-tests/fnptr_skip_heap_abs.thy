(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory fnptr_skip_heap_abs
imports AutoCorres2_Main.AutoCorres_Main
begin

term gets_the
install_C_file "fnptr.c"
autocorres [skip_heap_abs,ts_force nondet = voidcaller] fnptr.c


end