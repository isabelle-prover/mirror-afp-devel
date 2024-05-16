(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory partial_open_nested
  imports
    "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "partial_open_nested.c"

term True

declare [[show_types=false, show_sorts=false,
 verbose = 0, verbose_timing = 0, ML_print_depth = 1000, goals_limit=20]]

init-autocorres [
  addressable_fields =
    A.f1
    A.f3
    A.f2
    B.a
    B.f4
    B.f6
    B.f7,
  single_threaded
] "partial_open_nested.c"

autocorres "partial_open_nested.c"

end
