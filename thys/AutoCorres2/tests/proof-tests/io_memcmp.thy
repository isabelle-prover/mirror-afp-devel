(*
 * Copyright (c) 2025 Apple Inc. All rights reserved. 
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory io_memcmp
imports AutoCorres2_Main.AutoCorres_Main
begin

install_C_file "io_memcmp.c"

init-autocorres [
  in_out_globals = main1 do_memcmp,
  in_out_parameters =
    main() and
    do_memcmp() where disjoint[],
    no_heap_abs = do_memcmp,
    ts_force nondet = do_memcmp
] "io_memcmp.c"



autocorres "io_memcmp.c"

(* we don't want to have disjoint_set guard for the second call to do_memcmp*)
thm ts_def

end


