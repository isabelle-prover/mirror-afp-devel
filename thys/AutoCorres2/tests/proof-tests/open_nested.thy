(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory open_nested
imports "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "open_nested.c"

declare [[verbose = 1, verbose_timing = 0, ML_print_depth = 1000]]

init-autocorres [addressable_fields =
 element_C.all
 outer.inner
 inner.array,
 single_threaded ] "open_nested.c"

autocorres open_nested.c

end
