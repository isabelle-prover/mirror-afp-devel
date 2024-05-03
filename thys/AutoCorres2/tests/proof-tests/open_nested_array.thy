(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory open_nested_array
imports "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "open_nested_array.c"

init-autocorres [addressable_fields = outer_C.inners] "open_nested_array.c"

thm ptr_valid

autocorres open_nested_array.c


end
