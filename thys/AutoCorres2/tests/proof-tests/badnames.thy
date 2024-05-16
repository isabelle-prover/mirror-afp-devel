(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Test handling of C idents that are unusual or at risk of conflicting with other names.
 *)
theory badnames imports "AutoCorres2_Main.AutoCorres_Main" begin

declare [[allow_underscore_idents]]

install_C_file "badnames.c"

autocorres "badnames.c"


end
