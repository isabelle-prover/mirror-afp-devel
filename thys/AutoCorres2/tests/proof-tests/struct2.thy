(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory struct2
imports "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "struct2.c"

autocorres [ignore_addressable_fields_error, keep_going] "struct2.c"

end
