(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory mutual_recursion
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "mutual_recursion.c"

autocorres "mutual_recursion.c"

end
