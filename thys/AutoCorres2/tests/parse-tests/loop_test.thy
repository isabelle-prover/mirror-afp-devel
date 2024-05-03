(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory loop_test
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin


install_C_file "loop_test.c"

autocorres "loop_test.c"

end