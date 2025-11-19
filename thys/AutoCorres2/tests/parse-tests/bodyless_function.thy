(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory bodyless_function
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "bodyless_function.c"

autocorres "bodyless_function.c"

thm bodyless_body_def


thm wa_def
thm ts_def
thm ts_corres

end