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

context bodyless_function_simpl
begin
thm local.bodyless_body_def
end
context ts_corres_call_bodyless
begin
thm wa_def
thm ts_def
thm ts_corres
end

end