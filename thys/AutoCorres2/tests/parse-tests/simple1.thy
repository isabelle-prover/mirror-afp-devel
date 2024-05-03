(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory simple1
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "simple1.c"

autocorres "simple1.c"

context simple1_all_corres
begin
thm add_body_def
thm add'_def
end
end