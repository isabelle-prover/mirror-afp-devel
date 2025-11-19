(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory underscore_funs
imports AutoCorres2_Main.AutoCorres_Main
begin

(*
declare [[allow_underscore_idents]]
*)

install_C_file "underscore_funs.c"
autocorres "underscore_funs.c"


thm l1_def
thm foo__body_def
thm bar_body_def
thm foo_body_def
thm ts_def

end
