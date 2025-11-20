(*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
theory init_globals imports "AutoCorres2_Main.AutoCorres_Main" 
begin

thm signed_typ_heap_simulations

declare [[ML_print_depth=1000]]
declare [[allow_underscore_idents]]
install_C_file "init_globals.c"

thm init'globals_body_def

thm global_const_defs
thm global_const_selectors
thm global_const_array_selectors
thm global_const_non_array_selectors

thm init'globals_body_def

declare [[verbose=0]]
init-autocorres [(* no_heap_abs = "init'globals" *) ] "init_globals.c"

autocorres [] "init_globals.c"
thm final_defs
thm final_defs
thm fupdate_def

end
