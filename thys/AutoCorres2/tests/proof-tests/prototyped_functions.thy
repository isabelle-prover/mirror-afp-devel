(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory prototyped_functions
imports "AutoCorres2_Main.AutoCorres_Main"
begin

declare [[c_parser_assume_prototypes_pure]]
install_C_file "prototyped_functions.c"

autocorres [no_body = moo1 moo2 moo3 moo4, phase=L1, ts_force option = moo4, single_threaded] "prototyped_functions.c"

autocorres [ single_threaded, ts_force option = moo4] "prototyped_functions.c"


thm moo1'_def
thm wa_moo1'_def
thm moo2'_def
thm moo3'_def
thm moo4'_def

lemma "moo1' = OFUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  by (simp add: moo1'_def)

lemma "moo2' = OFUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  by (simp add: moo2'_def)

lemma "moo3' x = OFUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  by (simp add: moo3'_def)

lemma "moo4' = OFUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  by (simp add: moo4'_def)

context prototyped_functions_global_addresses 
begin
thm moo1'_ac_corres
thm l1_moo1'_corres
thm cow_body_def
end
end
