(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory untouched_globals
imports "AutoCorres2.CTranslation"
begin


declare [[record_globinits=true, ML_print_depth=1000, c_parser_feedback_level=2]]
install_C_file "untouched_globals.c"
thm init'globals_body_def

(* 
Take all those globals that are not constant, and make an
SIMPL procedure: 

  g1 = g1_global_initializer ...
 ...

  These might be in the heap or in the globals record.
*
*)


ML \<open>
val globinits = ProgramAnalysis.get_fninfo (the (CalculateState.get_csenv @{theory} "untouched_globals.c"))
\<close>

ML \<open>
val globinits = ProgramAnalysis.get_globinits (the (CalculateState.get_csenv @{theory} "untouched_globals.c"))
\<close>
ML \<open>
val globs = ProgramAnalysis.get_globals (the (CalculateState.get_csenv @{theory} "untouched_globals.c"))
\<close>
ML \<open>
val vars = ProgramAnalysis.get_vars (the (CalculateState.get_csenv @{theory} "untouched_globals.c"))
\<close>

context untouched_globals_global_addresses
begin
thm outer1_def
thm array_int_initial_value_def
  thm x_def
  thm x_initial_value_def
  thm glob1_def
  thm glob1_initial_value_def
  thm glob2_def
  thm glob2_initial_value_def
  thm y_initial_value_def

lemma "x = 0" by (simp add: x_def)

lemma "y_initial_value = 1" by (unfold y_initial_value_def, simp)

lemma "c_C glob1 = 0" by (simp add: glob1_def)

lemma "c_C glob2 = 51" by (simp add: glob2_def)

end (* context *)

end (* theory *)
