(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_struct_array
imports "AutoCorres2.CTranslation"
begin

declare [[ML_print_depth=1000,
c_parser_check_embedded_function_calls=true]]
install_C_file "parse_struct_array.c"

ML \<open>

val deps = ProgramAnalysis.get_variable_dependencies (the (CalculateState.get_csenv @{theory} "parse_struct_array.c"))
val embedded_fncall_exprs = ProgramAnalysis.get_embedded_fncall_exprs (the (CalculateState.get_csenv @{theory} "parse_struct_array.c"))

\<close>

term "globk2_'"


  thm f_body_def
  thm g_body_def
  thm h_body_def
  thm ts20110511_1_body_def
  thm ts20110511_2_body_def

ML \<open>
  val bthm = @{thm "ts20110511_1_body_def"}
  val b_t = Thm.concl_of bthm
  val cs = Term.add_consts b_t []
\<close>

ML \<open>member (op =) (map #1 cs) "CProof.strictc_errortype.C_Guard" orelse
      OS.Process.exit OS.Process.failure\<close>


end
