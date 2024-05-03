(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_struct_array
imports "AutoCorres2.CTranslation"
begin

install_C_file "parse_struct_array.c"

term "globk2_'"


context parse_struct_array_simpl
begin

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

end
