(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver310
  imports "AutoCorres2.CTranslation"
begin

install_C_file "jiraver310.c"

context jiraver310_simpl
begin

  thm f_body_def
  thm g_body_def

  lemma "g_body = X"
  apply (simp add: g_body_def)
  oops

  thm h_body_def

end (* context *)

end (* theory *)
