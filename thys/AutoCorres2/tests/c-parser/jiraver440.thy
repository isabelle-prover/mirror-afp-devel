(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver440
  imports "AutoCorres2.CTranslation"
begin

install_C_file "jiraver440.c"

context jiraver440_simpl
begin

thm f_body_def
thm g_body_def

lemma "f_body = g_body"
  by (simp add: f_body_def g_body_def locals)


end

end
