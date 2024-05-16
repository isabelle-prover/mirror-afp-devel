(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver443a
  imports "AutoCorres2.CTranslation"
begin

install_C_file "jiraver443a.c"

context jiraver443a_simpl
begin

thm get_body_def

end (* context *)

end
