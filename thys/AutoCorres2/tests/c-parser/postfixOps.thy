(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory postfixOps
imports "AutoCorres2.CTranslation"
begin

install_C_file "postfixOps.c"

context postfixOps_simpl
begin

thm doit_body_def


end (* context *)


end
