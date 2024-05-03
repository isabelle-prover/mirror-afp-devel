(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ummbug20100217
imports "AutoCorres2.CTranslation"
begin

install_C_file "ummbug20100217.c"


context ummbug20100217_simpl
begin

thm g_body_def
thm h_body_def
thm j_body_def

end

end
