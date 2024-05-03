(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_voidfn
imports "AutoCorres2.CTranslation"
begin

install_C_file "parse_voidfn.c"

context parse_voidfn_simpl
begin
thm f_body_def
thm g_body_def
end

end
