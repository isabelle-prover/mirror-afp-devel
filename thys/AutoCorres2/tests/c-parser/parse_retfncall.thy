(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_retfncall
imports "AutoCorres2.CTranslation"
begin

install_C_file "parse_retfncall.c"

context parse_retfncall_simpl
begin
thm add1_body_def
thm add2_body_def
end

end
