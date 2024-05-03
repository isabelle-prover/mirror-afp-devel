(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_include
imports "AutoCorres2.CTranslation"
begin

include_C_file "includes/test_include2.h" for "parse_include.c"

new_C_include_dir "includes"

install_C_file "parse_include.c"

context parse_include_simpl
begin
thm g_body_def
thm h_body_def
thm included_fn_body_def
end
end
