(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory extern_dups
imports "AutoCorres2.CTranslation"
begin

install_C_file "extern_dups.c"

print_locale extern_dups_simpl

context extern_dups_simpl
begin

thm f_body_def
thm g_body_def
thm index_body_def
thm update_body_def
thm h_body_def

end

end
