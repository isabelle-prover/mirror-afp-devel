(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory decl_only
imports "AutoCorres2.CTranslation"
begin

install_C_file "decl_only.c"

print_locale! decl_only_global_addresses
print_locale! decl_only_simpl
context decl_only_simpl
begin
term x
thm x_def
end

end
