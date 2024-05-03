(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory inner_fncalls
imports "AutoCorres2.CTranslation"
begin

install_C_file "inner_fncalls.c"

print_locale inner_fncalls_simpl

context inner_fncalls_simpl
begin
thm f_body_def
thm e_body_def
thm f2_body_def
thm g_body_def
thm function_body_def
thm function2_body_def
end

end
