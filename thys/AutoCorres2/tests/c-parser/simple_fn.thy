(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory simple_fn
imports "AutoCorres2.CTranslation"
begin

declare [[ML_print_depth = 1000]]
install_C_file "simple_fn.c"

context simple_fn_simpl
begin
thm fact_body_def
thm fact_impl
end

end
