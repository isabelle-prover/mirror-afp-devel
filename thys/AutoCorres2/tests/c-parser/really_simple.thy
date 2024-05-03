(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory really_simple
imports "AutoCorres2.CTranslation"
begin

install_C_file "really_simple.c"

context really_simple_simpl
begin
thm f_body_def
thm f_impl
end

end
