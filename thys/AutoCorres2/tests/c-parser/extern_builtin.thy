(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory extern_builtin
  imports "AutoCorres2.CTranslation"
begin

declare [[allow_underscore_idents=true]]

install_C_file "extern_builtin.c"

context extern_builtin_simpl
begin
thm foo_body_def
end
end
