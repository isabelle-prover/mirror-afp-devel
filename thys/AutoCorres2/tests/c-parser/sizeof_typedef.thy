(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory sizeof_typedef
imports "AutoCorres2.CTranslation"
begin

install_C_file "sizeof_typedef.c"

context sizeof_typedef_simpl
begin
thm f_body_def
end

end
