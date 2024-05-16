(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory spec_annotated_voidfn
imports "AutoCorres2.CTranslation"
begin

install_C_file "spec_annotated_voidfn.c"

context f_spec
begin
thm f_spec
end

context spec_annotated_voidfn_simpl
begin
thm f_body_def
end

end