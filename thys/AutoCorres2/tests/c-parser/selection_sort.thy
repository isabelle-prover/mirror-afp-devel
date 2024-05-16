(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory selection_sort
imports "AutoCorres2.CTranslation"
begin

install_C_file "selection_sort.c"

context selection_sort_simpl
begin
thm len_body_def
thm lmin_body_def
thm ssort_body_def
end

end
