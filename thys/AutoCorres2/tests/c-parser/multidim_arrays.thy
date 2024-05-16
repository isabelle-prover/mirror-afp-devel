(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory multidim_arrays
imports "AutoCorres2.CTranslation"
begin

install_C_file "multidim_arrays.c"

context multidim_arrays_simpl
begin

thm h1_body_def
thm h2_body_def


end

end
