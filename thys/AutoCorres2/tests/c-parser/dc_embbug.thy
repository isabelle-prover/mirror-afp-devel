(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory dc_embbug
imports "AutoCorres2.CTranslation"
begin

install_C_file "dc_embbug.c"

context dc_embbug_simpl
begin
thm f_body_def
thm h_body_def
end

end
