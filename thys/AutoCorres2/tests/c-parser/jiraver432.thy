(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver432
  imports "AutoCorres2.CTranslation"
begin

install_C_file "jiraver432.c"

thm AnonStruct1'_size
thm AnonStruct2'_size

context jiraver432_simpl
begin
  thm f_body_def
end (* context *)

end

