(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory protoparamshadow
imports "AutoCorres2.CTranslation"
begin

install_C_file "protoparamshadow.c"

context protoparamshadow_simpl
begin

  thm f_body_def
  thm realone_body_def


end

end
