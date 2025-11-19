(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory sideeffects_reject1
  imports AutoCorres2.CTranslation
begin

install_C_file_expect_reject "sideeffects_reject1.c"

end
