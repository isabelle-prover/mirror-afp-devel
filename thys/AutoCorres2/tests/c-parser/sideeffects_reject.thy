(*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory sideeffects_reject
  imports AutoCorres2.CTranslation
begin

install_C_file_expect_reject "sideeffects_reject1.c"
install_C_file_expect_reject "sideeffects_reject2.c"
install_C_file_expect_reject "sideeffects_reject3.c"
install_C_file_expect_reject "sideeffects_reject4.c"
install_C_file_expect_reject "sideeffects_reject5.c"
install_C_file_expect_reject "sideeffects_reject6.c"
end
