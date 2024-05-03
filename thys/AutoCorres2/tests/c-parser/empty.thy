(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory empty
  imports AutoCorres2.CTranslation
begin

include_C_file "empty.h" for empty.c
install_C_file "empty.c"


end
