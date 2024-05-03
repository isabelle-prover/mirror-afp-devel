(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory struct_init0
imports "AutoCorres2.CTranslation"
begin

install_C_file "struct_init0.c"

lemma (in struct_init0_global_addresses) "x = t_C 0 0"
  by (simp add: x_def)

end
