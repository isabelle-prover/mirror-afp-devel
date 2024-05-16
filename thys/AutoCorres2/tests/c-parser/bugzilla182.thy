(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory bugzilla182
imports "AutoCorres2.CTranslation"
begin

install_C_file "bugzilla182.c"

lemma "OFCLASS(small_C, packed_type_class)"
  by intro_classes

end
