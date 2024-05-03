(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory globals_in_record
imports
  "AutoCorres2.CTranslation"
begin

install_C_file "globals_in_record.c"

context globals_in_record_simpl 
begin

thm globals.equality

find_theorems "zuzu_'"
thm globals.zuzu_'_def

find_theorems "zozo_'"
term "zozo_'"
find_theorems "zyzy"
thm zyzy_def

end

end
