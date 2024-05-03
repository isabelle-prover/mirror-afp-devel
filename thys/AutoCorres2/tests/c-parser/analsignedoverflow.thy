(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory analsignedoverflow
imports "AutoCorres2.CTranslation"
begin


declare [[anal_integer_conversion=true]]
install_C_file "analsignedoverflow.c"

context f_impl
begin

lemma "\<Gamma> \<turnstile> \<lbrace> c = sint \<acute>c & c \<le> 117 \<rbrace> \<acute>ret' :== CALL f()
           \<lbrace> sint \<acute>ret' = c + 10 \<rbrace>"
  apply vcg
  apply safe
  oops

end

end
