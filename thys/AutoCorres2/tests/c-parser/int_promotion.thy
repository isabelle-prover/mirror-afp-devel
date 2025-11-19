(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory int_promotion
imports "AutoCorres2.CTranslation"
begin

install_C_file "int_promotion.c"


thm f_body_def

lemma (in int_promotion_global_addresses) includes f_variables 
  shows "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL f() \<lbrace> \<acute>ret' = 1 \<rbrace>"
  apply vcg
  apply simp
  done
end
