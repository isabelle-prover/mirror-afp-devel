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

context int_promotion_simpl
begin

thm f_body_def
end
lemma (in f_impl) "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL f() \<lbrace> \<acute>ret' = 1 \<rbrace>"
  apply vcg
  apply simp
  done
end
