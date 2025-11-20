(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory retprefix
imports "AutoCorres2.CTranslation"
begin

install_C_file "retprefix.c"


thm f_body_def
thm g_body_def
thm h_body_def
thm i_body_def

lemma (in retprefix_global_addresses) includes h_variables 
  shows "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>x :== CALL h() \<lbrace> \<acute>x = 6 \<rbrace>"
by vcg simp

lemma (in retprefix_global_addresses) includes i_variables 
  shows  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL i() \<lbrace> \<acute>ret' = 6 \<rbrace>"
by vcg simp


end (* theory *)
