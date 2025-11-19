(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory arithmetic_right_shift
imports "AutoCorres2.CTranslation"
begin

declare [[arithmetic_right_shift]]
install_C_file "arithmetic_right_shift.c"

context f_impl
begin

lemma "\<Gamma> \<turnstile> \<lbrace> -1 = \<acute>c \<rbrace> \<acute>ret' :== CALL f() \<lbrace> \<acute>ret' = -1 \<rbrace>"
  by vcg (auto simp: sshiftr_n1)

end

context g_impl
begin

lemma "\<Gamma> \<turnstile> \<lbrace> u = \<acute>u \<rbrace> \<acute>ret' :== CALL g() \<lbrace> \<acute>ret' = u >> 5 \<rbrace>"
  by vcg simp_all

end

end
