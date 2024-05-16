(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ptr_modifies
imports "AutoCorres2.CTranslation"
begin

install_C_file "ptr_modifies.c"

context ptr_modifies_simpl
begin
  thm foo_ptr_new_modifies
  thm f_modifies
  thm f_body_def
  thm g_modifies
  thm h_modifies
end

locale g_impl' = f_spec + g_impl  

lemma (in g_impl') g_spec:
  "\<forall> i. \<Gamma> \<turnstile> \<lbrace> \<acute>i = i \<rbrace> \<acute>ret' :== CALL g(\<acute>i) \<lbrace> \<acute>ret' = i + 4 \<rbrace>"
  apply vcg
  apply simp
  done

end
