(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory globals_fn
imports "AutoCorres2.CTranslation"
begin

install_C_file "globals_fn.c"

print_locale globals_fn_global_addresses

context globals_fn_simpl
begin
  thm f_body_def
  thm gupdate_body_def
  thm update_body_def
  thm test1_body_def
  thm test2_body_def
  thm test3_body_def

end

lemma (in test2_impl) returns40:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== PROC test2() \<lbrace> \<acute>ret' = 40 \<rbrace>"
  apply vcg
  apply auto
done


end