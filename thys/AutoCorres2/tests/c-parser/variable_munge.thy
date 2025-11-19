(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory variable_munge
imports "AutoCorres2.CTranslation"
begin

install_C_file "variable_munge.c"

thm f_body_def
thm g_body_def
thm h_body_def
thm j_body_def
thm bar_body_def
thm qux_body_def

declare [[ML_print_depth=1000]]
lemma (in variable_munge_global_addresses) includes j_variables shows j_test1:

  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL j(255) \<lbrace> \<acute>ret' = 0 \<rbrace>"
apply vcg
apply simp
done

lemma (in variable_munge_global_addresses) includes j_variables shows  j_test2:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL j(-200) \<lbrace> \<acute>ret' = -400 \<rbrace>"
apply vcg
apply simp
done

end
