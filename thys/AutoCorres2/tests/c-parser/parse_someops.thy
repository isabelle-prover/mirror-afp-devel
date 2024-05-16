(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_someops
imports "AutoCorres2.CTranslation"
begin

install_C_file "parse_someops.c"

context parse_someops_simpl
begin
thm f_body_def
thm g_body_def
thm condexp_body_def
thm cbools_body_def
thm bitwise_body_def
thm shifts_body_def
thm callbool_body_def
thm ptr_compare_body_def
thm large_literal_rshift_body_def
end

lemma (in callbool_impl) foo:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL callbool(1) \<lbrace> \<acute>ret' = 1 \<rbrace>"
apply vcg
apply simp
done

end
