(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver345
  imports "AutoCorres2.CTranslation"
begin

install_C_file "jiraver345.c"

context jiraver345_simpl
begin

thm good_body_def
thm bad_body_def
end

lemma (in good_impl) "\<Gamma> \<turnstile> \<lbrace> \<acute>p = Ptr 0 \<rbrace> \<acute>ret' :== CALL good(\<acute>p) \<lbrace> \<acute>ret' = 0 \<rbrace>"
apply vcg
apply simp
done

lemma (in bad_impl) "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL bad(Ptr 0) \<lbrace> \<acute>ret' = 0 \<rbrace>"
apply vcg
apply simp
done

end
