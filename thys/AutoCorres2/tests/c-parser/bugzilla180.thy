(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory bugzilla180
imports "AutoCorres2.CTranslation"
begin

install_C_file "bugzilla180.c"

context "g_impl"
begin

thm g_body_def

lemma "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL g() \<lbrace> \<acute>ret' = 15 \<rbrace>"
apply vcg
apply simp
done
end

context "h_impl"
begin
thm h_body_def

lemma "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL h() \<lbrace> \<acute>ret' = 15 \<rbrace>"
apply vcg
apply simp
done

end

end (* theory *)
