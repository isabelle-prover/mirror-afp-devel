(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver439
  imports "AutoCorres2.CTranslation"
begin

install_C_file "jiraver439.c"

context jiraver439_simpl
begin

thm f_body_def
thm g1_body_def
thm g2_body_def
thm h3_body_def
end

lemma (in f_impl) "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>z :== CALL f();; \<acute>ret' :== CALL f() \<lbrace> \<acute>ret' = \<acute>z + 1 \<rbrace>"
apply vcg
apply simp
done

end
