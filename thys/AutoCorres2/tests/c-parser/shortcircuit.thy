(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory shortcircuit
imports "AutoCorres2.CTranslation"
begin

install_C_file "shortcircuit.c"


context shortcircuit_simpl
begin

  thm f_body_def
  thm deref_body_def
  thm test_deref_body_def
  thm imm_deref_body_def
  thm simple_body_def
  thm condexp_body_def
end


lemma (in test_deref_impl) semm: "\<Gamma> \<turnstile> \<lbrace> \<acute>p = NULL \<rbrace> Call shortcircuit.test_deref \<lbrace> \<acute>ret' = 0 \<rbrace>"
apply vcg
apply simp
done

lemma (in condexp_impl) condexp_semm:
  "\<Gamma> \<turnstile> \<lbrace> \<acute>i = 10 & \<acute>ptr = NULL & \<acute>ptr2 = NULL \<rbrace>
                    Call shortcircuit.condexp
                  \<lbrace> \<acute>ret' = 23 \<rbrace>"
apply vcg
apply (simp add: word_sless_def word_sle_def)
done

end (* theory *)
