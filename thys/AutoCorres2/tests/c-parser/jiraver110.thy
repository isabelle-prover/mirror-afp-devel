(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver110
imports "AutoCorres2.CTranslation"
begin

install_C_file "jiraver110.c"

context jiraver110_simpl
begin

thm f_body_def
end

(* this should be provable *)
lemma (in f_impl) shouldbetrue:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL f(0) \<lbrace> \<acute>ret' = 1 \<rbrace>"
apply vcg
apply simp
(* when this is provable, more will be required here *)
done

end

