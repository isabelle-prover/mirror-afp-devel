(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory spec_annotated_fn
imports "AutoCorres2.CTranslation"
begin

declare sep_conj_ac [simp add]

install_C_file "spec_annotated_fn.c"


print_locale spec_annotated_fn_simpl
print_locale Square_spec

context f_impl
begin
declare [[show_types=false]]
ML \<open>
val x = StateFun.trace_data (Context.Proof @{context})
\<close>

ML \<open>
val x = StateSpace.trace_data (Context.Proof @{context})
\<close>

end
context Square_spec
begin
thm Square_spec
end
context spec_annotated_fn_simpl
begin

thm Square_body_def
thm Square_impl

thm f_spec_def
thm f_body_def

end

lemma (in Square_spec) foo:
  shows "\<Gamma> \<turnstile> \<lbrace> T \<rbrace> \<acute>ret' :== CALL Square(4) \<lbrace> \<acute>ret' = 16 \<rbrace> "
apply vcg
apply simp
done

lemma (in Square_impl)
shows "\<forall>n. \<Gamma> \<turnstile> \<lbrace> \<acute>n = n \<rbrace> \<acute>ret' :== PROC Square(\<acute>n)
               \<lbrace>\<acute>ret' = n * n \<rbrace>"
  apply vcg
  apply simp
done

lemma (in f_impl)
shows "\<forall>n. \<Gamma> \<turnstile> \<lbrace> \<acute>n = n \<rbrace> \<acute>ret' :== PROC f(\<acute>n) \<lbrace> \<acute>ret' = n * n \<rbrace>"
apply vcg
  apply (clarsimp simp add: mex_def meq_def)
done

end
