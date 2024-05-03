(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory builtins
imports "AutoCorres2.CTranslation"
begin

install_C_file "builtins.c"


declare [[hoare_trace=1]]
context f_impl
begin

lemma "\<Gamma> \<turnstile> \<lbrace>\<acute>i = 3 \<rbrace> Call builtins.f \<lbrace> \<acute>ret' = 6 \<rbrace>" 
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (hoare_rule HoarePartial.Catch [where R="\<lbrace> \<acute>ret' = 6 & is_local \<acute>global_exn_var'\<rbrace>"])
   apply (hoare_rule HoarePartial.Seq [where R="{}"])
    apply (rule Seq_propagate_precond)
     apply (vcg)
     apply simp
    apply (hoare_rule HoarePartial.Cond [where P\<^sub>1="{}" and P\<^sub>2="\<lbrace>\<acute>i=3\<rbrace>"])
        apply (simp add: subset_eq word_sless_def word_sle_def)
      apply (hoare_rule HoarePartial.conseq_exploit_pre)
      apply simp
    apply vcg
    apply simp
   apply vcg
  apply vcg
  apply simp
done


(* NOTE:

  apply vcg

at the outset generates three sub-goals, last of which is not provable
*)

end
end
