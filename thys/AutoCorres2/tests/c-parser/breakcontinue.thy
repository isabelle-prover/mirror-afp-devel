(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory breakcontinue
imports "AutoCorres2.CTranslation"
begin

declare sep_conj_ac [simp add]

install_C_file "breakcontinue.c"

context breakcontinue_simpl
begin

thm f_body_def
thm g_body_def
thm h_body_def
thm i_body_def
thm dotest_body_def
end

context h_impl
begin
term "\<lbrace> -10 <=s \<acute>e & \<acute>e <s 0 \<rbrace>"
end
lemma (in h_impl) h:
  "\<Gamma> \<turnstile> \<lbrace> -10 <=s \<acute>e & \<acute>e <s 0 \<rbrace>
  \<acute>ret' :== PROC h(\<acute>e)
  \<lbrace> \<acute>ret' = \<acute>e \<rbrace>"
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (hoare_rule HoarePartial.Catch [where R = "\<lbrace> \<acute>ret' = \<acute>e & is_local \<acute>global_exn_var'\<rbrace>"])
  defer
   apply vcg
   apply simp
apply (hoare_rule HoarePartial.conseq
           [where P' = "\<lambda>e. \<lbrace> \<acute>e = e & e <s 0 & -10 <=s e \<rbrace>"
            and Q' = "\<lambda>e. \<lbrace> \<acute>e = e & \<acute>ret' = e & is_local \<acute>global_exn_var'\<rbrace>"
            and A' = "\<lambda>e. \<lbrace> \<acute>e = e & \<acute>ret' = e & is_local \<acute>global_exn_var'\<rbrace>"])
  defer
  apply (simp add: subset_iff)
apply (rule allI)
apply (rule_tac R="{}" in HoarePartial.Seq)
  defer
   apply vcg
  apply (rule Seq_propagate_precond)
  apply (vcg, simp)
apply (rule_tac R="\<lbrace> \<acute>e = Z \<rbrace>" in HoarePartial.Seq)
  defer
   apply (vcg, simp)

apply (rule_tac R = "\<lbrace> \<acute>e = Z & \<acute>global_exn_var' = Break \<rbrace>" in HoarePartial.Catch)
  defer

  apply (vcg, simp)
  apply simp
apply (rule_tac P' = "\<lbrace> \<acute>e = Z & Z <s 0 & -10 <=s Z \<rbrace>"
            and Q' = "\<lbrace> \<acute>e = Z & Z <s 0 & -10 <=s Z \<rbrace> \<inter> - \<lbrace> \<acute>e <s 10 \<rbrace>"
            and A' = "\<lbrace> \<acute>e = Z & \<acute>global_exn_var' = Break \<rbrace>"
         in HoarePartial.conseq_no_aux)
  defer
  apply simp
apply (simp add: whileAnno_def)
apply (rule HoarePartialDef.While)
apply vcg
apply (simp add: subset_iff)
done

(* another example where vcg fails, generating impossible sub-goals *)
lemma (in dotest_impl) dotest:
  "\<Gamma> \<turnstile> \<lbrace> \<acute>x = 4 \<rbrace> \<acute>ret' :== PROC dotest(\<acute>x)
       \<lbrace> \<acute>ret' = 4 \<rbrace>"
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (hoare_rule HoarePartial.Catch [where R="\<lbrace> \<acute>ret' = 4 & is_local \<acute>global_exn_var'\<rbrace>"])
   apply (hoare_rule HoarePartial.Seq [where R="{}"])
    apply (rule Seq_propagate_precond)
  apply (vcg, simp)
    apply (hoare_rule HoarePartial.Seq [where R="\<lbrace> \<acute>x = 4 \<rbrace>"])
      apply (hoare_rule HoarePartial.Catch [where R="\<lbrace> \<acute>x = 4 & \<acute>global_exn_var' = Break \<rbrace>"])
        apply (hoare_rule HoarePartial.Seq [where R="\<lbrace> False \<rbrace>"])
          apply (vcg, simp)
        apply (hoare_rule HoarePartial.conseq_exploit_pre, simp)
      apply (vcg, simp)
    apply (vcg, simp)
  apply vcg
apply (vcg, simp)
done

end
