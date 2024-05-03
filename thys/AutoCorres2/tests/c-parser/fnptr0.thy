(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory fnptr0
imports "AutoCorres2.CTranslation"
begin


declare [[ML_print_depth = 10000, c_parser_feedback_level=5]]
declare [[hoare_use_call_tr' = false, hoare_trace=1]]
install_C_file "fnptr0.c"


context fnptr0_global_addresses
begin
thm fun_ptr_distinct
thm fun_ptr_simps
thm fun_ptr_subtree
thm global_const_defs
thm global_const_array_selectors
thm global_const_non_array_selectors
thm global_const_selectors
end

context fnptr0_simpl
begin

  thm f_body_def
  thm callthem_body_def
  thm callable1_body_def
  thm voidcaller_body_def
  thm callvoidcaller_body_def

  thm callintcaller_body_def
  thm intcaller_body_def
  thm intcallable1_body_def

end

definition
  "symbols_ok ==  c_fnptr_guard (fnptr0.callable1)
        \<and> c_fnptr_guard (fnptr0.intcallable2)"


lemma  (in fnptr0_simpl)
  includes callvoidcaller_scope
  shows cvc_updates_global1: "!!x. \<Gamma> \<turnstile> \<lbrace> \<acute>global1 = x  \<and> symbols_ok\<rbrace>
    \<acute>ret' :== PROC callvoidcaller() \<lbrace> \<acute>global1 = x + 1 \<rbrace>"
apply (hoare_rule HoarePartial.ProcNoRec1)
  apply vcg_step
  apply vcg_step
   apply vcg_step
apply vcg_step
apply vcg_step
   apply vcg_step
  apply (rule Seq_propagate_precond)
   apply vcg_step
   apply vcg_step
   apply simp
  apply vcg_step
  apply vcg_step
 apply vcg_step
   apply vcg_step
   defer
  apply vcg_step
  apply vcg_step
   apply vcg_step
 apply vcg_step
 apply vcg_step
 apply vcg_step
  apply vcg_step
     apply vcg_step
  apply (rule hoare_indirect_call_guard)
     apply (rule order_refl)
    apply (rule hoare_indirect_call_known_proc [where q=fnptr0.callable1])
  apply vcg
  apply vcg
  apply (clarsimp simp add: symbols_ok_def)
done

lemma (in fnptr0_simpl) cic_returns_4:
  includes callintcaller_scope
  shows "\<Gamma>\<turnstile> {| symbols_ok |} \<acute>ret' :== PROC callintcaller()
                        {| \<acute>ret' = 4 |}"
apply (hoare_rule HoarePartial.ProcNoRec1)
  apply vcg_step
  apply (rule ccatchreturn_wp)
apply vcg_step
apply vcg_step
apply vcg_step
apply vcg_step
apply vcg_step
apply vcg_step

apply (rule HoarePartial.Call_exnBody
           [where R = "%s t. { u. t \<cdot>\<^sub>\<L> intcaller.ret' = 4 }"
               and \<Gamma>=\<Gamma>, OF _ _ _ intcaller_impl])
    defer
    apply (simp only: intcaller_body_def)
apply (rule allI)
apply vcg_step
apply vcg_step
apply vcg_step
apply vcg_step
apply vcg_step
      apply vcg_step
     apply vcg_step
       apply vcg_step
      apply (rule hoare_indirect_call_guard)

     apply (rule order_refl)
   apply (rule hoare_indirect_call_known_proc [where q=fnptr0.intcallable2])
apply simp
      apply vcg
     apply vcg
    apply (vcg, simp)
   defer
   apply (vcg_step)
  apply vcg
apply (auto simp: symbols_ok_def )[1]
done

end


