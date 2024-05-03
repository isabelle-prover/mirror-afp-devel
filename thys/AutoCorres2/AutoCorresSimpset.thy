(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory AutoCorresSimpset
imports SimplBucket
begin

lemma globals_surj: "surj globals"
  apply (rule surjI [where f="\<lambda>x. undefined\<lparr> globals := x\<rparr>"])
  apply simp
  done

lemma triv_ex_apply: "\<exists>s1 s0. f s0 = s1"
  by (iprover)

lemmas ptr_val_ptr_add_simps =
  ptr_add_word32
  ptr_add_word32_signed
  ptr_add_word64
  ptr_add_word64_signed

(*
 * The "full" simpset used internally within AutoCorres during
 * processing.
 *)
ML \<open>

val AUTOCORRES_SIMPSET =
  @{context} delsimps (
    (* interferes with heap_lift *)
    @{thms fun_upd_apply}
    (* affects boolean expressions *)
    @ @{thms word_neq_0_conv neq0_conv}
    (* interferes with struct_rewrite *)
    @ @{thms ptr_coerce.simps ptr_add_0_id}
    (* oversimplifies Spec sets prior to L2 stage
       (we will control this explicitly in L2Peephole) *)
    @ @{thms CollectPairFalse}
    @ @{thms unsigned_of_nat unsigned_of_int}
    @ @{thms map_of_default.simps}
    @ @{thms field_lvalue_append} @
    @{thms ptr_val_ptr_add_simps} )
  addsimps (
    (* Needed for L2corres_spec *)
    @{thms globals_surj}
    )
  addsimps (
    (* builds up by monad_equiv tactic, and record updates *)
    @{thms triv_ex_apply} (* fixme Shouldn't this already be handled by HOL.ex_simps and simproc defined_Ex.*)
    )
  addsimps (@{thms ptr_NULL_conv})
  delsimprocs
    [@{simproc case_prod_beta},@{simproc case_prod_eta}]
  |> simpset_of

\<close>

end
