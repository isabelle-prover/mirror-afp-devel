(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* This is the "standard" instantiation of the MemoryModelExtras
   signature.

   Other implementations using the parser code may wish to 'use' a different
   file than this one.  The theory is that everything will "just work" as
   long as that file declares a structure MemoryModelExtras matching the
   signature.
*)

structure MemoryModelExtras : MEMORY_MODEL_EXTRAS =
struct

open TermsTypes UMM_TermsTypes
val extended_heap_ty = heap_raw_ty
fun check_safety {heap=h,ptrval} = let
  val heap_desc = mk_hrs_htd_t $ h
in
  (mk_ptr_safe ptrval heap_desc, safety_error)
end

fun dereference_ptr {heap,ptrval} = mk_lift(mk_hrs_mem_t $ heap,ptrval)

fun mk_heap_update_extended t = mk_hrs_mem_update_t $ t

fun mk_aux_guard t = mk_aux_guard_t $ t

fun mk_aux_update t = mk_hrs_htd_update_t $ (mk_aux_heap_desc_t $ t)

fun mk_aux_type ty = mk_auxupd_ty ty

val check_global_record_type = HeapStateType.hst_prove_globals

structure UserTypeDeclChecking =
struct
  open UMM_Proofs
  type t = T
  type csenv = ProgramAnalysis.csenv
  val initial_state = umm_empty_state
  val finalise = umm_finalise
  fun struct_type cse {struct_type,tag_def_thm, typ_info_t_thm,state} lthy =
      umm_struct_calculation cse (struct_type,tag_def_thm, typ_info_t_thm, state,lthy)
  fun array_type _ {element_type, array_size, state} lthy =
      umm_array_calculation element_type array_size state lthy

end

end
