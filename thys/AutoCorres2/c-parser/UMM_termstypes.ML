(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature UMM_TERMS_TYPES =
sig

  val typ_tag_ty : typ
  val mk_tag_type : typ -> typ
  val empty_tag_tm : typ -> int -> string -> term
  val heap_desc_ty : typ
  val heap_raw_ty : typ
  val typ_name_ty : typ

  val mk_aux_guard_t : term
  val mk_aux_heap_desc_t : term
  val mk_auxupd_ty : typ -> typ

  val mk_hrs_htd_update_t : term
  val mk_hrs_mem_t : term
  val mk_hrs_htd_t : term
  val mk_hrs_mem_update_t : term

  val mk_ptr_safe : term -> term -> term

  val mk_field_lookup : typ * string -> term
  val mk_field_lookup_nofs : typ * string -> term
  val mk_fg_cons_tm : typ -> typ -> string -> Proof.context -> term

  val mk_sizetd : term -> term
  val mk_aligntd : term -> term
  val mk_size_aligntd : term -> term -> term -> term
  val mk_align_of : Proof.context -> typ -> (term * Proof.context)
  val mk_typ_info_tm : typ -> term
  val mk_typ_info_of : typ -> term
  val mk_typ_name_of : typ -> term
  val mk_td_names : term -> term
  val mk_sizeof : term -> term
  val mk_tag_pad_tm : int -> typ -> typ -> string -> Proof.context -> term
  val final_pad_tm : int -> typ -> term
  
  val mk_component_desc : typ -> term
  val mk_field_update : typ -> term
  val mk_field_update_component_desc_apply : typ -> string -> string -> term

  val mk_h_val_field_eq : Proof.context -> typ -> typ -> string -> string -> string -> term
  val mk_h_val_unfold: Proof.context -> typ -> string -> string -> (string * typ) list -> term
  val mk_heap_update_field_eq: Proof.context -> typ -> typ -> string -> string -> string -> string -> term
end

structure UMM_TermsTypes : UMM_TERMS_TYPES =
struct

open TermsTypes
fun field_desc_ty ty =
    Type(@{type_name "CTypesDefs.field_desc_ext"}, [ty, unit])

fun mk_typ_desc_unit_ty ty = Type(@{type_name "CTypesDefs.typ_desc"}, [ty,@{typ unit}])
fun mk_typ_desc_ty ty = Type(@{type_name "CTypesDefs.typ_desc"}, [ty,ty])
fun mk_tag_type ty = mk_typ_desc_ty (field_desc_ty ty)


val normalisor_ty = mk_list_type word8 --> mk_list_type word8
val typ_tag_ty = mk_typ_desc_unit_ty normalisor_ty

val tag_rung_ty = bool
val heap_desc_ty = addr_ty --> (mk_prod_ty (bool,nat --> mk_option_ty (mk_prod_ty (typ_tag_ty,tag_rung_ty))))
val heap_raw_ty = mk_prod_ty (heap_ty, heap_desc_ty)


val mk_auxupd_val_ty =  mk_prod_ty (bool, heap_desc_ty --> heap_desc_ty)
fun mk_auxupd_ty ty = ty --> mk_auxupd_val_ty
val mk_aux_guard_t = Const(@{const_name "fst"}, mk_auxupd_val_ty --> bool)
val mk_aux_heap_desc_t = Const(@{const_name "snd"}, mk_auxupd_val_ty --> heap_desc_ty
    --> heap_desc_ty)

val mk_hrs_htd_update_t = @{const "HeapRawState.hrs_htd_update"}
val mk_hrs_mem_t = @{const "HeapRawState.hrs_mem"}
val mk_hrs_htd_t = @{const "HeapRawState.hrs_htd"}
val mk_hrs_mem_update_t = @{const "HeapRawState.hrs_mem_update"}

val typ_name_ty = string_ty

fun mk_typ_name_tm ty =
    Const(@{const_name "CTypesDefs.typ_name"}, mk_tag_type ty --> typ_name_ty)

fun empty_tag_tm ty align nm =
    Const(@{const_name "empty_typ_info"}, nat --> string_ty --> mk_tag_type ty) $ mk_nat_numeral align $
    mk_string nm

fun final_pad_tm align ty =
    Const(@{const_name "final_pad"}, nat --> mk_tag_type ty --> mk_tag_type ty) $ mk_nat_numeral align

fun field_access_tm recty ty nm ctxt = let
  val recname = case recty of Type(rn, []) => rn
                            | _ => raise Fail "field_access_tm: Record type \
                                              \looks unlikely"
  val access_ty = recty --> ty
  val fldnm = Sign.intern_const (Proof_Context.theory_of ctxt) (recname ^ "." ^ nm)
in
  Const(fldnm, access_ty)
end

fun field_update recty ty nm ctxt = let
  val recname = case recty of Type(rn, []) => rn
                            | _ => raise Fail "field_access_tm: Record type \
                                              \looks unlikely"
  fun tytr ty = ty --> ty
  val field_update_ty = tytr ty --> tytr recty
  val fldnm = Sign.intern_const (Proof_Context.theory_of ctxt) (recname ^ "." ^ nm)
  val field_update = Const (suffix Record.updateN fldnm,
      field_update_ty)
in
 field_update 
end

fun field_update_tm recty ty nm ctxt = let
  val recname = case recty of Type(rn, []) => rn
                            | _ => raise Fail "field_access_tm: Record type \
                                              \looks unlikely"
  fun tytr ty = ty --> ty
  val update_ty = ty --> tytr recty
  val field_update_ty = tytr ty --> tytr recty
  val fldnm = Sign.intern_const (Proof_Context.theory_of ctxt) (recname ^ "." ^ nm)
  val field_update = Const (suffix Record.updateN fldnm,
      field_update_ty)
  val K_rec_ty = ty --> tytr ty
in
  Const(@{const_name "Fun.comp"}, field_update_ty --> K_rec_ty --> update_ty) $
       field_update $ K_rec ty
end


fun mk_tag_pad_tm align recty ty nm ctxt = let
  val tag_pad_combine = \<^Const>\<open>ti_typ_pad_combine ty recty\<close>
  val field_access = field_access_tm recty ty nm ctxt
  val field_update = field_update_tm recty ty nm ctxt
in
  tag_pad_combine $ mk_TYPE ty $ field_access $ field_update $ mk_nat_numeral align $ mk_string nm
end



fun mk_h_val T h p = \<^instantiate>\<open>'a=T and p = p and h = \<open>Free (h, @{typ "heap_mem"})\<close> in term \<open>h_val h p\<close>\<close>


fun mk_ptrT T = Type (@{type_name "ptr"}, [T])

fun mk_field_lvalue recty ty p f = 
  \<^instantiate>\<open>'a = ty and 'b = recty and p = \<open>Free(p, mk_ptrT recty)\<close> and f=\<open>mk_string f\<close> 
  in term \<open>PTR('a::c_type) &(p\<rightarrow>[f])\<close> for p::\<open>'b::c_type ptr\<close>\<close>

fun mk_h_val_field_eq ctxt recty ty h p f  =
  let
    val lhs = mk_h_val ty h (mk_field_lvalue recty ty p f)
    val rhs = field_access_tm recty ty f ctxt $ (mk_h_val recty h (Free(p, mk_ptrT recty))) 
  in
     HOLogic.Trueprop $ HOLogic.mk_eq (lhs, rhs) 
  end

fun mk_heap_update T p v h = \<^instantiate>\<open>'a=T and p = p and v = v and h = \<open>Free (h, @{typ "heap_mem"})\<close> 
  in term \<open>heap_update p v h\<close>\<close>

fun mk_heap_update_field_eq ctxt recty ty h p v f =
  let
    val v = Free(v, ty)
    val lhs = mk_heap_update ty (mk_field_lvalue recty ty p f) v h 
    val p = Free(p, mk_ptrT recty)
    val cgrd = \<^instantiate>\<open>'a = recty and p = p in prop \<open>c_guard p\<close>\<close>
    val rhs = mk_heap_update recty p (field_update recty ty f ctxt $ Abs ("_", ty, v) $ (mk_h_val recty h p)) h
  in
    Logic.mk_implies (cgrd, HOLogic.Trueprop $ HOLogic.mk_eq (lhs, rhs))
  end

fun mk_h_val_unfold ctxt recty h p fs = 
  let
    val rec_name = dest_Type recty |> fst
    val constr = Symtab.lookup (RecursiveRecordPackage.get_info (Proof_Context.theory_of ctxt)) rec_name
          |> the |> #constructor
    val lhs = mk_h_val recty h (Free(p, mk_ptrT recty))
    val comps = fs |> map (fn (fname, ty) => 
          mk_h_val ty h (mk_field_lvalue recty ty p fname))
    val rhs = Term.list_comb (Const constr, comps)
  in
    HOLogic.Trueprop $ HOLogic.mk_eq (lhs, rhs)
  end
fun mk_fg_cons_tm recty ty nm ctxt =
  Const(@{const_name "fg_cons"}, (recty --> ty) --> (ty --> recty --> recty)
      --> bool) $
      field_access_tm recty ty nm ctxt $
      field_update_tm recty ty nm ctxt

fun mk_td_names tm =
    Const(@{const_name "td_names"}, type_of tm --> mk_set_type string_ty) $ tm

fun mk_sizetd tm = let
  val ty = type_of tm
in
  Const(@{const_name "size_td"}, ty --> nat) $ tm
end

fun mk_aligntd tm = let
  val ty = type_of tm
in
  Const(@{const_name "align_td"}, ty --> nat) $ tm
end

fun mk_size_aligntd tm s a = let
  val ty = type_of tm
in
  Const(@{const_name "size_align_td"}, ty --> nat --> nat --> bool) $ tm $ s $ a
end

fun mk_align_of ctxt ty = let
 val iT =  mk_itself_type ty
 val ([t], ctxt') = Variable.variant_fixes ["t"] ctxt
in
  (Const(@{const_name "align_of"}, iT --> nat) $ Free (t, iT), ctxt')
end

fun mk_typ_info_tm ty =
    \<^Const>\<open>typ_info_t ty\<close>
                                                           
fun mk_typ_info_of ty = mk_typ_info_tm ty $ mk_TYPE ty

fun mk_field_lookup (ty,f) =
    Const(@{const_name "CTypesDefs.field_lookup"},
          mk_tag_type ty --> qualified_field_name_ty -->
          nat --> mk_option_ty (mk_prod_ty (mk_tag_type ty, nat))) $
    mk_typ_info_of ty $
    mk_list_cons (mk_string f, Free("fs", qualified_field_name_ty)) $
    Free("m", nat)

fun mk_field_lookup_nofs (ty,f) =
    Const(@{const_name "CTypesDefs.field_lookup"},
          mk_tag_type ty --> qualified_field_name_ty -->
          nat --> mk_option_ty (mk_prod_ty (mk_tag_type ty, nat))) $
    mk_typ_info_of ty $
    mk_list_singleton (mk_string f) $
    mk_nat_numeral 0

fun mk_typ_name_of ty = mk_typ_name_tm ty $ mk_typ_info_of ty

fun mk_ptr_safe t d = let
  val ptrty = type_of t
in
  Const(@{const_name "ptr_safe"}, ptrty --> heap_desc_ty --> bool) $ t $ d
end

fun mk_component_desc ty =
  Const(@{const_name "component_desc"}, mk_tag_type ty --> field_desc_ty ty)

fun mk_field_update ty =
  Const (@{const_name "field_update"}, field_desc_ty ty --> @{typ "byte list"} --> ty --> ty)

fun mk_field_update_component_desc_apply ty bs v =
  mk_field_update ty $ (mk_component_desc ty $ (mk_typ_info_of ty)) $ Free (bs, @{typ "byte list"}) $ Free (v, ty)

end
