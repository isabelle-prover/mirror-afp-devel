(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

structure TermsTypes : TERMS_TYPES =
struct

open IsabelleTermsTypes
open HP_TermsTypes

fun mk_word_ty n = Word_Lib.mk_wordT n
fun mk_sword_ty n =
  let
    val Type(w, [binT]) = Word_Lib.mk_wordT n
  in Type (w, [Type (@{type_name "Signed_Words.signed"}, [binT])]) end


fun to_unsigned_word T = 
  if Word_Lib.is_wordT T then
    (let
      val (_, [aT]) = dest_Type T
      val binT = case aT of (Type (@{type_name Signed_Words.signed}, [binT])) => binT | _ => raise Match
  
      val wT = Type (@{type_name Word.word}, [binT])
    in
      SOME wT
    end
    handle Match => NONE)
  else NONE

fun to_signed_word T = 
  if Word_Lib.is_wordT T then
    (let
      val (_, [binT]) = dest_Type T
      val _ = case binT of (Type (@{type_name Signed_Words.signed}, _)) => raise Match | _ => ()

      val sT = Type (@{type_name Word.word}, [Type (@{type_name Signed_Words.signed}, [binT])])
    in
      SOME sT
    end
    handle Match => NONE)
 else NONE     

val is_signed_word = is_some o to_unsigned_word
val is_unsigned_word = is_some o to_signed_word

fun binT_of_wordT T =
  if Word_Lib.is_wordT T then
    let
      val (_, [aT]) = dest_Type T
    in SOME aT end
  else NONE

fun coerce_word fromT toT t =
  if fromT = toT then t
  else
    let
      val from = the (binT_of_wordT fromT)
      val to = the (binT_of_wordT toT)
      val res = \<^instantiate>\<open>'a = from and 'b =to and t = t in term "(ucast::'a::len word \<Rightarrow> 'b::len word) t"\<close>
    in
      res
    end
    handle Option => t
fun word_ty arg = Type(@{type_name "Word.word"}, [arg])
val word8 = word_ty @{typ "8"}
val word16 = word_ty @{typ "16"}
val word32 = word_ty @{typ "32"}
val word64 = word_ty @{typ "64"}
val word128 = word_ty @{typ "128"}

fun sword_ty arg = Type(@{type_name "Word.word"}, [Type (@{type_name "Signed_Words.signed"}, [arg])])
val sword8 = sword_ty @{typ "8"}
val sword16 = sword_ty @{typ "16"}
val sword32 = sword_ty @{typ "32"}
val sword64 = sword_ty @{typ "64"}
val sword128 = sword_ty @{typ "128"}

val symbol_table = Free ("symbol_table", @{typ "string => addr"})

fun dest_array_type ty =
    case ty of
      Type("Arrays.array", args) => (hd args, hd (tl args))
    | _ => raise TYPE("dest_array_type: not an array type", [ty], [])

fun mk_array_type (ty, n) = let
in
  Type(@{type_name "Arrays.array"}, [ty, mk_numeral_type n])
end

val is_array_type = is_some o try dest_array_type

val element_type = fst o dest_array_type

fun innermost_element_type ty =
  case try dest_array_type ty of
    SOME (eT, _) => innermost_element_type eT
  | NONE => ty

fun array_dimension ty =
  case try dest_array_type ty of
    SOME (eT, _) => array_dimension eT + 1
  | NONE => 0

fun array_indexes ty =
  case try dest_array_type ty of
    SOME (eT, iT) =>  array_indexes eT @ [dest_numeral_type iT]
  | NONE => []

fun dest_array_index ty =
  let
    val (eT, iT) = dest_array_type ty
  in
    (eT, dest_numeral_type iT)
  end

(* ----------------------------------------------------------------------
    Terms
   ---------------------------------------------------------------------- *)



fun mk_array_update_t ty = let
  val (elty, _) = dest_array_type ty
in
  Const(@{const_name "Arrays.update"}, ty --> nat --> elty --> ty)
end

fun mk_array_nth (array,n) = let
  val arrayty = type_of array
  val (elty, _) = dest_array_type arrayty
in
  Const(@{const_name "Arrays.index"}, arrayty --> nat --> elty) $ array $ n
end

(* word terms *)
fun mk_w2n t = let
  val ty = type_of t
in
  Const("Word.unat", ty --> nat) $ t
end

fun mk_i2w_t rty = Const(@{const_name "of_int"},
                         int --> rty)

fun mk_lshift(t1 : term, t2 : term) : term =
    Const(@{const_name "shiftl"},
          type_of t1 --> nat --> type_of t1) $ t1 $ t2

fun mk_rshift(t1, t2) =
    Const(@{const_name "shiftr"},
          type_of t1 --> nat --> type_of t1) $ t1 $ t2

fun mk_arith_rshift(t1, t2) =
    Const(@{const_name "sshiftr"},
          type_of t1 --> nat --> type_of t1) $ t1 $ t2

fun mk_w2ui t =
    Const(@{const_name "Word.unsigned"}, type_of t --> int) $ t

fun mk_w2si t =
    Const(@{const_name "Word.signed"}, type_of t --> int) $ t


(* ----------------------------------------------------------------------
    Integer type information

    Allow for the possibility that the user may wish to verify C programs
    with different Isabelle types corresponding to int and unsigned int.
    This structure stores all of the necessary information in one place.
   ---------------------------------------------------------------------- *)

fun width_to_ity n =
    case n of
      8 => word8
    | 16 => word16
    | 32 => word32
    | 64 => word64
    | 128 => word128
    | n => mk_word_ty n

fun width_to_sity n =
    case n of
      8 => sword8
    | 16 => sword16
    | 32 => sword32
    | 64 => sword64
    | 128 => sword128
    | n => mk_sword_ty n


structure IntInfo : INT_INFO =
struct
  open Absyn  
  val bool = width_to_ity ImplementationNumbers.boolWidth
  val char = if CType.is_signed PlainChar then
               width_to_sity ImplementationNumbers.charWidth
             else
               width_to_ity ImplementationNumbers.charWidth
  val short = width_to_sity ImplementationNumbers.shortWidth
  val int = width_to_sity ImplementationNumbers.intWidth
  val long  = width_to_sity ImplementationNumbers.longWidth
  val longlong = width_to_sity ImplementationNumbers.llongWidth
  val int128 = width_to_sity ImplementationNumbers.int128Width
  val addr_ty = width_to_ity ImplementationNumbers.ptrWidth
  val ity_to_nat = mk_w2n
  val INT_MAX = ImplementationNumbers.INT_MAX
  val INT_MIN = ImplementationNumbers.INT_MIN
  val UINT_MAX = ImplementationNumbers.UINT_MAX
  fun intify t = @{term "Int.int"} $ t

  fun gen_ity2wty {bitint_padding} PlainChar = char
    | gen_ity2wty {bitint_padding} Bool = bool
    | gen_ity2wty {bitint_padding} (Unsigned Char) = width_to_ity ImplementationNumbers.charWidth
    | gen_ity2wty {bitint_padding} (Unsigned Short) = width_to_ity ImplementationNumbers.shortWidth
    | gen_ity2wty {bitint_padding} (Unsigned Int) = width_to_ity ImplementationNumbers.intWidth
    | gen_ity2wty {bitint_padding} (Unsigned Long) = width_to_ity ImplementationNumbers.longWidth
    | gen_ity2wty {bitint_padding} (Unsigned LongLong) = width_to_ity ImplementationNumbers.llongWidth
    | gen_ity2wty {bitint_padding} (Unsigned Int128) = width_to_ity ImplementationNumbers.int128Width
    | gen_ity2wty {bitint_padding} (Unsigned (BitInt n)) = width_to_ity (if bitint_padding then next_power_of_2 n else n)
    | gen_ity2wty {bitint_padding} (Signed Char) = width_to_sity ImplementationNumbers.charWidth
    | gen_ity2wty {bitint_padding} (Signed Short) = width_to_sity ImplementationNumbers.shortWidth
    | gen_ity2wty {bitint_padding} (Signed Int) = width_to_sity ImplementationNumbers.intWidth
    | gen_ity2wty {bitint_padding} (Signed Long) = width_to_sity ImplementationNumbers.longWidth
    | gen_ity2wty {bitint_padding} (Signed LongLong) = width_to_sity ImplementationNumbers.llongWidth
    | gen_ity2wty {bitint_padding} (Signed Int128) = width_to_sity ImplementationNumbers.int128Width
    | gen_ity2wty {bitint_padding} (Signed (BitInt n)) = width_to_sity (if bitint_padding then next_power_of_2 n else n)
    | gen_ity2wty {bitint_padding} (EnumTy _) = width_to_sity ImplementationNumbers.intWidth
    | gen_ity2wty {bitint_padding} ty = raise Fail ("ity2wty: argument "^tyname ty^
                                      " not integer type")

  val ity2wty = gen_ity2wty {bitint_padding = false}
  val ptrdiff_ity = ity2wty ImplementationTypes.ptrdiff_t
  fun numeral2w ty = mk_numeral (ity2wty ty)
  fun nat_to_word PlainChar n = mk_i2w_t char $ intify n
    | nat_to_word (ty as (Signed _)) n = mk_i2w_t (ity2wty ty) $ intify n
    | nat_to_word (ty as (Unsigned _)) n = mk_i2w_t (ity2wty ty) $ intify n
    | nat_to_word ty _ = raise Fail ("nat_to_word: can't convert from ctype "^
                                     tyname ty)
  fun word_to_int ty n =
    if CType.is_signed ty then
      mk_w2si n
    else
      mk_w2ui n
end


(* UMM types *)
val addr_ty = IntInfo.addr_ty
val heap_ty = addr_ty --> word8

fun mk_ptr_ty ty = \<^Type>\<open>ptr ty\<close>
fun dest_ptr_ty ty =
    case ty of
       \<^Type>\<open>ptr T\<close> => T
    | _ => raise Fail "dest_ptr_ty: not a ptr type"
val is_ptr_ty = can dest_ptr_ty

(* vcg terms *)
fun mk_ptr (w,ty) =
    Const(@{const_name "CTypesBase.ptr.Ptr"}, addr_ty --> mk_ptr_ty ty) $ w

fun mk_global_addr_ptr ctxt (gname, ty) =
  let
    val (ptr as Const (c, T)) = Proof_Context.read_const {proper=true, strict=true} ctxt gname
    val _ = @{assert} (T = mk_ptr_ty ty)
  in
    ptr
  end

fun mk_local_ptr_name name =
  suffix "\<^sub>p" name

fun dest_local_ptr_name name =
  the_default name (try (unsuffix "\<^sub>p") name)

fun mk_local_ptr (name, ty) =
  let
    val name = mk_local_ptr_name name
  in
    Free (name, mk_ptr_ty ty)
  end

fun mk_fnptr thy s =
    HP_TermsTypes.mk_VCGfn_name (Proof_Context.init_global thy) (MString.dest s)

(* UMM terms *)
fun mk_heap_upd_t ty = Const(@{const_name "CTypesDefs.heap_update"},
                             mk_ptr_ty ty --> ty --> heap_ty --> heap_ty)
fun mk_heap_upd (addr_t, val_t) =
    mk_heap_upd_t (type_of val_t) $ addr_t $ val_t

fun mk_lift_t ty = Const(@{const_name "CTypesDefs.h_val"}, heap_ty --> mk_ptr_ty ty --> ty)

fun mk_lift (hp_t, addr_t) =
    mk_lift_t (dest_ptr_ty (type_of addr_t)) $ hp_t $ addr_t

fun mk_ptr (w,ty) =
    Const(@{const_name "CTypesBase.ptr.Ptr"}, addr_ty --> mk_ptr_ty ty) $ w



fun mk_qualified_field_name s = mk_list_singleton (mk_string s)
val field_name_ty = string_ty
val qualified_field_name_ty = mk_list_type field_name_ty

fun mk_field_lvalue (p,f,ty) =
    Const(@{const_name "CTypesDefs.field_lvalue"},
          mk_ptr_ty ty --> qualified_field_name_ty --> addr_ty) $ p $ f

fun mk_field_lvalue_ptr _ (p,f,ty,res_ty) =
      mk_ptr (mk_field_lvalue (p,f,ty), res_ty)

val NULLptr = mk_ptr(Const(@{const_name "Groups.zero_class.zero"}, addr_ty), unit)

fun mk_ptr_coerce(oldtm, newty) = let
  val oldty = type_of oldtm
in
  Const(@{const_name "ptr_coerce"}, oldty --> newty) $ oldtm
end

fun mk_cguard_ptr t = let
  val ptrty = type_of t
in
  Const(@{const_name "c_guard"}, ptrty --> bool) $ t
end

fun mk_ptr_val tm = let
  val ty = type_of tm
in
  Const(@{const_name "ptr_val"}, ty --> addr_ty) $ tm
end

fun mk_ptr_add (t1, t2) = let
  val ty = type_of t1
in
  Const (@{const_name "CTypesDefs.ptr_add"}, ty --> @{typ int} --> ty) $ t1 $ t2
end

fun mk_okptr tm = mk_cguard_ptr tm

fun mk_sizeof tm = let
  val ty = type_of tm
in
  Const(@{const_name "CTypesDefs.size_of"}, ty --> nat) $ tm
end

fun mk_bool_term true = True | mk_bool_term false = False

fun mk_asm_spec styargs msT ghost_acc vol nm lhs_update args = let
  val all_args = [Logic.mk_type msT, ghost_acc,
    mk_bool_term vol, HOLogic.mk_string nm,
    lhs_update, Abs ("s", hd styargs, HOLogic.mk_list addr_ty
            (map (fn a => a $ Bound 0) args))]
  val sty = hd styargs
  val rel_typ = mk_prod_ty (sty, sty) |> mk_set_type
  val typ = map fastype_of all_args ---> rel_typ
  val rel = list_comb (Const (@{const_name "CProof.asm_spec"}, typ), all_args)
in mk_Spec (styargs, rel) end

fun mk_asm_ok_to_ignore msT vol nm = let
  val all_args = [Logic.mk_type msT, mk_bool_term vol, HOLogic.mk_string nm]
  val const_typ = map fastype_of all_args ---> @{typ bool}
in list_comb (Const (@{const_name asm_semantics_ok_to_ignore}, const_typ),
  all_args)
end

datatype 'varinfo termbuilder =
         TB of {var_updator : bool -> 'varinfo -> term -> term -> term,
                var_accessor : 'varinfo -> term -> term,
                rcd_updator : string*string -> term -> term -> term,
                rcd_accessor : string*string -> term -> term}
               (* in updator functions, first term is the new value, second is
                  composite value being updated *)

end (* struct *)
