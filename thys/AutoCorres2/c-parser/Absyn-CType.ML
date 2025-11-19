(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

structure CTypeDatatype =
struct
datatype inttype = datatype BaseCTypes.base_inttype
datatype 'c ctype =
         Signed of 'c inttype
       | Unsigned of 'c inttype
       | Bool
       | PlainChar
       | StructTy of string
       | UnionTy of string
       | EnumTy of string option
       | Ptr of 'c ctype
       | Array of 'c ctype * 'c option
       | Bitfield of 'c ctype * 'c (* true for signed field *)
       | Ident of string
       | Function of 'c ctype * 'c ctype list
       | Void
       | TypeOf of 'c
end

signature CTYPE =
sig
  datatype inttype = datatype CTypeDatatype.inttype
  datatype ctype = datatype CTypeDatatype.ctype
  datatype rcd_kind = Struct
                    | Union of string list (* list of variants that are actually used in program *)
  datatype attribute = AlignedExponent of int | Packed
  val type_of_rcd : string * (rcd_kind * 'a * 'c * 'd) -> 'b CTypeDatatype.ctype
  val inttyname : int inttype -> string
  val inttype_ord : int inttype * int inttype -> order
  val int_width : int inttype -> IntInf.int (* size in bits *)
  val int_sizeof : int inttype -> int (* size in bytes *)
  val int_alignof : int inttype -> int
  val next_power_of_2: int -> int
  val next_power_of_2_inttype: int inttype -> int inttype
  val next_power_of_2_bitint: int ctype -> int ctype

  val map_atomic_ctype : ('a CTypeDatatype.ctype -> 'a CTypeDatatype.ctype) ->
      'a CTypeDatatype.ctype -> 'a CTypeDatatype.ctype
  val is_signed : 'a ctype -> bool
  val dest_int_type : 'a ctype -> (bool * 'a inttype)
  val scalar_type : 'a ctype -> bool
  val ptr_type : 'a ctype -> bool
  val ptr_or_array_type : 'a ctype -> bool
  val integer_type : 'a ctype -> bool
  val arithmetic_type : 'a ctype -> bool
  val array_type : 'a ctype -> bool
  val flexible_array_type: 'a ctype -> bool
  val function_type : 'a ctype -> bool
  val fun_ptr_type: 'a ctype -> bool
  val aggregate_type : 'a ctype -> bool
  val dest_union_type : 'a ctype -> string option
  val is_union_type : 'a ctype -> bool
  val dest_struct_type : 'a ctype -> string option
  val is_struct_type : 'a ctype -> bool
  val dest_rcd_type: ' ctype -> string option
  val single_variant : string -> string list -> (string RegionExtras.wrap * 'a) list -> (string RegionExtras.wrap * 'a) list
  val active_variants : string -> string list -> (string RegionExtras.wrap * 'a) list -> (string  RegionExtras.wrap * 'a) list

  val array_to_ptr_decay : 'a ctype -> 'a ctype
  val fparam_norm : 'a ctype -> 'a ctype
  val param_norm : 'a ctype -> 'a ctype
  val remove_enums : 'a ctype -> 'a ctype
  val integer_promotions : 'a ctype -> 'a ctype
  val arithmetic_conversion : int ctype * int ctype -> int ctype
  val unify_types : int ctype * int ctype -> int ctype
  val imax : int ctype -> IntInf.int
  val imin : int ctype -> IntInf.int
  val ty_width : int ctype -> IntInf.int (* only for integral types *)
  val sizeof : (string -> (int * bool)) -> int ctype -> (int * bool)
               (* function gives sizes for structs (by name) *)

  val norm_enum: 'a ctype -> 'a ctype
  val tyname0 : ('a -> string) -> 'a ctype -> string
  val tyname : int ctype -> string

  val ctype_ord : ('a * 'a -> order) -> ('a -> int) -> 'a ctype * 'a ctype -> order
  structure ImplementationTypes : sig
    val size_t : int ctype
    val ptrdiff_t : int ctype
    val ptrval_t : int ctype
  end
  val C_field_name : string -> string
  val unC_field_name : string -> string
  val nested_types : 'a ctype -> 'a ctype list
  structure CTypeTab: TABLE
end

structure CType : CTYPE =
struct

datatype rcd_kind = Struct |  Union of string list
datatype attribute = AlignedExponent of int | Packed

fun single_variant name active [fld] = [fld]
  | single_variant name active flds =
    (case filter (fn (f, _) => member (op = ) active (RegionExtras.node f)) flds of
        [] => take 1 flds (* avoid empty structs *)
      | flds' as [f] => flds'
      | flds' => error ("single_variant union \"" ^ name ^ "\": only *one* active variant supported, got: "
          ^ @{make_string} flds' ^ "\nof\n" ^
          @{make_string}flds))

fun active_variants name active [fld] = [fld]
  | active_variants name active flds =
    (case filter (fn (f, _) => member (op =) active (RegionExtras.node f)) flds of
        [] => take 1 flds (* avoid empty structs *)
      | flds' => flds')


open CTypeDatatype

fun type_of_rcd (name, (Struct, _, _, _)) = StructTy name
  | type_of_rcd (name, (Union _, _, _, _)) = UnionTy name

fun gen_inttyname str_of ty =
    case ty of
      Char => "char"
    | Short => "short"
    | Int => "int"
    | Long => "long"
    | LongLong => "longlong"
    | Int128 => "int128"
    | BitInt n => "bitint_" ^ str_of n

val inttyname = gen_inttyname Int.toString

fun irank Char = 1 | irank Short = 2 | irank Int = 3 | irank Long = 4 |
    irank LongLong = 5 | irank Int128 = 6

fun raw_inttype_ord x = measure_ord irank x

local
  open ImplementationNumbers
in
fun bitwidth bw Char = charWidth
  | bitwidth bw Short = shortWidth
  | bitwidth bw Int = intWidth
  | bitwidth bw Long = longWidth
  | bitwidth bw LongLong = llongWidth
  | bitwidth bw Int128 = int128Width
  | bitwidth bw (BitInt n) = bw n
end

fun gen_inttype_ord bw (BitInt n, BitInt m) = int_ord (bw n, bw m)
  | gen_inttype_ord bw (BitInt n, x)        = (case int_ord (bw n, bitwidth bw x) of EQUAL => LESS | v => v)
  | gen_inttype_ord bw (x       , BitInt m) = (case int_ord (bitwidth bw x, bw m) of EQUAL => GREATER | v => v)
  | gen_inttype_ord bw (x       , y)        = raw_inttype_ord (x,y)

val inttype_ord = gen_inttype_ord I


fun conversion_inttype_ord ((true, i1) , (true, i2))  = inttype_ord (i1, i2)
  | conversion_inttype_ord ((false, i1), (false, i2)) = inttype_ord (i1, i2)
  | conversion_inttype_ord ((true (*signed *), i1), (false (* unsigned *), i2)) = 
      (case inttype_ord (i1, i2) of
         EQUAL => LESS
       | LESS => LESS
       | GREATER => GREATER)
  | conversion_inttype_ord ((false (*unsigned *), i1), (true (* signed *), i2)) = 
      (case inttype_ord (i1, i2) of
         EQUAL => GREATER
       | LESS => GREATER
       | GREATER => LESS)
       
fun bool_compare (b1,b2) = if b1 = b2 then EQUAL
                           else if b1 = false then LESS
                           else GREATER


fun is_signed (Signed _) = true
  | is_signed PlainChar = ImplementationNumbers.char_signedp
  | is_signed _ = false

fun dest_int_type (Signed i) = (true, i)
  | dest_int_type (Unsigned i) = (false, i)
  | dest_int_type  _ = raise Fail ("integer type expected")

fun dest_union_type (UnionTy s) = SOME s
  | dest_union_type _ = NONE

fun is_union_type t = (is_some o dest_union_type) t

fun dest_struct_type (StructTy s) = SOME s
  | dest_struct_type _ = NONE

fun is_struct_type t = (is_some o dest_struct_type) t

fun dest_rcd_type (StructTy name) = SOME name
  | dest_rcd_type (UnionTy name) = SOME name
  | dest_rcd_type _ = NONE

fun tyname0 f ty = let
  val tyname = tyname0 f
  fun seplist [] = ""
    | seplist [x] = tyname x
    | seplist (h::t) = String.concat [tyname h, "'", seplist t]
in
  case ty of
    Signed ity => (case ity of Char => "signed_char" | _ => gen_inttyname f ity)
  | Unsigned x => let
    in
      case x of
        Int => "unsigned"
      | _ => "unsigned_"^gen_inttyname f x
    end
  | PlainChar => "char"
  | Bool => "_Bool"
  | Ptr ty0 => "ptr_to_" ^ tyname ty0
  | Array(ty0, SOME sz) => tyname ty0 ^ "_array" ^ f sz
  | Array(ty0, NONE) => tyname ty0 ^ "_array[incomplete]"
  | StructTy s => "struct_" ^ s
  | UnionTy s => "union_" ^ s
  | Ident s => "typedef_"^s
  | Bitfield (ty0, n) => tyname ty0 ^ ":" ^f n
  | Void => "void"
  | Function (ret, ptys) =>
      String.concatWith "_" [seplist ptys, "_", tyname ret]
  | EnumTy (SOME s) => "enum_"^s
  | EnumTy NONE => "anonymous_enum"
  | TypeOf _ => "typeof"
end

fun norm_enum ty =
  (case ty of
    EnumTy _ => Signed Int
  | Ptr ty0 => Ptr (norm_enum ty0)
  | Array(ty0, sz) => Array (norm_enum ty0, sz)
  | Bitfield (ty0, n) => Bitfield (norm_enum ty0, n)
  | Function (ret, ptys) =>
      Function (norm_enum ret, map norm_enum ptys)
  | T => T)

val tyname = tyname0 Int.toString


structure ImplementationTypes =
struct
  val size_t = Unsigned ImplementationNumbers.ptr_t
  val ptrdiff_t = Signed ImplementationNumbers.ptr_t
  val ptrval_t = Unsigned ImplementationNumbers.ptr_t
end

fun scalar_type ty =
    case ty  of
      Signed _ => true
    | Unsigned _ => true
    | PlainChar => true
    | Ptr _ => true
    | EnumTy _ => true
    | Array _ => true (* coz it decays to a pointer *)
    | Bool => true
    | _ => false

fun ptr_type (Ptr _) = true
  | ptr_type _ = false

fun ptr_or_array_type (Ptr _) = true
  | ptr_or_array_type (Array _) = true
  | ptr_or_array_type _ = false

fun integer_type ty = scalar_type ty andalso not (ptr_or_array_type ty)

val arithmetic_type = integer_type (* in the absence of floating types *)

fun array_to_ptr_decay (Array (x, _)) = Ptr x
  | array_to_ptr_decay t = t

fun fparam_norm ty = let
in
  case ty of
    Ptr (Array(ty,NONE)) => Ptr (Ptr (fparam_norm ty))
  | Ptr ty => Ptr (fparam_norm ty)
  | Array (ty,sz) => Array(fparam_norm ty, sz)
  | Function (ret, args) => Function(fparam_norm ret, map param_norm args)
  | ty => ty
end
and param_norm ty =
    case ty of
      Function (ret,args) =>
      Ptr (Function (fparam_norm ret, map param_norm args))
    | Array (ty, sz) => Ptr (fparam_norm ty)
    | ty => fparam_norm ty

fun array_type (Array _) = true
  | array_type _ = false

fun flexible_array_type (Array(_, NONE)) = true
  | flexible_array_type _ = false

fun function_type (Function _) = true
  | function_type _ = false

fun fun_ptr_type (Ptr (Function _)) = true
  | fun_ptr_type _ = false

fun remove_enums ty =
    case ty of
      Ptr ty => Ptr (remove_enums ty)
    | Array(ty, x) => Array(remove_enums ty, x)
    | Function(rettype, argtypes) => Function(remove_enums rettype,
                                              map remove_enums argtypes)
    | EnumTy _ => Signed Int
    | _ => ty


fun tysz_rank ty =
    case ty of
      Signed _ => 0
    | Unsigned _ => 1
    | StructTy _ => 2
    | UnionTy _ => 3
    | EnumTy _ => 4
    | Ptr _ => 5
    | Array _ => 6
    | Bitfield _ => 7
    | Ident _ => 8
    | Function _ => 9
    | Void => 10
    | PlainChar => 11
    | Bool => 12
    | TypeOf _ => 13

fun ctype_ord cecmp bw (ty1, ty2) =
  case (ty1, ty2) of
    (Signed i1, Signed i2) => gen_inttype_ord bw (i1,i2)
  | (Unsigned i1, Unsigned i2) => gen_inttype_ord bw (i1, i2)
  | (StructTy s1, StructTy s2) => string_ord(s1, s2)
  | (UnionTy s1, UnionTy s2) => string_ord(s1, s2)
  | (EnumTy s1, EnumTy s2) => option_ord string_ord(s1, s2)
  | (Ptr ty1, Ptr ty2) => ctype_ord cecmp bw (ty1, ty2)
  | (Array tysz1, Array tysz2) =>
      prod_ord (ctype_ord cecmp bw) (option_ord (cecmp)) (tysz1,tysz2)
  | (Bitfield bce1, Bitfield bce2) =>
      prod_ord (ctype_ord cecmp bw) cecmp (bce1, bce2)
  | (Ident s1, Ident s2) => string_ord(s1, s2)
  | (Function f1, Function f2) =>
      prod_ord (ctype_ord cecmp bw) (list_ord (ctype_ord cecmp bw))
                  (f1, f2)
  | _ => measure_ord tysz_rank (ty1, ty2)


fun integer_promotions ty = let
  open ImplementationNumbers
  (* see 6.3.1.1 *)
in
  case ty of
    Bool => Signed Int
  | Signed Char => Signed Int
  | Unsigned Char => if UCHAR_MAX > INT_MAX then Unsigned Int else Signed Int
  | Signed Short => Signed Int
  | Unsigned Short => if USHORT_MAX > INT_MAX then Unsigned Int else Signed Int
  | PlainChar => if CHAR_MAX > INT_MAX then Unsigned Int else Signed Int
  | EnumTy _ => Signed Int (* arbitrary! Implementations may do this
                              differently *)
  | ty => ty
end

fun imax ty = let
  open ImplementationNumbers
in
  case ty of
    Bool => 1
  | PlainChar => CHAR_MAX
  | Unsigned Char => UCHAR_MAX
  | Signed Char => SCHAR_MAX
  | Unsigned Short => USHORT_MAX
  | Signed Short => SHORT_MAX
  | Signed Int => INT_MAX
  | Unsigned Int => UINT_MAX
  | Signed Long => LONG_MAX
  | Unsigned Long => ULONG_MAX
  | Signed LongLong => LLONG_MAX
  | Unsigned LongLong => ULLONG_MAX
  | Signed Int128 => INT128_MAX
  | Unsigned Int128 => UINT128_MAX
  | Unsigned (BitInt n) => IntInf.pow (2, n)
  | Signed (BitInt n) => IntInf.pow (2, n - 1) - 1
  | _ => raise Fail ("imax called on bad type: "^tyname0 (fn _ => "") ty)
end

fun imin ty = let
  open ImplementationNumbers
in
  case ty of
    Unsigned _ => 0
  | Bool => 0
  | Signed Char => SCHAR_MIN
  | Signed Short => SHORT_MIN
  | Signed Int => INT_MIN
  | Signed Long => LONG_MIN
  | Signed LongLong => LLONG_MIN
  | Signed Int128 => INT128_MIN
  | PlainChar => CHAR_MIN
  | Signed (BitInt n) => ~ (IntInf.pow(2, n - 1))
  | _ => raise Fail ("Abysn.imin called on: "^tyname0 (fn _ => "") ty)
end

fun arithmetic_conversion (t1,t2) = let
  val t1' = integer_promotions t1
  val t2' = integer_promotions t2
  val cmp =
      ctype_ord
          (fn p => raise Fail "arithmetic_conversion: comparing non-arithmetic\
                              \ types")
          I
  fun signedp (Signed i) = (true, i)
    | signedp (Unsigned i) = (false, i)
    | signedp x = raise Fail ("arithmetic_conversion.signedp: comparing \
                             \non-arithmetic types" ^ @{make_string} x ^ " comparing " ^ @{make_string} t1 ^ " and " ^ @{make_string} t2)
  fun doit (t1, t2) =
      case cmp(t1, t2) of
        EQUAL => t1
      | GREATER => doit(t2, t1)
      | LESS => let
          val (sp1, i1) = signedp t1
          val (sp2, i2) = signedp t2
        in
          (case conversion_inttype_ord ((sp1, i1), (sp2, i2)) of
             EQUAL => error ("arithmetic_conversion: unexpected")
           | LESS => t2
           | GREATER => t1)
        end
in
  doit (t1', t2')
end

fun unify_types (ty1, ty2) = let
  (* for use in conditional expressions where the type of the branches
     needs to be the same, but might give different types when analysed
     independently, as would happen in something like
         ptr_valid(ptr) ? ptr : 0;
  *)
in
  if ptr_or_array_type ty1 andalso not (ptr_or_array_type ty2) then unify_types (ty2, ty1)
  else let
      val ty2 = array_to_ptr_decay ty2
    in
      case (ty1, ty2) of
        (Signed _, Ptr _) => ty2
      | (Unsigned _, Ptr _) => ty2
      | (PlainChar, Ptr _) => ty2
      | (EnumTy _, Ptr _) => ty2
      | (Ptr subty1, Ptr subty2) => if subty1 = Void then ty2
                                    else if subty2 = Void then ty1
                                    else if subty1 = subty2 then ty1
                                    else raise Fail "Not unifiable"
      | _ => if integer_type ty1 andalso integer_type ty2 then
               arithmetic_conversion (ty1, ty2)
             else if ty1 = ty2 then ty1
             else raise Fail "Not unifiable"
    end
end

fun map_atomic_ctype f T = 
  case T of
    Signed _ => f T
  | Unsigned _ => f T
  | Bool => f T
  | PlainChar => f T
  | StructTy _ => f T
  | UnionTy _ => f T
  | EnumTy _ => f T
  | Ptr T' => Ptr (map_atomic_ctype f T')
  | Array (T', i) => Array (map_atomic_ctype f T', i)
  | Bitfield (T', b) => Bitfield (map_atomic_ctype f T', b)
  | Ident _ => f T
  | Function (resT, argTs) => Function (map_atomic_ctype f resT, map (map_atomic_ctype f) argTs)
  | Void => f T
  | TypeOf _ => f T


local open ImplementationNumbers
in
fun int_width Char = CHAR_BIT
  | int_width Short = shortWidth
  | int_width Int = intWidth
  | int_width Long = longWidth
  | int_width LongLong = llongWidth
  | int_width Int128 = int128Width
  | int_width (BitInt n) = n


fun ty_width (Signed i) = int_width i
  | ty_width (Unsigned i) = int_width i
  | ty_width PlainChar = CHAR_BIT
  | ty_width ty = raise Fail ("Absyn.ty_width: non integral argument: "^
                              tyname0 (fn _ => "") ty)

fun raw_next_power_of_2 n =
  if n <= 1 then 
    1
  else
    let
      fun pw acc =
         if acc >= n then acc
         else pw (acc * 2)
    in
      pw 1
    end

fun next_power_of_2 n = Int.max (CHAR_BIT, raw_next_power_of_2 n)
fun int_sizeof ty = 
  (case ty of BitInt n => next_power_of_2 n | _ => int_width ty) div CHAR_BIT

fun int_alignof ty = int_sizeof ty

fun next_power_of_2_inttype t =
  case t of
   BitInt n => BitInt (next_power_of_2 n)
  | _ => t

fun next_power_of_2_bitint t =
  case t of
    Signed n => Signed (next_power_of_2_inttype n)
  | Unsigned n => Unsigned (next_power_of_2_inttype n)
  | _ => t

end                  



fun sizeof (structsizes : string -> (Int.int * bool)) ty : (Int.int * bool) = let
  open ImplementationNumbers
in
  case ty of
    Signed i => (int_sizeof i, false)
  | Unsigned i => (int_sizeof i, false)
  | PlainChar => (1, false)
  | Bool => (boolWidth div CHAR_BIT, false)
  | StructTy s => structsizes s
  | UnionTy s => structsizes s
  | EnumTy s => (int_sizeof Int, false)
  | Ptr _ => (ptrWidth div CHAR_BIT, false)
  | Array(base, SOME sz) => 
      let val (el_sz, padding) = sizeof structsizes base in (sz * el_sz, padding) end
  | Array(base, NONE) => let val (_, padding) = sizeof structsizes base in (0, padding) end  (* may be relevant for flexible array member in struct *)
  | Bitfield (ty, width) =>
      let
        val (signed, int_ty) = dest_int_type ty
        val iw = int_width int_ty
      in
        if width <> 0 andalso width mod iw = 0 then (width div CHAR_BIT, false)
        else raise ERROR ("Can't compute sizes for bit-fields, (consecutive) bitfield width of "
          ^ string_of_int width ^ " is not a multiple of integer width: " ^ string_of_int iw)
      end
  | Ident _ => raise Fail "Can't compute sizes for type-defs"
  | Function _ => raise Fail "Can't compute sizes for functions"
  | Void => raise Fail "Can't compute a size for void"
  | TypeOf _ => raise Fail  "Can't compute a size for TypeOf. Should be compiled out here."
end

fun aggregate_type (StructTy _) = true
  | aggregate_type (UnionTy _) = true
  | aggregate_type (Array _) = true
  | aggregate_type _ = false

(* an approximation, ignoring the type variable component *)
fun eqty(ty1, ty2) =
    case (ty1, ty2) of
      (Signed ity1, Signed ity2) => ity1 = ity2
    | (Unsigned ity1, Unsigned ity2) => ity1 = ity2
    | (PlainChar, PlainChar) => true
    | (StructTy s1, StructTy s2) => s1 = s2
    | (UnionTy s1, UnionTy s2) => s1 = s2
    | (EnumTy s1, EnumTy s2) => s1 = s2
    | (Ptr ty1, Ptr ty2) => eqty(ty1, ty2)
    | (Array(ty1,_), Array(ty2,_)) => eqty(ty1,ty2)
    | (Bitfield(ty1, _), Bitfield(ty2,_)) => eqty(ty1,ty2)
    | (Ident s1, Ident s2) => s1 = s2
    | (Function(retty1, args1), Function(retty2, args2)) =>
         eqty(retty1,retty2) andalso
         ListPair.all eqty (args1, args2)
    | (Void, Void) => true
    | _ => false

fun C_field_name s = s ^ "_C"
fun unC_field_name s =
    if String.isSuffix "_C" s then
      String.extract(s,0,SOME(size s - 2))
    else s

fun nested_types t =
  let
    fun add_types t ts =
      case t of
       Ptr t' => add_types t' (t::ts)
      | Array (t',_) => add_types t' (t::ts)
      | Bitfield (t', _) => add_types t' (t::ts)
      | Function (r, args) => (t::ts) |> fold add_types (r::args)
      | other => other::ts
  in
    add_types t []
  end

structure CTypeTab = Table(struct
  type key = int ctype
  val ord = ctype_ord int_ord I
end)

end (* struct *)
