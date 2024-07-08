(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

structure ExprDatatype =
struct

type numliteral_info =
     {value: IntInf.int, suffix : string, base : StringCvt.radix}
     (* use of IntInf makes no difference in Poly, but is useful in mlton *)

type 'a wrap = 'a RegionExtras.wrap
type 'a ctype = 'a CType.ctype

datatype literalconstant_node =
         NUMCONST of numliteral_info
       | STRING_LIT of string
type literalconstant = literalconstant_node wrap

datatype binoptype =
         LogOr | LogAnd | Equals | NotEquals | BitwiseAnd | BitwiseOr
       | BitwiseXOr
       | Lt | Gt | Leq | Geq | Plus | Minus | Times | Divides | Modulus
       | RShift | LShift

datatype unoptype = Negate | Not | Addr | BitNegate

type var_info = (int CType.ctype * more_info) option Unsynchronized.ref

fun map_more_info f x =
  case !x of
    SOME (ty, info) => Unsynchronized.ref (SOME (ty, f info))
  | NONE => Unsynchronized.ref NONE

fun var_info_ord (v1, v2) = option_ord (prod_ord (CType.ctype_ord int_ord) more_info_ord) (!v1, !v2)

datatype expr_node =
         BinOp of binoptype * expr * expr
       | UnOp of unoptype * expr
       | CondExp of expr * expr * expr
       | Constant of literalconstant
       | Var of string * var_info
       | StructDot of expr * string
       | ArrayDeref of expr * expr
       | Deref of expr
       | TypeCast of expr ctype wrap * expr
       | Sizeof of expr
       | SizeofTy of expr ctype wrap
       | EFnCall of expr * expr list
       | CompLiteral of expr ctype * (designator list * initializer) list
       | Arbitrary of expr ctype
       | MKBOOL of expr
       | OffsetOf of expr ctype wrap * string list
and expr = E of expr_node wrap
and initializer =
    InitE of expr
  | InitList of (designator list * initializer) list
and designator =
    DesignE of expr
  | DesignFld of string

datatype ecenv =
         CE of {enumenv : (IntInf.int * string option) Symtab.table,
                          (* lookup is from econst name to value and the
                             name of the type it belongs to, if any
                             (they can be anonymous) *)
                typing : expr -> int ctype,
                structsize : string -> (int * bool),
                offset_of: string -> string list -> int}

end (* struct *)

signature EXPR =
sig

  datatype binoptype = datatype ExprDatatype.binoptype
  datatype unoptype = datatype ExprDatatype.unoptype
  datatype expr_node = datatype ExprDatatype.expr_node
  datatype initializer = datatype ExprDatatype.initializer
  datatype designator = datatype ExprDatatype.designator
  datatype literalconstant_node = datatype ExprDatatype.literalconstant_node
  type expr
  type numliteral_info = ExprDatatype.numliteral_info
  type literalconstant = ExprDatatype.literalconstant

  val unopname : unoptype -> string
  val unop_ord : unoptype * unoptype -> order

  val binopname : binoptype -> string
  val binop_ord : binoptype * binoptype -> order
  val expr_string : expr -> string

  val numconst_type : numliteral_info -> 'a CType.ctype (* can raise Subscript *)
  val eval_litconst : Proof.context -> literalconstant -> IntInf.int * 'a CType.ctype

  val enode : expr -> expr_node
  val eleft : expr -> SourcePos.t
  val eright : expr -> SourcePos.t
  val ewrap : expr_node * SourcePos.t * SourcePos.t -> expr
  val ebogwrap : expr_node -> expr
  val eFail : Proof.context -> expr * string -> 'a
  val expr_ord : expr * expr -> order

  val is_number : expr -> bool
  val fncall_free : expr -> bool
  val eneeds_sc_protection : expr -> bool

  val expr_int : IntInf.int -> expr
  val eval_binop : Proof.context ->
      (SourcePos.t * SourcePos.t) ->
      binoptype * (IntInf.int * 'a CType.ctype) * (IntInf.int * 'a CType.ctype) ->
      IntInf.int * 'a CType.ctype


  datatype ecenv = datatype ExprDatatype.ecenv (* "enumerated constant environment" *)
  val eclookup : ecenv -> string -> (IntInf.int * string option) option
  val constify_abtype : bool -> Proof.context -> ecenv -> expr CType.ctype -> int CType.ctype
  val consteval : bool -> Proof.context -> ecenv -> expr -> IntInf.int

  val fun_of_var_expr: expr -> string option
  val vars_expr: {typ:bool, addr:bool} -> expr -> (string * ExprDatatype.var_info) list

  val map_var: ((string *  ExprDatatype.var_info) -> (string *  ExprDatatype.var_info)) -> expr_node -> expr_node
  val map_enode: (expr_node -> expr_node) -> expr -> expr
end

structure Expr : EXPR =
struct

open RegionExtras
open CType
open ExprDatatype

(* can raise Subscript *)
fun numconst_type {value,base,suffix} = let
  val suffix = String.translate (str o Char.toLower) suffix
  val suffixU = CharVector.exists (fn c => c = #"u") suffix
  val suffixLL = String.isPrefix "ll" suffix orelse
                 String.isSuffix "ll" suffix
  val suffixL = (String.isPrefix "l" suffix orelse
                 String.isSuffix "l" suffix)
  val type_index = if suffixLL then 4 else if suffixL then 2 else 0
  (* where to start looking in the typesequence *)
  val typesequence = [Signed Int, Unsigned Int,
                      Signed Long, Unsigned Long,
                      Signed LongLong, Unsigned LongLong,
                      Signed Int128, Unsigned Int128]
  fun search i = let
    val candidate = List.nth(typesequence, i)
  in
    if suffixU andalso is_signed candidate then search (i + 1)
    else if base = StringCvt.DEC andalso not suffixU andalso
            not (is_signed candidate)
    then search (i + 1)
    else if imax candidate >= value then candidate
    else search (i + 1)
  end
in
  search type_index
end

fun eval_litconst ctxt lc = let
  val fi = IntInf.fromInt
in
  case node lc of
    NUMCONST nc => (#value nc, numconst_type nc)
  | STRING_LIT _ => (Feedback.errorStr' ctxt (left lc, right lc,
                                        "Don't evaluate string literals!");
                     (fi 1, Signed Int))
end

fun unopname opn =
    case opn of
        Negate => "-"
      | Not => "!"
      | Addr => "&"
      | BitNegate => "~"
val unop_ord = inv_img_ord unopname string_ord

fun binopname opn =
    case opn of
      Lt => "<"
    | Gt => ">"
    | Leq => "<="
    | Geq => ">="
    | Equals => "=="
    | NotEquals => "!="
    | LogOr => "||"
    | LogAnd => "&&"
    | Plus => "+"
    | Times => "*"
    | Minus => "-"
    | Divides => "/"
    | BitwiseAnd => "&"
    | BitwiseOr => "|"
    | BitwiseXOr => "^"
    | RShift => ">>"
    | LShift => "<<"
    | Modulus => "%"

val binop_ord = inv_img_ord binopname string_ord

type var_info = (int ctype * more_info) option Unsynchronized.ref


fun eleft (E w) = the (Region.left (Region.Wrap.region w))
    handle Option => bogus
fun eright (E w) = the (Region.right (Region.Wrap.region w))
    handle Option => bogus
fun enode (E w) = node w
fun eregion (E w) = Region.Wrap.region w
fun ewrap (n, l, r) = E (wrap(n,l,r))
fun ebogwrap en = E (bogwrap en)
fun eFail ctxt (e, s) = Feedback.error_region ctxt (eregion e) s

fun fncall_free e =
    case enode e of
      BinOp(_, e1, e2) => fncall_free e1 andalso fncall_free e2
    | UnOp(_, e) => fncall_free e
    | CondExp(e1,e2,e3) => fncall_free e1 andalso fncall_free e2 andalso
                           fncall_free e3
    | StructDot(e, _) => fncall_free e
    | ArrayDeref(e1, e2) => fncall_free e1 andalso fncall_free e2
    | Deref e => fncall_free e
    | TypeCast(_, e) => fncall_free e
    | EFnCall _ => false
    | CompLiteral (_, dilist) => List.all dinit_fncall_free dilist
    | _ => true
and dinit_fncall_free (dis, init) =
    List.all difncall_free dis andalso init_fncall_free init
and difncall_free (DesignE e) = fncall_free e
  | difncall_free (DesignFld _) = true
and init_fncall_free (InitE e) = fncall_free e
  | init_fncall_free (InitList dis) = List.all dinit_fncall_free dis

fun is_number e =
    case enode e of
      Constant litw => (case node litw of NUMCONST _ => true | _ => false)
    | _ => false

fun sint i = {value = i, suffix = "", base = StringCvt.DEC}
fun expr_int i = ebogwrap (Constant (bogwrap (NUMCONST (sint i))))

fun expr_string e =
    case enode e of
      BinOp _ => "BinOp"
    | UnOp _ => "UnOp"
    | CondExp _ => "CondExp"
    | Constant _ => "Constant"
    | Var(nm, _) => "Var" ^ nm
    | StructDot _ => "StructDot"
    | ArrayDeref _ => "ArrayDeref"
    | Deref _ => "Deref"
    | TypeCast _ => "TypeCast"
    | Sizeof _ => "Sizeof"
    | SizeofTy _ => "SizeofTy"
    | EFnCall _ => "EFnCall"
    | CompLiteral _ => "CompLit"
    | Arbitrary _ => "Arbitrary"
    | MKBOOL _ => "MKBOOL"
    | OffsetOf _ => "OffsetOf"
    | _ => "[whoa! Unknown expr type]"

fun radn r = let
  open StringCvt
in
  case r of
      BIN => 2
    | OCT => 8
    | DEC => 10
    | HEX => 16
end

fun nli_ord (nli1, nli2) = let
  val {value = v1, suffix = s1, base = r1} = nli1
  val {value = v2, suffix = s2, base = r2} = nli2
in
  prod_ord (prod_ord int_ord string_ord) (measure_ord radn)
               (((v1, s1), r1), ((v2, s2), r2))
end

(* ignores location information *)
fun lc_ord (lc1, lc2) =
    case (node lc1, node lc2) of
        (NUMCONST nli1, NUMCONST nli2) => nli_ord (nli1, nli2)
      | (NUMCONST _, _) => LESS
      | (_, NUMCONST _) => GREATER
      | (STRING_LIT s1, STRING_LIT s2) => string_ord(s1, s2)

fun vi_ord((s1,vi1 : var_info), (s2,vi2)) =
    case string_ord(s1, s2) of
        EQUAL =>
        if vi1 = vi2 then EQUAL
        else option_ord (inv_img_ord #1 (ctype_ord int_ord))
                            (!vi1, !vi2)
      | x => x

(* ignores location information *)
fun expr_ord (e1,e2) =
    case string_ord (expr_string e1, expr_string e2) of
        EQUAL =>
        let
        in
          case (enode e1, enode e2) of
              (BinOp(opn1, e11, e12), BinOp(opn2, e21, e22)) =>
              (case binop_ord(opn1,opn2) of
                   EQUAL => list_ord expr_ord ([e11,e12], [e21,e22])
                 | x => x)
            | (UnOp p1, UnOp p2) => prod_ord unop_ord expr_ord (p1, p2)
            | (CondExp(e11,e12,e13), CondExp(e21,e22,e23)) =>
              list_ord expr_ord ([e11,e12,e13], [e21,e22,e23])
            | (Constant lc1, Constant lc2) => lc_ord (lc1, lc2)
            | (Var vi1, Var vi2) => vi_ord (vi1, vi2)
            | (StructDot p1, StructDot p2) =>
              prod_ord expr_ord string_ord (p1,p2)
            | (ArrayDeref p1, ArrayDeref p2) =>
              prod_ord expr_ord  expr_ord (p1,p2)
            | (Deref e1, Deref e2) => expr_ord (e1, e2)
            | (TypeCast p1, TypeCast p2) =>
              prod_ord (inv_img_ord node (ctype_ord expr_ord)) expr_ord
                           (p1, p2)
            | (Sizeof e1, Sizeof e2) => expr_ord (e1, e2)
            | (SizeofTy ty1, SizeofTy ty2) =>
              inv_img_ord node (ctype_ord expr_ord) (ty1, ty2)
            | (EFnCall(e1, elist1), EFnCall(e2, elist2)) =>
              list_ord expr_ord (e1::elist1, e2::elist2)
            | (CompLiteral p1, CompLiteral p2) =>
              prod_ord (ctype_ord expr_ord) (list_ord (prod_ord (list_ord d_cmp) i_cmp))
                           (p1, p2)
            | (Arbitrary ty1, Arbitrary ty2) => ctype_ord expr_ord (ty1, ty2)
            | (MKBOOL e1, MKBOOL e2) => expr_ord (e1, e2)
            | (OffsetOf p1, OffsetOf p2) =>
              prod_ord (inv_img_ord node (ctype_ord expr_ord)) (list_ord string_ord) (p1, p2)
            | _ => raise Fail ("expr_compare: can't happen: " ^ expr_string e1)
        end
      | x => x
and d_cmp p =
    case p of
        (DesignE e1, DesignE e2) => expr_ord (e1, e2)
      | (DesignE _, _) => LESS
      | (_, DesignE _) => GREATER
      | (DesignFld fld1, DesignFld fld2) => string_ord (fld1, fld2)
and i_cmp p =
    case p of
        (InitE e1, InitE e2) => expr_ord (e1,e2)
      | (InitE _, _) => LESS
      | (_, InitE _) => GREATER
      | (InitList dil1, InitList dil2) =>
        list_ord (prod_ord (list_ord d_cmp) i_cmp) (dil1, dil2)

fun bool b = (if b then IntInf.fromInt 1 else IntInf.fromInt 0, Signed Int)

fun safeop ctxt (l,r) destty f x = let
  val dmod = imax destty + 1
  val dmin = imin destty
  val result = f x
  val overflow = result >= dmod orelse result < dmin
  val result' = if overflow then (result mod dmod, destty)
                else (result, destty)
in
  if overflow andalso is_signed destty then
    Feedback.errorStr' ctxt (l,r,"Signed overflow")
  else ();
  result'
end


fun eval_binop ctxt (l, r) (binop, (n1,ty1), (n2,ty2)) = let
  open IntInf
  val destty = case binop of
                 LShift => integer_promotions ty1
               | RShift => integer_promotions ty2
               | _ => arithmetic_conversion (ty1, ty2)
  val safeop = fn f => safeop ctxt (l,r) destty f (n1,n2)
in
  case binop of
    Lt => bool (n1 < n2)
  | Gt => bool (n1 > n2)
  | Leq => bool (n1 <= n2)
  | Geq => bool (n1 >= n2)
  | Equals => bool (n1 = n2)
  | NotEquals => bool (n1 <> n2)
  | LogOr => bool (n1 <> 0 orelse n2 <> 0)
  | LogAnd => bool (n1 <> 0 andalso n2 <> 0)
  | Plus => safeop op+
  | Times => safeop op*
  | Minus => safeop op-
  | Divides => safeop (op div)
  | Modulus => safeop (op mod)
  | BitwiseAnd => (andb(n1, n2), destty)
  | BitwiseOr => (orb(n1, n2), destty)
  | BitwiseXOr => (xorb(n1, n2), destty)
  | LShift => (if n2 < 0 orelse n2 >= ty_width destty then
                 Feedback.errorStr' ctxt (l,r,"Invalid/overflowing shift")
               else ();
               safeop (fn (n1,n2) => <<(n1, Word.fromInt (toInt n2))))
  | RShift => (if n2 < 0 orelse n2 >= ty_width destty orelse
                  (is_signed destty andalso n1 < 0)
               then
                 Feedback.errorStr' ctxt (l,r,"Invalid/overflowing shift")
               else ();
               safeop (fn (n1,n2) => ~>>(n1, Word.fromInt (toInt n2))))
end

val fi = IntInf.fromInt

fun eval_unop ctxt (l, r, uop, (n, ty)) = let
  open IntInf
  val destty = integer_promotions ty
in
  case uop of
    Negate => safeop ctxt (l,r) destty ~ n
  | Not => bool (n = 0)
  | Addr => (Feedback.errorStr' ctxt (l,r, "Can't evaluate address-of in constant \
                                     \expression");
             (fi 0, Signed Int))
  | BitNegate => (notb n, destty)
end


fun eclookup (CE {enumenv,...}) s = Symtab.lookup enumenv s

fun get_offset_of ctxt offset_of cty flds =
  let
    fun off kind s =
      let
        val n = offset_of s flds
      in
       if n >= 0 then n
       else Feedback.error_range ctxt (left cty) (right cty)
             ("Fields " ^  (space_implode "." (map CType.unC_field_name flds)) ^
              " not contained in " ^ kind ^ " " ^ quote s)
     end

  in
    case node cty of
      StructTy s => off "structure" s
    | UnionTy u => off "union" u
    | _ => (Feedback.errorStr' ctxt (left cty, right cty, "offset_of type not supported"); ~1)
  end

fun consteval0 report_error ctxt (ecenv as CE {enumenv, typing, structsize, offset_of}) e = let
  val fi = IntInf.fromInt
  val zero = (fi 0, Signed Int)
  fun Fail s = if report_error then Feedback.error_range ctxt (eleft e) (eright e) s else error s
  val consteval = consteval0 report_error ctxt ecenv
in
  case enode e of
    BinOp (bop, e1, e2) => eval_binop ctxt (eleft e, eright e)
                                      (bop, consteval e1, consteval e2)
  | UnOp (uop, e) => eval_unop ctxt (eleft e, eright e, uop, consteval e)
  | Constant lc => eval_litconst ctxt lc
  | Var (s,_) => let
    in
      case Symtab.lookup enumenv s of
        NONE => Fail ("Variable "^s^ " can't appear in a constant expression")
      | SOME (v, _) => (v, Signed Int)
    end
  | StructDot _ =>
    Fail "Can't evaluate fieldref in constant expression"
  | ArrayDeref _ =>
    Fail "Can't evaluate array deref in constant expression"
  | Deref _ => Fail "Can't evaluate deref in constant expression"
  | CondExp(g,t,e) => if #1 (consteval g) <> fi 0 then consteval t
                      else consteval e
  | SizeofTy ty =>
     let
       val sz = fst (sizeof structsize (constify_abtype report_error ctxt ecenv (node ty)))
     in (fi sz, ImplementationTypes.size_t)
     end
  | Sizeof e0 => (fi (fst (sizeof structsize (typing e0))),
                  ImplementationTypes.size_t)
  | MKBOOL e => bool (#1 (consteval e) <> fi 0)
  | OffsetOf (cty, flds) => (fi (get_offset_of ctxt offset_of cty flds),
                            ImplementationTypes.size_t)
  | TypeCast(destty, e0) => let
      val (v,_) = consteval e0
    in
      safeop ctxt (eleft e, eright e) (node destty) (fn x => x) v
    end
  | _ => Fail ("Unexpected expression form (" ^ expr_string e ^
               ") in consteval")
end
and consteval report_error ctxt ecenv e = #1 (consteval0 report_error ctxt ecenv e)
and constify_abtype report_error ctxt (ecenv as CE {enumenv, typing, structsize, offset_of}) (ty : expr ctype): int ctype = let
  fun recurse ty =
      case ty of
        Array (ty0, SOME sz) => Array (recurse ty0,
                                       SOME (IntInf.toInt (consteval report_error ctxt ecenv sz)))
      | Array (ty0, NONE) => Array(recurse ty0, NONE)
      | Ptr ty => Ptr (recurse ty)
      | Signed x => Signed x
      | PlainChar => PlainChar
      | Unsigned x => Unsigned x
      | StructTy s => StructTy s
      | UnionTy u => UnionTy u
      | EnumTy x => EnumTy x
      | Bitfield(ty0,e) => Bitfield (recurse ty0, IntInf.toInt (consteval report_error ctxt ecenv e))
      | Ident s => Ident s
      | Function (retty, args) => Function (recurse retty, map recurse args)
      | Void => Void
      | Bool => Bool
      | TypeOf e => typing e
      | _ => raise Fail ("constify_abtype: unexpected type form: "^tyname0 (K "") ty)
in
  recurse ty
end

(* predicates on expressions to determine if they can't be evaluated freely
   when on the rhs of a short-circuiting operator.  *)
fun bop_needs_scprot bop =
    case bop of
      Divides => true
    | Modulus => true
    | RShift => true
    | LShift => true
    | _ => false
fun uop_needs_scprot _ = false

fun eneeds_sc_protection e =
    case enode e of
      BinOp(bop, e1, e2) => bop_needs_scprot bop orelse
                            eneeds_sc_protection e1 orelse
                            eneeds_sc_protection e2
    | UnOp(uop, e) => uop_needs_scprot uop orelse eneeds_sc_protection e
    | CondExp(e1,e2,e3) => List.exists eneeds_sc_protection [e1,e2,e3]
    | Constant _ => false
    | Var _ => false
    | StructDot (e,_) => eneeds_sc_protection e
    | ArrayDeref _ => true (* could try to figure out if the array is
                                    a pointer, but even if it isn't, there
                                    should be bounds checking going on *)
    | Deref _ => true
    | TypeCast (_, e) => eneeds_sc_protection e
    | Sizeof _ => false
    | SizeofTy _ => false
    | EFnCall _ => true
    | CompLiteral (_, dis) => List.exists (i_needs_scprot o #2) dis
    | Arbitrary _ => false
    | _ => raise Fail ("eneeds_sc_protection: can't handle "^expr_string e)
and i_needs_scprot i =
    case i of
      InitE e => eneeds_sc_protection e
    | InitList dis => List.exists (i_needs_scprot o #2) dis



fun fun_of_var_expr (E w) = case node w of
   Var (_, r) => Option.mapPartial (dest_munged_var_info o snd) (!r)
 | _ => NONE


fun vars_node (t as {typ, addr}) e =
  case e of
    BinOp (bop, e1, e2) => vars_expr t e1 @ vars_expr t e2
  | UnOp (uop, e1) => if not addr andalso uop = Addr then [] else vars_expr t e1
  | CondExp (e1, e2, e3) => vars_expr t e1 @ vars_expr t e2 @ vars_expr t e3
  | Constant _ => []
  | Var (n, info) => [(n, info)]
  | StructDot (e1, _) => vars_expr t e1
  | ArrayDeref (e1, e2) => vars_expr t e1 @ vars_expr t e2
  | Deref e1 => vars_expr t e1
  | TypeCast (T, e1) => vars_type t (node T) @ vars_expr t e1
  | Sizeof e1 => if typ then vars_expr t e1 else []
  | SizeofTy T => vars_type t (node T)
  | EFnCall (e, es) => vars_expr t e @ flat (map (vars_expr t) es)
  | CompLiteral (T, dis) =>
       vars_type t T @ flat (map (fn (d, i) => flat (map (vars_designator t) d) @ vars_initializer t i) dis)
  | Arbitrary T => vars_type t T
  | MKBOOL e1 => vars_expr t e1
  | OffsetOf (T, _) => vars_type t (node T)
and vars_expr t (E e) = vars_node t (node e)
and vars_initializer t i =
  case i of
    InitE e1 => vars_expr t e1
  | InitList dis => flat (map (fn (d, i) => flat (map (vars_designator t) d) @ vars_initializer t i) dis)
and vars_designator t d =
  case d of
    DesignE e1 => vars_expr t e1
  | DesignFld _ => []
and vars_type (t as {typ, addr}) T = if not typ then [] else
  (case T of
    TypeOf e => vars_expr t e
  | Ptr T1 => vars_type t T1
  | Array (T1, Topt) => vars_type t T1 @ (case Topt of NONE => [] | SOME e => vars_expr t e)
  | Bitfield (T1, e) => vars_type t T1 @ vars_expr t e
  | Function (T1, Ts) => vars_type t T1 @ flat (map (vars_type t) Ts)
  | _ => [])


fun map_var f (Var x) = Var (f x)
  | map_var _ e = e

fun map_enode f (E x) = E (apnode f x)

end (* struct *)
