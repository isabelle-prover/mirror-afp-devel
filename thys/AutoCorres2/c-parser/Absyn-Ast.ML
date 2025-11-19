(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022-2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

structure AstDatatype =
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
datatype modifiertype = Plus_Plus | Minus_Minus

datatype selector = Field of string | Index of int option

fun norm_index (Index (SOME _)) = Index NONE
  | norm_index x = x

fun selector_ord (Field s1, Field s2) = fast_string_ord (s1, s2)
  | selector_ord (Field _ , Index _) = LESS
  | selector_ord (Index _, Field _)  = GREATER
  | selector_ord (Index o1, Index o2) = option_ord int_ord (o1, o2)

val selectors_ord = list_ord selector_ord

val ctype_selectors_ord = prod_ord (CType.ctype_ord int_ord I) selectors_ord

structure CTypeSelectorsTab = Table(struct
  type key = int ctype * selector list
  val ord = ctype_selectors_ord
end)

datatype more_info = 
  MungedVar of {munge : MString.t, owned_by : string option, 
    fname : string option, init : bool, kind: variable_kind}
  | EnumC
  | FunctionName



fun map_init f {munge, owned_by, fname, init, kind} = 
  {munge = munge, owned_by = owned_by, fname = fname, init= f init, kind=kind}

fun map_munged_var f (MungedVar x) = (MungedVar (f x))
  | map_munged_var _ x = x

fun dest_munged_var_info (MungedVar {fname=SOME n, ...}) = SOME n
  | dest_munged_var_info _ = NONE

fun get_init (MungedVar {init, ...} ) = SOME init
  | get_init _ = NONE 

fun munged_var_ord ({munge = m1, owned_by = o1, fname = f1, init = i1, kind = k1}, 
     {munge = m2, owned_by = o2, fname = f2, init = i2, kind = k2}) =
   (prod_ord MString.ord (prod_ord (option_ord string_ord) (prod_ord (option_ord string_ord) (prod_ord bool_ord variable_kind_ord)))) 
     ((m1, (o1, (f1, (i1, k1)))), (m2, (o2, (f2, (i2, k2)))))

fun more_info_ord (x, y) = 
  case (x, y) of
     (FunctionName, FunctionName) => EQUAL
   | (EnumC, EnumC) => EQUAL
   | (MungedVar m1, MungedVar m2) => munged_var_ord (m1, m2)
   | (MungedVar _, _) => LESS
   | (EnumC, MungedVar _) => GREATER
   | (_, FunctionName) => LESS
   | (FunctionName, _) => GREATER


type var_info = (int CType.ctype * more_info) option Unsynchronized.ref

fun map_more_info f x =
  case !x of
    SOME (ty, info) => Unsynchronized.ref (SOME (ty, f info))
  | NONE => Unsynchronized.ref NONE

fun var_info_ord (v1, v2) = option_ord (prod_ord (CType.ctype_ord int_ord I) more_info_ord) (!v1, !v2)

datatype storage_class =
         SC_EXTERN | SC_STATIC | SC_AUTO | SC_REGISTER | SC_THRD_LOCAL

datatype trappable = BreakT | ContinueT

datatype expr_origin = 
    Statement (* intermediate tag for program analysis *) 
  | Expression (* default *)
datatype block_kind = 
    Open (* intermediate tag for program analysis *) 
  | Closed (* default *)

datatype expr_node =
         BinOp of binoptype * expr * expr
       | UnOp of unoptype * expr
       | PostOp of expr * modifiertype
       | PreOp of expr * modifiertype
       | CondExp of expr * expr * expr
       | Constant of literalconstant
       | Var of string * var_info
       | StructDot of expr * string
       | ArrayDeref of expr * expr
       | Deref of expr
       | TypeCast of expr ctype wrap * expr
       | Sizeof of expr
       | SizeofTy of expr ctype wrap
       | EFnCall of expr_origin * expr * expr list
       | CompLiteral of expr ctype * (designator list * initializer) list
       | Arbitrary of expr ctype
       | MKBOOL of expr
       | OffsetOf of expr ctype wrap * string list
       | AssignE of expr_origin * expr * expr
       | StmtExpr of block_item list * expr option
       | Comma of expr * expr

and expr = E of expr_node wrap
and initializer =
    InitE of expr
  | InitList of (designator list * initializer) list
and designator =
    DesignE of expr
  | DesignFld of string

and gcc_attribute = GCC_AttribID of string
                       | GCC_AttribFn of string * expr list
                       | OWNED_BY of string

and fnspec = fnspec of string wrap
                | relspec of string wrap
                | fn_modifies of string list
                | didnt_translate
                | gcc_attribs of gcc_attribute list


and declaration =
         VarDecl of (expr ctype *
                     string wrap *
                     storage_class list *
                     initializer option *
                     gcc_attribute list)
         (* VarDecl's bool is true if the declaration is not an extern;
            if the declaration is "genuine".
            The accompanying optional initialiser is only used to calculate the
            size of an array when a declaration like
              int a[] = {...}
            is made.
            Initialisers are translated into subsequent assignment statements
            by the parser. *)
       | StructDecl of string wrap * (expr ctype * string wrap * gcc_attribute list) list * gcc_attribute list wrap
       | UnionDecl of string wrap * (expr ctype * string wrap * gcc_attribute list) list * gcc_attribute list wrap
       | TypeDecl of (expr ctype * string wrap * gcc_attribute list wrap) list
       | ExtFnDecl of {rettype : expr ctype, name : string wrap,
                       params : (expr ctype * string option) list,
                       specs : fnspec list}
       | EnumDecl of string option wrap * (string wrap * expr option) list

and statement_node =
         Assign of expr * expr
       | AssignFnCall of expr option * expr * expr list (* lval, fn, args *)
       | Chaos of expr
       | EmbFnCall of expr * expr * expr list (* lval, fn, args *)
       | Block of block_kind * (block_item list)
       | LabeledStmt of string * statement
       | While of expr * string wrap option * statement
       | Trap of trappable * statement
       | Return of expr option
       | ReturnFnCall of expr * expr list
       | Break | Continue | Goto of string
       | IfStmt of expr * statement * statement
       | Switch of expr * (expr option list * block_item list) list
       | EmptyStmt
       | Auxupd of string
       | Ghostupd of string
       | Spec of ((string * string) * statement list * string)
       | AsmStmt of {volatilep : bool, asmblock : {head : string,
                 mod1 : (string option * string * expr) list,
                 mod2 : (string option * string * expr) list,
                 mod3 : string list}}
       | LocalInit of expr
       | AttributeStmt of gcc_attribute list wrap * statement
       | ExprStmt of expr

and statement = Stmt of statement_node Region.Wrap.t
and block_item =
    BI_Stmt of statement
  | BI_Decl of declaration wrap

type body = block_item list wrap
type fn_defn = (expr ctype * string wrap) * (expr ctype * string wrap) list *
                   fnspec list (* fnspec *) * body
datatype ext_decl =
         FnDefn of fn_defn
       | Decl of declaration wrap


fun map_snode f (Stmt sw) = Stmt (Region.Wrap.map_node f sw)

type namedstringexp = string option * string * expr

type asmblock = {head : string,
                 mod1 : namedstringexp list,
                 mod2 : namedstringexp list,
                 mod3 : string list}

datatype ecenv =
         CE of {enumenv : (IntInf.int * string option) Symtab.table,
                          (* lookup is from econst name to value and the
                             name of the type it belongs to, if any
                             (they can be anonymous) *)
                typing : expr -> int ctype,
                structsize : string -> (int * bool),
                offset_of: string -> string list -> int}


fun enode (E w) = RegionExtras.node w
fun snode (Stmt w) = RegionExtras.node w
fun eleft (E w) = the (Region.left (Region.Wrap.region w))
    handle Option => RegionExtras.bogus
fun eright (E w) = the (Region.right (Region.Wrap.region w))
    handle Option => RegionExtras.bogus

fun ewrap (n, l, r) = E (RegionExtras.wrap(n,l,r))
fun swrap (s, l, r) = Stmt(RegionExtras.wrap(s,l,r))
fun sleft (Stmt w) = RegionExtras.left w
fun sright (Stmt w) = RegionExtras.right w

fun comma_exprs [] = error ("comma_exprs: empty list")
  | comma_exprs [e] = e
  | comma_exprs (e::es) = 
     let
       val e' = comma_exprs es
     in ewrap (Comma (e, e'), eleft e, eright e') end 
 
fun fold_option _ NONE acc = acc
  | fold_option f (SOME x) acc = f x acc

fun fold_map_option f NONE acc = (NONE, acc)
  | fold_map_option f (SOME x) acc = 
      let val (x', acc') = f x acc
      in (SOME x', acc') end

fun fold_expr (diginto as {types}) f_expr f_stmt e acc0 =
  let
    val fld = fold_expr diginto f_expr f_stmt
    val fld_t = fold_ctype diginto f_expr f_stmt
    val fld_i = fold_initializer diginto f_expr f_stmt
    val fld_s = fold_stmt diginto f_expr f_stmt
    val fld_b = fold_block_item diginto f_expr f_stmt
    val acc = f_expr e acc0
  in
    case enode e of
      BinOp (_, e1, e2) => fld e1 acc |> fld e2
    | UnOp (_, e1) =>  fld e1 acc
    | PostOp (e1, _) => fld e1 acc
    | PreOp (e1, _) => fld e1 acc
    | CondExp (e1, e2, e3) => fld e1 acc |> fld e2 |> fld e3
    | Constant _ => acc
    | Var _ => acc
    | StructDot (e1, _) => fld e1 acc
    | ArrayDeref (e1, e2) => fld e1 acc |> fld e2
    | Deref e1 => fld e1 acc
    | TypeCast (t, e1) => fld_t (RegionExtras.node t) acc |> fld e1
    | Sizeof e1 => fld e1 acc
    | SizeofTy t => fld_t (RegionExtras.node t) acc
    | EFnCall (_, e1, es) => fld e1 acc |> fold fld es
    | CompLiteral (t, is) => fld_t t acc |> fold fld_i (map snd is)
    | Arbitrary t => fld_t t acc
    | MKBOOL e => fld e acc
    | OffsetOf (t, _) => fld_t (RegionExtras.node t) acc
    | AssignE (_, e1, e2) => fld e1 acc |> fld e2
    | StmtExpr (bl, e1) => fold fld_b bl acc |> fold_option fld e1
    | Comma (e1, e2) => fld e1 acc |> fld e2
  end 
and fold_ctype (diginto as {types}) f_expr f_stmt t acc =
  if types then
    let
      open CType
      val fld = fold_expr diginto f_expr f_stmt
      val fld_t = fold_ctype diginto f_expr f_stmt
    in  
      case t of
        TypeOf e => fld e acc
      | Ptr t1 => fld_t t1 acc
      | Array (t1, NONE) => fld_t t1 acc
      | Array (t1, SOME e1) => fld_t t1 acc |> fld e1
      | Bitfield (t1, e1) => fld_t t1 acc |> fld e1
      | Function (t1, ts) => fld_t t1 acc |> fold fld_t ts
      | _ => acc
    end
  else acc
and fold_initializer diginto f_expr f_stmt i acc =
  let
    val fld = fold_expr diginto f_expr f_stmt
    val fld_i = fold_initializer diginto f_expr f_stmt
  in
    case i of
      InitE e1 => fld e1 acc
    | InitList is => fold fld_i (map snd is) acc
  end
and fold_stmt diginto f_expr f_stmt s acc0 =
  let
    val fld = fold_expr diginto f_expr f_stmt
    val fld_s = fold_stmt diginto f_expr f_stmt
    val fld_b = fold_block_item diginto f_expr f_stmt
    val acc = f_stmt s acc0
  in
    case snode s of
      Assign (e1, e2) => fld e1 acc |> fld e2
    | AssignFnCall (e1_opt, e2, es) => fold_option fld e1_opt acc |> fld e2 |> fold fld es
    | Chaos e1 => fld e1 acc
    | EmbFnCall (e1, e2, es) => fld e1 acc |> fld e2 |> fold fld es
    | Block (_, bs) => fold fld_b bs acc
    | LabeledStmt (_, s1) => fld_s s1 acc
    | While (e, _, s1) => fld e acc |> fld_s s1
    | Trap (_, s1) => fld_s s1 acc
    | Return e_opt => fold_option fld e_opt acc
    | ReturnFnCall (e1, es) => fld e1 acc |> fold fld es
    | Break => acc
    | Continue => acc
    | Goto _ => acc
    | IfStmt (e, s1, s2) => fld e acc |> fld_s s1 |> fld_s s2
    | Switch (e, cs) => fld e acc |> fold (fn (es_opt, bs) => fold (fold_option fld) es_opt #> fold fld_b bs) cs
    | EmptyStmt => acc
    | Auxupd _ => acc
    | Ghostupd _ => acc
    | Spec _ => acc
    | AsmStmt {asmblock={mod1, mod2,...}, ...} => fold fld (map #3 mod1) acc |> fold fld (map #3 mod2)
    | LocalInit e => fld e acc
    | AttributeStmt (_, s1) => fld_s s1 acc
    | ExprStmt e => fld e acc    
  end
and fold_block_item diginto f_expr f_stmt b acc =
  let
    val fld_s = fold_stmt diginto f_expr f_stmt
    val fld_d = fold_decl diginto f_expr f_stmt
  in
    case b of
      BI_Stmt s1 => fld_s s1 acc
    | BI_Decl d => fld_d (RegionExtras.node d) acc
  end
and fold_decl (diginto as {types}) f_expr f_stmt d acc =
  let
    open CType
    val fld = fold_expr diginto f_expr f_stmt
    val fld_t = fold_ctype diginto f_expr f_stmt
    val fld_i = fold_initializer diginto f_expr f_stmt
  in
    case d of
      VarDecl (t, _, _, NONE, _) => fld_t t acc
    | VarDecl (t, _, _, SOME i, _) => fld_t t acc |> fld_i i
    | StructDecl (_, flds, _) => fold fld_t (map #1 flds) acc
    | UnionDecl (_, variants, _) => fold fld_t (map #1 variants) acc
    | TypeDecl ts => fold fld_t (map #1 ts) acc
    | ExtFnDecl {rettype, params, ...} => fld_t rettype acc |> fold fld_t (map fst params)
    | EnumDecl (_, xs) => fold fld (map_filter I (map snd xs)) acc
  end

(* bottom up: f_expr / f_stmt applied on transformed arguments *)
fun fold_and_transform_expr (diginto as {types}) f_expr f_stmt e acc0 =
  let
    val fld = fold_and_transform_expr diginto f_expr f_stmt
    val fld_t = fold_and_transform_ctype diginto f_expr f_stmt
    val fld_i = fold_and_transform_initializer diginto f_expr f_stmt
    val fld_b = fold_and_transform_block_item diginto f_expr f_stmt
                     
    fun fld_option NONE acc = (NONE, acc)
      | fld_option (SOME x) acc = 
          let val (x', acc') = fld x acc
          in (SOME x', acc') end
  in
    case enode e of
      BinOp (bop, e1, e2) => 
        let 
          val (e1', acc1) = fld e1 acc0
          val (e2', acc2) = fld e2 acc1
          val e_new = ewrap (BinOp (bop, e1', e2'), eleft e, eright e)
        in f_expr e_new acc2 end
    | UnOp (uop, e1) =>  
        let 
          val (e1', acc1) = fld e1 acc0
          val e_new = ewrap (UnOp (uop, e1'), eleft e, eright e)
        in f_expr e_new acc1 end
    | PostOp (e1, pop) => 
        let 
          val (e1', acc1) = fld e1 acc0
          val e_new = ewrap (PostOp (e1', pop), eleft e, eright e)
        in f_expr e_new acc1 end
    | PreOp (e1, pop) => 
        let 
          val (e1', acc1) = fld e1 acc0
          val e_new = ewrap (PreOp (e1', pop), eleft e, eright e)
        in f_expr e_new acc1 end
    | CondExp (e1, e2, e3) => 
        let 
          val (e1', acc1) = fld e1 acc0
          val (e2', acc2) = fld e2 acc1
          val (e3', acc3) = fld e3 acc2
          val e_new = ewrap (CondExp (e1', e2', e3'), eleft e, eright e)
        in f_expr e_new acc3 end
    | Constant c => f_expr e acc0
    | Var v => f_expr e acc0
    | StructDot (e1, f) => 
        let 
          val (e1', acc1) = fld e1 acc0
          val e_new = ewrap (StructDot (e1', f), eleft e, eright e)
        in f_expr e_new acc1 end
    | ArrayDeref (e1, e2) => 
        let 
          val (e1', acc1) = fld e1 acc0
          val (e2', acc2) = fld e2 acc1
          val e_new = ewrap (ArrayDeref (e1', e2'), eleft e, eright e)
        in f_expr e_new acc2 end
    | Deref e1 => 
        let 
          val (e1', acc1) = fld e1 acc0
          val e_new = ewrap (Deref e1', eleft e, eright e)
        in f_expr e_new acc1 end
    | TypeCast (t, e1) => 
        let 
          val (t', acc1) = fld_t (RegionExtras.node t) acc0
          val (e1', acc2) = fld e1 acc1
          val t_new = RegionExtras.wrap (t', RegionExtras.left t, RegionExtras.right t) 
          val e_new = ewrap (TypeCast (t_new, e1'), eleft e, eright e)
        in f_expr e_new acc2 end
    | Sizeof e1 => 
        let 
          val (e1', acc1) = fld e1 acc0
          val e_new = ewrap (Sizeof e1', eleft e, eright e)
        in f_expr e_new acc1 end
    | SizeofTy t => 
        let 
          val (t', acc1) = fld_t (RegionExtras.node t) acc0
          val e_new = ewrap (SizeofTy (RegionExtras.wrap (t', RegionExtras.left t, RegionExtras.right t)), eleft e, eright e)
        in f_expr e_new acc1 end
    | EFnCall (attrs, e1, es) => 
        let 
          val (e1', acc1) = fld e1 acc0
          val (es', acc2) = fold_map fld es acc1
          val e_new = ewrap (EFnCall (attrs, e1', es'), eleft e, eright e)
        in f_expr e_new acc2 end
    | CompLiteral (t, is) => 
        let 
          val (t', acc1) = fld_t t acc0
          val (is', acc2) = fold_map fld_i (map snd is) acc1
          val is'' = map fst is ~~ is' 
          val e_new = ewrap (CompLiteral (t', is''), eleft e, eright e)
        in f_expr e_new acc2 end
    | Arbitrary t => 
        let 
          val (t', acc1) = fld_t t acc0
          val e_new = ewrap (Arbitrary t', eleft e, eright e)
        in f_expr e_new acc1 end
    | MKBOOL e1 => 
        let 
          val (e1', acc1) = fld e1 acc0
          val e_new = ewrap (MKBOOL e1', eleft e, eright e)
        in f_expr e_new acc1 end
    | OffsetOf (t, flds) => 
        let 
          val (t', acc1) = fld_t (RegionExtras.node t) acc0
          val t_new = RegionExtras.wrap (t', RegionExtras.left t, RegionExtras.right t)
          val e_new = ewrap (OffsetOf (t_new, flds), eleft e, eright e)
        in f_expr e_new acc1 end
    | AssignE (aop, e1, e2) => 
        let 
          val (e1', acc1) = fld e1 acc0
          val (e2', acc2) = fld e2 acc1
          val e_new = ewrap (AssignE (aop, e1', e2'), eleft e, eright e)
        in f_expr e_new acc2 end
    | StmtExpr (bl, e1) => 
        let 
          val (bl', acc1) = fold_map fld_b bl acc0
          val (e1', acc2) = fld_option e1 acc1
          val e_new = ewrap (StmtExpr (bl', e1'), eleft e, eright e)
        in f_expr e_new acc2 end
    | Comma (e1, e2) => 
        let 
          val (e1', acc1) = fld e1 acc0
          val (e2', acc2) = fld e2 acc1
          val e_new = ewrap (Comma (e1', e2'), eleft e, eright e)
        in f_expr e_new acc2 end
  end 
and fold_and_transform_ctype (diginto as {types}) f_expr f_stmt t acc =
  if types then
    let
      open CType
      val fld = fold_and_transform_expr diginto f_expr f_stmt
      val fld_t = fold_and_transform_ctype diginto f_expr f_stmt
      val fld_inttype = fold_and_transform_inttype diginto f_expr f_stmt
             
    in  
      case t of
        TypeOf e => 
          let val (e', acc') = fld e acc
          in (TypeOf e', acc') end
      | Ptr t1 => 
          let val (t1', acc') = fld_t t1 acc
          in (Ptr t1', acc') end
      | Array (t1, NONE) => 
          let val (t1', acc') = fld_t t1 acc
          in (Array (t1', NONE), acc') end
      | Array (t1, SOME e1) => 
          let 
            val (t1', acc1) = fld_t t1 acc
            val (e1', acc2) = fld e1 acc1
          in (Array (t1', SOME e1'), acc2) end
      | Bitfield (t1, e1) => 
          let 
            val (t1', acc1) = fld_t t1 acc
            val (e1', acc2) = fld e1 acc1
          in (Bitfield (t1', e1'), acc2) end
      | Function (t1, ts) => 
          let 
            val (t1', acc1) = fld_t t1 acc
            val (ts', acc2) = fold_map fld_t ts acc1
          in (Function (t1', ts'), acc2) end
      | Unsigned e =>
         let val (e', acc') = fld_inttype e acc
         in (Unsigned e', acc') end
      | Signed e =>
         let val (e', acc') = fld_inttype e acc
         in (Signed e', acc') end
      | _ => (t, acc)
    end
  else (t, acc)
and fold_and_transform_inttype (diginto as {types}) f_expr f_stmt t acc =
  let
     open BaseCTypes
     val fld = fold_and_transform_expr diginto f_expr f_stmt
  in
    case t of
      BitInt n => let val (n', acc') = fld n acc in (BitInt n', acc') end
    | _ => (t, acc)
  end
and fold_and_transform_initializer diginto f_expr f_stmt i acc =
  let
    val fld = fold_and_transform_expr diginto f_expr f_stmt
    val fld_i = fold_and_transform_initializer diginto f_expr f_stmt
  in
    case i of
      InitE e1 => 
        let val (e1', acc') = fld e1 acc
        in (InitE e1', acc') end
    | InitList is => 
        let val (is', acc') = fold_map fld_i (map snd is) acc
        in (InitList ((map fst is) ~~ is') , acc') end
  end
and fold_and_transform_stmt diginto f_expr f_stmt s acc0 =
  let
    val fld = fold_and_transform_expr diginto f_expr f_stmt
    val fld_s = fold_and_transform_stmt diginto f_expr f_stmt
    val fld_b = fold_and_transform_block_item diginto f_expr f_stmt
                                            
    fun fld_switch_case (es_opt, bs) acc =
      let
        val (es_opt', acc1) = fold_map (fold_map_option fld) es_opt acc
        val (bs', acc2) = fold_map fld_b bs acc1
      in ((es_opt', bs'), acc2) end
  in
    case snode s of
      Assign (e1, e2) => 
        let 
          val (e1', acc1) = fld e1 acc0
          val (e2', acc2) = fld e2 acc1
          val s_new = swrap (Assign (e1', e2'), sleft s, sright s)
        in f_stmt s_new acc2 end
    | AssignFnCall (e1_opt, e2, es) => 
        let 
          val (e1_opt', acc1) = fold_map_option fld e1_opt acc0
          val (e2', acc2) = fld e2 acc1
          val (es', acc3) = fold_map fld es acc2
          val s_new = swrap (AssignFnCall (e1_opt', e2', es'), sleft s, sright s)
        in f_stmt s_new acc3 end
    | Chaos e1 => 
        let 
          val (e1', acc1) = fld e1 acc0
          val s_new = swrap (Chaos e1', sleft s, sright s)
        in f_stmt s_new acc1 end
    | EmbFnCall (e1, e2, es) => 
        let 
          val (e1', acc1) = fld e1 acc0
          val (e2', acc2) = fld e2 acc1
          val (es', acc3) = fold_map fld es acc2
          val s_new = swrap (EmbFnCall (e1', e2', es'), sleft s, sright s)
        in f_stmt s_new acc3 end
    | Block (attrs, bs) => 
        let 
          val (bs', acc1) = fold_map fld_b bs acc0
          val s_new = swrap (Block (attrs, bs'), sleft s, sright s)
        in f_stmt s_new acc1 end
    | LabeledStmt (lbl, s1) => 
        let 
          val (s1', acc1) = fld_s s1 acc0
          val s_new = swrap (LabeledStmt (lbl, s1'), sleft s, sright s)
        in f_stmt s_new acc1 end
    | While (e, attrs, s1) => 
        let 
          val (e', acc1) = fld e acc0
          val (s1', acc2) = fld_s s1 acc1
          val s_new = swrap (While (e', attrs, s1'), sleft s, sright s)
        in f_stmt s_new acc2 end
    | Trap (trap, s1) => 
        let 
          val (s1', acc1) = fld_s s1 acc0
          val s_new = swrap (Trap (trap, s1'), sleft s, sright s)
        in f_stmt s_new acc1 end
    | Return e_opt => 
        let 
          val (e_opt', acc1) = fold_map_option fld e_opt acc0
          val s_new = swrap (Return e_opt', sleft s, sright s)
        in f_stmt s_new acc1 end
    | ReturnFnCall (e1, es) => 
        let 
          val (e1', acc1) = fld e1 acc0
          val (es', acc2) = fold_map fld es acc1
          val s_new = swrap (ReturnFnCall (e1', es'), sleft s, sright s)
        in f_stmt s_new acc2 end
    | Break => f_stmt s acc0
    | Continue => f_stmt s acc0
    | Goto lbl => f_stmt s acc0
    | IfStmt (e, s1, s2) => 
        let 
          val (e', acc1) = fld e acc0
          val (s1', acc2) = fld_s s1 acc1
          val (s2', acc3) = fld_s s2 acc2
          val s_new = swrap (IfStmt (e', s1', s2'), sleft s, sright s)
        in f_stmt s_new acc3 end
    | Switch (e, cs) => 
        let 
          val (e', acc1) = fld e acc0
          val (cs', acc2) = fold_map fld_switch_case cs acc1
          val s_new = swrap (Switch (e', cs'), sleft s, sright s)
        in f_stmt s_new acc2 end
    | EmptyStmt => f_stmt s acc0
    | Auxupd aux => f_stmt s acc0
    | Ghostupd ghost => f_stmt s acc0
    | Spec spec => f_stmt s acc0
    | AsmStmt {volatilep, asmblock={head, mod1, mod2, mod3}} => 
        let 
          val (mod1', acc1) = fold_map fld (map #3 mod1) acc0
          val (mod2', acc2) = fold_map fld (map #3 mod2) acc1
          val asmblock' = {head = head, 
            mod1 = map2 (fn (x,y,_) => fn z => (x, y, z)) mod1 mod1', 
            mod2 = map2 (fn (x,y,_) => fn z => (x, y, z)) mod2 mod2', 
            mod3 = mod3 }
          val s_new = swrap (AsmStmt {volatilep = volatilep, asmblock = asmblock'}, sleft s, sright s) 
        in f_stmt s_new acc2 end
    | LocalInit e => 
        let 
          val (e', acc1) = fld e acc0
          val s_new = swrap (LocalInit e', sleft s, sright s)
        in f_stmt s_new acc1 end
    | AttributeStmt (attrs, s1) => 
        let 
          val (s1', acc1) = fld_s s1 acc0
          val s_new = swrap (AttributeStmt (attrs, s1'), sleft s, sright s)
        in f_stmt s_new acc1 end
    | ExprStmt e => 
        let 
          val (e', acc1) = fld e acc0
          val s_new = swrap (ExprStmt e', sleft s, sright s)
        in f_stmt s_new acc1 end
  end
and fold_and_transform_block_item diginto f_expr f_stmt b acc =
  let
    val fld_s = fold_and_transform_stmt diginto f_expr f_stmt
    val fld_d = fold_and_transform_decl diginto f_expr f_stmt
  in
    case b of
      BI_Stmt s1 => 
        let val (s1', acc') = fld_s s1 acc
        in (BI_Stmt s1', acc') end
    | BI_Decl d => 
        let val (d', acc') = fld_d (RegionExtras.node d) acc
        in (BI_Decl (RegionExtras.wrap (d', RegionExtras.left d, RegionExtras.right d)), acc') end
  end
and fold_and_transform_decl (diginto as {types}) f_expr f_stmt d acc =
  let
    open CType
    val fld = fold_and_transform_expr diginto f_expr f_stmt
    val fld_t = fold_and_transform_ctype diginto f_expr f_stmt
    val fld_i = fold_and_transform_initializer diginto f_expr f_stmt
  in
    case d of
      VarDecl (t, name, attrs, NONE, spec) => 
        let val (t', acc') = fld_t t acc
        in (VarDecl (t', name, attrs, NONE, spec), acc') end
    | VarDecl (t, name, attrs, SOME i, spec) => 
        let 
          val (t', acc1) = fld_t t acc
          val (i', acc2) = fld_i i acc1
        in (VarDecl (t', name, attrs, SOME i', spec), acc2) end
    | StructDecl (name, flds, attrs) => 
        let 
          val (fld_types', acc') = fold_map fld_t (map #1 flds) acc
          val flds' = map2 (fn a => fn (_, x, y) =>  (a, x, y)) fld_types' flds
        in (StructDecl (name, flds', attrs), acc') end
    | UnionDecl (name, variants, attrs) => 
        let 
          val (variant_types', acc') = fold_map fld_t (map #1 variants) acc
          val variants' = map2 (fn a => fn (_, x, y) =>  (a, x, y))  variant_types' variants
        in (UnionDecl (name, variants', attrs), acc') end
    | TypeDecl ts => 
        let 
          val (ts_types', acc') = fold_map (fld_t) (map #1 ts) acc
          val ts' = map2 (fn a => fn (_, x, y) =>  (a, x, y)) ts_types' ts 
        in (TypeDecl ts', acc') end
    | ExtFnDecl {rettype, name, params, specs} => 
        let 
          val (rettype', acc1) = fld_t rettype acc
          val (param_types', acc2) = fold_map fld_t (map fst params) acc1
          val params' = param_types' ~~ map snd params
        in (ExtFnDecl {rettype=rettype', name=name, params=params', specs=specs}, acc2) end
    | EnumDecl (name, xs) => 
        let 
          val (xs', acc') = fold_map (fold_map_option fld) (map snd xs) acc
        in (EnumDecl (name, map fst xs ~~ xs'), acc') end
  end

fun fold_and_transform_ext_decl diginto f_expr f_stmt x acc =
  case x of
    FnDefn (x, y, z, body) => 
      let val (bs', acc') = fold_map (fold_and_transform_block_item diginto f_expr f_stmt) (RegionExtras.node body) acc
      in (FnDefn (x, y, z, RegionExtras.wrap (bs', RegionExtras.left body, RegionExtras.right body)), acc') end
  | Decl d => 
      let val (d', acc') = fold_and_transform_decl diginto f_expr f_stmt (RegionExtras.node d) acc
      in (Decl (RegionExtras.wrap (d', RegionExtras.left d, RegionExtras.right d)), acc') end

fun fold_and_transform_program diginto f_expr f_stmt = 
  fold_map (fold_and_transform_ext_decl diginto f_expr f_stmt)

      
@{record \<open>datatype variables = Variables of
 {global_vars: Symuset.T,
  heap_vars: bool}
\<close>};

fun variables_ord 
  (Variables {global_vars = g1, heap_vars = h1}, 
   Variables {global_vars = g2, heap_vars = h2}) =
  prod_ord Symuset.ord bool_ord ((g1, h1), (g2, h2))

val vars_empty = Variables {global_vars = Symuset.empty, heap_vars = false}

fun bool_is_empty false = true
  | bool_is_empty true = false

fun vars_is_empty (Variables {global_vars, heap_vars}) = 
  Symuset.is_empty global_vars andalso bool_is_empty heap_vars

@{record \<open>datatype dependencies = Dependencies of
  {read: variables, write: variables}\<close>};

fun dependencies_ord (Dependencies {read = r1, write = w1}, Dependencies {read = r2, write = w2}) =
  prod_ord variables_ord variables_ord ((r1, w1), (r2, w2))

val deps_empty = Dependencies {read = vars_empty, write = vars_empty}
fun deps_is_empty (Dependencies {read, write}) = vars_is_empty read andalso vars_is_empty write

fun bool_union _ true = true
  | bool_union true _ = true
  | bool_union _ _ = false

fun bool_inter _ false = false
  | bool_inter false _ = false
  | bool_inter _ _ = true

fun bool_insert b x = bool_union b x

fun vars_union 
  (Variables {global_vars = g1, heap_vars = h1}) 
  (Variables {global_vars = g2, heap_vars = h2}) =
  Variables { 
    global_vars = Symuset.union g1 g2, 
    heap_vars = bool_union h1 h2}

val prototype_default_vars = Variables {
  global_vars = Symuset.univ, 
  heap_vars = true}

fun vars_inter 
  (Variables {global_vars = g1, heap_vars = h1}) 
  (Variables {global_vars = g2, heap_vars = h2}) =
  Variables {
    global_vars = Symuset.inter g1 g2, 
    heap_vars = bool_inter h1 h2}

fun deps_union
  (Dependencies {read = r1, write = w1}) (Dependencies {read = r2, write = w2}) =
  Dependencies {read = vars_union r1 r2, write = vars_union w1 w2}

fun deps_inter
  (Dependencies {read = r1, write = w1}) (Dependencies {read = r2, write = w2}) =
  Dependencies {read = vars_inter r1 r2, write = vars_inter w1 w2}

fun deps_unions [] = deps_empty
  | deps_unions (x::xs) = deps_union x (deps_unions xs)

fun union_read_to_write (Dependencies {read, write}) =
  Dependencies {read = read, write = vars_union read write}

val prototype_pure_dependencies = deps_empty (* __attribute__(__const__) *)
val prototype_default_dependencies = Dependencies {
  read = prototype_default_vars, 
  write = prototype_default_vars}

(* __attribute__(__pure__) *)
val prototype_read_only_dependencies = Dependencies {
  read = prototype_default_vars,
  write = vars_empty
}

val phantom_machine_state = "phantom_machine_state"

val read_nothing_write_phantom_machine_state = prototype_pure_dependencies
  |> map_read (map_global_vars (K (Symuset.make [phantom_machine_state])))
  |> map_write (map_global_vars (K (Symuset.make [phantom_machine_state])))

val read_anything_write_phantom_machine_state = prototype_read_only_dependencies 
  |> map_write (map_global_vars (K (Symuset.make [phantom_machine_state])))

val read_phantom_machine_state_write_phantom_machine_state = prototype_pure_dependencies
  |> map_write (map_global_vars (K (Symuset.make [phantom_machine_state])))

val read_heap_and_phantom_machine_state_write_phantom_machine_state = prototype_read_only_dependencies
  |> map_read (map_global_vars (K (Symuset.make [phantom_machine_state])))
  |> map_write (map_global_vars (K (Symuset.make [phantom_machine_state])))

val read_heap_and_phantom_machine_state_write_heap_and_phantom_machine_state = prototype_default_dependencies
  |> map_read (map_global_vars (K (Symuset.make [phantom_machine_state])))
  |> map_write (map_global_vars (K (Symuset.make [phantom_machine_state])))


end

