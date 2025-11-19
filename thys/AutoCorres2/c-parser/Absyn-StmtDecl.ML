(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


signature STMT_DECL =
sig
  datatype gcc_attribute = datatype AstDatatype.gcc_attribute
  datatype storage_class = datatype AstDatatype.storage_class
  datatype fnspec = datatype AstDatatype.fnspec
  datatype declaration = datatype AstDatatype.declaration
  datatype trappable = datatype AstDatatype.trappable
  datatype statement_node = datatype AstDatatype.statement_node
  type statement
  type namedstringexp = string option * string * AstDatatype.expr

  type asmblock = {head : string,
                 mod1 : namedstringexp list,
                 mod2 : namedstringexp list,
                 mod3 : string list}

  datatype block_item = datatype AstDatatype.block_item
  datatype ext_decl = datatype AstDatatype.ext_decl

  val merge_specs : fnspec list -> fnspec list -> fnspec list
  val has_IDattribute : (string -> bool) -> fnspec list -> string option
  val all_IDattributes : fnspec list -> string Binaryset.set
  val get_owned_by : gcc_attribute list -> string option
  val fnspec2string : fnspec -> string

  val snode : statement -> statement_node
  val swrap : statement_node * SourcePos.t * SourcePos.t -> statement
  val sbogwrap : statement_node -> statement
  val block: statement list -> statement
  val sleft : statement -> SourcePos.t
  val sright : statement -> SourcePos.t

  val stmt_type : statement -> string

  val stmt_fail : statement * string -> exn

  val is_extern : storage_class list -> bool
  val is_static : storage_class list -> bool

  val sub_stmts : statement -> statement list
  val last_blockitem: block_item list -> block_item option
  val check_statement_expression_blockitems: Proof.context -> SourcePos.t -> SourcePos.t ->
        block_item list -> Expr.expr
  val pre_post_op_to_stmt: Proof.context -> Expr.expr -> AstDatatype.statement_node
  val check_rexpression_statement: Proof.context -> AstDatatype.expr -> AstDatatype.statement
end

structure StmtDecl : STMT_DECL =
struct

open AstDatatype RegionExtras Expr

fun attr2string (GCC_AttribID s) = s
  | attr2string (GCC_AttribFn(s, _)) = s ^ "(...)"
  | attr2string (OWNED_BY s) = "[OWNED_BY "^s^"]"

fun has_IDattribute P fspecs = let
  val search_gccattrs = get_first
                            (fn GCC_AttribID s => if P s then SOME s else NONE
                              | _ => NONE)
  fun oneP fspec =
      case fspec of
        gcc_attribs attrs => search_gccattrs attrs
      | _ => NONE
in
  get_first oneP fspecs
end

fun all_IDattributes fspecs = let
  fun getID (GCC_AttribID s) acc = Binaryset.add(acc,s) 
    | getID _ acc = acc
  fun getGCCs (gcc_attribs attrs) acc = acc |> fold getID attrs
    | getGCCs _ acc  = acc
in
  (Binaryset.empty string_ord) |> fold getGCCs fspecs
end

fun get_owned_by gattrs =
    case gattrs of
        [] => NONE
      | OWNED_BY s :: _ => SOME s
      | _ :: rest => get_owned_by rest



val commas = String.concat o separate ","
fun fnspec2string fs =
    case fs of
      fnspec s => "fnspec: "^node s
    | fn_modifies slist => "MODIFIES: "^String.concat (separate " " slist)
    | didnt_translate => "DONT_TRANSLATE"
    | gcc_attribs attrs => "__attribute__((" ^ commas (map attr2string attrs) ^
                           "))"
    | relspec s => "relspec: "^node s


fun collapse_mod_attribs sp = let
  local
    open Binaryset
  in
  fun IL (NONE, slist) = SOME (addList(empty string_ord, slist))
    | IL (SOME s, slist) = SOME (addList(s, slist))
  end
  fun recurse (acc as (mods, attribs, specs)) sp =
      case sp of
        [] => acc
      | s :: rest => let
        in
          case s of
            fn_modifies slist => recurse (IL (mods, slist), attribs, specs) rest
          | gcc_attribs gs => recurse (mods, Library.union op= gs attribs,
                                       specs)
                                      rest
          | _ => recurse (mods, attribs, s::specs) rest
        end
  val (mods, attribs, specs) = recurse (NONE, [], []) sp
  val mods = Option.map Binaryset.listItems mods
  val mods' = case mods of NONE => [] | SOME l => [fn_modifies l]
  val attribs' = case attribs of [] => [] | _ => [gcc_attribs attribs]
in
  mods' @ attribs' @ specs
end

fun merge_specs sp1 sp2 = collapse_mod_attribs (sp1 @ sp2)


val sleft = AstDatatype.sleft
val sright = AstDatatype.sright
val swrap = AstDatatype.swrap
val snode = AstDatatype.snode
fun sbogwrap s = Stmt(wrap(s,bogus,bogus))
fun block stmts =
  sbogwrap(Block (AstDatatype.Closed, map BI_Stmt stmts))

fun stmt_type s =
    case snode s of
      Assign _ => "Assign"
    | AssignFnCall _ => "AssignFnCall"
    | EmbFnCall _ => "EmbFnCall"
    | Block _ => "Block"
    | Chaos _ => "Chaos"
    | While _ => "While"
    | Trap _ => "Trap"
    | Return _ => "Return"
    | ReturnFnCall _ => "ReturnFnCall"
    | Break => "Break"
    | Continue => "Continue"
    | IfStmt _ => "IfStmt"
    | Switch _ => "Switch"
    | EmptyStmt => "EmptyStmt"
    | Auxupd _ => "Auxupd"
    | Spec _ => "Spec"
    | AsmStmt _ => "AsmStmt"
    | LocalInit _ => "LocalInit"
    | ExprStmt _ => "ExprStmt"
    | _ => "[whoa!  Unknown stmt type]"

fun map_concat f ss = map f ss |> List.concat

fun sub_stmts s =
    case snode s of
      Block (_, bis) => map_concat bi_stmts bis
    | While (_, _, s) => [s]
    | Trap (_, s) => [s]
    | IfStmt (_, l, r) => [l, r]
    | Switch (_, sws) => map_concat (map_concat bi_stmts o snd) sws
    | Spec (_, ss, _) => ss
    | _ => []
and bi_stmts (BI_Stmt s) = sub_stmts s
  | bi_stmts _ = []

fun stmt_fail (Stmt w, msg) =
    Fail (Region.toString (Region.Wrap.region w) ^ ": " ^ msg)

val is_extern = List.exists (fn x => x = SC_EXTERN)
val is_static = List.exists (fn x => x = SC_STATIC)

fun last_blockitem [] = NONE 
  | last_blockitem (bilist : block_item list) = 
  let
    val bi = List.last bilist
    fun recurse bi =
      case bi of
        BI_Stmt st => (case snode st of
                         Block (_, bilist) => last_blockitem bilist
                      | _ => SOME bi)
      | _ => SOME bi
   in
     recurse bi
   end

fun split_last_blockitem [] = NONE
  | split_last_blockitem (bl:block_item list) =
     let
        val (bl', last) = split_last bl
     in 
       case last of
         BI_Stmt st => 
          (case snode st of
             Block (_, bilist) => 
               (case split_last_blockitem bilist of
                 SOME (bl'', last') => SOME (bl'@bl'', last')
                | NONE => SOME (bl', last))
           | _ => SOME (bl', last))
       | _ => SOME (bl', last)
     end         
fun dest_nested_statement_expression ctxt e =
  case enode e of
    StmtExpr (bl, e_opt) => 
      let
        val (bl'', e'', bl_r) = case e_opt of SOME e' => dest_nested_statement_expression ctxt e' | _ => ([], NONE, eleft e)
      in
        (bl @ bl'', e'', bl_r)
      end
   | _ => ([], SOME e, eleft e)

fun check_statement_expression_blockitems ctxt l r bl = 
  let
    val msg1 = "expecting gcc-style expression-statement: compound statement where last statement is an expression"
  in
    case bl of 
      [] => Feedback.error_range ctxt l r msg1
    | _ => 
      let 
        val (bl', last) = the (split_last_blockitem bl)
        val (bl'', e_opt, bl''_r (* FIMXE: unused *)) = 
          case last of
            BI_Stmt st => 
              (case snode st of 
                 ExprStmt e => dest_nested_statement_expression ctxt e
               | AssignFnCall (NONE, e, es) => ([], SOME (ewrap (EFnCall(Statement, e, es), sleft st, sright st)), sleft st)
               | _ => ([last], NONE, sright st))
          | _ => Feedback.error_range ctxt l r msg1 
        val res = ewrap (StmtExpr (bl'@ bl'', e_opt), l, r)
      in res end
  end

val one_const = expr_int 1

fun pre_post_op_to_stmt ctxt e =
  (case enode e of
     PostOp (e, Plus_Plus) => Assign(e,ebogwrap(BinOp(Plus,e,one_const)))
   | PostOp (e, Minus_Minus) => Assign(e,ebogwrap(BinOp(Minus,e,one_const)))
   | PreOp (e, Plus_Plus) => Assign(e,ebogwrap(BinOp(Plus,e,one_const)))
   | PreOp (e, Minus_Minus) => Assign(e,ebogwrap(BinOp(Minus,e,one_const)))
   | _ =>  (Feedback.errorStr' ctxt (eleft e, eright e,
                      "Expecting ++ / -- here."); EmptyStmt))

fun check_rexpression_statement ctxt e =
  let
    val l = eleft e
    val r = eright e
    val expr_stmt = swrap (ExprStmt e, l, r)
  in
    case enode e of
      EFnCall(_, fn_e, args) => swrap(AssignFnCall(NONE, fn_e, args),l,r)
    | PostOp _ => swrap (pre_post_op_to_stmt ctxt e, l, r)
    | PreOp _ => swrap (pre_post_op_to_stmt ctxt e, l, r)
    | AssignE (_, e1, e2) => swrap (Assign (e1, e2), l, r)
    | StmtExpr (bl, NONE) => swrap (Block (AstDatatype.Closed, bl), l, r)
    | StmtExpr (bl, SOME e1) => 
         let
           val stmt' = check_rexpression_statement ctxt e1
           val bi = BI_Stmt stmt'
           val bl' = bl @ [bi]
         in swrap (Block (AstDatatype.Closed, bl'), l, r) end              
    | _ => expr_stmt
  end

end
