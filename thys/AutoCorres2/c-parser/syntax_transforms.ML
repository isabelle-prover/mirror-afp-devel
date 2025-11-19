(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature SYNTAX_TRANSFORMS =
sig
  type program = Absyn.ext_decl list
  val remove_typedefs : program -> program
  val anonymous_empty_fields: program -> program
  val remove_embedded_fncalls : Proof.context -> ProgramAnalysis.csenv -> program -> program
  val remove_anonstructs : Proof.context -> program -> program
  val nest_gotos: Proof.context -> program -> program
  val eval_static_builtins: Proof.context -> program -> program
end;


structure SyntaxTransforms : SYNTAX_TRANSFORMS =
struct

type program = Absyn.ext_decl list
open Absyn Basics

fun extend_env newbinds [] = [newbinds] (* shouldn't happen *)
  | extend_env newbinds (h::t) = (newbinds @ h) :: t

fun env_lookup(env, k) =
    case env of
      [] => NONE
    | e::es => (case AList.lookup (op =) e k of
                  NONE => env_lookup(es, k)
                | x => x)

fun map_attribute_expr f expr = 
  case expr of
    GCC_AttribFn (n, exprs) => GCC_AttribFn (n, map f exprs)
   | other => other  

fun ap1 f (a, b, c) = (f a, b, c)

fun map_triple f g h (a, b, c) = (f a, g b, h c)
fun map_triple_idx f g h (i, (a, b, c)) = (f i a, g i b, h i c)

fun typedef_attrs env ty =
  case ty of
     Ident s => (case env_lookup(env, s) of
                    NONE => raise Fail ("No typedef for "^s)
                  | SOME (ty,attrs) => node attrs)
  | Array (ty', _) => typedef_attrs env ty'
  | _ => []

fun update_type env (ty : Absyn.expr ctype) : Absyn.expr ctype =
    case ty of
      Ptr ty0 => Ptr (update_type env ty0)
    | Array (ty0, n) => Array(update_type env ty0,
                              Option.map (remove_expr_typedefs env) n)
    | Bitfield (ty0, n) => Bitfield (update_type env ty0, n)
    | Ident s => (case env_lookup(env, s) of
                    NONE => raise Fail ("No typedef for "^s)
                  | SOME (ty,attrs) => update_type env ty)
    | TypeOf e => TypeOf(remove_expr_typedefs env e)
    | Function (retT, argTs) => Function (update_type env retT, map (update_type env) argTs)
    | _ => ty
and remove_expr_typedefs env expr = let
  val ret = remove_expr_typedefs env
  val rit = remove_init_typedefs env
  val rdt = remove_designator_typedefs env
  val rst = remove_stmt_typedefs env
  val rbl = #2 o anonymous_empty_fields_body env
  val l = eleft expr
  val r = eright expr
  fun w en = ewrap (en, l, r)
  val updty = update_type env
  val updtyw = apnode updty
in
  case enode expr of
    BinOp(bop,e1,e2) => w(BinOp(bop, ret e1, ret e2))
  | UnOp(unop, e) => w(UnOp(unop, ret e))
  | PostOp(e, m) => w (PostOp(ret e, m))
  | CondExp(e1,e2,e3) => w(CondExp(ret e1, ret e2, ret e3))
  | StructDot(e,s) => w(StructDot(ret e, s))
  | ArrayDeref(e1, e2) => w(ArrayDeref(ret e1, ret e2))
  | Deref e => w(Deref (ret e))
  | TypeCast(ty,e) => w(TypeCast(updtyw ty, ret e))
  | Sizeof e => w(Sizeof (ret e))
  | SizeofTy ty => w(SizeofTy (updtyw ty))
  | EFnCall(origin,fnnm,elist) => w(EFnCall(origin,fnnm, map ret elist))
  | CompLiteral(ty, dis) =>
       w(CompLiteral(updty ty,
                     map (fn (ds,i) => (map rdt ds, rit i)) dis))
  | Arbitrary ty => w(Arbitrary (update_type env ty))
  | MKBOOL e => w (MKBOOL (ret e))
  | OffsetOf (ty, fld) => w(OffsetOf (updtyw ty, fld))
  | AssignE (origin, e1, e2) => w(AssignE(origin, ret e1, ret e2))
  | StmtExpr (bl, e) => w (StmtExpr(rbl bl, Option.map ret e))
  | _ => expr
end
and remove_init_typedefs env i = let
  val ret = remove_expr_typedefs env
  val rit = remove_init_typedefs env
  val rdt = remove_designator_typedefs env
in
  case i of
    InitE e => InitE (ret e)
  | InitList ilist => InitList (map (fn (ds,i) => (map rdt ds, rit i)) ilist)
end
and remove_designator_typedefs env d =
    case d of
      DesignE e => DesignE (remove_expr_typedefs env e)
    | DesignFld _ => d
and remove_stmt_typedefs env stmt = let
  val ret = remove_expr_typedefs env
  val rst = remove_stmt_typedefs env
  fun w st = swrap(st, sleft stmt, sright stmt)
in
  case snode stmt of
    Assign(e1, e2) => w(Assign(ret e1, ret e2))
  | AssignFnCall(fopt,s,args) => let 
      in w(AssignFnCall(Option.map ret fopt, ret s,
                                                map ret args)) end
  | Block (kind, b) => w(Block (kind, #2 (anonymous_empty_fields_body env b)))
  | Chaos e => w(Chaos(ret e))
  | While(g,sopt,body) => w(While(ret g, sopt, rst body))
  | Trap(tty,s) => w(Trap(tty, rst s))
  | Return eopt => w(Return (Option.map ret eopt))
  | ReturnFnCall (s,args) => w(ReturnFnCall(s,map ret args))
  | IfStmt(g,s1,s2) => w(IfStmt(ret g, rst s1, rst s2))
  | LabeledStmt(l,s1) =>w(LabeledStmt(l, rst s1))
  | Switch(g,bilist) => let
      val g' = ret g
      fun foldthis ((eoptlist, bilist), (env,acc)) = let
        val eoptlist' = map (Option.map ret) eoptlist
        val (env', bilist') = anonymous_empty_fields_body env bilist
      in
        (env', ((eoptlist',bilist') :: acc))
      end
      val (_, bilist') = List.foldr foldthis (env,[]) bilist
    in
      w(Switch(g',bilist'))
    end
  | EmptyStmt => stmt
  | Auxupd _ => stmt
  | Ghostupd _ => stmt
  | Spec _ => stmt
  | Break => stmt
  | Continue => stmt
  | Goto _ => stmt
  | AsmStmt _ => stmt
  | AttributeStmt(attrs,s1) =>w(AttributeStmt(attrs, rst s1))
  | ExprStmt e => w(ExprStmt(ret e))
  | _ => raise Fail ("remove_stmt_typedefs: unhandled type - "^stmt_type stmt)
end
and anonymous_empty_fields_body env bilist =
    case bilist of
      [] => (env, [])
    | BI_Stmt st :: rest => let
        val st' = BI_Stmt (remove_stmt_typedefs env st)
        val (env', rest') = anonymous_empty_fields_body env rest
      in
        (env', st' :: rest')
      end
    | BI_Decl d :: rest => let
        val (dopt, env') = remove_decl_typedefs env (node d)
        val (env'', rest') = anonymous_empty_fields_body env' rest
      in
        case dopt of
          NONE => (env'', rest')
        | SOME d' => (env'', BI_Decl (wrap(d',left d,right d)) :: rest')
      end
and remove_typedef_record_field env (typ, name, attrs) = 
  let
    val more_attrs = typedef_attrs env typ
  in
    (update_type env typ, name, (more_attrs @ (remove_attrs_typedefs env attrs)))
  end
and remove_decl_typedefs env d =
  case d of
    VarDecl (basety,name,is_extern,iopt,attrs) => let
    in
      (SOME (VarDecl (update_type env basety, name, is_extern,
                      Option.map (remove_init_typedefs env) iopt,
                      attrs)),
       env)
    end

  | StructDecl (sname, tys, attrs) =>    
      (SOME (StructDecl (sname, map (remove_typedef_record_field env) tys, 
         apnode (remove_attrs_typedefs env) attrs)), env) 
  | UnionDecl (sname, tys, attrs) =>
      (SOME (UnionDecl (sname,map (remove_typedef_record_field env) tys, 
         apnode (remove_attrs_typedefs env) attrs)), env)
  | TypeDecl tys => let
      val newrhs = map (fn (ty, nm, attrs) => (node nm, (update_type env ty, attrs))) tys
    in
      (NONE, extend_env newrhs env)
    end
  | ExtFnDecl {rettype, name, params, specs} => let
    in
      (SOME (ExtFnDecl{ rettype = update_type env rettype,
                        name = name,
                        params = map (apfst (update_type env)) params,
                        specs = specs}),
       env)
    end
  | EnumDecl (sw, ecs) => let
      fun ecmap (sw, eopt) = (sw, Option.map (remove_expr_typedefs env) eopt)
    in
      (SOME (EnumDecl (sw, map ecmap ecs)), env)
    end
and remove_attrs_typedefs env attrs =
  (map (map_attribute_expr (remove_expr_typedefs env))) attrs






val unsuffix_compound_record = ExpressionTyping.unsuffix_compound_record
val compound_record_name = ExpressionTyping.compound_record_name

val anonymous_field_names = map (node o #2) #> ExpressionTyping.anonymous_field_names
fun rename_field_name ns i x = apnode (K (nth ns i)) x



fun anonymous_empty_fields_decl env d =
  case d of
    StructDecl (sname, tys, attrs) =>
      let val names = anonymous_field_names tys in
      (SOME (StructDecl (sname, map_index (map_triple_idx (K I) (rename_field_name names) (K I)) tys, 
         attrs)), env) end
  | UnionDecl (sname, tys, attrs) =>
      let val names = anonymous_field_names tys in
      (SOME (UnionDecl (sname,map_index (map_triple_idx (K I) (rename_field_name names) (K I)) tys, 
          attrs)), env) end
  | _ => (SOME d, env)

val bogus = SourcePos.bogus






fun remove_typedefs p = let
  fun transform acc env p =
      case p of
        [] => List.rev acc
      | e::es => let
        in
          case e of
            Decl d => let
              val (dopt, env') = remove_decl_typedefs env (node d)
            in
              case dopt of
                NONE => transform acc env' es
              | SOME d' => transform (Decl (wrap (d',left d, right d))::acc)
                                     env' es
            end
          | FnDefn ((retty, s), params, prepost, body) => let
              val params' = map (apfst (update_type env)) params
              val retty' = update_type env retty
              val (_, body') = anonymous_empty_fields_body env (node body)
              val wbody = wrap(body', left body, right body)
              val newfn = FnDefn((retty', s), params', prepost, wbody)
            in
              transform (newfn :: acc) env es
            end
        end
  val p' = transform [] [] p
in
  p'
end


fun anonymous_empty_fields_stmt env stmt = let
  val ret = I
  val rst = anonymous_empty_fields_stmt env
  fun w st = swrap(st, sleft stmt, sright stmt)
in
  case snode stmt of
    Assign(e1, e2) => w(Assign(ret e1, ret e2))
  | AssignFnCall(fopt,s,args) => w(AssignFnCall(Option.map ret fopt, s,
                                                map ret args))
  | Block (kind, b) => w(Block (kind, #2 (anonymous_empty_fields_body env b)))
  | Chaos e => w(Chaos(ret e))
  | While(g,sopt,body) => w(While(ret g, sopt, rst body))
  | Trap(tty,s) => w(Trap(tty, rst s))
  | Return eopt => w(Return (Option.map ret eopt))
  | ReturnFnCall (s,args) => w(ReturnFnCall(s,map ret args))
  | IfStmt(g,s1,s2) => w(IfStmt(ret g, rst s1, rst s2))
  | LabeledStmt(l,s1) =>w(LabeledStmt(l, rst s1))
  | Switch(g,bilist) => let
      val g' = ret g
      fun foldthis ((eoptlist, bilist), (env,acc)) = let
        val eoptlist' = map (Option.map ret) eoptlist
        val (env', bilist') = anonymous_empty_fields_body env bilist
      in
        (env', ((eoptlist',bilist') :: acc))
      end
      val (_, bilist') = List.foldr foldthis (env,[]) bilist
    in
      w(Switch(g',bilist'))
    end
  | EmptyStmt => stmt
  | Auxupd _ => stmt
  | Ghostupd _ => stmt
  | Spec _ => stmt
  | Break => stmt
  | Continue => stmt
  | Goto _ => stmt
  | AsmStmt _ => stmt
  | AttributeStmt (attrs, s1) => w(AttributeStmt(attrs, rst s1))
  | ExprStmt e => w(ExprStmt (ret e))
  | _ => raise Fail ("anonymous_empty_fields_stmt: unhandled type - "^stmt_type stmt)
end
and anonymous_empty_fields_body env bilist =
    case bilist of
      [] => (env, [])
    | BI_Stmt st :: rest => let
        val st' = BI_Stmt (anonymous_empty_fields_stmt env st)
        val (env', rest') = anonymous_empty_fields_body env rest
      in
        (env', st' :: rest')
      end
    | BI_Decl d :: rest => let
        val (dopt, env') = anonymous_empty_fields_decl env (node d)
        val (env'', rest') = anonymous_empty_fields_body env' rest
      in
        case dopt of
          NONE => (env'', rest')
        | SOME d' => (env'', BI_Decl (wrap(d',left d,right d)) :: rest')
      end


fun anonymous_empty_fields p = let
  fun transform acc env p =
      case p of
        [] => List.rev acc
      | e::es => let
        in
          case e of
            Decl d => let
              val (dopt, env') = anonymous_empty_fields_decl env (node d)
            in
              case dopt of
                NONE => error ("anonymous_empty_fields: no result for: " ^ @{make_string} d) 
              | SOME d' => transform (Decl (wrap (d',left d, right d))::acc) env' es
            end
          | FnDefn ((retty, s), params, prepost, body) => let
              val params' = params
              val retty' = retty
              val (_, body') = anonymous_empty_fields_body env (node body)
              val wbody = wrap(body', left body, right body)
              val newfn = FnDefn((retty', s), params', prepost, wbody)
            in
              transform (newfn :: acc) env es
            end
        end
  val p' = transform [] [] p
in
  p'
end

(* set up little state-transformer monad *)
open NameGeneration

infix >> >-
fun (f >- g) m = let
  val (m',result) = f m
in
  g result m'
end
fun (f >> g) = f >- (fn _ => g)
fun return v m = (m,v)
fun peek m = (m, m)
fun map_state f m = (f m, ())

fun mmap f list =
    case list of
      [] => return []
    | h::t => f h >- (fn h' => mmap f t >- (fn t' => return (h'::t')))

fun new_var fname (ty,l,r) (embmap, pre_stmts, post_stmts) = let
  val rtype_n = tyname ty

  val temp_i = case Symtab.lookup embmap rtype_n of
                 NONE => 1
               | SOME i => i + 1
  val nm = tmp_var_name (rtype_n, temp_i)
  val mvinfo = MungedVar{munge = nm, owned_by = NONE, fname = SOME fname, init=true, kind=Local}
  val temp = ewrap(Var (MString.dest nm, Unsynchronized.ref (SOME (ty, mvinfo))), l, r)
  val emb' = Symtab.update (rtype_n, temp_i) embmap
in
  ((emb',pre_stmts, post_stmts), temp)
end


fun add_pre_stmts stmts (embmap,sts, post_sts) = ((embmap, sts @ stmts, post_sts), ())
fun add_pre_stmt st = add_pre_stmts [st]

fun new_call ctxt cse fname fn_e args (l,r) = let
  open ProgramAnalysis
  val (_, (rty, _)) = fndes_callinfo ctxt fname [] cse fn_e
in
  new_var fname (rty, eleft fn_e, eright fn_e) >- (fn temp =>
  add_pre_stmt (swrap(EmbFnCall(temp,fn_e,args), l, r)) >>
  return temp)
end

val bogus_empty = sbogwrap EmptyStmt


fun assign (v, e) = swrap(Assign(v,e), eleft e, eright e)
fun assign_bool (v, e) = swrap(Assign(v,ewrap(MKBOOL e, eleft e, eright e)), eleft e, eright e)

fun poscond v pre_stmts post_stmts =
    sbogwrap(IfStmt(v,block (pre_stmts @ post_stmts),bogus_empty))
fun negcond v pre_stmts post_stmts =
    sbogwrap(IfStmt(v,bogus_empty,block (pre_stmts @ post_stmts)))


fun mk_pre_post_op_assign (e, m) =
  let
    val l = eleft e
    val r = eright e
    val operation = case m of Plus_Plus => Plus | Minus_Minus => Minus
    val binop = ewrap (BinOp (operation, e, expr_int 1), l, r)
  in
    swrap (Assign (e, binop), l, r)
  end

fun set_pre_stmts stmts0 = map_state (fn (env, _, post_stmts) => (env, stmts0, post_stmts))
fun set_post_stmts stmts0 = map_state (fn (env, pre_stmts, _) => (env, pre_stmts, stmts0))

fun ex_remove_embfncalls ctxt cse fname e = let
  val doit = ex_remove_embfncalls ctxt cse fname
  fun w e0 = ewrap(e0,eleft e,eright e)
  val tempvar_if_postops = tempvar_if_postop ctxt cse fname
  fun one_tempvar_bool_op e =
    (* One temporary variable is enough to evaluate nested LogOr / LogAnd *)
    let
      fun lin_cond cond v e1 e2 = linearise v e1 >- (fn _ => peek >- (fn (_, pre_e1, post_e1) => 
             set_pre_stmts [] >> set_post_stmts [] >>
             linearise v e2 >- (fn _ => peek >- (fn (_, pre_e2, post_e2) =>
               set_pre_stmts (pre_e1 @ post_e1 @ [cond v pre_e2  post_e2]) >> 
               return v))))
      and linearise v e = 
         case enode e of
           BinOp(LogOr, e1, e2) => lin_cond negcond v e1 e2
         | BinOp(LogAnd, e1, e2) => lin_cond poscond v e1 e2
         | _ => doit e >- (fn e' => peek >- (fn (_, pre_sts, _) => 
             set_pre_stmts (pre_sts @ [assign_bool (v, e')]) >> 
             return v))
    in
      peek >- (fn (_, _, post_sts0) => set_post_stmts [] >>
      new_var fname (Signed Int, eleft e, eright e) >- (fn v =>
        linearise v e >> 
        set_post_stmts (post_sts0) >> 
        return v))
    end
in
  case enode e of
    BinOp(bop,e1,e2) => let
      val logical_op = 
        case bop of
          LogOr => true 
        |  LogAnd => true
        | _ => false
    in
      if logical_op andalso (has_post_effects ctxt e1 orelse eneeds_sc_protection e2) then
        one_tempvar_bool_op e
      else
        doit e1 >- (fn e1' =>
        doit e2 >- (fn e2' =>
        return (w(BinOp(bop,e1',e2')))))
    end
  | Comma (e1, e2) => 
    let
      val ty1 = ProgramAnalysis.cse_typing {report_error=true} ctxt cse e1
      val res = peek >- (fn (_, pre_sts0, post_sts0) => set_pre_stmts [] >> set_post_stmts [] >>
        doit e1 >- (fn e1' => peek >- (fn (_, pre_e1, post_e1) => set_pre_stmts [] >> set_post_stmts [] >>
        doit e2 >- (fn e2' => peek >- (fn (_, pre_e2, post_e2) =>
          new_var fname (ty1, eleft e1, eright e1) >- (fn v =>
          set_pre_stmts (pre_sts0 @ pre_e1 @ [assign (v, e1')] @ post_e1 @ pre_e2) >>
          set_post_stmts (post_sts0 @ post_e2) >>
          return e2'))))))
    in
      res
    end 
  | UnOp(uop,e) => doit e >- (fn e' => return (w(UnOp(uop, e'))))
  | PostOp(e, m) =>       
      doit e >- (fn e' => 
      map_state (fn (env, pre_stmts, post_stmts) => (env, pre_stmts, post_stmts @ [mk_pre_post_op_assign (e', m)])) >> 
      return e')
  | PreOp(e, m) => 
      doit e >- (fn e' => 
      map_state (fn (env, pre_stmts, post_stmts) => (env, pre_stmts @ [mk_pre_post_op_assign (e', m)], post_stmts)) >> 
      return e')
  | AssignE(_, e1, e2) =>
      doit e1 >- (fn e1' =>
      doit e2 >- (fn e2' =>
      map_state (fn (env, pre_stmts, post_stmts) => (env, pre_stmts @ [swrap (Assign (e1', e2'), eleft e, eright e)], post_stmts)) >>
      return e1'))
  | CondExp (g,t,e) => let
    in
      if  has_post_effects ctxt g orelse eneeds_sc_protection t orelse eneeds_sc_protection e then let
          val t_ty = ProgramAnalysis.cse_typing {report_error=true} ctxt cse t
          val e_ty = ProgramAnalysis.cse_typing {report_error=true} ctxt cse e
          val branch_type = unify_types(t_ty, e_ty)
              handle Fail _ => t_ty (* error will have already been reported
                                       in process_decls pass *)
          val sbw = sbogwrap

          fun create_if gsts post_gsts g' tsts post_tsts t' ests post_ests e' v = let
            val tbr = sbw(Block (AstDatatype.Closed, map BI_Stmt (post_gsts @ tsts @ [sbw(Assign(v,t'))] @ post_tsts)))
            val ebr = sbw(Block (AstDatatype.Closed, map BI_Stmt (post_gsts @ ests @ [sbw(Assign(v,e'))] @ post_ests)))
          in
            add_pre_stmts (gsts @ [sbw(IfStmt(g',tbr,ebr))]) >>
            return v
          end
          val new = peek >- (fn (_, pre_sts0, post_sts0) => set_pre_stmts [] >> 
               doit g >- (fn g' => peek >- (fn (_, gsts, post_gsts) => set_pre_stmts [] >> set_post_stmts [] >>
               doit t >- (fn t' => peek >- (fn (_, tsts, post_tsts) => set_pre_stmts [] >> set_post_stmts [] >>
               doit e >- (fn e' => peek >- (fn (_, ests, post_ests) => set_pre_stmts pre_sts0 >> set_post_stmts post_sts0 >>
               new_var fname (branch_type,eleft g,eright g) >- create_if gsts post_gsts g' tsts post_tsts t' ests post_ests e' )))))))
        in
          new
        end
      else
        doit g >- (fn g' =>
        doit t >- (fn t' =>
        doit e >- (fn e' =>
        return (w(CondExp (g',t',e'))))))
    end
  | Var _ => return e
  | Constant _ => return e
  | StructDot (e,fld) => doit e >- (fn e' => return (w(StructDot(e',fld))))
  | ArrayDeref(e1,e2) => doit e1 >- (fn e1' =>
                         doit e2 >- (fn e2' =>
                         return (w(ArrayDeref(e1',e2')))))
  | Deref e => doit e >- return o w o Deref
  | TypeCast(ty,e) => doit e >- (fn e' => return (w(TypeCast(ty,e'))))
  | Sizeof _ => return e
  | SizeofTy _ => return e
  | CompLiteral (ty,dis) => mmap (di_rm_efncalls ctxt cse fname) dis >- (fn dis' =>
                            return (w(CompLiteral(ty,dis'))))
  | EFnCall(origin, fn_e,args) => let
    in
      doit fn_e >- (fn fn_e' =>
      mmap tempvar_if_postops (args) >- (fn args' =>
      new_call ctxt cse fname fn_e' args' (eleft e, eright e) >- (fn temp => 
      return temp)))
    end
  | Arbitrary _ => return e
  | OffsetOf _ => return e
  | _ => Feedback.error_range ctxt (eleft e) (eright e) ("ex_remove_embfncalls: couldn't handle: " ^ expr_string e)
end
and i_rm_efncalls ctxt cse fname i =
    case i of
      InitE e => ex_remove_embfncalls ctxt cse fname e >- return o InitE
    | InitList dis => mmap (di_rm_efncalls ctxt cse fname) dis >- return o InitList
and di_rm_efncalls ctxt cse fname (d,i) = i_rm_efncalls ctxt cse fname i >- (fn i' => return (d,i'))
and tempvar_if_postop ctxt cse fname e = 
  let
    val doit = ex_remove_embfncalls ctxt cse fname
  in
    if has_post_effects ctxt e then 
      let
        val ty = ProgramAnalysis.cse_typing {report_error=true} ctxt cse e 
        val res = peek >- (fn (_, pre_sts0, post_sts0) => set_pre_stmts [] >> set_post_stmts [] >>
          doit e >- (fn e' => peek >- (fn (_, pre_e, post_e) =>
          new_var fname (ty, eleft e, eright e) >- (fn v =>
            set_pre_stmts (pre_sts0 @ pre_e @ [assign (v, e')] @ post_e) >>
            set_post_stmts (post_sts0) >>
            return v))))
      in res end 
    else doit e
  end
and expr_remove_embfncalls ctxt cse fname e = let
  val ((_, pre_sts, post_sts), e') = ex_remove_embfncalls ctxt cse fname e (Symtab.empty, [], [])
in
  (e', pre_sts, post_sts)
end

fun decl_remove_embfncalls _ (*cse*) d = (d, [])



                 
fun bitem_remove_embfncalls ctxt cse fname pre_stmts bi =
    case bi of
      BI_Decl dw => let
        val (d',sts) = decl_remove_embfncalls cse (node dw)
      in
        (map BI_Stmt (pre_stmts @ sts) @ [BI_Decl (wrap(d',left dw,right dw))])
      end
    | BI_Stmt st => map BI_Stmt (pre_stmts @ stmt_remove_embfncalls ctxt cse fname st)
and stmt_remove_embfncalls ctxt cse fname st = let
  val expr_remove_embfncalls = expr_remove_embfncalls ctxt cse fname
  val stmt_remove_embfncalls = stmt_remove_embfncalls ctxt cse fname
  fun w s = swrap(s,sleft st, sright st)
  val bog_empty = swrap(EmptyStmt,bogus,bogus)
  fun mk_single [] = bog_empty
    | mk_single [st] = st
    | mk_single rest = swrap(Block(AstDatatype.Closed, map BI_Stmt rest), sleft (hd rest),
                             sright (List.last rest))
in
  case snode st of
    Assign(e1,e2) => let
      val (e1',sts1, post_sts1) = expr_remove_embfncalls e1
      val (e2',sts2, post_sts2) = expr_remove_embfncalls e2
    in
      sts1 @ sts2 @ [w(Assign(e1',e2'))] @ post_sts1 @ post_sts2
    end
  | AssignFnCall(tgt,fnm,args) => let
      (* don't need to consider tgt as parser ensures this is always a simple
         object reference (field reference or variable) *)
      val ((_, pre_sts, post_sts), call) = (Symtab.empty, [], []) |> (
        ex_remove_embfncalls ctxt cse fname fnm >- (fn fnm' =>
        (* nested_fun_ptr_tmp_eval {report_error=true} ctxt cse fname >- (fn fnm' => *)
        mmap (tempvar_if_postop ctxt cse fname) args >-  
        (* mmap (nested_fun_ptr_tmp_eval {report_error=false} ctxt cse fname) >- *) (fn args'' => 
        return (w(AssignFnCall(tgt,fnm',args''))))))
    in
      pre_sts @ post_sts @ [call]
    end
  | Block (kind, bilist) =>
      [w(Block (kind, List.concat (map (bitem_remove_embfncalls ctxt cse fname []) bilist)))]
  | Chaos e =>
    let
      val (e',sts, post_sts) = expr_remove_embfncalls e
    in
      sts @ [w(Chaos e')] @ post_sts
    end
  | While(g0,spec,body) => let
      val g = g0
      val (g1, gsts, post_stmts) = expr_remove_embfncalls g
      val body' = stmt_remove_embfncalls body
    in
      (if null (gsts @ post_stmts) andalso length body' = 1 then
        [w(While(g1,spec,hd body'))]
      else
        let
          val res = gsts @ [w(While(g1,spec, swrap(Block (AstDatatype.Closed, map BI_Stmt (post_stmts @ body' @ gsts)),
                                       sleft body,
                                       sright body)))] @ post_stmts
        in res end)
      
    end
  | Trap(tty, s) => let
      val s' = stmt_remove_embfncalls s
    in
      [w(Trap(tty,mk_single s'))]
    end
  | Return (SOME e) => let
      val (e', sts, post_sts) = expr_remove_embfncalls e
    in
      sts @ [w(Return(SOME e'))] @ post_sts
    end
  | Return NONE => [st]
  | ReturnFnCall (fnm, args) => let
      val ((_, pre_sts, post_sts), call) = (Symtab.empty, [], []) |> (
        ex_remove_embfncalls ctxt cse fname fnm >- (fn fnm' => 
        (* nested_fun_ptr_tmp_eval {report_error=true} ctxt cse fname >- (fn fnm' => *)
        mmap (tempvar_if_postop ctxt cse fname) args >-  
        (* mmap (nested_fun_ptr_tmp_eval {report_error=false} ctxt cse fname) >- *) (fn args'' => 
        return (w(ReturnFnCall(fnm',args''))))))
    in
      pre_sts @ post_sts @ [call]
    end
  | Break => [st]
  | Continue => [st]
  | Goto _ => [st]
  | LabeledStmt(l,bdy) => let
      val bdy' = stmt_remove_embfncalls bdy
    in
      [w(LabeledStmt(l, mk_single bdy'))]
    end
  | IfStmt(g,tst,est) => let
      val (g',gsts, post_sts) = expr_remove_embfncalls g
      val tst' = stmt_remove_embfncalls tst
      val est' = stmt_remove_embfncalls est
    in
      gsts @ [w(IfStmt(g',mk_single (post_sts @ tst'), mk_single (post_sts @ est')))] 
    end
  | Switch(g,cases) => let
      val (g',gsts, post_sts) = expr_remove_embfncalls g
      fun mapthis (labs,bis) =
          (labs, List.concat (map (bitem_remove_embfncalls ctxt cse fname post_sts) bis))
    in
      gsts @ [w(Switch(g',map mapthis cases))] @ post_sts
    end
  | EmptyStmt => [st]
  | Auxupd _ => [st]
  | Ghostupd _ => [st]
  | Spec _ => [st]
  | AsmStmt _ => [st]
  | LocalInit _ => [st]
  | AttributeStmt(attrs,bdy) => let
      val bdy' = stmt_remove_embfncalls bdy
    in
      [w(AttributeStmt(attrs, mk_single bdy'))]
    end
  | ExprStmt e =>
      let 
        val (e', ests, post_sts) = expr_remove_embfncalls e
        val _ = check_pure_ground_expression ctxt e'
      in
        ests @ post_sts
      end
  | _ => raise Fail ("stmt_remove_embfncalls: Couldn't handle " ^ stmt_type st)
end

fun extdecl_remove_embfncalls ctxt cse e =
    case e of
      FnDefn ((retty,nm),params,spec,body) => let
        val body' = List.concat (map (bitem_remove_embfncalls ctxt cse (node nm) []) (node body))
      in
        FnDefn((retty,nm),params,spec,wrap(body',left body,right body))
      end
    | Decl d => let
        val (d', sts) = decl_remove_embfncalls cse d
      in
        if null sts then Decl d'
        else (!Feedback.warnf("Not handling initialisation of global \
                              \variables", NONE);
              Decl d')
      end

fun remove_embedded_fncalls ctxt cse = map (extdecl_remove_embfncalls ctxt cse)




fun unsuffix_compound' n = the_default n (unsuffix_compound_record n |> Option.map fst)


fun dest_compound_name name =
  unsuffix_compound_record name 
  |> Option.map (fn (name', union) => (space_explode "'" name', union))

fun subst_atomic_name th n =
  the_default n (Symtab.lookup th n)

fun subst_name th n =
  case dest_compound_name n of
    SOME (path, union) => compound_record_name {union=union} (map (unsuffix_compound' o subst_atomic_name th) path)
  | NONE => subst_atomic_name th n 

fun norm_name th n = 
  let val n' = subst_name th n
  in if n' = n then n' else norm_name th n' end

fun norm_theta th =
  Symtab.dest th |> map (fn (n, m) => (n, norm_name th m)) |> Symtab.make

fun tysubst th ty =
    case ty of
        StructTy s => StructTy (subst_name th s)
      |  UnionTy s => UnionTy (subst_name th s)
      | Ptr ty => Ptr (tysubst th ty)
      | Array (ty, sz) => Array (tysubst th ty, sz)
      | Function (retty, args) => Function (tysubst th retty,
                                            map (tysubst th) args)
      | _ => ty

fun ws th strw =
  let
    fun strf s = case Symtab.lookup th s of NONE => s | SOME s' => s'
  in
    apnode strf strw
  end

fun apfst' f (x, y, z) = (f x, y, z);

fun dsubst th d =
    case d of
        StructDecl (nmw, flds, attrs) => StructDecl (ws th nmw, map (ap1 (tysubst th)) flds, attrs)
      | UnionDecl (nmw, flds, attrs) => UnionDecl (ws th nmw, map (ap1 (tysubst th)) flds, attrs)
      | VarDecl(ty, nm, b, iopt, attrs) =>
          VarDecl(tysubst th ty, nm, b, iopt, attrs)
      | TypeDecl tnms => TypeDecl (map (apfst' (tysubst th)) tnms)
      | _ => d

fun map_decl f (BI_Decl d) = BI_Decl (f d)
  | map_decl f x = x
 
fun edsubst th ed =
    case ed of
        FnDefn (ret, args, specs, bdy) => FnDefn (ret, args, specs, apnode (map ((map_decl ((apnode (dsubst th)))))) bdy) 
      | Decl d => Decl (apnode (dsubst th) d)


fun paths_to_struct_or_union decls seen s = 
  if member (op =) seen s then [] else
  let
    fun struct_or_union_fld (StructTy n, nm, _) = SOME (node nm, n)  
      | struct_or_union_fld (UnionTy n, nm, _) = SOME (node nm, n)
      | struct_or_union_fld _ = NONE (* Do I have to expand typedefs? *)

    fun augment_path struct_name fld_name (intermediate_struct_name::xs) = struct_name::fld_name::xs
    fun fld_paths s1 flds = if s1 = s then [] else 
          let
            val xs = flds |> map_filter struct_or_union_fld |> map (fn (fld_name, s') =>
               if s' = s then [[s1, fld_name]] 
               else if member (op =) seen s' then [] else 
                 paths_to_struct_or_union decls (s1::s'::s::seen) s |> filter_out null |> map (augment_path s1 fld_name))  
               |> flat
          in xs end

    fun paths (StructDecl (nm, flds, _) ) = 
         fld_paths (node nm) flds
      | paths (UnionDecl (nm, flds, _)) = fld_paths (node nm) flds
      | paths _ = [] 
  in
    maps paths decls
  end


val legacy_anonymous_names = Attrib.setup_config_bool @{binding legacy_anonymous_names} (K false)

fun calctheta ctxt edecs edec acc =
  let
    val get_decls' = map_filter (fn BI_Decl dw => SOME (node dw) | _ => NONE)

    fun decl (FnDefn (ret, args, specs, bdy)) = get_decls' (node bdy)
      | decl (Decl x) = [node x]
    val decls = maps decl edecs
    val is_anonymous = String.isPrefix internalAnonStructPfx

    fun struct_or_union union nmw (acc as (i, th)) =              
      let
        val oldnm = node nmw
        open NameGeneration
      in
        if not (Symtab.defined th oldnm) andalso is_anonymous oldnm then
          if Config.get ctxt legacy_anonymous_names then
             (i + 1, Symtab.update (oldnm, mkAnonStructName {union=false} i) th)
          else
            case paths_to_struct_or_union decls [] oldnm of
              [path] => (i, Symtab.update (oldnm, compound_record_name {union=union} path) th)
            | _ => (i + 1, Symtab.update (oldnm, mkAnonStructName {union=union} i) th)

        else
          acc
      end

    fun add_type_def (ty, n, attrs) (acc as (i, th)) =
     let
       val tname = node n
     in
       case ty of 
         StructTy oldnm => if is_anonymous oldnm then (i, Symtab.update (oldnm, C_struct_name tname) th) else acc
       | UnionTy oldnm => if is_anonymous oldnm then (i, Symtab.update (oldnm, C_struct_name tname) th) else acc
       | _ => acc
     end

    fun add_decl dw acc = 
      (case node dw of
           StructDecl (nmw, _, _) => struct_or_union false nmw acc
         | UnionDecl (nmw, _, _) => struct_or_union true nmw acc
         | TypeDecl ts => acc |> fold add_type_def ts
         | _ => acc)

    val get_decls = map_filter (fn BI_Decl dw => SOME dw | _ => NONE)
  in  
    case edec of
        FnDefn (ret, args, specs, bdy) => acc |> fold add_decl (get_decls (node bdy)) 
      | Decl dw => add_decl dw acc
        
  end

fun remove_anonstructs ctxt edecs =
  let
    val (_, theta) = (1, Symtab.empty) |> fold (calctheta ctxt edecs) edecs
    val theta = norm_theta theta
    val edecs' = map (edsubst theta) edecs
  in
    edecs'
  end

fun add_goto_targets_stmt handled stmt labels =
  case snode stmt of
     Goto l => if member (op =) handled l then labels else l :: labels
   | LabeledStmt (l, stmt') => add_goto_targets_stmt (l::handled) stmt' labels
   | AttributeStmt (_, stmt') => add_goto_targets_stmt handled stmt' labels
   | While (_, _ , bdy) => add_goto_targets_stmt handled bdy labels 
   | Trap (_, stmt') => add_goto_targets_stmt handled stmt' labels
   | IfStmt (_, stmt1, stmt2) => add_goto_targets_stmt handled stmt2 (add_goto_targets_stmt handled stmt1 labels) 
   | Spec (_, stmts, _ ) => fold (add_goto_targets_stmt handled) stmts labels
   | Block (_, bis) => fold (add_goto_targets_block_item handled) bis labels
   | Switch (_, cases) => fold (add_goto_targets_block_item handled) (flat (map snd cases)) labels
   |  _ => labels
and 
    add_goto_targets_block_item handled bi labels =
  case bi of
    BI_Stmt stmt => add_goto_targets_stmt handled stmt labels
  | _ => labels

fun check_nesting_stmt ctxt handled stmt =
  let 
    fun error l = Feedback.error_region ctxt (Region.make{left = sleft stmt, right = sright stmt}) 
       ("invalid goto label '" ^ l ^ "'. \n" ^ 
        "Only block-structured nested gotos are supported")
  in
    case snode stmt of
       Goto l => if member (op =) handled l then true else (error l; false) 
     | LabeledStmt (l, stmt') => check_nesting_stmt ctxt (l::handled) stmt'
     | AttributeStmt (_, stmt') => check_nesting_stmt ctxt handled stmt'
     | While (_, _ , bdy) => check_nesting_stmt ctxt handled bdy  
     | Trap (_, stmt') => check_nesting_stmt ctxt handled stmt' 
     | IfStmt (_, stmt1, stmt2) => check_nesting_stmt ctxt handled stmt1 andalso check_nesting_stmt ctxt handled stmt2
     | Spec (_, stmts, _ ) => forall (check_nesting_stmt ctxt handled) stmts 
     | Block (_, bis) => forall (check_nesting_block_item ctxt handled) bis 
     | Switch (_, cases) => forall (check_nesting_block_item ctxt handled) (flat (map snd cases)) 
     |  _ => true 
  end
and 
    check_nesting_block_item ctxt handled bi  =
  case bi of
    BI_Stmt stmt => check_nesting_stmt ctxt handled stmt 
  | _ => true

fun get_toplevel_label stmt =
  case snode stmt of
     LabeledStmt (l, s) => SOME (l,s)
   |  _ => NONE

fun get_toplevel_label_block_item bi =
  case bi of
    BI_Stmt stmt => get_toplevel_label stmt
  | _ => NONE

fun append_hd x [] = [[x]]
  | append_hd x (xs::xss) = ((xs @ [x])::xss)

fun list_dest [] = ([], [])
  | list_dest (xs::xss) = (xs, xss)

fun bi_left [] = bogus
  | bi_left (BI_Stmt stmt::_) = sleft stmt
  | bi_left (BI_Decl decl::_) = left decl

fun bi_right [] = bogus
  | bi_right bs = case snd (split_last bs) of BI_Stmt stmt => sright stmt | BI_Decl decl => right decl

(* recursively apply a function to all nested block-item lists - bottom up *)
fun map_block_items_stmt f stmt =
  let
    fun w s = swrap(s, sleft stmt, sright stmt)
  in
    (case snode stmt of
       Block (kind, bis) => w (Block (kind, map_stmt_block_items f bis))
     | LabeledStmt (l, stmt') => w (LabeledStmt (l, map_block_items_stmt f stmt'))
     | AttributeStmt (attrs, stmt') => w (AttributeStmt (attrs, map_block_items_stmt f stmt'))
     | While (c, I, bdy) => w (While (c, I, map_block_items_stmt f bdy))
     | Trap (t, stmt') => w (Trap (t, map_block_items_stmt f stmt'))
     | IfStmt (c, stmt1, stmt2) => w (IfStmt (c, map_block_items_stmt f stmt1, map_block_items_stmt f stmt2))
     | Switch (e, cases) => w (Switch (e, map (fn (c, bis) => (c, map_stmt_block_items f bis)) cases))
     | Spec (x, stmts, y) => w (Spec (x, map (map_block_items_stmt f) stmts, y)) 
     | _ => stmt)
  end
and map_stmt_block_items f bis =
  let
    val bis' = map (fn BI_Stmt stmt => BI_Stmt (map_block_items_stmt f stmt) | d => d) bis
  in f bis' end

fun nest_labeled_block_items' nested gotos bis = 
  case bis of
    [] => nested
  | BI_Decl d::bis' => 
     if null gotos 
     then nest_labeled_block_items' ([BI_Decl d]::nested) gotos bis'
     else nest_labeled_block_items' (append_hd (BI_Decl d) nested) gotos bis'
  | BI_Stmt stmt::bis' =>
     let
       val fresh_gotos = add_goto_targets_stmt [] stmt []
       val new_gotos = fresh_gotos @ gotos
     in
       if null gotos
       then nest_labeled_block_items' ([BI_Stmt stmt]::nested) new_gotos bis'
       else 
         (case get_toplevel_label stmt of
            NONE => nest_labeled_block_items' (append_hd (BI_Stmt stmt) nested) new_gotos bis'
          | SOME (l, stmt') =>  
            let 
              val (blk, blks) = list_dest nested
              val gotos' = filter_out (fn n => n = l) new_gotos
              val new_blk = LabeledStmt (l, swrap (Block (AstDatatype.Closed, blk), bi_left blk, bi_right blk))
            in 
              nest_labeled_block_items' 
                ([BI_Stmt (swrap (new_blk, bi_left blk, sleft stmt')), BI_Stmt stmt']::blks) 
                gotos' bis' 
            end)           
     end

fun toplevel_nest_labeled_block_items ctxt bis = 
  flat (rev (nest_labeled_block_items' [] [] bis))

fun nest_labeled_block_items ctxt bis = 
  let 
    val result = map_stmt_block_items (toplevel_nest_labeled_block_items ctxt) bis
    val _ = forall (check_nesting_block_item ctxt []) result
  in result end

fun nest_gotos ctxt = map 
  (fn FnDefn (ret, params, prepost, body) => 
    let
       val bdy' = nest_labeled_block_items ctxt (node body)
    in FnDefn (ret, params, prepost, wrap (bdy', left body, right body)) end
   | d => d) 
 

fun dest_fun_name e =
  case enode e of Var (n, _) => SOME (NameGeneration.rmUScoreSafety n)
     | _ => NONE

val empty_ecenv = AstDatatype.CE 
  {enumenv = Symtab.empty,
   typing = fn _ => error "empty typing",
   structsize = fn _ => error "empty structsize",
   offset_of = fn _ => fn _ => error "empty offset_of"
   };


val builtin_constant_p_constant_only = Attrib.setup_config_bool @{binding "c_parser_builtin_constant_p_constant_only"} (K true)


fun eval_builtins ctxt f args =
  dest_fun_name f |> Option.mapPartial (fn n =>
    case n of
      "__builtin_choose_expr" => 
        (case args of 
          [c, x, y] => try (consteval false ctxt empty_ecenv) c |> Option.map (fn n =>
               if n = 0 then y else x)
         | _ => NONE)
    | "__builtin_constant_p" => 
        (case args of 
          [x] => (case try (consteval false ctxt empty_ecenv) x of 
                   SOME _ => SOME (expr_int' (eleft f) (eright x) 1)
                  | _ => if Config.get ctxt builtin_constant_p_constant_only then 
                           Feedback.error_range ctxt (eleft f) (eright x) 
                             ("__builtin_constant_p did not evalute to true. Maybe consider option c_parser_builtin_constant_p_constant_only=false")
                         else 
                           SOME (expr_int' (eleft f) (eright x) 0))
         | _ => NONE)
    | _ => NONE)

fun eval_static_builtins ctxt program = 
  let
    
    fun f_expr e () = 
      case enode e of 
        EFnCall (_, f, args)  => 
          let
          in 
            case eval_builtins ctxt f args of 
              SOME e' => (e', ())
            | NONE => (e, ())
          end
      | _ => (e, ())
    fun f_stmt s () =
      case snode s of
        AssignFnCall (SOME lval, f, args) =>
          let
          in 
            case eval_builtins ctxt f args of 
              SOME e' => (swrap (Assign (lval, e'), sleft s, sright s), ())
            | NONE => (s, ()) 
          end
      | _ => (s, ())
   
  in
    AstDatatype.fold_and_transform_program {types=true} f_expr f_stmt program () |> fst
  end
 
end (* struct *)
