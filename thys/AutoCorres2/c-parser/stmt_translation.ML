(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

structure ASM_Ignore_Hooks = struct

structure Data = Generic_Data
(
  type T = (int * (ProgramAnalysis.asm_stmt_elements -> bool)) list
  val empty = []
  val merge = Ord_List.merge (int_ord o apply2 fst)
)

fun add_hook hk = Data.map (Ord_List.insert (int_ord o apply2 fst)
    (serial (), hk))

fun ignore' nm = exists (fn (_, f) => f nm) o Data.get

fun ignore_thy nm thy = ignore' nm (Context.Theory thy)
fun ignore nm ctxt = ignore' nm (Context.Proof ctxt)

end

structure stmt_translation =
struct

open ExpressionTranslation TermsTypes Absyn Basics
open ExpressionTyping



fun might_raise trap s =
    case snode s of
      While (_, _, b) => might_raise trap b
    | IfStmt(_, s1, s2) => might_raise trap s1 orelse might_raise trap s2
    | Switch(_, cases) =>
        List.exists (List.exists (bi_might_raise trap) o #2) cases
    | Block bis => List.exists (bi_might_raise trap) bis
    | Trap(trap', s) => trap <> trap' andalso might_raise trap s
    | Spec(_, slist, _) => List.exists (might_raise trap) slist
    | Break => trap = BreakT
    | Continue => trap = ContinueT
    | _ => false
and bi_might_raise trap (BI_Stmt s) = might_raise trap s
  | bi_might_raise _ (BI_Decl _) = false

fun map_locals ctxt statety locty varname ty =
  let
    val thy = Proof_Context.theory_of ctxt
    val locupd = #upd (CalculateState.get_locals_data statety locty thy)
    val map = CLocals.mk_update ctxt varname $ Bound 0
  in
    Abs ("upd", ty--> ty,  locupd $ map)
  end


fun update_locals ctxt statety locty varname new_value  =
  if varname = NameGeneration.global_exn_var_name
  then
    let
      val thy = Proof_Context.theory_of ctxt
      val upd = #upd (CalculateState.get_global_exn_var_data statety thy)
    in
      upd $ new_value
    end
  else
    let
      val thy = Proof_Context.theory_of ctxt
      val locupd = #upd (CalculateState.get_locals_data statety locty thy)
      val upd = CLocals.mk_update ctxt varname $ new_value
    in
      locupd $ upd
    end

fun update_positional ctxt statety locty ty pos new_value =
  let
    val thy = Proof_Context.theory_of ctxt
    val locupd = #upd (CalculateState.get_locals_data statety locty thy)
    val upd = CLocals.mk_update_positional ty pos $ new_value
  in
    locupd $ upd
  end

fun gen_update_locals ctxt statety locty (NameGeneration.Positional (pos, ty)) new_value =
      update_positional ctxt statety locty ty pos new_value
  | gen_update_locals ctxt statety locty (NameGeneration.Named name) new_value =
      update_locals ctxt statety locty name new_value



fun var_updator ctxt globty locty k_upd (name, ty, cty, vsort) newvalue state =
  let
    val thy = Proof_Context.theory_of ctxt
    open CalculateState NameGeneration
    val statety = type_of state
    val newvalue' = if k_upd then K_rec ty $ newvalue else newvalue
  in
    case vsort of
      Local _ =>
        if name = NameGeneration.global_exn_var
        then
          Const (Sign.intern_const thy ("CProof.state." ^ suffix Record.updateN name),
            ((ty --> ty) --> statety --> statety)) $ newvalue' $ state
        else
          update_locals ctxt statety locty name newvalue' $ state

    | NSGlobal =>
        let
          val fullname =
            Sign.intern_const thy (global_rcd_name ^ "." ^ suffix Record.updateN name)
          val glob_update =
              Sign.intern_const thy (suffix Record.updateN "globals")
          val globupd_t = #upd (get_globals_data statety globty thy)
          val fldupd = Const(fullname, (ty --> ty) --> (globty --> globty))
        in
          globupd_t $ (fldupd $ newvalue') $ state
        end
    | AddressedGlobal => raise Fail "var_updator: shouldn't be called on addressed global"
    | UntouchedGlobal => raise Fail "var_updator: shouldn't be called on untouched global"
  end


fun lookup_locals ctxt statety locty name state =
  let
    val lookup_var = CLocals.mk_lookup ctxt name
    val thy = Proof_Context.theory_of ctxt
    val loc_t = #acc (CalculateState.get_locals_data statety locty thy)
  in lookup_var $ (loc_t $ state) end

fun lookup_positional ctxt statety locty ty pos state =
  let
    val lookup_var = CLocals.mk_lookup_positional ty pos
    val thy = Proof_Context.theory_of ctxt
    val loc_t = #acc (CalculateState.get_locals_data statety locty thy)
  in lookup_var $ (loc_t $ state) end

fun gen_lookup_locals ctxt statety locty (NameGeneration.Positional (pos, ty)) state =
      lookup_positional ctxt statety locty ty pos state
  | gen_lookup_locals ctxt statety locty (NameGeneration.Named name) state =
      lookup_locals ctxt statety locty name state

fun lookup_locals_fun ctxt statety locty name =
  let
    val s = Free("s___", statety)
  in
    Abs ("s", statety, abstract_over (s, lookup_locals ctxt statety locty name s))
  end

fun var_accessor ctxt globty locty (name, ty, _ (*cty *), vsort) state =
  let
    val thy = Proof_Context.theory_of ctxt
    open CalculateState NameGeneration
  in
    case vsort of
      Local _ =>
        if name = NameGeneration.global_exn_var
        then
          Const (Sign.intern_const thy ("CProof.state." ^ name), (type_of state) --> ty) $ state
        else
          lookup_locals ctxt (type_of state) locty name state
    | NSGlobal =>
        let
          val glob_t = #acc (get_globals_data (type_of state) globty thy)
        in
          Const(Sign.intern_const thy (global_rcd_name ^ "." ^ name),
                globty --> ty) $
          (glob_t $ state)
        end
    | AddressedGlobal => raise Fail "var_updator: shouldn't be called on addressed global"
    | UntouchedGlobal => raise Fail "var_updator: shouldn't be called on untouched global"
  end


fun mk_callresult_exn ctxt globty locty statety =
  let
    val svar = Free("s", statety)
    val tvar = Free("t", statety)
    val exn_var_data = (NameGeneration.global_exn_var, c_exntype_ty, true, (* unused parameter *)
                       CalculateState.Local ("cparser'internal", false))
    val exn_updator = var_updator ctxt globty locty true exn_var_data
    val exn_accessor = var_accessor ctxt globty locty exn_var_data
    val exn_prj = c_Nonlocal $ (c_the_Nonlocal $ (exn_accessor tvar))
  in
    mk_abs(svar, mk_abs(tvar, exn_updator exn_prj svar))
  end

fun mk_callreturn_norm thy globty statety =
  let
    val svar = Free("s", statety)
    val tvar = Free("t", statety)
    val gupdate = Const(suffix Record.updateN "StateSpace.state.globals",
                        (globty --> globty) --> (statety --> statety))
    val gaccess = Const(@{const_name "StateSpace.state.globals"},
                        statety --> globty)
    val Kupd = K_rec globty $ (gaccess $ tvar)
  in
    mk_abs(svar, mk_abs(tvar, gupdate $ Kupd $ svar))
  end

val single_id = (hd, [("", TermsTypes.bool)])

fun trans_list styargs [] = mk_skip_t styargs
  | trans_list _ stmts = list_mk_seq stmts

fun bilist2stmts [] = []
  | bilist2stmts (BI_Stmt st :: rest) = st :: bilist2stmts rest
  | bilist2stmts (BI_Decl _ :: rest) = bilist2stmts rest

fun calc_asm_params styargs statety globty thy = let
  open CalculateState
  val gs = get_standard_globals statety globty thy
  val ((ghost_acc, _), _) = #ghost gs
  val ((ms_acc, _), _) = #phantom gs
  val ((hp_acc, _), _) = #hp gs
  val gdata_acc = Abs ("s", domain_type (fastype_of ghost_acc),
    HOLogic.mk_prod (ghost_acc $ Bound 0,
        @{term "hrs_htd"} $ (hp_acc $ Bound 0)))
  val msT = range_type (fastype_of ms_acc)
in
  (msT, gdata_acc)
end

fun calc_asm_spec styargs statety globty thy vol spec lval rvals = let
  val (msT, gdata_acc) = calc_asm_params styargs statety globty thy
  val res = mk_asm_spec styargs msT gdata_acc vol spec lval rvals
in
  res
end

fun calc_asm_semantics_ok_to_ignore styargs statety globty thy vol spec = let
  val (msT, _) = calc_asm_params styargs statety globty thy
in
  mk_asm_ok_to_ignore msT vol spec
end

fun mk_init_var ctxt styargs locty ty name =
  let
    val name = name
    val statetype = hd styargs
    val upd_ty = (ty --> ty) --> statetype --> statetype
    val vupd_t = map_locals ctxt statetype locty name ty
    val com_t = Const(@{const_name "lvar_nondet_init"},
                         upd_ty --> mk_com_ty styargs)
  in
    com_t $ vupd_t
  end

fun mk_With_Fresh_Stack_Ptr ctxt n init c =
let
  val base = @{const_name "stack_heap_state.With_Fresh_Stack_Ptr"} |> Long_Name.base_name
      |> Long_Name.qualify NameGeneration.state_rcd_name
  val With_Fresh_Stack_Ptr = Syntax.read_term ctxt base |> Utils.dummy
in
 With_Fresh_Stack_Ptr $ n $ init $ c |> Utils.infer_types_simple ctxt
end

fun get_info fninfo name =
  the (List.find (fn r => #fname r = name) fninfo)
  handle Option => error("No function information for " ^ name)


(* called so that parsing of invariants etc can be done in a context where
   Isabelle variables corresponding to global variable pointers (x_addr, for example)
   get the right type *)
fun lookup_addr_vars state = let
  fun foldthis ({varname,fnname}, (realnm,ty,cty,vsort)) acc =
      case fnname of
        NONE => Symtab.update
                    (NameGeneration.global_addr (MString.dest varname), mk_ptr_ty ty)
                    acc
      | SOME _ => acc
in
  CNameTab.fold foldthis state Symtab.empty
end

fun read_annotation ctxt (state : CalculateState.mungedb) (str, T)  =
  let
    val raw_term = Syntax.parse_term ctxt str
    val typetable = lookup_addr_vars state
    val theta = []
      |> Symtab.fold (fn (vnm,ty) => fn acc => (Free(vnm, dummyT), Free(vnm, ty)) :: acc) typetable
    val eq = Const(@{const_name "HOL.eq"}, dummyT) $ subst_free theta raw_term $ mk_arbitrary T
    val (_ $ x $ _) = Syntax.check_term ctxt eq
  in
    x
  end

fun dest_init_var cse e =
  case enode e of
    Var(x, Unsynchronized.ref extra) => extra |> Option.mapPartial (fn (_, MungedVar vinfo) =>
      ProgramAnalysis.get_local_info cse (#munge vinfo, #fname vinfo)
      |> Option.map (fn loc_info => (#init vinfo, x,  loc_info)))
    | _ => NONE


fun stmt_term (ctxt : Proof.context)
              (cse : ProgramAnalysis.csenv)
              (state : CalculateState.mungedb)
              (fname : string)
              (termbuilders : varinfo termbuilder)
              (varinfo : MString.t -> varinfo option)
              (fninfo : HPInter.fninfo list)
              (statetype : Term.typ)
              (globty : Term.typ)
              (locty : Term.typ)
              (styargs : Term.typ list)
              (memsafe : bool)
              (skip_asm : bool)
              (stmts : Absyn.statement list) : term =
  case stmts of
    [] => mk_skip_t styargs
  | (stmt::stmts) =>

  let
    val stmt_term =
        stmt_term ctxt cse state fname termbuilders varinfo fninfo
                  statetype globty locty styargs memsafe skip_asm
    val thy = Proof_Context.theory_of ctxt
    val filename = Config.get_global thy HP_TermsTypes.current_C_filename
    val prog_name = HP_TermsTypes.get_program_name ctxt
    val region = Region.make{left = sleft stmt, right = sright stmt}
    val error = fn s => Feedback.error_region ctxt region (": " ^ s)
    val this_fn_info = get_info fninfo fname
    val expr_term = expr_term ctxt cse termbuilders varinfo
    val emptystmt = mk_skip_t styargs
    val svar = Free("s", statetype)
    val exn_var_data =  (NameGeneration.global_exn_var, c_exntype_ty,
                         true, (* unused parameter *)
                         CalculateState.Local ("cparser'internal", false))
    fun exn_assign value = let
    val updator = var_updator ctxt globty locty true exn_var_data
    in
      mk_basic_t styargs $ (mk_abs(svar, updator value svar))
    end
    val exn_accessor = var_accessor ctxt globty locty exn_var_data
    fun wrap_cont_on_loop body_tm = let (* handles Continue "exception" *)
      val condition =
          mk_collect_t statetype $
                       mk_abs(svar, mk_eqt(exn_accessor svar, Continue_exn))
      val check_continue =
          mk_cond_t styargs $ condition $ emptystmt $
                    mk_throw_t styargs
    in
      mk_catch_t styargs $ body_tm $ check_continue
    end
    fun wrap_break_on_loop loop_tm = let
      val check_break = mk_ccatchbrk thy styargs statetype
    in
      mk_catch_t styargs $ loop_tm $ check_break
    end
    fun guard_it (gds : (term -> term * term) list) (com : term) : term = let
      fun foldthis (f,com) = let
        val (gcond, gtype) = f svar
        val gcond_set = mk_collect_t statetype $ mk_abs(svar, gcond)
      in
        mk_guard gcond_set gtype com
      end
    in
      List.foldr foldthis com gds
    end
    fun implicit_cast_rval (cty : int ctype) (e : Absyn.expr) : expr_info = let
        val e_info = array_decay ctxt (strip_kb (expr_term e))
        val e_cty  = ctype_of e_info
    in
        if cty = e_cty then e_info
        else if assignment_compatible (cty,e_cty,e) then
            typecast(ctxt, cty, e_info)

        else error ("Can't assign from type "^tyname e_cty^" to type "^
                    tyname cty)
    end
    val read_annotation = read_annotation ctxt state

    fun seq_rest stmt = if null stmts then stmt else list_mk_seq [stmt, stmt_term stmts]
  in
    case snode stmt of
      Block bilist => stmt_term (bilist2stmts bilist) |> seq_rest

    | LabeledStmt (l, stmt') =>
        let
          val stmt' = stmt_term [stmt']
        in
          mk_catch_t styargs $ stmt' $ mk_ccatchgoto thy styargs statetype l
          |> seq_rest
        end
    | Assign(e1, e2) => let
        val e1_info = expr_term e1
        val e1_cty = ctype_of e1_info
        val (e1_lval, e1_rval) = (the (lval_of e1_info), rval_of e1_info)
            handle Option => error "No lvalue for lhs of assignment"
        val e2' =
            (* if the lvar on the left is of array type, assume that this is an
               initialisation of an array, rather than an attempt to do an
               illegal assignment to an array object.  Could enforce by having
               two Assign forms in the statement type, but for now just rely
               on having a C compiler check code for well-formedness *)
            case e1_cty of
              Array _ => expr_term e2
            | _ => implicit_cast_rval e1_cty e2

      in
        case dest_init_var cse e1 of
           SOME (true, x, {kind = NameGeneration.Loc, addressed = true, ...}) =>
             let
               val xty = CalculateState.ctype_to_typ ctxt e1_cty
               val init = mk_abs(svar, HOLogic.mk_set \<^Type>\<open>list xty\<close> [HOLogic.mk_list xty [rval_of e2' svar]])
               val x_ptr = TermsTypes.mk_local_ptr (x, xty)
               val c = stmt_term stmts |> Term.absfree (dest_Free x_ptr)
               val t = mk_With_Fresh_Stack_Ptr ctxt @{term "1::nat"} init c
               val gds = guards_of e2'
             in
               guard_it gds t
             end
        | _ =>
          let
            val gds = guards_of e1_info @ guards_of e2' @
                  (if memsafe then lguards_of e1_info else [])
           in
             guard_it gds
               (mk_basic_t styargs $ mk_abs(svar, e1_lval (rval_of e2' svar) svar))
             |> seq_rest
           end
      end

    | LocalInit v_e => let
        open TermsTypes
        val vinfo =
            case enode v_e of
              Var(nm, Unsynchronized.ref extra) => let
              in
                case extra of
                  SOME (_, MungedVar mvi) => mvi
                | _ => error "Confused by lack of variable info"
              end
            | _ => error "Bad variable being initialised"
        val einfo = expr_term v_e
        val ety = CalculateState.ctype_to_typ ctxt (ctype_of einfo)
        val loc_info = ProgramAnalysis.get_local_info cse (#munge vinfo, #fname vinfo)
      in
        case (#init vinfo, loc_info) of
          (true, SOME {kind = NameGeneration.Loc, addressed = true, ...}) =>
            let
              val x = MString.dest (#munge vinfo)
              val init = \<^instantiate>\<open>'s = statetype and 'a = ety in term \<open>\<lambda>s::'s. UNIV::'a list set\<close>\<close>
              val x_ptr = TermsTypes.mk_local_ptr (x, ety)
              val c = stmt_term stmts |> Term.absfree (dest_Free x_ptr)
              val t = mk_With_Fresh_Stack_Ptr ctxt @{term "1::nat"} init c
            in
              t
            end
        | (true, SOME {kind = NameGeneration.In i, addressed = true, ...}) =>
            let
              val x = MString.dest (#munge vinfo)
              val init = mk_abs(svar,
                           (HOLogic.mk_set \<^Type>\<open>list \<open>ety\<close>\<close> [HOLogic.mk_list ety [lookup_locals ctxt (type_of svar) locty x svar]]))
              val x_ptr = TermsTypes.mk_local_ptr (x, ety)
              val c = stmt_term stmts |> Term.absfree (dest_Free x_ptr)
              val t = mk_With_Fresh_Stack_Ptr ctxt @{term "1::nat"} init c

            in
              t
            end
        | _ => mk_init_var ctxt styargs locty ety (MString.dest (#munge vinfo)) |> seq_rest
      end
    | Auxupd r => let
        open MemoryModelExtras
        val hrs = (NameGeneration.global_heap_var,
                   extended_heap_ty,
                   NONE, (* no corresponding C type *)
                   CalculateState.NSGlobal)
        fun upd r_tm =
            mk_abs(svar,
                   var_updator ctxt globty locty false hrs (mk_aux_update (r_tm $ svar))
                               svar)
        fun gcond_set r_tm =
            mk_collect_t statetype $ mk_abs(svar, mk_aux_guard (r_tm $ svar))

        val r_tm = read_annotation (NameGeneration.apt_string r, mk_aux_type statetype)
      in
        mk_guard (gcond_set r_tm) safety_error (mk_basic_t styargs $ upd r_tm)
        |> seq_rest
      end
    | Ghostupd s => let
        open MemoryModelExtras
        val ghostty = case CalculateState.get_ghostty thy filename of
                        NONE => raise Fail ("No ghosttype data for "^filename)
                      | SOME typ => typ
        val ghostvar = (NameGeneration.global_var NameGeneration.ghost_state_name,
                        ghostty,
                        NONE,
                        CalculateState.NSGlobal)
        val stype = mk_prod_ty (bool,ghostty --> ghostty)
        val fst = Const(@{const_name "fst"}, stype --> bool)
        val snd = Const(@{const_name "snd"}, stype --> ghostty --> ghostty)
        fun upd t = mk_abs(svar,
                           var_updator ctxt globty locty false ghostvar (snd $ (t $ svar)) svar)

        fun guard t =
            mk_collect_t statetype $ mk_abs(svar, fst $ (t $ svar))

        val t = read_annotation (NameGeneration.apt_string s, statetype --> stype)

      in
        mk_guard (guard t) @{const "GhostStateError"} (mk_basic_t styargs $ upd t)
        |> seq_rest
      end

    | EmptyStmt => emptystmt |> seq_rest

    | Trap(trappable, stmt) => let
        val stmt' = stmt_term [stmt]
        val wrap0 = case trappable of BreakT => wrap_break_on_loop
                                    | ContinueT => wrap_cont_on_loop
        val wrap = if might_raise trappable stmt then wrap0 else (fn x => x)
      in
        wrap stmt'
        |> seq_rest
      end
    | While(guard,inv,body) => let
        val guard' = mk_isabool ctxt (expr_term guard)
        val guard_val = rval_of guard'
        val guard_guards = guards_of guard'
        val guard_tm = mk_collect_t statetype $ mk_abs(svar, guard_val svar)
        val var_tm =
            mk_arbitrary (mk_set_type (mk_prod_ty(statetype, statetype)))
        val body_f = stmt_term [body]
        fun mkloop body_tm inv_tm = let
          val body' = if null guard_guards then body_tm
                      else list_mk_seq [body_tm, guard_it guard_guards emptystmt]
          val base = mk_while_t styargs $ guard_tm $ inv_tm $ var_tm $ body'
        in
          guard_it guard_guards base
        end
      in
        case inv of
          NONE => let
            val inv_tm = mk_empty_INV statetype
          in
            mkloop (body_f) inv_tm |> seq_rest
          end
        | SOME s => let
            val inv_tm = read_annotation (node s, mk_set_type statetype)
          in
             mkloop (body_f ) inv_tm |> seq_rest
          end
      end
    | IfStmt(guard,thenbr,elsebr) => let
        val guard_ei = mk_isabool ctxt (expr_term guard)
        val guard_val = rval_of guard_ei
        val then_tm = stmt_term [thenbr]
        val else_tm = stmt_term [elsebr]
      in
        guard_it (guards_of guard_ei)
                   (mk_cond_t styargs $
                              (mk_collect_t statetype $
                                            mk_abs(svar, guard_val svar)) $
                              then_tm $
                              else_tm)
        |> seq_rest
      end
    | Return (SOME e) => let
        val (retvar_name, retvar_ty, retvar_cty, _) = (hd (#outparams this_fn_info))
            handle Empty =>
                   error ("No return parameter for function "^fname)
        val retvar = map_locals ctxt statetype locty retvar_name retvar_ty
        val e'     = implicit_cast_rval retvar_cty e
        val value  = mk_abs (svar, rval_of e' svar) (* Is svar safe? *)
      in
        guard_it (guards_of e')
          (mk_creturn thy styargs statetype retvar value)
        |> seq_rest
      end

    | Return NONE =>
        mk_creturn_void thy styargs statetype |> seq_rest
    | ReturnFnCall (s, args) => let
        val (retvar_name, _, cretty, _) =
            hd (#outparams this_fn_info)
            handle Empty => error ("No return parameter for function "^fname)
        val mvi = MungedVar {munge = MString.mk retvar_name, owned_by = NONE, fname=SOME fname, init=false}
        val retvar =
            ewrap (Var (retvar_name, Unsynchronized.ref (SOME (cretty, mvi))),
                   eleft s,
                   eright s)
        val retvar_assign =
              stmt_term [(swrap(AssignFnCall(SOME retvar, s, args),
                                        sleft stmt, sright stmt))]
        val return_t =
              stmt_term [(swrap(Return (SOME retvar),
                                         sleft stmt, sright stmt))]
      in
        list_mk_seq [retvar_assign, return_t]
        |> seq_rest
      end

    | Break => mk_cbreak thy styargs statetype |> seq_rest
    | Continue => let
        val exn_assign = exn_assign Continue_exn
      in
        list_mk_seq [exn_assign, mk_throw_t styargs] |> seq_rest
      end
    | Goto l => mk_cgoto thy styargs statetype l |> seq_rest

    | EmbFnCall(lval,callname,args) => let
      in
        stmt_term [(swrap (AssignFnCall(SOME lval, callname, args),
                          sleft stmt,
                          sright stmt))] |> seq_rest
      end
    | AssignFnCall(lvalopt, call_e, args) => (case Option.mapPartial (dest_init_var cse) lvalopt of
        SOME (true, x, {kind = NameGeneration.Loc, addressed = true, info = vinfo}) =>
          let
            val xty = CalculateState.ctype_to_typ ctxt (ProgramAnalysis.get_vtype vinfo)
            val init = \<^instantiate>\<open>'s = statetype and 'a = xty in term \<open>\<lambda>s::'s. UNIV::'a list set\<close>\<close>
            val x_ptr = TermsTypes.mk_local_ptr (x, xty)
            val lvalopt_initialised = lvalopt |>
                 (Option.map o map_enode o map_var o apsnd o ExprDatatype.map_more_info o map_munged_var o map_init)
                   (K false)
            val stmt' = stmt |> StmtDeclDatatype.map_snode (K (AssignFnCall(lvalopt_initialised, call_e, args)))
            val c = stmt_term (stmt':: stmts) |> Term.absfree (dest_Free x_ptr)
            val t = mk_With_Fresh_Stack_Ptr ctxt @{term "1::nat"} init c
          in
            t
          end
      | _ =>
       let
        open ProgramAnalysis
        fun mk_param (s,ty,cty) =
          (0, (s, ty, cty, false))

        fun ret_opt [] = NONE
          | ret_opt (r::_) = SOME r

        val (HP_call_t, fndes_t, informals, outname_info_opt, callname, callgds, direct) =
            case fndes_callinfo ctxt cse call_e of
              (DirectCall callname, _) =>
                if callname = NameGeneration.exitN
                then (Bound 0, Bound 0, [mk_param HP_TermsTypes.c_exit_status_info], NONE, callname, [], true)
                else
                  let
                    val (ins, outopt) =
                      case List.find (fn {fname,...} => fname = callname) fninfo of
                        NONE => error ("Unknown function: " ^ callname)
                      | SOME r => HPfninfo.positional_params r |> apsnd ret_opt

              in
                (mk_call_t styargs,
                 mk_VCGfn_name ctxt callname,
                 ins,
                 outopt,
                 callname,
                 [],
                 true)
              end

            | (FnPtrCall((rty, argTs), _, _), _) => let
                val call_ei = expr_term call_e
                open NameGeneration
                val naming = Const (Sign.intern_const thy naming_scheme_name,
                      procT --> mk_option_ty string_ty)
                val pbody = rval_of call_ei svar
                val (ins, outs) = HPInter.params_of_fun_type ctxt (CType.Ptr (CType.Function (rty, argTs)))
                                |> HPfninfo.positional
                val outopt = ret_opt outs
                fun ptr_guard s = let
                  val fptr_val = rval_of call_ei s
                in
                  (@{const "c_fnptr_guard"} $ fptr_val,
                    c_guard_error)
                end
                fun mk_guard f =
                  let
                    val (pred, kind) = f svar
                  in
                    mk_collect_t statetype $ mk_abs(svar, pred)
                  end
              in
                (mk_dyncall_t styargs (map mk_guard (ptr_guard :: guards_of call_ei)),
                 mk_abs(svar, pbody), ins, outopt,
                 "fn. ptr", [], false)
              end
        (* call's arguments are:
            1. initialisation (copying actual parameters to formals)
            2. name of procedure to call (a string in all likelihood)
            3. a return modification function where the first argument is the
               very original state, and the next one is the final state that is
               going to be modified.
            4. the continuation, if you like: what to do after returning.
               Gets the same parameters as 3 gets.
               Doesn't get called with exception returns.  Will get called
               in a third state again, that pertaining after 3 has been
               applied.
        *)
        (* first step is to match up actuals to formals *)
        val actuals = map (fn e => (array_decay ctxt (strip_kb (expr_term e)), e)) args
        val gds = List.concat (map (fn (ei,_) => guards_of ei) actuals) @
                  callgds


        val callee_ctxt = HPInter.enter_scope prog_name callname ctxt
        fun param_to_lval (param_pos, (param_name, ipty, pty, _)) ((actual_info, actuale), st) = let
          val actual_cty = ctype_of actual_info
          val coerced_value =
              if actual_cty = pty then actual_info
              else if assignment_compatible(pty, actual_cty, actuale) then
                typecast(ctxt,pty,actual_info)
              else
                error ("Actual parameter's type: "^tyname actual_cty^
                       " is not compatible with formal parameter's type: "^
                       tyname pty)
          val v = rval_of coerced_value svar
          val rv = if callname = NameGeneration.exitN
            then Const (@{const_name Nonlocal}, @{typ exit_status} --> ipty) $ v
            else v
          val Kupd = K_rec ipty $ rv
          val loc_ref = if direct then NameGeneration.Named param_name
                        else NameGeneration.Positional (param_pos, ipty)
        in
          gen_update_locals callee_ctxt statetype locty loc_ref Kupd $ st
        end

        val formal_fs = map param_to_lval informals
        val _ = if length formal_fs <> length actuals then
                  error("Number of arguments ("
                        ^Int.toString (length actuals)^
                        ") in call to "^callname^
                        " doesn't match declarations ("
                        ^Int.toString (length formal_fs)^")")
                else ()
        fun mkinit formals actuals =
            case (formals, actuals) of
              ([], []) => svar
            | (f::fs, ac::acs) => f (ac, mkinit fs acs)
            | _ => raise Fail "Catastrophic invariant failure XXX"
        val init = mk_abs(svar, mkinit (List.rev formal_fs) (List.rev actuals))
        val return = mk_callreturn_norm thy globty statetype
        val result_exn = mk_callresult_exn ctxt globty locty statetype
        val result = let
          val tvar = Free("t", statetype)
        in
          case lvalopt of
            NONE => let
              val skip_equivalent =
                  mk_basic_t styargs $ mk_abs(svar, svar)
            in
              mk_abs(svar, mk_abs(tvar, skip_equivalent))
            end
          | SOME e => let
              val lhs_ei = expr_term e
              val lhs_cty = ctype_of lhs_ei
              val outlval = the (lval_of lhs_ei)
                  handle Option => error "Assigning function call to non-lvalue"
              val (out_pos, (out_name, out_typ, out_ctyp, _)) = the outname_info_opt
                  handle Option =>
                         error ("Using return value from void function "^
                                callname)

              val out_ref = if direct then NameGeneration.Named out_name else NameGeneration.Positional (out_pos, out_typ)
              fun outrval0 st = gen_lookup_locals callee_ctxt statetype locty out_ref st

              val out_einfo = mk_rval(outrval0, out_ctyp, false, sleft stmt,
                                      sright stmt)
              val outrval =
                  if lhs_cty = out_ctyp then outrval0
                  else if assignment_compatible(lhs_cty, out_ctyp,
                                                (* expression is irrelevant *)
                                                ewrap(Arbitrary (Signed Int),
                                                      SourcePos.bogus,
                                                      SourcePos.bogus))
                  then
                    rval_of (typecast(ctxt,lhs_cty,out_einfo))
                  else
                    error("Return type of function "^callname^
                          " not compatible with value assigned to")
              val uvar = Free("u", statetype)
            in
              mk_abs(svar,
                     mk_abs(tvar,
                            mk_basic_t styargs $
                                 mk_abs(uvar, outlval (outrval tvar) uvar)))
            end
        end
        val call = if callname = NameGeneration.exitN
         then
           let
             val exit = mk_exit_t styargs $ init
           in exit end
         else (HP_call_t $ init $ fndes_t $ return $ result_exn $ result)
      in
        guard_it gds call |> seq_rest
      end)

    | Spec((prevar, pre), body, post) => let
        val body_tm = stmt_term body
        fun mk_abs_string s = "\<lambda> "^prevar^" . (" ^ s ^")"
        val pre_tm = read_annotation (mk_abs_string pre, statetype --> mk_set_type statetype)
        val post_tm = read_annotation (mk_abs_string post, statetype --> mk_set_type statetype)
      in
          mk_specAnno pre_tm (Abs(prevar, statetype, body_tm)) post_tm |> seq_rest
      end

    | Switch (testexp, cases) => let
        (* "The integer promotions are performed on the controlling expression." *)

        val e = intprom_ei ctxt (expr_term testexp)
        val testexp_t = ctype_of e
        val e_rv = rval_of e
        val test_body = e_rv svar
        val gty = type_of test_body
        val e_test = mk_abs(svar, test_body)
        fun mk_case (labs : expr option list, bilist : block_item list) = let
          val s_r = stmt_term (bilist2stmts bilist)
          val lab_t : term = let
            fun foldthis lab acc : term = let
              (* "The constant expression in each case label is converted to the
               * promoted type of the controlling expression." *)
              val e = typecast (ctxt, testexp_t, expr_term (the lab))
              val e_t = rval_of e svar
            in
              mk_insert(e_t,acc)
            end
          in
            if labs = [NONE] then mk_UNIV gty
            else (mk_empty gty) |> fold foldthis labs
          end
        in
          (lab_t, s_r)
        end
        val case_results0 : (term * term) list = map mk_case cases
        val case_ts = map mk_pair case_results0
      in
          mk_switch (e_test, HOLogic.mk_list (type_of (hd case_ts)) case_ts)
          |> guard_it (guards_of e)
          |> seq_rest
      end

    | Chaos expr =>
      let
        val ei = expr_term expr
        val lv = the (lval_of ei)
                 handle Option => error ("Value (" ^ expr_string expr ^
                                         ") without l-value passed to Chaos")
        val cty = ctype_of ei
        val v = Free("v", CalculateState.ctype_to_typ ctxt cty)
        val f = list_mk_abs([v,svar], lv v svar)
      in
        Const(@{const_name "cchaos"}, type_of f --> mk_com_ty styargs) $ f
        |> seq_rest
      end
    | AsmStmt st =>
      (let
        (* fixme: is this correct for all arches? *)
        val reg_cty = Unsigned ImplementationNumbers.ptr_t;
        val (nm, vol, ret, args) = ProgramAnalysis.split_asm_stmt (AsmStmt st)
        val _ = if ASM_Ignore_Hooks.ignore_thy (nm, vol, ret, args) thy
          then raise Fail "hook fired" else ()
        val ret = case ret of NONE => (fn x => (fn s => s))
          | SOME r => the (lval_of (expr_term r))
              handle Option => error ("Value (" ^ expr_string r
                  ^ ") without l-value used as asm stmt lval specifier.")
        val x = Free ("x", addr_ty)
        val ret = mk_abs (x, mk_abs (svar, ret x svar))
        fun conv_arg arg = mk_abs (svar, rval_of (typecast
              (ctxt, reg_cty, expr_term arg)) svar)
          handle Option => error ("Value (" ^ expr_string arg
                  ^ ") without r-value used as asm stmt rval specifier.")
        val args = map conv_arg args
      in
        if skip_asm then
          mk_skip_t styargs |> seq_rest
        else
          calc_asm_spec styargs statetype globty thy
              (#volatilep st) nm ret args |> seq_rest
      end handle Fail str => let
        val nm = #head (#asmblock st)
        val ok = calc_asm_semantics_ok_to_ignore styargs statetype globty thy
              (#volatilep st) nm
        val err = unspecified_syntax_error2 str
        val guard = mk_collect_t statetype
              $ mk_abs (svar, HOLogic.mk_disj (ok, err))
      in
        mk_guard guard unspecified_syntax_error1 emptystmt
        |> seq_rest
      end)
    | _ => error ("Can not yet handle "^stmt_type stmt^" statement forms")
  end

fun lookup_fld alist (s, f) =
    case AList.lookup (op =) alist s of
      NONE => error ("No struct information for type "^s)
    | SOME (flds, sattrs) => let
      in
        case List.find (fn (fldname, ty, cty, attrs) => fldname = f) flds  of
          NONE => error ("No type information for field "^f^" in struct "^s)
        | SOME (_, ty, _, _) => ty
      end

fun rcd_accessor thy cse rcdinfo (sname, fldname) rcdterm =
  case CalculateState.union_variant {non_canonical=true} thy cse (sname, fldname) of 
    NONE => (* ordinary structure or single variant union or canonical union variant *)
      let
        val fullname = Sign.intern_const thy (sname ^ "." ^ fldname)
        val fldty = lookup_fld rcdinfo (sname, fldname)
      in
        Const(fullname, type_of rcdterm --> fldty) $ rcdterm
      end
  | SOME (union_ty, variant_ty, field_ty) => (* non-canonical union variants *)
      let
        val coerce = \<^Const>\<open>coerce union_ty variant_ty\<close>
        val (variant_ty_name, _) = dest_Type variant_ty
        val sel_name = Sign.intern_const thy (variant_ty_name ^ "." ^ fldname)
        val sel = Const(sel_name, variant_ty --> field_ty)
      in 
        sel $ (coerce $ rcdterm)
      end 

fun rcd_updator thy cse (sname, fldname) newvalue rcdterm =
  case CalculateState.union_variant {non_canonical=true} thy cse (sname, fldname) of
    NONE => (* ordinary structure or single variant union or canonical union variant *)
      let
        val fullname =
            Sign.intern_const thy (sname ^ "." ^ suffix Record.updateN fldname)
        val valty = type_of newvalue
        val rcdty = type_of rcdterm
        val ty = (valty --> valty) --> (rcdty --> rcdty)
        val Kupd = K_rec valty $ newvalue
      in
        Const(fullname, ty) $ Kupd $ rcdterm
      end 
    | SOME (union_ty, variant_ty, _) => (* non-canonical union variants *)
      let
        val coerce_map = \<^Const>\<open>coerce_map variant_ty union_ty\<close>
        val (variant_ty_name, _) = dest_Type variant_ty
        val upd_name = Sign.intern_const thy (variant_ty_name ^ "." ^ suffix Record.updateN fldname)
        val val_ty = type_of newvalue
        val upd_ty = (val_ty --> val_ty) --> (variant_ty --> variant_ty)
        val upd = Const(upd_name, upd_ty)
        val Kupd = K_rec val_ty $ newvalue
      in 
        (coerce_map $ (upd $ Kupd) $ rcdterm)
      end 

fun state_vlookup (fname_opt : string option) (s:MString.t) (state:CalculateState.mungedb) = let
in
  case CNameTab.lookup state {varname = s, fnname = fname_opt} of
    NONE => NONE
  | SOME (realnm, ty, cty, vsort) => let
      val realnm' = case fname_opt of
                      NONE => NameGeneration.global_var (MString.dest realnm)
                    | SOME f => MString.dest realnm
    in
      SOME(realnm',ty,cty,vsort)
    end
end

fun state_varlookup fname s state =
    (* check to see if it's a normal local variable *)
    case state_vlookup (SOME fname) s state of
      NONE => let
      in
        (* check to see if it's a global variable (one accessed through a
           pointer) *)
        case state_vlookup NONE (NameGeneration.C_global_var s) state of
          NONE => let
          in
            (* check to see if it's a embedded function call return variable *)
            if NameGeneration.is_return_or_tmp s then
               state_vlookup (SOME "") s state
            else
               NONE
          end
        | x => x
      end
    | x => x


fun strip_invs com statetype =
    case com of
      (c as Const("Language.whileAnno", T)) $ g $ i $ v $ b => let
      in
        c $ g $ mk_empty_INV statetype $ v $ strip_invs b statetype
      end
    | (Const("Language.specAnno", T) $ _ $ (Abs(_, _, bdy)) $ _ $ _) => let
      in
        strip_invs bdy statetype
      end
    | (t $ g) => strip_invs t statetype $ strip_invs g statetype
    | Abs (v, T, b) => Abs (v, T, strip_invs b statetype)
    | t => t




fun fndefn_term (state : CalculateState.mungedb) cse fninfo rcdinfo memsafe skip_asm globty locty styargs lthy decl = let
  val thy = Proof_Context.theory_of lthy
  open CalculateState
  val statetype = hd styargs
  val ((_ (* rettype *), fname), _ (* params *), _ (* prepost *), locbodyw) =
      decl
  val fname = node fname
  val info = get_info fninfo fname
  val bilist = node locbodyw
  val _ = Feedback.informStr lthy (0, "Translating function "^fname)
  val body = bilist2stmts bilist
  fun varinfo s = state_varlookup fname s state

  val termbuilders : varinfo termbuilder =
      TB { var_updator = var_updator lthy globty locty,
           var_accessor = var_accessor lthy globty locty,
           rcd_updator = rcd_updator thy cse,
           rcd_accessor = rcd_accessor thy cse rcdinfo}

  val stmt_trans = stmt_term lthy cse state fname termbuilders
                             varinfo fninfo
                             statetype globty locty styargs memsafe skip_asm

  val addressed_params = #inparams info |> filter (#4)

  fun mk_init_addressed_param (n, ty, cty, true) =
    let
      val v = Var (n, Unsynchronized.ref (SOME (cty, MungedVar {fname = SOME fname, init = true, munge = MString.mk n, owned_by = NONE})))
            |> RegionExtras.bogwrap |> ExprDatatype.E |> LocalInit |> RegionExtras.bogwrap |> StmtDeclDatatype.Stmt
    in
      v
    end

  val body_stmts = stmt_trans (map (mk_init_addressed_param) addressed_params @ body )

  (* a function is translated to a TRY body CATCH ccatchreturn global_exn_var END form;
     the catch is for any return statements in the body.  Other local abrupt
     terminations would be of break or continue statements, which would
     be handled by the looping forms.  For this reason the catch checks for any
     local abrupt termination and propages non-local abrupt terminations.

     If the last statement of the function is not a return, the flow of
     control will just fall through the bottom of the function, which is
     fine.
  *)
  val init_ret_var =
    map (fn (name, ty, _, _) =>  mk_init_var lthy styargs locty ty name) (#outparams info)


  val body_stmts' =
      case ProgramAnalysis.get_rettype fname cse of
        NONE => raise Fail ("No return type info for function "^fname)
      | SOME Void => body_stmts
      | _ => list_mk_seq (init_ret_var @ [body_stmts,
                          mk_guard (mk_empty statetype) dont_reach_error
                                   (mk_skip_t styargs)])
  val body = mk_catch_t styargs $ body_stmts' $ mk_ccatchreturn thy styargs statetype
in
  (fname, body, strip_invs body statetype)
end

fun extract_defined_functions ast = let
  fun recurse acc decls =
      case decls of
        [] => List.rev acc
      | FnDefn p :: ds => recurse (p::acc) ds
      | _ :: ds => recurse acc ds
in
  recurse [] ast
end




fun translate_body (globty, locty, styargs)
                     (vdecls : CalculateState.mungedb)
                     cse
                     fninfo
                     rcdinfo
                     ms
                     skip_asm
                     lthy
                     decl =
  let
    val result = fndefn_term vdecls cse fninfo rcdinfo ms skip_asm globty locty styargs lthy decl
  in
    result
  end

(* this function is directly called by the Isar loop, and is passed the
   variable state information, as well as the AST of the C program being
   installed
     state :
     ast   : Absyn.ext_decl list
*)
fun define_functions (globty, locty, styargs)
                     (vdecls : CalculateState.mungedb)
                     cse
                     fninfo
                     rcdinfo
                     memsafe
                     skip_asm
                     ast
                     ctxt =
let
  open TermsTypes CalculateState
  val fns = extract_defined_functions ast
  val function_info =
      map (fndefn_term vdecls cse fninfo rcdinfo memsafe skip_asm globty locty styargs ctxt) fns
in
  function_info
end

end (* struct *)
