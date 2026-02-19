(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* interface to Norbert Schirmer's Hoare Package code *)
structure HPfninfo =
struct

  type vars = (string * typ * int Absyn.ctype * bool) list
  type T = {fname : string,
            inparams : vars,
            outparams : vars,
            locals : vars,
            fun_pointer_params: (vars * vars) list,
            body : Absyn.ext_decl HoarePackage.bodykind option,
            spec : (string * Element.context) list,
            mod_annotated_protop : bool,
            callees : string list,
            referenced_funs : string list,
            recursivep : bool,
            clique : string list}

fun positional (inparams:vars, outparams:vars) =
  let
    fun pos (i, (n, T, cT, addressed)) = (i, (n, T, cT, addressed))
    val ins = tag_list 0 inparams |> map pos
    val outs = tag_list (length ins) outparams |> map pos
  in (ins, outs) end

fun positional_params ({inparams, outparams, ...}:T) = positional (inparams, outparams)

end

signature HPINTER =
sig

  type csenv = ProgramAnalysis.csenv
  type fninfo = HPfninfo.T
  val mk_fninfo : local_theory -> csenv -> (string -> bool) ->
                  Absyn.ext_decl list -> (fninfo list list * ProgramAnalysis.callgraph * string list)
  val define_state_spaces : string -> typ list -> string -> fninfo list -> theory -> theory
  val make_function_definitions :
      csenv ->                   (* result of ProgramAnalysis over declarations *)
      typ list ->                (* type arguments to state type operator *)
      fninfo list list ->             (* result of mk_fninfo above *)
      (Proof.context -> AstDatatype.fn_defn -> (string * term * term)) ->
                                 (* compilation/translation function *)
      string ->                  (* name of globals locale *)
      (typ,'a,'b) Element.ctxt list ->
                                 (* globals living in the globals locale *)
      string ->                  (* program name *)
      local_theory ->
      (string list * local_theory)
  val all_locvars: Proof.context -> term -> (string * (term * typ)) list
  val collect_positional: term -> term -> (string * term) list
  val mk_locals:  Proof.context -> term -> term
  val get_actual_locvar: Proof.context -> NameGeneration.local_ref -> term -> term * typ
  val name_type_from_local_var_update:  term -> (term * typ) option
  val dest_local_var_lookup: term -> (term * typ * term) option
  val dest_local_var_update: term -> (term * typ * term option * term option) option
  val dest_local_var_update': term -> (NameGeneration.local_ref * typ * term option * term option) option
  val dest_local_var_update_bare': term -> (NameGeneration.local_ref * typ * term option * term option) option
  val raw_abs_update_actual_locvar: typ -> Proof.context -> string -> term
  val subst_var_update: Proof.context -> string -> term -> term
  val enter_scope: string -> string -> Proof.context -> Proof.context
  val params_of_fun_type: Proof.context -> int CType.ctype -> (HPfninfo.vars * HPfninfo.vars)

  val sublocale: xstring -> (Proof.context -> tactic) -> local_theory -> local_theory
  val sublocale_positional: xstring -> term option list -> (Proof.context -> tactic) -> local_theory -> local_theory
  val immediate_sublocale: xstring -> local_theory -> local_theory
  val global_sublocale: xstring -> xstring -> (Proof.context -> tactic) -> theory -> theory
  val immediate_global_sublocale: xstring -> xstring -> theory -> theory

  val import : (string * term) list -> theory -> xstring ->
        string * ((string * bool) * (term Expression.map * ((binding * Token.T list list) * term) list))
  val apply_in_locale : theory -> xstring -> (local_theory -> 'a) -> 'a
  val check_const_name: (typ -> 'a) -> Proof.context -> string -> string

  val for_clause: bstring -> binding * 'a option * mixfix

  val GENERALISE: Proof.context -> int -> tactic
end

structure HPInter: HPINTER =
struct

type fninfo = HPfninfo.T
type csenv = ProgramAnalysis.csenv

val c_parser_assume_fnspec = Attrib.setup_config_bool @{binding c_parser_assume_fnspec} (K false);

structure LocalsSplitState : SPLIT_STATE =
struct
\<comment> \<open>
* Local variables are represented as function @{typ \<open>nat \<Rightarrow> byte list\<close>},
  where the @{typ nat} represents the position. A typed view is obtained via @{const clookup}
  and @{const cupdate}.
* Global variables are record.
* exn-variable is record field.
\<close>

val is_state_type = IsabelleTermsTypes.is_state_type

val full_globalsN = @{const_name StateSpace.state.globals};

fun isState ctxt (trm as (Const _$Abs (s,T,t))) =
  let
    val res = is_state_type ctxt T andalso
      is_none (try HoarePackage.dest_hoare_raw (strip_qnt_body @{const_name All} t))
  in
    res
  end
  | isState _ _ = false;

fun isFreeState ctxt (t as Free (_,T)) =
    is_state_type ctxt T
  | isFreeState _ t = false;

fun abs_state ctxt = Option.map snd o HoarePackage.first_subterm (isFreeState ctxt);

fun comp_name t =
    case try HoarePackage.dest_string t of
      SOME str => str
    | NONE => (case t of
                 Free (s,_) => s
               | Const (s,_) => Long_Name.base_name s
               | t => raise TERM ("LocalsSplitState.comp_name",[t]))

fun sel_name (Const (@{const_name clookup}, _)$name$_) = comp_name name
  | sel_name (Const (x,_)$_) = Long_Name.base_name x (* record selection *)
  | sel_name t = raise TERM ("LocalsSplitState.sel_name",[t]);

fun is_global (Const _$(Const (sel,_)$_)) = (sel = full_globalsN)
  | is_global (Const (@{const_name clookup}, _) $ _ $ (Const (@{const_name locals}, _) $ _)) = false
  | is_global (Const _$_) = false (* globals_exn_var *)
  | is_global t = raise TERM ("LocalsSplitState.is_global",[t]);

fun sel_type (\<^Const_>\<open>clookup T for n s\<close>) = T
  | sel_type (Const (_,T)$_) = range_type T
  | sel_type t = raise TERM ("LocalsSplitState.sel_type",[t]);

fun sel_eq t y = (sel_name t = y)

val sel_idx = HoarePackage.idx sel_eq;

fun bound xs t =
  let val i = sel_idx xs (sel_name t)
  in if i < 0 then (length xs, xs@[t]) else (i,xs) end

fun is_state s t =
  let
    val res = case t of
      (Const _ $(Const _ $ Free (s',_))) => s'=s
    | (Const _ $ Free (s',_)) => s' = s
    | Free (s',_) => s' = s
    | _ => false
  in
    res
  end;


fun fold_state_prop var app abs other inc s res (t as (Const (@{const_name clookup},_)$name$state)) =
         if is_state s state
         then var inc res t
         else other res t (*raise TERM ("LocalsSplitState.fold_state_prop",[t])*)
  | fold_state_prop var app abs other inc s res (t as (Const (sel,_)$Free (s',_))) = (* Record selection, exn-var *)
         if s'=s
         then if HoarePackage.is_state_var sel
              then var inc res t
              else raise TERM ("LocalsSplitState.fold_state_prop(1)",[t])
         else other res t
  | fold_state_prop var app abs other inc s res
      (t as ((t1 as (Const (sel,_)))$(t2 as (Const (glb,_)$Free (s',_))))) = (* global record selection *)
         if s'=s andalso HoarePackage.is_state_var sel andalso (glb=full_globalsN)
         then var inc res t
         else let val res1 = fold_state_prop var app abs other inc s res t1
                  val res2 = fold_state_prop var app abs other inc s res1 t2
              in app res1 res2
              end
  | fold_state_prop var app abs other inc s res (t as (Free (s',_))) =
         if s'=s then raise TERM ("LocalsSplitState.fold_state_prop(2)",[t])
         else other res t
  | fold_state_prop var app abs other inc s res (t1$t2) =
         let val res1 = fold_state_prop var app abs other inc s res t1
             val res2 = fold_state_prop var app abs other inc s res1 t2
         in app res1 res2 end
  | fold_state_prop var app abs other inc s res (Abs (x,T,t)) =
         let val res1 = fold_state_prop var app abs other (inc+1) s res t
         in abs x T res1
         end
  | fold_state_prop var app abs other inc s res t = other res t

fun collect_vars s t =
  let
    fun var _ vars t  = snd (bound vars t);
    fun app _ vars2 = vars2;
    fun abs _ _ vars = vars;
    fun other vars _ = vars;
    val res = fold_state_prop var app abs other 0 s [] t;
  in res end;

fun abstract_vars vars s t =
  let
    fun var inc _ t  = let val i = fst (bound vars t) in Bound (i+inc) end;
    fun app t1 t2 = t1$t2;
    fun abs x T t = Abs (x,T,t);
    fun other _ t = t;
    val dummy = Bound 0;
    val res = fold_state_prop var app abs other 0 s dummy t;
  in res end;

fun sort_vars ctxt vars =
  let
    fun compare (t1,t2) =
      let
        val g1 = is_global t1
        val g2 = is_global t2
        val n1 = sel_name t1;
        val n2 = sel_name t2;
      in if g1
         then if g2 then
              string_ord (n1,n2)
              else LESS
         else if g2 then GREATER
              else string_ord (n1,n2)
      end
  in sort (rev_order o compare) vars end;

fun split_state ctxt s _ t =
  let
    val vars  = collect_vars s t;
    val vars' = if Config.get ctxt HoarePackage.sort_variables then sort_vars ctxt vars else vars;
    val abs = abstract_vars vars' s t
  in (abs, rev vars') end;

fun abs_var ctxt t = (HoarePackage.remdeco' ctxt (sel_name t), sel_type t);

(* Proof for: EX x_1 ... x_n. P x_1 ... x_n
 *            ==> EX s. P (clookup proj_1 x_1 s) ... (clookup_n x_n s)
 * Supported (nested) state selections:
     - record selections (including 'globals' and 'locals') and
     - locals (function) lookups
 * Implementation-Idea:
 * 1. Eliminate existential quantifiers in premise
 * 2. Instantiate s with:
       (%x. undefined)("x_1" := inj_1 x_1, ..., "x_n" := inj_n x_n)
 * 3. Simplify
 *)

local

val ss =
  simpset_of
    (put_simpset (simpset_of @{theory_context Fun}) @{context}
    |> Simplifier.add_simps (@{thm StateFun.id_id_cancel}
      :: @{thms list.inject list.distinct char.inject
      cong_exp_iff_simps simp_thms})
    |> fold Simplifier.add_proc [Record.simproc, StateFun.lazy_conj_simproc]
    |> fold Simplifier.add_proc @{code_simprocs state_simp}
    |> fold Simplifier.add_cong @{thms block_conj_cong});

in

fun ex_tac ctxt vs = SUBGOAL (fn (goal, i) =>
  let
    val (Const (_, exT) $ _) = HOLogic.dest_Trueprop (Logic.strip_imp_concl goal);
    val sT = domain_type (domain_type exT);

    val s0 = Const (@{const_name HOL.undefined},sT);

    fun strip_sel (sel$state) = let val (sels, state') = strip_sel state in (sel::sels, state') end
      | strip_sel state = ([], state)

    fun sel_to_upd (\<^Const_>\<open>clookup T\<close> $ name) =
          let
            val upd = \<^Const>\<open>cupdate T\<close>
          in
            ((comp_name name, T), fn v => upd $ name $ v)
          end
      | sel_to_upd (Const (record_sel, T)) =
          let
            val stateT = domain_type T
            val valT = range_type T
          in
            ((Long_Name.base_name record_sel, valT),
             fn v => Const (suffix Record.updateN record_sel, (valT --> valT) --> stateT --> stateT) $ v)
          end
      | sel_to_upd t = raise TERM ("LocalsSplitState.sel_to_upd", [t])

    fun mk_upd (i, t) (vTs, s) =
      let
        val (sels, s') = strip_sel t
        val (vTs', upds) = map sel_to_upd sels |> split_list
        val (v, T) = hd vTs'
        val K_v = Abs (v, T, Bound (i + 1))
      in
        ((v, T)::vTs, fold (fn upd => fn v => upd v) upds K_v $ s)
      end


    fun mk_witness_state vs =
      let
        val (vars, s) = fold_index mk_upd vs ([], s0)
        val abs_s = fold_rev Term.abs vars s
      in
        abs_s
      end

    val inst = mk_witness_state (rev vs);

    fun lift_inst_ex_tac i st =
      let
        val rule  = Thm.lift_rule (Thm.cprem_of st i) (Drule.incr_indexes st exI);
        val (_$x) = HOLogic.dest_Trueprop (Logic.strip_assums_concl (hd (Thm.prems_of rule)));
        val inst_rule =
          infer_instantiate ctxt [(#1 (dest_Var (head_of x)), Thm.cterm_of ctxt inst)] rule;
      in (compose_tac ctxt (false,inst_rule, Thm.nprems_of exI) i st) end;
  in
    EVERY
      [REPEAT_DETERM_N (length vs) (eresolve_tac ctxt [exE] i),
       lift_inst_ex_tac i,
       simp_tac (put_simpset ss ctxt
         addsimps (Named_Theorems.get @{context} @{named_theorems "state_simp"})) i
      ]
  end
)

end (* local *)

end;

structure GeneraliseStateLocals = Generalise (structure SplitState=LocalsSplitState);

val GENERALISE = GeneraliseStateLocals.GENERALISE

val _ = Theory.setup (
  let
    val sp =
      {
        name = NameGeneration.locals_stackN,
        is_state_type = IsabelleTermsTypes.is_state_type,
        generalise = GeneraliseStateLocals.GENERALISE,
        state_simprocs = [Record.simproc] @ @{code_simprocs state_simp},
        state_upd_simprocs = [Record.upd_simproc],
        state_ex_sel_eq_simprocs = [Record.ex_sel_eq_simproc],
        is_defined = CLocals.is_defined,
        read_function_name = CLocals.read_function_pointer,
        lookup_tr = CLocals.mk_lookup,
        update_tr = CLocals.mk_update,
        is_lookup = CLocals.is_lookup,
        lookup_tr' = CLocals.lookup_tr',
        dest_update_tr' = CLocals.dest_update_tr',
        update_tr' = CLocals.update_tr'
      }
  in
    Context.theory_map (Hoare.install_state_space sp)
  end)


fun in_positional deco params =
 tag_list 1 params |> map (fn (i, (_ , ty, cty, addressed)) =>
   (NameGeneration.positional_name deco "in" i cty, ty, cty, addressed))

fun params_of_fun_signature ctxt (retT, argTs) =
      (map (fn cty => ("", CalculateState.ctype_to_typ {bitint_padding=true} ctxt cty, cty, false)) argTs |> in_positional false,
       [(MString.dest NameGeneration.return_var_name, CalculateState.ctype_to_typ {bitint_padding=true} ctxt retT, retT, false)])

fun params_of_fun_type ctxt T =
  case T of
    (CType.Ptr (CType.Function(pTs))) => params_of_fun_signature ctxt pTs
  | CType.Function(pTs) => params_of_fun_signature ctxt pTs
  | _ => ([], [])

fun params_of_fun_types ctxt ctys = map (params_of_fun_type ctxt) ctys

val empty = Binaryset.empty String.compare
(* make function information - perform a preliminary analysis on the
   abstract syntax to extract function names, parameters and specifications *)

fun mk_fninfo ctxt csenv includeP decllist: (fninfo list list * ProgramAnalysis.callgraph * string list) =
let
  val cg as {callees,callers} = ProgramAnalysis.compute_callgraphs csenv
  val funs_in_fun_ptr_environment = 
    Binaryset.addList (empty, ProgramAnalysis.get_functions_used_via_fun_ptr csenv)
  val funs_with_fun_ptr_calls = ProgramAnalysis.functions_with_fun_ptr_calls csenv
  val funs_with_fun_ptr_calls' = Binaryset.addList (empty, funs_with_fun_ptr_calls)
  val funs_depending_on_fun_ptr_environment = ProgramAnalysis.closure callers funs_with_fun_ptr_calls
  val fun_ptr_clique = Binaryset.intersection (funs_in_fun_ptr_environment, funs_depending_on_fun_ptr_environment)

  fun depends_on_fun_ptr_clique fnm =
    Binaryset.member (fun_ptr_clique, fnm) orelse Binaryset.member (funs_with_fun_ptr_calls', fnm)


  fun lookup f fnm = the_default empty (Symtab.lookup f fnm)
  datatype kind = Caller | Callee


  fun mk_list f fnm = 
    let
      val directs = lookup f fnm
    in
       Binaryset.listItems directs
    end

  val cliques = ProgramAnalysis.get_functions csenv
    |> Topo_Sort.topo_sort {cmp = String.compare,
                            graph = mk_list callees,
                            converse = mk_list callers}

  val cliques = map (filter includeP) cliques |> filter_out null
  val n = 0 |> fold (curry op +) (map length cliques)
  val _ = Feedback.informStr ctxt (0, "Number of functions: " ^ string_of_int n)
  val _ = Feedback.informStr ctxt (2, "fun_ptr_clique: " ^ @{make_string} (Binaryset.listItems fun_ptr_clique))
  val _ = Feedback.informStr ctxt (2, "cliques: " ^ @{make_string} cliques)

  fun get_clique' fname =
   these (find_first (fn fs => member (op =) fs fname) cliques)

  open Absyn NameGeneration
  (* don't fold top-level declarations into the table again: the program
     analysis that built the csenv in the first place will have already
     grabbed this *)
  fun toInclude (FnDefn((_, fname), _, _, _)) = includeP (node fname)
    | toInclude _ = false
  val table = ProgramAnalysis.get_hpfninfo csenv
    |> fold (fn d => fn tab => if toInclude d then
                                  ProgramAnalysis.update_hpfninfo0 d tab
                               else tab)
         decllist
  fun parse_spec fname fspec =
      case fspec of
        fnspec spec => let
          val toklist = Token.explode (Thy_Header.get_keywords (Proof_Context.theory_of ctxt)) Position.none (node spec)
                        (* it might be nice to remember where the spec came
                           from so we could put in a reasonable pos'n above *)
          val filtered = List.filter Token.is_proper toklist
          val eof = Token.stopper
          val nameproplist = the (Scan.read eof
                                              HoarePackage.proc_specs
                                              filtered)
                             handle Option =>
                               raise Fail ("Failed to scan spec for "^fname)
          fun nprop2Assume (name, prop) =
              ((Binding.name name, []), [(prop, [])])
        in
          [("", Element.Assumes (map nprop2Assume nameproplist))]
        end
      | fn_modifies slist => let
          val mgoal = Modifies_Proofs.gen_modify_goalstring csenv fname slist
        in
          [("", Element.Assumes [((Binding.name (fname ^ "_modifies"), []),
                                  [(mgoal, [])])])]
        end
      | didnt_translate => []
      | gcc_attribs _ => []
      | relspec _ => [] (* fixme *)
  fun parse_specs fname fspecs =
      List.concat (map (parse_spec fname) fspecs)
  fun mk_ret rettype =
      if rettype = Void then []
      else [(MString.dest return_var_name,
             CalculateState.ctype_to_typ {bitint_padding=true} ctxt rettype,
             rettype, false)]
  fun to_param fname vi = let
    open CalculateState ProgramAnalysis
    val cty = get_vtype vi
    val typ = ctype_to_typ {bitint_padding=true} ctxt cty
    val addressed = is_addressed csenv (get_mname vi, SOME fname)
  in
    (MString.dest (get_mname vi), typ, cty, addressed)
  end

  fun foldthis (_, d) (i as (acc, external)) =
      case d of
        FnDefn((_ (* retty *),fname_w), _ (* inparams *), prepost, _ (* body *)) => let
          open HoarePackage CalculateState ProgramAnalysis
          val fname = node fname_w
          val rettype = the (get_rettype fname csenv)
          val inparams =  map (to_param fname) (the (get_params fname csenv))
                      handle Option =>
                        raise Fail ("mk_fninfo: No function information for "^
                                    fname)
        in
          ({fname = fname,
           inparams = inparams,
           outparams = mk_ret rettype,
           locals = map (to_param fname) (get_locals csenv fname) |> distinct (op =),
           fun_pointer_params = params_of_fun_types ctxt (used_fun_types_of_fun csenv fname),
           callees = get_direct_callees csenv fname,
           referenced_funs = these (Symtab.lookup (get_referenced_funs csenv) fname),
           recursivep = is_recursivefn csenv fname,
           body = SOME (BodyTerm d), spec = parse_specs fname prepost,
           mod_annotated_protop = false, clique = get_clique' fname}
          ::
          acc, external)
        end
      | Decl d0 => let
        in
          case node d0 of
            ExtFnDecl { name, specs, params = _, rettype = _ } => let
              open CalculateState ProgramAnalysis
              val fname = node name
              val params = map (to_param fname) (the (get_params fname csenv))
                  handle Option =>
                         raise Fail ("mk_fninfo: No function information for "^
                                     fname)
              val rettype = the (get_rettype fname csenv)
              val locals = map (to_param fname) (get_locals csenv fname) |> distinct (op =)
              val spec = parse_specs fname specs
              val mod_annotated_protop = is_some (get_fun_modifies csenv fname)
              val body = NONE
            in
              ({fname = fname,
               inparams = params, recursivep = false, callees = get_direct_callees csenv fname,
               referenced_funs = these (Symtab.lookup (get_referenced_funs csenv) fname),
               outparams = mk_ret rettype, locals = locals, body = body,
               spec = spec, mod_annotated_protop = mod_annotated_protop,
               clique = get_clique' fname,
               fun_pointer_params = params_of_fun_types ctxt (used_fun_types_of_fun csenv fname)}
              ::
              acc, (fname, length params) :: external)
            end
          | _ => i
        end
  val (fninfos, externals) = Symtab.fold foldthis table ([], []);
  val _ = if not (null externals) then
      Feedback.informStr ctxt (0,
        cat_lines ("The following functions are external" ::
          (externals |> sort_by fst |> map (fn (n, l) => n ^ " (" ^ Int.toString l ^ " args)"))))
    else ()
  fun get_info fname =
     the (find_first (fn info => #fname info = fname) fninfos);
  val fninfo_cliques = map (map get_info) cliques;
in
  (fninfo_cliques, cg, Binaryset.listItems fun_ptr_clique)
end

fun extract_element_asms e =
    case e of
      Element.Assumes asms =>
        map (fn (nm, [(t,_)]) => (nm, t)
              | _ => raise Fail "extract_element_term: malformed Assumes") asms
    | _ => raise Fail "extract_element_term: malformed element"


fun mkSpecFunction lthy cse styargs (f : fninfo) = let
  open TermsTypes
  val {fname,...} = f
  val state_ty = hd styargs
  val mods = fname |> ProgramAnalysis.get_fun_modifies cse
                   |> the |> Binaryset.listItems
  val s = Free("s", state_ty)
  val t = Free("t", state_ty)
  val relbody = Modifies_Proofs.gen_modify_body lthy state_ty s t mods
  val collect_t = mk_collect_t (mk_prod_ty (state_ty, state_ty))
  fun typedterm t =
    Syntax.string_of_term lthy t ^ " :: " ^
    Syntax.string_of_typ lthy (type_of t)
  fun appi f l = let
    fun recurse i l = case l of [] => () | h::t => (f i h; recurse (i + 1) t)
  in
    recurse 0 l
  end


  fun parse_spec (_, e) = let
    val lnm_strs = extract_element_asms e
    fun innermap (((speclocalename_b,_), tstr)) = let
      val speclocalename = Binding.name_of speclocalename_b
        (* jump into an lthy corresponding to globloc to parse the tstr; this lthy
           is dropped and not used again *)
      val tm = Syntax.read_term lthy tstr
      val (vs, body) = strip_forall tm
      val PQopt =
        case body of
          Const(@{const_name "hoarep"}, _) $ _ (* gamma *) $ _ $_ $ P $ _ $ Q $ _ =>
            if String.isSuffix "modifies" speclocalename then NONE
            else SOME (P,Q)
        | _ =>
            let
              val (f, args) = strip_comb tm
              val cstr = case f of Const(s, _) => "const: "^s
                                 | Free(s, _) => "free: "^s
                                 | _ => "huh?"
            in
              raise Fail ("parse_spec: bad specification " ^ speclocalename ^ " : " ^
                          Syntax.string_of_term lthy t ^ "\n(" ^
                          cstr ^ " applied to " ^
                          Int.toString (length args) ^ " arguments)")
            end
    in
      case PQopt of
        NONE => NONE
      | SOME (P0, Q0) =>
        let
          val _ = appi (fn n => fn v =>
                        Feedback.informStr lthy (0, "var#"^Int.toString n^" "^typedterm v)) vs
          val elty0 = dest_set_type (type_of P0)
          val sigma = the (TermsTypes.match_type_frees{pattern = elty0, m = state_ty})
                      handle Option => raise Fail "Couldn't match state types"
          val ptype = Syntax.string_of_typ lthy
          fun foldthis (ty1, ty2) acc = (ptype ty1 ^ " |-> " ^ ptype ty2) :: acc
          val sigma_elts0 = TypTable.fold foldthis sigma []
          val P1 = subst_frees sigma P0
          val Q1 = subst_frees sigma Q0
          val vs = map (subst_frees sigma) vs
          val s = variant vs s
          val t = variant vs t
          val P2 = List.foldr (fn (v, t) => unbeta{bv=v,body=t}) P1 vs
          val Q2 = List.foldr (fn (v, t) => unbeta{bv=v,body=t}) Q1 vs
          val P = list_mk_comb(P2, vs)
          val Q = list_mk_comb(Q2, vs)
          val body_imp = list_mk_forall(vs, mk_imp(mk_IN(s,P), mk_IN(t,Q)))
          val Pexists = list_mk_exists(vs, mk_IN(s,P))
          val res = collect_t $ list_mk_pabs([s,t], mk_conj(body_imp, Pexists))
        in
          SOME (res, mk_collect_t state_ty $ list_mk_pabs ([s], Pexists))
        end
    end
  in
    List.mapPartial innermap lnm_strs
  end

  val mod_spec = collect_t $ list_mk_pabs([s,t], relbody)

  val otherspecs_pres = List.concat (map parse_spec (#spec f))
  val (otherspecs, pres) = split_list otherspecs_pres
  val assume = Config.get lthy c_parser_assume_fnspec
  val fbody =
    if null otherspecs then
      mk_Spec(styargs, mod_spec)
    else
      let
        val _ = appi (fn n => fn t => Feedback.informStr lthy (0,
                       "spec#" ^ Int.toString n ^ ": " ^ typedterm t)) otherspecs
        val spec_t = mod_spec |> fold (curry mk_inter) otherspecs
        val True = \<^instantiate>\<open>'s = state_ty in term \<open>{(s::'s). True}\<close>\<close>
        val pre_t = case pres of [] => True | (p:: ps) => p |> fold (curry mk_inter) ps
      in
       if assume then
         Const(@{const_name "spec_pre_post"},
                    @{typ "strictc_errortype"} --> @{typ "strictc_errortype"} --> type_of pre_t --> type_of spec_t -->
                    mk_com_ty styargs) $ @{const "ImpossibleSpec"} $ @{const "AssumeError"} $ pre_t $ spec_t
       else 
         Const(@{const_name "guarded_spec_body"},
                    @{typ "strictc_errortype"} --> type_of spec_t -->
                    mk_com_ty styargs) $ @{const "ImpossibleSpec"} $ spec_t
      end
in
  (fname, fbody, fbody)
end

fun rhs_extras rhs =
    Term.fold_aterms
        (fn v as Free _ => insert (op aconv) v | _ => I)
        rhs
        [];

fun extract_fixes elems = let
  open Element
  fun fix2term (n,tyopt,_) =
      case tyopt of
        NONE => NONE
      | SOME ty => SOME (Free(Binding.name_of n,ty))
  fun recurse elems =
      case elems of
        [] => []
      | Fixes fs::rest => List.mapPartial fix2term fs @ recurse rest
      | _ :: rest => recurse rest
in
  recurse elems
end

fun create_bodyloc_elems globs lthy (name, body_t, body_stripped_t) =
let
  val thy = Proof_Context.theory_of lthy
  val rhs_vars0 = rhs_extras body_t
  val rhs_vars = filter_out
        (fn (t as Free(n,T)) => member (op aconv) globs t orelse Variable.is_fixed lthy n) rhs_vars0

  fun mk_rhs(nm, vars, t) = let
    val t0 = TermsTypes.list_mk_abs (vars, t)
  in
    (nm, Term.map_types (Sign.certify_typ thy) t0)
  end

  val eqt_stripped = mk_rhs(name ^ "_body", [], body_stripped_t)
  val eqt = mk_rhs(name ^ (if null rhs_vars then "_body" else "_invs_body"),
                   rhs_vars, body_t)
  fun eqn_to_definfo (nm, t) = let
    val b = Binding.name nm
  in
    ((b, NoSyn), ((Thm.def_binding b, []), t))
  end
  val elems =
      if null rhs_vars then [eqn_to_definfo eqt]
      else [eqn_to_definfo eqt_stripped, eqn_to_definfo eqt]
  type lthy_def_info = (binding * mixfix) * (Attrib.binding * term)
in
  (elems : lthy_def_info list,
   (name, if null rhs_vars then body_t else body_stripped_t))
end

fun add_syntax (name, recp, inpars, outpars) lthy =
  let
    open HoarePackage
    val (in_positional, out_positional) =  HPfninfo.positional (inpars, outpars)
    fun mk_lense (i, (_, T, _, _)) = {
          lookup = CLocals.mk_lookup_positional T i,
          update = CLocals.mk_update_positional T i};

    val pars = map (fn par as (_, (n, _, _, _))  => (In , n, SOME (mk_lense par))) in_positional @
               map (fn par as (_, (n, _, _, _))  => (Out, n, SOME (mk_lense par))) out_positional

    val lthy_decl =
      lthy
      |> More_Local_Theory.in_theory (Context.theory_map (add_params Morphism.identity name pars))
      |> More_Local_Theory.in_theory (Context.theory_map
                (add_state_kind Morphism.identity name (HoarePackage.Other NameGeneration.locals_stackN)))
      |> recp? More_Local_Theory.in_theory (Context.theory_map (add_recursive Morphism.identity name))

  in
    lthy_decl
  end

fun intern_locale thy = Locale.intern thy #> perhaps Long_Name.dest_hidden;

fun dest_local_var_lookup \<^Const_>\<open>clookup T for n \<open>@{term_pat \<open>locals ?s\<close>}\<close>\<close> =
  SOME (n, T, s)
  | dest_local_var_lookup (Abs (_, _, bdy)) = dest_local_var_lookup bdy
  | dest_local_var_lookup _ = NONE

fun dest_local_var_update_bare (t as @{term_pat "locals_update o (cupdate ?n)"}) =
      let
        val cupd = Term.dest_comb t |> snd
        val T = fastype_of cupd |> strip_type |> fst |> hd |> range_type
      in
        SOME (n, T, NONE, NONE)
      end
  | dest_local_var_update_bare (t as @{term_pat "(\<lambda>upd. locals_update (cupdate ?n upd))"}) =
      let
        val Abs (upd, updT, _) = t 
        val T = updT |> range_type
      in
        SOME (n, T, NONE, NONE)
      end
  | dest_local_var_update_bare _ = NONE


fun dest_local_var_update @{term_pat "locals_update (cupdate ?n ?upd) ?s"} =
      SOME (n, range_type (fastype_of upd), SOME upd, SOME s)
  | dest_local_var_update @{term_pat "locals_update (cupdate ?n ?upd)"} =
      SOME (n, range_type (fastype_of upd), SOME upd, NONE)
  | dest_local_var_update _ = NONE

fun subst_var_update ctxt value_name term =
  let
    fun dest_abs (Abs (s, sT, bdy$Bound 0)) = (SOME (s, sT), bdy, fn t => t $ Bound 0)
      | dest_abs (Abs (s, sT, bdy)) = (SOME (s, sT), bdy, I)
      | dest_abs term = (NONE, term, I)

    val (maybe_state, bdy, mk_bdy) = dest_abs term

    fun mk_free upd =
      let
        val T = fastype_of upd
      in
        case maybe_state of
          NONE => Free (value_name, T)
        | SOME (s, sT) => Free (value_name, sT --> T) $ Bound 0
      end

    val bdy' =
      case snd (Utils.norm_eta bdy) of
        @{term_pat "locals_update (cupdate ?n ?upd) ?s"} =>
          \<^infer_instantiate>\<open> upd = \<open>mk_free upd\<close>  and n = n and s = s
            in term \<open>locals_update (cupdate n upd) s\<close>\<close> ctxt
      | t as @{term_pat "locals_update (cupdate ?n ?upd)"} =>
          (case maybe_state of
             SOME (s, sT) =>
                \<^infer_instantiate>\<open>upd = \<open>mk_free upd\<close> and s = \<open>Free(s, sT)\<close> and n = n
                  in term \<open>locals_update (cupdate n upd) s\<close>\<close> ctxt
                |> dest_comb |> fst
           | NONE =>
              \<^infer_instantiate>\<open>upd = \<open>mk_free upd\<close> and n = n and
                   s = \<open>Free ("s", Term.range_type (fastype_of t))\<close>
                 in term \<open>locals_update (cupdate n upd) s\<close>\<close> ctxt
               |> dest_comb |> fst)
      | (Const var $ upd $ s) => Const var $ mk_free upd $ s
      | (Const var $ upd) => Const var $ mk_free upd
      | _ => bdy
  in
    case maybe_state of
      SOME (s, sT) => Abs (s, sT, mk_bdy bdy')
    |  NONE => mk_bdy bdy'
  end

fun gen_dest_local_var_update' dest t = dest t
  |> Option.mapPartial (fn (t, T, upd, s) =>
       let
       in
         case try Utils.dest_nat_or_number t of
           SOME i => SOME (NameGeneration.Positional (i, T), T, upd, s)
         | NONE => (case t of Const (n, _) => SOME (NameGeneration.Named n, T, upd, s) | _ => NONE) 
       end)


val dest_local_var_update' = gen_dest_local_var_update' dest_local_var_update
val dest_local_var_update_bare' = gen_dest_local_var_update' dest_local_var_update_bare

fun name_type_from_local_var_update @{term_pat "locals_update (cupdate ?n ?upd) ?s"} =
      SOME (n, range_type (fastype_of upd))
  | name_type_from_local_var_update @{term_pat "locals_update (cupdate ?n ?upd)"} =
      SOME (n,  range_type (fastype_of upd))
  | name_type_from_local_var_update (t as @{term_pat "\<lambda>upd. locals_update (cupdate ?n upd)"}) =
      SOME (n,  range_type (domain_type (fastype_of t)))
  | name_type_from_local_var_update _ = NONE

(* ensure that proc comes first to resolve short_names *)
fun enter_scope_declaration prog_name fname phi =
  CLocals.scope_map (K [prog_name, fname])

fun enter_scope prog_name fname =
 Context.proof_map (enter_scope_declaration prog_name fname Morphism.identity)

fun mk_locals ctxt state =
  Const(@{const_name locals}, dummyT) $ state
  |> Syntax.check_term ctxt

fun get_locvar ctxt (T, lookup) state =
   let
    val locals = Const(@{const_name locals}, dummyT) $ state
    val value = lookup $ locals |> Syntax.check_term ctxt
  in (value, T) end

fun get_actual_locvar ctxt loc_ref state =
  let
    val locals = Const(@{const_name locals}, dummyT) $ state
    val (lookup, T) = CLocals.gen_mk_lookup ctxt loc_ref
    val value = lookup $ locals |> Syntax.check_term ctxt
  in (value, T) end

fun gen_abs_update_actual_locvar raw ctxt name state =
  let
    val value = Bound 0
    val upd = CLocals.mk_update ctxt name $ value
    val abs_state as (Abs (v, vT, (loc_upd $ s))) =
      Abs ("v", dummyT, Const (@{const_name locals_update}, dummyT) $ upd $ state)
      |> Syntax.check_term ctxt
  in if raw then (Abs (v, vT, loc_upd)) else abs_state end

fun raw_abs_update_actual_locvar stateT ctxt name =
  let
    val state = Free ("_s", stateT)
  in
    gen_abs_update_actual_locvar true ctxt name state
  end

fun all_locvars ctxt state =
  let
    val locals = CLocals.get_locals ctxt
  in
    locals |> map (fn (name, lookup) => (name, get_locvar ctxt lookup state))
  end

fun add_positional s (t as (\<^Const_>\<open>clookup T for n s'\<close>)) ps =
      if s = s' then
        (case try Utils.dest_nat_or_number n of
          SOME i => if exists (fn (_, t') => t' = t) ps then
                        ps
                    else
                      (string_of_int i, t) :: ps
        | _ => ps)
      else ps
  | add_positional _ _ ps = ps;

fun fold_term f (t as Abs (_, _, b)) = f t  #> fold_term f b
  | fold_term f (x as (t $ u)) = f x #> fold_term f t #> fold_term f u
  | fold_term f t = f t;

fun collect_positional state t = [] |> fold_term (add_positional state) t;

fun import named_fixes thy name =
  let
    val term_map =  Expression.Named named_fixes
  in (NameGeneration.intern_locale thy name, (("", false), (term_map,[]))) end

fun import_positional fixes thy name =
  let
    val term_map =  Expression.Positional fixes
  in (NameGeneration.intern_locale thy name, (("", false), (term_map,[]))) end

fun import_impl_locale thy args name =
  let
    val term_map = Expression.Named []
  in
    (NameGeneration.intern_impl_locale_name thy name, (("", false), (term_map,[])))
  end

fun for_clause name = (Binding.name name, NONE, NoSyn)

fun sublocale super_loc tac lthy =
  let
    val current_locale = the (Named_Target.locale_of lthy)
    val _ = Feedback.informStr lthy (1, "establishing " ^ quote current_locale ^ " as sublocale of: " ^ quote super_loc)
  in
    lthy
    |> Interpretation.sublocale ([import [] (Proof_Context.theory_of lthy) super_loc],[]) []
    |> Proof.global_terminal_proof
          ((Method.Basic (fn ctxt => SIMPLE_METHOD (tac ctxt)), Position.no_range), NONE)
  end

fun sublocale_positional super_loc fixes tac lthy =
  let
    val current_locale = the (Named_Target.locale_of lthy)
    val _ = Feedback.informStr lthy (1, "establishing " ^ quote current_locale ^ " as sublocale of: " ^ quote super_loc)
  in
    lthy
    |> Interpretation.sublocale ([import_positional fixes (Proof_Context.theory_of lthy) super_loc],[]) []
    |> Proof.global_terminal_proof
          ((Method.Basic (fn ctxt => SIMPLE_METHOD (tac ctxt)), Position.no_range), NONE)
  end

fun immediate_sublocale super_loc =
  sublocale super_loc (fn ctxt => Locale.intro_locales_tac {strict = false, eager = true} ctxt [])

fun global_sublocale loc super_loc tac thy =
  let
    val ctxt = Proof_Context.init_global thy
    val _ = Feedback.informStr ctxt (1, "establishing " ^ quote loc ^ " as sublocale of: " ^ quote super_loc)
  in
    Utils.timeit_msg 1 ctxt (fn _ => quote loc ^ " sublocale of: " ^ quote super_loc) (fn _ => 
    thy
    |> Interpretation.global_sublocale (intern_locale thy loc) ([import [] thy super_loc],[]) []
    |> Proof.global_terminal_proof
         ((Method.Basic (fn ctxt => SIMPLE_METHOD (tac ctxt)), Position.no_range), NONE)
    |> Proof_Context.theory_of)
  end

fun immediate_global_sublocale loc super_loc =
  global_sublocale loc super_loc (fn ctxt => 
    Utils.timeap_msg_tac 2 ctxt (fn _ => "immediate_sublocale intro_locales")  
     (Locale.intro_locales_tac {strict = false, eager = true} ctxt []))


fun define_state_spaces prog_name styargs globloc fninfos thy =
  let

    fun define_function_scope {fname, inparams, outparams, locals, ...} thy =
      let
        fun prj (s, T, _, _) = (s, T)
        fun tag_in (i, (s, T, _, _)) = (s, T, NameGeneration.In i)
        fun tag kind (s, T, _, _) = (s, T, kind)

        val vars =
          map tag_in (tag_list 0 inparams) @
          map (tag NameGeneration.Out) outparams @
          map (tag NameGeneration.Loc) locals
      in
        thy |> CLocals.define_locals [prog_name, fname] vars
      end

    val thy = thy |> fold define_function_scope fninfos

    fun proj xs = map (fn (n, T, _ ) => (HoarePackage.varname n, T)) xs

    fun define_variables_bundle fname name thy =
         thy |> Bundle.init {open_bundle = false} (Binding.make (name, \<^here>))
             |> Local_Theory.declaration {syntax = true, pervasive = false, pos = \<^here>} (fn phi =>
                   Hoare.set_default_state_kind (Hoare.Other NameGeneration.locals_stackN) #>
                   enter_scope_declaration prog_name fname phi)
             |> Local_Theory.exit_global

    fun define_function_state_spaces ({fname, inparams, outparams, locals, fun_pointer_params, ...}:fninfo) thy =
      let
        val varsN = NameGeneration.variables_bundle_name fname
      in
        thy
        |> define_variables_bundle fname varsN
      end


    val thy = thy
      |> fold define_function_state_spaces fninfos
  in
    thy
  end


fun apply_in_locale thy loc_name f =
  let
    val lthy = Named_Target.init [] (NameGeneration.intern_locale thy loc_name) thy
  in f lthy end

fun try_apply_in_locale thy loc_name f =
  let
    val lthy = Named_Target.init [] (NameGeneration.intern_locale thy loc_name) thy
  in try f lthy end



fun check_const_name check ctxt name =
  let
    val Const(c, T) = Proof_Context.read_const {proper = true, strict = false} ctxt name
    val _ = check T
  in
    c
  end

val add_locale = CalculateState.add_locale

(* The following is modelled on the code in HoarePackage.procedures_definition
*)
fun make_function_definitions (cse : ProgramAnalysis.csenv)
                              (styargs : typ list)
                              (fninfo_cliques : fninfo list list)
                              translate_body
                              globloc
                              globals_elems
                              prog_name
                              lthy =
let
  val informStr = Feedback.informStr lthy
  open HoarePackage

  val gamma = HP_TermsTypes.mk_gamma lthy prog_name
  val gammaT = fastype_of gamma
  val opt_comT = range_type gammaT
  val comT = IsabelleTermsTypes.dest_option_ty opt_comT

  val fninfos = flat fninfo_cliques;

  val name_pars =
      map (fn {fname,inparams,outparams,recursivep,...} =>
                [(fname, recursivep, inparams, outparams),
                  (Long_Name.qualify prog_name fname, recursivep, inparams, outparams)])
          fninfos |> flat
  val name_specs = map (fn {fname,spec,...} => (fname,spec)) fninfos

  val lthy = List.foldr (uncurry add_syntax) lthy name_pars (* TODO *)
  (* make a function for a single definition thy\<rightarrow> thy which will change into the
     locale context first
  *)

  val globs = extract_fixes globals_elems
  fun define_body (f as {fname, body, mod_annotated_protop,...}:fninfo) thy =
    let
      fun translate lthy = case body of
            SOME (BodyTerm (StmtDecl.FnDefn fndefn)) => SOME (translate_body lthy fndefn)
          | NONE => if mod_annotated_protop then SOME (mkSpecFunction lthy cse styargs f) else NONE
          | _ => error ("define_body: neither prototype nor body found for '" ^ fname ^ "'")

      val vars_bundle = NameGeneration.intern_variables_bundle_name thy fname
      datatype 'e def_info = Def of 'e | Decl of string 
      fun def e =
        let
          val _ = Feedback.informStr lthy (1, "Adding body_def for " ^ Binding.name_of (#1 (#1 e)))
        in Local_Theory.define e #> snd end
      fun decl name lthy =
        let
          val _ = Feedback.informStr lthy (1, "Adding body declaration for " ^ name)
        in
          lthy |> Local_Theory.background_theory 
            (Sign.declare_const_global (((Binding.make (name ^ "_body", \<^here>), comT)), Mixfix.NoSyn)  
            #> snd)
        end
      fun decl_or_defs (Def es) lthy = fold def es lthy
        | decl_or_defs (Decl n) lthy = decl n lthy
 
      fun def_elem lthy =
        let
          val defines =            
            translate lthy
            |> Option.map (create_bodyloc_elems globs lthy #> fst #> Def)
            |> the_default (Decl fname)
        in decl_or_defs defines lthy end
    in
      thy
      |> Named_Target.theory_init
      |> Local_Theory.begin_nested |> snd
      |> Bundle.unbundle [(true, vars_bundle)] 
      |> def_elem 
      |> Local_Theory.end_nested
      |> Local_Theory.exit_global
    end


  val lthy = lthy |> More_Local_Theory.in_theory (
       fold define_body fninfos) (* fold_join_thy, seems to be less efficient for large number of functions *)

  val _ = Feedback.informStr lthy (0, "Translated all functions")

  fun define_gamma_and_interprete_progL thy =
    let
      val ctxt = Proof_Context.init_global thy
      val gamma_fullN = dest_Const gamma |> fst
      val gammaN = Long_Name.base_name gamma_fullN 
      fun mk_free (Const (x, T)) = Free (Long_Name.base_name x, T)
      fun fn_ptr fname = Proof_Context.read_const {proper=true, strict=false} ctxt 
        (Long_Name.qualify prog_name (NameGeneration.fun_ptr_name fname))
      fun fn_body fname = Proof_Context.read_const {proper=true, strict=false} ctxt (fname ^ "_body")
      fun mk_bdy {fname,...} =
        case try fn_body fname of
          SOME bdy => \<^instantiate>\<open>'a = comT and bdy = bdy in term \<open>Some bdy\<close>\<close>
        | NONE => \<^Const>\<open>None comT\<close>

      fun mk_ptr {fname, ...} = fn_ptr fname
      fun mk_pair x y = \<^infer_instantiate>\<open>x = x and y = y in term \<open>(x, y)\<close>\<close> ctxt
      fun mk_assoc fninfo = mk_pair (mk_ptr fninfo) (mk_bdy fninfo)
      fun mk_fun_ptr_eq fninfo = (#fname fninfo, HOLogic.Trueprop $ (HOLogic.mk_eq (gamma $ mk_ptr fninfo, mk_bdy fninfo)))
      val fun_ptr_eqs = map mk_fun_ptr_eq fninfos
      val xs = map mk_assoc fninfos |> HOLogic.mk_list (HOLogic.mk_prodT (@{typ "unit ptr"}, opt_comT))
      val rhs = \<^instantiate>\<open>'a = comT and xs = xs in term \<open>map_of_default (\<lambda>_::unit ptr. None) xs\<close>\<close>
      val eq = Logic.mk_equals (mk_free gamma, rhs)
      fun define lthy =
        let
          val _ = Feedback.informStr ctxt (0, "defining \<Gamma>")
          val ((_,(_, def_eq)), lthy') = 
             Specification.definition NONE [] [] ((Binding.empty, []), eq) lthy
          val _ = Feedback.informStr ctxt (2, Thm.string_of_thm lthy' def_eq)
        in (def_eq, lthy') end

      fun prove_and_note_fun_ptr_simps def_eq thy =
        let
          val lthy = thy |> Named_Target.init [] globloc
          val eqs = Named_Bindings.get_thms lthy @{named_bindings fun_ptr_map_of_default_eqs}
          val disj_G_S = Named_Theorems.get lthy @{named_theorems disjoint_\<G>_\<S>}
          val simp_ctxt = lthy 
            |> Simplifier.add_simps (def_eq :: disj_G_S @ eqs)
            |> Simplifier.del_simps @{thms map_of_default.simps}
          val fun_ptr_thms = Utils.timeit_label 3 lthy "fun_ptr_thms" (fn _ => 
            map snd fun_ptr_eqs |> map (fn prop => prove' lthy [] [] prop (fn {context, ...} => 
                asm_full_simp_tac simp_ctxt 1)))
          val eqs = (map fst fun_ptr_eqs) ~~ fun_ptr_thms
          val implN = NameGeneration.impl_locale_name; (* NB: this theorem name is used by Hoare tactic in modifies proof *)
          val notes_data = map (fn (fname, thm) => ((Binding.make (implN fname, \<^here>), []), [thm])) eqs
          val (_, lthy) = lthy 
            |> fold_map (Local_Theory.note) notes_data
            ||> Named_Bindings.binding_declarations (map (fst o fst) notes_data, [@{named_bindings fun_ptr_simps}])
        in lthy |> Local_Theory.exit_global end
    in 
      thy 
      |> Overloading.theory_map_result [(gammaN, (gamma_fullN, gammaT), true)] Morphism.thm define
      |> (fn (def_eq, thy) => prove_and_note_fun_ptr_simps def_eq thy)
    end

  val lthy = lthy 
    |> Config.get lthy Utils.define_gamma ? 
        More_Local_Theory.in_theory (define_gamma_and_interprete_progL)

  (* Speclocale imports sigN*)

  (* three levels of folding - woohoo *)
  fun add_spec_locales (name,specs) (localemap, thy) = let
    (* add any spec locales *)
    fun foldthis (_, e) (localemap, thy) = let
      val lnm_strs = extract_element_asms e
      fun innerfold ((speclocalename_b,_), tstr) (localemap, thy) = let
        val speclocalename = Binding.name_of speclocalename_b
        val vars_bundle = NameGeneration.intern_variables_bundle_name thy name
        (* jump into an sig_locale corresponding to globloc to parse the tstr; this lthy
           is dropped and not used again *)
        val lthy = Named_Target.init [(true, vars_bundle)] globloc thy
        val t = Syntax.read_term lthy tstr
        val _ = informStr (0, "Adding spec locale "^speclocalename^
                         (if speclocalename = "" then "" else " ")^
                         "for function "^name ^ " (" ^ tstr ^ ")")
        val e' = Element.Assumes [((speclocalename_b,[]),
                                   [(TermsTypes.mk_prop t, [])])]
        val speclocalename_b = Binding.map_name
                                   (fn s => if s = "" then
                                              suffix HoarePackage.specL name
                                            else s)
                                   speclocalename_b
        val (locname, lthy) = thy
            |> add_locale speclocalename_b speclocalename_b
                 (map (import [] thy) [globloc], [])
                 [e']
            ||> Bundle.unbundle [(true, vars_bundle)]

        (* localename is the name we wanted, locname is the name Isabelle
           gives back to us.  This will be properly qualified yadda yadda *)
      in
        (Symtab.update (speclocalename, locname) localemap,
         Local_Theory.exit_global lthy)
      end
    in
      (localemap, thy) |> fold innerfold lnm_strs
    end
    val (speclocnames,thy) = (localemap, thy) |> fold foldthis specs
  in
    (speclocnames, thy)
  end

  val (speclocnames, lthy) = lthy
    |> More_Local_Theory.in_theory_result
      (fn thy => (Symtab.empty, thy) |> fold add_spec_locales name_specs)


in
  (Symtab.keys speclocnames, lthy)
end


end (* struct *)
