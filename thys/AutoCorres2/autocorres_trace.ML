(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Functions to perform tracing of AutoCorres's proof steps.
 * Also includes some utilities for printing the traces.
 * The theory data for recording traces is defined in AutoCorresData.
 * See tests/examples/TraceDemo.thy for an output example.
 *)
signature AUTOCORRES_TRACE = sig

  val trace_solve_prove:
        Proof.context ->
        bool ->
        (Proof.context -> cterm -> (thm * tactic) list) ->
        int option ->
        thm ->
        thm 

  val fconv_rule_traced:
        Proof.context -> (cterm -> thm) -> thm -> thm 
  val fconv_rule_maybe_traced:
        Proof.context -> (cterm -> thm) -> thm -> bool -> thm 


  val rules_tac: Proof.context -> thm list -> int -> (thm * tactic) list

  val get_trace_info_msg: Proof.context -> string
  val put_trace_info: string -> FunctionInfo.phase -> FunctionInfo.stage -> Proof.context -> Proof.context
  val put_trace_info_function: string -> Proof.context -> Proof.context
  val put_trace_info_phase: FunctionInfo.phase -> Proof.context -> Proof.context 
  val put_trace_info_stage: FunctionInfo.stage -> Proof.context -> Proof.context 

  val transfer_trace_info: Proof.context -> Proof.context -> Proof.context

  val dest_trace_info: {function: string, phase: FunctionInfo.phase, stage: FunctionInfo.stage} -> 
    (string * FunctionInfo.phase * FunctionInfo.stage)
  val mk_trace_info: string -> FunctionInfo.phase -> FunctionInfo.stage -> 
    {function: string, phase: FunctionInfo.phase, stage: FunctionInfo.stage}

  val timeit_trace_msg:  int -> Proof.context -> string -> cterm -> (unit -> 'a) -> 'a;
  val timeit_trace_conv: int -> Proof.context -> string -> cterm -> conv -> thm;

  val print_resolve_tac: (term -> bool) -> string -> Proof.context -> thm -> int -> tactic;

  val mk_resolve_match_rules: (Context.generic -> (int -> term -> term) list) -> Context.generic ->
        thm list -> int -> Proof.context -> cterm -> (thm * tactic) list
                                   
  structure ProfileConv:
    sig
      structure Prf_Data: PROOF_DATA
      structure Table: TABLE
      structure Thy_Data: THEORY_DATA
      val enabled: bool Config.T
      val get: Proof.context -> (Timing.timing * (cterm * thm)) Table.table
      val lookup: Proof.context -> Table.key -> (Timing.timing * (cterm * thm)) option
      val timeit: Proof.context -> Table.key option -> (cterm -> thm) -> cterm -> thm
      val tracing_msg:
         Proof.context -> (string * FunctionInfo.phase * FunctionInfo.stage) option -> Timing.timing -> cterm -> thm -> unit
      val transfer: Proof.context -> theory -> theory
      val verbosity: int Config.T
    end

  structure Statistics:
    sig
      val changed: ('a * ('b * ('c * thm))) list -> ('a * ('b * ('c * thm))) list
      val changed_eq: 'a * ('b * ('c * thm)) -> bool
      val changed_thm: thm -> bool
      val group_name: ('a -> string) -> 'a list -> string
      val name_of: ('a * 'b * 'c) * 'd -> 'a
      val names: ((''a * 'b * 'c) * 'd) list -> ''a list
      val phase_of: ('a * 'b * 'c) * 'd -> 'b
      val phases: (('a * ''b * 'c) * 'd) list -> ''b list
      val same_name: ''a -> (''a * 'b * 'c) * 'd -> bool
      val same_phase: ''a -> ('b * ''a * 'c) * 'd -> bool
      val same_stage: ''a -> ('b * 'c * ''a) * 'd -> bool
      val select: 'a list -> ('a -> bool) -> 'a list
      val stage_of: ('a * 'b * 'c) * 'd -> 'c
      val stages: (('a * 'b * ''c) * 'd) list -> ''c list
      val statistics:
         ((string * FunctionInfo.phase * FunctionInfo.stage) *
          ({cpu: Time.time, elapsed: Time.time, gc: Time.time} * ('a * thm))
         )
         list
           -> unit
      val timesum:
         ('a * ({cpu: Time.time, elapsed: Time.time, gc: Time.time} * 'b)) list ->
           {cpu: Time.time, elapsed: Time.time, gc: Time.time}
      val timing_add:
         {cpu: Time.time, elapsed: Time.time, gc: Time.time} ->
           {cpu: Time.time, elapsed: Time.time, gc: Time.time} ->
             {cpu: Time.time, elapsed: Time.time, gc: Time.time}
      val unchanged: ('a * ('b * ('c * thm))) list -> ('a * ('b * ('c * thm))) list
      val unchanged_eq: 'a * ('b * ('c * thm)) -> bool
      val unchanged_thm: thm -> bool
    end
end;

structure AutoCorresTrace: AUTOCORRES_TRACE = struct

val verbose_msg = Utils.verbose_msg
val verbose_msg_tac = Utils.verbose_msg_tac
(*
 * Custom unifier for trace_solve_tac.
 * Isabelle's built-in unifier has several problems:
 * 1. It gives up when the unifications become "complicated", even if it is
 *    only due to variables needing large instantiations.
 *    This happens for trace_solve_tac because it unifies subgoals with subgoal proofs,
 *    thus it may instantiate a variable to an entire program term.
 *    We can fall back to tactics replay when this happens, but we would rather not
 *    at the top levels (which is when this problem occurs), as it involves replaying
 *    large branches of the proof tree.
 *
 * 2. When it gives up, it produces a lot of tracing output.
 *    This tracing is a global option, so we cannot turn it off in the local context.
 *    The volume of tracing invariably causes Isabelle/jEdit's poorly-written GUI to lock up.
 *
 * This unifier is less general, but should work for AutoCorres's purposes.
 * It unifies terms t and t', where t' is assumed to be fully concrete (the subgoal proof).
 * Schematic variables in t, including functions, are instantiated by substituting them with
 * the corresponding subterm in t'. We assume that schematic variables do not have schematic
 * arguments. (fixme: add this test)
 * We also do some instantiations of schematic type variables in t, because it's currently needed
 * by WordAbstract. We assume that the type vars are never applied to arguments.
 *)

(* generalised Term.lambda *)
fun my_lambda args =
  let val n = length args
      fun lambda' depth args t =
        (case Utils.findIndex (fn (a, _) => a = t) args of
            NONE =>
              (case t of
                  f $ x => lambda' depth args f $ lambda' depth args x
                | Abs (v, typ, t) => Abs (v, typ, lambda' (depth + 1) (map (apfst (incr_boundvars 1)) args) t)
                | Bound k => if k >= depth then Bound (k + n) else Bound k
                | _ => t)
          | SOME (_, k) => Bound (k + depth))
  in lambda' 0 (rev args)
     #> fold (fn (_, (name, typ)) => fn t => Abs (name, typ, t)) (rev args)
  end

fun subterm_type absvars t = let
  fun subst absvars (Bound k) = Free (nth absvars k)
    | subst absvars (f $ x) = subst absvars f $ subst absvars x
    | subst absvars (Abs (v, typ, t)) = Abs (v, typ, subst ((v, typ) :: absvars) t)
    | subst _ t = t
  in fastype_of (subst absvars t) end
fun my_typ_insts (Type (_, args)) (Type (_, args')) =
    if length args <> length args' then NONE else
    let val instss = Utils.zipWith my_typ_insts args args'
    in if exists (not o is_some) instss then NONE else
         SOME (List.mapPartial I instss |> List.concat) end
  | my_typ_insts (TFree _) (TFree _) = SOME []
  | my_typ_insts (TVar tv) typ = SOME [(tv, typ)]
  | my_typ_insts _ _ = NONE
fun my_typ_match' absvars (t as f $ x) t' =
      (case strip_comb t of
          (Var _, _) => my_typ_insts (subterm_type absvars t) (subterm_type absvars t')
        | _ => (case t' of
                   f' $ x' => (case (my_typ_match' absvars f f', my_typ_match' absvars x x') of
                                  (SOME fmatch, SOME xmatch) => SOME (fmatch @ xmatch)
                                | _ => NONE)
                 | _ => NONE))
  | my_typ_match' absvars (Abs (_, typ, t)) (Abs (v', typ', t')) =
      (case (my_typ_insts typ typ', my_typ_match' ((v', typ') :: absvars) t t') of
          (SOME absmatch, SOME tmatch) => SOME (absmatch @ tmatch)
        | _ => NONE)
  | my_typ_match' absvars t t' = case my_typ_insts (subterm_type absvars t) (subterm_type absvars t') of
       SOME x => SOME x
     | NONE => raise TYPE ("my_typ_insts fail", [subterm_type absvars t, subterm_type absvars t'], [t, t'])
fun my_typ_match t t' = my_typ_match' [] (Envir.beta_norm t) t'
                        handle TYPE (msg, typs, terms) => raise TYPE (msg, typs, terms @ [t, t'])

fun annotate_boundvar _ absvars (Bound n) =
      if n < length absvars then (Bound n, nth absvars n)
        else raise TYPE ("annotate_boundvar", map snd absvars, [Bound n])
  | annotate_boundvar _ _ (t as Free (name, typ)) = (t, (name, typ))
  | annotate_boundvar i absvars t = (t, ("var" ^ Int.toString i, subterm_type absvars t))
fun my_match' _ (Var v) t' = SOME [(v, [], t')]
  | my_match' absvars (t as f $ x) t' =
      (case strip_comb t of
          (Var v, args) => SOME [(v, map (fn (i, arg) => annotate_boundvar i absvars arg)
                                         (Utils.enumerate args), t')]
        | _ => (case t' of
                   f' $ x' => (case (my_match' absvars f f', my_match' absvars x x') of
                                  (SOME uf, SOME ux) => SOME (uf @ ux)
                                | _ => NONE)
                 | _ => NONE))
  | my_match' absvars (Abs (name, typ, t)) (Abs (_, typ', t')) =
      if typ = typ' then my_match' ((name, typ)::absvars) t t' else NONE
  | my_match' absvars t t' = if t = t' then SOME [] else NONE
fun my_match t t' = my_match' [] (Envir.beta_norm t) t'

fun my_unify_fact_tac ctxt subproof n state =
  let val cterm_of' = Thm.cterm_of ctxt
      val ctyp_of' = Thm.ctyp_of ctxt
  in
  if length (Thm.prems_of state) < n then no_tac state else
  let val stateterm = nth (Thm.prems_of state) (n-1)
      val proofterm = Thm.prop_of subproof
  in
  case my_typ_match stateterm proofterm of
     NONE => Seq.empty
   | SOME typinsts =>
     \<^try>\<open>case Thm.instantiate (TVars.make (map (fn (v, t) => (v, ctyp_of' t)) (Utils.nubBy fst typinsts)), Vars.empty) state of
       state' =>
        let val stateterm' = nth (Thm.prems_of state') (n-1) in
        case my_match stateterm' proofterm of
           NONE => Seq.empty
         | SOME substs =>
            \<^try>\<open>
             let val substs' = Utils.nubBy #1 substs
                               |> map (fn (var, args, t') => (var, my_lambda args t'))
                               |> map (fn (v, t) => (v, cterm_of' t))
             in
             case Thm.instantiate (TVars.empty, Vars.make substs') state of state' =>
              \<^try>\<open>case Proof_Context.fact_tac ctxt [Variable.gen_all ctxt subproof] 1 state' |> Seq.pull of
                   NONE => Seq.empty
                 | r => Seq.make (fn () => r)
             catch _ => Seq.empty\<close>
             end
       catch _ => Seq.empty\<close>
      end
      catch _ => Seq.empty\<close>
  end
  end


datatype 'a RuleTrace = RuleTrace of {
    input: cterm,
    step: 'a * tactic,
    output: thm,
    trace: 'a RuleTrace list
    }

fun trace_steps (RuleTrace tr) = #step tr :: List.concat (map trace_steps (#trace tr))

fun dest_rule_comb (Const (@{const_name "Trueprop"}, _) $ t) = dest_rule_comb t
  | dest_rule_comb t = dest_rule_comb (Logic.dest_all_global t |> snd)
                       handle TERM _ => strip_comb t
fun get_rule_abstract t = dest_rule_comb t |> snd |> (fn args => nth args (length args - 2))

exception TRACE_SOLVE_TAC_FAIL of (thm * thm) list


fun print_term_tac err thm msg ctxt t st = 
  let 
    val _ = tracing (msg ^ Pretty.string_of (Syntax.pretty_term ctxt t))
    val _ = if err t then raise TRACE_SOLVE_TAC_FAIL [(st,thm)] else () 
  in all_tac st end
      
fun print_resolve_tac err msg ctxt thm = SUBGOAL (fn (t,i) => 
  EVERY [resolve_tac ctxt [thm] i, print_term_tac err thm msg ctxt t]
  ) 

fun rtac_of ctxt n ((i, all), rule) =
  let
    val consumes = Rule_Cases.get_consumes rule
    val (rtac, consumes) = if consumes > 0 then (eresolve_tac, consumes - 1) else (resolve_tac, consumes)
  in
    Utils.trace_if_success ctxt rule (
       DETERM (EVERY' (
         [rtac ctxt [rule]] @
         replicate consumes (assume_tac ctxt) @
         [K (verbose_msg_tac 2 ctxt (fn level =>  
           let val rule_str = if level <= 3 then string_of_int i else string_of_int i ^ ": " ^ Thm.string_of_thm ctxt rule
           in "rtac_of: rule (consumes " ^ string_of_int consumes ^ ") " ^  rule_str ^ " of " ^ string_of_int all ^ " resolved subgoal" end))]) n))
  end

fun number xs = 
  let
    val all = length xs
  in ((all,all), []) 
     |> fold_rev (fn x => fn ((i, all), xs) => ((i-1, all), ((i, all), x)::xs)) xs
     |> snd
   
  end

fun rules_tac ctxt rules n =
  let 
    val all = length rules
  in 
    map (fn ((i, all), rule) => (rule, rtac_of ctxt n ((i,all), rule))) (number rules) @
    [(@{thm HOL.FalseE}, 
      Utils.verbose_print_subgoal_tac 2 ("rules_tac: none of " ^ string_of_int all ^ " rules did apply.") ctxt 1 
      THEN no_tac)]
  end

fun resolve_match_rules mk_pattern (rule_net, raw_rules) = (fn i => fn ctxt => fn ct =>
  let
    val maxidx = Thm.maxidx_of_cterm ct
    val t = Thm.term_of ct
    val concl = Utils.concl_of_subgoal_open t |> mk_pattern maxidx
  in
    case Item_Net.retrieve_matching rule_net concl of
      [] => (verbose_msg 2 ctxt (fn _ => "resolve_match_rules: no match found in net - falling back to raw rules - for:\n " ^ 
              Pretty.string_of (Syntax.pretty_term ctxt concl)); rules_tac ctxt raw_rules i)
    | rs => 
       let
         val n = length rs
         val _ = verbose_msg 2 ctxt (fn level => "resolve_match_rules: found " ^ string_of_int n ^ 
             " potentially matching rules " ^ 
             (if level <= 3 then "" else "\n" ^ 
                Utils.big_list_of_thms "rules:" ctxt rs ^ "\n" ^
                " concl: " ^ Pretty.string_of (Syntax.pretty_term ctxt concl)))
       in rules_tac ctxt rs i end
  end)

fun try_pattern maxidx mk_pattern t =
  let 
    val p = mk_pattern maxidx t
  in SOME p end
  handle Match => NONE

fun try_make_pattern maxidx [] t = NONE
  | try_make_pattern maxidx (mk_pattern::mk_patterns) t = 
      case try_pattern maxidx mk_pattern t of
        SOME p => SOME p
      | NONE => try_make_pattern maxidx mk_patterns t

fun make_pattern maxidx mk_patterns t = the_default t (try_make_pattern maxidx mk_patterns t)

fun insert_rule ctxt mk_patterns rule (rule_net, raw_rules) =
  let
    val concl = Thm.concl_of rule
  in
   case try_make_pattern (~1) mk_patterns concl of
     SOME p => 
       let 
         val _ = verbose_msg 1 ctxt (fn _ => "adding rule for pattern: " ^ 
                   Pretty.string_of (Syntax.pretty_term ctxt p) ^ "\n rule: " ^
                   Pretty.string_of (Thm.pretty_thm ctxt rule))
         val _ = case Item_Net.retrieve_matching rule_net p of
                   [] => ()
                  | rs => verbose_msg 1 ctxt (fn _ =>  
                       Utils.big_list_of_thms "the following rules match the same pattern:" ctxt rs)
       in       
         (Item_Net.update rule rule_net, raw_rules)
       end
    | NONE => 
        let
          val _ = verbose_msg 1 ctxt (fn _ => "no custom pattern for rule found, taking rule as is: " ^ @{make_string} rule)
        in 
          (rule_net, rule :: raw_rules) 
        end
  end

(* Resolution with a set of rules. The rules are preprocessed into a term-net to narrow down
  the applicable rules. The function get_patterns is used to derive the index of the net. It is
  used both for building the term-net and for retrieval of a rule for a given goal. 
  In case the term-net does not find any matching rule, 
  the remaining rules (not covered by get_patterns) are tried sequentially,  
*)
fun mk_resolve_match_rules get_patterns context rules =
 let
   val mk_patterns = get_patterns context
   val ctxt = Context.proof_of context
   val index = Thm.concl_of #> try_make_pattern (~1) mk_patterns #> the_list   
   val empty_net = Item_Net.init Thm.eq_thm_prop index
   val (net, rules') = fold (insert_rule ctxt mk_patterns) (rules) (empty_net, [])
   val rules' = distinct (Thm.eq_thm_prop) rules'
   val n = length rules'
   val _ = if n = 0 then () else verbose_msg 1 ctxt (fn _ => Utils.big_list_of_thms
        ("the following " ^ string_of_int n ^ " rules are not in the term-net, and will be applied consecutively as is (raw rules):")  
         ctxt rules') 
   fun mk_pattern maxidx = make_pattern maxidx mk_patterns
 in resolve_match_rules mk_pattern (net, rules') end

(* cf comment on trace_solve_tac for description *)
fun fast_solve_tac (ctxt : Proof.context)
                   (backtrack : bool)
                   (get_tacs : Proof.context -> cterm -> (thm * tactic) list)
                   (depth : int option)
                   (num_subgoals : int)
                   (st : thm)
                   : thm option =
  let val n = Thm.nprems_of st
      val msg = "fast_solve_tac (depth = " ^ @{make_string} depth  ^ ", subgoals = " ^ string_of_int n ^ ")"
      fun timeap_tac tag = Utils.timeap_msg_tac 2 ctxt (fn _ => msg ^ "\n " ^ Utils.string_of_rule ctxt tag)
      val timeap = Utils.timeap_msg 2 ctxt (fn _ => msg ^ " get_tac:")
      val ctxt' = Utils.inc_indent 2 ctxt
      fun try [] = if backtrack then NONE else raise TRACE_SOLVE_TAC_FAIL [(st, @{thm reflexive})]
        | try ((tag, tactic) :: rules_rest) =
            case timeap_tac tag tactic st |> Seq.pull of
                NONE => try rules_rest
              | SOME (next, _) =>
                let 
                  val m = Thm.nprems_of next
                  val fresh_goals = m - n + 1
                in
                  if fresh_goals = 0
                  then
                    (* next subgoal on same level *)
                    fast_solve_tac ctxt' backtrack get_tacs depth (num_subgoals - 1) next 
                  else if fresh_goals > 0
                  then 
                    (* recursively solve fresh subgoals *)
                    case fast_solve_tac ctxt' backtrack get_tacs (Option.map (fn d => d - 1) depth) fresh_goals next
                           handle TRACE_SOLVE_TAC_FAIL tr => raise TRACE_SOLVE_TAC_FAIL ((st, tag) :: tr) of
                      NONE => if backtrack 
                              then (Utils.timing_msg 2 ctxt (fn _ => msg ^ ": backtracking"); try rules_rest) 
                              else raise TRACE_SOLVE_TAC_FAIL [(st, tag), (next, @{thm reflexive})]
                    | SOME next => 
                         (* solve remaining subgoals on same level *)
                         fast_solve_tac ctxt' backtrack get_tacs depth (num_subgoals - 1) next
                  else (warning "fast_solve_tac: tactic solved more than first subgoal"; 
                        raise TRACE_SOLVE_TAC_FAIL [(st, tag), (next, @{thm reflexive})])
                end
  in if depth = SOME 0 then (warning "fast_solve_tac giving up: depth limit reached"; raise TRACE_SOLVE_TAC_FAIL [(st, @{thm reflexive})]) else
     if n = 0 orelse num_subgoals <= 0 then SOME st else
       let
         val _ = Utils.verbose_print_subgoal_tac 4 "fast_solve_tac" ctxt 1 st
         val _ = Utils.verbose_print_maingoal_tac 5 "fast_solve_tac" ctxt st
       in try (timeap (get_tacs ctxt) (Thm.cprem_of st 1)) end
  end

fun pretty_TRACE_SOLVE_TAC_FAIL ctxt ts =
  let
    fun pretty_state st = Syntax.pretty_term ctxt (Thm.term_of (Thm.cprem_of st 1))
    fun pretty_tag thm = Thm.pretty_thm ctxt thm
    fun pretty_tuple (step, (st, rule_tag)) = Pretty.block ( 
          [Pretty.str ("step " ^ (string_of_int step) ^ ": "), Pretty.fbrk] @
          (Pretty.commas [ 
            Pretty.block [Pretty.str "tag: ", pretty_tag rule_tag], 
            Pretty.block [Pretty.str "headgoal: ", pretty_state st]]))

    fun pretty_goal st = Pretty.block [Pretty.str "goal: ", Syntax.pretty_term ctxt (Thm.concl_of st)]
  in
    Pretty.chunks (
     [Pretty.str "TRACE_SOLVE_TAC_FAIL ", pretty_goal (fst (hd ts))] @
     Pretty.breaks (map pretty_tuple (rev (tag_list 1 ts))))
  end

(*
 * Tactic that generalises the idea of recursively applying intro rules
 * to a goal (e.g. to synthesise a schematic variable). 
 *
 * The 'rules' are specified by the parameter get_tacs and are recursively applied 
 * to all subgoals of a proof state:
 * 
 *    get_tacs: Proof_context -> cterm -> (thm * tactic) list
 * 
 * It is assumed that each of the tactics given, operates only on the first subgoal 
 * (presented as cterm) and may *deterministically* either 
 *   - fail (empty result sequence)
 *   - or generate zero subgoals, meaning the first subgoal is (solved) 
 *   - or 1 ore more subgoals, meaning that the first subgoal was refined
 * 
 * The thm is merely used for tracing purposes as a tag for the tactic.
 *
 * depth specifies an optional depth limit for the recursion.
 *
 * The backtrack flag indicates whether another tactic in the list is tried when we fail
 * to prove the first subgoal by recursive application. So the list is conceptually a
 * ORELSE for the current depth.
 * 
 *
 * Reports timing and tracing information, depending on configuration options 
 * autocorres_timing and autocorres_verbose.
 *
 *
 *)
fun trace_solve_prove (ctxt : Proof.context)
                      (backtrack : bool)
                      (get_tacs : Proof.context -> cterm -> (thm * tactic) list)
                      (depth : int option)
                      (st : thm)
                      : thm =
  case fast_solve_tac ctxt backtrack get_tacs depth 1 st of
    SOME st' => Goal.finish ctxt st'
   | NONE => error ("trace_solve_prove could not prove: " ^ Thm.string_of_thm ctxt st)
  handle TRACE_SOLVE_TAC_FAIL ts => 
    error (Pretty.string_of (pretty_TRACE_SOLVE_TAC_FAIL ctxt ts))


structure TraceInfo = AC_Proof_Data (
  type T = {function:string, phase:FunctionInfo.phase, stage: FunctionInfo.stage} option
  val init = K NONE;
)

val transfer_trace_info = TraceInfo.transfer;

fun get_trace_info_msg ctxt = 
  case TraceInfo.get ctxt of 
    NONE => ""
  | SOME {function, phase, stage } => FunctionInfo.string_of_phase phase ^ " " ^ function;

fun put_trace_info function phase stage =
  TraceInfo.map (fn _ => SOME {function=function, phase=phase, stage=stage});

fun put_trace_info_function x =
  TraceInfo.map (Option.map (fn {function, phase, stage} => {function=x, phase=phase, stage=stage}));

fun put_trace_info_phase x =
  TraceInfo.map (Option.map (fn {function, phase, stage} => {function=function, phase=x, stage=stage}));

fun put_trace_info_stage x =
  TraceInfo.map (Option.map (fn {function, phase, stage} => {function=function, phase=phase, stage=x}));

fun dest_trace_info {function, phase, stage} = (function, phase, stage);
fun mk_trace_info function phase stage = {function=function, phase=phase, stage=stage};


fun timeit_trace_msg level ctxt s (ct:cterm) x = 
  let
    fun msg {verbose,...} =  
      let    
        val info = get_trace_info_msg ctxt
        val s' = if s = "" then info else info ^ " " ^ enclose "(" ")" s;
        val res = if verbose >= 3 then s' ^ ": "  ^ Syntax.string_of_term ctxt (Thm.term_of ct) else s
      in res end
  in Utils.timeap_msg level ctxt msg x () end


fun timeit_trace_conv level ctxt s (ct:cterm) conv =
  let
    fun msg {verbose, output, ...} = 
      let    
        val info = get_trace_info_msg ctxt
        val s' = if s = "" then info else info ^ " " ^ enclose "(" ")" s;
        val rhs = Thm.rhs_of output |> Thm.term_of
        val res = if verbose >= 3 
          then s' ^ ": "  ^ @{make_string} ct ^ "\n simplified: " ^ Syntax.string_of_term ctxt rhs
          else s'
       in res end
  in Utils.timeap_msg level ctxt msg conv ct end


structure ProfileConv = Profile(
  structure Key = 
    struct 
      type key = string * FunctionInfo.phase * FunctionInfo.stage 
      val ord = triple_ord fast_string_ord FunctionInfo.phase_ord FunctionInfo.stage_ord
    end
  type from = cterm
  type to = thm
  val make_string_from = K (K "") (* All information of conversion is in result equation *)
  val make_string_to = K @{make_string}
  val make_string_key = (fn _ => fn (fname, phase, stage) => 
    fname ^ " (" ^ FunctionInfo.string_of_phase phase ^ " - " ^ FunctionInfo.string_of_stage stage ^ ")")  
  val name = "autocorres_profile_conversion"
);

structure Statistics = 
struct
  fun unchanged_thm thm = (Thm.term_of (Thm.lhs_of thm)) aconv (Thm.term_of (Thm.rhs_of thm))
  fun changed_thm thm = not (unchanged_thm thm)

  fun name_of ((n, _, _), _) = n;
  fun phase_of ((_, p, _), _) = p;
  fun stage_of ((_, _, s), _) = s;


  fun timing_add {elapsed = e1, cpu = c1, gc = g1} {elapsed = e2, cpu = c2, gc = g2} =
    {elapsed = Time.+ (e1,e2), cpu = Time.+ (c1,c2), gc = Time.+ (g1,  g2)};

  fun timesum ps =
    {elapsed=Time.zeroTime, cpu=Time.zeroTime, gc=Time.zeroTime} 
    |> fold (fn (_,(t1,_)) => fn t => timing_add t1 t) ps

  fun changed_eq (_, (_, (_, eq))) = changed_thm eq
  fun unchanged_eq (_, (_, (_, eq))) = unchanged_thm eq

  fun changed ps = filter changed_eq ps
  fun unchanged ps = filter unchanged_eq ps

  fun select ps p = filter p ps

  fun names ps = distinct (op =) (map name_of ps)
  fun phases ps = distinct (op =) (map phase_of ps) 
  fun stages ps = distinct (op =) (map stage_of ps) 

  fun same_name n e = name_of e = n
  fun same_phase p e = phase_of e = p
  fun same_stage s e = stage_of e = s

  fun group_name name ps = case ps of nil => "" | (p::_) => name p


  fun statistics ps = 
  let
    val grouped_by_name = map (select ps o same_name) (names ps)
    val grouped_by_phase = map (select ps o same_phase) (phases ps)
    val grouped_by_stage = map (select ps o same_stage) (stages ps)

    fun mk_entry (msg, ps) = (msg, length ps, timesum ps);
    fun mk_entry_msg (msg,len,timing) =
      msg ^ ": " ^ @{make_string} len ^ " (" ^ Timing.message timing ^  ")";
    
    fun mk_group name ps = (group_name name ps, 
      map mk_entry (["all","changed","unchanged"] ~~ [ps, changed ps, unchanged ps]));

    fun mk_group_msg (msg, xs) =
      cat_lines (
        ["=== " ^ msg ^ "==="] @ 
        map mk_entry_msg xs @ 
        ["-------------------------------------------"]
      );

    val stats = 
      [mk_group (K "overall") ps] @
      (map (mk_group name_of) grouped_by_name) @
      (map (mk_group (FunctionInfo.string_of_phase o phase_of)) grouped_by_phase) @
      (map (mk_group (FunctionInfo.string_of_stage o stage_of)) grouped_by_stage)     
  in 
    tracing (cat_lines (map mk_group_msg stats)) 
  end
end
                             
fun fconv_rule_traced ctxt conv thm =
  let val ct = Thm.cprop_of thm
      val maybe_key = Option.map dest_trace_info (TraceInfo.get ctxt)
      val eq_thm = ProfileConv.timeit ctxt maybe_key conv ct 
      val _ = verbose_msg 2 ctxt (fn _ => "fconv_rule_traced: " ^ Thm.string_of_thm ctxt eq_thm)
  in 
    if Thm.is_reflexive eq_thm then thm else Thm.equal_elim eq_thm thm (* Pure/conv.ML *)
  end

fun fconv_rule_maybe_traced ctxt conv thm do_trace =
  if do_trace then fconv_rule_traced ctxt conv thm 
              else Conv.fconv_rule conv thm


(* Display and debugging utils *)
local

fun print_term ctxt t =
  Pretty.pure_string_of (Syntax.pretty_term ctxt t)

fun print_ac_trace' indent (RuleTrace tr) =
  let
    val ctxt = ML_PP.toplevel_context ()
    val print_cterm = print_term ctxt o Thm.term_of
    val print_thm = print_term ctxt o Thm.prop_of
    val indent2 = indent ^ "  "
  in
    indent ^ "Subgoal: " ^ print_cterm (#input tr) ^ "\n" ^
    indent ^ "Output:  " ^ print_thm (#output tr) ^ "\n" ^
    (if null (#trace tr) then indent ^ "Proof: " ^ print_thm (#step tr |> fst) ^ "\n" else
       indent ^ "Proof:\n" ^
       indent2 ^ "Step: " ^ print_thm (#step tr |> fst) ^ "\n\n" ^
       cat_lines (map (print_ac_trace' indent2) (#trace tr)))
  end
in
val print_ac_trace = print_ac_trace' ""
end

end
