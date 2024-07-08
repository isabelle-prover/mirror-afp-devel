(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature MODIFIES_PROOFS =
sig

  type csenv = ProgramAnalysis.csenv
  val gen_modify_body : local_theory -> typ -> term -> term ->
                        ProgramAnalysis.modify_var list -> term
  (* [gen_modify_body thy ty s0 s vs]
     ty is the Isabelle type of the state
     s0 is an Isabelle var standing for the initial state
     s is an Isabelle var standing for the final state
     vs is the list of variables allowed to be modified.

     The "global exception" variable will automatically be added to the
     list of variables as something that can be modified.
  *)


  val gen_modify_goal : local_theory -> typ list -> term -> string ->
                        ProgramAnalysis.modify_var list -> term
  (* [gen_modify_goal thy tys tm fname vs]
     tys is the three types that are parameters to all HoarePackage constants
     tm is the \<Gamma> that houses the lookup table from fn names to bodies
     fname is the name of the function being called
     vs is the list of variables allowed to be modified.

     The "global exception" variable will automatically be added to the
     goal as something that can be modified.
  *)

  val gen_modify_goalstring : csenv -> string -> string list -> string

  val modifies_vcg_tactic : local_theory -> int -> tactic
  val modifies_tactic : bool -> thm -> local_theory -> tactic


  val prove_all_modifies_goals : csenv -> (string -> bool) ->
                                 typ list -> string -> string list list ->  theory -> theory
   (* string list list are the recursive cliques *)


  val sorry_modifies_proofs : bool Config.T
  val calculate_modifies_proofs : bool Config.T
end

structure Modifies_Proofs : MODIFIES_PROOFS =
struct

open TermsTypes
type csenv = ProgramAnalysis.csenv

(* Config item to determine if "modifies" thms should be generated. *)
val calculate_modifies_proofs =
  Attrib.setup_config_bool @{binding calculate_modifies_proofs} (K true)

val sorry_modifies_proofs =
  Attrib.setup_config_bool @{binding sorry_modifies_proofs} (K false);

fun put_conditional conf VAR ctxt =
  let
    val v = can getenv_strict VAR
    val ctxt' = Config.put_generic conf v ctxt
  in
    Output.tracing ("Set " ^ Config.name_of conf ^ " to " ^ Config.print_value (Config.Bool v));
    ctxt'
  end

fun cond_sorry_modifies_proofs VAR ctxt =
  let
    val ctxt' = put_conditional sorry_modifies_proofs VAR ctxt
  in
    if Config.get_generic ctxt' sorry_modifies_proofs andalso
       not (Config.get_generic ctxt' quick_and_dirty)
    then warning "Setting sorry_modifies_proofs without quick_and_dirty."
    else ();
    ctxt'
  end

fun gen_modify_goalstring csenv fname modstrings = let
  fun foldthis vname vset =
      case XMSymTab.lookup (ProgramAnalysis.get_addressed csenv) (MString.mk vname, NONE) of
        NONE => Binaryset.add(vset, vname)
      | SOME _ => Binaryset.add(vset, NameGeneration.global_heap)
  val vset = Binaryset.empty string_ord |> fold foldthis modstrings
in
    "\<forall>\<sigma>. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Call "^
    fname ^ "_'proc " ^
    "{t. t may_only_modify_globals \<sigma> in [" ^
    commas (Binaryset.listItems vset) ^ "]}"
end

fun mvar_to_string mv = let
  open ProgramAnalysis
in
  case mv of
    M vi => MString.dest (get_mname vi)
  | TheHeap => NameGeneration.global_heap
  | PhantomState => NameGeneration.phantom_state_name
  | GhostState => NameGeneration.ghost_state_name
  | AllGlobals => raise Match

end

fun gen_modify_body lthy state_ty sigma t mvars =
let
  val thy = Proof_Context.theory_of lthy
  val vars = map mvar_to_string mvars
  val vars = rev (sort_strings vars)
  val glob_ty =
      case state_ty of
          Type(@{type_name "StateSpace.state.state_ext"}, [g, _]) => g
        | _ => raise TYPE ("state_ty has unexpected form", [state_ty], [])
  val globals_name = @{const_name "globals"}
  val globals_t = Const(globals_name, state_ty --> glob_ty)
  val base_t = globals_t $ sigma
  fun gettypes v = let
    val vn = HoarePackage.varname v
    val qvn = "globals." ^ vn
    val fullvar_name = Sign.intern_const thy qvn
    val varaccessor_ty =
        the (Sign.const_type thy fullvar_name)
        handle Option => raise Fail ("Couldn't get type for constant "^
                                     fullvar_name)
    val (_, var_ty) = dom_rng varaccessor_ty
  in
    (vn, fullvar_name, var_ty)
  end
  val vartypes = map gettypes vars
  fun mk_update((var_name, fullvarname, var_ty), acc) = let
    val var_v = Free(var_name, var_ty)
    val updfn = mk_abs(Free("_", var_ty), var_v)
    val updator = Const(suffix Record.updateN fullvarname,
                        (var_ty --> var_ty) --> (glob_ty --> glob_ty))
  in
    updator $ updfn $ acc
  end
  val updated_t = List.foldr mk_update base_t vartypes
  val globals_tt = globals_t $ t
  val meq_t = Const(HoarePackage.modeqN, glob_ty --> glob_ty --> bool) $
              globals_tt $ updated_t
  fun mk_mex (var_name, _, var_ty) base = let
    val abs_t = mk_abs(Free(var_name, var_ty), base)
  in
    Const(HoarePackage.modexN, (var_ty --> bool) --> bool) $
    abs_t
  end
in
  meq_t |> fold mk_mex vartypes
end

fun gen_modify_goal_pair lthy tyargs gamma fname mvars = let
  val state_ty = hd tyargs
  val name_ty = List.nth(tyargs, 1)
  val com_ty = mk_com_ty tyargs
  val stateset_ty = mk_set_type state_ty
  val error_ty = List.nth(tyargs, 2)
  val sigma = Free("\<sigma>", state_ty)
  val t = Free("t", state_ty)

  val theta_element_ty =
      list_mk_prod_ty [stateset_ty, name_ty, stateset_ty, stateset_ty]
  val theta_ty = mk_set_type theta_element_ty
  val hoarep_t =
      Const(@{const_name "hoarep"},
            (name_ty --> mk_option_ty com_ty) -->
            theta_ty -->
            mk_set_type error_ty -->
            stateset_ty -->
            com_ty -->
            stateset_ty -->
            stateset_ty -->
            bool)
  val theta_t = mk_empty theta_element_ty
  val faults_t = mk_UNIV error_ty
  val pre_t = list_mk_set state_ty [sigma]
  val prog_t = Const(@{const_name "Language.com.Call"},
                     name_ty --> mk_com_ty tyargs) $
                HP_TermsTypes.mk_VCGfn_name lthy fname
  (* post_t is the complicated Collect term *)
  val post_t = let
    val mexxed_t = gen_modify_body lthy state_ty sigma t mvars
  in
    mk_collect_t state_ty $ mk_abs(t, mexxed_t)
  end
  val abr_t = post_t
  val goal_t = hoarep_t $ gamma $ theta_t $ faults_t $ pre_t $ prog_t $ post_t $ abr_t
in
  (mk_abs(sigma, post_t), mk_forall(sigma, goal_t))
end

fun gen_modify_goal lthy tyargs gamma fname mvars = let
  val (_, goal) = gen_modify_goal_pair lthy tyargs gamma fname mvars
in
  goal
end

fun munge_tactic ctxt goal msgf tac = let
  fun tacticfn {prems = _,context} st =
      if Config.get context sorry_modifies_proofs then
         if Config.get context quick_and_dirty
         then Skip_Proof.cheat_tac context 1 st
         else error "Can skip modifies-proofs only in quick-and-dirty mode."
      else
         tac context st
  fun tacticmsg st t = case Seq.pull (tacticfn st t) of
      NONE => Seq.empty
    | SOME (t, _) => (msgf (); Seq.single t)
in
  Goal.prove_future ctxt [] [] (TermsTypes.mk_prop goal) tacticmsg
end

val debug = false
fun debug_print_subgoal_tac msg ctxt i st =
      if debug then Utils.verbose_print_subgoal_tac 0 msg ctxt i st else all_tac st

fun modifies_vcg_tactic ctxt i st = let
  val _ = debug_print_subgoal_tac "modifies_vcg_tac:" ctxt i st
  val timer = Timer.startCPUTimer ()
  val tac = HoarePackage.vcg_tac "_modifies" "false" [] ctxt i
  val res = Seq.list_of (DETERM tac st)
  val {usr, sys} = Timer.checkCPUTimer timer
in
  Feedback.informStr ctxt (1, "modifies vcg-time:" ^ Time.fmt 2 (Time.+ (usr, sys)));
  Seq.of_list res
end

fun dest_modifies_inv_prop @{term_pat \<open>modifies_inv_prop ?P\<close>} = P
  | dest_modifies_inv_prop t = raise TERM("dest_modifies_inv_prop", [t])

fun gen_modifies_tactic heap hoare_proc_rule mod_inv_props lthy =
let
  val mod_inv_props = mod_inv_props |> sort_distinct Thm.thm_ord

  fun interprete (i, mod_inv_prop) state =
    let
      val ctxt = Proof.context_of state
      val P = dest_modifies_inv_prop (HOLogic.dest_Trueprop (Thm.prop_of mod_inv_prop))
      val expr =
        if heap then
          let
            val params = HP_TermsTypes.globals_stack_heap_raw_state_params State ctxt
            val ([hrs, hrs_upd, S]) = map Utils.dummy_schematic [#hrs params, #hrs_upd params, #S params]
          in ([(@{locale modifies_assertion_stack_heap_raw_state}, ((string_of_int i, false),
                     (Expression.Positional (map SOME ([P, hrs, hrs_upd, S])), [])))], [])
          end
        else
          ([(@{locale modifies_state_assertion}, ((string_of_int i, false),
                     (Expression.Positional (map SOME ([P])), [])))], [])

      val state' = state
        |> Interpretation.interpret expr
        |> Proof.local_terminal_proof ((Method.Basic (fn ctxt =>  SIMPLE_METHOD (
            (Locale.intro_locales_tac {strict = false, eager = true} ctxt [] THEN
              resolve_tac ctxt [mod_inv_prop] 1 THEN
              ALLGOALS (simp_tac (ctxt addsimps @{thms hrs_mem_update_def hrs_htd_update_def})) THEN
              ALLGOALS (Hoare.solve_modifies_tac ctxt
                (Hoare.get_default_state_kind ctxt) (K ~1))))),
            Position.no_range), NONE)
     in state' end

  val ctxt' = lthy |> Proof.init |> Proof.begin_block
    |> fold interprete (tag_list 1 mod_inv_props)
    |> Proof.context_of
  val mip_intros = Named_Theorems.get ctxt' @{named_theorems modifies_inv_intros}
  val gsurj = Proof_Context.get_thm lthy "globals.surjective"
  val geqs = map (fn t => [gsurj, gsurj] MRS t) @{thms asm_store_eq_helper}
  val gsp = Proof_Context.get_thms lthy "globals.splits"
  val solve_remaining_sideconditions =
        EVERY [
          ALLGOALS (clarsimp_tac lthy),
          ALLGOALS (TRY o resolve_tac lthy @{thms asm_spec_enabled}),
          ALLGOALS (clarsimp_tac
                      (lthy addSEs @{thms asm_specE state_eqE} addsimps (gsp @ @{thms state.splits}))),
          ALLGOALS (clarsimp_tac (lthy addsimps geqs)),
          ALLGOALS (TRY o REPEAT_ALL_NEW (resolve_tac lthy [exI])),
          ALLGOALS (asm_full_simp_tac lthy)
        ]
in
   (HoarePackage.hoare_rule_tac lthy [hoare_proc_rule] THEN_ALL_NEW
     (REPEAT_ALL_NEW (resolve_tac lthy (@{thms allI} @ mip_intros) ORELSE' modifies_vcg_tactic lthy))) 1 THEN
   solve_remaining_sideconditions
end


fun modifies_tactic heap mod_inv_prop  = gen_modifies_tactic heap @{thm HoarePartial.ProcNoRec1} [mod_inv_prop]

fun get_mod_inv_prop ctxt post_abs mod_inv_props = let
  fun prove_mod_inv_prop () = let
    val mi_prop_ty = fastype_of post_abs --> HOLogic.boolT
    fun mi_goal prop = HOLogic.mk_Trueprop (Const (prop, mi_prop_ty) $ post_abs)
    fun mi_prop_tac _ = let
      val globals_equality = Proof_Context.get_thm ctxt "globals.equality"
      fun mi_refl_tac _ =
        simp_tac (clear_simpset ctxt addsimps @{thms modifies_inv_refl_def mex_def meq_def}) 1 THEN
        resolve_tac ctxt @{thms allI} 1 THEN
        resolve_tac ctxt @{thms CollectI} 1 THEN
        TRY (REPEAT_ALL_NEW (resolve_tac ctxt @{thms exI}) 1) THEN
        resolve_tac ctxt [globals_equality] 1 THEN
        ALLGOALS (simp_tac (clear_simpset ctxt addsimprocs [Record.simproc]))
      fun mi_incl_tac _ =
        simp_tac (clear_simpset ctxt addsimps @{thms modifies_inv_incl_def mex_def meq_def}) 1 THEN
        resolve_tac ctxt @{thms allI} 1 THEN
        resolve_tac ctxt @{thms allI} 1 THEN
        resolve_tac ctxt @{thms impI} 1 THEN
        resolve_tac ctxt @{thms Collect_mono} 1 THEN
        TRY (REPEAT_ALL_NEW (resolve_tac ctxt @{thms ex_mono}) 1) THEN
        eresolve_tac ctxt @{thms CollectE} 1 THEN
        TRY (REPEAT_ALL_NEW (eresolve_tac ctxt @{thms exE}) 1) THEN
        clarsimp_tac ctxt 1
      val mi_refl = Goal.prove ctxt [] [] (mi_goal @{const_name modifies_inv_refl}) mi_refl_tac
      val mi_incl = Goal.prove ctxt [] [] (mi_goal @{const_name modifies_inv_incl}) mi_incl_tac
    in
      REPEAT_ALL_NEW (resolve_tac ctxt (mi_refl :: mi_incl :: @{thms modifies_inv_prop})) 1
    end
    val mi_prop = Goal.prove_future ctxt [] [] (mi_goal @{const_name modifies_inv_prop}) mi_prop_tac
  in
    (mi_prop, Termtab.update (post_abs, mi_prop) mod_inv_props)
  end
in
  case Termtab.lookup mod_inv_props post_abs of
      SOME mi_prop => (mi_prop, mod_inv_props)
    | NONE => prove_mod_inv_prop ()
end


fun prove_all_modifies_goals_local prog_name csenv includeP tyargs cliques thy =
  let
    open ProgramAnalysis
    val ctxt = Proof_Context.init_global thy
    val _ = Feedback.informStr ctxt (0, "Proving automatically calculated modifies proofs")
    val globs_all_addressed = Config.get ctxt CalculateState.globals_all_addressed
    val _ = Feedback.informStr ctxt (1, "Globals_all_addressed mode = " ^ Bool.toString globs_all_addressed)
    (* first enter the locale where \<Gamma> exists, and where all the
       mappings from function name to function body exist *)
    fun gamma_t ctxt = HP_TermsTypes.mk_gamma ctxt prog_name;


    val {callees,callers} = ProgramAnalysis.compute_callgraphs ctxt csenv

    fun do_one fname (failedsofar, mod_inv_props, thy) =
      let
        val lthy = Named_Target.init [] (NameGeneration.intern_impl_locale_name thy fname) thy
          |> Context_Position.set_visible false
        val _ = Feedback.informStr lthy (0, "Beginning modifies proof for singleton " ^ fname)
        val timer = Timer.startCPUTimer ()

        fun modifies_msg msg () = let
            val {usr, sys} = Timer.checkCPUTimer timer
          in
            Feedback.informStr lthy (1, "modifies:" ^ fname ^ ":" ^
                     Time.fmt 2 (Time.+ (usr, sys)) ^ "s:" ^ msg)
          end;
        val (failedsofar', mod_inv_props', lthy') =
          case get_fun_modifies csenv fname of
            NONE => (modifies_msg "can't do modifies proof" ();
                     (Binaryset.add(failedsofar,fname), mod_inv_props, lthy))
          | SOME mods =>
              let
                val mvlist = Binaryset.listItems mods
                val mvlist =
                    (* map globals to "TheHeap" if globals_all_addressed is true*)
                    if globs_all_addressed then map (fn M _ => TheHeap | x => x) mvlist
                    else mvlist
                val calls = case Symtab.lookup callees fname of
                              NONE => Binaryset.empty string_ord
                            | SOME s => s
                val i = Binaryset.intersection(calls, failedsofar)
              in
                if Binaryset.isEmpty i then let
                    val (post_abs, goal) = gen_modify_goal_pair lthy tyargs (gamma_t lthy) fname mvlist
                    val heap = exists (fn TheHeap => true | _ => false) mvlist
                    val (mod_inv_prop, mod_inv_props') = get_mod_inv_prop ctxt (*sic*) post_abs mod_inv_props
                    val th = munge_tactic lthy goal (modifies_msg "completed") (modifies_tactic heap mod_inv_prop)
                    val (_, lthy) = Local_Theory.note ((Binding.name (fname ^ "_modifies"), []), [th]) lthy

                  in
                    (failedsofar, mod_inv_props', lthy)
                  end
                else let
                    val example = the (Binaryset.find (fn _ => true) i)
                    val _ = modifies_msg
                                ("not attempted, as it calls a function ("
                                 ^ example ^ ") that has failed")
                  in
                    (Binaryset.add(failedsofar, fname), mod_inv_props, lthy)
                  end
              end
         val thy' = lthy' |> Local_Theory.exit_global
      in
        (failedsofar', mod_inv_props', thy')
      end

    exception NoMods of string Binaryset.set

    fun do_recgroup fnlist (failedsofar, mod_inv_props, thy) =
      let
        val ctxt = Proof_Context.init_global thy
        val n = length fnlist (* >= 1 *)

        val rec_thm = HoarePackage.gen_proc_rec ctxt HoarePackage.Partial n
        val mods = the (get_fun_modifies csenv (hd fnlist))
            handle Option => (Feedback.informStr ctxt (0, "No modifies info for "^hd fnlist);
                              raise NoMods (Binaryset.addList(failedsofar, fnlist)))
        val mvlist = Binaryset.listItems mods
        val heap = exists (fn TheHeap => true | _ => false) mvlist
        val lthy = Named_Target.init [] (NameGeneration.intern_impl_clique_locale_name thy fnlist) thy
          |> Context_Position.set_visible false
        fun gen_modgoal (fname : string) : (term * term) =
          let
            val calls = case Symtab.lookup callees fname of
                          NONE => raise Fail (fname ^ " part of clique, but \
                                                      \doesn't call anything??")
                        | SOME s => s
            val i = Binaryset.intersection(calls, failedsofar)
          in
            if Binaryset.isEmpty i then
              gen_modify_goal_pair lthy tyargs (gamma_t lthy) fname mvlist
            else let
                val example = the (Binaryset.find (fn _ => true) i)
                val _ = Feedback.informStr lthy (0, "Not attempting modifies proof for "^fname^
                                 " (or its recursive component) as it calls a\
                                 \ function ("^example^") that has failed")
              in
                raise NoMods (Binaryset.addList(failedsofar, fnlist))
              end
          end
        val (modifies_assertions, nway_goal) =  (map gen_modgoal fnlist) |> split_list |> apsnd list_mk_conj
        val modifies_assertions = map (fn assn => fst (get_mod_inv_prop ctxt (*sic*) assn mod_inv_props)) modifies_assertions
        fun tac ctxt = gen_modifies_tactic heap rec_thm modifies_assertions ctxt
      in
        let
          val pnm = "Modifies proof for recursive clique " ^ commas fnlist
          val _ = Feedback.informStr lthy (0, pnm ^ " commencing.")
          fun msg () = Feedback.informStr lthy(0, pnm ^ " completed.")
          val nway_thm = munge_tactic lthy nway_goal msg tac
          val nway_thms = HOLogic.conj_elims lthy nway_thm
          val _ = length nway_thms = length fnlist orelse
                  raise Fail "CONJUNCTS nway_thm and fnlist don't match up!"
          fun note_it nm th lthy =
              (Feedback.informStr lthy (0, "Modifies rule for "^nm^" extracted");
               #2 (Local_Theory.note ((Binding.name (nm ^ "_modifies"), []),
                                      [th])
                                     lthy))
          val noted_lthy = lthy |> fold2 note_it fnlist nway_thms
          val thy' = noted_lthy |> Local_Theory.exit_global
        in
          (failedsofar, mod_inv_props, thy')
        end
      end handle NoMods newset => (newset, mod_inv_props, thy)


    fun do_scc fnlist acc =
        case fnlist of
          [fname] =>
            if includeP fname then
              if not (is_recursivefn csenv fname) then
                do_one fname acc
              else do_recgroup fnlist acc
            else acc
        | (fname::_) => if includeP fname then do_recgroup fnlist acc
                        else acc
        | _ => raise Fail "SCC with empty list!"

    val acc_init = (Binaryset.empty string_ord, Termtab.empty, thy)
    val (_, _, thy) = acc_init |> fold do_scc cliques
    val _ = Feedback.informStr ctxt (0, "Modifies proofs done")
  in
    thy
  end


fun prove_all_modifies_goals csenv includeP tyargs prog_name cliques thy =
  if Config.get_global thy calculate_modifies_proofs then
    thy
    |> prove_all_modifies_goals_local prog_name csenv includeP tyargs cliques
  else
    thy


val _ =
  Outer_Syntax.command
    @{command_keyword "cond_sorry_modifies_proofs"}
    "set sorry_modifies_proof option, conditional on env variable"
    (Parse.embedded >> (Toplevel.generic_theory o cond_sorry_modifies_proofs))

end (* struct *)
