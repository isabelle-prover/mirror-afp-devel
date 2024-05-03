(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Rewrite L2 specifications to use a higher-level ("lifted") heap representation.
 *
 * The main interface to this module is translate (and inner functions
 * convert and define). See AutoCorresUtil for a conceptual overview.
 *)

structure HeapLift =
struct
         
(* Convenience shortcuts. *)
val warning = Utils.ac_warning
val apply_tac = Utils.apply_tac
val the' = Utils.the'
val timeit_msg = Utils.timeit_msg
val timing_msg' = Utils.timing_msg'
val verbose_msg = Utils.verbose_msg

structure Data = Generic_Data (
  type T = (stamp * (int -> term -> term)) list;
  val empty = [];
  fun merge (mk_patterns1, mk_patterns2) =
    if pointer_eq (mk_patterns1, mk_patterns2) then mk_patterns1 
    else AList.merge (op =) (K true) (mk_patterns1, mk_patterns2);
)

   
fun add_pattern mk_pattern =
  Data.map (fn mk_patterns => mk_patterns @ [(stamp (), mk_pattern)])

val hl_resolve_match_rules = AutoCorresTrace.mk_resolve_match_rules (map snd o Data.get)

(* Print the current goal state then fail hard. *)
exception ProofFailed of string


fun fail_tac ctxt s = (print_tac ctxt s THEN (fn _ => Seq.single (raise (ProofFailed s))))

type heap_info = HeapLiftBase.heap_info



(* Return the heap type used by a function. *)
fun get_expected_fn_state_type heap_info is_function_lifted fn_name =
  if is_function_lifted fn_name then
    #globals_type heap_info
  else
    #old_globals_type heap_info

(* Get a state translation function for the given function. *)
fun get_expected_st heap_info is_function_lifted fn_name =
  if is_function_lifted fn_name then
    (#lift_fn_full heap_info)
  else
    \<^Const>\<open>id \<open>#old_globals_type heap_info\<close>\<close>

(* Get the expected type of a function from its name. *)
fun get_expected_hl_fn_type prog_info fn_ptr_infos l2_infos (heap_info : HeapLiftBase.heap_info)
                            is_function_lifted fn_name =
let
  val (args, retT, errT,  globals_typ) = case AList.lookup (op =) fn_ptr_infos fn_name of 
               SOME info => let val hl_info = info FunctionInfo.HL 
                            in (#args hl_info, 
                                AutoCorresData.retT_from_fn_ptr_info hl_info, @{typ "exit_status c_exntype"},
                                AutoCorresData.state_type_of_exn_monad (#prog_env hl_info)) end
             | NONE => the (Symtab.lookup l2_infos fn_name) 
                    |> (fn info => (FunctionInfo.get_plain_args info, 
                         FunctionInfo.get_return_type info,
                         FunctionInfo.get_exn_type info,
                         get_expected_fn_state_type heap_info is_function_lifted fn_name))

  val fn_params_typ = map snd args
  val fn_typ = fn_params_typ
                 ---> AutoCorresData.mk_l2monadT globals_typ retT errT
in
  fn_typ
end

fun mk_fn_ptr_infos ctxt prog_info fn_args info =
  AutoCorresData.mk_fn_ptr_infos ctxt prog_info "" fn_args info

(* Get the expected proposition that will be generated about a function. *)
fun get_hl_corres_prop skips prog_info fn_ptr_infos l2_infos (heap_info : HeapLiftBase.heap_info)
    is_function_lifted ctxt assume fn_name function_free fn_args  =
let
  val hl_corres_attr = AutoCorresData.corres_thm_attribute (ProgramInfo.get_prog_name prog_info) skips FunctionInfo.HL fn_name
  (* Get L2 const *)
  val (l2_fun, hl_fun, l2_props, is_lifted) = case AList.lookup (op =) fn_ptr_infos fn_name of
        SOME info => 
          let
            val l2_info = info FunctionInfo.L2
            val hl_info = info FunctionInfo.HL
            val P_l2 = #prog_env l2_info 
            val P_hl = #prog_env hl_info 
            val p = Free (#ptr_val l2_info)
            val is_lifted = AutoCorresData.state_type_of_exn_monad (#prog_env hl_info) = #globals_type heap_info
          in    
            (P_l2 $ p, P_hl $ p, 
             [],
             K is_lifted)
          end
      | NONE => (the (Symtab.lookup l2_infos fn_name) |> FunctionInfo.get_const, 
                 function_free, [], is_function_lifted)

  val l2_term = betapplys (l2_fun, fn_args)
  (* Get expected HL const. *)
  val hl_term = betapplys (hl_fun, fn_args)

  val prems = case Symtab.lookup l2_infos fn_name of 
        SOME info => (* regular function not a function pointer parameter *)
          let  (* We add corres preconditions for any function pointer parameter in this function *)
            val fn_ptr_param_infos = mk_fn_ptr_infos ctxt prog_info fn_args info           
          in
            fn_ptr_param_infos 
            |> map (fn (ptr, ptr_info) => 
                let
                  val hl_info = ptr_info FunctionInfo.HL
                  val p = Free (#ptr_val hl_info)
                  val args = map Free (#args hl_info)
                  val (l2_props, (hl_prop, _)) = 
                    get_hl_corres_prop skips prog_info fn_ptr_param_infos l2_infos heap_info is_function_lifted ctxt false ptr p args
                  val l2_props = map fst l2_props
                  val hl_prop = fold Logic.all (rev args) hl_prop
                in  l2_props @ [hl_prop] end)
            |> flat
          end
        | NONE => [] 

in
  (l2_props,
    (Logic.list_implies (prems,
      \<^infer_instantiate>\<open>st = \<open>get_expected_st heap_info is_lifted fn_name\<close> and A = hl_term and C = l2_term 
        in prop \<open>L2Tcorres st A C\<close>\<close> ctxt), 
     [hl_corres_attr]))
end

fun get_unchanged_typing_prop prog_info fn_ptr_infos l2_infos 
    ctxt fn_name fn_args  =
let

  val unchanged_typing_on = Syntax.read_term ctxt 
        (fold_rev Long_Name.qualify [NameGeneration.global_rcd_name, "typing"]
          (Long_Name.base_name @{const_name heap_typing_state.unchanged_typing_on})) 
        |> Term_Subst.instantiate_frees (TFrees.make [(("'a", @{sort type}), @{typ unit})], Frees.empty)
  val S = TermsTypes.S ctxt

  val attrs = map (Attrib.attribute ctxt) @{attributes [runs_to_vcg]}

  
  (* Get L2 const *)
  val l2_fun = case AList.lookup (op =) fn_ptr_infos fn_name of
        SOME info => 
          let
            val l2_info = info FunctionInfo.L2
            val P_l2 = #prog_env l2_info 
            val p = Free (#ptr_val l2_info)
          in
            (P_l2 $ p)
          end
      | NONE => (the (Symtab.lookup l2_infos fn_name) |> FunctionInfo.get_const)

  val l2_term = betapplys (l2_fun, fn_args)
  val prems = case Symtab.lookup l2_infos fn_name of 
        SOME info => (* regular function not a function pointer parameter *)
          let  (* We add corres preconditions for any function pointer parameter in this function *)
            val fn_ptr_param_infos = mk_fn_ptr_infos ctxt prog_info fn_args info           
          in
            fn_ptr_param_infos 
            |> map (fn (ptr, ptr_info) => 
                let
                  val l2_info = ptr_info FunctionInfo.L2
                  val args = map Free (#args l2_info)
                  val (([], prop), _) = 
                    get_unchanged_typing_prop prog_info fn_ptr_param_infos l2_infos ctxt ptr args
                  val hl_prop = fold Logic.all (rev args) prop
                in  [hl_prop] end)
            |> flat
          end
        | NONE => [] 

in
  ((prems,
    \<^infer_instantiate>\<open>C = l2_term and unchanged = \<open>unchanged_typing_on $ S\<close> 
        in prop \<open>\<And>s. runs_to_partial C s (\<lambda>r t. unchanged s t)\<close>\<close> ctxt), 
   attrs)
end

(* Get arguments passed into the function. *)
fun get_expected_hl_fn_args prog_info fn_ptr_infos l2_infos fn_name =
  case AList.lookup (op =) fn_ptr_infos fn_name of 
    SOME info => #args (info FunctionInfo.HL)
   | NONE => 
      let
        val res = FunctionInfo.get_plain_args (the (Symtab.lookup l2_infos fn_name))
      in
        res
      end

fun convert_global_field_getters_setters (heap_info : heap_info) =
  let
    val gets = #global_field_getters heap_info |> Symtab.dest |> map snd
    val sets = #global_field_setters heap_info |> Symtab.dest |> map snd
    val term_map = Termtab.empty |> fold Termtab.update (gets @ sets)
  in
    Term.map_aterms (perhaps (Termtab.lookup term_map)) 
  end

(*
 * Resolve "base_thm" with "subgoal_thm" in all assumptions it is possible to
 * do so.
 *
 * Return a tuple: (<new thm>, <a change was made>).
 *)
fun greedy_thm_instantiate base_thm subgoal_thm =
let
  val asms = Thm.prop_of base_thm |> Logic.strip_assums_hyp
in
  fold (fn (i, asm) => fn (thm, change_made) =>
    if (Term.could_unify (asm, Thm.concl_of subgoal_thm)) then
      (subgoal_thm RSN (i, thm), true) handle (THM _ ) => (thm, change_made)
    else
      (thm, change_made)) (tag_list 1 asms) (base_thm, false)
end

(* Return a list of thm's where "base_thm" has been successfully resolved with
 * one of "subgoal_thms". *)
fun instantiate_against_thms base_thm subgoal_thms =
  map (greedy_thm_instantiate base_thm) subgoal_thms
  |> filter snd
  |> map fst

(*
 * Modify a list of thms to instantiate assumptions where ever possible.
 *)
fun cross_instantiate base_thms subgoal_thm_lists =
let
  fun iterate_base subgoal_thms base_thms =
    map (fn thm => (instantiate_against_thms thm subgoal_thms) @ [thm]) base_thms
    |> List.concat
in
  fold iterate_base subgoal_thm_lists base_thms
end

(* Extract the abstract term out of a L2Tcorres thm. *)
fun dest_L2Tcorres_term_abs @{term_pat "L2Tcorres _ ?t _"} = t



fun hl_fn_ptr info =
  let
    val hl_info = info FunctionInfo.HL
  in (#prog_env hl_info $ Free (#ptr_val hl_info)) end

fun mk_L2Tcorres_fun_ptr_thm prog_info (rec_funs, rec_ptrs) ctxt ((P_prev as Const (_, T_prev), _), (P as Const (Pname, T), _)) =
 let
   val (ptrT::argTs, monad_prevT) = strip_type T_prev
   val state_prevT = #stateT (AutoCorresData.dest_monad_type monad_prevT)
   val funT = let val (ptrT::argTs, retT) = strip_type T in argTs ---> retT end
   fun mk_fun_ptr fname = HP_TermsTypes.mk_fun_ptr ctxt (ProgramInfo.get_prog_name prog_info) fname
   val (empty, ptr_assoc) = map_filter (fn fname => find_first (fn (n, _) => n = fname) rec_funs) rec_ptrs
     |> filter (fn (_, Free (_, fT)) => fT = funT)  
     |> `null 
     ||> map (apfst mk_fun_ptr) ||> map HOLogic.mk_prod 
     ||> HOLogic.mk_list (HOLogic.mk_prodT (@{typ "unit ptr"}, funT))
   val _ = if empty andalso not (null rec_funs) then raise Match else ()

   
   val stateT = T |> strip_type |> snd |> AutoCorresData.dest_monad_type |> #stateT
   val args = map (fn T => ("x", T)) argTs
   val st = ("st", state_prevT --> stateT)
   val (st::args, ctxt') = Utils.fix_variant_frees ([st, ("p", ptrT)] @ args) ctxt
   val P = if empty then P else \<^infer_instantiate>\<open>P = P and xs = ptr_assoc in term \<open>map_of_default P xs\<close>\<close> ctxt'
   val P_prev = betapplys(P_prev, args)
   val P = betapplys(P, args) 

   val corres = \<^infer_instantiate>\<open>st and P and P_prev in term \<open>L2Tcorres st P P_prev\<close>\<close> ctxt'
   val goal = \<^instantiate>\<open>corres in term \<open>PROP DYN_CALL (Trueprop corres) \<Longrightarrow> corres\<close>\<close>
   val [thm] = Goal.prove ctxt' [] [] goal (fn {context,...} => 
         asm_full_simp_tac (ctxt addsimps @{thms DYN_CALL_def}) 1) 
     |> single |> Proof_Context.export ctxt' ctxt
 in
   [("", thm)]
 end
 handle Match => []



fun prepare prog_info skips (l2_infos: FunctionInfo.function_info Symtab.table) (clique: string list) (lthy:local_theory) = 
  if null (flat (map (ProgramAnalysis.callers_with_addressable_variables (ProgramInfo.get_csenv prog_info)) clique)) 
     andalso
     (if exists (ProgramAnalysis.is_recursivefn (ProgramInfo.get_csenv prog_info)) clique then
         not (exists (ProgramAnalysis.has_addressable_variables (ProgramInfo.get_csenv prog_info)) clique) 
      else true) 
  then
    let 
      val _ = verbose_msg 3 lthy (fn _ => "Skipping unchanged typing proof for " ^ commas clique)
    in lthy end
  else
     let
       fun finfo f = (the (Symtab.lookup l2_infos f))
       val is_recursive = FunctionInfo.is_function_recursive (finfo (hd clique))
       val induct_thms = FunctionInfo.get_induct_thms (finfo (hd clique))
   
       fun check ctxt = AutoCorresUtil.check_dyn_call_goal ctxt prog_info (FunctionInfo.L2, FunctionInfo.L2)
       fun splitter ctxt = AutoCorresUtil.dyn_call_split_simp_sidecondition_tac (check ctxt) [] [] ctxt
               
       fun prop f ctxt =
         let
           val info = finfo f
           val args = FunctionInfo.get_plain_args info
           val def = FunctionInfo.get_definition info
           val (params, ctxt) = Utils.fix_variant_frees args ctxt;
   
           val fn_ptr_infos = mk_fn_ptr_infos ctxt prog_info params info
           val ((prems, prop), attrs) = get_unchanged_typing_prop prog_info fn_ptr_infos l2_infos lthy f (map Free args)
           val ((arbitrary_vars, prop), ctxt) = Utils.import_universal_prop prop ctxt
           val (prems, ctxt) = Assumption.add_assumes (map (Thm.cterm_of ctxt) prems) ctxt
           val (_, ctxt) = fold_map (Thm.proof_attributes attrs) prems ctxt
         in
           ((def, params, arbitrary_vars, (prop, attrs)), ctxt)
         end      
                      
       val def_locale = AutoCorresData.definition_locale lthy skips (FunctionInfo.prev_phase skips FunctionInfo.HL) 
              (ProgramInfo.get_prog_name prog_info) clique     

       val lthy = lthy |> AutoCorresData.in_locale def_locale (fn lthy =>
         let
           val (props, ctxt) = lthy |> fold_map prop clique
                
           val thms = timeit_msg 1 lthy (fn _ => "Trying unchanged typing proof for " ^ commas clique) (fn _ => 
                 AutoCorresUtil.prove_functions is_recursive induct_thms 
                   (Unchanged_Typing.unchanged_typing_tac (SOME splitter))
                   (fn attrss => fn ctxt => ALLGOALS (AutoCorresUtil.prove_induction_case 
                        (K (Unchanged_Typing.unchanged_typing_tac (SOME splitter))) attrss ctxt))
                   ctxt props 
                   handle ERROR msg => 
                    (warning ("Could not prove 'unchanged_typing_on' for " ^ commas clique ^ "\n " ^ msg); []))
           
           val thms = thms |> (Proof_Context.export ctxt lthy)
           val lthy = lthy |> not (null thms)?
             (Local_Theory.note ((Binding.make (suffix "_unchanged_typing" (space_implode "_" clique), \<^here>), 
               @{attributes [unchanged_typing]}), thms) #> snd)
          in 
            lthy
          end)   
      in
        lthy
      end
               
(* Convert a program to use a lifted heap. *)
fun translate
    (skips: FunctionInfo.skip_info)
    (base_locale_opt: string option)
    (prog_info : ProgramInfo.prog_info)
    (HL_setup : HeapLiftBase.heap_lift_setup)
    (no_heap_abs : Symset.key Symset.set)
    (heap_abs_syntax : bool)
    (keep_going : bool)
    (HL_opt : FunctionInfo.stage)
    (trace_opt : bool)
    (parallel : bool)
    (cliques: string list list)
    (lthy: local_theory)
    : string list list * local_theory =

let
  val phase = FunctionInfo.HL 
  val prev_phase = FunctionInfo.prev_phase skips phase
  val filename = ProgramInfo.get_prog_name prog_info
  val hl_function_name = ProgramInfo.get_mk_fun_name prog_info phase
  val existing_l2_infos = AutoCorresData.get_default_phase_info (Context.Proof lthy) filename prev_phase
  val existing_hl_infos = AutoCorresData.get_default_phase_info (Context.Proof lthy) filename phase
  val conversion_start = Timing.start ();

  val heap_info = #heap_info HL_setup;

  (*
   * Fetch rules from the theory, instantiating any rule with the
   * lifted_globals lemmas for "valid_globals_field", "valid_typ_heap" etc.
   * that we generated previously.
   *)
  val base_rules = Utils.get_rules lthy @{named_theorems heap_abs}
  val rules =
      cross_instantiate base_rules (#lifted_heap_lemmas HL_setup)
      (* Remove rules that haven't been fully instantiated *)
      |> filter_out (Thm.prop_of #> exists_subterm (fn x =>
           case x of Const (@{const_name "valid_globals_field"}, _) => true
                   | Const (@{const_name "valid_struct_field"}, _) => true
                   | Const (@{const_name "typ_heap_simulation"}, _) => true
                   | _ => false));

  (* We only use this blanket rule for non-lifted functions;
   * liftable expressions can be handled by specific struct_rewrite rules *)
  val nolift_rules = @{thms struct_rewrite_expr_id}

  fun is_function_lifted f_name =
        case Symtab.lookup existing_hl_infos f_name of
            SOME info => let
              (* We heap-lifted this function earlier. Check its state type. *)
              (* NB: Note that we are not in the corres-locale yet, hence concl_of as the
                     definition might have locale-preconditions.*)
              val body = FunctionInfo.get_definition info |> Thm.concl_of |> Utils.rhs_of_eq;
              val stT = AutoCorresData.state_type_of_exn_monad body;
              in stT = #globals_type heap_info end
          | NONE => let
              val can_lift = not (Symset.contains no_heap_abs f_name)
              in can_lift end;
  (* Cache answers for which functions we are lifting. *)
  val is_function_lifted = String_Memo.memo is_function_lifted;

  (* Convert to new heap format. *)
  fun convert lthy l2_infos f: AutoCorresUtil.convert_result =
  let
    val f_l2_info = the (Symtab.lookup l2_infos f);

    (* Fix argument variables. *)
    val new_fn_args = get_expected_hl_fn_args prog_info [] l2_infos f;
    val (arg_frees, lthy') = Utils.fix_variant_frees new_fn_args lthy;

    val fn_ptr_infos = mk_fn_ptr_infos lthy' prog_info arg_frees f_l2_info

    (* Add callee assumptions. *)
    val (lthy'', callee_terms) =
      AutoCorresUtil.assume_called_functions_corres lthy' (map (apsnd hl_fn_ptr) (fn_ptr_infos))
        (FunctionInfo.get_recursive_clique f_l2_info)
        (get_expected_hl_fn_type prog_info fn_ptr_infos l2_infos heap_info is_function_lifted)
        (get_hl_corres_prop skips prog_info fn_ptr_infos l2_infos heap_info is_function_lifted)
        (get_expected_hl_fn_args prog_info fn_ptr_infos l2_infos)
        (hl_function_name "");

    val rec_funs = map (fn (n, (t,_)) => (n, t)) callee_terms
    val rec_ptrs = FunctionInfo.get_clique_recursion_fun_ptrs f_l2_info

    val lthy'' = lthy'' 
      |> AutoCorresData.prove_and_note_fun_ptr_intros false
        (AutoCorresUtil.prev_phase_pair skips phase) prog_info 
           (mk_L2Tcorres_fun_ptr_thm prog_info (rec_funs, rec_ptrs))

    (* Fetch the function definition. *)
    val l2_body_def =
        FunctionInfo.get_definition f_l2_info
        (* Instantiate the arguments. *)
        |> Utils.inst_args lthy'' (map (Thm.cterm_of lthy'') arg_frees)

    (* Get L2 body definition with function arguments. *)
    val l2_term = betapplys (FunctionInfo.get_const f_l2_info, arg_frees)

    (* Get our state translation function. *)
    val st = get_expected_st heap_info is_function_lifted f

    (* Generate a schematic goal. *)
    val goal = \<^infer_instantiate>\<open>st = st and C = l2_term in prop (schematic) \<open>L2Tcorres st A C\<close>\<close> lthy'
        |> Thm.cterm_of lthy''
        |> Goal.init
        |> Utils.apply_tac lthy'' "unfold RHS" (EqSubst.eqsubst_tac lthy'' [0] [l2_body_def] 1)

    val fun_ptr_intros = Named_Theorems.get lthy'' @{named_theorems "fun_ptr_intros"}

    val more_corres = Named_Theorems.get lthy'' @{named_theorems "hl_corres"}
    val known_function_corres = Named_Theorems.get lthy'' @{named_theorems known_function_corres}
    val rules = (rev rules) @ (flat (map (snd #> #2) callee_terms)) @ 
          fun_ptr_intros @ more_corres @ known_function_corres
    val rules = if is_function_lifted f then rules else rules @ nolift_rules
    val fo_rules = Utils.get_rules lthy'' @{named_theorems heap_abs_fo}

    (* Convert the concrete side of the given L2T term to/from first-order form. *)
    fun prove_abs_spec_thm ctxt abs_spec_def abs_spec st C =
      let
        fun map_typ f (T as (Type (n, Ts))) = f (Type (n, map (map_typ f) Ts))
          | map_typ f T = T

        val (concrete_stateT, abstract_stateT) = fastype_of st |> dest_funT
        val simp_thms = (#lift_fn_simp_thms heap_info) @ abs_spec_def @ @{thms mex_def meq_def} @
          Proof_Context.get_thms ctxt "globals.splits" @ [#lift_fn_thm heap_info] @
          Proof_Context.get_thms ctxt @{named_theorems "abs_spec"};
        val P' = Abs ("s", abstract_stateT, @{term True});
        val A' =
          if is_function_lifted f
          then C 
            |> convert_global_field_getters_setters heap_info
            |> Term.map_types (map_typ (fn T => if T = concrete_stateT then abstract_stateT else T))
          else C
      in
        Goal.prove ctxt [] [] (HOLogic.Trueprop $ (abs_spec $ st $ P' $ A' $ C))
          (K (auto_tac (ctxt addsimps simp_thms)))
      end

    fun solve_abs_spec_globals_no_heap ctxt = SUBGOAL (fn (_, i) => fn st => 
      let
        val ({context, concl,...}, _) = Subgoal.focus ctxt i NONE st
        val @{term_pat "?abs_spec ?f ?P ?A ?C"} = Thm.term_of concl |> HOLogic.dest_Trueprop
        val @{term_pat "abs_spec"} = abs_spec
        val [thm] = prove_abs_spec_thm context @{thms abs_spec_def} abs_spec f C 
          |> single |> Proof_Context.export context ctxt
      in
        resolve_tac ctxt [thm] i st
      end
      handle Match => no_tac st
           | Bind => no_tac st
           | TERM _ => no_tac st
    )

    fun check ctxt = AutoCorresUtil.check_dyn_call_goal lthy prog_info (FunctionInfo.L2, FunctionInfo.L2)
    fun splitter ctxt = AutoCorresUtil.dyn_call_split_simp_sidecondition_tac (check ctxt) [] [] ctxt

    fun solve_unchanged_typing ctxt = SUBGOAL (fn (t, i) => fn st =>
      case t |> Utils.concl_of_subgoal_open  of
        @{term_pat "Trueprop (runs_to_partial _ _ (\<lambda>r t. heap_typing_state.unchanged_typing_on _ _ _ _))"} => 
          let
            val ({context, concl,...}, _) = Subgoal.focus ctxt i NONE st    
            val res = try (Goal.prove_internal ctxt [] concl) (fn _ => 
                        Unchanged_Typing.unchanged_typing_tac (SOME splitter) ctxt)  
                    |> Option.map (singleton (Proof_Context.export context ctxt))
            val tac =  case res of
                  SOME thm => 
                    Utils.verbose_print_subgoal_tac 4 "solve_unchanged_typing success" ctxt i THEN 
                    resolve_tac ctxt [thm] i
                | _ => 
                    Utils.verbose_print_subgoal_tac 3 "solve_unchanged_typing FAILED" ctxt i THEN 
                    no_tac      
          in
            tac st
          end
      | _ => no_tac st)
 

    fun solve_abs_assume_globals_no_heap ctxt = SUBGOAL (fn (_, i) => fn st => 
      let
        val ({context, concl,...}, _) = Subgoal.focus ctxt i NONE st
        val @{term_pat "?abs_assume ?f ?P ?A ?C"} = Thm.term_of concl |> HOLogic.dest_Trueprop
        val @{term_pat "abs_assume"} = abs_assume
        val [thm] = prove_abs_spec_thm context @{thms abs_assume_def}  abs_assume f C 
          |> single |> Proof_Context.export context ctxt
      in
        resolve_tac ctxt [thm] i st
      end
      handle Match => no_tac st
           | Bind => no_tac st
           | TERM _ => no_tac st
    )

    val rules_tac = hl_resolve_match_rules (Context.Proof lthy'') rules 1

    val THIN_tac = Utils.THIN_tac HeapLiftBase.prune_unused_bounds_hl_tac 
 
    val check = AutoCorresUtil.check_dyn_call_goal lthy prog_info
      (AutoCorresUtil.prev_phase_pair skips FunctionInfo.HL)
    (*
     * Recursively solve subgoals.
     *
     * We allow backtracking in order to solve a particular subgoal, but once a
     * subgoal is completed we don't ever try to solve it in a different way.
     *
     * This allows us to try different approaches to solving subgoals without
     * leading to exponential explosion (of many different combinations of
     * "good solutions") once we hit an unsolvable subgoal.
     *)
    fun tactics ctxt ct =
        if FunctionInfo.get_is_simpl_wrapper f_l2_info
        then (* Solver for trivial simpl wrappers. *)
             [(@{thm L2Tcorres_id}, resolve_tac ctxt [@{thm L2Tcorres_id}] 1)]
        else [(@{thm thin_rl}, THIN_tac ctxt 1)]
             @ rules_tac ctxt ct
             @ [(@{thm runs_to_partial_skip}, solve_unchanged_typing ctxt 1) ]
             @ [(@{thm L2Tcorres_guarded_simple}, AutoCorresUtil.dyn_call_split_simp_sidecondition_tac check
                    more_corres [] ctxt 1)]
             @ (map (fn rule => (rule, Utils.fo_arg_resolve_tac lthy'' rule ctxt 1)) fo_rules)
             @ [(@{thm abs_spec_def}, solve_abs_spec_globals_no_heap ctxt 1)]
             @ [(@{thm abs_assume_def}, solve_abs_assume_globals_no_heap ctxt 1)]
              
    val thm = timeit_msg 1 lthy'' (fn _ => "Conversion (HL) - trace_solve_prove - " ^ f) \<^try>\<open>(fn () => 
         AutoCorresTrace.trace_solve_prove lthy'' true tactics NONE goal)
         catch exn => (warning ("Failed to lift " ^ quote f ^ " into split heap. Exclude from lifting (option: no_heap_abs)?"); Exn.reraise exn)
         \<close>
    (* DEBUG: make sure that all uses of field_lvalue and c_guard are rewritten.
     *        Also make sure that we cleaned up internal constants. *)
    fun contains_const name = exists_subterm (fn x => case x of Const (n, _) => n = name | _ => false)
    fun const_gone term name =
        if not (contains_const name term) then ()
        else Utils.TERM_non_critical keep_going
               ("Heap lift: could not remove " ^ name ^ " in " ^ f ^ ".") [term]
    fun const_old_heap term name =
        if not (contains_const name term) then ()
        else warning ("Heap lift: could not remove " ^ name ^ " in " ^ f ^
                      ". Output program may be unprovable.")
    val _ = if not (is_function_lifted f) then []
            else (map (const_gone (term_of_thm thm))
                      [@{const_name "heap_lift__h_val"}];
                  map (const_old_heap (term_of_thm thm))
                      [@{const_name "field_lvalue"}, @{const_name "c_guard"}]
                 )

    val _ = timing_msg' 1 lthy'' (fn _ => "Conversion HL - " ^ f) conversion_start;

    (* Apply peephole optimisations to the theorem. *)
    val _ = writeln ("Simplifying (HL) " ^ f)
    val _ = verbose_msg 1 lthy'' (fn _ => "HL (raw) - " ^ f ^ ": " ^ Thm.string_of_thm lthy'' thm);
    val thm = timeit_msg 1 lthy (fn _ => "Simplification HL (opt) - " ^ f) (fn _ =>
       L2Opt.cleanup_thm_tagged 
         (lthy'' |> AutoCorresTrace.put_trace_info f FunctionInfo.HL FunctionInfo.RAW)
         [] (#pointwise_to_heapwide_thms heap_info) thm HL_opt 2 trace_opt "HL");
    val _ = verbose_msg 1 lthy'' (fn _ => "HL (opt) - " ^ f ^ ": " ^ Thm.string_of_thm lthy'' thm);

    (* If we created extra heap wrappers, apply them now.
     * Our simp rules don't seem to be enough for L2Opt,
     * so we cannot change the program before that. *)
    val thm = if not heap_abs_syntax then thm else
                Raw_Simplifier.rewrite_rule lthy'' (#heap_syntax_rewrs HL_setup) thm
    val f_body = dest_L2Tcorres_term_abs (HOLogic.dest_Trueprop (Thm.concl_of thm));
    (* Get actual recursive callees *)
    val rec_callees = AutoCorresUtil.get_rec_callees callee_terms f_body;

    (* Return the constants that we fixed. This will be used to process the returned body. *)
    val callee_consts =
          callee_terms |> map (fn (callee, (const, _)) => (callee, const)) |> Symtab.make;
  in
    { body = f_body,
      proof =  hd (Proof_Context.export lthy'' lthy [thm]),
      rec_callees = rec_callees,
      callee_consts = callee_consts,
      arg_frees = map dest_Free arg_frees
    }
  end

  (* Define a previously-converted function (or recursive function group).
   * lthy must include all definitions from hl_callees. *)
  fun define
        (lthy: local_theory)
        (funcs: AutoCorresUtil.convert_result Symtab.table)
        : local_theory = let
    val l2_infos = AutoCorresData.get_default_phase_info (Context.Proof lthy) (ProgramInfo.get_prog_name prog_info) prev_phase 
    val funcs' = Symtab.dest funcs |>
          map (fn result as (name, {proof, arg_frees, ...}) =>
                     (name, (AutoCorresUtil.abstract_fn_body l2_infos result,
                             proof, arg_frees)));

    val (new_thms, lthy') =
          AutoCorresUtil.define_funcs
              skips
              FunctionInfo.HL prog_info I {concealed_named_theorems=false} (hl_function_name "")
              (get_expected_hl_fn_type prog_info [] l2_infos heap_info is_function_lifted)
              (get_hl_corres_prop skips prog_info [] l2_infos heap_info is_function_lifted)
              (get_expected_hl_fn_args prog_info [] l2_infos)
              funcs'
              lthy;
    in lthy' end;

  val (groups, lthy) = lthy |>
      AutoCorresUtil.gen_convert_and_define_cliques (prepare prog_info skips) skips base_locale_opt prog_info
        FunctionInfo.HL parallel
        convert define cliques

in 
  (groups, lthy) 
end

end
