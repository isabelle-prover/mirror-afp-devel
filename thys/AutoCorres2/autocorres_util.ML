(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Common code for all translation phases: defining funcs, calculating dependencies,
 * variable fixes, etc.
 *)

(*
 * Here is a brief explanation of how most AutoCorres phases work
 * with each other.
 *
 * AutoCorres's phases are L1, L2, HL, WA and TS. (TS doesn't share these
 * utils for historical reasons; fixing that is another story.)
 * Basically, each of L1, L2, HL and WA:
 *   1. takes a list of input function specs;
 *   2. converts each function individually;
 *   3. defines each new function (or recursive function group).
 *      This updates the local theory sequentially;
 *   4. proves monad_mono theorems and places them into the
 *      output list of functions;
 *   5. outputs a list of new function specs in the original format.
 *
 * === Concurrency ===
 * To support concurrent processing better, we do not use lists.
 * Instead, we use a future-chained sequence (FSeq, below) so that
 * define and convert steps can be done in parallel (up to the
 * dependencies between them, of course).
 *
 * (We do not use a plain list of futures because a define
 * step may produce one or more function groups, so we can't
 * know how many groups there will be in advance. See the
 * recursive group splitting comment for define_funcs_sequence.)
 *
 * Additionally, AutoCorres is structured so that conversions
 * do not require the most up-to-date local theory, so we also
 * output a stream of intermediate local theories. This allows
 * conversions of phase N+1 to be pipelined with define steps of
 * phase N.
 *
 * FunctionInfo.phase_results is the uniform sequence type that
 * most AutoCorres translation phases adhere to.
 *
 * === (2) Conversion ===
 * Converting a function starts by assuming correspondence theorems
 * for all the functions that it calls (including itself, if
 * recursive). We invent free variables to stand for those functions;
 * see assume_called_functions_corres.
 *
 * Because it's fiddly to have these assumptions everywhere,
 * we use Assumption to hide them in the thm hyps during conversion.
 * When done, we export the assumptions using Morphism.thm.
 *
 * After performing these conversions, we get a corres theorem
 * with corres assumptions for called functions (along with other
 * auxillary info). These are generally packaged into a
 * convert_result record.
 *
 * The conversions are all independent, so we launch them in
 * topological order; see par_convert. This is the most convenient
 * because each conversion takes place between the previous and next
 * define step, which already require topological order.
 *
 * === (3) Definition ===
 * We take the sequence of conversion results and define each
 * function (or recursive group) in the theory.
 *
 * Each function group and its convert_results are processed by
 * define_funcs. Conventionally, AutoCorres phases provide a
 * "define" wrapper that sets up the required inputs to define_funcs
 * and constructs function_infos for the newly defined functions.
 *
 * There is also a high-level wrapper, define_funcs_sequence, that
 * calls these "define" wrappers in the correct order.
 * It also splits recursive groups after defining them; see its
 * documentation for details.
 *
 * === (4) Corollaries ===
 * Currently, each phase only proves one type of corollary,
 * monad_mono theorems. These proofs are duplicated in the source
 * of the individual phases (this should be fixed) and do not make
 * use of the utils here.
 *
 * === Incremental mode support ===
 * AutoCorres supports incremental translation, which means that
 * we need to insert previously-translated function data at the
 * appropriate places. The par_convert and define_funcs_sequence
 * wrappers take "existing_foo" arguments and ensure that these
 * are available to the per-phase convert and define steps.
 *)

infix 1 THEN_UNSOLVED

fun (tac1 THEN_UNSOLVED tac2) i st =
  let
    val np = Thm.nprems_of st;
    fun cond_tac2 i st = if Thm.nprems_of st >= np then tac2 i st else all_tac st
  in
    ((tac1 i) THEN (cond_tac2 i)) st
  end
structure AutoCorresUtil =
struct

val verbose = Utils.verbose
val verbose_msg = Utils.verbose_msg
val timing_msg = Utils.timing_msg
val timeit_msg = Utils.timeit_msg
val timeap_msg_tac = Utils.timeap_msg_tac

fun timeit_conversion_msg level ctxt finfo f = 
  let
    val fname = FunctionInfo.get_name finfo
    val phase = FunctionInfo.next_phase (FunctionInfo.get_phase finfo)
    fun mk_msg s e =
          s ^ " (" ^ FunctionInfo.string_of_phase phase ^ ") for function " ^ fname ^ e
    val _  = timing_msg level ctxt (fn _ => mk_msg "Converting" " ...")
  in timeit_msg level ctxt (fn _ => mk_msg "Converted" "") f end;

fun timeit_conversion_msg' level ctxt phase fname f = 
  let
    fun mk_msg s e  =
          s ^ " (" ^ FunctionInfo.string_of_phase phase ^ ") for function " ^ fname ^ e
    val _  = timing_msg level ctxt (fn _ => mk_msg "Converting" " ...")
  in timeit_msg level ctxt (fn _ => mk_msg "Converted" "") f end;

fun timeit_prepare_msg' level ctxt phase clique f = 
  let
    fun mk_msg s e  =
          s ^ " (" ^ FunctionInfo.string_of_phase phase ^ ") for clique " ^ commas clique ^ e
    val _  = timing_msg level ctxt (fn _ => mk_msg "Preparing" " ...")
  in timeit_msg level ctxt (fn _ => mk_msg "Preparing" "") f end;

fun timeit_ts_msg level ctxt fnames f = 
  let
    val fgroup = commas fnames
    val phase = FunctionInfo.TS
    fun mk_msg s e = 
          s ^ " (" ^ FunctionInfo.string_of_phase phase ^ ") for function(s) " ^ fgroup ^ e
    val _ = timing_msg level ctxt (fn _ => mk_msg "Converting" " ...")
    in timeit_msg level ctxt (fn _ => mk_msg "Converted" "") f end;

fun safe_unprefix [] x = x
 | safe_unprefix (p::ps) x = case try (unprefix p) x of SOME x' => x' | _ => safe_unprefix ps x
  

(*
 * Get functions called by a particular function.
 *
 * We split the result into standard calls and recursive calls (i.e., calls
 * which may recursively call back into us).
 *)

fun get_callees fn_info =
  (Symset.dest (FunctionInfo.get_callees fn_info), Symset.dest (FunctionInfo.get_rec_callees fn_info))

fun get_callees' fn_infos fn_name =
let
  val fn_info = the (Symtab.lookup fn_infos fn_name)
in
  get_callees fn_info
end

fun CHANGED' tac i st =
  let fun diff st' = let 
                       val res = not (Thm.eq_thm (st, st'));
                     in res end
  in Seq.filter diff (tac i st) end;


fun REPEAT_DETERM_N' n tac i =
  REPEAT_DETERM_N n (tac i)
        
fun maybe_dest_Trueprop t =
 case try HOLogic.dest_Trueprop t of SOME t' => t' |  NONE => t
 

fun prev_phase_pair skips phase = (FunctionInfo.prev_phase skips phase, phase)

fun dest_corres_progs @{term_pat "L1corres _ _ ?new ?old"} = SOME {new=new, old=old}
  | dest_corres_progs @{term_pat "L2corres _ _ _ _ ?new ?old"} = SOME {new=new, old=old}
  | dest_corres_progs @{term_pat "IOcorres _ _ _ _ _ ?new ?old"} = SOME {new=new, old=old}
  | dest_corres_progs @{term_pat "L2Tcorres _ ?new ?old"} = SOME {new=new, old=old}
  | dest_corres_progs @{term_pat "corresTA _ _ _ ?new ?old"} = SOME {new=new, old=old}
  | dest_corres_progs @{term_pat "refines ?old ?new _ _ _"} = SOME {new=new, old=old}
  | dest_corres_progs _ = NONE

fun is_var_new (_, schematic_vars:cterm Vars.table) concl =
  case (try HOLogic.dest_Trueprop concl) |> Option.mapPartial dest_corres_progs of
    SOME {new, ...} => Vars.exists (fn (_, v) => Thm.term_of v = new) schematic_vars
  | NONE => false


fun EVERY_UNSOLVED [] i = all_tac
  | EVERY_UNSOLVED (tac::tacs) i = (tac THEN_UNSOLVED (EVERY_UNSOLVED tacs)) i

fun add_matches match (t as (u $ v)) (xs, ctxt) = (case match ctxt t of SOME x => (x::xs, ctxt) | NONE => add_matches match v (add_matches match u (xs, ctxt)))
  | add_matches match (t as (Abs _)) (xs, ctxt) = (case match ctxt t of SOME x => (x::xs, ctxt) | NONE => 
      let 
        val ((_, bdy), ctxt') = Variable.dest_abs t ctxt 
     in add_matches match bdy (xs, ctxt') end)
  | add_matches match t (xs, ctxt) = (case match ctxt t of SOME x => (x::xs, ctxt) | NONE => (xs, ctxt))

fun notin_tac ctxt = SUBGOAL (fn (t,i) =>
 case t |> Utils.concl_of_subgoal_open of
  @{term_pat "Trueprop (_ \<notin> _)"} => SOLVED' (asm_full_simp_tac ctxt THEN' Utils.print_subgoal_tac "notin end" ctxt) i
 | _ => no_tac)

val d1 = Unsynchronized.ref false
val d2 = Unsynchronized.ref false

val dest_map_of_default = map_of_default_args.dest_map_of_default
val dest_assoc = map_of_default_args.dest_assoc

fun mk_assoc (xs as ((p,f)::_)) = 
     let
       val pT = @{typ "unit ptr"}
       val fT = fastype_of f
     in
       {xs = xs |> map HOLogic.mk_prod |> HOLogic.mk_list (HOLogic.mk_prodT (pT, fT)), pT = pT, fT = fT}
     end
  | mk_assoc [] = error ("mk_assoc: empty")

fun mk_map_of_default {xs, fT, ...} =
  let
    val d = AutoCorresData.mk_default fT
  in
     \<^instantiate>\<open>'a = fT and d=d and xs = xs in term \<open>map_of_default (\<lambda>_::unit ptr. d) xs\<close>\<close>
  end

fun subst_atomic ctxt substs t =
  let

    val thy = Proof_Context.theory_of ctxt
    fun rew t = case AList.lookup (op =) substs t of SOME rhs => rhs | _ => Same.same t 
    fun do_rew t = case t of Const _ => rew t | Free _ => rew t | _ => Same.same t 
  in Term.map_aterms do_rew t end

val head_name = Term.head_of #> Term.term_name

type corres_funs = {old: term, new: term}
fun get_first_corres {dest_corres_funs: term -> corres_funs} thms old =
  let
    val old_name = head_name old
  in
    get_first (fn thm => 
      Thm.concl_of thm |> dest_corres_funs |> (fn {new, old} => 
        if head_name old = old_name then SOME (Term.head_of new, thm) else NONE)) 
     thms
  end

fun check_map_of_default ct = ct |> Thm.term_of |> Utils.concl_of_subgoal_open |> 
  exists_subterm (fn @{term_pat "map_of_default ?d ?xs ?p"} => true | _ => false)

fun map_of_default_core t = 
  case try dest_map_of_default t of 
    SOME {map_of_default, d, fs, p, ...} => map_of_default $ d $ fs $ p
  | _ => t

fun strip_args n t =
  let
    val (head, args) = strip_comb t
    val args' = rev (drop n (rev args))
  in
    list_comb (head, args')
  end

fun replace_arg t x = fst (Term.dest_comb t) $ x 
 

fun mk_corres_map_of_default_thm {get_first_corres} ctxt thms map_of_default_old =
  let
    val {fs, d, args, ...} = map_of_default_old |> dest_map_of_default
    val arity = length args
    val (ptrs, olds) = dest_assoc fs |> split_list |> apsnd (map (strip_args arity))
    val (news, relevant_thms) = map_filter (get_first_corres thms) olds |> split_list
    val corres_top = Named_Theorems.get ctxt @{named_theorems corres_top}
    val _ = @{assert} (length news = length olds)
    val assoc = (ptrs ~~ news) |> mk_assoc
    val fs' = #xs assoc
    val d' = AutoCorresData.mk_default (@{typ  "unit ptr"} --> #fT assoc)
    val map_of_default_new = mk_map_of_default assoc
    val ([p], ctxt1) = Utils.fix_variant_frees [("p", @{typ "unit ptr"})] ctxt
    val rewrs = [(hd olds, replace_arg (map_of_default_core map_of_default_old) p ), (hd news, map_of_default_new $ p)]
    val prop = hd relevant_thms |> Thm.prop_of |> subst_atomic ctxt rewrs
    val rule = Drule.infer_instantiate ctxt1 
      [ (("ys", 0), Thm.cterm_of ctxt1 fs'), (("d'", 0),  Thm.cterm_of ctxt1 d'), (("p", 0), Thm.cterm_of ctxt1 p), 
        (("xs", 0), Thm.cterm_of ctxt1 fs), (("d", 0),  Thm.cterm_of ctxt1 d)]
      @{thm map_of_default_list_all2_cases}
    val intros = corres_top @ @{thms list_all2_prod_cons list_all2_prod_nil conjI refl} 
    val ([prop'], ctxt2) = Variable.import_terms false [prop] ctxt1
    val thm = prove ctxt2 [] [] prop' (fn {context, ...} => 
          Utils.dprint_tac (!d1) "init:" context THEN
          ( resolve_tac context [rule] THEN_ALL_NEW 
          REPEAT_ALL_NEW (Utils.dprint_subgoal_tac (!d1) "repeat:" context THEN' resolve_tac context (relevant_thms @ intros))) 1 THEN
          Utils.dprint_tac (!d1) "after intros:" context) 
      |> singleton (Proof_Context.export ctxt2 ctxt) 
      |> Goal.norm_result ctxt
    val _ = if (!d2) then tracing ("mk_corres_map_of_default_thm: " ^ Thm.string_of_thm ctxt thm) else ()
  in
    (map_of_default_new, thm)
  end

(* Measure variables are currently hardcoded as nats. *)

val measureT = @{typ nat};
fun split_Ball_attr phase = Thm.declaration_attribute (fn thm => fn context =>
  let
    val ctxt = Context.proof_of context
    val derived_thms = thm |> Conv.fconv_rule (Simplifier.rewrite ctxt) |> HOLogic.conj_elims

  in
    context |> fold (Named_Theorems.add_thm (AutoCorresData.corres_named_thms phase)) derived_thms
  end
  )
(*
 * Assume theorems for called functions.
 *
 * A new context is returned with the assumptions in it, and a list of the functions assumed:
 *
 *   (<function name>, ( <function free>, <function thms>))
 *
 * In this context, the theorems refer to functions by fixed free variables.
 *
 * get_fn_args may return user-friendly argument names that clash with other names.
 * We will process these names to avoid conflicts.
 *
 * get_fn_assumption should produce the desired theorems to assume. Its arguments:
 *   context (with fixed vars), callee name, callee term, arg terms
 * (all terms are fixed free vars).
 *
 * get_const_name generates names for the free function placeholders.
 *
 *)

fun assume_called_functions_corres ctxt rec_callees
    get_fn_type get_fn_prop get_fn_args get_const_name  =
let
  (* Assume the existence of a function, along with a theorem about its
   * behaviour. *)
  fun assume_func ctxt fn_name maybe_fn_ptr_info =
  let
    val fn_args = get_fn_args fn_name

    (* Fix a variable for the function. *)

    val (fn_free, ctxt') = case maybe_fn_ptr_info of 
          SOME l2_term => (l2_term, ctxt)
        | NONE => 
            let     
              val ([fixed_fn_name], ctxt') = Variable.variant_fixes [get_const_name fn_name] ctxt
              val fn_free = Free (fixed_fn_name, get_fn_type fn_name)
            in (fn_free, ctxt') end

    
    (* Fix a variables for function arguments. *)
    val (arg_names, ctxt'')
        = Variable.variant_fixes ((map fst fn_args)) ctxt'
    val fn_arg_terms = map (fn (n, T) => Free (n, T)) (arg_names ~~ (map snd fn_args))

    (* Create our assumption. *)
    val assumptions =
        get_fn_prop ctxt'' true fn_name fn_free fn_arg_terms
        |> (fn (current_phase_prop, params_opt) => ( 
             [current_phase_prop |> apfst 
               (fold Logic.all (rev fn_arg_terms))]))
        |> map (apfst (Sign.no_vars ctxt' #> Thm.cterm_of ctxt'))
    val (thms, ctxt''') = Assumption.add_assumes (map fst assumptions) ctxt''
    val (thms, ctxt'''') = ctxt''' 
      |> fold_map (fn (thm, attrs) => Thm.proof_attributes attrs thm) 
           (thms ~~ map snd assumptions)
  in
    (fn_free, thms, ctxt'''')
  end
 
  (* Add assumptions: recursive calls first, matching the order in define_functions *)
  val (res, ctxt') = ctxt |> fold_map (
    fn (fn_name, is_fn_ptr_param) =>
      fn ctxt =>
        let
          val (free, thms, ctxt') =
              assume_func ctxt fn_name is_fn_ptr_param
        in
          ((fn_name, (free, thms)), ctxt')
        end)
     (map (fn f => (f, NONE)) (Symset.dest rec_callees))
in
  (ctxt', res)
end

(* Determine which functions are called by a code fragment.
 * Only function terms in callee_consts are used. *)
fun get_body_callees
      (callee_consts: string Termtab.table)
      (body: term)
      : symset =
  Term.fold_aterms (fn t => fn a =>
      (Termtab.lookup callee_consts t
          |> Option.map single
          |> the_default []) @ a)
      body []
  |> Symset.make;

(* Determine which recursive calls are actually used by a code fragment.
 * This is used to make adjustments to recursive function groups
 * between conversion and definition steps.
 *
 * callee_terms is a list of (is_recursive, func const, thm)
 * as provided by assume_called_functions_corres *)
fun get_rec_callees
      (callee_terms: (string * (term * thm list)) list)
      (body: term)
      : symset = let
    val callee_lookup =
          callee_terms |> List.mapPartial (fn (callee, (const, _)) =>
              SOME (const, callee)) 
          |> Termtab.make;
    in get_body_callees callee_lookup body end;

fun is_recursive_group infos group =
  let
    val recursive = null group orelse FunctionInfo.is_function_recursive (the (Symtab.lookup infos (hd group))) 
    val _ = @{assert} (forall (fn f => recursive = FunctionInfo.is_function_recursive (the (Symtab.lookup infos f))) group)
  in recursive end

fun prove_induction_case tac (attrss:attribute list list) ctxt i = Subgoal.FOCUS (fn {context, prems,...} => 
   let
     val (thms, ctxt) = context 
       |> fold_map (fn (thm, attrs) => Thm.proof_attributes attrs thm) (prems ~~ attrss)
   in
     tac thms ctxt
   end) ctxt i


fun mcont_tac ctxt i =
  REPEAT (
  resolve_tac ctxt @{thms mcont_id'} i
  ORELSE 
  (resolve_tac ctxt @{thms mcont2mcont_call} i THEN 
   TRY (EqSubst.eqsubst_tac ctxt [0]  @{thms gfp_lub_fun [symmetric]} i) THEN 
   TRY (EqSubst.eqsubst_tac ctxt [0]  @{thms gfp_le_fun [symmetric]} i)))


fun gen_corres_admissible_tac basic_rules ctxt = 
  (REPEAT' (resolve_tac ctxt basic_rules)) THEN_UNSOLVED
(*  simp_tac (Simplifier.clear_simpset ctxt addsimps @{thms gfp_lub_fun gfp_le_fun})  THEN' *)
  (Utils.dprint_subgoal_tac (!d1) "after simp" ctxt) THEN_UNSOLVED
  ( (REPEAT' (resolve_tac ctxt (@{thms admissible_subst_fun_lub_fun_ord} @ basic_rules)))  THEN_ALL_NEW 
    ((Utils.dprint_subgoal_tac (!d1) "after resolve admissible_subst_fun_lub_fun_ord" ctxt) THEN' SOLVED' (mcont_tac ctxt) ORELSE' 
      REPEAT_ALL_NEW (resolve_tac ctxt basic_rules THEN' (Utils.dprint_subgoal_tac (!d1) "after solve resolve" ctxt)))) 




fun corres_admissible_tac ctxt =
  let
    val structural_rules = @{thms admissible_imp admissible_all admissible_imp'}
    val corres_rules = Named_Theorems.get ctxt @{named_theorems corres_admissible}
    val basic_rules = structural_rules @ corres_rules
  in
    gen_corres_admissible_tac basic_rules ctxt
  end

fun prove_functions is_recursive induct_thms solve_non_recursive solve_recursive ctxt props  =
  let                  
    val defs = map (#1) props
    val paramss = map (#2) props
    val arbitrary_varss = map (#3) props
    val preds = map (#1 o #4) props 
    val attrss = map (#2 o #4) props

    val all_varss = map (fn (xs, ys) => xs @ ys) (paramss ~~ arbitrary_varss)
    val N = length props
    val top_thms = Named_Theorems.get ctxt @{named_theorems corres_top}

    val defs = defs |> map (Local_Defs.abs_def_rule ctxt)
    fun prove_non_recursive (def, _, _, (prop, attribs)) = 
          Goal.prove ctxt [] [] prop (fn {context, prems} => 
            EqSubst.eqsubst_tac context [1] defs 1 THEN
            solve_non_recursive context)

    fun admissibility_tac ctxt i = Seq.INTERVAL (corres_admissible_tac ctxt) i (i + N - 1)
    val bump_unify_bound = Config.map Unify.search_bound (fn n => n * N)
    val _ = if not (!d1) then () else
      let
        val _ = tracing (big_list_of_terms "prove_functions preds:" ctxt preds)
        val _ = tracing ("all_varss: " ^ @{make_string} all_varss)
        val _ = if (!d2) then tracing (big_list_of_thms "induct_thms:" ctxt induct_thms) else ()
      in () end
    val thms = 
      if is_recursive then
        let
        in
          Goal.prove_common ctxt NONE [] [] preds (fn {context, prems = _} =>
          Utils.dprint_tac (!d1) "prove_functions before induct" context THEN
          DETERM (Induct.induct_tac (bump_unify_bound context) false 
            []
            (map (map_filter (try dest_Free)) all_varss) []
            (SOME induct_thms) [] 1) THEN
          Utils.dprint_tac (!d1) "prove_functions after induct" context THEN
          (* solve admissibility *)
          admissibility_tac (bump_unify_bound context) 1 THEN (* FIXME: instantiate admissible_subst_fun_lub_fun_ord instead of bumping unification bound *) 
          Utils.dprint_tac (!d1) "prove_functions after admissiblity_tac" context THEN
          (* solve base-(top)-cases *)
          REPEAT_DETERM_N N (match_tac context top_thms 1) THEN
          Utils.dprint_tac (!d1) "prove_functions after top" context THEN
          (* solve induction-cases *)
          solve_recursive attrss context THEN 
          Utils.dprint_tac (!d1) "prove_functions after solve_recursive" context)
        end
      else
        map prove_non_recursive props
  in
    thms
  end 

fun WITH_NSUBGOALS tac st = 
   tac (Thm.nprems_of st) st 

fun subgoal_assm_tac all_prems = Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
  let
    val all_prems' = prems @ all_prems
  in
    (DETERM' (resolve_tac context all_prems') THEN_ALL_NEW subgoal_assm_tac all_prems' context) 1
  end)

fun subgoal_intro_tac thms = Subgoal.FOCUS (fn {context, prems, ...} => 
  let
    val n = length thms
  in
  (DETERM' (resolve_tac context thms)
    THEN_ALL_NEW (
      (DETERM' (resolve_tac context prems)) 
      THEN_ALL_NEW ( 
        ((*Method.assm_tac context ORELSE' *)subgoal_assm_tac prems context)))) 1
  end)

(* FIXME: remove clone in TS phase? *)
fun subgoal_intro_tac' thms = Subgoal.FOCUS (fn {context, prems, ...} => 
  let
    val n = length thms
    val hyps = take n prems
    val inst_thms = map (fn thm => thm OF hyps) thms
      
  in
  (resolve_tac context inst_thms 
      THEN_ALL_NEW (subgoal_assm_tac prems context)) 1
  end)

fun subgoal_intro_tac'' {instantiate} thms = 
  (if instantiate then Subgoal.FOCUS else Subgoal.FOCUS_PREMS) (fn {context, prems, ...} => 
  let
    val (thm_insts, other_prems) = 
      if instantiate then 
        let 
          val n = length thms
          val hyps = take n prems
          val rest = drop n prems
          val inst_thms = map (fn thm => thm OF hyps) thms
        in
          (inst_thms, rest)

        end
      else (thms, [])

  in
  (DETERM' (resolve_tac context thm_insts)
    THEN_ALL_NEW (
      (subgoal_intro_tac'' {instantiate=false} (prems@other_prems) context))) 1
  end)

fun apply f params = fold (fn x => fn f => f $ x) params f
fun lambdas [] t = t
   | lambdas (x::xs) t = Term.lambda x (lambdas xs t)

(*
 * Given one or more function specs, define them and instantiate corres proofs.
 *
 *   "callee_thms" contains corres theorems for already-defined functions.
 *
 *   "fn_infos" is used to look up function callees. It is expected
 *   to consist of the previous translation output for the functions
 *   being defined, but may of course contain other entries.
 *
 *   "functions" contains a list of (fn_name, (body, corres proof, arg_frees)).
 *   The body should be of the form generated by abstract_fn_body,
 *   with lambda abstractions for all callees and arguments.
 *
 *   The given corres proof is expected to use the free variables in
 *   arg_frees for the function's arguments (including the measure variable,
 *   if there if there is one). It is also expected to use schematic
 *   variables for assumed callees.
 *   (fixme: this interface should be simplified a bit.)
 *
 *   We assume that all functions in this list are mutually recursive.
 *   (If not, you should call "define_funcs" multiple times, each
 *   time with a single function.)
 *
 * Returns the new function constants, definitions, final corres proofs,
 * and local theory.
 *)
fun define_funcs_single_recursive_group
    (skips: FunctionInfo.skip_info) 
    (phase : FunctionInfo.phase)
    (prog_info: ProgramInfo.prog_info)
    (qualify: binding -> binding)
    concealed
    (get_const_name : string -> string)
    (get_fn_type : string -> typ)
    (get_fn_prop : Proof.context -> bool -> string -> term -> term list ->  
       ((term * attribute list) * term list option))
    (get_fn_args_def : string -> (string * typ) list)
    (get_fn_args_prop : string -> (string * typ) list)
    (functions : (string * (term * thm * (string * typ) list)) list)
    (lthy : local_theory)
  : string list * local_theory =
  let
    val _ = @{assert} (not (null functions));
    val fn_names = map fst functions
    val fn_bodies = map (snd #> #1) functions
    val fn_thms = map (#2 o #2) functions
    val N = length fn_names

    val prev_phase = FunctionInfo.prev_phase skips phase
 
    val fn_names_str = commas (map get_const_name fn_names);
    val filename = ProgramInfo.get_prog_name prog_info

    val _ = writeln ("Defining (" ^ FunctionInfo.string_of_phase phase ^ ") " ^ fn_names_str)

    (*
     * Determine if we are in a recursive case by checking to see if the
     * first function in our list makes recursive calls to any other
     * function. (This "other function" will be itself if it is simple
     * recursion, but may be a different function if we are mutually
     * recursive.)
     *)
    fun get_prev_info lthy name = 
      AutoCorresData.get_function_info (Context.Proof lthy) filename prev_phase name |> the 
    val is_recursive = FunctionInfo.is_function_recursive (get_prev_info lthy (hd fn_names))
    val _ = assert (length fn_names = 1 orelse is_recursive)
            "define_funcs passed multiple functions, but they don't appear to be recursive."

    (*
     * Patch in functions into our function body in the following order:
     *
     *    * Non-recursive calls;
     *    * Recursive calls
     *)
    fun fill_body fn_name body =
    let
      val fn_info = get_prev_info lthy fn_name
      val rec_calls = map (fn x => Free (get_const_name x, get_fn_type x)) (Symset.dest (FunctionInfo.get_rec_callees fn_info))
    in
      body
      |> (fn t => betapplys (t, rec_calls))
    end

    (*
     * Define our functions.
     *
     * Definitions should be of the form:
     *
     *    %arg1 arg2 arg3. (arg1 + arg2 + arg3)
     *
     * Mutually recursive calls should be of the form "Free (fn_name, fn_type)".
     *)
    val defs = map (
        fn (fn_name, fn_body) => let
            val fn_args = get_fn_args_def fn_name
            (* fixme: this retraces assume_called_functions_corres *)
            val (fn_free ::  arg_frees, _) = Variable.variant_fixes
                    (get_const_name fn_name :: map fst fn_args) lthy
            in (fn_name, get_const_name fn_name, (* be inflexible when it comes to fn_name *)
                 (arg_frees ~~ map snd fn_args), (* changing arg names is ok *)
                fill_body fn_name fn_body) end)
        (fn_names ~~ fn_bodies)

    val _ = if (!d1) then tracing ("define_funcs_single_recursive_group: before definition") else ()
    val lthy = lthy |>  AutoCorresData.in_theory'
      (fn lthy => 
        let 
           val (_, lthy') = lthy |> Utils.define_functions defs qualify true is_recursive "spec_monad_gfp"
             [AutoCorresData.define_function_attribute concealed filename skips phase] [] []
        in lthy' end)
    val _ = if (!d1) then tracing ("define_funcs_single_recursive_group: before fn_defs (0)") else ()

    val fn_def_thms = map (FunctionInfo.get_definition o the o (AutoCorresData.get_function_info (Context.Proof lthy) filename phase)) fn_names
    val _ = if (!d1) then tracing ("define_funcs_single_recursive_group: before fn_defs (1)") else ()
    val fn_def_thms = fn_def_thms |> map (safe_mk_meta_eq) 
    val _ = if (!d1) then tracing ("define_funcs_single_recursive_group: before induct_thms") else ()
    fun get_induct_thms () = 
      let
        val c = hd fn_def_thms |> Thm.lhs_of |> Thm.term_of |> Term.head_of 
      in
        Mutual_CCPO_Rec.lookup_info_trimmed (Context.Proof lthy) c |> the_list |> maps #inducts
      end

    val induct_thms = timeit_msg 1 lthy (fn _ => "induct_thms") (get_induct_thms)

    (*
     * Instantiate schematic function calls in our theorems with their
     * concrete definitions.
     *)
    val _ = if (!d1) then tracing ("define_funcs_single_recursive_group: before combined_thms") else ()
    val combined_callees = map (get_callees o get_prev_info lthy) (map fst functions)
    val _ = if (!d1) then tracing ("define_funcs_single_recursive_group: before combined_normal_calls") else ()
    val combined_normal_calls =
        map fst combined_callees |> flat |> sort_distinct fast_string_ord

    (* The non-recursive callee's correspondence theorems *)
    fun get_corres_thm name = AutoCorresData.get_function_info (Context.Proof lthy) filename phase name 
      |> the |> FunctionInfo.get_corres_thm
    val _ = if (!d1) then tracing ("define_funcs_single_recursive_group: before nrec_corres_thms") else ()
    val nrec_corres_thms = map get_corres_thm combined_normal_calls

    val _ = if (!d1) then tracing ("define_funcs_single_recursive_group: before props") else ()
    (* Generate corres predicates for each function. *)
    val (props, ctxt') = lthy |> fold_map (
      fn (fn_name, def) => fn ctxt =>
      let
        val fn_const = Utils.get_term lthy (get_const_name fn_name)

        (* Fetch parameters to this function. *)
        val (params, ctxt') = Utils.fix_variant_frees (get_fn_args_prop fn_name) ctxt
        (* Generate the prop. *)
        val ((corres_prop_current_phase, attrs), params_opt) = get_fn_prop ctxt' false fn_name fn_const params
        val params' = the_default params params_opt
        val changed_params = filter_out (member (op =) params) params'
        val ((arbitrary_vars, corres_prop_current_phase), ctxt') = Utils.import_universal_prop corres_prop_current_phase ctxt'
      in       
        ((def, params', arbitrary_vars @ changed_params, (corres_prop_current_phase, attrs)), ctxt')
      end) (fn_names ~~ fn_def_thms)
 
    fun solve_recursive _ ctxt = (*ALLGOALS *) REPEAT (subgoal_intro_tac'' {instantiate=false} fn_thms ctxt 1)
    fun solve_non_recursive ctxt =  (             
      match_tac ctxt fn_thms
      THEN_ALL_NEW 
         (((EVERY' [match_tac ctxt (nrec_corres_thms)]) THEN_ALL_NEW Method.assm_tac ctxt)
         ORELSE' 
         (* function-ptr-parameter assumptions *)
         Method.assm_tac ctxt)
      ORELSE' (K (print_tac ctxt "define_funcs_single_recursive_group final proof failed")))
      1

    val _ = if (!d1) then tracing ("define_funcs_single_recursive_group: before corres_thms") else ()
    val corres_thms = prove_functions is_recursive induct_thms solve_non_recursive solve_recursive ctxt' props
                          
    (*
     * Export the correspondence theorems in the original context.
     *)
    val corres_thms =
      corres_thms
      |> Variable.export ctxt' lthy
      |> map (Goal.norm_result lthy) 

    val _ = if (!d1) then tracing ("define_funcs_single_recursive_group: before define_lemma") else ()
    val (corres_thms, lthy) = lthy 
      |> fold_map (fn (name, thm) => Utils.define_lemma (Binding.name (AutoCorresData.corres_thm_name prog_info phase name)) 
             [AutoCorresData.corres_thm_attribute filename skips phase name] thm)
           (fn_names ~~ corres_thms)
    val _ = if (!d1) then tracing ("define_funcs_single_recursive_group: end") else ()
  in
    (fn_names, lthy)
  end

fun gen_define_funcs 
    (skips: FunctionInfo.skip_info) 
    (phase : FunctionInfo.phase)
    (prog_info: ProgramInfo.prog_info)
    (qualify: binding -> binding)
    concealed
    (get_const_name : string -> string)
    (get_fn_type : string -> typ)
    (get_fn_prop: Proof.context -> bool -> string -> term -> term list -> 
       ((term * attribute list) * term list option))
    (get_fn_args_def : string -> (string * typ) list)
    (get_fn_args_prop : string -> (string * typ) list)
    (functions : (string * (term * thm * (string * typ) list)) list)
    (lthy : local_theory)
  : string list * Proof.context =
let
   val prev_phase = FunctionInfo.prev_phase skips phase
   fun is_recursive name = AutoCorresData.get_function_info (Context.Proof lthy) (ProgramInfo.get_prog_name prog_info) prev_phase 
     name |> the |> FunctionInfo.is_function_recursive

   val funcss = if null functions orelse is_recursive (fst (hd functions)) 
                then [functions]
                else map (fn x => [x]) functions
in
  ([], lthy) |> fold (fn funcs => fn (names, lthy)  =>
      let 
        val (new_names, lthy') = lthy |>
            define_funcs_single_recursive_group
              skips phase prog_info qualify concealed get_const_name get_fn_type get_fn_prop get_fn_args_def get_fn_args_prop
              funcs
      in (names @ new_names, lthy') end) funcss
end


fun define_funcs 
    (skips: FunctionInfo.skip_info) 
    (phase : FunctionInfo.phase)
    (prog_info: ProgramInfo.prog_info)
    (qualify: binding -> binding)
    concealed
    (get_const_name : string -> string)
    (get_fn_type : string -> typ)
    (get_fn_prop: Proof.context -> bool -> string -> term -> term list -> 
       ((term * attribute list) * term list option))
    (get_fn_args : string -> (string * typ) list)
    (functions : (string * (term * thm * (string * typ) list)) list)
    (lthy : local_theory) = 
  gen_define_funcs skips phase prog_info qualify concealed get_const_name get_fn_type get_fn_prop
    get_fn_args get_fn_args
    functions lthy

(* Utility for doing conversions in parallel.
 * The conversion of each function f should depend only on the previous
 * define phase for f (which necessarily also includes f's callees). *)
type convert_result = {
       body: term, (* new body *)
       proof: thm, (* corres thm *)
       rec_callees: symset, (* minimal rec_callees after translation *)
       callee_consts: term Symtab.table, (* assumed frees for other callees *)
       arg_frees: (string * typ) list (* fixed argument frees *)
     }


fun in_corres_locale_result prog_info skips phase filename clique f lthy =
  let
    val loc = NameGeneration.intern_globals_locale_name (Proof_Context.theory_of lthy) filename
  in AutoCorresData.in_locale_result loc f lthy end


fun in_corres_locale prog_info skips phase filename clique f lthy =
  let
    val loc = NameGeneration.intern_globals_locale_name (Proof_Context.theory_of lthy) filename
   in AutoCorresData.in_locale_result loc (fn lthy => f lthy) lthy end

(* Given a function body containing arguments and assumed function calls,
 * abstract the code over those parameters.
 *
 * The returned body will have free variables as placeholders for the function's
 * measure parameter and other arguments, as well as for the functions it calls.
 *
 * We modify the body to be of the form:
 *
 *     %fun1 fun2 rec1 rec2 measure arg1 arg2. f <...>
 *
 * That is, all non-recursive calls are abstracted out the front, followed by
 * recursive calls, followed by the measure variable, followed by function
 * arguments. This is the format expected by define_funcs.
 *)
fun abstract_fn_body
      (prev_fn_infos: FunctionInfo.function_info Symtab.table)
      (fn_name, {body, callee_consts, arg_frees, ...} : convert_result) = let
  val (callees, rec_callees) = get_callees' prev_fn_infos fn_name;
  val rec_calls = map (the o Symtab.lookup callee_consts) rec_callees;

  val abs_body = body
        |> fold lambda (rev (map Free arg_frees))
        |> fold lambda (rev rec_calls)
  in abs_body end;

fun update_defined t1 t2 =
  Symtab.map (fn key => fn x =>
   case Symtab.lookup t2 key of
     NONE => x
   | SOME y => y) t1

fun restrict_domain keys t =
  [] 
  |> fold (fn k => fn xs => case Symtab.lookup t k of NONE => xs | SOME y => (k,y)::xs) keys
  |> Symtab.make


fun split_infos infos names =
 let
   val infos_without_names = infos |> fold Symtab.delete_safe names
   val infos_of_names = restrict_domain names infos
  in
    (infos_without_names, infos_of_names)
  end

fun no_prepare (finfos: FunctionInfo.function_info Symtab.table) (clique: string list) (lthy:local_theory) = lthy

fun do_prepare skips prog_info phase prepare clique lthy =
  if pointer_eq (prepare, no_prepare) then 
    lthy
  else
     let
       val prev_phase = FunctionInfo.prev_phase skips phase
       val filename = ProgramInfo.get_prog_name prog_info 
       val infos = AutoCorresData.get_default_phase_info (Context.Proof lthy) filename prev_phase
     in
       timeit_prepare_msg' 1 lthy phase clique (fn _ => prepare infos clique lthy)   
     end
     
fun convert_and_define_clique 
      (skips: FunctionInfo.skip_info)
      (prog_info: ProgramInfo.prog_info)
      (* The phase we are converting to *)
      (phase: FunctionInfo.phase)
      (parallel: bool)
      (* Worker: lthy -> function_infos for func and callees -> func name -> results *)
      (convert: local_theory -> FunctionInfo.function_info Symtab.table ->
                string -> convert_result)
      (define: local_theory ->
                      convert_result Symtab.table ->
                      (* new infos for functions *)
                      local_theory)
      (todo_clique: string list) (* (prev_results: FunctionInfo.phase_results) *)
      (lthy: local_theory)
      : (string list list * local_theory)
  = 
  let
    val prev_phase = FunctionInfo.prev_phase skips phase
    val par_map = if parallel then Par_List.map else map
    val filename = ProgramInfo.get_prog_name prog_info
    val existing_infos_prev_phase = AutoCorresData.get_default_phase_info (Context.Proof lthy) filename prev_phase
    val existing_infos_current_phase = AutoCorresData.get_default_phase_info (Context.Proof lthy) filename phase
    val recursive_group = is_recursive_group existing_infos_prev_phase todo_clique

    val loc = the (Named_Target.bottom_locale_of lthy)
    val _ = case todo_clique of [] => () | stuff => 
        verbose_msg 0 lthy (fn _ => "Conversions (" ^ FunctionInfo.string_of_phase phase ^ 
                 ") for: " ^ commas stuff ^ " in locale " ^ loc) 

    val conv_results =
      todo_clique
      |> par_map (fn fname =>
        (fname, timeit_conversion_msg' 1 lthy phase fname (fn () => convert lthy existing_infos_prev_phase fname)))
      |> Symtab.make;
    val lthy = if Symtab.is_empty conv_results then lthy else
      define lthy conv_results;
    val new_infos = AutoCorresData.get_phase_info (Context.Proof lthy) filename phase 
      |> the |> restrict_domain todo_clique

    val new_infoss = FunctionInfo.recalc_callees existing_infos_current_phase new_infos  

        (* Minimise callees and split recursive group if needed. *)
    val new_groups = map (map fst o Symtab.dest) new_infoss
    val lthy = lthy
      |> fold (fn group => 
           AutoCorresData.in_theory' (
             Local_Theory.declaration {pervasive=true, syntax=false, pos=\<^here>} (fn phi => 
                 AutoCorresData.map_default_phase_info filename phase 
                      (FunctionInfo.transfer_call_graph_infoss new_infoss))
            ))
         new_groups
    val groups_next_phase = if not recursive_group then [todo_clique] else new_groups
  in (groups_next_phase, lthy) end



fun gen_convert_and_define_cliques
      (* Some preparation in definition locale of previous phase *)
      (prepare: FunctionInfo.function_info Symtab.table -> string list -> local_theory -> local_theory)
      (skips: FunctionInfo.skip_info)
      (base_locale_opt: string option)
      (prog_info: ProgramInfo.prog_info)
      (* The phase we are converting to *)
      (phase: FunctionInfo.phase)
      (parallel: bool)
      (* Worker: lthy -> function_infos for func and callees -> func name -> results *)
      (convert: local_theory -> FunctionInfo.function_info Symtab.table ->
                string -> convert_result)
      (define: local_theory ->
                      (* data for functions *)
                      convert_result Symtab.table ->
                      (* new infos for functions in lthy *)
                      local_theory)
      (cliques: string list list) 
      (lthy: local_theory)
      : (string list list * local_theory)
  = 
let
  val prev_phase = FunctionInfo.prev_phase skips phase
  val filename = ProgramInfo.get_prog_name prog_info
  fun do_or_skip_group clique lthy =
    (* avoid entering the potential costly corres-locale if nothing is to be done *)
    let
      val existing_infos_current_phase = AutoCorresData.get_default_phase_info (Context.Proof lthy) filename phase
      val infos_prev_phase = AutoCorresData.get_default_phase_info (Context.Proof lthy) filename prev_phase
      val todo_clique = clique 
        |> filter_out (fn name =>
           member (op =) (Symtab.keys existing_infos_current_phase) name)
 
      val (groups_next_phase, lthy) = 
        if todo_clique = clique 
        then 
          lthy 
          |> do_prepare skips prog_info phase prepare clique 
          |> in_corres_locale_result prog_info skips phase filename clique 
              (convert_and_define_clique skips prog_info phase parallel convert define clique) 
        else 
          let
            val _ = @{assert} (null todo_clique)
            (* calculate new clique from existing infos *)
            val (infos_without_names, infos_of_names) = split_infos existing_infos_current_phase clique
            val groups_next_phase =  
             FunctionInfo.recalc_callees infos_without_names infos_of_names
              |> map (map fst o Symtab.dest)
           in
             (groups_next_phase, lthy)
           end 
      val _ = verbose_msg 1 lthy (fn _ => "groups_next_phase: " ^ @{make_string} groups_next_phase) 
   in
     (groups_next_phase, lthy)  
   end 
in
  ([], lthy) 
  |> fold (fn clique => fn (cliques, lthy) =>
         let
           val (new_cliques, lthy) = do_or_skip_group clique lthy
         in (cliques @ new_cliques, lthy) end)
     cliques
end

val convert_and_define_cliques = gen_convert_and_define_cliques no_prepare

end

