(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Lift monadic structures into lighter-weight monads.
 *)
structure TypeStrengthen =
struct

val timeit_msg = Utils.timeit_msg
val verbose_msg = Utils.verbose_msg

exception AllLiftingFailed of (string * thm) list
exception LiftingFailed of unit


(* Misc util functions. *)
val the' = Utils.the'
val apply_tac = Utils.apply_tac

fun state_typ finfo =
  let
    val term = FunctionInfo.get_const finfo;
    val res = AutoCorresData.state_type_of_exn_monad term
  in
    res
  end;

fun get_l2_state_typ l2_infos fn_name =
  state_typ (the (Symtab.lookup l2_infos fn_name))



fun get_typ_from_L2 (rule_set : Monad_Types.monad_type) L2_typ =
  let
    val res = FunctionInfo.dest_exn_monad_type L2_typ |> snd |> #typ_from_L2 rule_set
  in
    res
  end



 
 

(*
 * Make an equality prop of the form "L2_call <foo> = <liftE> $ <bar>".
 *
 * L2_call and <liftE> will typically be desired to be polymorphic in their
 * exception type. We fix it to "unit"; the caller will need to introduce
 * polymorphism as necessary.
 *
 * If "state_typ" is non-NONE, then "measure" is assumed to also take a
 * state parameter of the given type.
 *)
type fn_ptr_infos = (string * (FunctionInfo.phase -> AutoCorresData.fn_ptr_info)) list
fun get_ts_corres_prop dyn_call ctxt skips prog_info prev_phase  l2_infos fn_name
    (rule_set : Monad_Types.monad_type) state args rhs_term =
let
  (*val dyn_call = false*) (* FIXME *)
  val ts_corres_attr = AutoCorresData.corres_thm_attribute (ProgramInfo.get_prog_name prog_info) skips FunctionInfo.TS fn_name
  val synth_attr = Synthesize_Rules.add_rule_attrib (#rules_name (#refines_nondet rule_set)) {only_schematic_goal = false} 
       (Binding.make (fn_name ^ "_recursion" , \<^here>)) 10

  val (old_fn, new, args) = 
        let
          val fn_def = the (Symtab.lookup l2_infos fn_name)
        in (FunctionInfo.get_const fn_def, rhs_term, args) end
   
  val lift = #lift (#refines_nondet rule_set)
  val old = betapplys (old_fn, args)
  val sT = AutoCorresData.state_type_of_exn_monad old
  val resT = AutoCorresData.res_type_of_exn_monad old
  val exT = AutoCorresData.ex_type_of_exn_monad old
  val relator = (case exT of
         \<^Type>\<open>c_exntype _\<close> => Monad_Types.relator_from_c_exntype (#refines_nondet rule_set)
        | _ => #relator (#refines_nondet rule_set))

  val term = (
     \<^instantiate>\<open>
         's = sT and 'a = resT and 'f = exT and 'x = dummyT and 'e = dummyT and 'b = dummyT and 
         s = \<open>Free("s", sT)\<close> and old = old and lift=\<open>Utils.dummy lift\<close> and 
         new = new and relator=\<open>Utils.dummy relator\<close>
       in 
         prop \<open>refines old (lift new) s s (rel_prod relator (=))\<close> 
       for s::'s and old::\<open>('f, 'a, 's) exn_monad\<close> and 
           lift::\<open>'x \<Rightarrow> ('e::default, 'b, 's) spec_monad\<close> and new::'x and
           relator::\<open>('f, 'a) xval \<Rightarrow> ('e::default, 'b) exception_or_result \<Rightarrow> bool\<close>\<close> |> Utils.infer_types_simple ctxt)
      handle ERROR str => (* E.g. when trying to lift into pure monad from a nondet-monad *)
          (Utils.verbose_msg 1 ctxt (fn _ => "type strengthening into " ^ quote (#name rule_set) ^ " failed:\n" ^ str); 
            raise LiftingFailed ()) 
       

in
 ([],
  (term, [ts_corres_attr, synth_attr]))
end

(*
 * Assume recursively called functions correctly map into the given type.
 *
 * We return:
 *
 *   (<newly generated context>,
 *    <the measure variable used>,
 *    <generated assumptions>,
 *    <table mapping free term names back to their function names>,
 *    <morphism to escape the context>)
 *
 * fixme: refactor with AutoCorresUtil.assume_called_functions_corres
 *)
fun assume_rec_lifted ctxt skips prog_info l2_infos prev_phase make_function_name rule_set 
      state rec_fn_fixes recursive_calls fn_name =
let


  (* For each recursive call, generate a theorem assuming that it lifts into
   * the type/monad of "rule_set". *)
  val (rec_frees, assumptions_rec) = map (fn (callee, name) =>
    let
      val fn_def' = the (Symtab.lookup l2_infos callee)
      val args = FunctionInfo.get_plain_args fn_def' |> (fn xs => Utils.fix_variant_frees xs ctxt) |> fst |> map dest_Free
      val T = map snd args
          ---> (fastype_of (FunctionInfo.get_const fn_def') |> get_typ_from_L2 rule_set)
      val args = map Free args
      (* NB: pure functions would not use state, but recursive functions cannot
       * be lifted to pure (because we trigger failure when the measure hits
       * 0). So we can always assume there is state. *)
      val state_typ = get_l2_state_typ l2_infos fn_name
      val free = Free (name, T)
      val (prev_props, prop) = 
        get_ts_corres_prop true ctxt skips prog_info prev_phase l2_infos callee
           rule_set state args (betapplys(free, args))
    in
      (free, map (apfst (Thm.cterm_of ctxt)) (prev_props @ [apfst (fold Logic.all (rev (state::args))) prop])) 
    end) (recursive_calls ~~ rec_fn_fixes) 
    |> split_list |> apsnd flat   

 
  val assumptions = assumptions_rec 
  (* Assume the theorems we just generated. *)
  val (thms, ctxt_asms) = Assumption.add_assumes (map fst assumptions) ctxt
  val (thms, ctxt_asms) = ctxt_asms 
      |> fold_map (fn (thm, attrs) => Thm.proof_attributes attrs thm) 
           (thms ~~ map snd assumptions)
  val export_assms = Assumption.export_morphism ctxt_asms ctxt

in
  (ctxt_asms,
   thms,
   rec_frees,
   export_assms)
end

fun mk_corresTS_fun_ptr_thm prog_info (rec_funs, rec_ptrs) ctxt ((P_prev as Const (_, T_prev), _), (P as Const (Pname, T), monad_type)) =
 let
   val (ptrT::prev_argTs, ret_prevT) = strip_type T_prev
   val funT = let val (ptrT::argTs, retT) = strip_type T in argTs ---> retT end
   fun mk_fun_ptr fname = HP_TermsTypes.mk_fun_ptr ctxt (ProgramInfo.get_prog_name prog_info) fname
   val (empty, ptr_assoc) = map_filter (fn fname => find_first (fn (n, _) => n = fname) rec_funs) rec_ptrs
     |> filter (fn (_, Free (_, fT)) => fT = funT)  
     |> `null 
     ||> map (apfst mk_fun_ptr) ||> map HOLogic.mk_prod 
     ||> HOLogic.mk_list (HOLogic.mk_prodT (@{typ "unit ptr"}, funT))
   val _ = if empty andalso not (null rec_funs) then raise Match else ()

   val {exT=ex_prevT, resT= ret_prevT, stateT} = AutoCorresData.dest_exn_monad_result_type ret_prevT


   val mt = Monad_Types.get_monad_type monad_type (Context.Proof ctxt) |> the
   val lift = #lift (#refines_nondet mt)
   val relator = (case ex_prevT of
         \<^Type>\<open>c_exntype _\<close> => Monad_Types.relator_from_c_exntype (#refines_nondet mt)
        | _ => #relator (#refines_nondet mt))
   val args = map (fn T => ("x", T)) prev_argTs
   val (s::p::args, ctxt') = Utils.fix_variant_frees ([("s", stateT), ("p", ptrT)] @ args) ctxt
   val old = betapplys (P_prev, p::args)
   val P = if empty then P else \<^infer_instantiate>\<open>P = P and xs = ptr_assoc in term \<open>map_of_default P xs\<close>\<close> ctxt'
   val new = betapplys (P, p::args)
   val resT = AutoCorresData.res_type_of_exn_monad old
   val exT = AutoCorresData.ex_type_of_exn_monad old
   val corres = (
     \<^instantiate>\<open>
         's = stateT and 'a = resT and 'f = exT and 'x = dummyT and 'e = dummyT and 'b = dummyT and 
         s = \<open>s\<close> and old = old and lift=\<open>Utils.dummy lift\<close> and 
         new = new and relator=\<open>Utils.dummy relator\<close>
       in 
         prop \<open>refines old (lift new) s s (rel_prod relator (=))\<close> 
       for s::'s and old::\<open>('f, 'a, 's) exn_monad\<close> and 
           lift::\<open>'x \<Rightarrow> ('e::default, 'b, 's) spec_monad\<close> and new::'x and
           relator::\<open>('f, 'a) xval \<Rightarrow> ('e::default, 'b) exception_or_result \<Rightarrow> bool\<close>\<close> |> Utils.infer_types_simple ctxt)
   val corres_pre = @{term DYN_CALL} $ corres
   val goal = Logic.mk_implies (corres_pre, corres)
   val [thm] = Goal.prove ctxt' [] [] goal (fn {context, ...} =>
      asm_full_simp_tac (context addsimps @{thms DYN_CALL_def} delsimps @{thms map_of_default.simps}) 1) 
      |> single |> Proof_Context.export ctxt' ctxt
 in
   [(monad_type, thm)]
 end 
 handle Match => []

(*
 * Given a function definition, attempt to lift it into a different
 * monadic structure by applying a set of rewrite rules.
 *
 * For example, given:
 *
 *    foo x y = doE
 *      a <- returnOk 3;
 *      b <- returnOk 5;
 *      returnOk (a + b)
 *    odE
 *
 * we may be able to lift to:
 *
 *    foo x y = returnOk (let
 *      a = 3;
 *      b = 5;
 *    in
 *      a + b)
 *
 * This second function has the form "lift $ term" for some lifting function
 * "lift" and some new term "term". (These would be "returnOk" and "let a = ...
 * in a + b" in the example above, respectively.)
 *
 * We return a theorem of the form "foo x y == <lift> $ <term>", along with the
 * new term "<term>". If the lift was unsuccessful, we return "NONE".
 *)


fun perform_lift ctxt skips prog_info l2_infos prev_phase make_function_name rule_set fn_name =
let
  val f_info = the (Symtab.lookup l2_infos fn_name)

  (* Fix a variable for each such call, plus another for our measure variable. *)
  (* Find recursive calls. *)
  val recursive_calls = Symset.dest (FunctionInfo.get_recursive_clique f_info)
  val rec_names = map (make_function_name) recursive_calls
  val (rec_fn_fixes, ctxt1_fun_names)
       = Variable.add_fixes (map (make_function_name) recursive_calls) ctxt

  val _ = @{assert} (rec_fn_fixes = rec_names)


  val ([state], ctxt2_state) = ctxt1_fun_names |>  Utils.fix_variant_frees [("s", state_typ f_info)];


  (* Fix argument variables. *)
  val args = FunctionInfo.get_plain_args f_info;
  val (arg_frees, ctxt3_args) = Utils.fix_variant_frees args ctxt2_state;

  val export_fun_names = Variable.export_morphism ctxt1_fun_names ctxt
  val export_measure = Variable.export_morphism ctxt2_state ctxt1_fun_names
  val export_args = Variable.export_morphism ctxt3_args ctxt2_state


  (* Assume recursive calls can be successfully lifted into this type. *)
  val (ctxt4_rec_assms, thms, rec_frees, export_assms)
      = assume_rec_lifted ctxt3_args skips prog_info l2_infos prev_phase make_function_name rule_set 
          state rec_fn_fixes recursive_calls fn_name

  val fn_def = FunctionInfo.get_definition f_info

  (* Rewrite the term using the given rewrite rules. *)

  val synth  = Var (("_p", 0), (fastype_of (FunctionInfo.get_const f_info) |> get_typ_from_L2 rule_set))
  
  val (_, (goal,_)) = get_ts_corres_prop true ctxt4_rec_assms skips prog_info prev_phase l2_infos fn_name rule_set 
        state arg_frees synth

  val rewrite = Monad_Convert.sim_nondet prog_info FunctionInfo.TS ctxt4_rec_assms rule_set fn_def

(*
  val rewrite = if is_some (#rel_nondet_monad_rewrite rule_set) 
    then Monad_Convert.rel_nondet_monad_rewrite ctxt4_rec_assms prog_info rule_set prevs 
           (callee_names @ rec_names) (callee_thms @ thms @ more_corres) (mono_thms @ more_mono) (fun_ptr_callee_thms @ more_corres)
    else Monad_Convert.monad_rewrite ctxt4_rec_assms (SOME prog_info) [] rule_set  (callee_thms @ thms @ more_corres) fun_ptr_callee_thms true
  *)
  val maybe_thm = rewrite goal 
    |> Option.map (Morphism.thm (export_assms $> export_args $> export_measure))

  val _ = case maybe_thm of NONE => warning ("lifting failed for (" ^ #name rule_set ^ "): " ^ fn_name) | _ => ()
in
  (* Determine if the lifting succeeded. *)
  maybe_thm |> Option.map (rpair export_fun_names)

end

(* Like perform_lift, but also applies the polishing rules, hopefully yielding
 * an even nicer definition. *)
fun perform_lift_and_polish ctxt skips prog_info fn_info prev_phase make_function_name rule_set do_polish keep_going fn_name =
  case (timeit_msg 2 ctxt (fn _ => "trying type strengthening to '" ^ #name rule_set ^ "'-monad for function: "  ^ fn_name)   
         (fn () => perform_lift ctxt skips prog_info fn_info prev_phase make_function_name rule_set fn_name))
  of NONE => NONE
  | SOME (thm,  export_fun_names) => SOME let
  val _ = verbose_msg 3 ctxt (fn _ => "before polish thm: " ^ Thm.string_of_thm ctxt thm)
  val fun_names = ProgramInfo.get_csenv prog_info |> ProgramAnalysis.get_functions |> map make_function_name
    |> map (Syntax.read_term ctxt) |> map_filter (try (fst o dest_Const o head_of))  

  fun pretty_bounds_conv ctxt  = 
    (PrettyBoundVarNames.pretty_bound_vars_thm keep_going ctxt fun_names)
  (* Apply any polishing rules. *)
  val polish_thm = timeit_msg 1 ctxt (fn _ => "Polish - " ^ fn_name) 
    (fn _ => Monad_Convert.polish_refines ctxt rule_set do_polish 
       pretty_bounds_conv 
       map_of_default_args.fold_map_of_default_conv thm)
in (polish_thm,  export_fun_names) end


(*
 * Attempt to lift a function (or recursive function group) into the given monad.
 *
 * If successful, we define the new function (vis. group) to the theory.
 * We then return a theorem of the form:
 *
 *   "L2_call foo x y z == <lift> $ new_foo x y z"
 * where "lift" is a lifting function, such as "returnOk" or "gets", etc.
 *
 * If the lift does not succeed, the function returns NONE.
 *
 * The callees of this function need to be already translated in ts_infos
 * and also defined in lthy.
 *)

fun get_body ctxt (mt:Monad_Types.monad_type) @{term_pat "refines ?f ?new _ _ _"} =
     (case #dest_lift (#refines_nondet mt) new of
        SOME f' => (f, f')
       | NONE => (f, new))

(* FIXME: move to autocorres_util and integrate also in to prove_functions *)
fun admissibility_tac ctxt thms i =
  Seq.INTERVAL 
    (REPEAT_ALL_NEW  
      (match_tac ctxt (@{thms admissible_imp admissible_all admissible_imp'} @ thms))) 
    1 i

(* FIXME: sync with variant in autocorres_util.ML *)
fun subgoal_intro_tac' thms = Subgoal.FOCUS (fn {context, prems, ...} => 
  let
    val n = length thms
    val hyps = take n prems
    val inst_thms = map (fn thm => thm OF hyps) thms
      
  in
  (resolve_tac context inst_thms 
      THEN_ALL_NEW (AutoCorresUtil.subgoal_assm_tac prems context)) 1
  end)

fun lift_function_rewrite rule_set filename skips prog_info prev_phase l2_infos ts_infos
    fn_names make_function_name do_polish keep_going lthy =
let
  val ts_monad_name = #name rule_set
  val _ = verbose_msg 2 lthy (fn _ => "TS trying rule set: " ^ ts_monad_name)
  (* The general approach is: 
   * 1. First derive the new body by performing a hypothetical
   *    proof of an equation while assuming that all recursive calls are in the target monad.
   * 2. If successful we then take the body of the derived equation as a template to 
   *    actually define the new functions.
   * 3. Discharge the assumptions of 1 with the new defined functions in 2 by doing an
   *    induction proof to resolve recursion.
   *)
  val these_l2_infos = map (the o Symtab.lookup l2_infos) fn_names
  val is_recursive = exists FunctionInfo.is_function_recursive these_l2_infos
  val _ = if is_recursive andalso #ccpo_name rule_set = "" then raise LiftingFailed () else ()


  (*
   * Attempt to lift all functions into this type.
   *
   * For mutually recursive functions, every function in the group needs to be
   * lifted in the same type.
   *
   * Eliminate the "SOME", raising an exception if any function in the group
   * couldn't be lifted to this type.
   *)
  val lifted_functions = 
    map (perform_lift_and_polish lthy skips prog_info l2_infos prev_phase make_function_name rule_set do_polish keep_going) fn_names
  val lifted_functions = map (fn x =>
      case x of
          SOME a => a
        | NONE => raise LiftingFailed ())
      lifted_functions
  fun simplified ctxt thms = Simplifier.full_simplify ((Raw_Simplifier.clear_simpset ctxt) addsimps thms)
  val thms = map (simplified lthy @{thms DYN_CALL_def} o #1) lifted_functions 
  val morphs = map #2 lifted_functions

  (*
   * Generate terms necessary for defining the function, and define the
   * functions.
   *)
  fun gen_fun_def_term (fn_name, thm)  =
  let
    (* Import the derived equality to fix the arguments of the function.
     * Note that we abstract over them as they become the lhs of the defining equation,
     * so there is no need to give back the new context.
     *)
    val nargs = Symtab.lookup l2_infos fn_name |> the |> FunctionInfo.get_args |> length
    val (((typ_inst, var_inst), [imp_thm]), _) = Variable.import true [thm] lthy
    val (orig, new) = imp_thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> get_body lthy rule_set
    val args = strip_comb orig |> snd |> rev |> take nargs |> rev
    (* Extract the body from the conversion theorem.
     * E.g. for "L2_call foo = liftE body" we extract "body". *)
 
    (* Abstract over args, which are now known arg frees *)
    val term = foldr (fn (v, t) => Utils.abs_over "" v t) new args
  in
    (fn_name, make_function_name fn_name, map dest_Free args, term)
  end


  val phase = FunctionInfo.TS

  val input_defs = map gen_fun_def_term (fn_names ~~ thms)
  fun src_name n = get_first (fn (orig, n', _, _ ) => if n = n' then SOME orig else NONE) input_defs
  val do_guard_simps =  member (op =) ["nondet", "exit"] ts_monad_name
  fun has_fun_pointers b = the_default false (
    src_name (Binding.name_of b) 
    |> Option.map (ProgramAnalysis.has_fun_ptr_calls (ProgramInfo.get_csenv prog_info)))

  fun qualify b = 
    if do_guard_simps then 
      Binding.qualify true "raw" b 
    else 
      Binding.qualify (has_fun_pointers b) "ts" b

  val has_fun_pointers = ProgramAnalysis.program_has_fun_ptr_calls (ProgramInfo.get_csenv prog_info)
  val final_attr = 
    if has_fun_pointers orelse do_guard_simps then [] 
    else 
      [K (Named_Theorems.add @{named_theorems final_defs})]
  val lthy = lthy |> AutoCorresData.in_theory' (
        Utils.define_functions input_defs qualify false is_recursive (#ccpo_name rule_set) 
          (final_attr @ [AutoCorresData.define_function_attribute {concealed_named_theorems = do_guard_simps} filename skips phase]) 
          []
          []
        #> snd)
  val (fs, ts_defs) =
    let
       val finfos = fn_names |> map_filter (AutoCorresData.get_function_info (Context.Proof lthy) filename phase) 
         |> map (fn info => (FunctionInfo.get_const info, FunctionInfo.get_definition info))
    in
      split_list finfos
    end
  (* TODO: we may want to cleanup callees and rec_callees here, like we do
   *       in other phases. It's not crucial, however, since this is the
   *       final phase. *)
 
  (* Generate a theorem converting "L2_call <func>" into its new form,
   * such as L2_call <func> = liftE $ <new_func_def> *)


  val ([state], lthy') = Utils.fix_variant_frees [("s", get_l2_state_typ l2_infos (hd fn_names))] lthy

  val final_props' = (map (fn (fn_name, fn_trm) =>
    let
      val finfo = the (Symtab.lookup l2_infos fn_name)
      val args = FunctionInfo.get_plain_args finfo |> (fn xs => Utils.fix_variant_frees xs lthy') |> fst 
      val prop =  get_ts_corres_prop false lthy' skips prog_info prev_phase l2_infos fn_name
       rule_set state args (betapplys (fn_trm, args)) |> snd |> fst
    in
      fold Logic.all (rev (args)) prop
    end) (fn_names ~~ fs))


  (* Convert meta-logic into HOL statements, conjunct them together and setup
   * our goal statement. *)
  val ((paramss, props), lthy') = lthy' |> fold_map Utils.import_universal_prop final_props' |> apfst split_list
  
  val simps =
    @{thms gets_bind_ign L2_call_fail HOL.simp_thms}

  val exp_thms = map (fn (thm, export_fun_names) => Morphism.thm export_fun_names thm) (thms ~~ morphs)

  fun get_induct_thms () = 
      let
        val c = hd ts_defs |> Thm.concl_of |> Utils.lhs_of_eq |> Term.head_of 
      in
        Mutual_CCPO_Rec.lookup_info_trimmed (Context.Proof lthy) c |> the_list |> maps #inducts
      end
  val induct_thms = get_induct_thms ()

  val admissibility_thms = Named_Theorems.get lthy @{named_theorems corres_admissible}
  val top_thms = Named_Theorems.get lthy @{named_theorems corres_top}

  val N = length props
  val arbitrary_varss = replicate N [state]
  val all_varss = map (fn (xs, ys) => xs @ ys) (paramss ~~ arbitrary_varss)
  fun admissibility_tac ctxt i = Seq.INTERVAL (AutoCorresUtil.corres_admissible_tac ctxt) i (i + N - 1)
  val bump_unify_bound = Config.map Unify.search_bound (fn n => n * N)
  val rewrite_thms =
    if is_recursive then 
       Goal.prove_common lthy' NONE [] [] props (fn {context,...} =>
         DETERM (Induct.induct_tac  (bump_unify_bound context) false 
           [] (* instantiations *)
           (map (map dest_Free) all_varss) (* arbitrary *) [] (SOME induct_thms) [] 1) THEN
         admissibility_tac  (bump_unify_bound context) 1 THEN (* FIXME: instantiate admissible_subst_fun_lub_fun_ord instead of bumping unification bound *) 
         REPEAT_DETERM_N N (match_tac context top_thms 1) THEN
          (* solve induction-cases *)
          (*ALLGOALS *) REPEAT (subgoal_intro_tac' exp_thms context 1)
         )
    else
      Goal.prove_common lthy' NONE [] [] props (fn {context,...} =>
        EVERY [
         EqSubst.eqsubst_tac lthy' [0] [hd ts_defs] 1, 
         resolve_tac lthy' exp_thms 1,
         (REPEAT (
            FIRST [
               CHANGED (asm_simp_tac (put_simpset HOL_ss (Context_Position.set_visible false lthy') addsimps simps) 1),
               Method.assm_tac lthy' 1]))
         ]
       )
    
  (* Now, using this combined theorem, generate a theorem for each individual
   * function. *)

  (* 
   * Embed the theorems in the corresponding call rule, allowing the function to be called in
   * a nested exception block. 
   *)
  val new_thms = rewrite_thms
                 |> Proof_Context.export lthy' lthy 
  
  val (ctxt_new_thms, lthy) = lthy
    |> fold_map (fn (name, thm) =>
         let
           val thm_name = AutoCorresData.corres_thm_name prog_info FunctionInfo.TS name   
         in thm |> Utils.define_lemma (Binding.name thm_name) (
              AutoCorresData.corres_thm_attribute filename skips phase name::
              Monad_Types.add_call_rule_attribs (Context.Proof lthy) rule_set {only_schematic_goal = false}
                (Binding.make (thm_name, \<^here>)) 10) 
         end)
      (fn_names ~~ new_thms) 
in
  (ts_monad_name, lthy)
end


(* Return the lifting rule(s) to try for a function set.
   This is moved out of lift_function so that it can be used to
   provide argument checking in the AutoCorres.abstract wrapper. *)
fun compute_lift_rules rules force_lift fn_names =
let
    fun all_list f xs = fold (fn x => (fn b => b andalso f x)) xs true

    val forced = fn_names
                 |> map (fn func => case Symtab.lookup force_lift func of
                                        SOME rule => [(func, rule)]
                                      | NONE => [])
                 |> List.concat
in
    case forced of
        [] => rules (* No restrictions *)
      | ((func, rule) :: rest) =>
        (* Functions in the same set must all use the same lifting rule. *)
        if map snd rest |> all_list (fn rule' => #name rule = #name rule')
        then [rule] (* Try the specified rule *)
        else error ("autocorres: this set of mutually recursive functions " ^
                    "cannot be lifted to different monads: " ^
                    commas_quote (map fst forced))
end


(* Lift the given function set, trying each rule until one succeeds. *)
fun lift_function rules force_lift filename skips prog_info prev_phase l2_infos ts_infos
                  fn_names make_function_name do_polish keep_going lthy =
let
  val rules' = compute_lift_rules rules force_lift fn_names
  (* Find the first lift that works. *)
  fun first prevs (rule::xs) =
      (lift_function_rewrite rule filename skips prog_info prev_phase l2_infos ts_infos
                             fn_names make_function_name do_polish keep_going lthy
       handle LiftingFailed _ => 
         (Utils.verbose_msg 4 lthy (fn _ => "LiftingFailed: " ^ #name rule); 
         first (rule::prevs) xs))
    | first _ [] = raise AllLiftingFailed (map (fn f =>
                         (f, FunctionInfo.get_definition (the (Symtab.lookup l2_infos f)))) fn_names)
in
  first [] rules'
end

(* Show how many functions were lifted to each monad. *)
fun print_statistics results =
let
  fun count_dups x [] = [x]
    | count_dups (head, count) (next::rest) =
        if head = next then
          count_dups (head, count + 1) rest
        else
          (head, count) :: (count_dups (next, 1) rest)
  val tabulated = count_dups ("__fake__", 0) (sort_strings results) |> tl
  val data = map (fn (a,b) =>
      ("  " ^ a ^ ": " ^ (@{make_string} b) ^ "\n")
      ) tabulated
    |> String.concat
in
  writeln ("Type Strengthening Statistics: \n" ^ data)
end

fun drop_while P [] = []
  | drop_while P (x::xs) = if P x then drop_while P xs else (x::xs)

fun get_unchanged_typing_prop prog_info ts_infos monad_name
    ctxt fn_name fn_args  =
let
  
  val heap_abs = ProgramInfo.get_heap_abs (ProgramInfo.get_fun_options prog_info fn_name)

  val unchanged_typing_on = 
    (if heap_abs then
      Syntax.read_term ctxt 
        (fold_rev Long_Name.qualify [] (* FIXME: can we be more precise here?*)
          (Long_Name.base_name @{const_name heap_typing_state.unchanged_typing_on}))
    else
      Syntax.read_term ctxt 
        (fold_rev Long_Name.qualify [NameGeneration.global_rcd_name, "typing"]
          (Long_Name.base_name @{const_name heap_typing_state.unchanged_typing_on})))
    |> Term_Subst.instantiate_frees (TFrees.make [(("'a", @{sort type}), @{typ unit})], Frees.empty)

  val attrs = map (Attrib.attribute ctxt) @{attributes [runs_to_vcg]}
  
  (* Get TS const *)
  val ts_fun = (the (Symtab.lookup ts_infos fn_name) |> FunctionInfo.get_const)

  val ts_term = betapplys (ts_fun, fn_args)


in
  (([],
    \<^infer_instantiate>\<open>C = ts_term and unchanged = \<open>unchanged_typing_on\<close> 
        in prop \<open>\<And>s. Spec_Monad.runs_to_partial C s (\<lambda>r t. unchanged (UNIV::addr set) s t)\<close>\<close> ctxt), 
   attrs)
end



(* Run through every function, attempting to strengthen its type.
 * fixme: this stage is currently completely sequential. Conversions
 *        that do not depend on each other should be in parallel;
 *        this requires splitting the convert and define stages as usual. *)
fun translate
      (skips: FunctionInfo.skip_info)
      (base_locale_opt: string option)
      (rules : Monad_Types.monad_type list)
      (force_lift : Monad_Types.monad_type Symtab.table)
      (prog_info : ProgramInfo.prog_info)
      (keep_going : bool)
      (do_polish : bool)
      (groups: string list list)
      (lthy: local_theory)
      :  string list list * local_theory =
let
  val phase = FunctionInfo.TS
  val prev_phase = FunctionInfo.prev_phase skips phase
  val filename = ProgramInfo.get_prog_name prog_info
  val make_function_name = ProgramInfo.get_mk_fun_name prog_info phase 
  val existing_ts_infos = AutoCorresData.get_default_phase_info (Context.Proof lthy) filename phase
  val infos_prev_phase = AutoCorresData.get_default_phase_info (Context.Proof lthy) filename prev_phase
  (* For now, just works sequentially like the old TypeStrengthen. *)
  fun translate_group fn_names lthy =
    if forall (Symtab.defined existing_ts_infos) fn_names then
       lthy
    else
      let
        val _ = writeln ("Translating (type strengthen) " ^ commas fn_names);

        val (monad_name, lthy) = lthy |> AutoCorresUtil.timeit_ts_msg 1 lthy fn_names (fn () => 
              AutoCorresUtil.in_corres_locale_result prog_info skips phase filename fn_names (fn lthy => lthy |>
                let 
                  val l2_infos = AutoCorresData.get_default_phase_info (Context.Proof lthy) filename prev_phase
                  val ts_infos = AutoCorresData.get_default_phase_info (Context.Proof lthy) filename phase
                in lift_function rules force_lift filename skips prog_info prev_phase l2_infos ts_infos
                    fn_names (make_function_name "") do_polish keep_going
                end))

        val _ = writeln ("  --> " ^ monad_name);
      
        val heap_abs = ProgramInfo.get_heap_abs (ProgramInfo.get_fun_options prog_info (hd fn_names))
        val stateT = 
          if heap_abs then 
            the (ProgramInfo.get_lifted_globals_type prog_info)
          else  ProgramInfo.get_globals_type prog_info

        val all_rules = Monad_Types.get_ordered_rules [] (Context.Proof lthy)
        val monad_infos = all_rules |> drop_while (fn r => #name r <> monad_name) 
         |> map (fn {name, lift_from_previous_monad,...} => 
                   (name, if name = monad_name then I else lift_from_previous_monad lthy stateT))
        val monad_infos = (I, []) 
            |> fold (fn (n, current_lift) => fn (lift, xs) => 
                 let val new_lift = current_lift o lift in (new_lift, (n, new_lift)::xs) end)
                 monad_infos
            |> snd |> rev
            |> filter (fn (n, _) => member (op =) (map #name rules) n)
   
        val lthy = lthy |> member (op =) ["nondet", "exit"] monad_name ? (fn lthy =>
          let                                                                                   
            val ts_infos = AutoCorresData.get_default_phase_info (Context.Proof lthy) filename phase
            fun finfo f = (the (Symtab.lookup ts_infos f))
            val is_recursive = FunctionInfo.is_function_recursive (finfo (hd fn_names))
            fun get_induct_thms () = 
              let
                val c = (finfo (hd fn_names)) |>  FunctionInfo.get_const |> Term.head_of 
              in
                Mutual_CCPO_Rec.lookup_info_trimmed (Context.Proof lthy) c |> the_list |> maps #inducts
              end
            val induct_thms = get_induct_thms ()

            fun prop f ctxt =  
              let                     
                val info = finfo f
                val args = FunctionInfo.get_plain_args info
                val def = FunctionInfo.get_definition info
                val (params, ctxt) = Utils.fix_variant_frees args ctxt; 
                (* FIMXE: remove prems, should be empty all the time *)                                                 
                val ((prems, prop), attrs) = get_unchanged_typing_prop prog_info ts_infos monad_name lthy f params
                val ((arbitrary_vars, prop), ctxt) = Utils.import_universal_prop prop ctxt
                val (prems, ctxt) = Assumption.add_assumes (map (Thm.cterm_of ctxt) prems) ctxt
                val (_, ctxt) = fold_map (Thm.proof_attributes attrs) prems ctxt
              in
                ((def, params, arbitrary_vars, (prop, attrs)), ctxt)
              end      

            val heap_syntax_defs = Named_Theorems.get lthy @{named_theorems heap_update_syntax} 
              |> map (Utils.abs_def lthy)
            val (props, ctxt) = lthy |> fold_map prop fn_names
            val thms = Utils.timeit_label 1 lthy ("Trying unchanged typing proof for " ^ commas fn_names) (fn _ => 
                 AutoCorresUtil.prove_functions is_recursive induct_thms 
                   (fn ctxt => Unchanged_Typing.unchanged_typing_tac NONE (ctxt addsimps heap_syntax_defs))
                   (fn attrss => fn ctxt => ALLGOALS (AutoCorresUtil.prove_induction_case 
                        (K (Unchanged_Typing.unchanged_typing_tac NONE)) attrss (ctxt addsimps heap_syntax_defs)))
                   ctxt props 
                   handle ERROR msg => 
                    (warning ("Could not prove 'unchanged_typing' for " ^ commas fn_names ^ "\n " ^ msg); []))
           
           val thms = thms |> (Proof_Context.export ctxt lthy)
           val lthy = lthy |> not (null thms)?
             (Local_Theory.note ((Binding.make (suffix "_unchanged_typing" (space_implode "_" fn_names), \<^here>), 
               @{attributes [unchanged_typing]}), thms) #> snd)

           fun simplify_def f lthy =
             let
               val has_fun_pointers = ProgramAnalysis.has_fun_ptr_calls (ProgramInfo.get_csenv prog_info) f
               val final_attr = if has_fun_pointers then [] else [Named_Theorems.add @{named_theorems final_defs}]
               val info = finfo f
               val def = FunctionInfo.get_definition info
               val _ = Utils.verbose_msg 3 ctxt (fn _ => "before guard simplification:\n " ^ Thm.string_of_thm lthy def)
               val size_simps = Named_Theorems.get lthy @{named_theorems size_simps}
               val ctxt = lthy delsimps 
                      @{thms map_of_default.simps replicate_0 replicate_Suc replicate_numeral} @ (* Unify with setup in l2_opt.ML ? *)
                      size_simps
               val def' = timeit_msg 1 lthy (fn _ => "Simplifying guards within " ^ f) (fn _ => 
                 Monad_Cong_Simp.monad_simplify_import ctxt def)
               val _ = Utils.verbose_msg 3 ctxt (fn _ => "after guard simplification:\n " ^ Thm.string_of_thm lthy def')
               val base_name = make_function_name "" f
               val b = 
                 if is_recursive then 
                    Binding.name "simps" |> Binding.qualify true base_name
                 else
                    Binding.name (base_name ^ "_def")

             in
               lthy 
               |> Utils.define_lemma (Binding.qualify has_fun_pointers "ts" (Binding.new_pos \<^here> b))
                   (final_attr @ [AutoCorresData.define_function_attribute {concealed_named_theorems=false} filename skips phase f]) 
                   def'
               |> snd
             end
            val lthy = lthy |> fold simplify_def fn_names
          in
            lthy
          end)
      in lthy end;

  
  val lthy = lthy 
    |> fold translate_group groups

in
 (groups, lthy) 
end



end
