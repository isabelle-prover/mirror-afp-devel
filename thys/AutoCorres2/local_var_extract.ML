(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Extract local variables out of converted L1 fragments.
 *
 * The main interface to this module is translate (and helper functions
 * convert and define). See AutoCorresUtil for a conceptual overview.
 *)
structure LocalVarExtract =
struct

open Prog

val timeit_msg = Utils.timeit_msg
val timeap_msg_tac = Utils.timeap_msg_tac
val timing_msg' = Utils.timing_msg'
val verbose_msg = Utils.verbose_msg

val preservation_cache_mode = Attrib.setup_config_int @{binding "preservation_cache_mode"} (K 0)

structure Symstab = Table(type key = string list val ord = list_ord fast_string_ord)

(* Convenience abbreviations for set manipulation. *)
infix 1 INTER MINUS UNION
val empty_set = Varset.empty
val make_set = Varset.make
val union_sets = Varset.union_sets
fun (a INTER b) = Varset.inter a b
fun (a MINUS b) = Varset.subtract b a
fun (a UNION b) = Varset.union a b

local
  fun compare ((x,xT), (y,yT)) = Term_Ord.var_ord ( ((x, 0), xT), ((y, 0), yT))
  fun extern_compare prog_info ((x, xT), (y, yT)) =
    compare ((ProgramInfo.demangle_name prog_info x, xT), (ProgramInfo.demangle_name prog_info y, yT))
in
fun sort_extern prog_info = sort (extern_compare prog_info) (* sic: keep duplicates, as extern name is first short name match *)
fun dest_sort_extern prog_info s = Varset.dest s |> sort_extern prog_info (* legacy wrapper: sort positional names according to extern name *)
fun dest_extern prog_info s =  Varset.dest s |> map (apfst (ProgramInfo.demangle_name prog_info)) |> Ord_List.make compare
end

(* Convenience shortcuts. *)
val warning = Utils.ac_warning
val apply_tac = Utils.apply_tac
val the' = Utils.the'

val exit_status_name = "__exit_status"
val exit_status_pretty_name = "exit_status"

val exn_name = NameGeneration.global_exn_var_name
val exn_name_type = (exn_name, HP_TermsTypes.c_exntype_ty)

val exn_free = Free exn_name_type;
val exn_var = make_set [exn_name_type];


(* Simpset we use for automated tactics. *)
fun setup_l2_ss base_ss ctxt =
  let
    val state_simps = Named_Theorems.get ctxt @{named_theorems "state_simp"}
    val state_simprocs = @{code_simprocs "state_simp"}
  in
    (put_simpset base_ss (Context_Position.set_visible false ctxt))
      addsimps (@{thms
        globals_surj ucast_id pred_conj_def
        Hoare.Collect_False
        Set.mem_Collect_eq Set.Int_iff Set.empty_iff
        simp_thms HOL.implies_True_equals prod.sel
        Pure.triv_forall_equality comp_def K_eq_cong} @ state_simps)
      addsimprocs ([Record.simproc,
        @{simproc arg_cong}, @{simproc fun_cong} (* To trigger state_simprocs on nested arguments, e.g. heap updates*)] @
        state_simprocs)
  end

(* Convert a set of variable names into an Isabelle list of strings. *)
fun var_set_to_isa_list ctxt prog_info s =
  let
    fun demangle_name s =
      if s = exit_status_name then exit_status_pretty_name
      else ProgramInfo.demangle_name prog_info s
  in
    dest_sort_extern prog_info s
    |> map fst
    |> map demangle_name
    |> CLocals.name_hints ctxt
  end

(*
 * Remove references to local variables in "term", replacing them with free
 * variables.
 *
 * We return a list of variables that were successfully extracted, along with
 * the modified term itself.
 *
 * For instance:
 *
 *   convert_local_vars @{term "s \<cdot> a + b + c"}
 *       [("x", @{term "s \<cdot> a"}), ("y", @{term "s \<cdot> b"})]
 *
 * would return ("x", @{term "x + b + c"}).
 * Note that we abreviate lookup of local variables x in state s as s \<cdot> x.
 * Note that we take the freedom to ommit some name-mangling for x like x_' in the comments,
 *
 *)
fun convert_local_vars name_map term [] = ([], term)
  | convert_local_vars name_map term ((var_name, var_term) :: vars)  =
      if Utils.contains_subterm var_term term then
        let
          val free_var = name_map (var_name, fastype_of var_term)

          (* Pull out "term" from "var_term". *)
          val abstracted = betapply (Utils.abs_over var_name var_term term, free_var)

          (* Pull out the other variables. *)
          val (other_vars, other_term) = convert_local_vars name_map abstracted vars
        in
          (other_vars @ [(var_name, fastype_of var_term)], other_term)
        end
      else
        convert_local_vars name_map term vars

fun get_args_info l1_infos fn_name =
  let
    val fn_info = the (Symtab.lookup l1_infos fn_name);
  in
    FunctionInfo.get_args fn_info
  end

fun get_variables l1_infos fn_name =
let
  val fn_info = the (Symtab.lookup l1_infos fn_name);
  fun prj (n, (T, _)) = (n, T)

  val inputs = FunctionInfo.get_plain_args fn_info |> Varset.make;
  val locals = FunctionInfo.get_locals fn_info |> map prj |> Varset.make;
  val outputs = FunctionInfo.get_returns fn_info |> map prj |> Varset.make;
in
  (inputs, locals, outputs)
end

(* Get the set of variables a function accepts and returns. *)
fun get_fn_input_output_vars fn_ptr_infos l1_infos fn_name =
  case AList.lookup (op =) fn_ptr_infos fn_name of
    SOME (info) => let val l2_info = info FunctionInfo.L2
                   in (Varset.make (#args l2_info), Varset.make (#ret l2_info)) end
  | NONE => get_variables l1_infos fn_name |> (fn (inputs, _, outputs) => (inputs, outputs))


(* Get the return variable of a particular function. *)
fun get_ret_var' outputs = hd (outputs @ [("void", @{typ unit})])

fun get_ret_var fn_ptr_infos l1_infos fn_name =
let
  val (_, outputs) = get_fn_input_output_vars fn_ptr_infos l1_infos fn_name
in
  get_ret_var' (Varset.dest outputs)
end

(* Get the abstract/concrete term from a "L2corres" predicate. *)
fun dest_L2corres_term_abs @{term_pat "L2corres _ _ _ _ ?t _"} = t
fun dest_L2corres_term_conc @{term_pat "L2corres _ _ _ _ _ ?t"} = t



(*
 * Parse expressions of the form:
 *
 *     pat(?f s t)
 *
 * where "s" and "t" are input/output states. We want to parse the expression,
 * and convert it to an L2 expression dealing only with globals in "s" and "t".
 *
 * If the original SIMPL spec attempts to read or write to local variables, we
 * just fail.
 *)
fun extract_pair_of_globals pat ctxt prog_info term =
  let
    (*
     * If simplification was turned off in L1, the spec may still contain
     * unions and intersections, i.e. be of the form
     *   {(s, t). f s t} \<union> {(s, t). g s t} ...
     * We blithely rewrite them here.
     *)
    val term = Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt)
        (map safe_mk_meta_eq @{thms Collect_prod_inter Collect_prod_union}) [] term

    (* Apply a dummy old and new state variable to the term. *)
    val dummy_s = Free ("_dummy_state1", ProgramInfo.get_state_type prog_info)
    val dummy_t = Free ("_dummy_state2", ProgramInfo.get_state_type prog_info)
    (* Parse term according to \<open>pat\<close> *)
    val ([((vstateT, _), _)], [((vf, _), f)]) = Utils.match_insts ctxt pat term
    val t = Envir.beta_eta_contract (Thm.term_of f $ dummy_s $ dummy_t)

    (* Pull apart the "split" at the beginning of the term, then apply
     * to our dummy variables *)
    val t = Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt)
        (map mk_meta_eq @{thms split_def fst_conv snd_conv mem_Collect_eq}) [] t

    (*
     * Pull out any references to any other variables into a lambda
     * function.
     *
     * We pull out the globals variable first, because we want it to end
     * up inner-most compared to all the other lambdas we generate.
     *)
    val globals_getter = ProgramInfo.get_globals_getter prog_info
    val t = Utils.abs_over "t" (globals_getter $ dummy_t) t
            |> Utils.abs_over "s" (globals_getter $ dummy_s)

  in
    (* Determine if there are any references left to the dummy state
     * variable. If so, give up on the translation. *)
    if Utils.contains_subterm dummy_s t
    orelse Utils.contains_subterm dummy_t t then
      (warning ("Can't parse pair of globals term: "
          ^ (Utils.term_to_string ctxt term)); NONE)
    else
      (* recombine with pat *)
      SOME (subst_vars ([(vstateT, fastype_of (globals_getter $ dummy_t))], [(vf, t)]) pat)
  end

local
  val stateT = TVar (("'state", 0), [])

  (* "Spec" expressions are of the form: {(s, t). f s t} *)
  val pat_spec =
    \<^Const>\<open>Collect \<open>HOLogic.mk_prodT (stateT, stateT)\<close>\<close> $
    (HOLogic.mk_case_prod (Abs ("s", stateT, Abs ("t", stateT,
      Var (("f", 0), stateT --> stateT --> HOLogic.boolT) $ Bound 1 $ Bound 0))))

  (* "Assume" expressions are of the form: (\<lambda>s. {(_, t). f s t}) *)
  val pat_assume = Abs ("s", stateT, \<^Const>\<open>Collect \<open>HOLogic.mk_prodT (HOLogic.unitT, stateT)\<close>\<close> $
      (HOLogic.mk_case_prod (Abs ("u", HOLogic.unitT, Abs ("t", stateT,
        Var (("f", 0), stateT --> stateT --> HOLogic.boolT) $ Bound 2 $ Bound 0)))))
in

fun parse_spec ctxt prog_info term = extract_pair_of_globals pat_spec ctxt prog_info term

fun parse_assume ctxt prog_info term = extract_pair_of_globals pat_assume ctxt prog_info term

end

(*
 * Parse an L1 expression containing references to the global state.
 *
 * We assume that the input term is in the "abstracted" form "%s. f s" where
 * "s" is the global state variable.
 *
 * Our return value is a list of variables abstracted, whether the global
 * variable was used, and the abstracted term itself.
 *
 * The function will fail (and return NONE) if the input expression performs
 * arbitrary transformations on the state. For example:
 *
 *    "%s. s \<cdot> a"          => ([a], False, SOME @{term "%a s. a"})
 *    "%s. globals s"      => ([], True, SOME @{term "%s. s"})
 *    "%s. s \<cdot> a + s \<cdot> b"   => ([a, b], False, SOME @{term "%a b s. a + b"})
 *    "%s. False"          => ([], False, SOME @{term "%s. False"})
 *    "%s. bot s"          => ([], False, NONE)
 *)
fun parse_expr ctxt prog_info name_map term =
  let
    val dummy_state = Free ("_dummy_state", ProgramInfo.get_state_type prog_info)

    (* Apply a dummy state variable to the term. This makes our later analysis
    * easier. *)
    val term = Envir.beta_eta_contract (term $ dummy_state)
    (*
     * Pull out any references to any other variables into a lambda
     * function.
     *
     * We pull out the globals variable first, because we want it to end
     * up inner-most compared to all the other lambdas we generate.
     *)
    val globals_getter = ProgramInfo.get_globals_getter prog_info $ dummy_state
    val globals_used = Utils.contains_subterm globals_getter term
    val t = Utils.abs_over "s" globals_getter term

    (* Pull out local variables. *)
    val all_getters = ProgramInfo.all_var_getters ctxt prog_info dummy_state |> map (apsnd fst)
    val ps = HPInter.collect_positional (HPInter.mk_locals ctxt dummy_state) t
    val (v1, t) = convert_local_vars name_map t (all_getters @ ps)
    (*
     * Determine if there are any references left to the dummy state
     * variable.
     *
     * If so, we are stuck: we aren't pulling out a part of the state
     * record, but instead performing an arbitrary transformation on it.
     * The most likely reason for this is the C parser's dummy function
     * "lvar_init", which attempts to set an uninitialised local
     * variable to an invalid state. Other possibilities include "bot",
     * the always-false guard.
     *)
    val t = if Utils.contains_subterm dummy_state t then
      (warning ("Can't parse expression: "
          ^ (Utils.term_to_string ctxt term)); NONE)
      else
        SOME t;
  in
    (v1, globals_used, t)
  end

(*
 * Parse an "L1_modify" expression.
 *)
fun gen_parse_modify (params as {write_scope, read_scope, two_state}) ctxt prog_info name_map term =
  let
    val dummy_state_write = Free ("_dummy_state", ProgramInfo.get_state_type prog_info)
    val dummy_state_read = if two_state then Free ("_dummy_state_old", ProgramInfo.get_state_type prog_info) else dummy_state_write
    val trm = if two_state then (term $ dummy_state_read) else term
    fun parse_modify' term =
      let
        (*
         * We expect modify clauses in two forms: both "%x. (foo x) x" and just
         * "foo". We apply a state variable to the function and beta/eta contract
         * to normalise our output for the next steps.
         *)
        val trm = if two_state then (term $ dummy_state_read) else term
        val modify_clause = Envir.beta_eta_contract (trm $ dummy_state_write)
        (*
         * Extract "xxx" from "foo_'_update xxx".
         *
         * If the user has written custom "modifies" clauses (presumably
         * using "AUXUPD" directives), this may fail.
         *)

        val ((var_name, var_type), modify_val, s) = case ProgramInfo.dest_var_update modify_clause of
           SOME v => v
          | _ => Utils.invalid_term' ctxt "variable update" modify_clause;

        (*
         * At this stage we have assume we have an update function "f" of
         * type "'a => 'a" which expects the old value of the variable
         * being updated, and returns a new value.
         *
         * We now want to convert this into a value of type "'a", returning
         * the new value. We do this by applying "(field_' s)" to the
         * function f, followed by normalisation.
         *)
        val get_value = ProgramInfo.get_var_value (write_scope ctxt) prog_info var_name dummy_state_read
        val modify_val = betapply (modify_val, get_value)
            |> Envir.beta_eta_contract

        (*
         * We are now in the form of "foo dummy_state". Pull out
         * our dummy state variable, and parse the expression.
         *)
        fun remove_dummy_state st t = Utils.abs_over "s" st t
        val (vars, globals_used, modify_val) = parse_expr (read_scope ctxt) prog_info name_map (remove_dummy_state dummy_state_read modify_val)
      in
        ((var_name, var_type), vars, globals_used, modify_val,
          remove_dummy_state dummy_state_write s |> two_state ? remove_dummy_state dummy_state_read)
      end
  in
    if Envir.beta_eta_contract (trm $ dummy_state_write) = dummy_state_write then []
    else
      let
        val (updated_var, read_vars, reads_globals, term, residual) = parse_modify' term
      in
        (updated_var, read_vars, reads_globals, term) :: gen_parse_modify params ctxt prog_info name_map residual
      end
  end

val parse_modify = gen_parse_modify {write_scope = I, read_scope = I, two_state = false};

val parse_modify_two_state = gen_parse_modify {write_scope = I, read_scope = I, two_state = true};

fun int_of_string s =
 case (s |> Symbol.explode |> read_int) of
   (i, []) => SOME i
 | _ => NONE

(* FIXME: avoid this name mangling? Use loc_refs in the first place? *)
fun mk_loc_ref T n =
 case NameGeneration.dest_positional_name n of
   SOME (NameGeneration.In i, _) => NameGeneration.Positional (i, T)
 | _ => (case int_of_string n of
           SOME i => NameGeneration.Positional (i, T) (* positional return parameter *)
        | _ => NameGeneration.Named n)

(* Fetch a variable getter, from variable's name. *)

fun var_getter ctxt (prog_info : ProgramInfo.prog_info) state proj_status (var, T) =
    let
      fun getter x = Symtab.lookup (ProgramInfo.get_var_getters prog_info) x |> the
      fun proj x = if proj_status then @{const the_Nonlocal(exit_status)} $ x else x
      fun get state =
        if var = NameGeneration.global_exn_var_name andalso T = @{typ exit_status}
        then proj (getter NameGeneration.global_exn_var_name $ state)
        else ProgramInfo.get_var_value ctxt prog_info (mk_loc_ref T var) state
    in get state
    end handle Option => (Utils.invalid_input "valid local variable name" var)

fun dest_positional ctxt vars =
 Varset.dest vars |> sort (CLocals.positional_ord ctxt o (apply2 fst))

(*
 * Construct precondition from variable set.
 *
 * These preconditions are of the form:
 *
 *    "(%s. s \<cdot> n_' = n) and (%s. s \<cdot> n_' = i) and ..."
 *)

fun mk_precond ctxt prog_info name_map vars =
let
  val myvarsT = ProgramInfo.get_state_type prog_info
  val dummy_state = Free ("_dummy_state", myvarsT)
in
  Utils.chain_preds myvarsT
    (map (fn (var_name, var_type) =>
          let
            val var = var_getter ctxt prog_info dummy_state false (var_name, var_type)
          in
            Utils.abs_over "s" dummy_state
                (HOLogic.mk_eq (var, name_map (var_name, var_type)))
          end)
          (dest_positional ctxt vars)) (* sic: keep canonical (positional) order of parameters *)
end


(*
 * Construct extraction functions, of the form:
 *
 *      "%s. (s \<cdot> a, s \<cdot> b, s \<cdot> c)"
 *)
fun mk_xf ctxt (prog_info : ProgramInfo.prog_info) vars =
let
  val dummy_state = Free ("_dummy_state", ProgramInfo.get_state_type prog_info)
in
  Utils.abs_over "s" dummy_state
    (HOLogic.mk_tuple (dest_sort_extern prog_info vars |> map (var_getter ctxt prog_info dummy_state true)))
end

(*
 * Construct a correspondence lemma between a given L2 and L1 terms.
 *)
fun mk_corresXF_prop ctxt prog_info name_map return_vars except_vars precond_vars l2_term l1_term =
  let
    (* Construct precondition and extraction functions. *)
    val precond = mk_precond ctxt prog_info name_map precond_vars
    val return_xf = mk_xf ctxt prog_info return_vars
    val except_xf = mk_xf ctxt prog_info except_vars
    val corres = \<^infer_instantiate>\<open>st = \<open>ProgramInfo.get_globals_getter prog_info\<close> and ret_xf = return_xf and
            ex_xf = except_xf and P = precond and A = l2_term and C = l1_term
          in prop \<open>L2corres st ret_xf ex_xf P A C\<close>\<close> ctxt
  in
    corres
  end


(*
 * Prove correspondence between L1 and L2.
 *
 *    ctxt: Local theory context
 *
 *    return_vars: Variables that are returned by the abstract spec's monad.
 *
 *    except_vars: Variables that are thrown by the abstract spec's monad.
 *
 *    precond_vars: Variables that must match between abstract and concrete.
 *
 *    l2_term / l1_term: Abstract and concrete specs.
 *)
fun mk_corresXF_thm ctxt prog_info  name_map return_vars except_vars precond_vars l2_term l1_term tac =
let
  val ctxt = ctxt addsimps @{thms split_def}
  val prop = timeit_msg 2 ctxt (fn _ => "mk_corresXF_prop: ") (fn _ => mk_corresXF_prop ctxt prog_info name_map
       return_vars except_vars precond_vars l2_term l1_term)
in
  prop
  |> (fn goal => (*Goal.prove ctxt [] [] goal tac*) Utils.simple_prove ctxt goal tac)
end



fun solve_simp_sideconditions ctxt thm =
  let
    val nprems = Thm.prems_of thm |> length
    val st = thm |> Goal.protect nprems
  in
    Utils.simple_cprove ctxt st
      (timeap_msg_tac 2 ctxt (fn _ => "solve_simp_sideconditions")
      (REPEAT (CHANGED (asm_full_simp_tac ctxt 1))))
  end

fun mk_corresXF_thm_direct ctxt prog_info name_map return_vars except_vars precond_vars l2_term l1_term thm =
  let
    val goal = mk_corresXF_prop ctxt prog_info name_map return_vars except_vars precond_vars l2_term l1_term
    val concl = Thm.concl_of thm
    val nprems = Thm.prems_of thm |> length
    val (ty_insts, trm_insts) = Utils.match_or_unify ctxt concl goal
    val st = Thm.instantiate (TVars.make ty_insts, Vars.make trm_insts) thm |> Goal.protect nprems
    val ctxt = ctxt addsimps @{thms split_def}
  in
    Utils.simple_cprove ctxt st
      (timeap_msg_tac 2 ctxt (fn _ => "mk_corresXF_thm_direct - solve sideconditions")
      (REPEAT (CHANGED (asm_full_simp_tac ctxt 1))))
  end


fun dummy_state_guards_l1 prog_info = Free ("_dummy_state", ProgramInfo.get_state_type prog_info)
fun dummy_state_guards_l2 prog_info = Free ("_dummy_state_l2", ProgramInfo.get_globals_type prog_info)
val dummy_fun_ptr = Free ("_p", @{typ "unit ptr"})

fun l1call_function_const t = case strip_comb t |> apsnd rev of
    (Const c, (Const c' :: _)) => if String.isSuffix "_'proc" (fst c')
        then Const c' else Const c
  | (Const c, _) => Const c
  | (Abs (_, _, t), []) => l1call_function_const t
  | _ => raise TERM ("l1call_function_const", [t])

fun callee_scope prog_info t ctxt =
   (case strip_comb t of
     (Const (fname, _), _) =>
        (case try (ProgramInfo.get_dest_fun_name prog_info FunctionInfo.L1 "") (Long_Name.base_name fname) of
          SOME fname => CLocals.switch_scope fname ctxt
         | _ => ctxt)
    | _ => ctxt)


(*
 * Parse an L1 term.
 *
 * In particular, we break down the structure of the program and parse the
 * usage of local variables in all expressions and modifies clauses.
 *)
fun parse_l1 ctxt prog_info l1_infos l1_call_info name_map term =
  case term of
      (Const (@{const_name "L1_skip"}, _)) =>
        Modify (term,
            (SOME (Abs ("s", ProgramInfo.get_globals_type prog_info, @{term "()"})), empty_set, false), empty_set)

    | (Const (@{const_name "L1_modify"}, _) $ m) =>
        let
          val parsed_clause = parse_modify ctxt prog_info name_map m
          val (updated_var, read_vars, is_globals_reader, parsed_expr) =
            case parsed_clause of
                [x] => x
              | _ => Utils.invalid_term' ctxt "Modifies clause too complex." m
        in
          Modify (term, (parsed_expr, make_set read_vars, is_globals_reader),
            make_set [apfst NameGeneration.the_named updated_var])
        end

    | (Const (@{const_name "L1_seq"}, _) $ lhs $ rhs) =>
        Seq (term, parse_l1 ctxt prog_info l1_infos l1_call_info name_map lhs,
                   parse_l1 ctxt prog_info l1_infos l1_call_info name_map rhs)

    | (Const (@{const_name "L1_catch"}, _) $ lhs $ rhs) =>
        Catch (term, parse_l1 ctxt prog_info l1_infos l1_call_info name_map lhs,
                     parse_l1 ctxt prog_info l1_infos l1_call_info name_map rhs)

    | (Const (@{const_name "L1_guard"}, _) $ c) =>
        let
          val (read_vars, is_globals_reader, parsed_expr) = parse_expr ctxt prog_info name_map c
        in
          Guard (term, (parsed_expr, make_set read_vars, is_globals_reader))
        end
    | @{term_pat "L1_guarded ?g (gets ?dest >>= ?c)"} =>
        let
          val (read_vars, is_globals_reader, parsed_expr) = parse_expr ctxt prog_info name_map g
          val (read_vars_dest, is_globals_reader_dest, parsed_expr_dest) = parse_expr ctxt prog_info name_map dest
          val dummy_state = dummy_state_guards_l1 prog_info
          val p = Envir.beta_eta_contract (dest $ dummy_state)
          val c = Envir.beta_eta_contract (c $ p)
        in
          Guarded (term, (parsed_expr, make_set read_vars, is_globals_reader),
            (parsed_expr_dest, make_set read_vars_dest, is_globals_reader_dest),
            parse_l1 ctxt prog_info l1_infos l1_call_info name_map c)
        end
    | (Const (@{const_name "L1_throw"}, _)) =>
        Throw term

    | (Const (@{const_name "L1_condition"}, _) $ cond $ lhs $ rhs) =>
        let
          (* Parse the conditional. *)
          val (read_vars, is_globals_reader, parsed_expr) = parse_expr ctxt prog_info name_map cond
        in
          Condition (term, (parsed_expr, make_set read_vars, is_globals_reader),
              parse_l1 ctxt prog_info l1_infos l1_call_info name_map lhs,
              parse_l1 ctxt prog_info l1_infos l1_call_info name_map rhs)
        end

    | (Const (@{const_name "L1_call"}, L1_call_type)
            $ arg_setup $ callee_term $ return_norm $ return_exn $ ret_extract) =>
        let
          (* Parse arg setup. We treat this not as a modify, but as several
           * expressions, as the modified variables are only in the scope of
           * this L1_call command. *)
          val arg_setup_exprs =
            gen_parse_modify {write_scope = callee_scope prog_info callee_term, read_scope = I, two_state = false}
              ctxt prog_info name_map arg_setup
            |> map (fn (_, read_vars, is_globals_reader, term) =>
                (term, make_set read_vars, is_globals_reader))
          val callee_expr =
            let
              val callee' = Utils.abs_over "s" (dummy_state_guards_l1 prog_info) callee_term
              val (read_vars, is_globals_reader, term) = parse_expr ctxt prog_info name_map callee'
            in (term, make_set read_vars, is_globals_reader) end
          val parsed_clause =
                gen_parse_modify {write_scope = I, read_scope = callee_scope prog_info callee_term, two_state = false}
                   ctxt prog_info name_map (betapply (ret_extract, Free ("_dummy_state", ProgramInfo.get_state_type prog_info)))
                |> map (fn (target_var, read_vars, globals_read, expr) =>
                    let
                      val ret_var = get_ret_var' read_vars
                    in
                     (target_var, (make_set read_vars) MINUS (make_set [ret_var]),
                        globals_read, Option.map (Utils.abs_over "ret" (name_map ret_var)) expr)
                    end)
          val (ret_expr, updated_var) =
            case parsed_clause of
                [(target_var, read_vars, globals_read, expr)] =>
                    ((expr, read_vars, globals_read), make_set [apfst NameGeneration.the_named target_var])
              | [] => ((NONE, empty_set, false), empty_set)
              | x => Utils.invalid_input "single return param" (@{make_string} x)
        in
          Call (term, callee_expr, arg_setup_exprs, ret_expr, (updated_var UNION exn_var), ())
        end

    | (Const (@{const_name "L1_while"}, _) $ cond $ body) =>
        let
          (* Parse conditional. *)
          val (read_vars, is_globals_reader, parsed_expr) = parse_expr ctxt prog_info name_map cond;
        in
          While (term, (parsed_expr, make_set read_vars, is_globals_reader),
                 parse_l1 ctxt prog_info l1_infos l1_call_info name_map body)
        end

    | (Const (@{const_name "L1_init"}, _) $ setter) =>
        let
          val updated_var = ProgramInfo.guess_var_name_type_from_setter_term setter
        in
          Init (term, make_set [updated_var])
        end

    | (Const (@{const_name "L1_spec"}, _) $ c) =>
        (case parse_spec ctxt prog_info c of
            SOME x =>
              Spec (term, (SOME x, empty_set, true))
          | NONE =>
              Spec (term, (NONE, empty_set, true)))

    | (Const (@{const_name "L1_assume"}, _) $ c) =>
        (case parse_assume ctxt prog_info c of
            SOME x =>
              Assume (term, (SOME x, empty_set, true))
          | NONE =>
              Assume (term, (NONE, empty_set, true)))

    | (Const (@{const_name "L1_fail"}, _)) =>
        Fail term

    | other =>
       let
         val {init, c, ...} = with_fresh_stack_ptr.match ctxt other
         val Abs (p, pT, _) = c
         val sT = fastype_of init |> domain_type
         val (read_vars, is_globals_reader, parsed_expr) = parse_expr ctxt prog_info name_map init
         val ((p, pT), bdy) = Term.dest_abs_fresh p c
         val ([p], ctxt') = Utils.gen_fix_variant_frees true [(p, pT)] ctxt
         val bdy' = parse_l1 ctxt' prog_info l1_infos l1_call_info name_map bdy
       in
         Stack (term, (parsed_expr, make_set read_vars, is_globals_reader), bdy')
       end handle Match => Utils.invalid_term' ctxt "a L1 term" other

type export_info =
 {phi_export: Morphism.morphism,
  dummy_value: string,
  dummy_init: string,
  phi_cache: Morphism.morphism,
  weaken_superset : varset -> thm -> thm};

fun mk_pattern ctxt dummy_value dummy_init t =
  let
    val mk_pattern = mk_pattern ctxt dummy_value dummy_init
  in
    case t of
      (c as Const (@{const_name "L1_modify"}, T)) $ f =>
        c $ HPInter.subst_var_update ctxt dummy_value f
    | (c as Const (@{const_name "L1_call"}, _)) $ init $ n $ exit $ res_exn $ res_ret =>
       c $ Free (dummy_init , fastype_of init) $ n $ exit $ res_exn $ HPInter.subst_var_update ctxt dummy_value res_ret
    | (c as Const (@{const_name "L1_seq"}, _)) $ lhs $ rhs =>
      let
        val lhs' = mk_pattern lhs
        val rhs'= mk_pattern rhs
      in
        c $ lhs' $ rhs'
      end
    | (c as Const (@{const_name "L1_while"}, _)) $ cond $ body =>
      let
        val body' = mk_pattern body
      in
        c $ cond $ body'
      end
    | (c as Const (@{const_name "L1_condition"}, _)) $ cond $ lhs $ rhs =>
      let
        val lhs' = mk_pattern lhs
        val rhs' = mk_pattern rhs
      in
        c $ cond $ lhs' $ rhs'
      end
    | (c as Const (@{const_name "L1_catch"}, _)) $ lhs $ rhs =>
      let
        val lhs' = mk_pattern lhs
        val rhs' = mk_pattern rhs
      in
        c $ lhs' $ rhs'
      end
    | _ => t
   end

fun fold_default d f xs =
  case xs of
    [] => d
  | [x] => x
  | (x::xs) => fold f xs x

fun join_preserve_thms thms =
  fold_default @{thm hoareE_TrueI}
    (fn x => fn y => @{thm combine_validE} OF [x,y])
    thms

\<comment>\<open>Cache for preservation proofs, indexed by term-pattern and list of variables being preserved.
* The term pattern optimizes for the common cases of an assignment and procedure call and abstracts the value
  of the assignment, i.e.
     x = <some term>

     becomes

     x = _v

  Theorems are generalized accordingly.
  This means that for example x = 2 and  x = 3 are handled by the same preservation theorem.
  The same idea holds for the result parameter of a procedure call.

* mode < 0: disable caching
* mode = 0: basic caching
* mode >= 1: lookup detects preservation theorems for a superset of the variables and applies a weakening
  proof instead of reproving the theorem.
* mode >= 2: additional to 1, lookup also detects the case where multiple theorems form a superset, these are
  then joined and weakening is applied.
\<close>
@{record \<open>datatype pres_cache = Cache of
    {tab: thm Symstab.table Termtab.table,
     mode: int,
     hits: int,
     misses: int,
     superset: int,
     join: int}\<close>}


fun pres_cache_empty ctxt = make_pres_cache {mode = Config.get ctxt preservation_cache_mode,
  tab = Termtab.empty, hits = 0, misses = 0, superset = 0, join = 0};

local
fun key var_set = map fst (Varset.dest var_set)

fun find_superset mode tab var_set =
  if Varset.card var_set = 0 orelse mode <= 0 then NONE
  else
    let
      val set = Symset.make (map fst (Varset.dest var_set))
      val elems = Symstab.dest tab
    in
      case find_first (fn (vars, thm) => Symset.subset (set, Symset.make vars)) elems of
        SOME (_, thm) => SOME [thm]
      | NONE => if mode >= 2 then
                  let
                    val all = Symset.make (flat (map fst elems))
                  in
                    if Symset.subset (set, all)
                    then SOME (map snd elems)
                    else NONE
                  end
                else NONE

    end
in

fun update_pres_cache_pattern pat var_set thm cache =
  cache
  |> get_mode cache >= 0 ?
     map_tab (Termtab.map_default (pat, Symstab.empty) (Symstab.update (key var_set, thm)))


fun lookup_pres_cache_pattern export_info cache pat var_set =
  if get_mode cache < 0 then (NONE, pat, cache)
  else
    case Termtab.lookup (get_tab cache) pat of
      NONE => (NONE, pat, map_misses (fn i => i + 1) cache)
    | SOME vars => (case Symstab.lookup vars (key var_set) of
                      NONE => (case find_superset (get_mode cache) vars var_set of
                                NONE => (NONE, pat,  map_misses (fn i => i + 1) cache)
                               | SOME superset_thms =>
                                   let
                                     val (thm, cache) = case superset_thms of [thm] => (thm, cache)
                                       | _ => (join_preserve_thms superset_thms, map_join (fn i => i + 1) cache)
                                     val thm = (#weaken_superset export_info) var_set thm
                                     val cache = map_superset (fn i => i + 1) cache
                                   in (SOME thm, pat, update_pres_cache_pattern pat var_set thm cache) end)

                    | SOME thm => (SOME thm, pat, map_hits (fn i => i + 1) cache))

fun lookup_pres_cache ctxt export_info cache term var_set =
  let
    val pat = mk_pattern ctxt (#dummy_value export_info) (#dummy_init export_info) term
  in
    lookup_pres_cache_pattern  export_info cache pat var_set
  end
end

fun weaken_superset ctxt phi_export prog_info name_map var_set thm =
 timeit_msg 2 ctxt (fn _ => "weaken_superset: ") (fn _ =>
 let
   val precond = mk_precond ctxt prog_info name_map var_set
   fun i thm args = Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) args) thm
   val weaken = i @{thm validE_weaken_dependent_same} [precond] OF [Morphism.thm phi_export thm]

   val tac = SOLVES
     (EVERY [CHANGED (asm_full_simp_tac ctxt 1),
        REPEAT (eresolve_tac ctxt @{thms conjE} 1),
        REPEAT (TRY (resolve_tac ctxt @{thms conjI} 1) THEN assume_tac ctxt 1)])
 in
   Utils.solve_sideconditions ctxt weaken (REPEAT1 tac)
 end)


(*
 * Generate a proof showing that a particular variables "var" is not modified
 * over the given input L1 term.
 *)
fun mk_preservation_proof_atomic ctxt export_info prog_info name_map var pat (cache : pres_cache) =
  case lookup_pres_cache_pattern export_info cache pat (make_set [var]) of
    (SOME t, _, cache) => (t, cache)
  | (NONE, pat, cache) =>
  let
    (* simplify all remaining subgoals. *)
    fun s thm =
      Utils.solve_sideconditions ctxt thm (TRY (REPEAT (CHANGED (asm_full_simp_tac ctxt 1))))

    fun i thm args = Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) args) thm
    val e = Morphism.thm (#phi_cache export_info)

    (* Generate the predicate. *)
    val var_set = make_set [var]
    val precond = mk_precond ctxt prog_info name_map var_set

    (* Construct a tactic that solves the problem. *)
    val (thm, cache) =
      (case pat of
          (Const (@{const_name "L1_skip"}, _)) =>
            (i @{thm L1_skip_lp_same_pre_post} [precond], cache)
        | (Const (@{const_name "L1_init"}, _) $ f) =>
            (i @{thm L1_init_lp_same_pre_post} [precond, f], cache)
        | (Const (@{const_name "L1_modify"}, _) $ f) =>
            (e (i @{thm L1_modify_lp_same_pre_post} [precond, f]), cache)
        | (Const (@{const_name "L1_call"}, _) $ init $ n $ exit $ res_exn $ res_ret) =>
            (e (i @{thm L1_call_lp_same_pre_post} [precond, res_ret, exit, res_exn, init, n]), cache)
        | (Const (@{const_name "L1_guard"}, _) $ g) =>
            (i @{thm L1_guard_lp_same_pre_post} [precond, g], cache)
        | (Const (@{const_name "L1_throw"}, _)) =>
            (i @{thm L1_throw_lp_same_pre_post} [precond], cache)
        | (Const (@{const_name "L1_spec"}, _) $ _) =>
            (i @{thm hoareE_TrueI} [precond, pat], cache)
        | (Const (@{const_name "L1_assume"}, _) $ _) =>
            (i @{thm hoareE_TrueI} [precond, pat], cache)
        | (Const (@{const_name "L1_fail"}, _)) =>
            (i @{thm L1_fail_lp} [precond], cache)
        | other => error ("mk_preservation_proof_atomic does not handle compound statements: " ^ Syntax.string_of_term ctxt other))

    val thm = s thm

  in
    (thm, update_pres_cache_pattern pat var_set thm cache)
  end


(* Generate a preservation proof for multiple variables. *)
(* N.S. Here we have complexity N (number of variables not changed) * M (size of program)
 * Does not seem to be a performance bottleneck in praxis.
*)
fun mk_multivar_preservation_proof_atomic ctxt export_info prog_info name_map term var_set cache =
let
  val (proofs, cache) = Utils.dep_timeit_msg 0 (Utils.threshold_msg (seconds 10.0)
    (fn _ => "preservation_proof longrunning: " ^ Syntax.string_of_term ctxt term)) (fn _ =>
    cache |>
    fold_map (fn x => mk_preservation_proof_atomic ctxt export_info prog_info name_map x term)
      (rev (dest_sort_extern prog_info var_set))) (* sic: ensures same nesting as mk_precond *)
  val result = join_preserve_thms proofs
in
  (result, cache)
end
handle Option => error ("Preservation proof failed for " ^ quote (@{make_string} var_set))


fun mk_multivar_preservation_proof ctxt (export_info: export_info) prog_info name_map term var_set (cache : pres_cache) =
  if Varset.card var_set = 0 then (@{thm hoareE_TrueI}, cache) else
  case lookup_pres_cache ctxt export_info cache term var_set of
    (SOME t, _, cache) => (t, cache)
  | (NONE, pat, cache) =>
  let

    (* Construct a tactic that solves the problem. *)
    val (thm, cache) =
      (case pat of
         (Const (@{const_name "L1_while"}, _) $ _ $ body) =>
          let
            val (body', cache) = mk_multivar_preservation_proof ctxt export_info prog_info name_map body var_set cache
          in
            (@{thm L1_while_lp_same_pre_post} OF [body'], cache)
          end
        | (Const (@{const_name "L1_condition"}, _) $ _ $ lhs $ rhs) =>
          let
            val (lhs', cache) = mk_multivar_preservation_proof ctxt export_info prog_info name_map lhs var_set cache
            val (rhs', cache) = mk_multivar_preservation_proof ctxt export_info prog_info name_map rhs var_set cache
          in
            (@{thm L1_condition_lp_same_pre_post} OF [lhs', rhs'], cache)
          end
        | (Const (@{const_name "L1_seq"}, _) $ lhs $ rhs) =>
          let
            val (lhs', cache) = mk_multivar_preservation_proof ctxt export_info prog_info name_map lhs var_set cache
            val (rhs', cache) = mk_multivar_preservation_proof ctxt export_info prog_info name_map rhs var_set cache
          in
            (@{thm L1_seq_lp_same_pre_post} OF [lhs', rhs'], cache)
          end
        | (Const (@{const_name "L1_catch"}, _) $ lhs $ rhs) =>
          let
            val (lhs', cache) = mk_multivar_preservation_proof ctxt export_info prog_info name_map lhs var_set cache
            val (rhs', cache) = mk_multivar_preservation_proof ctxt export_info prog_info name_map rhs var_set cache
          in
            (@{thm L1_catch_lp_same_pre_post} OF [lhs', rhs'], cache)
          end
        | @{term_pat \<open>L1_guarded _ (gets ?dest \<bind> ?body)\<close>} =>
          let
            val (body', cache) = mk_multivar_preservation_proof ctxt export_info prog_info name_map body var_set cache
            val thm = @{thm L1_guarded_lp_gets} OF [body']
          in
            (thm, cache)
          end
        | (abs as Abs (x, xT, body)) => (* e.g. dynamic call of function, i.e L1_guarded --- (gets dest \<bind> (%p. L1_call ... (P p)... )) *)
          let
            val ([x], ctxt') = Utils.fix_variant_frees [(x,xT)] ctxt
            fun strip_x (t as (bdy $ x')) = if x=x' then bdy else t
              | strip_x t = t
            val body = betapply(abs, x) 
            val (body', cache) = mk_multivar_preservation_proof ctxt' export_info prog_info name_map body var_set cache
            val [body'] = Proof_Context.export ctxt' ctxt [body']
          in
            (body', cache) (* FIXME *)
          end
        | other =>
          let
            val {init, c, ...} = with_fresh_stack_ptr.match ctxt other
            val Abs (p, pT, _) = c
            val ((p, pT), bdy) = Term.dest_abs_fresh p c
            val ([p], ctxt') = Utils.gen_fix_variant_frees true [(p, pT)] ctxt
            val (bdy', cache) = mk_multivar_preservation_proof ctxt' export_info prog_info name_map bdy var_set cache
            val [bdy'] = Proof_Context.export ctxt' ctxt [bdy']
            val (rule::_) = Named_Theorems.get ctxt @{named_theorems with_fresh_stack_ptr_lp_same_pre_post} |> Utils.OFs [bdy']
            val thm = solve_simp_sideconditions ctxt rule
          in
            (thm, cache)
          end handle Match => mk_multivar_preservation_proof_atomic ctxt export_info prog_info name_map other var_set cache)
  in
    (thm, update_pres_cache_pattern pat var_set thm cache)
  end



fun status_ty T =
 if T = HP_TermsTypes.c_exntype_ty then @{typ exit_status} else T

fun exn_status_ty (n, T) =
  if n = NameGeneration.global_exn_var_name then status_ty T else T


(*
 * Generate a well-typed L2 monad expression.
 *
 *    "const" is the name of the monadic function (e.g., @{const_name "L2_gets"})
 *
 *    "ret"/"throw" are the variables being returned or thrown by this monadic
 *    expression. This is used only for determining the type of the output
 *    monad.
 *
 *    "params" are the expressions to be beta applied to the monad.
 *)
fun mk_l2monad ctxt (prog_info : ProgramInfo.prog_info) const ret throw params =
let
  val retT = HOLogic.mk_tupleT (dest_sort_extern prog_info ret |> map snd)
  val exT = HOLogic.mk_tupleT (dest_sort_extern prog_info  throw |> map snd)
  val monadT = AutoCorresData.mk_l2monadT (ProgramInfo.get_globals_type prog_info) retT exT
in
  betapplys ((Const (const, (map fastype_of params) ---> monadT)), params)
end

(* Abstract over a tuple using the given name map. *)
(* Note that we use extern names for bound variables to improve readability of intermediate terms,
   a final renaming is performed in the final autocorres phase, trying to restore the original
   names of the C input.
*)
fun abs_over_tuple_vars prog_info (name_map : (string * typ) -> term) (vars : varset) =
  Utils.abs_over_tuple (map (fn (a, b) => (ProgramInfo.demangle_name prog_info a, name_map (a, b))) (dest_sort_extern prog_info vars))

(*
 * Given a L2 monad that returns the variables "vars_returned", convert it into
 * an L2 monad that returns "needed_returns".
 *
 * This is frequently needed when a particular monad is only capable of returning
 * a particular variable (or set of variables), but needs to return a different set
 * of these variables. For example, both branches in an "condition" block need
 * to return the same set of variables.
 *
 * The injection is done by (if necessary) appending an additional "L2_seq" to
 * the input monad, returning the desired set of variables.
 *
 * "allow_excess" is the output monad is allowed to return a superset of
 * "needed_returns". By allowing such excess variables to be returned, the
 * generated output can be neater than if we were more strict.
 *)
fun inject_return_vals ctxt (export_info: export_info) prog_info name_map needed_returns allow_excess throw_vars
      term (vars_read, vars_returned, output_monad, thm, cache) =
  if needed_returns = vars_returned then
    (* We already have precisely what is needed --- no more to do. *)
    (vars_read, vars_returned, output_monad, thm, cache)
  else if (allow_excess andalso Varset.subset (needed_returns, vars_returned)) then
    (* We already provide a superset of what is needed, and this is allowed. *)
    (vars_read, vars_returned, output_monad, thm, cache)
  else
    let
      val (l1_term, _, _) = get_node_data term
      (* Generate the return statement. *)
      val injected_return =
            mk_l2monad ctxt prog_info @{const_name L2_gets} needed_returns throw_vars
                [absdummy (ProgramInfo.get_globals_type prog_info) (HOLogic.mk_tuple (dest_sort_extern prog_info needed_returns |> map name_map)),
                    var_set_to_isa_list ctxt prog_info needed_returns]
            |> abs_over_tuple_vars prog_info name_map vars_returned

      (* Append the return statement to the input term. *)
      val generated_term = mk_l2monad ctxt prog_info @{const_name L2_seq}
          needed_returns throw_vars [output_monad, injected_return]
      val preserved_vals = needed_returns MINUS vars_returned
      (* Generate a proof of correctness. *)

      val generated_thm =
        let
          val (preserve_proof, cache) = mk_multivar_preservation_proof ctxt export_info prog_info name_map l1_term preserved_vals cache
        in
          mk_corresXF_thm_direct ctxt prog_info name_map needed_returns throw_vars (vars_read UNION preserved_vals)
              generated_term l1_term
              (@{thm L2corres_inject_return'} OF [thm, @{thm asm_rl} ,  @{thm validE_weaken} OF [preserve_proof]])
        end
    in
      (vars_read UNION preserved_vals, needed_returns, generated_term, generated_thm, cache)
    end

val corres_seq_split = Fun_Cache.create @{binding "L2corres_seq_split"}
  (fn c => @{make_string} c) Inttab.empty Inttab.lookup Inttab.update
  (Tuple_Tools.split_rule @{context} ["P'", "B"] @{thm L2corres_seq})

val corres_catch_split = Fun_Cache.create @{binding "L2corres_catch_split"}
  (fn c => @{make_string} c) Inttab.empty Inttab.lookup Inttab.update
  (Tuple_Tools.split_rule @{context} ["P'", "R"] @{thm L2corres_catch})

val corres_while_split = Fun_Cache.create @{binding "L2corres_while_split"}
  (fn c => @{make_string} c) Inttab.empty Inttab.lookup Inttab.update
  (Tuple_Tools.split_rule @{context} ["P'", "A"] @{thm L2corres_while})

(* Test and initialise caches *)

val _ = map corres_seq_split (1 upto 5)
val _ = map corres_catch_split (1 upto 5)
val _ = map corres_while_split (1 upto 5)

fun trace_resolve_tac do_trace ctxt thm i st =
 let
   val _ = if do_trace then tracing ("trying to resolve: " ^ Thm.string_of_thm ctxt thm) else ()
 in
   resolve_tac ctxt [thm] i st
 end

fun string_of_terms ctxt ts =
  map (Syntax.string_of_term ctxt) ts |> Pretty.strs |> Pretty.string_of

fun l2_prog_env ctxt prog_info rec_funs rec_ptrs (retT, argTs) =
 let
   val (_, P as Const (Pname, T)) = AutoCorresData.get_progenv_for_sig ctxt prog_info "" FunctionInfo.L2 (retT, argTs) |> the
   val (ptrT::argTs, retT) = strip_type T
   val funT = argTs ---> retT
   fun mk_fun_ptr fname = HP_TermsTypes.mk_fun_ptr ctxt (ProgramInfo.get_prog_name prog_info) fname
   val (empty, ptr_assoc) = map_filter (fn fname => find_first (fn (n, _) => n = fname) rec_funs) rec_ptrs
     |> filter (fn (_, Free (_, fT)) => fT = funT)
     |> `null
     ||> map (apfst mk_fun_ptr) ||> map HOLogic.mk_prod
     ||> HOLogic.mk_list (HOLogic.mk_prodT (@{typ "unit ptr"}, funT))
   val ([p], ctxt') = Utils.fix_variant_frees [("p", @{typ "unit ptr"})] ctxt
   val P = if empty then P else \<^infer_instantiate>\<open>P = P and xs = ptr_assoc in term \<open>map_of_default P xs\<close>\<close> ctxt'
 in
   SOME P
 end
 handle Option.Option => NONE


(*
 * Convert an L1 function into an L2 function.
 *
 * We assume that our input term has come out of the L1 conversion functions.
 *
 * We have inputs of the following:
 *
 *      ctxt: Isabelle context
 *
 *      needed_vars:
 *
 *          Variables that are read in later executions.
 *
 *          These are passed into the conversion so that we know what variables
 *          we need to track for later execution, and what variables we can
 *          just discard on the spot.
 *
 *          If we didn't know what we actually needed to track, then the
 *          converted code would be significantly bloated due to returning
 *          variables that aren't actually used.
 *
 *      allow_excess:
 *
 *          Are we allowed to return _more_ variables than otherwise needed
 *          according to needed_vars? By setting this to true, more efficient
 *          code can be generated.
 *
 *      throw_vars:
 *
 *          Variables that must be thrown in the event we decide to emit an
 *          "L2_throw" call. These are calculated as we enter a try/catch block
 *          to ensure that all sites are consistent in the values they throw.
 *
 *      term: The L1 term to convert.
 *
 * The return value of this function is a tuple:
 *
 *      (<vars read by block>, <vars returned>, <term>, <proof>)
 *
 * The "vars returned" is the variables that are returned through the "bind"
 * combinator.
 *)
fun do_conv
    (ctxt : Proof.context)
    (export_info: export_info)
    skips
    prog_info
    (l1_infos : FunctionInfo.function_info Symtab.table)
    (l1_call_info : FunctionInfo.call_graph_info)
    name_map
    fname
    recursive_fun_ptrs
    (fn_vars : varset)
    (callee_proofs : (term * thm list) Symtab.table)
    (grds: thm list)
    (needed_vars : varset)
    (allow_excess : bool)
    (throw_vars : varset)
    (term : (term * varset * varset, term option * varset * bool, (string * typ) list, unit) prog)
    (cache : pres_cache)
    : (varset * varset * term * thm * pres_cache) =
let
  val l1_term = get_node_data term |> #1
  val live_vars = get_node_data term |> #2
  val modified_vars = get_node_data term |> #3
  (* N.B. fixme: Clarify the usage and redundancy of the various sets and avoid recalculation of some sets.
   * A central part of this function is to perform the preservation proofs for the local variables
   * that are not changed by a block of code. The sets are already calculated before and stored
   * in the prog. Unfortunately the code seems to be varying in wheter to consider the stored
   * information or to (re-)calculate some parts on the spot.
   *)
  (*
   * needed_vars \<rightarrow> variables read after current block
   * live_vars \<rightarrow> vars for which values are preserved by current block:
   *   incomplete as they are calculated backwards from needed_vars
   * modified_vars \<rightarrow> vars modified by current block
  *)
  val inject =
      inject_return_vals ctxt export_info prog_info name_map needed_vars allow_excess throw_vars term
  fun mkthm read_vars ret_vars generated_term thm =
      mk_corresXF_thm_direct ctxt prog_info name_map ret_vars throw_vars read_vars generated_term l1_term thm
  val mk_monad = mk_l2monad ctxt prog_info
  fun do_conv' ctxt = do_conv ctxt export_info skips prog_info l1_infos l1_call_info name_map fname recursive_fun_ptrs fn_vars callee_proofs
  val do_conv = do_conv' ctxt
  fun read_vars_of_call (Call (_, expr_f, expr_args, (ret_expr, ret_read_vars, _), ret_var, _)) =
        union_sets (map #2 (expr_f::expr_args)) UNION (throw_vars MINUS exn_var)
    | read_vars_of_call t = error ("read_vars_of_call: only works for call statements: " ^ @{make_string} t)
in
  case term of
      Init (_, [output_var]) =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "Init_SOME begin " ^ fname)
          val start = Timing.start ();
          val out_vars = make_set [output_var]
          val generated_term = mk_monad @{const_name L2_unknown} out_vars throw_vars
                                        [var_set_to_isa_list ctxt prog_info out_vars]
          val thm = mkthm empty_set out_vars generated_term @{thm L2corres_spec_unknown}
        in
          inject (empty_set, out_vars, generated_term, thm, cache)
          before (timing_msg' 2 ctxt (fn _ => "Init_SOME") start)
        end

      (* L1_skip. *)
    | Modify (_, (SOME expr, _, _), []) =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "Modify_SOME begin " ^ fname)
          val start = Timing.start ();
          val generated_term = mk_monad @{const_name L2_gets}
              empty_set throw_vars [expr, var_set_to_isa_list ctxt prog_info empty_set]
          val thm = mkthm empty_set empty_set generated_term @{thm L2corres_gets_skip}
        in
          inject (empty_set, empty_set, generated_term, thm, cache)
          before (timing_msg' 2 ctxt (fn _ => "Modify_SOME") start)
        end

       (* L1_modify with unparsable expression. *)
    | Modify (_, (NONE, _, _), [output_var]) =>
       let
         val _ = verbose_msg 3 ctxt (fn _ => "Modify_NONE begin " ^ fname)
         val start = Timing.start ();
         val out_vars = make_set [output_var]
         val generated_term = mk_monad @{const_name L2_unknown} out_vars throw_vars []
         val thm = mkthm empty_set out_vars generated_term @{thm L2corres_modify_unknown}
       in
         inject (empty_set, out_vars, generated_term, thm, cache)
         before (timing_msg' 2 ctxt (fn _ => "Modify_NONE") start)
       end

      (* L1_modify that only modifies globals. *)
    | Modify (_, (SOME expr, read_vars, _), [("globals'", _)]) =>
       let
         val _ = verbose_msg 3 ctxt (fn _ => "Modify_SOME_globals begin " ^ fname)
         val start = Timing.start ();
         val generated_term = mk_monad @{const_name L2_modify} empty_set throw_vars [expr]
         val thm = mkthm read_vars empty_set generated_term @{thm L2corres_modify_global}
       in
         inject (read_vars, empty_set, generated_term, thm, cache)
         before (timing_msg' 2 ctxt (fn _ => "Modify_SOME_globals") start)
       end

      (* L1_modify that only modifies a local and also reads globals. *)
    | Modify (_, (SOME expr, read_vars, _), [output_var]) =>
       let
         val _ = verbose_msg 3 ctxt (fn _ => "Modify_SOME_SOME begin " ^ fname)
         val start = Timing.start ();
         val generated_term = mk_monad @{const_name L2_gets}
             (make_set [output_var]) throw_vars [expr, var_set_to_isa_list ctxt prog_info (make_set [output_var])]
         val thm = mkthm read_vars (make_set [output_var]) generated_term @{thm L2corres_modify_gets}
       in
         inject (read_vars, make_set [output_var], generated_term, thm, cache)
         before (timing_msg' 2 ctxt (fn _ => "Modify_SOME_SOME") start)
       end
    | Throw _ =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "Throw begin " ^ fname)
          val start = Timing.start ();
          val generated_term = mk_monad @{const_name L2_throw} needed_vars throw_vars
              [HOLogic.mk_tuple (dest_sort_extern prog_info throw_vars |> map name_map),
                    var_set_to_isa_list ctxt prog_info throw_vars]
          val thm = mkthm throw_vars needed_vars generated_term @{thm L2corres_throw}
        in
          (throw_vars, needed_vars, generated_term, thm, cache)
          before (timing_msg' 2 ctxt (fn _ => "Throw") start)
        end

    | Spec (_, (SOME expr, read_vars, _)) =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "Spec_SOME begin " ^ fname)
          val start = Timing.start ();
          val generated_term = mk_monad @{const_name "L2_spec"} needed_vars throw_vars [expr]
          val thm = mkthm read_vars needed_vars generated_term @{thm L2corres_spec}
        in
          inject (read_vars, needed_vars, generated_term, thm, cache)
          before (timing_msg' 2 ctxt (fn _ => "Spec_SOME") start)
        end

    | Spec (_, (NONE, _, _)) =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "Spec_NONE begin " ^ fname)
          val start = Timing.start ();
          val generated_term = mk_monad @{const_name "L2_fail"} needed_vars throw_vars []
          val thm = mkthm empty_set needed_vars generated_term @{thm L2corres_fail}
        in
          inject (empty_set, needed_vars, generated_term, thm, cache)
          before (timing_msg' 2 ctxt (fn _ => "Spec_NONE") start)
        end

    | Assume (_, (SOME expr, read_vars, _)) =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "Assume_SOME begin " ^ fname)
          val start = Timing.start ();
          val generated_term = mk_monad @{const_name "L2_assume"} needed_vars throw_vars [expr]
          val thm = mkthm read_vars needed_vars generated_term @{thm L2corres_assume}
        in
          inject (read_vars, needed_vars, generated_term, thm, cache)
          before (timing_msg' 2 ctxt (fn _ => "Assume_SOME") start)
        end

    | Assume (_, (NONE, _, _)) =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "Assume_NONE begin " ^ fname)
          val start = Timing.start ();
          val generated_term = mk_monad @{const_name "L2_fail"} needed_vars throw_vars []
          val thm = mkthm empty_set needed_vars generated_term @{thm L2corres_fail}
        in
          inject (empty_set, needed_vars, generated_term, thm, cache)
          before (timing_msg' 2 ctxt (fn _ => "Spec_NONE") start)
        end

    | Guard (_, (SOME expr, read_vars, _)) =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "Guard_SOME begin " ^ fname)
          val start = Timing.start ();
          val generated_term = mk_monad @{const_name "L2_guard"} empty_set throw_vars [expr]
          val thm = mkthm read_vars empty_set generated_term @{thm L2corres_guard}
        in
          inject (read_vars, empty_set, generated_term, thm, cache)
          before (timing_msg' 2 ctxt (fn _ => "Guard_SOME") start)
        end

    | Guard (_, (NONE, _, _)) =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "Guard_NONE begin " ^ fname)
          val start = Timing.start ();
          val generated_term = mk_monad @{const_name "L2_fail"} needed_vars throw_vars []
          val thm = mkthm empty_set needed_vars generated_term @{thm L2corres_fail}
        in
          (empty_set, needed_vars, generated_term, thm, cache)
          before (timing_msg' 2 ctxt (fn _=> "Guard_NONE") start)
        end

    | Fail _ =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "Fail begin " ^ fname)
          val start = Timing.start ();
          val generated_term = mk_monad @{const_name "L2_fail"} needed_vars throw_vars []
          val thm = mkthm empty_set needed_vars generated_term @{thm L2corres_fail}
        in
          (empty_set, needed_vars, generated_term, thm, cache)
          before (timing_msg' 2 ctxt (fn _ => "Fail") start)
        end

    | Seq (_, lhs, rhs) =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "Seq begin " ^ fname)
          val start = Timing.start ();
          val (_, rhs_live, rhs_modified) = get_node_data rhs
          val (lhs_term, _, lhs_modified) = get_node_data lhs

          (* Convert LHS and RHS. *)
          val ret_vars = rhs_live INTER lhs_modified
          val (lhs_reads, lhs_rets, new_lhs, lhs_thm, cache)
              = do_conv grds ret_vars true throw_vars lhs cache
          val (rhs_reads, rhs_rets, new_rhs, rhs_thm, cache)
              = do_conv grds needed_vars allow_excess throw_vars rhs cache


          val start_montage = Timing.start ();
          val block_reads = lhs_reads UNION (rhs_reads MINUS lhs_modified)

          val rhs_thm = timeit_msg 2 ctxt (fn _ => "Seq export rhs_thm: ")
            (fn _ => Morphism.thm (#phi_export export_info) rhs_thm)
          (* Reconstruct body to support our input tuple. *)
          val new_rhs = timeit_msg 2 ctxt (fn _ => "Seq abs_over_tuple_vars: ")
               (fn _ => abs_over_tuple_vars prog_info name_map lhs_rets new_rhs);

          (* Generate the final term. *)
          val generated_term = timeit_msg 2 ctxt (fn _ => "Seq mk_monad: ")
               (fn _ => mk_monad @{const_name L2_seq} rhs_rets throw_vars [new_lhs, new_rhs])

          (* Generate a proof. *)
          val (thm, cache) =
          let
            (* Show that certain variables are preserved by the LHS. *)
            val needed_preserves = (rhs_reads MINUS lhs_modified)
            val (preserve_proof, cache) = timeit_msg 2 ctxt (fn _ => "preserve_proof: ") (fn _ =>
                  mk_multivar_preservation_proof ctxt export_info prog_info name_map lhs_term needed_preserves cache);

            val weaken = timeit_msg 2 ctxt (fn _ => "weaken: ") (fn _ =>
                  @{thm validE_weaken} OF [preserve_proof])
            val seq_split = corres_seq_split (Varset.card lhs_rets)
            val seq = timeit_msg 2 ctxt (fn _ => "seq: ") (fn _ => seq_split OF [lhs_thm, rhs_thm, weaken])
          in
            timeit_msg 2 ctxt (fn _ => "Seq mkthm: ") (fn _ => (mkthm block_reads rhs_rets generated_term seq, cache))
            before (timing_msg' 2 ctxt (fn _ => "Seq_montage") start_montage)
          end
        in
          inject (block_reads, rhs_rets, generated_term, thm, cache)
          before (timing_msg' 2 ctxt (fn _ => "Seq") start)
        end

    | Catch (_, lhs, rhs) =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "Catch begin " ^ fname)
          val start = Timing.start ();
          val (lhs_term, _, lhs_modified) = get_node_data lhs
          val (_, rhs_live, _) = get_node_data rhs

          (* Convert LHS and RHS. *)
          val lhs_throws = rhs_live INTER lhs_modified
          val (lhs_reads, lhs_rets, new_lhs, lhs_thm, cache)
              = do_conv grds needed_vars false lhs_throws lhs cache
          val (rhs_reads, _, new_rhs, rhs_thm, cache)
              = do_conv grds needed_vars false throw_vars rhs cache

          val block_reads = lhs_reads UNION (rhs_reads MINUS lhs_throws)

          (* Reconstruct body to support our input tuple. *)
          val rhs_thm = timeit_msg 2 ctxt (fn _ => "Catch export rhs_thm: ")
            (fn _ => Morphism.thm (#phi_export export_info) rhs_thm)
          val new_rhs = abs_over_tuple_vars prog_info name_map lhs_throws new_rhs

          (* Generate the final term. *)
          val generated_term = mk_monad @{const_name L2_catch} needed_vars throw_vars [new_lhs, new_rhs]

          (* Generate a proof. *)
          val (thm, cache) =
          let
            (* Show that certain variables are preserved by the LHS. *)
            val needed_preserves = (rhs_reads MINUS lhs_modified)
            val (preserve_proof, cache) = mk_multivar_preservation_proof ctxt export_info prog_info name_map lhs_term needed_preserves cache
            val catch_split = corres_catch_split (Varset.card lhs_throws)
          in
            (mkthm block_reads needed_vars generated_term
                (catch_split OF [lhs_thm, rhs_thm, @{thm validE_weaken} OF [preserve_proof]]), cache)
          end
        in
          inject (block_reads, needed_vars, generated_term, thm, cache)
          before (timing_msg' 2 ctxt (fn _ => "Catch") start)
        end
    | Condition (_, (SOME expr, read_vars, _), lhs, rhs) =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "Condition begin " ^ fname)
          val start = Timing.start ();
          (* Convert LHS and RHS. *)
          val requested_vars = needed_vars INTER modified_vars (* FIXME: the INTER seems weired *)

          val (lhs_reads, _, new_lhs, lhs_thm, cache)
              = do_conv grds requested_vars false throw_vars lhs cache
          val (rhs_reads, _, new_rhs, rhs_thm, cache)
              = do_conv grds requested_vars false throw_vars rhs cache
          val block_reads = lhs_reads UNION rhs_reads UNION read_vars

          (* Generate the final term. *)
          val generated_term = mk_monad @{const_name "L2_condition"}
                requested_vars throw_vars [expr, new_lhs, new_rhs]
          val thm = mkthm block_reads requested_vars generated_term
              (@{thm L2corres_cond} OF [lhs_thm, rhs_thm])
        in
          inject (block_reads, requested_vars, generated_term, thm, cache)
          before (timing_msg' 2 ctxt (fn _ => "Condition") start)
        end

    | While (_, (SOME expr, read_vars, _), body) =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "While begin " ^ fname)
          val start = Timing.start ();
          (* Convert body. *)
          val loop_iterators = (needed_vars UNION live_vars) INTER modified_vars
          val (body_reads, _, new_body, body_thm, cache) =
              do_conv grds loop_iterators false throw_vars body cache
          val (body_term, body_live, body_modifies) = get_node_data body

          (* Reconstruct body to support our input tuple. *)
          val new_body = abs_over_tuple_vars prog_info name_map loop_iterators new_body
          val body_thm = timeit_msg 2 ctxt (fn _ => "While export body_thm: ")
            (fn _ => Morphism.thm (#phi_export export_info) body_thm)

          (* Generate the final term. *)
          val generated_term =
              mk_monad @{const_name "L2_while"} loop_iterators throw_vars [
                abs_over_tuple_vars prog_info name_map loop_iterators expr,
                new_body,
                HOLogic.mk_tuple (dest_sort_extern prog_info loop_iterators |> map name_map),
                var_set_to_isa_list ctxt prog_info loop_iterators]

          (* Generate a proof. *)
          val (thm, cache) =
          let
            (* Show that certain variables are preserved by the LHS. *)
            val needed_preserves = ((body_reads UNION read_vars)  MINUS body_modifies)
            val (preserve_proof, cache) = mk_multivar_preservation_proof ctxt export_info prog_info name_map body_term needed_preserves cache

            (* Instantiate while loop rule to avoid ambiguous unification. *)
            val tracked_vars = (body_reads UNION read_vars UNION loop_iterators)
            val invariant_precond = abs_over_tuple_vars prog_info name_map loop_iterators
                  (mk_precond ctxt prog_info name_map tracked_vars)
            val while_split = corres_while_split (Varset.card loop_iterators)
            val base_thm = Utils.named_cterm_instantiate ctxt [
                  ("P", Thm.cterm_of ctxt invariant_precond)
                ] while_split
          in
            (mkthm (body_reads UNION read_vars UNION loop_iterators) loop_iterators generated_term
                (base_thm OF [body_thm, @{thm validE_weaken} OF [preserve_proof]]), cache)
          end
        in
          inject (body_reads UNION read_vars UNION loop_iterators, loop_iterators, generated_term, thm, cache)
          before (timing_msg' 2 ctxt (fn _ => "While") start)
        end
    | Guarded (_, (SOME g, read_vars, _), (SOME dest, read_vars_dest, _), bdy) =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "Guarded begin " ^ fname)
          val start = Timing.start ();
          val bdy_reads = read_vars_of_call bdy
          val @{term_pat "L1_guarded ?g' (gets ?dest' \<bind> ?c0')"} = l1_term
          val s' = dummy_state_guards_l1 prog_info
          val s = dummy_state_guards_l2 prog_info
          val bdy_precond = mk_precond ctxt prog_info name_map bdy_reads
          val st = ProgramInfo.get_globals_getter prog_info
          val ([_, _], ctxt') = Utils.gen_fix_variant_frees true (map dest_Free [s', s]) ctxt
          val ([g_thm, st_eq, bdy_precond_thm], ctxt') = ctxt'
            |> Assumption.add_assumes (map (Thm.cterm_of ctxt') [
                  HOLogic.Trueprop $ (g' $ s'),
                  HOLogic.Trueprop $ (HOLogic.mk_eq (s, st $ s')),
                  HOLogic.Trueprop $ (bdy_precond $ s')])
          val g_thms = Utils.split_conj g_thm
  
          val (bdy_reads, bdy_rets, new_bdy, bdy_thm, cache)
              = do_conv' ctxt' (grds @ [g_thm, st_eq, bdy_precond_thm]) (needed_vars) allow_excess throw_vars bdy cache

          val @{term_pat "L2corres ?st ?ret ?ex ?P ?c ?c'"} = bdy_thm |> Thm.concl_of |> HOLogic.dest_Trueprop
          val p' = Envir.beta_eta_contract (dest' $ s')
          val p = Envir.beta_eta_contract (dest $ s)
          val c = Utils.abs_over "p" p c
          val c' = Utils.abs_over "p" p' c'
          val [bdy_thm] = Proof_Context.export ctxt' ctxt [bdy_thm]
          val new_bdy = Utils.abs_over "p" p new_bdy
          val new_bdy =  \<^infer_instantiate>\<open>dest = dest and bdy = new_bdy in term \<open>L2_seq (L2_gets dest []) bdy\<close>\<close> ctxt
          val generated_term = mk_monad @{const_name "L2_guarded"} bdy_rets throw_vars [g, new_bdy]
          val rule = @{thm L2corres_guarded''} |> Drule.infer_instantiate' ctxt
                (map (SOME o Thm.cterm_of ctxt) [g', st, bdy_precond, ret, ex, c, dest, c', dest', g])
          val thm = mkthm bdy_reads bdy_rets generated_term (rule OF [bdy_thm])
        in
          inject (bdy_reads, bdy_rets, generated_term, thm, cache)
          before (timing_msg' 2 ctxt (fn _ => "Guarded") start)
        end
    | (call_t as Call (_, expr_f, expr_list, (ret_expr, ret_read_vars, _), ret_var, _)) =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "Call begin " ^ fname)
          val start = Timing.start ();
          val @{term_pat "_ ?arg_setup ?callee ?return_norm ?return_exn ?ret_extract"} = l1_term

          val (callee, is_fun_ptr) = case callee of
                (Const (P, _) $ f') => if Long_Name.base_name P = AutoCorresData.progenvN (* FIXME *) then (f', true) else (callee, false)
                | _ => (callee, false)

          val callee_scope = if is_fun_ptr then I else callee_scope prog_info callee
          (* Parse argument setup. *)
          val arg_setup_vals = gen_parse_modify {read_scope = I, write_scope = callee_scope, two_state = false}
                ctxt prog_info name_map arg_setup |> List.rev
          val arg_rets = gen_parse_modify {read_scope = callee_scope, write_scope = I, two_state = true}
                ctxt prog_info Free ret_extract |> map #2 |> flat

          val (callee_trm, args, callee_thms) =
            if is_fun_ptr
            then
              let
                val retT = if null arg_rets then @{typ unit} else snd (hd arg_rets)
                val args = arg_setup_vals |> map #1 (* FIXME  should also work for ordinary call *)
                val argTs = map snd args
                val rec_funs = Symtab.dest callee_proofs |> map (fn (n, (t, _)) => (n, t))
                val penv = l2_prog_env ctxt prog_info rec_funs recursive_fun_ptrs (retT, argTs)
                val ptr_parameter_callee_thms = case HPInter.dest_local_var_lookup callee of
                       SOME (Free (p, _), _, _) =>
                           Symtab.lookup callee_proofs p |> the |> #2
                      | _ => []
                val callee_thms = AutoCorresData.get_default_phase_info (Context.Proof ctxt) (ProgramInfo.get_prog_name prog_info) FunctionInfo.L2
                       |> Symtab.dest |> map_filter (FunctionInfo.get_proper_corres_thm o snd)

                val (_, _, SOME callee') = parse_expr ctxt prog_info name_map
                      (Utils.abs_over "s" (dummy_state_guards_l1 prog_info) callee)
                val callee' = betapply(callee', dummy_state_guards_l2 prog_info)
              in
                case penv of
                  SOME penv => (penv $ callee', args, ptr_parameter_callee_thms @ callee_thms)
                | NONE =>  error ("do_conv: could not retrieve program environment for: " ^
                           quote (Syntax.string_of_term ctxt callee))
              end
            else
              let
                val callee_name = Termtab.lookup (#const_to_function l1_call_info) (l1call_function_const callee) |> the
                val callee' = Symtab.lookup l1_infos callee_name
                val callee_proof = Option.mapPartial
                   (Symtab.lookup callee_proofs) (Option.map FunctionInfo.get_name callee')
              in
                case callee_proof of
                  SOME (callee_free, callee_thms) =>
                    (callee_free,
                     map (apfst NameGeneration.Named) (FunctionInfo.get_plain_args (the callee')),
                     callee_thms)
                | NONE =>
                    (case AutoCorresData.get_function_info (Context.Proof ctxt)
                            (ProgramInfo.get_prog_name prog_info) (FunctionInfo.L2) callee_name of
                       SOME callee_info => (FunctionInfo.get_const callee_info,
                                           map (apfst NameGeneration.Named) (FunctionInfo.get_plain_args callee_info),
                                           FunctionInfo.get_corres_thm callee_info |> single)
                     | NONE => error ("do_conv: could not retrieve callee theorem for: " ^
                              quote (Syntax.string_of_term ctxt callee)))
              end

          (* Ensure that we can parse everything. *)
          val arg_setup_vals =
            map (fn (a, b, c, parsed_expr) =>
              case parsed_expr of
                  NONE =>
                    raise Utils.InvalidInput ("Could not parse function parameter '" ^ @{make_string} (fst a) ^ "'")
                | SOME x =>
                    (a, b, c, x)
              ) arg_setup_vals

          (* Sanity check: ensure that we have the correct number of arguments. *)
          val _ = if length arg_setup_vals <> length args then
              raise TERM ("Argument list length does not match function definition.", [arg_setup])
            else
              ()

          (* Rename input parameter names. *)
          fun new_name (NameGeneration.Named x) sfx = Variable.variant_fixes [suffix sfx x] ctxt |> fst |> hd
            | new_name (NameGeneration.Positional (i, T)) sfx =
                Variable.variant_fixes [suffix sfx (string_of_int i)] ctxt |> fst |> hd
          val arg_setup_vals = map (fn ((a, T), b, c, d) => ((new_name a "'param", T), b, c, d)) arg_setup_vals
          (* Generate the call. *)

          val args = map (Free o #1) arg_setup_vals
          val call_args =
              (betapplys (callee_trm, args))

          val exn_var_term = name_map exn_name_type

          fun mk_exn t = if t = exn_var_term then
                          \<^instantiate>\<open>e = exn_var_term in term \<open>Nonlocal (the_Nonlocal e)\<close> for e::\<open>exit_status CProof.c_exntype\<close>\<close>
                         else t
          val emb = Utils.abs_over exn_name exn_var_term (HOLogic.mk_tuple (dest_sort_extern prog_info throw_vars |> map (mk_exn o name_map )))
          val (call, ret_vars) =
            case (filter_out (fn x => x = exn_name_type) ret_var, ret_expr) of
                ([("globals'", _)], SOME e) =>
                    (mk_monad @{const_name L2_modifycall} empty_set throw_vars
                        [call_args, e, emb, CLocals.name_hints ctxt ["ret"]], empty_set)
              | ([x], SOME e) =>
                    (mk_monad @{const_name L2_returncall} (make_set [x]) throw_vars
                        [call_args, e, emb, CLocals.name_hints ctxt [fst x]], make_set [x]) 
              | ([], _) =>
                    (mk_monad @{const_name L2_voidcall} empty_set throw_vars
                        [call_args, emb, CLocals.name_hints ctxt ["ret"]], empty_set)
              | _ => error ("LocalVarExtract.do_conv unexpected input for call")
          (*
           * We have a list of arguments; some may be expressions that refer to
           * global variables, while others will be purely local variables. We
           * just emit them all as "L2_gets" calls, and will clean them up
           * later.
           *)
          val extractors = foldr (
            fn ((updated_var, read_vars, is_globals_reader, expr), rest) =>
              let
                val ret_type = (make_set [("x'", fastype_of expr |> body_type)])
                val rest_type = (make_set [("x'", AutoCorresData.res_type_of_exn_monad rest)])
                val getter = mk_monad @{const_name L2_folded_gets} ret_type throw_vars
                              [expr,
                               var_set_to_isa_list (callee_scope ctxt) prog_info
                                 (make_set [apfst (unsuffix "'param") updated_var])]
              in
                mk_monad @{const_name "L2_seq"} rest_type throw_vars [
                  getter,
                  Utils.abs_over (fst updated_var) (Free updated_var) rest]
              end
              )
              call
              arg_setup_vals
          (* (: check ret_read_vars: These should be read in the callee, so they should be unimportant here! *)
          val read_vars = read_vars_of_call call_t
          (* Generate a proof. *)
          val my_debug_tac = if false then print_tac ctxt else fn _ => all_tac
          val L2_call_thms = @{thms L2corres_returncall L2corres_voidcall L2corres_modifycall}

          val thy_ss = simpset_of (Proof_Context.init_global (Proof_Context.theory_of ctxt))

          val fun_ptr_simps = Named_Theorems.get ctxt @{named_theorems "fun_ptr_simps"}
          val only_fun_ptr_simps =
            let
               val ss = simpset_of (put_simpset HOL_basic_ss ctxt
                        addsimps fun_ptr_simps)
            in put_simpset ss end

          (* FIXME: with the attributes in place we might be able to unify / simplify the cases *)
          fun callee_tac ctxt thms =
            if is_fun_ptr
            then
              let
                val ctxt = put_simpset thy_ss ctxt
              in
                SOLVES_debug ctxt "callee_tac (1)" (EVERY [
                  Method.insert_tac ctxt grds 1,
                  AutoCorresUtil.dyn_call_split_simp_sidecondition_tac
                    (AutoCorresUtil.check_dyn_call_goal ctxt prog_info
                        (AutoCorresUtil.prev_phase_pair skips FunctionInfo.L2))
                    thms [] ctxt 1,
                  REPEAT (resolve_tac ctxt thms 1 THEN (REPEAT (Method.assm_tac ctxt 1)))])
              end
            else
              let
              in
                SOLVES_debug ctxt "callee_tac (2)" (
                  REPEAT1 (EVERY [ (* FIXME: bad style. Might solve to many subgoals *)
                    simp_tac (only_fun_ptr_simps ctxt) 1,
                    resolve_tac ctxt thms 1]))
              end

          val known_function_corres = Named_Theorems.get ctxt @{named_theorems known_function_corres}

          val all_callee_thms = callee_thms @
                Named_Theorems.get ctxt @{named_theorems "l2_corres"} @
                Named_Theorems.get ctxt @{named_theorems "l1_corres"} @ 
                known_function_corres

          val thm =
            mk_corresXF_thm ctxt prog_info name_map ret_vars throw_vars read_vars  extractors l1_term (fn {context=ctxt, ...} =>
              (my_debug_tac "unfold folded_gets"
                    THEN (REPEAT (resolve_tac ctxt @{thms L2corres_folded_gets} 1)))
              THEN (my_debug_tac "propagate fixed function pointer parameters"
                    THEN (asm_full_simp_tac (ctxt addsimps @{thms More_Lib.pred_conj_def}
                          |> Simplifier.add_cong @{thm L2corres_l2_propagate_fixed_cong}) 1)
                    THEN (my_debug_tac "apply callee proof")
                    THEN FIRST (map_index (fn (i, thm) =>
                                               trace_resolve_tac false ctxt thm 1 THEN
                                               my_debug_tac ("resolved L2_call_thms (" ^ string_of_int i ^ ")") THEN
                                               callee_tac ctxt all_callee_thms)
                                    L2_call_thms))
              THEN (my_debug_tac "final simp" (* FIXME: cleanup is this THEN_ALL_NEW? *)
                    THEN (REPEAT (CHANGED (asm_full_simp_tac ctxt 1))))
            )
        in
          inject (read_vars, ret_vars, extractors, thm, cache)
          before (timing_msg' 2 ctxt (fn _ => "Call") start)

        end
    | Stack ((t, _,_), (SOME expr, read_vars, _), bdy) =>
        let
          val _ = verbose_msg 3 ctxt (fn _ => "Stack begin " ^ fname)
          val start = Timing.start ();

          val requested_vars = needed_vars UNION read_vars (* read_vars: variables read in init *)
          val {n, init, c, ...} = with_fresh_stack_ptr.match ctxt t
          val Abs (pn, pT, _) = c

          val sT = fastype_of init |> domain_type
          val ([p], ctxt') = Utils.gen_fix_variant_frees true [(pn, pT)] ctxt
          val (bdy_reads, _, new_bdy, bdy_thm, cache)
              = do_conv' ctxt' grds requested_vars false throw_vars bdy cache
          val [bdy_thm] =  [bdy_thm] |> Proof_Context.export ctxt' ctxt
          val rules = Named_Theorems.get ctxt @{named_theorems L2corres_with_fresh_stack_ptr}
                      |> Utils.OFs [bdy_thm]
          val with_fresh_stack_ptr = with_fresh_stack_ptr.term ctxt (ProgramInfo.get_globals_type prog_info)
          val new_bdy = Term.lambda_name (pn, p) new_bdy
          val name_hint = CLocals.name_hint ctxt (TermsTypes.dest_local_ptr_name pn)
            |> single |> HOLogic.mk_list \<^typ>\<open>nat\<close>

          val generated_term = \<^infer_instantiate>\<open>w=with_fresh_stack_ptr and init = expr and c = new_bdy and
                nm = name_hint and n=n
                in term \<open>w n init (L2_VARS c nm)\<close>\<close> ctxt
          val block_reads = bdy_reads UNION read_vars
          val thm = mkthm block_reads requested_vars generated_term (hd rules)
        in
          inject (block_reads, requested_vars, generated_term, thm, cache)
          before (timing_msg' 2 ctxt (fn _ => "Stack") start)
        end
    | _ => Utils.invalid_input "a parsed L1 term" (l1_term |> head_of |> @{make_string})
end

val internalN = "lvar'"
val internal_name = prefix internalN

fun l2_fn_ptr info =
  let
    val l2_info = info FunctionInfo.L2
  in #prog_env l2_info $ Free (#ptr_val l2_info) end

(* Get the expected type of a function from its name. *)
fun get_expected_l2_fn_type prog_info fn_ptr_infos l1_infos fn_name =
let
  val (args, retT) = case AList.lookup (op =) fn_ptr_infos fn_name of
               SOME info =>
                  let val l2_info = info FunctionInfo.L2
                  in (#args l2_info, AutoCorresData.retT_from_fn_ptr_info l2_info) end
             | NONE => the (Symtab.lookup l1_infos fn_name)
                    |> (fn info => (FunctionInfo.get_plain_args info, FunctionInfo.get_return_type info))
  val fn_params_typ = map (#2) args
in
  fn_params_typ ---> AutoCorresData.mk_l2monadT (ProgramInfo.get_globals_type prog_info) retT HP_TermsTypes.c_exntype_ty
end

(* Get arguments passed into the function. *)
fun get_expected_l2_fn_args lthy prog_info fn_ptr_infos l1_infos fn_name =
let
  val args = case AList.lookup (op =) fn_ptr_infos fn_name of
               SOME info => #args (info FunctionInfo.L2)
             | NONE => the (Symtab.lookup l1_infos fn_name) |> FunctionInfo.get_plain_args
in
  map (apfst (ProgramInfo.demangle_name prog_info)) args
end

fun mk_fn_ptr_infos ctxt prog_info fn_args info =
  AutoCorresData.mk_fn_ptr_infos ctxt prog_info "" fn_args info

fun get_l2_corres_prop skips prog_info fn_ptr_infos l1_infos ctxt assume fn_name fn_free fn_args  =
let
  val ctxt = HPInter.enter_scope (ProgramInfo.get_prog_name prog_info) fn_name ctxt
  (* Fetch input/output params for monad type. *)
  val (input_params, output_params) = get_fn_input_output_vars fn_ptr_infos l1_infos fn_name

  val l2_corres_attr = AutoCorresData.corres_thm_attribute (ProgramInfo.get_prog_name prog_info) skips FunctionInfo.L2 fn_name

  (* Get mapping from internal variable names that we use to the names passed
   * in "fn_args". *)
  val (l1_fun, l2_fun, args, l1_props) = case AList.lookup (op =) fn_ptr_infos fn_name of
        SOME info =>
          let
            val cp_info = info FunctionInfo.CP
            val l1_info = info FunctionInfo.L1
            val l2_info = info FunctionInfo.L2
            val Gamma = #prog_env cp_info
            val P_l1 = #prog_env l1_info
            val P_l2 = #prog_env l2_info
            val p = Free (#ptr_val l2_info)
            val l1_corres_attr = AutoCorresData.corres_thm_attribute
                  (ProgramInfo.get_prog_name prog_info) skips FunctionInfo.L1 fn_name

          in (P_l1 $ p, P_l2 $ p, #args l2_info,
               [(\<^infer_instantiate>\<open>G = Gamma and P = P_l1 and proc = p
                   in prop\<open>L1corres True G (P proc) (Call (proc))\<close>\<close> ctxt,
                [l1_corres_attr])])
          end
      | NONE => the (Symtab.lookup l1_infos fn_name) |> (fn info =>
                  (FunctionInfo.get_const info, fn_free, FunctionInfo.get_plain_args info, []))


  val prems = case Symtab.lookup l1_infos fn_name of
        SOME info => (* regular function not a function pointer parameter *)
          let  (* We add corres preconditions for any function pointer parameter in this function *)
            val fn_ptr_param_infos = mk_fn_ptr_infos ctxt prog_info fn_args info
          in
            fn_ptr_param_infos
            |> map (fn (ptr, ptr_info) =>
                let
                  val l2_info = ptr_info FunctionInfo.L2
                  val p = Free (#ptr_val l2_info)
                  val args = map Free (#args l2_info)
                  val (l1_props, (l2_prop, _)) =
                    get_l2_corres_prop skips prog_info fn_ptr_param_infos l1_infos ctxt false ptr p args
                  val l2_prop = fold Logic.all (rev args) l2_prop
                in map fst l1_props @ [l2_prop] end)
            |> flat
          end
        | NONE => []

  val args = map fst args
  val m = Symtab.make (args ~~ fn_args)
  fun name_map (n, _) = Symtab.lookup m n |> the
in
  (l1_props,
    (Logic.list_implies (prems,
       mk_corresXF_prop ctxt prog_info name_map
         output_params exn_var input_params
         (betapplys (l2_fun, fn_args))
         (l1_fun)), [l2_corres_attr]))
end




(* Extract the abstract body of a L2corres theorem. *)
fun get_body_of_thm ctxt thm =
  Thm.concl_of (Variable.gen_all ctxt thm)
  |> HOLogic.dest_Trueprop
  |> dest_L2corres_term_abs

fun get_l2corres_thm ctxt skips prog_info l1_infos fn_ptr_infos l1_call_info L2_opt trace_opt fn_name
    callee_terms fn_args l1_term init_unfold = let
  val ctxt = HPInter.enter_scope (ProgramInfo.get_prog_name prog_info) fn_name ctxt
  (* Get information about the return variable. *)
  val fn_info = the (Symtab.lookup l1_infos fn_name)

  val recursive_fun_ptrs = FunctionInfo.get_clique_recursion_fun_ptrs fn_info
  (* Get return variables. *)
  val (fn_input_vars, fn_local_vars, fn_ret_vars) = get_variables l1_infos fn_name

  (* Get mapping from internal variable names to external arguments. *)
  val m = Symtab.make (map fst (FunctionInfo.get_plain_args fn_info) ~~ fn_args)
  fun name_map_ext (n, T) = Symtab.lookup m n |> the

  val fn_ptr_param_map = fn_ptr_infos
    |> map (fn (n, info) => (NameGeneration.un_varname n, #1 (#ptr_val (info FunctionInfo.L2))))
    |> AList.lookup (op =)

  fun remove_fn_ptr_params vars = vars
    |> filter_out (is_some o fn_ptr_param_map o fst)

  val fn_input_vars_wo_fn_ptr_params = fn_input_vars |> Varset.dest |> remove_fn_ptr_params |> Varset.make

  fun name_map_internal (n, T) =
    case fn_ptr_param_map n of
      SOME n' => Free (n', T)
    | NONE => Free (internal_name n, T)



  (*
   * Many constructs from SIMPL (and also L1) are in set form, but we really
   * need them to be in functional form to be able to effectively parse them.
   * In particular we can parse:
   *
   *      (%s. s \<cdot> n)
   *
   * but not:
   *
   *      {s. s \<cdot> n}
   *
   * We do some basic conversions here to convert common sets into lambda
   * functions.
   *)
  val init_rule = Thm.cterm_of ctxt l1_term
    |> Conv.rewr_conv (safe_mk_meta_eq init_unfold)

  (* Extract the term we will be working with. *)
  val source_term = Thm.concl_of init_rule |> Utils.rhs_of_eq

  (* Do basic parsing. *)
  val parsed_term = parse_l1 ctxt prog_info l1_infos l1_call_info name_map_internal source_term
  val _ = verbose_msg 4 ctxt (fn _ => "parsed_term " ^ fn_name ^ ": " ^ @{make_string}
         (parsed_term |> Prog.map_prog (fn _ => Bound 0) I I I))
  (* Get a list of all variables either read from or written to. *)
  val all_vars = Prog.fold_prog
      (K I)
      (fn (_, vars, _) => fn old_vars => vars UNION old_vars)
      (fn mod_var => fn old_vars =>  mod_var UNION old_vars)
      (K I)
      parsed_term empty_set

  (* Perform liveness analysis of the function. *)
  val liveness_data = calc_live_vars exn_var parsed_term (union_sets [fn_ret_vars]) exn_var
  (*
   * Get information about modified variables.
   *
   * "NONE" represents "modifies potentially all variables"; we modify
   * the results to fit this.
   *)
  val _ = verbose_msg 3 ctxt (fn _ => "liveness_data " ^ fn_name ^ ": " ^ @{make_string} liveness_data)

  val modification_data =
      get_modified_vars parsed_term
      |> map_prog (fn x => Option.getOpt (x, all_vars)) I I I

  (* Combine collected data. *)
  fun zip_node_data a b c =
    zip_progs a (zip_progs b c)
    |> map_prog (fn (a, (b, c)) => (a, b, c)) fst (dest_sort_extern prog_info o fst) fst
  val input_term = zip_node_data parsed_term liveness_data modification_data

  (* Ensure that the only live variables at the beginning of the function are
   * those that are function inputs. *)
  val fn_inputs = get_node_data liveness_data
  val fn_params = FunctionInfo.get_plain_args fn_info
  val excess_inputs = fn_inputs MINUS (make_set fn_params)
  val _ =
    if excess_inputs <> empty_set then
      warning
          ("Input function '" ^ fn_name ^ "' has unresolved variables: "
              ^ @{make_string} (dest_sort_extern prog_info excess_inputs))
    else
      ()

  (* Do the conversion. *)
  val all_vars = map Varset.dest [fn_input_vars_wo_fn_ptr_params, fn_local_vars, fn_ret_vars, exn_var] |> flat
  val all_vars_internal = map (fn (n,T) => (Term.dest_Free (name_map_internal (n,T)))) all_vars;

  val _ = verbose_msg 2 ctxt (fn _ =>  "all_vars_internal: " ^ @{make_string} all_vars_internal)

  val (all_vars_internal', ctxt_internal) = Utils.fix_variant_frees all_vars_internal ctxt;
  val _ = verbose_msg 2 ctxt (fn _ =>  "all_vars_internal': " ^ @{make_string} all_vars_internal')

  val phi_import = perhaps (dest_Free #> fst
    #> AList.lookup (op =) (map fst all_vars_internal ~~ all_vars_internal'))
  val name_map_internal = phi_import o name_map_internal
  val ([dummy_value, dummy_init], ctxt') = Variable.variant_fixes ["dummy_val", "dummy_init"] ctxt_internal
  val phi_export = Variable.export_morphism ctxt' ctxt
  val phi_cache = Variable.export_morphism ctxt' ctxt_internal

  \<comment>\<open>
    In ctxt' we fix the local variables that we are about to abstract into lambdas.
    The fixed variables will be used in the correspondence proof of subterms to denote the *current*
    live value of the corresponding variable. Eventually this value will be abstracted in a lambda.
    Consider sequential composition: L2_seq X (\<lambda>v. Y v)
    First we do a correspondence proof for Y  with a fixed "v" (to some L1 statement).
    Then it is 'abstracted' to the bound "v" when it is composed in @{thm L2corres_seq}.
    In order to achieve this we export the result such that "v" becomes a "?v" before applying
    it on @{thm L2corres_seq} for unification. Therefor the morphism \<open>phi_export\<close> is used within
    the proof.

    Note that at any point in the proof, there will be *at most one* live value for each variable.
    That is why it is sufficient to fix the local variables once here at the outside of the
    proof. The context ctxt' will remain the same throughout the proof. The \<open>name_map_internal\<close>
    is used by auxiliary functions to generate the fixed variables for the corresponding
    state-selections in the L1 term.

    A cache is maintained for variable preservation proofs of subterms. Certain portions
    of the term are generalized in the term pattern with placeholders, to improve cache hits.
    The context ctxt'  also holds the placeholders ('dummy_value' / 'dummy_init'), and the
    morphism 'phi_cache' is used to generalize over the placeholders.
   \<close>

  fun assert_fixed ctxt name_map = fn x =>
    let
      val res as Free(n, T) = name_map x
      val _ = if Variable.is_fixed ctxt n then () else
        error ("unexpected local variable: " ^ quote n ^ " for " ^ @{make_string} x)
    in res end;

  val checked_name_map_internal = assert_fixed ctxt' name_map_internal

  val export_info = {phi_export = phi_export, phi_cache = phi_cache,
    dummy_value = dummy_value, dummy_init = dummy_init,
    weaken_superset = weaken_superset ctxt' phi_export prog_info checked_name_map_internal}


  val ctxt_ss = setup_l2_ss HOL_basic_ss ctxt'
  val _ = verbose_msg 2 ctxt' (fn _ => "input_term " ^ fn_name ^ ": " ^ Syntax.string_of_term ctxt' (#1 (get_node_data input_term)))
  val _ = verbose_msg 2 ctxt' (fn _ => "input_term (raw) " ^ fn_name ^ ": " ^ @{make_string} (#1 (get_node_data input_term)))
  val (_, _, term, thm, cache) = timeit_msg 1 ctxt_ss (fn _ => "Conversion L2 (do_conv) " ^ fn_name ^ ": ") (fn _ =>
        do_conv ctxt_ss export_info skips prog_info l1_infos l1_call_info checked_name_map_internal
                 fn_name recursive_fun_ptrs fn_input_vars
                 callee_terms [] fn_ret_vars false exn_var input_term (pres_cache_empty ctxt'));
  val [thm] = Variable.export ctxt' ctxt [thm];
  val _ = verbose_msg 0 ctxt' (fn _ => "preservation_cache (hits: " ^ string_of_int (get_hits cache) ^
      ", misses: " ^ string_of_int (get_misses cache) ^
      ", superset: " ^ string_of_int (get_superset cache) ^
      ", join: " ^ string_of_int (get_join cache) ^
      ", mode: " ^ string_of_int (get_mode cache) ^ ")")


  (* Replace our internal terms with external terms. *)
  val fn_params_wo_fn_ptr = remove_fn_ptr_params fn_params
  val replacements = (map (dest_Var o Morphism.term phi_export o name_map_internal) fn_params_wo_fn_ptr) ~~
       (map (Thm.cterm_of ctxt o name_map_ext) fn_params_wo_fn_ptr)
  val inst_extern = AList.lookup (op =) replacements


  (*
   * Generate a theorem with the folded L1-function and with the L2-function unfolded.
   * Moreover, use external fixed variable names for the parameters.
   * Moreover, generalize precondition to contain full list of input parameters in canonical order as
   * the proof above might have ended up with a theorem only containing a subset of the parameters.
   *)
  val thm_folded = timeit_msg 2 ctxt  (fn _ => "fold: ") (fn _ => Local_Defs.fold ctxt [init_rule] thm);

  val new_thm = Utils.instantiate_thm_vars ctxt inst_extern thm_folded
  val @{term_pat "Trueprop (L2corres _ _ _ ?precond _ _)"} = Thm.prop_of new_thm
  val canonical_precond = mk_precond ctxt prog_info name_map_ext fn_input_vars
  val generalize_precond = \<^infer_instantiate>\<open>P = canonical_precond and Q = precond in prop \<open>pred_imp P Q\<close>\<close> ctxt
  val generalize_precond_thm = Goal.prove ctxt [] [] generalize_precond (fn {context, ...} => EVERY [
        resolve_tac context @{thms pred_impI} 1,
        TRY (resolve_tac context @{thms TrueI} 1),
        REPEAT (eresolve_tac context @{thms pred_andE} 1),
        REPEAT (TRY (resolve_tac context @{thms pred_andI} 1) THEN assume_tac context 1)])
  val new_thm = @{thm L2corres_guard_imp} OF [new_thm, generalize_precond_thm]

  (* Remove intermediate scaffolding. *)
  fun corres_prog_conv conv = Conv.fconv_rule (Utils.remove_meta_conv (fn ctxt =>
     Utils.nth_arg_conv 5 (conv ctxt)) ctxt)
  val new_thm = new_thm |> corres_prog_conv (fn ctxt =>
    Raw_Simplifier.rewrite ctxt false @{thms L2_remove_scaffolding_1}
    then_conv
    Raw_Simplifier.rewrite ctxt false @{thms L2_remove_scaffolding_2})


  (* Cleanup. *)
  val _ = writeln ("Simplifying (L2opt) " ^ fn_name)
  val _ = verbose_msg 1 ctxt (fn _ => "L2 (raw) - " ^ fn_name ^ ": " ^ Thm.string_of_thm ctxt new_thm)
  (* HACK: we need to avoid these simps until heap_lift *)
  val cleanup_del = @{thms ptr_coerce.simps ptr_add_0_id}
  val fn_ptr_guard_simps = callee_terms |> Symtab.dest |> map (#2 o #2) |> flat
  val ctxt = ctxt |> AutoCorresTrace.put_trace_info fn_name FunctionInfo.L2 FunctionInfo.PEEP;
  val new_thm = timeit_msg 1 ctxt (fn _ => "Simplification (L2opt): " ^ fn_name) (fn _ =>
    L2Opt.cleanup_thm_tagged (ctxt delsimps cleanup_del) fn_ptr_guard_simps [] new_thm
    L2_opt 5 trace_opt "L2")
  val _ = verbose_msg 1 ctxt (fn _ => "L2 (L2opt) - " ^ fn_name ^ ": " ^ Thm.string_of_thm ctxt new_thm)

  (* Introduce nested exceptions *)

  val _ = writeln ("Introduce nested exceptions (L2exn) " ^ fn_name)
  val _ = Utils.verbose_fn 2 ctxt (fn _ => Synthesize_Rules.print_rules (Context.Proof ctxt) @{synthesize_rules_name L2_rel_spec_monad} NONE)
  val new_thm = timeit_msg 1 ctxt (fn _ => "Nested exceptions (L2exn): " ^ fn_name) (fn _ =>
    new_thm
    |> corres_prog_conv (fn ctxt => (L2_Exception_Rewrite.abstract_try_catch_conv ctxt))
   )
  val _ = verbose_msg 1 ctxt (fn _ => "L2 (L2exn) - " ^ fn_name ^ ": " ^ Thm.string_of_thm ctxt new_thm)


  val _ = writeln ("Remove unused tuple components (L2prj) " ^ fn_name)
  val new_thm = timeit_msg 1 ctxt (fn _ => "Remove unused tuple components (L2prj): " ^ fn_name) (fn _ =>
    new_thm
    |> corres_prog_conv (fn ctxt => (L2_Exception_Rewrite.project_used_components_conv ctxt))
   )
  val _ = verbose_msg 1 ctxt (fn _ => "L2 (L2prj) - " ^ fn_name ^ ": " ^ Thm.string_of_thm ctxt new_thm)
in
  new_thm
end


(* For functions that are not translated, just generate a trivial wrapper. *)
fun mk_l2corres_call_simpl_thm prog_info l1_infos fn_ptr_infos ctxt fn_name fn_args = let
    val fn_def = the (Symtab.lookup l1_infos fn_name)
    val const = FunctionInfo.get_const fn_def
    val args = FunctionInfo.get_plain_args fn_def

    val f_info = Utils.the' ("L2 conversion missing info for " ^ fn_name)
                          (Symtab.lookup l1_infos fn_name);

    (* Get return variables. *)
    val (fn_input_vars, fn_ret_vars) = get_fn_input_output_vars fn_ptr_infos l1_infos fn_name
    (* Get mapping from internal variable names to external arguments. *)
    val m = Symtab.make (map fst args ~~ fn_args)
    fun name_map_ext (n, T) = Symtab.lookup m n |> the

    val arg_xf = mk_precond ctxt prog_info name_map_ext fn_input_vars
    val ret_xf = mk_xf ctxt prog_info fn_ret_vars
    (*val ex_xf = Abs ("s", #state_type prog_info, HOLogic.unit)*)
    val ex_xf = mk_xf ctxt prog_info exn_var

    val thm = Utils.named_cterm_instantiate ctxt
              (map (apsnd (Thm.cterm_of ctxt))
                   [("l1_f", betapply (const, Free ("rec_measure'", @{typ "nat"}))),
                    ("ex_xf", ex_xf), ("gs", ProgramInfo.get_globals_getter prog_info),
                    ("ret_xf", ret_xf), ("arg_xf", arg_xf)])
              @{thm L2corres_L2_call_simpl}
        OF [FunctionInfo.get_definition fn_def]
  in thm end

fun insert_fn_ptr name =
 Varset.insert (name, @{typ "unit ptr"})

val insert_fn_ptrs = fold insert_fn_ptr

(*
 * Convert a single function. Returns a thm that looks like
 *   \<lbrakk> L2corres ?callee1 l1_callee1; ... \<rbrakk> \<Longrightarrow>
 *   L2corres (conversion result...) l1_f
 * i.e. with assumptions for called functions, which are parameterised as Vars.
 *)
fun convert
      (lthy: local_theory) (* must contain at least L1 callee defs, but no other requirements *)
      (skips: FunctionInfo.skip_info)
      (prog_info: ProgramInfo.prog_info)
      (l1_infos: FunctionInfo.function_info Symtab.table)
      (L2_opt: FunctionInfo.stage)
      (trace_opt: bool)
      (l2_function_name: string -> string)
      (f_name: string)
      : AutoCorresUtil.convert_result = let
  val (l1_call_info, l1_infos) = FunctionInfo.calc_call_graph l1_infos;

  val f_info = Utils.the' ("L2 conversion missing info for " ^ f_name)
                          (Symtab.lookup l1_infos f_name);
  val callee_names = FunctionInfo.all_callees f_info;
  val _ = filter (fn f => not (is_some (Symtab.lookup l1_infos f))) (Symset.dest callee_names)
          |> (fn bad => if null bad then () else
                          error ("L2 conversion missing callees for " ^ f_name ^ ": " ^ commas bad));

  val f_args = map (apfst (ProgramInfo.demangle_name prog_info)) (FunctionInfo.get_plain_args f_info);
  val (arg_frees, lthy') = Utils.fix_variant_frees f_args lthy;
  val fn_ptr_infos = mk_fn_ptr_infos lthy prog_info arg_frees f_info

  val rec_clique = FunctionInfo.get_recursive_clique f_info

  (* Add callee assumptions. Note that our define code has to use the same assumption order. *)
  val (lthy'', callee_terms) =
    AutoCorresUtil.assume_called_functions_corres lthy' (map (apsnd l2_fn_ptr) (fn_ptr_infos))
      rec_clique
      (get_expected_l2_fn_type prog_info fn_ptr_infos l1_infos)
      (get_l2_corres_prop skips prog_info fn_ptr_infos l1_infos)
      (get_expected_l2_fn_args lthy prog_info fn_ptr_infos l1_infos)
      l2_function_name;

  (* Fix argument variables.
   * We do this after fixing the callees, because there is still some broken code
   * (e.g. in define_funcs) that requires callee var to exactly match the
   * names generated by l2_function_name. *)


  val f_l1_def = FunctionInfo.get_definition f_info
  val thm =
      if FunctionInfo.get_is_simpl_wrapper f_info
      then mk_l2corres_call_simpl_thm prog_info l1_infos fn_ptr_infos lthy'' f_name arg_frees
      else get_l2corres_thm lthy'' skips prog_info l1_infos fn_ptr_infos l1_call_info L2_opt trace_opt f_name
             (Symtab.make callee_terms) arg_frees
             (FunctionInfo.get_const f_info)
             f_l1_def;

  val f_body = dest_L2corres_term_abs (HOLogic.dest_Trueprop (Thm.concl_of thm));
  (* Get actual recursive callees *)
  val rec_callees = AutoCorresUtil.get_rec_callees callee_terms f_body;

  (* Return the constants that we fixed. This will be used to process the returned body. *)
  val callee_consts =
        callee_terms |> map (fn (callee, (const, _)) => (callee, const)) |> Symtab.make;
  in
    { body = f_body,
      proof = hd (Proof_Context.export lthy'' lthy [thm]),
      rec_callees = rec_callees,
      callee_consts = callee_consts,
      arg_frees =  map dest_Free arg_frees
    }
  end


(* Define a previously-converted function (or recursive function group).
 * lthy must include all definitions from l2_callees. *)
fun define
      (skips: FunctionInfo.skip_info)
      (prog_info: ProgramInfo.prog_info)
      (l2_function_name: string -> string)
      (funcs: AutoCorresUtil.convert_result Symtab.table)
      (lthy: local_theory)
      : local_theory =
  let
    val l1_infos = AutoCorresData.get_default_phase_info (Context.Proof lthy) (ProgramInfo.get_prog_name prog_info) FunctionInfo.L1

    (* fixme: the abstract_fn_body step should be moved into define_funcs *)
    val funcs' = Symtab.dest funcs |>
          map (fn result as (name, {proof, arg_frees, ...}) =>
                     (name, (AutoCorresUtil.abstract_fn_body l1_infos result,
                             proof, arg_frees)));
    val clique = map fst funcs'
    val (new_thms, lthy) =
          AutoCorresUtil.define_funcs
              skips
              FunctionInfo.L2 prog_info I {concealed_named_theorems=false} l2_function_name
              (get_expected_l2_fn_type prog_info [] l1_infos)
              (get_l2_corres_prop skips prog_info [] l1_infos)
              (get_expected_l2_fn_args lthy prog_info [] l1_infos)
              funcs'
              lthy;

  in lthy end;

fun translate
      (skips: FunctionInfo.skip_info)
      (base_locale_opt: string option)
      (prog_info: ProgramInfo.prog_info)
      (L2_opt: FunctionInfo.stage)
      (trace_opt: bool)
      (parallel: bool)
      (cliques: string list list)
      (lthy: local_theory)
      :  string list list * local_theory =
  let
    val phase = FunctionInfo.L2
    val l2_function_name = ProgramInfo.get_mk_fun_name prog_info phase
    fun define_worker lthy f_convs =
          define skips prog_info (l2_function_name "") f_convs lthy;
  in
    lthy |>
      AutoCorresUtil.convert_and_define_cliques skips base_locale_opt prog_info
        phase parallel
        (fn lthy => fn l1_infos => convert lthy skips prog_info l1_infos L2_opt trace_opt (l2_function_name ""))
        define_worker cliques
  end

end
