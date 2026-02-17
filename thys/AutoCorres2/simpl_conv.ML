(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Automatically convert SIMPL code fragments into a monadic form, with proofs
 * of correspondence between the two.
 *
 * The main interface to this module is translate (and helper functions
 * convert and define). See AutoCorresUtil for a conceptual overview.
 *)
structure SimplConv =
struct

(* Convenience shortcuts. *)
val warning = Utils.ac_warning
val apply_tac = Utils.apply_tac
val the' = Utils.the'
val timeit_msg = Utils.timeit_msg
val verbose_msg = Utils.verbose_msg

exception FunctionNotFound of string

val simpl_conv_ss = AUTOCORRES_SIMPSET

(*
 * Given a function constant name such as "Blah.foo_'proc", guess the underlying
 * function name "foo".
 *)
fun guess_function_name const_name =
  const_name |> Long_Name.base_name |> Hoare.chopsfx Hoare.proc_deco

(*
 * Extract the L1 monadic term out of a L1corres constant.
 *)
fun get_L1corres_monad @{term_pat "L1corres _ _ ?l1_monad _"} = l1_monad
  | get_L1corres_monad t = raise TERM ("get_L1corres_monad", [t])

(*
 * Generate a SIMPL term that calls the given function.
 *
 * For instance, we might return:
 *
 *   "Call foo_'proc"
 *)
fun mk_SIMPL_call_term prog_info target_fn =
  \<^instantiate>\<open>'s = \<open>ProgramInfo.get_state_type prog_info\<close> and proc = \<open>FunctionInfo.get_const target_fn\<close> 
    in term \<open>Call proc  :: ('s, unit ptr, strictc_errortype) com\<close>\<close>

(*
 * Construct a correspondence lemma between a given monadic term and a SIMPL fragment.
 *
 * The term is of the form:
 *
 *    L1corres check_termination \<Gamma> monad simpl
 *)
fun mk_L1corres_prop ctxt prog_info check_termination monad_term simpl_term =
 \<^infer_instantiate>\<open>ct = \<open>Utils.mk_bool check_termination\<close> and gamma = \<open>ProgramInfo.get_gamma prog_info\<close> and 
        monad = monad_term and simpl = simpl_term in term \<open>L1corres ct gamma monad simpl\<close>\<close> ctxt

(*
 * Construct a prop claiming that the given term is equivalent to
 * a call to the given SIMPL function:
 *
 *    L1corres ct \<Gamma> <term> (Call foo_'proc)
 *
 *)
fun mk_L1corres_call_prop ctxt prog_info check_termination target_fn term =
    mk_L1corres_prop ctxt prog_info check_termination term
      (mk_SIMPL_call_term prog_info target_fn)
    |> HOLogic.mk_Trueprop

fun is_h_val_fun_ptr thy = Match_Cterm.switch [ 
 @{match "\<lambda>s. h_val (?h s) (?p s)"} thy #> (fn _  => true),
 fn _ => false]

fun dest_init ctxt (t as (Abs (s, T, upds))) =
 let
   val ((s, T), bdy) = Term.dest_abs_global t
   fun value_from_const_upd (t as (Abs (v, vT, const))) = 
     if Term.is_dependent const then 
       error ("dest_init: " ^ Syntax.string_of_term ctxt t) 
     else Term.absfree (s, T) const 
   fun dest bdy = 
     case HPInter.dest_local_var_update bdy of
      SOME (n, T, SOME upd, SOME s) => ((n, T, value_from_const_upd upd):: dest s)
    | SOME (n, T, SOME upd, NONE) => [(n, T, value_from_const_upd upd)]
    | _  => []

 in
   dest bdy
 end
   | dest_init ctxt t = error ("dest_init: unexpected term: " ^ Syntax.string_of_term ctxt t)


fun mk_guard_fun _ [] = error ("mk_guard: empty")
  | mk_guard_fun _ [g] = g
  | mk_guard_fun ctxt (g::gs) = \<^infer_instantiate>\<open>g = g and gs = \<open>mk_guard_fun ctxt gs\<close>
                 in term \<open>\<lambda>s. (g s) \<and> (gs s)\<close>\<close> ctxt

val d1 = Unsynchronized.ref (false)
fun dprint_tac d ctxt msg = if d then print_tac ctxt msg else all_tac 
(*
 * Convert a SIMPL fragment into a monadic term.
 *
 * We return the monadic version of the input fragment and a tactic
 * to prove correspondence.
 *)
fun simpl_conv'
    (fn_name: string)
    (prog_info : ProgramInfo.prog_info)
    (simpl_defs : FunctionInfo.function_info Symtab.table)
    (ctxt : Proof.context)
    (callee_terms : (term * thm list) Symtab.table)
    (check_termination: bool)
    (simpl_term : term) =
  let
    fun prove_term subterms base_thm result_term =
      let
        val subterms' = map (simpl_conv' fn_name prog_info simpl_defs ctxt callee_terms check_termination) subterms;
        val converted_terms = map fst subterms';
        val subproofs = map snd subterms';
        val new_term = (result_term converted_terms);
      in
        (new_term, (resolve_tac ctxt [base_thm] 1) THEN dprint_tac (!d1) ctxt "prove_term" THEN (EVERY subproofs))
      end

    val state_type = ProgramInfo.get_state_type prog_info
    (* Construct a "L1 monad" term with the given arguments applied to it. *)
    fun mk_l1 (Const (a, _)) args =
      Term.betapplys (Const (a, map fastype_of args
          ---> AutoCorresData.mk_l1monadT state_type), args)
    
    val Gamma = ProgramInfo.get_gamma prog_info

    (* Convert a set construct into a predicate construct. *)
    fun set_to_pred t =
      (Const (@{const_name L1_set_to_pred},
          fastype_of t --> (HOLogic.dest_setT (fastype_of t) --> @{typ bool})) $ t)

    (* Convert a rel construct into a function construct. *)
    fun mk_rel_to_fun t =
      let val (aT, bT) = HOLogic.dest_prodT (HOLogic.dest_setT (fastype_of t))
      in (Const (@{const_name L1_rel_to_fun},
              fastype_of t --> aT --> HOLogic.mk_setT (HOLogic.mk_prodT (HOLogic.unitT, bT)))) $ t
      end

    val indirect_callee_thms = AutoCorresData.get_default_phase_info (Context.Proof ctxt) (ProgramInfo.get_prog_name prog_info) FunctionInfo.L1
         |> Symtab.dest |> map_filter (FunctionInfo.get_proper_corres_thm o snd)
    val callee_thms = callee_terms |> Symtab.dest |> map (#2 o #2) |> flat
  in
    (case simpl_term of
        (*
         * Various easy cases of SIMPL to monadic conversion.
         *)

        (Const (@{const_name Skip}, _)) =>
          prove_term [] @{thm L1corres_skip}
            (fn _ => mk_l1 @{term "L1_skip"} [])

      | (Const (@{const_name Seq}, _) $ left $ right) =>
          prove_term [left, right] @{thm L1corres_seq}
            (fn [l, r] => mk_l1 @{term "L1_seq"} [l, r])

      | (Const (@{const_name Basic}, _) $ m) =>
          prove_term [] @{thm L1corres_modify}
            (fn _ => mk_l1 @{term "L1_modify"} [m])

      | (Const (@{const_name Cond}, _) $ c $ left $ right) =>
          prove_term [left, right] @{thm L1corres_condition}
            (fn [l, r] => mk_l1 @{term "L1_condition"} [set_to_pred c, l, r])

      | (Const (@{const_name Catch}, _) $ left $ right) =>
          prove_term [left, right] @{thm L1corres_catch}
            (fn [l, r] => mk_l1 @{term "L1_catch"} [l, r])

      | (Const (@{const_name While}, _) $ c $ body) =>
          prove_term [body] @{thm L1corres_while}
            (fn [body] => mk_l1 @{term "L1_while"} [set_to_pred c, body])

      | (Const (@{const_name Throw}, _)) =>
          prove_term [] @{thm L1corres_throw}
            (fn _ => mk_l1 @{term "L1_throw"} [])

      | (Const (@{const_name Guard}, _) $ _ $ c $ body) =>
          prove_term [body] @{thm L1corres_guard}
            (fn [body] => mk_l1 @{term "L1_seq"} [mk_l1 @{term "L1_guard"} [set_to_pred c], body])

      | @{term_pat "lvar_nondet_init ?upd"} =>
          prove_term [] @{thm L1corres_init}
            (fn _ => mk_l1 @{term "L1_init"} [upd])

      | (Const (@{const_name com.Spec}, _) $ s) =>
          prove_term [] @{thm L1corres_spec}
            (fn _ => mk_l1 @{term "L1_spec"} [s])

      | (Const (@{const_name guarded_spec_body}, _) $ @{const AssumeError} $ s) =>
          prove_term [] @{thm L1corres_assume}
            (fn _ => mk_l1 @{term "L1_assume"} [mk_rel_to_fun s])

      | (Const (@{const_name guarded_spec_body}, _) $ _ $ s) =>
          prove_term [] @{thm L1corres_guarded_spec}
            (fn _ => mk_l1 @{term "L1_spec"} [s])

      | (Const (@{const_name spec_pre_post}, _) $ @{const ImpossibleSpec} $ @{const AssumeError} $ P $ R) =>
         let
           val l1 = \<^infer_instantiate>\<open>P = P and R = R in term \<open>(L1_seq (L1_guard (\<lambda>s. s \<in> P)) ((L1_assume (L1_rel_to_fun R)))) \<close>\<close> ctxt
         in
           prove_term [] @{thm L1corres_assume_spec_pre_post}
             (fn _ => l1)
         end

      (*
       * "call": This is primarily what is output by the C parser. We
       * accept input terms of the form:
       *
       *     "call <argument_setup> <proc_to_call> <locals_reset> (%_ s. Basic (<store return value> s))".
       *
       * In particular, the last argument needs to be of precisely the
       * form above. SIMPL, in theory, supports complex expressions in
       * the last argument.  In practice, the C parser only outputs
       * the form above, and supporting more would be a pain.
       *)
      | (Const (@{const_name call_exn}, _) $ init $ (fn_const as Const (b, _)) $ c1 $ c2 $ (Abs (_, _, Abs (_, _, (Const (@{const_name Basic}, _) $ d))))) =>
          let
            val target_fn_name = guess_function_name b
          in
            case Symtab.lookup callee_terms target_fn_name of
                NONE =>
                (* If no proof of our callee could be found, we emit a call to
                 * "fail". This may happen for functions without bodies. *)
                let
                  val _ = warning ("Function '" ^ target_fn_name ^ "' contains no body. "
                      ^ "Replacing the function call with a \"fail\" command.")
                in
                  prove_term [] @{thm L1corres_fail} (fn _ => mk_l1 @{term "L1_fail"} [])
                end
              | SOME (term, [thm]) =>
                  let 
                    val (call_trm, tac) = (mk_l1 @{term "L1_call"} [init, term, c1, c2, absdummy state_type d],
                          resolve_tac ctxt @{thms L1corres_call} 1
                          THEN resolve_tac ctxt [thm] 1 THEN dprint_tac (!d1) ctxt "L1_call")
                  in
                     (call_trm, tac)
                  end
          end

      | dyncom as (Const (@{const_name dynCall_exn}, _) $ (Const (@{const_name UndefinedFunction}, _) $ dom) $ g $ init $ proc $ return $ result_exn $ (Abs (_, sT, Abs (_, _, (Const (@{const_name Basic}, _) $ result))))) => 
          let
            val callee_ptrs = dom |> HOLogic.dest_set
            val callee_infos = callee_ptrs |> map (fn ptr => (ptr , the (Symtab.lookup callee_terms (Term.term_name ptr))))
            val T = \<^Type>\<open>spec_monad \<open>@{typ "unit option"}\<close> \<open>@{typ unit}\<close> sT\<close>
            val assoc = callee_infos |> map (fn (p, (v, _)) => HOLogic.mk_prod (p,v)) |> HOLogic.mk_list \<^Type>\<open>prod \<open>@{typ "unit ptr"}\<close> T\<close>
            val g' = \<^infer_instantiate>\<open>g = g in term \<open>L1_set_to_pred g\<close>\<close> ctxt
            val ghost_ss = (put_simpset HOL_basic_ss ctxt) addsimps 
               @{thms list.map comp_apply snd_conv L1_set_to_pred_def in_set_to_pred 
                 Int_iff mem_Collect_eq} 
            val eq = Simplifier.rewrite ghost_ss (Thm.cterm_of ctxt g')
            fun remove_fnptr_guard @{term_pat "c_fnptr_guard ?x"} = SOME \<^term>\<open>True\<close>
              | remove_fnptr_guard _ = NONE 
            val g'0 =  eq |> Thm.rhs_of |> Thm.term_of 
            val g' = g'0
              |> Pattern.rewrite_term (Proof_Context.theory_of ctxt) [] [remove_fnptr_guard] 

            val l1 = mk_l1 @{const "L1_dyn_call_map_of_default"('s)}  [g', init, proc, assoc, return, result_exn, absdummy state_type result]

            val rule = @{thm L1corres_dyn_call_map_of_default_conseq}
            val simp_ctxt = Splitter.add_split @{thm if_split_asm} ctxt
            val fun_ptr_simps = Named_Bindings.get_thms ctxt @{named_bindings fun_ptr_simps}
            val fun_ptr_guards = Named_Bindings.get_thms ctxt @{named_bindings fun_ptr_guards}
            fun solve_guards ctxt = asm_full_simp_tac ctxt 
              THEN_ALL_NEW 
              (REPEAT_ALL_NEW (eresolve_tac ctxt @{thms disjE} THEN_ALL_NEW asm_full_simp_tac ctxt))
            val callee_thms = maps (#2 o #2) callee_infos
            val dyncall_tac = SOLVES_debug ctxt ("L1 dyn_call in " ^ fn_name ) (
             EVERY [
              resolve_tac ctxt [rule] 1,
              dprint_tac (!d1) ctxt ("L1 dyn_call after resolve in " ^ fn_name),
              solve_guards (simp_ctxt addsimps (fun_ptr_simps @ fun_ptr_guards)) 1,
              dprint_tac (!d1) ctxt ("L1 dyn_call after simp (1) in " ^ fn_name),
              asm_full_simp_tac (simp_ctxt addsimps callee_thms) 1,
              dprint_tac (!d1) ctxt ("L1 dyn_call after simp (2) in " ^ fn_name),
              dprint_tac (!d1) ctxt ("L1 dyn_call in " ^ fn_name)])

          in (l1, dyncall_tac) end
       | exec_spec_monad as (Const (@{const_name exec_spec_monad}, _) $ get_x $ upd_x $ st $ args $ f $ res) => 
           let 
             val l1 = mk_l1 @{const "L1_exec_spec_monad"('s,'t,'b,'a)} [upd_x, st, args, f, res]
             val rule = @{thm L1corres_exec_spec_monad'}
           in (l1, match_tac ctxt [rule ] 1) end
       | other => 
          let
            val {n, init, c, ...} = With_Fresh_Stack_Ptr.match ctxt other
            val Abs (p, pT, _) = c
            val sT = fastype_of init |> domain_type
            val ((p, pT), bdy) = Term.dest_abs_fresh p c
            val ([p], ctxt') = Utils.gen_fix_variant_frees true [(p, pT)] ctxt
            val (l1_bdy, bdy_tac) = simpl_conv' fn_name prog_info simpl_defs ctxt' callee_terms check_termination bdy
            val l1_bdy = Term.absfree (dest_Free p) l1_bdy
            val with_fresh_stack_ptr = with_fresh_stack_ptr.term ctxt sT
            val l1 = \<^infer_instantiate>\<open>w = with_fresh_stack_ptr and init = init and bdy = l1_bdy and n = n
                  in term \<open>w n init bdy\<close>\<close> ctxt
            val rules = Named_Theorems.get ctxt @{named_theorems L1corres_with_fresh_stack_ptr}
          in 
            (l1, resolve_tac ctxt rules 1 THEN dprint_tac (!d1) ctxt "other" THEN bdy_tac)
          end handle Match => Utils.invalid_term' ctxt "a SIMPL term" other)
       



  end

(* Perform post-processing on a theorem. *)
fun cleanup_thm ctxt L1_opt trace_opt prog_info fn_name thm =
let
  (* Conversion combinator to apply a conversion only to the L1 subterm of a
   * L1corres term. *)
  fun l1conv conv = (Conv.arg_conv (Utils.nth_arg_conv 3 conv))

  (* Conversion to simplify guards. *)
  fun guard_ctxt ctxt = ctxt
    |> put_simpset simpl_conv_ss
    |> fold Simplifier.add_simp @{thms L1_functions.L1_dyn_call_def L1_dyn_call_map_of_default_def pred_conj_def}
    |> Simplifier.del_proc Record.upd_simproc

  fun guard_conv' ctxt c =
    case (Thm.term_of c) of
      (Const (@{const_name "L1_guard"}, _) $ _) => Simplifier.asm_full_rewrite (guard_ctxt ctxt) c
    | (Const (@{const_name "L1_functions.L1_dyn_call"}, _) $ P $ g $ scope_setup $ dest $ scope_teardown_norm $ scope_teardown_exn $ f)
        => Simplifier.asm_full_rewrite (guard_ctxt ctxt) c
    | (Const (@{const_name "L1_dyn_call_map_of_default"}, _) $ g $ scope_setup $ dest $ ps $ scope_teardown_norm $ scope_teardown_exn $ f)
        => Simplifier.asm_full_rewrite (guard_ctxt ctxt) c
    | _ =>
        Conv.all_conv c
  val guard_conv = Conv.top_conv (guard_conv') ctxt
  val simp_ctxt = put_simpset HOL_basic_ss ctxt addsimps @{thms scast_numerals}
  (* Apply all the conversions on the generated term. *)
  val _ = verbose_msg 1 ctxt (fn _ => "L1 (raw) - " ^ fn_name ^ ": " ^ Thm.string_of_thm ctxt thm);
  val _ = ctxt |> AutoCorresTrace.put_trace_info fn_name FunctionInfo.L1 FunctionInfo.RAW;
  val thm = timeit_msg 1 ctxt (fn _ => "L1 (guard-opt) - " ^ fn_name)  (fn _ => 
    AutoCorresTrace.fconv_rule_maybe_traced ctxt (l1conv guard_conv) thm trace_opt); (* fixme: double timing *)

  val _ = verbose_msg 1 ctxt (fn _ => "L1 (guard-opt) - " ^ fn_name ^ ": " ^ Thm.string_of_thm ctxt thm);
  val _ = ctxt |> AutoCorresTrace.put_trace_info_stage FunctionInfo.PEEP;
  val thm = timeit_msg 1 ctxt (fn _ => "L1 (peephole-opt) - " ^ fn_name)  (fn _ =>
    AutoCorresTrace.fconv_rule_maybe_traced ctxt
      (l1conv (Simplifier.rewrite (simp_ctxt addsimps
                     (if not (L1_opt = FunctionInfo.RAW) then Utils.get_rules ctxt @{named_theorems L1opt} else []))))
      thm trace_opt);
  val _ = verbose_msg 1 ctxt (fn _ => "L1 (peephole-opt) - " ^ fn_name ^ ": " ^ Thm.string_of_thm ctxt thm);

in
  thm  
end

(*
 * Get theorems about a SIMPL body in a format convenient to reason about.
 *
 * In particular, we unfold parts of SIMPL where we would prefer to reason
 * about raw definitions instead of more abstract constructs generated
 * by the C parser.
 *)
fun get_simpl_body ctxt simpl_defs fn_name =
let
  (* Find the definition of the given function. *)
  val info = Utils.the' ("SimplConv.get_simpl_body: no such function: " ^ fn_name)
                                 (Symtab.lookup simpl_defs fn_name)
  val simpl_thm = FunctionInfo.get_definition info 
      handle ERROR _ => raise FunctionNotFound fn_name;

  (* Unfold terms in the body which we don't want to deal with. *)
  val unfolded_simpl_thm =
      Conv.fconv_rule (Utils.rhs_conv
          (Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps
             (Utils.get_rules ctxt @{named_theorems L1unfold}))))
          simpl_thm
  val unfolded_simpl_term = Thm.concl_of unfolded_simpl_thm |> Utils.rhs_of;
  (*
   * Get the implementation definition for this function. These rules are of
   * the form "Gamma foo_'proc = Some foo_body".
   *)
  val impl_thm =
    if FunctionInfo.get_invented_body info then NONE
    else 
      Proof_Context.get_thm ctxt (fn_name ^ "_impl")
      |> Local_Defs.unfold ctxt [unfolded_simpl_thm]
      |> SOME
      handle (ERROR _) => NONE
in
  (unfolded_simpl_term, unfolded_simpl_thm, impl_thm)
end

fun get_l1corres_thm prog_info simpl_defs
                     check_termination ctxt L1_opt trace_opt
                     fn_name callee_terms = 
  let
    val ctxt = ctxt delsimps @{thms map_of_default.simps} 
      |> HPInter.enter_scope (ProgramInfo.get_prog_name prog_info) fn_name
    val fn_def = Utils.the' ("SimplConv.get_l1corres_thm: no such function: " ^ fn_name)
                   (Symtab.lookup simpl_defs fn_name);
    val (simpl_term, simpl_thm, impl_thm) = get_simpl_body ctxt simpl_defs fn_name
    (*
     * Do the conversion.  We receive a new monadic version of the SIMPL
     * term and a tactic for proving correspondence.
     *)
    val options = ProgramInfo.get_fun_options prog_info fn_name
    val _ = is_some impl_thm 
      orelse ProgramInfo.get_no_body options 
      orelse error ("No implementation or specification for function prototype: " ^ fn_name ^ 
        ". \n Use option 'no_body' or provide a specification by overloaded definition of: " ^ (fn_name ^ "_body")) 
    val (monad, tactic) = simpl_conv' fn_name prog_info simpl_defs ctxt callee_terms check_termination simpl_term
   
    (*
     * Return a new theorem of correspondence between the original
     * SIMPL body (with folded constants) and the output monad term.
     *)
  in
    mk_L1corres_call_prop ctxt prog_info check_termination fn_def monad
    |> Thm.cterm_of ctxt
    |> Goal.init
    |> (case impl_thm of
            NONE     => if null (FunctionInfo.get_returns fn_def) 
                        then apply_tac ctxt ("unfold SIMPL body (1): "  ^ fn_name) (resolve_tac ctxt @{thms L1corres_undefined_call} 1)
                        else apply_tac ctxt ("unfold SIMPL body (2): "  ^ fn_name) (resolve_tac ctxt @{thms L1corres_init_return_undefined_call} 1)
          | SOME def => apply_tac ctxt ("unfold SIMPL body (3): " ^ fn_name) (resolve_tac ctxt @{thms L1corres_Call} 1 THEN
                                                       resolve_tac ctxt [def] 1)
                        #> apply_tac ctxt ("solve L1corres: " ^ fn_name) tactic)
    |> Goal.finish ctxt
    (* Apply simplifications to the L1 term. *)
    |> cleanup_thm ctxt L1_opt trace_opt prog_info fn_name
  end

fun get_body_of_l1corres_thm thm =
   (* Extract the monad from the thm. *)
   Thm.concl_of thm
   |> HOLogic.dest_Trueprop
   |> get_L1corres_monad

(* For functions that are not translated, just generate a trivial wrapper. *)
fun mk_l1corres_call_simpl_thm check_termination ctxt simpl_def = let
    val const = FunctionInfo.get_const simpl_def
    val impl_thm = Proof_Context.get_thm ctxt (FunctionInfo.get_name simpl_def ^ "_impl")
    val gamma = safe_mk_meta_eq impl_thm |> Thm.concl_of |> Logic.dest_equals
        |> fst |> (fn (f $ _) => f | t => raise TERM ("gamma", [t]))
    val thm = Utils.named_cterm_instantiate ctxt
        [("ct", Thm.cterm_of ctxt (Utils.mk_bool check_termination)),
         ("proc", Thm.cterm_of ctxt const),
         ("Gamma", Thm.cterm_of ctxt gamma)]
        @{thm L1corres_call_simpl}
  in thm end

(* All L1 functions have the same signature: measure \<Rightarrow> L1_monad *)
fun l1_fn_type prog_info = AutoCorresData.mk_l1monadT (ProgramInfo.get_state_type prog_info);

(* L1corres for f's callees. *)
fun get_l1_fn_assumption prog_info check_termination simpl_infos ctxt fn_name free =
    (mk_L1corres_call_prop ctxt prog_info check_termination
        (Utils.the' ("SimplConv: missing callee def for " ^ fn_name)
                    (Symtab.lookup simpl_infos fn_name)) free, 
     []);

fun get_l1_corres_prop prog_info check_termination simpl_infos ctxt assume fn_name free args =
  let
    val concl = get_l1_fn_assumption prog_info check_termination simpl_infos ctxt fn_name free 
  in
    (concl, NONE)
  end

(*
 * Convert a single function. Returns a thm that looks like
 *   \<lbrakk> L1corres ?callee1 (Call callee1_'proc); ... \<rbrakk> \<Longrightarrow>
 *   L1corres (conversion result...) (Call f_'proc)
 * i.e. with assumptions for called functions, which are parameterised as Vars.
 *)
fun convert
      (lthy: local_theory)
      (prog_info: ProgramInfo.prog_info)
      (simpl_infos: FunctionInfo.function_info Symtab.table)
      (check_termination: bool)
      (L1_opt: FunctionInfo.stage)
      (trace_opt: bool)
      (l1_function_name: string -> string)
      (f_name: string)
      : AutoCorresUtil.convert_result =
let
  val f_info = Utils.the' ("SimplConv: missing SIMPL def for " ^ f_name) (Symtab.lookup simpl_infos f_name);
  (* Fix measure variable. *)


  val callees = FunctionInfo.get_callees f_info
  val rec_clique = FunctionInfo.get_recursive_clique f_info
  val l1_infos = AutoCorresData.get_function_info (Context.Proof lthy) (ProgramInfo.get_prog_name prog_info) FunctionInfo.L1

  (* Add callee assumptions. Note that our define code has to use the same assumption order. *)
  val (lthy', callee_terms) =
    AutoCorresUtil.assume_called_functions_corres lthy
      rec_clique
      (K (l1_fn_type prog_info))
      (get_l1_corres_prop prog_info check_termination simpl_infos)
      (K [])    
      l1_function_name;

  val more_callee_terms = callees |> Symset.dest |> map (fn name => 
    let
      val info = the (l1_infos name)
    in
      (name, (FunctionInfo.get_const info, [FunctionInfo.get_corres_thm info]))
    end)

  val thm =
      if FunctionInfo.get_is_simpl_wrapper f_info
      then mk_l1corres_call_simpl_thm check_termination lthy' f_info
      else get_l1corres_thm prog_info simpl_infos check_termination lthy'
                            L1_opt trace_opt f_name (Symtab.make (callee_terms @ more_callee_terms));

  val f_body = get_L1corres_monad (HOLogic.dest_Trueprop (Thm.concl_of thm));
  (* Get actual recursive callees *)
  val rec_callees = AutoCorresUtil.get_rec_callees callee_terms f_body;

  (* Return the constants that we fixed. This will be used to process the returned body. *)
  val callee_consts =
        callee_terms |> map (fn (callee, (const, _)) => (callee, const)) |> Symtab.make;

  in
    { body = f_body,
      (* Expose callee assumptions and generalizes callee vars *)
      proof = hd (Proof_Context.export lthy' lthy [thm]),
      rec_callees = rec_callees,
      callee_consts = callee_consts,
      arg_frees = []
    }
  end

fun option_fold f NONE x = (NONE, x)
  | option_fold f (SOME v) x = let val (res, y) = f v x in (SOME res, y) end 


(* Define a previously-converted function (or recursive function group).
 * lthy must include all definitions from l1_callees.
 * simpl_defs must include current function set and its immediate callees.  *)
fun define
      (skips: FunctionInfo.skip_info)
      (prog_info: ProgramInfo.prog_info)
      (check_termination: bool)
      (l1_function_name: string -> string -> string)
      (lthy: local_theory)
      (funcs: AutoCorresUtil.convert_result Symtab.table)
      : local_theory = 
let
  val recursive = Symtab.dest funcs |> map (#rec_callees o snd) |> exists (not o Symset.is_empty)
  val simpl_infos = AutoCorresData.get_default_phase_info (Context.Proof lthy) (ProgramInfo.get_prog_name prog_info) FunctionInfo.CP

  val funcs' = Symtab.dest funcs |>
        map (fn result as (name, {proof, arg_frees, ...}) =>
                   (name, (AutoCorresUtil.abstract_fn_body simpl_infos result, proof, arg_frees)))
        
  val clique = map fst funcs'

  val (new_funs, lthy) =
        AutoCorresUtil.define_funcs
            skips
            FunctionInfo.L1 prog_info I {concealed_named_theorems=false} (l1_function_name "")
            (K (l1_fn_type prog_info))
            (get_l1_corres_prop prog_info check_termination simpl_infos)
            (K [])
            funcs'
            lthy;


  (* Rewrite exceptions. *)

  fun make_no_throw_thms ctxt fun_names fun_consts fun_defs =
    let 
      fun no_throw f = \<^infer_instantiate>\<open>f = f in prop \<open>no_throw (\<lambda>_. True) f\<close>\<close> ctxt

      val goals = map no_throw fun_consts

      val thms = (* no recursion is handled. This is postponed to TS phase *)
         Goal.prove_common ctxt NONE [] [] goals (fn {context, ...} => 
            DETERM (
             EVERY1 (map (fn body_def => SOLVED' (
               EqSubst.eqsubst_tac context [1] [body_def] THEN'
               simp_tac ctxt (* this should be except_rewrite_cache_ctxt from the previous body simplification *)  
               ))
            fun_defs)))
    in
      thms
    end
    handle ERROR _ => (warning ("could not prove no_throws for " ^ @{make_string} fun_names); [])

  val lthy = lthy |> AutoCorresData.in_theory' (fn lthy =>
    let
      (* In case of of a recursive function group, funcs and thus fun_names will only contain those
       * (mutually) recursive functions. We can thus consider all the callees of every function together. 
       * In case of nonrecursive functions, funcs and thus f_names might contain
       * independent functions according to the topological call order. For them we have to be selective 
       * about the actual callees to decide if we can proof a no_throws theorem. 
       *)
      fun get_callees n = Symtab.lookup simpl_infos n |> Option.map (Symset.dest o FunctionInfo.get_callees) |> these
      fun no_throw_callees n = get_callees n 
        |> map (the_list o AutoCorresData.get_function_info (Context.Proof lthy) (ProgramInfo.get_prog_name prog_info) FunctionInfo.L1)
        |> flat
        |> map FunctionInfo.get_no_throw_thm

      val maybe_no_throw_callees = map no_throw_callees new_funs |> flat 
      fun get_info lthy = the o AutoCorresData.get_function_info (Context.Proof lthy) (ProgramInfo.get_prog_name prog_info) (FunctionInfo.L1)
      val fun_consts = map (FunctionInfo.get_const o get_info lthy) new_funs
      val fun_defs = map (FunctionInfo.get_definition o get_info lthy) new_funs 

      val some_no_throw_callees = map_filter I maybe_no_throw_callees 
      val no_throw_thms = some_no_throw_callees 
      val cache_lthy = ExceptionRewrite.except_rewrite_cache_ctxt lthy no_throw_thms (* creates a fresh cache *)
      fun simplify_bdy ctxt = Conv.fconv_rule (Conv.arg_conv (ExceptionRewrite.except_rewrite_cache_conv ctxt))

      val filename = ProgramInfo.get_prog_name prog_info
      val phase = FunctionInfo.L1
      val lthy = cache_lthy |> fold (fn (f_name, (const, def)) => fn lthy  =>
        let
          val def_eq = def
          val opt_eq = timeit_msg 1 lthy (fn _ => "L1 (exn-opt) - " ^ f_name)  (fn _ => 
            simplify_bdy lthy def_eq)
          val _ = verbose_msg 1 lthy (fn _ => "L1 (exn-opt) - " ^ f_name ^ ": " ^ Thm.string_of_thm lthy opt_eq);
          val (def', lthy) = lthy 
            |> Utils.define_lemma (Binding.name (l1_function_name "opt_" f_name ^ "_def")) [AutoCorresData.define_function_attribute {concealed_named_theorems=false} filename skips phase f_name] opt_eq
          val no_throw_thm = 
            if recursive then ExceptionRewrite.get_callee_thm no_throw_thms const
            else if List.all is_some (no_throw_callees f_name) 
                 then try hd (make_no_throw_thms lthy [f_name] [const] [opt_eq])
                 else NONE
          val no_throw_attr = map (Attrib.attribute lthy) @{attributes [no_throw]}
          val (no_throw_thm, lthy) = lthy |> option_fold
             (Utils.define_lemma (Binding.name (l1_function_name "" f_name ^ "_no_throw")) 
               ([AutoCorresData.no_throw_thm_attribute filename skips phase f_name] @ no_throw_attr)) no_throw_thm
        in
          lthy  
        end) (new_funs ~~ (fun_consts ~~ fun_defs))   
    in
       lthy
    end)
  in lthy end;

(*
 * Top level translation from SIMPL to a monadic spec.
 *
 * We accept a filename (the same filename passed to the C parser; the
 * parser stashes away important information using this filename as the
 * key) and a local theory.
 *
 * We define a number of new functions (the converted monadic
 * specifications of the SIMPL functions) and theorems (proving
 * correspondence between our generated specs and the original SIMPL
 * code).
 *)
fun translate
      (skips: FunctionInfo.skip_info)
      (base_locale_opt: string option)
      (prog_info: ProgramInfo.prog_info)
      (check_termination: bool)
      (L1_opt: FunctionInfo.stage)
      (trace_opt: bool)
      (parallel: bool)
      (cliques: string list list)
      (lthy: local_theory)
      : string list list * local_theory =
let
  val phase = FunctionInfo.L1
  val l1_function_name = ProgramInfo.get_mk_fun_name prog_info phase
  val (cliques, lthy) = lthy |>
    AutoCorresUtil.convert_and_define_cliques skips base_locale_opt prog_info  
      phase parallel
      (fn lthy => fn simpl_infos =>
                     convert lthy prog_info simpl_infos check_termination
                             L1_opt trace_opt (l1_function_name ""))
      (define skips prog_info check_termination l1_function_name)
      cliques
in
  (cliques, lthy)
end


end
