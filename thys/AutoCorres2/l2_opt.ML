(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
(*
 * Optimise L2 fragments of code by using facts learnt earlier in the fragments
 * to simplify code afterwards.
 *)

structure L2Opt =
struct

(*
 * Map the given simpset to tweak it for L2Opt.
 *
 * If "use_ugly_rules" is enabled, we will use rules that are useful for
 * discharging proofs, but make the output ugly.
 *)
fun map_opt_simpset use_ugly_rules =
    Simplifier.add_cong @{thm if_cong}
    #> Simplifier.add_cong @{thm split_cong}
    #> Simplifier.add_cong @{thm HOL.conj_cong}
    #> (fn ctxt => ctxt addsimps @{thms triv_ex_apply}) (* fixme: should already be handled by HOL.ex_simps?*)
    #> (if use_ugly_rules then
          (fn ctxt => ctxt addsimps [@{thm split_def}])
        else
           I)

fun beta_eta_contraction_rule th =
  Thm.equal_elim (Drule.beta_eta_conversion (Thm.cprop_of th)) th;

fun instantiate_lhs eq_thm ct =
  let
    val lhs = eq_thm |> Thm.cconcl_of |> Thm.dest_equals_lhs
    val insts = Thm.match (lhs, ct)
  in
    Thm.instantiate insts (Thm.rename_boundvars (Thm.term_of lhs) (Thm.term_of ct) eq_thm)
  end

fun inst_norm_lhs eq_thm ct =
  beta_eta_contraction_rule (instantiate_lhs eq_thm ct)

(*
 * A simproc implementing the "L2_marked_gets_bind" rule. The rule, unfortunately, has
 * the ability to cause exponential growth in the spec size in some cases;
 * thus, we can only selectively apply it in cases where this doesn't happen.
 *
 * In particular, we propagate a "gets" into its usage
 *   - if the term getting propagated is small OR,
 *   - if it is used at most once OR,
 *   - if the term is a struct-record-constructor, and the usages are record-selectors
 *     (this captures the prominent C-idiom where a local struct variable is
 *     first declared without initialisation, and then initialised component-wise in subsequent code.
 *
 * Or, if the user asks for "no_opt", we only erase the "gets" if it is never used.
 * (Even with "no optimisation", we still want to get rid of control flow variables
 * emitted by c-parser. Hopefully the user won't mind if their own unused variables
 * also disappear.)
 *)


val is_numeral = is_some o try HOLogic.dest_number;


fun l2_marked_gets_bind_simproc' ctxt ct =
let
  val thy = Proof_Context.theory_of ctxt;

  fun is_simple (Bound _) = true
    | is_simple (Free _) = true
    | is_simple (Const _) = true
    | is_simple \<^Const>\<open>Ptr _ for p\<close> = is_numeral p
    | is_simple t = is_numeral t;

  fun record_constructor_or_update x =
      (case head_of x of
         Const (c,T) =>
           (case snd (strip_type T) of
             Type(r, _) =>
                if RecursiveRecordPackage.is_record thy r
                then if RecursiveRecordPackage.is_constructor thy r c then SOME (r, "")
                     else (case RecursiveRecordPackage.is_update thy r c of
                             SOME f => SOME (r, f)
                           | _ => NONE)
                else NONE
            | _ => NONE)
       | _ => NONE)

  fun is_constructor (_, "") = true
    | is_constructor _ = false

  val opt = AutoCorres_Options.get_unfold_constructor_bind_opt ctxt
in
  case Thm.term_of ct of
    (Const (@{const_name "L2_seq_gets"}, _) $ lhs $ names $ Abs (_, T, rhs)) =>
      let
        fun count_var_usage (a $ b) = count_var_usage a + count_var_usage b
          | count_var_usage (Abs (_, _, x)) = count_var_usage x
          | count_var_usage (Free ("_dummy", _)) = 1
          | count_var_usage _ = 0

        val rhs' = subst_bounds ([Free ("_dummy", T)], rhs)
        val count = count_var_usage rhs'

        fun expand lhs rhs =
          let
            val maybe_record = record_constructor_or_update lhs;
            fun is_matching_selector (record, field) sel =
              RecursiveRecordPackage.is_field thy record sel andalso (field = "" orelse field = sel);
            fun only_selection (Const(sel, _) $ Free ("_dummy", _)) = is_matching_selector (the maybe_record) sel
              | only_selection (a $ b) = only_selection a andalso only_selection b
              | only_selection (Abs (_, _, x)) = only_selection x
              | only_selection (Free ("_dummy", _)) = false
              | only_selection _ = true
          in
            case maybe_record of NONE => false
            | SOME record =>
               if is_constructor record then
                   (opt <> AutoCorres_Options.Never) andalso
                   (opt = AutoCorres_Options.Always orelse
                   (opt = AutoCorres_Options.Selectors andalso only_selection rhs))
               else (* update *)
                 only_selection rhs
          end
      in
        if is_simple lhs orelse count <= 1 orelse expand lhs rhs' then
          SOME @{thm L2_marked_seq_gets_apply}
        else
          NONE
      end
    | _ => NONE
end

fun aconv_diff tm1 tm2 =
  if pointer_eq (tm1, tm2) then []
  else
   case (tm1, tm2) of
     (t1 $ u1, t2 $ u2) => aconv_diff t1 t2 @ aconv_diff u1 u2
   | (Abs (x1, T1, t1), Abs (x2, T2, t2)) =>
       (if T1 = T2 then [] else
        [(Abs (x1, T1, Bound 0), Abs (x2, T2, Bound 0))]) @ aconv_diff t1 t2
   | (a1, a2) => if a1 = a2 then [] else [(a1, a2)]

fun l2_marked_gets_bind_augment_context_simproc' ctxt ct = (
let
  val t = Thm.term_of ct;

  fun prefer_fst (x::xs) (y::ys) = x::prefer_fst xs ys
    | prefer_fst xs [] = xs
    | prefer_fst [] ys = ys

  fun dest_body t =
    let
      val tupleT = domain_type (fastype_of t)
      val Ts = HOLogic.flatten_tupleT tupleT
      val n = length Ts
      val standard_names = map (Tuple_Tools.mk_el_name) (1 upto n)
      val case_prod_names = map fst (Tuple_Tools.strip_case_prod t)
    in (prefer_fst case_prod_names standard_names, Ts) end

  fun dest_term ct =
    let
      val {return, anno_names, body, ...} = @{cterm_match \<open>L2_seq_gets ?return ?anno_names ?body\<close>} ct
      val (names, Ts) = dest_body (Thm.term_of body)
      val annotated_names = these (try CLocals.dest_name_hints (Thm.term_of anno_names))
      val var_names = prefer_fst annotated_names names
      val rets = HOLogic.strip_tuple (Thm.term_of return)
    in (var_names ~~ Ts, rets, body) end

  fun augment_derived_facts frees defs ctxt =
    let
      fun contains_new_frees thm =
        exists (member (op =) (map dest_Free frees)) (Term.add_frees (Thm.prop_of thm) [])

      val new_prems = Simplifier.prems_of ctxt
        |> map (Local_Defs.fold ctxt defs)
        |> filter contains_new_frees

      val _ = if null new_prems then raise Match else ()
    in (ctxt |> Simplifier.add_prems new_prems) addsimps new_prems end

  val (varTs, rets, bdy) = dest_term ct;

  val is_unit = case varTs of [(_, @{typ unit})] => true | _ => false;
  val _ = if is_unit orelse List.null (Simplifier.prems_of ctxt) then raise Match else ();

  val (vs, ctxt1) = ctxt
    |> Variable.declare_term t
    |> Variable.variant_fixes (map fst varTs);
  val frees = map Free (vs ~~ map snd varTs)
  val defs = map (Thm.cterm_of ctxt1 o Logic.mk_equals) (frees ~~ rets) 

  val (def_thms, ctxt2) = Assumption.add_assumes defs ctxt1
  val app = Thm.apply bdy  (Thm.cterm_of ctxt2 (HOLogic.mk_tuple frees))
  val ctxt3 = Variable.declare_term (Thm.term_of app) ctxt2
  val ctxt4 = augment_derived_facts frees def_thms ctxt3
  val [bdy_thm] = Proof_Context.export ctxt4 ctxt [Simplifier.asm_full_rewrite ctxt4 app]
  val seq_inst = (instantiate_lhs @{thm L2_marked_seq_gets_stop} ct) OF [bdy_thm OF (replicate (length defs) reflexive_thm)]
  fun changed eq_thm =
    let
      val ord = eq_thm |> Thm.concl_of |> Logic.dest_equals |> Term_Ord.fast_term_ord
    in ord <> EQUAL end
in
  if changed bdy_thm then SOME seq_inst else NONE
end) handle Match => NONE

val l2_marked_gets_bind_simproc =
  Utils.mk_simproc' @{context}
    ("l2_marked_gets_bind_augment_context_simproc", ["L2_seq_gets ?c ?n ?A"],
      fn ctxt => fn ct =>
      case l2_marked_gets_bind_simproc' ctxt ct of
        NONE => (case l2_marked_gets_bind_augment_context_simproc' ctxt ct of
                   NONE => SOME @{thm L2_seq_gets_def}
                 | some => some)
      | some => some)

local
structure  Enabled = Proof_Data(type T = bool val init = K true);
in
val c_fnptr_guard_simproc =
 Simplifier.make_simproc @{context} {name = "c_fnptr_guard_simproc", kind = Simproc, identifier = [],
    lhss = [Proof_Context.read_term_pattern @{context} "c_fnptr_guard ?P"],
    proc = fn phi => fn ctxt => fn ct =>
  if Enabled.get ctxt then
    let
      val prems = Simplifier.prems_of ctxt
      fun relevant t = case t of
            @{term_pat "Trueprop ?P"} => relevant P
          | @{term_pat "_ <s _"} => true
          | @{term_pat "_ \<le>s _"} => true
          | @{term_pat "(_::'a::len word) < _"} => true
          | @{term_pat "(_::'a::len word) \<le> _"} => true
          | @{term_pat "(_::int) < _"} => true
          | @{term_pat "(_::int) \<le> _"} => true
          | @{term_pat "(_::nat) < _"} => true
          | @{term_pat "(_::nat) \<le> _"} => true
          | _ => false
      val relevant_prems = prems |> filter (relevant o Thm.prop_of)
      val goal = \<^instantiate>\<open>grd = ct in cprop \<open>grd = True\<close>\<close>
      val ctxt = Enabled.map (K false) ctxt (* avoid recursive call *)
      val maybe_eq = try (Goal.prove_internal ctxt [] goal) (fn _ =>
           EVERY [Method.insert_tac ctxt relevant_prems 1,
             AutoCorresUtil.dyn_call_split_simp_sidecondition_tac (K true) [] [] ctxt 1])
           |> Option.map mk_meta_eq
    in
       maybe_eq
    end
  else NONE
}
end

fun L2_guarded_local_simproc orig_ctxt =
 Simplifier.make_simproc orig_ctxt {name = "L2_guarded_simproc", kind = Simproc, identifier = [],
   lhss =  [Proof_Context.read_term_pattern orig_ctxt "L2_guarded ?g ?c", 
            Proof_Context.read_term_pattern orig_ctxt "L2_seq_guard ?g (%_. ?c)"],
   proc = fn phi => fn ctxt => fn ct =>
     let
       val {g, c, seq_guard} = ct |> Match_Cterm.switch [
              @{cterm_match "L2_guarded ?g ?c"} #> (fn {g, c, ...} => {g=g, c=c, seq_guard = false}),
              @{cterm_match "L2_seq_guard ?g (%_. ?c)"} #> (fn {g, c, ...} => {g=g, c=c, seq_guard = true})];

       val [stateT] = Thm.typ_of_cterm g |> binder_types
       val ([s'], ctxt') = Utils.fix_variant_cfrees [("s", stateT)] ctxt
       val guard_ctxt = (put_simpset (simpset_of orig_ctxt) ctxt') addsimprocs [c_fnptr_guard_simproc]
            |> Simplifier.add_cong @{thm "HOL.conj_cong"}
       val g_eq = Thm.apply g s' |> Cached_Theory_Simproc.rewrite_solve guard_ctxt
      
       val _ = Utils.verbose_msg 7 ctxt (fn _ => "guard (1): " ^ Thm.string_of_thm ctxt g_eq)
       val g' = Thm.rhs_of g_eq
       val (_, ctxt'') = Assumption.add_assumes [\<^instantiate>\<open>P = \<open>g'\<close> in cprop P\<close>] ctxt'
       val run = \<^infer_instantiate>\<open>c=c and s'=s' in cterm \<open>run c s'\<close>\<close> ctxt''
       val c_eq = run |> Simplifier.asm_full_rewrite ctxt'' |> singleton (Proof_Context.export ctxt'' ctxt)            
       val g_eq' = singleton (Proof_Context.export ctxt' ctxt) g_eq

       val rule = if seq_guard then @{thm L2_seq_guard_cong_stop0} else @{thm L2_guarded_cong_stop'}
       val thm0 = (Drule.infer_instantiate ctxt [(("g", 0), g), (("g'", 0), Thm.lambda s' g')] 
                    rule) OF [g_eq', c_eq]
       val thm = Utils.solve_sideconditions ctxt thm0 (assume_tac ctxt 1)
       val _ = Utils.verbose_msg 7 ctxt (fn _ => "guard (2): " ^ Thm.string_of_thm ctxt thm)
     in
       SOME thm
     end}

fun arg_simp n ctxt =
  Utils.nth_arg_conv n (Simplifier.asm_full_rewrite ctxt)

(*
 * Adjust "case_prod commands so that constructs such as:
 *
 *    while C (%x. gets (case x of (a, b) => %s. P a b)) ...
 *
 * are transformed into:
 *
 *    while C (%(a, b). gets (%s. P a b)) ...
 *)
fun fix_L2_while_loop_splits_conv ctxt =
  Simplifier.asm_full_rewrite (
    put_simpset HOL_ss ctxt
    addsimps @{thms L2_split_fixups}
    |> fold Simplifier.add_cong @{thms L2_split_fixups_congs})

fun cleanup_ss ctxt guard_simps opt =
let
  val record_ss = RecursiveRecordPackage.get_simpset (Proof_Context.theory_of ctxt)
  val autocorres_record_ss = (merge_ss (AUTOCORRES_SIMPSET, record_ss));
  val size_simps = Named_Theorems.get ctxt @{named_theorems size_simps}

  val guarded_ctxt = put_simpset autocorres_record_ss ctxt addsimps guard_simps delsimps size_simps
  (* normalise pointer accesses towards operations on the root pointer *)
  val h_val_fields = Named_Theorems.get ctxt @{named_theorems h_val_fields}
  val fl_ti_simps = Named_Theorems.get ctxt @{named_theorems fl_ti_simps}
  val fl_Some_simps = Named_Theorems.get ctxt @{named_theorems fl_Some_simps} 
  val fg_cons_simps = Named_Theorems.get ctxt @{named_theorems fg_cons_simps}
  val L2_modify_heap_update_field_root_conv =  Named_Theorems.get ctxt @{named_theorems L2_modify_heap_update_field_root_conv}

  val size_align_simps = Named_Theorems.get ctxt @{named_theorems size_align_simps}
  val ptr_access_thms =
        h_val_fields @ fl_ti_simps @ fl_Some_simps @ fg_cons_simps @
        L2_modify_heap_update_field_root_conv @ 
        size_align_simps @ (* To solve precondition of h_val_coerce_ptr_coerce_packed [unfolded size_of_def] *)
        @{thms 
            c_guard_ptr_coerceI
            c_guard_field_lvalue
            ptr_coerce_index_array_ptr_index_conv 
            ptr_coerce_index_array_ptr_index_sint_conv
            ptr_coerce_index_array_ptr_index_numeral_conv
            ptr_coerce_index_array_ptr_index_0_conv
            array_ptr_index_field_lvalue_conv
            unat_less_helper nat_sint_less_helper
            update_ti_adjust_ti(1)
            field_lookup_array field_ti_array field_lvalue_append

            h_val_field_from_bytes' (* h_val_field_from_root *) 
                                    (* does not match adjust_ti (adjust_ti ... 
                                       which comes from  paths \<ge> 2 *)
            h_val_coerce_ptr_coerce_packed [unfolded size_of_def]
            h_val_field_ptr_coerce_from_bytes_packed [unfolded size_of_def]}

  (* Setup basic simplifier. *)
  fun basic_ss ctxt = ctxt
      |> put_simpset autocorres_record_ss
      |> UMM_Proofs.set_array_bound_mksimps
      |> not (opt = FunctionInfo.RAW) ? (fn ctxt => ctxt 
          addsimps (Utils.get_rules ctxt @{named_theorems L2opt})
          addsimps ptr_access_thms
          delsimps size_simps
          delsimprocs [@{simproc case_prod_beta}]
          addsimprocs [
            L2_guarded_local_simproc guarded_ctxt,
            l2_marked_gets_bind_simproc,
            Tuple_Tools.SPLIT_simproc, Tuple_Tools.tuple_case_simproc
          ] @ [@{simproc field_lookup}]
          delsimps @{thms Product_Type.prod.case Product_Type.case_prod_conv replicate_0 replicate_Suc replicate_numeral}
          addloop ("tuple_inst_tac", Tuple_Tools.tuple_inst_tac)
          |> Simplifier.add_cong @{thm L2_marked_seq_gets_cong}
          |> Simplifier.add_cong @{thm L2_marked_seq_guard_cong}
          |> Simplifier.add_cong @{thm SPLIT_cong}
          |> Simplifier.add_cong @{thm STOP_cong}
          |> Simplifier.add_cong @{thm if_cong}
          |> Simplifier.add_cong @{thm HOL.conj_cong}
          |> Simplifier.add_cong @{thm L2_condition_cong}
          |> Simplifier.add_cong @{thm L2_while_cong_simp_split}
          |> Simplifier.add_cong @{thm L2_guarded_block_cong}
      )
      |> (fn ctxt => ctxt addsimps @{thms WORD_values WORD_signed_to_unsigned [symmetric]})
in
  basic_ss ctxt
end

(*
 * Carry out flow-sensitive optimisations on the given 'thm'.
 *
 * "n" is the argument number to cleanup, counting from 1. So for example, if
 * our input theorem was "corres P A B", an "n" of 2 would simplify "A".
 * If n < 0, then the cleanup is applied to the -n-th argument from the end.
 *
 *  "opt" is PEEP, apply L2Peephole and L2Opt simplification rules.
 * If RAW, do not use AutoCorres' simplification rules at all.
 *)
fun cleanup_thm ctxt guard_simps aux_simps thm opt n do_trace =
let
  val depth = strip_comb_depth_of_term (Thm.prop_of thm)
  (* Don't print out warning messages. *)
  val ctxt = ctxt |> Context_Position.set_visible false
             |> Config.map simp_depth_limit (K (depth + 20))

  val mark_seq_conv =
    (Conv.try_conv (Conv.rewrs_conv @{thms L2_seq_guard_def [symmetric] L2_seq_gets_def [symmetric]}))

  val l2opt_conv =
    (Simplifier.rewrite (put_simpset HOL_basic_ss ctxt
      addsimprocs [@{simproc ETA_TUPLED}]
      addsimps
      (Utils.get_rules ctxt @{named_theorems L2opt} @ @{thms STOP_def L2_seq_guard_def L2_seq_gets_def} @
       aux_simps)))

  fun simp_conv ctxt =
    Drule.beta_eta_conversion
    then_conv (fix_L2_while_loop_splits_conv ctxt)
    then_conv l2opt_conv
    then_conv (Conv.bottom_conv (K mark_seq_conv) ctxt)
    then_conv (Simplifier.asm_full_rewrite (cleanup_ss ctxt guard_simps opt))
    then_conv l2opt_conv

  fun l2conv conv =
    Utils.remove_meta_conv (fn ctxt => Utils.nth_arg_conv n (conv ctxt)) ctxt

  fun dest_alls (Const (@{const_name Pure.all}, _) $ Abs (_, _, t)) = dest_alls t
     | dest_alls t = t

  fun nth_arg n thm =
    let
      (* Same argument count as Utils.nth_arg_conv *)
      val args = thm |> Thm.prop_of |> dest_alls |> HOLogic.dest_Trueprop |> strip_comb |> snd;
      val num_args = length args
      val pos = (if n < 0 then num_args + 1 + n else n - 1)
    in
      nth args pos
    end;

  (* Apply peephole optimisations to the theorem. *)

  val msg = AutoCorresTrace.get_trace_info_msg ctxt;
  val ctxt = ctxt |> AutoCorresTrace.put_trace_info_stage FunctionInfo.PEEP;
  val new_thm =
    if not (opt = FunctionInfo.RAW) then
      let
        val _ = AutoCorresUtil.verbose_msg 1 ctxt (fn _ =>  "starting peephole optimisation");
        val new_thm =
          AutoCorresTrace.fconv_rule_maybe_traced ctxt (l2conv simp_conv) thm do_trace
          |> Drule.eta_contraction_rule
        val _ = AutoCorresUtil.verbose_msg 1 ctxt (fn _ => msg ^ " (peep): " ^ Thm.string_of_thm ctxt new_thm);
      in new_thm end
    else
      thm

  (* Beta/Eta normalise. *)
  val new_thm = Conv.fconv_rule (l2conv (K Drule.beta_eta_conversion)) new_thm
in
  new_thm
end

(* Also tag the traces in a suitable format to be stored in AutoCorresData. *)
fun cleanup_thm_tagged ctxt guard_simps aux_simps thm opt n do_trace phase =
  cleanup_thm ctxt guard_simps aux_simps thm opt n do_trace

end
