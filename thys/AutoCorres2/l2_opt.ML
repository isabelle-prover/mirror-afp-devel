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

fun proc_conv proc (ctxt: Proof.context):conv = fn ct =>
  the_default (Conv.all_conv ct) (proc ctxt ct |> Option.map (fn thm => Conv.rewr_conv thm ct))

\<comment> \<open>Apply conv to rhs in: \<^term>\<open>lhs \<equiv> STOP (rhs)\<close> \<close>
fun STOP_rhs_conv conv = Conv.fconv_rule (Conv.arg_conv \<comment> \<open>\<equiv>\<close> (Conv.arg_conv \<comment> \<open>STOP\<close> conv))

\<comment> \<open>Apply conv to rhs in: \<^term>\<open>lhs \<equiv> STOP (rhs)\<close> and remove \<^const>\<open>STOP\<close> in case rhs was modified\<close>
fun STOP_rhs_unfold_conv conv = Conv.fconv_rule (Conv.arg_conv \<comment> \<open>\<equiv>\<close> 
      (Conv.try_conv (Conv.changed_conv (Conv.arg_conv \<comment> \<open>STOP\<close> conv) then_conv (Conv.rewr_conv @{thm STOP_def}))))

fun until_conv done conv ct =
  if done ct then Conv.all_conv ct
  else ct |> (
     conv then_conv
     until_conv done conv)

fun rewrite_until_conv done thms = until_conv done (Conv.rewrs_conv thms)

fun rhs_prem_conv conv = Conv.fconv_rule (Conv.prems_conv 1 (Conv.arg_conv conv))
fun rewrite_rhs_prem thm = rhs_prem_conv (Conv.rewr_conv thm)
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

val exists_zero =
  exists_subterm (fn (Const (c, _)) => c = @{const_name c_type_class.zero} | _ => false)

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
                   (opt = AutoCorres_Options.Selectors andalso 
                      (exists_zero lhs (* we assume that this case only appears when eliminating L2_unknown / unbind *) orelse 
                       only_selection rhs)))
               else (* update *)
                 exists_zero lhs (* we assume that this case only appears when eliminating L2_unknown / unbind *)
                 orelse only_selection rhs
          end
         val x = expand lhs rhs'
      in
        if is_simple lhs orelse count <= 1 orelse expand lhs rhs' then
          SOME @{thm L2_marked_seq_gets_apply}
        else
          NONE
      end
    | (Const (@{const_name "L2_seq_gets"}, _) $ lhs $ _ $ _) =>
         if exists_zero lhs then (* we assume that this case only appears when eliminating L2_unknown / unbind *)
           SOME @{thm L2_marked_seq_gets_apply}
         else NONE
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

fun l2_marked_gets_bind_augment_context_simproc' ctxt ct =
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
    in (ctxt |> Simplifier.add_prems new_prems) addsimps new_prems end

  val (varTs, rets, bdy) = dest_term ct;

  val arity = length varTs

  val (vs, ctxt1) = ctxt
    |> Variable.declare_term t
    |> Variable.variant_fixes (map fst varTs);

  val frees = map Free (vs ~~ map snd varTs)
  val defs = map (Thm.cterm_of ctxt1 o Logic.mk_equals) (frees ~~ rets) 

  val (def_thms, ctxt2) = Assumption.add_assumes defs ctxt1
  val bdy_eta_thm = Tuple_Tools.eta_expand_tupled_conv ctxt2 bdy
  val bdy' = bdy_eta_thm |> Thm.rhs_of
  val app = Tuple_Tools.beta_tupled ctxt2 arity bdy' (Thm.cterm_of ctxt2 (HOLogic.mk_tuple frees))
  val ctxt3 = augment_derived_facts frees def_thms ctxt2
  val [bdy_thm] = Proof_Context.export ctxt3 ctxt [Simplifier.asm_full_rewrite ctxt3 app]
  val thy_ctxt = Proof_Context.theory_of ctxt |> Proof_Context.init_global (* avoid accidental name clash when splitting rule *)
  val splitted_rule = 
    if arity > 1 then 
      Tuple_Tools.split_rule thy_ctxt  ["f'", "g"] @{thm L2_marked_seq_gets_stop''} arity 
    else
      @{thm L2_marked_seq_gets_stop''}

  val seq_inst0 = instantiate_lhs splitted_rule ct OF [bdy_eta_thm, bdy_thm]
  val seq_inst = Utils.solve_sideconditions ctxt seq_inst0 (ALLGOALS (asm_full_simp_tac ctxt))
  fun changed eq_thm =
    let
      val ord = eq_thm |> Thm.concl_of |> Logic.dest_equals |> Term_Ord.fast_term_ord
    in ord <> EQUAL end
in
  if changed bdy_thm then SOME seq_inst else NONE
end

val l2_marked_gets_bind_simproc =
  Utils.mk_simproc' @{context}
    ("l2_marked_gets_bind_augment_context_simproc", ["L2_seq_gets ?c ?n ?A"],
      fn ctxt => fn ct =>
      case l2_marked_gets_bind_simproc' ctxt ct of
        NONE => (case l2_marked_gets_bind_augment_context_simproc' ctxt ct of
                   NONE => SOME @{thm L2_seq_gets_def}
                 | SOME eq => 
                    let
                      val eq' = STOP_rhs_unfold_conv (proc_conv l2_marked_gets_bind_simproc' ctxt) eq
                    in 
                      SOME eq'
                    end) 
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
            Proof_Context.read_term_pattern orig_ctxt "L2_seq_guard ?g ?c"],
   proc = fn phi => fn ctxt => fn ct =>
     let
       val {g, c, seq_guard} = ct |> Match_Cterm.switch [
              @{cterm_match "L2_guarded ?g ?c"} #> (fn {g, c, ...} => {g=g, c=c, seq_guard = false}),
              @{cterm_match "L2_seq_guard ?g ?c"} #> (fn {g, c, ...} => {g=g, c=c, seq_guard = true})];

       val [stateT] = Thm.typ_of_cterm g |> binder_types
       val ([s'], ctxt') = Utils.fix_variant_cfrees [("s", stateT)] ctxt
       val guard_ctxt = 
         if seq_guard then ctxt'
         else (put_simpset (simpset_of orig_ctxt) ctxt') addsimprocs [c_fnptr_guard_simproc]
            |> Simplifier.add_cong @{thm "HOL.conj_cong"}

       val g_eq = Thm.apply g s' |> Cached_Theory_Simproc.rewrite_solve guard_ctxt
      
       val _ = Utils.verbose_msg 7 ctxt (fn _ => "guard (1): " ^ Thm.string_of_thm ctxt g_eq)
       val g' = Thm.rhs_of g_eq
       val ([g'_thm], ctxt'') = Assumption.add_assumes [\<^instantiate>\<open>P = \<open>g'\<close> in cprop P\<close>] ctxt'
       val g'_eqs = Simplifier.mksimps ctxt'' g'_thm
       val g'_ariths = Utils.iariths_of_eqs g'_eqs
       val run = 
         if seq_guard then
           \<^infer_instantiate>\<open>c=c and s'=s' in cterm \<open>run (c ()) s'\<close>\<close> ctxt''
         else
           \<^infer_instantiate>\<open>c=c and s'=s' in cterm \<open>run c s'\<close>\<close> ctxt''
       val c_eq = run |> Simplifier.asm_full_rewrite (ctxt'' addsimps g'_eqs 
         |> Utils.add_ariths g'_ariths) |> singleton (Proof_Context.export ctxt'' ctxt)            
       val g_eq' = singleton (Proof_Context.export ctxt' ctxt) g_eq
       val rule = if seq_guard then @{thm L2_seq_guard_cong_stop0} else @{thm L2_guarded_cong_stop'}
       val thm0 = (Drule.infer_instantiate ctxt [(("g", 0), g), (("g'", 0), Thm.lambda s' g'), (("c", 0), c)] 
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
fun gen_split_fixup_convs thms ctxt =
  Simplifier.asm_full_rewrite (
    put_simpset HOL_ss ctxt
    addsimps thms
    |> fold Simplifier.add_cong @{thms L2_split_fixups_congs})

val fix_L2_while_loop_splits_conv = gen_split_fixup_convs @{thms L2_split_fixups}
 
fun bottom_rewrs_conv thms = Conv.bottom_conv (K (Conv.try_conv (Conv.rewrs_conv thms)))

val fold_seq_condition = bottom_rewrs_conv 
  @{thms L2_seq_condition_def [symmetric]}

val fold_seq_condition_unfold_STOP = bottom_rewrs_conv 
  @{thms L2_seq_condition_def [symmetric] STOP_def}

val unfold_seq_condition = bottom_rewrs_conv 
  @{thms L2_seq_condition_def}

fun mark_seq_conv phase = bottom_rewrs_conv 
  (@{thms 
     L2_seq_guard_def [symmetric] 
     L2_seq_gets_def [symmetric]  
     STOP_def} @ 
   (if phase = FunctionInfo.L2 then @{thms L2_seq_unknown_def [symmetric]} else []))

val mark_seq_conv' = bottom_rewrs_conv 
  @{thms 
     L2_seq_guard_def [symmetric] 
     L2_seq_gets_def [symmetric]
     STOP_def}



(* In L2 we try to remove unnecessary local variable initialisations (L2_unknown) and try to 
   minimize propagation of unused values through while loops. For struct variables this is a challenge
   as assignments and initialisations to the struct variable may be split to a sequence of 
   field assignments. 
   We do a best effort approach to group consecutive updates into a single constructor of the 
   whole structure to identify unused values and to minimize dependencies. 
   This is what "unbind" below refers to.
   This is an incomplete process but we try to handle some prominent C ideoms.

   Note that we first "unbind" unnecessary initialisations / assignments in the L2Opt phase of L2 
   and later remove the unused tuple components (in particular in while loops) during L2prj of L2.
*)
fun mk_unbind_thm ctxt T =
  let
    val unbind = Thm.instantiate (TVars.make [((("'a",0), @{sort c_type}), T)], Vars.empty) @{thm unbind}
    val ((_, [thm]), ctxt') = Variable.import false [unbind] ctxt 
    val unbind_inst = Utils.check_solve_sideconditions (K true) ctxt' thm (
      asm_full_simp_tac (ctxt' addsimps (Named_Theorems.get ctxt' @{named_theorems recursive_records_split_all_eqs} )) 1)
      |> Simpdata.mk_meta_cong ctxt'
      |> singleton (Proof_Context.export ctxt' ctxt) |> Drule.zero_var_indexes 
  in
    unbind_inst
  end

val condition_depth_limit = Attrib.setup_config_int @{binding condition_depth_limit} (K 11)

type data = {
  record_info : (string * RecursiveRecordPackage.info) list,
  condition_depth : int,
  field_fixes : Termset.T
}

fun map_record_info f ({record_info, condition_depth, field_fixes}:data) = 
  ({record_info = f record_info, condition_depth = condition_depth, field_fixes = field_fixes}:data)

fun map_condition_depth f ({record_info, condition_depth, field_fixes}:data) = 
  ({record_info = record_info, condition_depth = f condition_depth, field_fixes = field_fixes}:data)

fun map_field_fixes f ({record_info, condition_depth, field_fixes}:data) = 
  ({record_info = record_info, condition_depth = condition_depth, field_fixes = f field_fixes}:data)


structure Prf_Data = Proof_Data (
  type T = data;
  val init = K {record_info = [], condition_depth = 0, field_fixes = Termset.empty};
)

fun lookup_info ctxt (Type (r, _)) = AList.lookup (op =) (#record_info (Prf_Data.get ctxt)) r |> Option.map (pair r)
  | lookup_info ctxt _ = NONE

fun add_info x = Prf_Data.map (map_record_info (AList.update (op =) x))

local
  fun rT {constructor = (_, T), ...} = snd (strip_type T)
in 
fun get_record_info' ctxt r = 
      Symtab.lookup (RecursiveRecordPackage.get_info (Proof_Context.theory_of ctxt)) r 
      |> Option.map (fn info => (r, rT info, info))
end

fun get_record_info ctxt (rT as (Type (r, _))) = 
     get_record_info' ctxt r
  | get_record_info _ _ = NONE

fun mk_record_thms ctxt (r, {constructor, updates, fields}) =
  let
    val update_defs = updates |> map (Proof_Context.get_thm ctxt o (suffix "_def" o fst))
    val update_consts = Proof_Context.get_thms ctxt (suffix "_update_const" r)
    val update_zeros = Proof_Context.get_thms ctxt (suffix "_update_zero" r)
    val select_defs = fields |> map (Proof_Context.get_thm ctxt o (suffix "_def" o fst))
  in 
    {update_defs = update_defs, update_consts = update_consts, 
      update_zeros = update_zeros, select_defs = select_defs}
  end

fun get_record_thms' ctxt r =
  get_record_info' ctxt r |> Option.map (fn (r, _, info) => mk_record_thms ctxt (r, info))

fun get_record_thms ctxt (rT as (Type (r, _))) = get_record_thms' ctxt r
  | get_record_thms ctxt _ = NONE

fun add_thms 
  {update_defs = xs1, update_consts = xs2, update_zeros = xs3, select_defs = xs4}
  {update_defs = ys1, update_consts = ys2, update_zeros = ys3, select_defs = ys4}
  =
  {update_defs = xs1 @ ys1, update_consts = xs2 @ ys2, update_zeros = xs3 @ ys3, select_defs = xs4 @ ys4}
 
fun lookup_record_thms ctxt = 
   {update_defs = [], update_consts = [], update_zeros = [], select_defs = []} 
   |> fold add_thms (map (mk_record_thms ctxt) (#record_info (Prf_Data.get ctxt)))

fun field_fixes_of ctxt t =
  let
     val field_fixes = #field_fixes (Prf_Data.get ctxt)
     fun add (t as Free _) S = if (Termset.member field_fixes t) then Termset.insert t S else S
       | add _ S = S
  in 
    Termset.empty |> Term.fold_aterms add t 
  end

val L2_seq_condition_distrib_simproc =
  \<^simproc_setup>\<open>passive L2_seq_condition_distrib (\<open>L2_seq_condition c L R X\<close>) = \<open>K (fn ctxt => fn ct =>
  if #condition_depth (Prf_Data.get ctxt) <= Config.get ctxt condition_depth_limit then
    let
      val {c, L, R, X, ...} = @{cterm_match "L2_seq_condition ?c ?L ?R ?X"} ct
    (*
      If relevant field_fixes are no longer in L, R X we can stop.
      If there are still some left and we have not yet reached the condition_depth_limit:
        - Simplify L;X
        - Simplify R;X
        - Combine results 
      Note that this is actually a congproc. We do this top down.
    *)
      val remaining_field_fixes = field_fixes_of ctxt (Thm.term_of ct)
    in
      if Termset.is_empty remaining_field_fixes then
        (Utils.verbose_msg 2 ctxt (fn _ => "L2_seq_condition_distrib_simproc: no distrib");
        NONE)
      else
        let
          val _ = Utils.verbose_msg 2 ctxt (fn _ => "L2_seq_condition_distrib_simproc: distrib")
          val ctxt' = Prf_Data.map (map_condition_depth (fn n => n + 1)) ctxt
          val L_X = \<^infer_instantiate>\<open>L = L and X = X in cterm \<open>L2_seq L X\<close>\<close> ctxt
            |> Simplifier.asm_full_rewrite ctxt'
          val R_X = \<^infer_instantiate>\<open>R = R and X = X in cterm \<open>L2_seq R X\<close>\<close> ctxt
            |> Simplifier.asm_full_rewrite ctxt'
        in
          SOME (@{thm L2_seq_condition_unfold_STOP} OF [L_X, R_X]) 
        end
    end
  else (warning ("L2_seq_condition_distrib_simproc condition_depth_limit " ^ 
         string_of_int (Config.get ctxt condition_depth_limit) ^ " reached, aborting."); 
       NONE))\<close>\<close>

fun exploded_record_value T ctxt =
  get_record_info ctxt T |> Option.map (fn (rn, rT, info as {constructor, fields,...}) =>
  let
    val constr = Thm.cterm_of ctxt (Const constructor)
    val (xs, ctxt') = ctxt |> fold_map (exploded_field_value) fields
    val (field_values, fixes) = split_list xs
    val r = Utils.applies field_values constr
  in
    ((r, flat fixes), ctxt')
  end)
and exploded_field_value (fld_name, T) ctxt =
  case exploded_record_value T ctxt of
    SOME (v, ctxt') => (v, ctxt')
  | NONE => let val ([carg], ctxt') = Utils.fix_variant_cfrees [(safe_unsuffix "_C"  (Long_Name.base_name fld_name), T)] ctxt
            in ((carg, [carg]), ctxt') end

datatype unbind_result = Already_Unbound | Did_Unbind | Could_Not_Unbind

fun unbind_proc ctxt f = 
   get_record_info ctxt (domain_type (Thm.typ_of_cterm f)) |> Option.mapPartial (fn (rn, rT, info as {constructor, fields,...}) =>
   let     
      (* We assign a fresh value to the structure variable and aggressively unfold "L2_seq_gets" to see 
         if the fresh value disappears from the body. If it isappears we know that the
         value is not relevant and can assign ZERO instead.  
      *)
      val constr = Thm.cterm_of ctxt (Const constructor)
      val ((r, cargs), ctxt1) = the (exploded_record_value rT ctxt)
      val mark_f_r = Thm.apply f r |> fold_seq_condition_unfold_STOP ctxt1 
      val f_r = mark_f_r |> Thm.rhs_of
      val simp_ctxt = ctxt1 addsimps @{thms L2_seq_gets_unfold L2_seq_L2_gets_const} delsimps @{thms L2_seq_condition_def}
        |> Prf_Data.map (map_field_fixes (fold Termset.insert (map Thm.term_of cargs)))
      val eq = Utils.timeit_msg 2 ctxt (fn _ => "unbind_proc rhs" ) (fn _ => Simplifier.rewrite simp_ctxt f_r)
      val rhs = Thm.rhs_of eq
      val _ = Utils.verbose_msg 7 ctxt (fn _ => "unbind_proc rhs: " ^ string_of_cterm ctxt1 rhs)
   in 
     if exists_subterm (member (op aconv) (map Thm.term_of cargs)) (Thm.term_of rhs) then
       NONE
     else
       let
         val unbind = mk_unbind_thm ctxt (Thm.ctyp_of ctxt rT) |> Drule.infer_instantiate' ctxt [SOME f]
         val [eq'] = Proof_Context.export simp_ctxt ctxt [Thm.transitive mark_f_r eq] 
         val thm = Utils.solve_sideconditions ctxt unbind (resolve_tac ctxt [eq'] 1)
       in SOME (thm, (rn, rT, info)) end
   end)

fun unbind_conv ctxt cont ct =
  if is_some (try @{cterm_match "\<lambda>_. ?g"} ct) then cont Already_Unbound (Conv.all_conv ct)
  else
    (case unbind_proc ctxt ct of
       NONE => cont Could_Not_Unbind (Conv.all_conv ct)
    | SOME (f_unbind_eq, (rn, rT, info)) => 
      let
        val rhs = Thm.rhs_of f_unbind_eq
        val {update_zeros, ...} = the (get_record_thms ctxt rT)
        (* We propagate the zero less aggressively *)
        val ctxt1 = add_info (rn, info) ctxt addsimps (update_zeros )
        val eq = Utils.timeit_msg 2 ctxt (fn _ => "unbind_conv simp" ) (fn _ =>  
          rhs |> (
          unfold_seq_condition ctxt then_conv 
          Simplifier.asm_full_rewrite ctxt1))
        val eq1 = Thm.transitive f_unbind_eq eq
        val _ = Utils.verbose_msg 6 ctxt (fn _ => ("unbind_conv eq1: " ^ Thm.string_of_thm ctxt1 eq1))
      in cont Did_Unbind eq1 end)

fun string_of Already_Unbound = "already unbound"
  | string_of Did_Unbind = "did unbind"
  | string_of Could_Not_Unbind = "could not unbind"

fun safe_hd [] = ""
  | safe_hd (x::xs) = x

fun safe_tl [] = []
  | safe_tl (x::xs) = xs

(* N.B. Each L2_seq_unknown is handled separately. Thus in case of a sequence of 
 * L2_seq_unknown the body is normalised several times. 
 * Simultaneous treatment of all components together might speed up the process. 
 *)
val L2_seq_unknown_simproc = \<^simproc_setup>\<open>passive L2_seq_unknown ("L2_seq_unknown ns f") = \<open>K (fn ctxt => fn ct => 
  let
    val {ns, f,...} = @{cterm_match "L2_seq_unknown ?ns ?f"} ct
    fun msg tag = Utils.verbose_msg 1 ctxt (fn _ => 
      "L_seq_unknown (" ^ string_of tag ^ "): " ^ quote (safe_hd (CLocals.dest_name_hints (Thm.term_of ns))))
  in 
    f |> unbind_conv ctxt (fn unbind_result => fn eq =>
      case unbind_result of 
        Already_Unbound => 
         (msg unbind_result; SOME (@{thm L2_seq_unknown_unfold_STOP} OF [eq]))
      | Did_Unbind => 
          (msg unbind_result; SOME (@{thm L2_seq_unknown_unfold_STOP} OF [eq]))
      | Could_Not_Unbind =>
          (msg unbind_result; SOME (@{thm L2_seq_unknown_STOP} OF [eq])))
  end)\<close>\<close>

val case_prod_cong = @{lemma \<open>f \<equiv> f' \<Longrightarrow> case_prod f \<equiv> case_prod f'\<close> by simp}
val ext = @{lemma \<open>(\<And>v. f v \<equiv> g v) \<Longrightarrow> f \<equiv> g\<close> by (presburger)}



(* N.B. each tuple component is handled separately, bottom up. So the body is normalised
   several times. Simultaneous treatment of all components together might speed up the process. *)
(* used as a congproc, f is not yet simplified *)
fun unbind_tupled_conv ctxt label names ct = ct |> Match_Cterm.switch [
  @{cterm_match \<open>case_prod ?f\<close>} #> (fn {f, ...} => 
     let
        val vT = domain_type (Thm.typ_of_cterm f)
        val ([v], ctxt1) = Utils.fix_variant_cfrees [("v", vT)] ctxt
        val f_app_eq = (Thm.apply f v) |> (
          Thm.beta_conversion false then_conv 
          unbind_tupled_conv ctxt1 label (safe_tl names) then_conv
          mark_seq_conv' ctxt1)
          |> singleton (Proof_Context.export ctxt1 ctxt)
        val name_hint = safe_hd names
        val ext = case Thm.term_of f of Abs (x, _, _) => Drule.rename_bvars' [SOME x] ext | _ => ext
        val f_eq = Drule.infer_instantiate' ctxt [SOME f] ext OF [f_app_eq]
        val _ = Utils.verbose_msg 7 ctxt (fn _ => ("unbind_tupled_conv: f_eq: " ^ Thm.string_of_thm ctxt f_eq))
        val unbind_f_eq = Thm.rhs_of f_eq |> unbind_conv ctxt (fn tag => fn eq => 
          (Utils.verbose_msg 1 ctxt (fn _ => "unbind_tupled_conv " ^ label ^ " (" ^ string_of tag ^ "): " ^ quote name_hint); 
            Thm.transitive f_eq eq))
        val _ = Utils.verbose_msg 6 ctxt (fn _ => ("unbind_tupled_conv: unbind_f_eq: " ^ Thm.string_of_thm ctxt unbind_f_eq))
     in case_prod_cong OF [unbind_f_eq] end)
  , unbind_conv ctxt (fn res => fn eq => 
      case res of Did_Unbind => eq | _ => Simplifier.asm_full_rewrite ctxt ct)]

(* used as a congproc, body not yet simplified *)
val L2_while_unbind_simproc = \<^simproc_setup>\<open>passive L2_while_unbind ("L2_while c b i ns") = \<open>K (fn ctxt => fn ct =>
  let
    val _ = Utils.verbose_msg 5 ctxt (fn _ => ("L2_while_unbind_simproc: " ^ string_of_cterm ctxt ct))
    val {c, b, ns,...} = @{cterm_match "L2_while ?c ?b ?i ?ns"} ct
    val names = CLocals.dest_name_hints (Thm.term_of ns) 
    fun mk_name_map eq = 
      let
        val names' = map fst (Tuple_Tools.strip_case_prod (Thm.term_of (Thm.rhs_of eq)))
      in Utils.zip names' names end
    fun sanitize_names eq = Drule.rename_bvars (mk_name_map eq) eq

    val c_eq = unbind_tupled_conv ctxt "while condition" names c |> sanitize_names
    val _ = Utils.verbose_msg 5 ctxt (fn _ => ("L2_while_unbind_simproc: c_eq: " ^ Thm.string_of_thm ctxt c_eq))
    val b_eq = Utils.timeit_msg 2 ctxt (fn _ => "L2_while_unbind_simproc b_eq" ) (fn _ =>  
        unbind_tupled_conv ctxt "while body" names  b  |> sanitize_names)
    val _ = Utils.verbose_msg 5 ctxt (fn _ => ("L2_while_unbind_simproc: b_eq: " ^ Thm.string_of_thm ctxt b_eq))
    val rule = @{thm L2_while_unbind_STOP} OF[c_eq, b_eq]
    val _ = Utils.verbose_msg 4 ctxt (fn _ => ("L2_while_unbind_simproc: rule: " ^ Thm.string_of_thm ctxt rule))
  in 
    SOME (rule)
  end)\<close>\<close>


fun dest_abs ctxt ct = 
  Variable.dest_abs_cterm ct ctxt
  handle CTERM _ => 
   let
     val T = Thm.typ_of_cterm ct |> domain_type
     val ([x], ctxt1) = Utils.fix_variant_cfrees [("x", T)] ctxt 
   in
     ((x, Thm.apply ct x), ctxt1)
   end

fun mk_tuple [x] = x
  | mk_tuple (x::xs) =
     let val y = mk_tuple xs 
     in
      \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm x\<close> and 'b = \<open>Thm.ctyp_of_cterm y\<close> and
          x = x and y =\<open>y\<close>
        in cterm \<open>(x, y)\<close> for x::"'a" and y::"'b"\<close>
     end
  | mk_tuple [] = error ("mk_tuple: empty list")

fun dest_abs_tuple ctxt ct =
  let
    val T = Thm.typ_of_cterm ct |> domain_type
    val Ts = HOLogic.strip_tupleT T
  in
    if length Ts <= 1 then
      dest_abs ctxt ct 
    else
      let
        val fixes = tag_list 1 Ts |> map  (fn (i, T) => (suffix (string_of_int i) "x", T))
        val (xs, ctxt1) = Utils.fix_variant_cfrees fixes ctxt
        val y = mk_tuple xs
      in
        ((y, Thm.apply ct y), ctxt1)
      end
  end

fun strip_case_prods ctxt ct = ct |> Match_Cterm.switch [
  @{cterm_match \<open>case_prod ?f\<close>} #> (fn {f, ...} => 
     let 
       val ((x, bdy0), ctxt1) = dest_abs ctxt f
       val ((xs, bdy), ctxt2) = strip_case_prods ctxt1 bdy0
     in (((x::xs), bdy), ctxt2) end)
  , dest_abs_tuple ctxt #> apfst (apfst single)]

datatype seq_kind = Seq_gets | Gets | Other 

val classify = Match_Cterm.switch [
  @{cterm_match \<open>STOP (L2_seq_gets ?X ?n ?Y)\<close>} #> (fn _ => Seq_gets),
  @{cterm_match \<open>L2_gets ?X ?n\<close>} #> (fn _ => Gets),
  fn ct => Other]

val L2_condition_distrib = 
  @{lemma "L2_seq (L2_condition C L R) X \<equiv> L2_condition C (FUSE (L2_seq L X)) (FUSE (L2_seq R X))" 
    by (simp add: FUSE_def L2_condition_distrib)}
 
val L2_seq_rev_assoc = safe_mk_meta_eq @{thm L2_seq_rev_assoc} |> Drule.zero_var_indexes
val L2_seq_L2_gets_const = safe_mk_meta_eq @{thm L2_seq_L2_gets_const}
val L2_seq_STOP_unfold = @{lemma "L2_seq A (\<lambda>x. STOP (B x)) \<equiv> L2_seq A B" by (simp add: STOP_def)}
val L2_seq_L2_seq_gets_unfold = 
  @{lemma "L2_seq A (\<lambda>x. L2_seq_gets (X x) n (Y x)) \<equiv> L2_seq A (\<lambda>x. (L2_seq (L2_gets (\<lambda>_. X x) n) (Y x)))" 
  by (simp add: L2_seq_gets_def)}

val L2_seq_propagate_zero_simproc = \<^simproc_setup>\<open>passive L2_seq_propagate_zero ("L2_seq (L2_gets (\<lambda>_. c) ns) X") = \<open>K (fn ctxt => fn ct => 
  let
    val {c,...} = @{cterm_match "L2_seq (L2_gets (\<lambda>_. ?c) ?ns) ?X"} ct
    val constructors = #record_info (Prf_Data.get ctxt) |> map (Const o #constructor o snd)
    val t = Thm.term_of c
  in 
    if exists_zero t orelse exists_subterm (member (op aconv) constructors) t
    then SOME L2_seq_L2_gets_const
    else NONE
  end )\<close>\<close>

val FUSE_simproc = \<^simproc_setup>\<open>passive FUSE ("FUSE X") = \<open>K (fn ctxt => fn ct => 
  let
    val {X,...} = @{cterm_match "FUSE ?X"} ct
    val simp_ctxt = ctxt 
      addsimps @{thms L2_seq_assoc}
      addsimprocs [L2_seq_propagate_zero_simproc]
    val X_eq = Simplifier.asm_full_rewrite simp_ctxt X 
  in 
    SOME (@{thm FUSE_STOP} OF [X_eq])
  end)\<close>\<close>


val split_fixup_conv = gen_split_fixup_convs @{thms L2_split_fixups'}
fun split_fixup ctxt = Conv.fconv_rule (split_fixup_conv ctxt)

fun split ctxt names arity thm = 
  let
    val thy_ctxt = Proof_Context.theory_of ctxt |> Proof_Context.init_global (* avoid accidental name clash when splitting rule *)
    val thm' = Tuple_Tools.split_rule thy_ctxt names thm arity
      |> Drule.eta_contraction_rule
      |> split_fixup ctxt
      |> Drule.eta_contraction_rule
    val _ = Utils.verbose_msg 7 thy_ctxt (fn _ => "split: " ^ Thm.string_of_thm thy_ctxt thm') 
  in thm' end


fun assoc_conv ctxt = Match_Cterm.switch [
  @{cterm_match  "L2_seq ?A ?X"} #> (fn {A, X, ct_,...} =>
    let
      val ((bounds, bdy), ctxt1) = strip_case_prods ctxt X
      val arity = length bounds
      val rule = bdy |> Match_Cterm.switch [
          @{cterm_match "L2_seq ?B ?C"} #> (fn {B, C, ...} => 
            let
              val splitted = split ctxt1 ["B", "C"] arity L2_seq_rev_assoc
              val ns1 = these (PrettyBoundVarNames.get_var_names_ret ctxt [] (Thm.term_of A))
              val ns2 = these (PrettyBoundVarNames.get_var_names_ret ctxt [] (Thm.term_of B))
              val ns = CLocals.name_hints ctxt1 (ns2 @ ns1) |> Thm.cterm_of ctxt1
              val rule =  Drule.infer_instantiate ctxt [(("ns", 0), ns)] splitted
            in rule end),
          @{cterm_match "STOP ?B"} #> (fn _ =>
             split ctxt1 ["B"] arity L2_seq_STOP_unfold),
          @{cterm_match "L2_seq_gets ?X ?ns ?Y"} #> (fn _ =>
             split ctxt1 ["X", "Y"] arity L2_seq_L2_seq_gets_unfold),
          fn ct => raise CTERM("assoc_conv", [ct])]
      val _ = Utils.verbose_msg 6 ctxt (fn _ => "assoc_conv: rule: " ^ Thm.string_of_thm ctxt rule)
    in
      Conv.rewr_conv rule ct_
    end),
  fn ct => ct |> Conv.rewrs_conv 
    (@{thms STOP_def L2_seq_gets_def})]


fun assoc_conv' ctxt = Utils.verbose_conv 6 ctxt (fn _ => "assoc_conv") (assoc_conv ctxt)  

(*
Consider a structuure with two components fld1 and fld2
Use case: 
  if ... {
    x.fld1 = a;
  } else {
    x.fld1 = b;
  };
  x.fld2 = c; 
  ...

Transform to:
  if ... {
    x = {.fld1 = a, .fld2 = c};
  } else
    x = {.fld1 = b, .fld2 = c};
  }; ...

*)
val L2_condition_distrib_simproc = \<^simproc_setup>\<open>passive L2_condition_distrib (\<open>L2_seq (L2_condition c L R) X\<close>) = \<open>
  let
    val relevant_branch = Thm.term_of #> exists_zero
    fun is_gets (Const (c, _)) = (c = @{const_name L2_gets} orelse c = @{const_name L2_seq_gets})
      | is_gets _ = false
    
  in
    K (fn ctxt => fn ct =>
      let
        val {c, L, R, X, ...} = @{cterm_match \<open>L2_seq (L2_condition ?c ?L ?R) ?X\<close>} ct
        val ((bounds, X_bdy), ctxt1) = strip_case_prods ctxt X
        val bounds' = map Thm.term_of bounds
        fun dependent ct = exists_subterm (member (op aconv) bounds') (Thm.term_of ct)
        fun done ct = ct |> Match_Cterm.switch [
              @{cterm_match "L2_seq ?X ?Y"} #> (fn {Y, ...} => not (dependent Y)), 
              @{cterm_match "L2_seq_gets ?X ?n ?Y"} #> (fn _ => false),
              @{cterm_match "STOP ?X"} #> (fn _ => false),
              fn _ => true]
        val arity = length bounds
        val tags = bounds |> map (lookup_info ctxt o Thm.typ_of_cterm)
      in 
        if exists is_some tags andalso (relevant_branch L orelse relevant_branch R) then
          let
            val kind = classify X_bdy
            val _ = Utils.verbose_msg 4 ctxt (fn _ => ("L2_condition_distrib_simproc: kind, tags: " ^ @{make_string} (kind, tags)))
          in
            case kind of 
              Seq_gets => 
               (let 
                 val rev_assoc = X_bdy |> until_conv done (assoc_conv' ctxt1)
                   |> singleton (Proof_Context.export ctxt1 ctxt)
                 val splitted_rule = split ctxt ["X", "Y", "A"] arity @{thm L2_condition_L2_seq_gets_distrib'}
                 val inst_rule = instantiate_lhs splitted_rule ct
                     handle Pattern.MATCH => error ("inst_rule ct: " ^ string_of_cterm ctxt ct)
                 val rule = inst_rule OF [rev_assoc]
                 val _ = Utils.verbose_msg 4 ctxt (fn _ => "L2_condition_distrib_simproc: rule: " ^ Thm.string_of_thm ctxt rule)
               in
                 SOME rule
               end handle CTERM _ => (
                 Utils.verbose_msg 4 ctxt (fn _ => "L2_condition_distrib_simproc: rev_assoc failed: " ^ string_of_cterm ctxt X_bdy); 
                 NONE))
            | Gets => SOME L2_condition_distrib
            | Other => NONE
          end
        else
          NONE
      end)
  end\<close>\<close>

fun cleanup_ss ctxt guard_simps phase opt =
let
  val record_ss = 
    if FunctionInfo.phase_ord (phase, FunctionInfo.WA) = LESS 
    then RecursiveRecordPackage.get_no_congs_simpset (Proof_Context.theory_of ctxt) 
    else RecursiveRecordPackage.get_simpset (Proof_Context.theory_of ctxt)

  val autocorres_record_ss = (merge_ss (AUTOCORRES_SIMPSET, record_ss))
  val size_simps = Named_Theorems.get ctxt @{named_theorems size_simps}

  val word_simps = @{thms WORD_values WORD_signed_to_unsigned [symmetric]}
  val guarded_ctxt = put_simpset autocorres_record_ss ctxt addsimps (guard_simps @ word_simps) delsimps size_simps
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
            Tuple_Tools.SPLIT_simproc, Tuple_Tools.tuple_case_simproc, FUSE_simproc] @ 
            (if phase = FunctionInfo.L2 then 
              [L2_seq_unknown_simproc, L2_condition_distrib_simproc, L2_while_unbind_simproc,
               L2_seq_condition_distrib_simproc] 
             else []) @
            [@{simproc field_lookup}]  
          delsimps @{thms Product_Type.prod.case Product_Type.case_prod_conv replicate_0 replicate_Suc replicate_numeral}
          addloop ("tuple_inst_tac", Tuple_Tools.tuple_inst_tac)
          |> Simplifier.add_cong @{thm L2_marked_seq_gets_cong}
          |> Simplifier.add_cong @{thm L2_marked_seq_guard_block_cong}
          |> Simplifier.add_cong @{thm SPLIT_cong}
          |> Simplifier.add_cong @{thm STOP_cong}
          |> Simplifier.add_cong @{thm if_cong}
          |> Simplifier.add_cong @{thm HOL.conj_cong}
          |> Simplifier.add_cong @{thm L2_condition_cong}
          |> Simplifier.add_cong (if phase = FunctionInfo.L2 then @{thm L2_while_cong_block} else @{thm L2_while_cong_simp_split})
          |> Simplifier.add_cong @{thm L2_guarded_block_cong}
          |> Simplifier.add_cong @{thm FUSE_cong}
          |> Simplifier.add_cong @{thm STOP_UNBIND_cong}
          |> Simplifier.add_cong @{thm L2_seq_condition_block_cong} (* Only relevant in L2 *)
      )
      |> (fn ctxt => ctxt addsimps word_simps)
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
fun cleanup_thm ctxt guard_simps aux_simps thm (phase: FunctionInfo.phase) opt n do_trace =
let
  val depth = strip_comb_depth_of_term (Thm.prop_of thm)
  (* Don't print out warning messages. *)
  val ctxt = ctxt |> Context_Position.set_visible false
             |> Config.map simp_depth_limit (K (depth + 20))

  val l2opt_conv =
    (Simplifier.rewrite (put_simpset HOL_basic_ss ctxt
      addsimprocs [@{simproc ETA_TUPLED}, @{simproc Product_Type.unit_eq}]
      addsimps
      (Utils.get_rules ctxt 
        @{named_theorems L2opt} @ 
        @{thms STOP_def STOP_UNBIND_def L2_seq_guard_def L2_seq_gets_def L2_seq_unknown_def} @
        aux_simps)))

  fun simp_conv ctxt =
    Drule.beta_eta_conversion
    then_conv (fix_L2_while_loop_splits_conv ctxt)
    then_conv l2opt_conv
    then_conv (Utils.verbose_conv 3 ctxt (fn _ => "after mark_seq_conv") (mark_seq_conv phase ctxt))
    then_conv (Simplifier.asm_full_rewrite (cleanup_ss ctxt guard_simps phase opt))
    then_conv l2opt_conv
    then_conv (fix_L2_while_loop_splits_conv ctxt)

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
  cleanup_thm ctxt guard_simps aux_simps thm phase opt n do_trace

end
