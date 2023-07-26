signature TRANSFORM_DP =
sig
  val dp_fun_part1_cmd:
    (binding * string) * ((bool * (xstring * Position.T)) * (string * string) list) option
      -> local_theory -> local_theory
  val dp_fun_part2_cmd: string * (Facts.ref * Token.src list) list -> local_theory -> local_theory
  val dp_correct_cmd: local_theory -> Proof.state
end

structure Transform_DP : TRANSFORM_DP =
struct

fun dp_interpretation standard_proof locale_name instance qualifier dp_term lthy =
  lthy
  |> Interpretation.isar_interpretation ([(locale_name, ((qualifier, true), (Expression.Named (("dp", dp_term) :: instance), [])))], [])
  |> (if standard_proof then Proof.global_default_proof else Proof.global_immediate_proof)

fun prep_params (((scope, tm_str), def_thms_opt), mem_locale_opt) ctxt =
  let
    val tm = Syntax.read_term ctxt tm_str
    val scope' = (Binding.is_empty scope? Binding.map_name (fn _ => Transform_Misc.term_name tm ^ "\<^sub>T")) scope
    val def_thms_opt' = Option.map (Attrib.eval_thms ctxt) def_thms_opt
    val mem_locale_opt' = Option.map (Locale.check (Proof_Context.theory_of ctxt)) mem_locale_opt
  in
    (scope', tm, def_thms_opt', mem_locale_opt')
  end
(*
fun dp_interpretation_cmd args lthy =
  let
    val (scope, tm, _, mem_locale_opt) = prep_params args lthy
    val scope_name = Binding.name_of scope
  in
    case mem_locale_opt of
      NONE => lthy
    | SOME x => dp_interpretation x scope_name (Transform_Misc.uncurry tm) lthy
  end
*)

fun do_monadify heap_name scope tm mem_locale_opt def_thms_opt lthy =
  let
    val monad_consts = Transform_Const.get_monad_const heap_name
    val scope_name = Binding.name_of scope

    val memoizer_opt = if is_none mem_locale_opt then NONE else
      SOME (Transform_Misc.locale_term lthy scope_name "checkmem")

    val old_info_opt = Function_Common.import_function_data tm lthy
    val old_defs_opt = [
      K def_thms_opt,
      K (Option.mapPartial #simps old_info_opt)
    ] |> Library.get_first (fn x => x ())

    val old_defs = case old_defs_opt of
      SOME defs => defs
    | NONE => raise TERM("no definition", [tm])

    val ((_, old_defs_imported), ctxt') = lthy
      |> fold Variable.declare_thm old_defs
      |> Variable.import true old_defs
(*
    val new_bind = Binding.suffix_name "\<^sub>T'" scope
    val new_bindT = Binding.suffix_name "\<^sub>T" scope
*)
    val new_bind = Binding.suffix_name "'" scope
    val new_bindT = scope

    fun dest_def (def, def_imported) =
      let
        val def_imported_meta = def_imported |> Local_Defs.meta_rewrite_rule ctxt'
        val eqs = def_imported_meta |> Thm.full_prop_of
        val (head, _) = Logic.dest_equals eqs |> fst |> Transform_Misc.behead tm

        (*val _ = if Term.aconv_untyped (head, tm) then () else raise THM("invalid definition", 0, [def])*)
        val t = Term.lambda_name (Binding.name_of new_bind, head) eqs
        val ((t_name, _), eqs') = Term.dest_abs_global t
        val _ = @{assert} (t_name = Binding.name_of new_bind)

        (*val eqs' = Term.subst_atomic [(head, Free (Binding.name_of new_bind, fastype_of head))] eqs*)
        val (rhs_conv, eqsT, n_args) = Transform_Term.lift_equation monad_consts ctxt' (Logic.dest_equals eqs') memoizer_opt
        val def_meta' = def |> Local_Defs.meta_rewrite_rule ctxt' |> Conv.fconv_rule (Conv.arg_conv (rhs_conv ctxt'))

        val def_meta_simped = def_meta'
          |> Conv.fconv_rule (
               Transform_Term.repeat_sweep_conv (K Transform_Term.rewrite_pureapp_beta_conv) ctxt'
             )
(*
        val eqsT_simped = eqsT
          |> Syntax.check_term ctxt'
          |> Thm.cterm_of ctxt'
          |> Transform_Term.repeat_sweep_conv (K Transform_Term.rewrite_app_beta_conv) ctxt'
          |> Thm.full_prop_of |> Logic.dest_equals |> snd
*)

      in ((def_meta_simped, eqsT), n_args) end

    val ((old_defs', new_defs_raw), n_args) =
      map dest_def (old_defs ~~ old_defs_imported)
      |> split_list |>> split_list
      ||> Transform_Misc.the_element

    val new_defs = Syntax.check_props lthy new_defs_raw |> map (fn eqsT => eqsT
      |> Thm.cterm_of lthy
      |> Transform_Term.repeat_sweep_conv (K (#rewrite_app_beta_conv monad_consts)) lthy
      |> Thm.full_prop_of |> Logic.dest_equals |> snd)

    (*val _ = map (Pretty.writeln o Syntax.pretty_term @{context} o Thm.full_prop_of) old_defs'*)
    (*val (new_defs, lthy) = Variable.importT_terms new_defs lthy*)

    val (new_info, lthy1) = Transform_Misc.add_function new_bind new_defs lthy
    val replay_tac = case old_info_opt of
      NONE => no_tac
    | SOME info => Transform_Tactic.totality_replay_tac info new_info lthy1
    val totality_tac =
      replay_tac
      ORELSE (Function_Common.termination_prover_tac false lthy1
        THEN Transform_Tactic.my_print_tac "termination by default prover")

    val (new_info, lthy2) = Function.prove_termination NONE totality_tac lthy1
    val new_def' = new_info |> #simps |> the

    val head' = new_info |> #fs |> the_single
    val headT = Transform_Term.wrap_head monad_consts head' n_args |> Syntax.check_term lthy2
    val ((headTC, (_, new_defT)), lthy) = Local_Theory.define ((new_bindT, NoSyn), ((Thm.def_binding new_bindT,[]), headT)) lthy2

    val lthy3 = Transform_Data.commit_dp_info (#monad_name monad_consts) ({
      old_head = tm,
      new_head' = head',
      new_headT = headTC,

      old_defs = old_defs',
      new_def' = new_def',
      new_defT = new_defT
    }) lthy

    val _ = Proof_Display.print_consts true (Position.thread_data ()) lthy3 (K false) [
      (Binding.name_of new_bind, Term.type_of head'),
      (Binding.name_of new_bindT, Term.type_of headTC)]
  in lthy3 end

fun gen_dp_monadify prep_term args lthy =
  let
    val (scope, tm, def_thms_opt, mem_locale_opt) = prep_params args lthy
(*
    val memoizer_opt = memoizer_scope_opt |> Option.map (fn memoizer_scope =>
      Syntax.read_term lthy (Long_Name.qualify memoizer_scope Transform_Const.checkmemVN))
    val _ = memoizer_opt |> Option.map (fn memoizer =>
      if Term.aconv_untyped (head_of memoizer, @{term mem_defs.checkmem})
        then () else raise TERM("invalid memoizer", [the memoizer_opt]))
*)
  in
    do_monadify "state" scope tm mem_locale_opt def_thms_opt lthy
  end

val dp_monadify_cmd = gen_dp_monadify Syntax.read_term

fun dp_fun_part1_cmd ((scope, tm_str), (mem_locale_instance_opt)) lthy =
  let
    val scope_name = Binding.name_of scope
    val tm = Syntax.read_term lthy tm_str
    val _ = if is_Free tm then warning ("Free term: " ^ (Syntax.pretty_term lthy tm |> Pretty.string_of)) else ()
    val mem_locale_opt' = Option.map (Locale.check (Proof_Context.theory_of lthy) o (snd o fst)) mem_locale_instance_opt

    val lthy1 = case mem_locale_instance_opt of
      NONE => lthy
    | SOME ((standard_proof, locale_name), instance) =>
      let
        val locale_name = Locale.check (Proof_Context.theory_of lthy) locale_name
        val instance = map (apsnd (Syntax.read_term lthy)) instance
      in
        dp_interpretation standard_proof locale_name instance scope_name (Transform_Misc.uncurry tm) lthy
      end
  in
    Transform_Data.add_tmp_cmd_info (Binding.reset_pos scope, tm, mem_locale_opt') lthy1
  end

fun dp_fun_part2_cmd (heap_name, def_thms_str) lthy =
  let
    val {scope, head=tm, locale=locale_opt, dp_info=dp_info_opt} = Transform_Data.get_last_cmd_info lthy
    val _ = if is_none dp_info_opt then () else raise TERM("already monadified", [tm])
    val def_thms = Attrib.eval_thms lthy def_thms_str
  in
    do_monadify heap_name scope tm locale_opt (SOME def_thms) lthy
  end

fun dp_correct_cmd lthy =
  let
    val {scope, head=tm, locale=locale_opt, dp_info=dp_info_opt} = Transform_Data.get_last_cmd_info lthy
    val dp_info = case dp_info_opt of SOME x => x | NONE => raise TERM("not yet monadified", [tm])
    val _ = if is_some locale_opt then () else raise TERM("not interpreted yet", [tm])

    val scope_name = Binding.name_of scope
    val consistentDP = Transform_Misc.locale_term lthy scope_name "consistentDP"
    val dpT' = #new_head' dp_info
    val dpT'_curried = dpT' |> Transform_Misc.uncurry
    val goal_pat = consistentDP $ dpT'_curried
    val goal_prop = Syntax.check_term lthy (HOLogic.mk_Trueprop goal_pat)

    val tuple_pat = type_of dpT' |> strip_type |> fst |> length
      |> Name.invent_list [] "a"
      |> map (fn s => Var ((s, 0), TVar ((s, 0), @{sort type})))
      |> HOLogic.mk_tuple
      |> Thm.cterm_of lthy

    val memoized_thm_opt = Transform_Misc.locale_thms lthy scope_name "memoized" |> the_single |> SOME
      handle ERROR msg => (warning msg; NONE)
    val memoized_thm'_opt = memoized_thm_opt
      |> Option.map (Drule.infer_instantiate' lthy [NONE, SOME tuple_pat])

    val crel_thm_name = "crel"
    val memoized_thm_name = "memoized_correct"

    fun afterqed result lthy1 =
      let
        val [[crel_thm]] = result

        val (crel_thm_binds, lthy2) = lthy1
          |> Local_Theory.note ((Binding.qualify_name true scope crel_thm_name, []), [crel_thm])

        val _ = Proof_Display.print_theorem (Position.thread_data ()) lthy2 crel_thm_binds
      in
        case memoized_thm'_opt of
          NONE => lthy2
        | SOME memoized_thm' =>
            let
              val (memoized_thm_binds, lthy3) = lthy2
                |> Local_Theory.note
                  ((Binding.qualify_name true scope memoized_thm_name, []),
                    [(crel_thm RS memoized_thm') |> Local_Defs.unfold lthy @{thms prod.case}])
              val _ = Proof_Display.print_theorem (Position.thread_data ()) lthy3 memoized_thm_binds
            in lthy3 end
      end
  in
    Proof.theorem NONE afterqed [[(goal_prop, [])]] lthy
  end

end
