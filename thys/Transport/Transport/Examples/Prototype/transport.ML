(*  Title:      Transport/transport.ML
    Author:     Kevin Kappelmann, Paul Bachmann

Prototype for Transport. See README.md for future work.
*)

(*TODO: signature*)

structure Transport =
struct

structure Util = Transport_Util

(*definitions used by Transport that need to be folded before a PER proof and unfolded after
success.*)
structure Transport_Defs = Named_Thms(
  val name = @{binding "trp_def"}
  val description = "Definitions used by Transport"
)
val _ = Theory.setup Transport_Defs.setup

(* simplifying definitions *)

val simp_rhs = Simplifier.rewrite #> Conversion_Util.rhs_conv #> Conversion_Util.thm_conv

(*simplifies the generated definition of a transported term*)
fun simp_transported_def ctxt simps y_def =
  let
    val ctxt = ctxt addsimps simps
    val y_def_eta_expanded = Util.equality_eta_expand ctxt "x" y_def
  in apply2 (simp_rhs ctxt) (y_def, y_def_eta_expanded) end

(* resolution setup *)

val any_unify_trp_hints_resolve_tac = Unify_Resolve_Base.unify_resolve_any_tac
  Transport_Mixed_Unification.norms_first_higherp_first_comb_higher_unify
  Transport_Mixed_Unification.first_higherp_first_comb_higher_unify

fun get_theorems_tac f get_theorems ctxt = f (get_theorems ctxt) ctxt
val get_theorems_resolve_tac = get_theorems_tac any_unify_trp_hints_resolve_tac

val _ = Theory.setup (
    Method.setup @{binding trp_hints_resolve}
    (Attrib.thms >> (SIMPLE_METHOD' oo any_unify_trp_hints_resolve_tac))
    "Resolution with unification hints for Transport"
  )

(* PER equivalence prover *)

(*introduction rules*)
structure PER_Intros = Named_Thms(
  val name = @{binding "per_intro"}
  val description = "Introduction rules for per_prover"
)
val _ = Theory.setup PER_Intros.setup

fun per_prover_tac ctxt = REPEAT_ALL_NEW (get_theorems_resolve_tac PER_Intros.get ctxt)

val _ = Theory.setup (
    Method.setup @{binding per_prover}
    (Scan.succeed (SIMPLE_METHOD' o per_prover_tac))
    "PER prover for Transport"
  )

(* domain prover *)

structure Transport_in_dom = Named_Thms(
  val name = @{binding "trp_in_dom"}
  val description = "In domain theorems for Transport"
)
val _ = Theory.setup Transport_in_dom.setup

(*discharges the @{term "L x x'"} goals by registered lemmas*)
fun transport_in_dom_prover_tac ctxt = get_theorems_resolve_tac Transport_in_dom.get ctxt

val _ = Theory.setup (
    Method.setup @{binding trp_in_dom_prover}
    (Scan.succeed (SIMPLE_METHOD' o transport_in_dom_prover_tac))
    "in_dom prover for Transport"
  )


(* blackbox prover *)

(*first derives the PER equivalence, then looks for registered domain lemmas.*)
fun unfold_tac thms ctxt = simp_tac (clear_simpset ctxt addsimps thms)
val unfold_transport_defs_tac = get_theorems_tac unfold_tac Transport_Defs.get

fun transport_prover ctxt i =
  per_prover_tac ctxt i
  THEN TRY (SOMEGOAL
    (TRY o unfold_transport_defs_tac ctxt
    THEN' transport_in_dom_prover_tac ctxt)
  )

val _ = Theory.setup (
    Method.setup @{binding trp_prover}
    (Scan.succeed (SIMPLE_METHOD' o transport_prover))
    "Blackbox prover for Transport"
  )

(* whitebox prover intro rules *)

structure Transport_Related_Intros = Named_Thms(
  val name = @{binding "trp_related_intro"}
  val description = "Introduction rules for Transport whitebox proofs"
)
val _ = Theory.setup Transport_Related_Intros.setup


(* relator rewriter *)

(*rewrite rules to simplify the derived Galois relator*)
structure Transport_Relator_Rewrites = Named_Thms(
  val name = @{binding "trp_relator_rewrite"}
  val description = "Rewrite rules for relators used by Transport"
)
val _ = Theory.setup Transport_Relator_Rewrites.setup

(*simple rewrite tactic for Galois relators*)
fun per_simp_prover ctxt thm =
  let
    val prems = Thm.cprems_of thm
    val per_prover_tac = per_prover_tac ctxt
    fun prove_prem prem = Goal.prove_internal ctxt [] prem (fn _ => HEADGOAL per_prover_tac)
  in try (map prove_prem) prems |> Option.map (curry (op OF) thm) end
fun transport_relator_rewrite ctxt thm =
  let
    val transport_defs = Transport_Defs.get ctxt
    val transport_relator_rewrites = Transport_Relator_Rewrites.get ctxt
    val ctxt = (clear_simpset ctxt) addsimps transport_relator_rewrites
  in
    Local_Defs.fold ctxt transport_defs thm
    |> Raw_Simplifier.rewrite_thm (false, false, false) per_simp_prover ctxt
  end
fun transport_relator_rewrite_tac ctxt =
  EqSubst.eqsubst_tac ctxt [0] (Transport_Relator_Rewrites.get ctxt)
  THEN_ALL_NEW TRY o SOLVED' (per_prover_tac ctxt)

val _ = Theory.setup (
    Method.setup @{binding trp_relator_rewrite}
    (Scan.succeed (SIMPLE_METHOD' o transport_relator_rewrite_tac))
    "Rewrite Transport relator"
  )


(* term transport command *)

(*parsing*)
@{parse_entries (struct) PA [L, R, x, y]}
val parse_cmd_entries =
  let
    val parse_value = PA.parse_entry Parse.term Parse.term Parse.term Parse.term
    val parse_entry = Parse_Key_Value.parse_entry PA.parse_key Parse_Util.eq parse_value
  in PA.parse_entries_required Parse.and_list1 [PA.key PA.x] parse_entry (PA.empty_entries ()) end

(*some utilities to destruct terms*)
val transport_per_start_thm = @{thm "transport.transport_per_start"}
val related_if_transport_per_thm = @{thm "transport.left_Galois_if_transport_per"}
fun dest_transport_per \<^Const_>\<open>transport.transport_per S T for L R l r x y\<close> =
  ((S, T), (L, R, l, r, x, y))
val dest_transport_per_y = dest_transport_per #> (fn (_, (_, _, _, _, _, y)) => y)

fun mk_hom_Galois Ta Tb L R r x y =
  \<^Const>\<open>galois_rel.Galois Ta Ta Tb Tb for L R r x y\<close>
fun dest_hom_Galois \<^Const_>\<open>galois_rel.Galois Ta _ Tb _ for L R r x y\<close> =
  ((Ta, Tb), (L, R, r, x, y))
val dest_hom_Galois_y = dest_hom_Galois #> (fn (_, (_, _, _, _, y)) => y)

(*bindings for generated theorems and definitions*)
val binding_transport_per = \<^binding>\<open>transport_per\<close>
val binding_per = \<^binding>\<open>per\<close>
val binding_in_dom = \<^binding>\<open>in_dom\<close>
val binding_related = \<^binding>\<open>related\<close>
val binding_related_rewritten = \<^binding>\<open>related'\<close>
val binding_def_simplified = \<^binding>\<open>eq\<close>
val binding_def_eta_expanded_simplified = \<^binding>\<open>app_eq\<close>

fun note_facts (binding, mixfix) ctxt related_thm y binding_thms_attribs =
  let
    val ((_, (_, y_def)), ctxt) = Util.create_local_theory_def (binding, mixfix) [] y ctxt
    (*create simplified definition theorems*)
    val transport_defs = Transport_Defs.get ctxt
    val (y_def_simplified, y_def_eta_expanded_simplified) =
      simp_transported_def ctxt transport_defs y_def
    (*create relatedness theorems*)
    val related_thm_rewritten = transport_relator_rewrite ctxt related_thm
    fun prepare_fact (suffix, thm, attribs) =
      let
        val binding = (Util.add_suffix binding suffix, [])
        val ctxt = (clear_simpset ctxt) addsimps transport_defs
        val folded_thm =
          (*fold definition of transported term*)
          Local_Defs.fold ctxt [y_def] thm
          (*simplify other transport definitions in theorem*)
          |> (Simplifier.rewrite ctxt |> Conversion_Util.thm_conv)
        val thm_attribs = ([folded_thm], attribs)
      in (binding, [thm_attribs]) end
    val facts = map prepare_fact ([
        (binding_related, related_thm, []),
        (binding_related_rewritten, related_thm_rewritten,
          [Util.attrib_to_src (Binding.pos_of binding) Transport_Related_Intros.add]),
        (binding_def_simplified, y_def_simplified, []),
        (binding_def_eta_expanded_simplified, y_def_eta_expanded_simplified, [])
      ] @ binding_thms_attribs)
  in Local_Theory.notes facts ctxt |> snd end

(*black-box transport as described in the Transport paper*)
fun after_qed_blackbox (binding, mixfix) [thms as [per_thm, in_dom_thm]] ctxt =
  let
    val transport_per_thm = List.foldl (op INCR_COMP) transport_per_start_thm thms
    (*fix possibly occurring meta type variables*)
    val ((_, [transport_per_thm]), ctxt) = Variable.importT [transport_per_thm] ctxt
    val y = Util.real_thm_concl transport_per_thm |> dest_transport_per_y

    val related_thm = transport_per_thm INCR_COMP related_if_transport_per_thm
    val binding_thms = [
        (binding_transport_per, transport_per_thm, []),
        (binding_per, per_thm, []),
        (binding_in_dom, in_dom_thm,
          [Util.attrib_to_src (Binding.pos_of binding) Transport_in_dom.add])
      ]
  in note_facts (binding, mixfix) ctxt related_thm y binding_thms end

(*experimental white-box transport support*)
fun after_qed_whitebox (binding, mixfix) [[related_thm]] ctxt =
  let
    (*fix possibly occurring meta type variables*)
    val ((_, [related_thm]), ctxt) = Variable.importT [related_thm] ctxt
    val y = Util.real_thm_concl related_thm |> dest_hom_Galois_y
  in note_facts (binding, mixfix) ctxt related_thm y [] end

fun setup_goals_blackbox ctxt (L, R, cx) maxidx =
  let
    (*check*)
    val [cL, cR] = Syntax.check_terms ctxt [L, R] |> map (Thm.cterm_of ctxt)
    (*instantiate theorem*)
    val transport_per_start_thm = Thm.incr_indexes (maxidx + 1) transport_per_start_thm
    val args = [SOME cL, SOME cR, NONE, NONE, SOME cx]
    val transport_per_start_thm = Drule.infer_instantiate' ctxt args transport_per_start_thm
    val transport_defs = Transport_Defs.get ctxt
    val goals = Local_Defs.fold ctxt transport_defs transport_per_start_thm
      |> Thm.prems_of
      |> map (rpair [])
  in goals end

fun setup_goals_whitebox ctxt (yT, L, R, cx, y) maxidx =
  let
    val (r, _) = Term_Util.fresh_var "r" dummyT maxidx
    (*check*)
    val Galois = mk_hom_Galois (Thm.typ_of_cterm cx) yT L R r (Thm.term_of cx) y
      |> Syntax.check_term ctxt
    val goal = Util.mk_judgement Galois |> rpair []
  in [goal] end

fun setup_proof ((((binding, opt_yT, mixfix), params), unfolds), whitebox) lthy =
  let
    val ctxt = Util.set_proof_mode_schematic lthy
    (*type of transported term*)
    val yT = Option.map (Syntax.read_typ ctxt) opt_yT |> the_default dummyT
    (*theorems to unfold*)
    val unfolds = map (Proof_Context.get_fact ctxt o fst) unfolds |> flat
    (*term to transport*)
    val cx =
      (**read term**)
      Syntax.read_term ctxt (PA.get_x params) |> Thm.cterm_of ctxt
      (**unfold passed theorems**)
      |> Drule.cterm_rule (Local_Defs.unfold ctxt unfolds)
    (*transport relations and transport term goal*)
    val ([L, R, y], maxidx) =
      let
        (**configuration**)
        val opts = [PA.get_L_safe params, PA.get_R_safe params, PA.get_y_safe params]
        val opts_default_names = ["L", "R", "y"]
        val opts_constraints =
          [Util.mk_hom_rel_type (Thm.typ_of_cterm cx), Util.mk_hom_rel_type yT, yT]
          |> map Type.constraint
        (**parse**)
        val opts = map (Syntax.parse_term ctxt |> Option.map) opts
        val params_maxidx = Util.list_max (the_default ~1 o Option.map Term.maxidx_of_term)
          (Thm.maxidx_of_cterm cx) opts
        fun create_var (NONE, n) maxidx =
              Term_Util.fresh_var n dummyT params_maxidx ||> Integer.max maxidx
          | create_var (SOME t, _) created = (t, created)
        val (ts, maxidx) =
          fold_map create_var (opts ~~ opts_default_names) params_maxidx
          |>> map2 I opts_constraints
      in (ts, maxidx) end
    (*initialise goals and callback*)
    val (goals, after_qed) = if whitebox
      then (setup_goals_whitebox ctxt (yT, L, R, cx, y) maxidx, after_qed_whitebox)
      (*TODO: consider y in blackbox proofs*)
      else (setup_goals_blackbox ctxt (L, R, cx) maxidx, after_qed_blackbox)
  in
    Proof.theorem NONE (after_qed (binding, mixfix)) [goals] ctxt
    |> Proof.refine_singleton Util.split_conjunctions
  end

val parse_strings =
  (*binding for transported term*)
  Parse_Spec.constdecl
  (*other params*)
  -- parse_cmd_entries
  (*optionally pass unfold theorems in case of white-box transports*)
  -- Scan.optional (Parse.reserved "unfold" |-- Parse.thms1) []
  (*use a bang "!" to start white-box transport mode (experimental)*)
  -- Parse.opt_bang

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>trp_term\<close>
    "Transport term" (parse_strings >> setup_proof)


(* experimental white-box prover *)

val any_match_resolve_related_tac =
  let fun unif binders = Higher_Ordern_Pattern_First_Decomp_Unification.e_match
    Unification_Util.match_types unif Unification_Combinator.fail_unify binders
  in
    Unify_Resolve_Base.unify_resolve_any_tac
      Higher_Ordern_Pattern_First_Decomp_Unification.norms_match unif
  end

val related_comb_tac = any_match_resolve_related_tac @{thms related_Fun_Rel_combI}
val related_lambda_tac = any_match_resolve_related_tac @{thms related_Fun_Rel_lambdaI}
val related_tac = any_unify_trp_hints_resolve_tac
val related_assume_tac = assume_tac

fun mk_transport_related_tac cc_comb cc_lambda ctxt =
  let
    val transport_related_intros = Transport_Related_Intros.get ctxt
    val related_tac = related_tac transport_related_intros ctxt
    val comb_tac = related_comb_tac ctxt
    val lambda_tac = related_lambda_tac ctxt
    val assume_tac = related_assume_tac ctxt
  in
    Tactic_Util.CONCAT' [
      related_tac,
      cc_comb comb_tac,
      cc_lambda lambda_tac,
      assume_tac
    ]
  end
val transport_related_step_tac =
  let fun cc_comb tac i = tac i
    THEN prefer_tac i
    THEN prefer_tac (i + 1)
  in mk_transport_related_tac cc_comb I end
fun transport_related_tac ctxt =
  let
    fun transport_related_tac cc =
      let
        fun cc_comb tac = tac THEN_ALL_NEW TRY o cc
        fun cc_lambda tac = tac THEN' TRY o cc
      in mk_transport_related_tac cc_comb cc_lambda ctxt end
    fun fix tac i thm = tac (fix tac) i thm
  in fix transport_related_tac end

val _ = Theory.setup (
    Method.setup @{binding trp_related_prover}
    (Scan.succeed (SIMPLE_METHOD' o transport_related_tac))
    "Relatedness prover for Transport"
  )

fun instantiate_tac name ct ctxt =
  PRIMITIVE (Drule.infer_instantiate_types ctxt [((name, Thm.typ_of_cterm ct), ct)])
  |> CHANGED

val map_dummyT = Term.map_types (K dummyT)

fun mk_term_skeleton maxidx t =
  let
    val consts = Term.add_consts t []
    val (vars, _) = fold_map (uncurry Term_Util.fresh_var o apfst Long_Name.base_name) consts maxidx
    val t' = Term.subst_atomic (map2 (pair o Const) consts vars) t
  in t' end

fun instantiate_skeleton_tac ctxt =
  let fun tac ct =
    let
      val (x, y) = Transport_Util.cdest_judgement ct |> Thm.dest_binop
      val default_sort = Proof_Context.default_sort ctxt
      val skeleton =
        mk_term_skeleton (Thm.maxidx_of_cterm ct) (Thm.term_of x)
        |> map_dummyT
        |> Type.constraint (Thm.typ_of_cterm y)
        |> Syntax.check_term (Util.set_proof_mode_pattern ctxt)
        (*add sort constraints for type variables*)
        |> Term.map_types (Term.map_atyps (map_type_tvar (fn (n, _) => TVar (n, default_sort n))))
        |> Thm.cterm_of ctxt
    in instantiate_tac (Thm.term_of y |> dest_Var |> fst) skeleton ctxt end
  in Tactic_Util.CSUBGOAL_DATA I (K o tac) end

fun transport_whitebox_tac ctxt =
  instantiate_skeleton_tac ctxt
  THEN' transport_related_tac ctxt
  THEN_ALL_NEW (
    TRY o REPEAT1 o transport_relator_rewrite_tac ctxt
    THEN' TRY o any_unify_trp_hints_resolve_tac @{thms refl} ctxt
  )

val _ = Theory.setup (
    Method.setup @{binding trp_whitebox_prover}
    (Scan.succeed (SIMPLE_METHOD' o transport_whitebox_tac))
    "Whitebox prover for Transport"
  )


end