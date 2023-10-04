(*  Title:      ML_Unification/tests_base.ML
    Author:     Kevin Kappelmann

Basic setup for ML unifier tests.

TODO: generalise for unifiers with open terms; currently, all tests work with closed terms.
*)
signature UNIFICATION_TESTS_BASE =
sig

  structure Hints : TERM_INDEX_UNIFICATION_HINTS
  val add_hint : Unification_Hints_Base.unif_hint -> Context.generic -> Context.generic
  val add_hints : thm list -> Proof.context -> Proof.context

  val term_gen : Proof.context -> int -> int -> int * int * int * int ->
    (int -> int -> int SpecCheck_Generator.gen) -> term SpecCheck_Generator.gen
  val term_pair_gen : Proof.context -> int -> int -> int * int * int * int ->
    (int -> int -> int SpecCheck_Generator.gen) ->
    (term * term) SpecCheck_Generator.gen

  val term_gen' : Proof.context -> int -> int -> int * int * int * int -> int ->
    int -> term SpecCheck_Generator.gen
  val term_pair_gen' : Proof.context -> int -> int -> int * int * int * int ->
    int -> int -> (term * term) SpecCheck_Generator.gen

  val thms_correct : (Envir.env -> (term * term) -> (term * term)) ->
    Envir_Normalisation.thm_normaliser -> Proof.context -> Unification_Base.closed_unifier ->
    (term * term) SpecCheck_Property.pred

  val terms_unify : Proof.context -> Unification_Base.closed_unifier ->
    (term * term) SpecCheck_Property.pred

  val terms_unify_thms_correct : (Envir.env -> (term * term) -> (term * term)) ->
    Envir_Normalisation.thm_normaliser -> Proof.context -> Unification_Base.closed_unifier ->
    (term * term) SpecCheck_Property.pred

  val terms_unify_thms_correct_unif : Proof.context -> Unification_Base.closed_unifier ->
    (term * term) SpecCheck_Property.pred

  val terms_unify_thms_correct_match : Proof.context -> Unification_Base.closed_unifier ->
    (term * term) SpecCheck_Property.pred

  val check : (term * term, 'a) SpecCheck_Generator.gen_state -> string ->
    (term * term) SpecCheck_Property.prop ->
    (Proof.context, 'a) Lecker.test_state

  val check_thm : (Envir.env -> (term * term) -> (term * term)) -> Envir_Normalisation.thm_normaliser ->
    (term * term, 'a) SpecCheck_Generator.gen_state -> string ->
    Unification_Base.closed_unifier -> (Proof.context, 'a) Lecker.test_state

  val check_thm_unif : (term * term, 'a) SpecCheck_Generator.gen_state -> string ->
    Unification_Base.closed_unifier -> (Proof.context, 'a) Lecker.test_state

  val check_thm_match : (term * term, 'a) SpecCheck_Generator.gen_state -> string ->
    Unification_Base.closed_unifier -> (Proof.context, 'a) Lecker.test_state

  val check_list : (term * term) list -> string ->
    (term * term) SpecCheck_Property.prop -> Proof.context ->
    (term * term) Seq.seq

  val check_unit_tests_hints : (Envir.env -> (term * term) -> (term * term)) ->
    Envir_Normalisation.thm_normaliser -> (term * term) list -> bool -> thm list -> string ->
    Unification_Base.closed_unifier -> (Proof.context, 'a) Lecker.test_state

  val check_unit_tests_hints_unif : (term * term) list -> bool -> thm list -> string ->
    Unification_Base.closed_unifier -> (Proof.context, 'a) Lecker.test_state

  val check_unit_tests_hints_match : (term * term) list -> bool -> thm list -> string ->
    Unification_Base.closed_unifier -> (Proof.context, 'a) Lecker.test_state

end

structure Unification_Tests_Base : UNIFICATION_TESTS_BASE =
struct

structure Hints = Test_Unification_Hints

val add_hint = Test_Unification_Hints.add_hint_prio o rpair Prio.MEDIUM
fun add_hints thms ctxt = fold add_hint thms (Context.Proof ctxt) |> Context.proof_of

structure Gen = SpecCheck_Generator
structure UUtil = Unification_Util
structure Norm = Envir_Normalisation

fun term_num_args_gen nv ni weights num_args_gen h i =
  Gen.zip (Gen.aterm' (Gen.nonneg nv) (Gen.nonneg ni) weights) (num_args_gen h i)

fun term_gen ctxt nv ni weights num_args_gen =
  let val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
  in
    Gen.term_tree (term_num_args_gen nv ni weights num_args_gen)
    |> Gen.map (try (singleton (Variable.polymorphic ctxt') o Syntax.check_term ctxt'))
    |> Gen.filter is_some
    |> Gen.map the
  end

fun term_pair_gen ctxt nv ni weights num_args_gen =
  let
    val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
    val term_gen = Gen.term_tree (term_num_args_gen nv ni weights num_args_gen)
  in
    Gen.zip term_gen term_gen
    |> Gen.map (fn (s, t) => try (Variable.polymorphic ctxt' o Syntax.check_terms ctxt') [s, t])
    |> Gen.filter is_some
    |> Gen.map (fn SOME [s, t] => (s, t))
  end

fun num_args_gen max_h max_args h _ = if h > max_h then Gen.return 0 else Gen.nonneg max_args

fun term_gen' ctxt nv ni weights max_h max_args =
  term_gen ctxt nv ni weights (num_args_gen max_h max_args)

fun term_pair_gen' ctxt nv ni weights max_h max_args =
  term_pair_gen ctxt nv ni weights (num_args_gen max_h max_args)

fun show_termpair ctxt =
  let val pretty_term = Syntax.pretty_term ctxt
  in SpecCheck_Show.zip pretty_term pretty_term end

val shrink_termpair = SpecCheck_Shrink.product SpecCheck_Shrink.term SpecCheck_Shrink.none

fun thms_correct norm_terms norm_thm ctxt unif tp =
  let
    val env_thmq = unif ctxt tp (UUtil.empty_envir tp)
    fun thm_correct (env, thm) =
      let
        val (t1, t2) = norm_terms env tp
        val thm' = norm_thm ctxt env thm
        val (lhs, rhs) = Thm.concl_of thm' |> Logic.dest_equals
      in List.all Envir.aeconv [(t1, lhs), (t2, rhs)] andalso Thm.no_prems thm' end
  in List.all thm_correct (Seq.list_of env_thmq) end

fun terms_unify ctxt unif tp =
  UUtil.empty_envir tp
  |> unif ctxt tp
  |> General_Util.seq_is_empty
  |> not o fst

fun terms_unify_thms_correct norm_terms norm_thm ctxt unif tp =
  terms_unify ctxt unif tp andalso thms_correct norm_terms norm_thm ctxt unif tp

val terms_unify_thms_correct_unif = terms_unify_thms_correct
  (apply2 o Norm.beta_eta_short_norm_term_unif)
  (Norm.beta_eta_short_norm_thm Norm.norm_type_unif Norm.beta_eta_short_norm_term_unif)

val terms_unify_thms_correct_match = terms_unify_thms_correct
  (apfst o Norm.beta_norm_term_match)
  (*types are already normalised by matcher*)
  (Norm.beta_eta_short_norm_thm (K I) Norm.beta_norm_term_match)

fun check gen name prop ctxt =
  SpecCheck.check_shrink (show_termpair ctxt) shrink_termpair
    gen name prop ctxt

fun check_thm norm_terms norm_thm gen name unif ctxt = check gen ("Theorem correctness: " ^ name)
  (SpecCheck_Property.==> (terms_unify ctxt unif, thms_correct norm_terms norm_thm ctxt unif))
  ctxt

fun check_thm_unif norm_terms = check_thm
  (apply2 o Norm.beta_eta_short_norm_term_unif)
  (Norm.beta_eta_short_norm_thm Norm.norm_type_unif Norm.beta_eta_short_norm_term_unif)
  norm_terms

fun check_thm_match norm_terms = check_thm
  (apfst o Norm.beta_norm_term_match)
  (Norm.beta_eta_short_norm_thm (K I) Norm.beta_norm_term_match)
  norm_terms

fun check_list tests name prop ctxt =
  SpecCheck.check_list (show_termpair ctxt) tests name prop ctxt

fun check_unit_tests_hints norm_terms norm_thm tests should_succeed hints name unif ctxt s =
  let val ctxt' = add_hints hints ctxt
  in
    check_list tests name
      (SpecCheck_Property.prop
        (fn tp => terms_unify_thms_correct norm_terms norm_thm ctxt' unif tp = should_succeed))
      ctxt'
    |> K s
  end

fun check_unit_tests_hints_unif norm_terms = check_unit_tests_hints
  (apply2 o Norm.beta_eta_short_norm_term_unif)
  (Norm.beta_eta_short_norm_thm Norm.norm_type_unif Norm.beta_eta_short_norm_term_unif)
  norm_terms

fun check_unit_tests_hints_match norm_terms = check_unit_tests_hints
  (apfst o Norm.beta_norm_term_match)
  (Norm.beta_eta_short_norm_thm (K I) (K I))
  norm_terms

end
