(*  Title:      ML_Unification/first_order_unification.ML
    Author:     Kevin Kappelmann, Paul Bachmann

Proof-producing first-order E-unification.
*)
signature FIRST_ORDER_UNIFICATION =
sig
  include HAS_LOGGER

  (* E-matching *)
  (*precondition: types of terms are matched*)
  val gen_e_match : Unification_Base.term_type_matcher * Envir_Normalisation.type_normaliser ->
    Unification_Base.e_matcher
  val gen_match_args_match : Unification_Base.term_type_matcher * Envir_Normalisation.type_normaliser
  val gen_match_args_unif : Unification_Base.term_type_matcher * Envir_Normalisation.type_normaliser
  val e_match : Unification_Base.e_matcher
  val match : Unification_Base.matcher
  val norms_match : Unification_Base.normalisers

  (* E-unification *)
  (*precondition: types of terms are unified*)
  val e_unify : Unification_Base.e_unifier
  val unify : Unification_Base.unifier
  val norms_unify : Unification_Base.normalisers
end

structure First_Order_Unification : FIRST_ORDER_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "First_Order_Unification"

(* shared utils *)
structure UBase = Unification_Base
structure Util = Unification_Util
structure Norm = Envir_Normalisation
structure Comb = Unification_Combinator

exception FALLBACK

(*check if sequence is empty or raise FALLBACK exception*)
fun seq_try sq = General_Util.seq_try FALLBACK sq

(* E-matching *)
fun gen_e_match (match_term_types, norm_type_rec) match_theory binders ctxt pt env = Seq.make (fn _ =>
  let
    val norm_term_types = Norm.norm_term_types norm_type_rec
    val norm_thm_types = Norm.norm_thm_types norm_type_rec
    (*norm_pt is not optimal: it doesn't normalise types in case of matching in the logger output*)
    val norm_pt = apfst o Same.commit o Norm.gen_norm_term_match norm_type_rec
    fun rigid_rigid ctxt p t env = Util.rigid_rigid (K o K I) ctxt p t env |> seq_try
    (*standard first-order matcher that calls match_theory on failure*)
    fun match binders ctxt (pt as (p, t)) (env as Envir.Envir {tenv,...}) = (case pt of
        (Abs absp, Abs abst) =>
          Util.abstract_abstract norm_term_types match binders ctxt absp abst env |> seq_try
      (*eta-expand on the fly*)
      | (Abs absp, _) => Util.abstract_left norm_term_types match binders ctxt absp t env |> seq_try
      | (_, Abs abst) => Util.abstract_right norm_term_types match binders ctxt p abst env |> seq_try
      | (Bound i, Bound j) => Util.bound_bound binders ctxt (i, j) |> Seq.map (pair env)
      | (Free f, Free _) => rigid_rigid ctxt f t env
      | (Const c, Const _) => rigid_rigid ctxt c t env
      | (f $ x, g $ y) => ((match_term_types (Binders.binder_types binders) ctxt (x, y) env
          |> Util.comb_comb norm_thm_types (match binders) ctxt (f, x) (g, y) |> seq_try)
          handle UBase.UNIF => raise FALLBACK)
      | (Var (x, Tx), _) => (case Envir.lookup1 tenv (x, Tx) of
          NONE =>
            if Term.is_open t then
              (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
                  Pretty.str "Failed to match (open term) ",
                  Util.pretty_unif_problem binders ctxt (norm_pt env pt)
                ] |> Pretty.string_of);
              raise FALLBACK)
            else Seq.single (Envir.update ((x, Tx), t) env, UBase.reflexive_term ctxt t)
        | SOME p' => if (op aconv) (apply2 (Same.commit Term_Normalisation.beta_eta_short) (p', t))
            then Seq.single (env, UBase.reflexive_term ctxt t)
            else raise FALLBACK)
      | _ => raise FALLBACK)
      handle FALLBACK => (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
            Pretty.str "First-order matching failed.",
            Util.pretty_call_theory_match binders ctxt (norm_pt env pt)
          ] |> Pretty.block |> Pretty.string_of);
        match_theory binders ctxt pt env)
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "First-order E-matching ",
        Util.pretty_unif_problem binders ctxt (norm_pt env pt)
      ] |> Pretty.string_of);
    match binders ctxt pt env)
    |> Seq.pull
  end)

(*standard first-order matching*)
val gen_match_args_match = (Util.match_term_types, K I)
val gen_match_args_unif = (Util.unify_term_types, Norm.norm_type_unif)
val e_match = gen_e_match gen_match_args_match
val match = e_match Comb.fail_match
val norms_match = Util.eta_short_norms_match

(* E-unification *)

(*occurs check*)
fun occurs v (Var (x, _)) = x = v
  | occurs v (s $ t) = occurs v s orelse occurs v t
  | occurs v (Abs (_, _, t)) = occurs v t
  | occurs _ _ = false

fun e_unify unify_theory binders ctxt st env = Seq.make (fn _ =>
  let
    val norm_type = Norm.norm_type_unif
    val norm_term_types = Norm.norm_term_types norm_type
    val norm_thm_types = Norm.norm_thm_types norm_type
    val norm_st = apply2 o Same.commit o Norm.norm_term_unif
    fun rigid_rigid ctxt t n env = Util.rigid_rigid (K o K I) ctxt t n env |> seq_try
    (*standard first-order unifier that calls unify_theory on failure*)
    fun unif binders ctxt (st as (s, t)) env = (case st of
        (Abs abss, Abs abst) =>
          Util.abstract_abstract norm_term_types unif binders ctxt abss abst env |> seq_try
      (*eta-expand on the fly*)
      | (Abs abss, _) => Util.abstract_left norm_term_types unif binders ctxt abss t env |> seq_try
      | (_, Abs abst) => Util.abstract_right norm_term_types unif binders ctxt s abst env |> seq_try
      | (Bound i, Bound j) => Util.bound_bound binders ctxt (i, j) |> Seq.map (pair env)
      | (Free f, Free _) => rigid_rigid ctxt f t env
      | (Const c, Const _) => rigid_rigid ctxt c t env
      | (f $ x, g $ y) => ((Util.unify_term_types (Binders.binder_types binders) ctxt (x, y) env
          |> Util.comb_comb norm_thm_types (unif binders) ctxt (f, x) (g, y) |> seq_try)
          handle UBase.UNIF => raise FALLBACK (*types do not unify*))
      | (Var (x, Tx), _) => let val norm = Norm.norm_term_unif env
          in
            unif binders ctxt (norm s, t) env
            handle Same.SAME => let val t = Same.commit norm t
              in
                if Term.is_open t then
                  (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
                      Pretty.str "Failed to unify (open term) ",
                      Util.pretty_unif_problem binders ctxt (norm_st env st)
                    ] |> Pretty.string_of);
                  raise FALLBACK)
                else
                  let val vars_eq = is_Var t andalso x = fst (dest_Var t)
                  in
                    if not vars_eq andalso occurs x t then
                      (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
                          Pretty.str "Failed to unify (occurs check) ",
                          Util.pretty_unif_problem binders ctxt (norm_st env st)
                        ] |> Pretty.string_of);
                      raise FALLBACK)
                    else (not vars_eq ? Envir.vupdate ((x, Tx), t)) env
                      |> rpair (UBase.reflexive_term ctxt t)
                      |> Seq.single
                  end
              end
          end
       | (_, Var _) => Comb.flip_unifier unif binders ctxt st env
      | _ => raise FALLBACK)
      handle FALLBACK =>
        (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
            Pretty.str "First-order unification failed.",
            Util.pretty_call_theory_unif binders ctxt (norm_st env st)
          ] |> Pretty.block |> Pretty.string_of);
        unify_theory binders ctxt st env)
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "First-order E-unifying ",
        Util.pretty_unif_problem binders ctxt (norm_st env st)
      ] |> Pretty.string_of);
    unif binders ctxt st env)
    |> Seq.pull
  end)

(*standard first-order unification*)
val unify = e_unify Comb.fail_unify
val norms_unify = Util.eta_short_norms_unif

end
