(*  Title:      ML_Unification/simplifier_unification.ML
    Author:     Kevin Kappelmann

Solving equations for unification problems with the simplifier.
*)
signature SIMPLIFIER_UNIFICATION =
sig
  include HAS_LOGGER
  (*solves "SIMPS_TO s t \<equiv> rhs" via simplification of s when given a theorem
    "SIMPS_TO s t \<Longrightarrow> SIMPS_TO s t \<equiv> rhs"*)
  val SIMPS_TO_unify : thm -> Unification_Base.closed_unifier
  (*solves "SIMPS_TO_UNIF s t \<equiv> rhs" via simplification of s to s', followed by unification of
    "s' \<equiv>\<^sup>? t", when given a theorem "SIMPS_TO_UNIF s t \<Longrightarrow> SIMPS_TO_UNIF s t \<equiv> rhs"*)
  val SIMPS_TO_UNIF_unify : thm -> Unification_Base.normalisers ->
    Unification_Base.closed_unifier -> Unification_Base.closed_unifier
  (*solves "s \<equiv>\<^sup>? t" via simplification followed by unification*)
  val simp_unify : Unification_Base.normalisers -> Unification_Base.closed_unifier ->
    Unification_Base.closed_unifier
  (*solves "s \<equiv>\<^sup>? t" via simplification followed by unification; aborts if no progress was made
  during simplification*)
  val simp_unify_progress : (term * term -> bool) -> (Unification_Base.normalisers ->
    Unification_Base.closed_unifier -> Unification_Base.closed_unifier) ->
    Envir_Normalisation.term_normaliser -> Unification_Base.normalisers ->
    Unification_Base.e_unifier
end

structure Simplifier_Unification : SIMPLIFIER_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Simplifier_Unification"

structure Util = Tactic_Util

(*some "safe" solvers create instantiations via flex-flex pairs, which we disallow*)
val safe_simp_tac = Util.safe_simp_tac

fun match_tac ctxt = Tactic.match_tac ctxt o single

fun SIMPS_TO_unify preprocess_rule ctxt =
  let fun tac (tp as (lhs, _)) =
    if can Simps_To.dest_SIMPS_TO lhs
    then
      (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
          Pretty.str "Solving ",
          Syntax.pretty_term ctxt @{term SIMPS_TO},
          Pretty.str " unification problem ",
          Unification_Util.pretty_unif_problem ctxt tp
        ] |> Pretty.string_of);
      match_tac ctxt preprocess_rule
      THEN' Simps_To.SIMPS_TO_tac (safe_simp_tac ctxt) ctxt)
    else K no_tac
  in Tactic_Unification.unify (Tactic_Unification.env_tac_from_no_inst_tac o tac) ctxt end

fun SIMPS_TO_UNIF_env_thm_tac norms unif ctxt env tSIMPS_TO_UNIF state =
  let
    val tp = Simps_To_Unif.dest_SIMPS_TO_UNIF tSIMPS_TO_UNIF
    val conv = #conv norms
    fun norm_resolve (env, thm) =
      Tactic_Util.HEADGOAL (Unification_Util.inst_norm_subgoal (#inst_unif_thm norms) conv)
        ctxt env state
      |> Thm.elim_implies (Conversion_Util.apply_thm_conv conv thm)
      |> pair env
  in
    Simps_To_Unif.SIMPS_TO_UNIF_env_thmsq (safe_simp_tac ctxt) norms unif ctxt tp env
    |> Seq.map norm_resolve
  end

fun SIMPS_TO_UNIF_unify preprocess_rule norms unif ctxt =
  let fun tac (tp as (lhs, _)) i (env, state) =
    if can Simps_To_Unif.dest_SIMPS_TO_UNIF lhs
    then
      (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
          Pretty.str "Solving ",
          Syntax.pretty_term ctxt @{term SIMPS_TO_UNIF},
          Pretty.str " unification problem ",
          Unification_Util.pretty_unif_problem ctxt tp
        ] |> Pretty.string_of);
      match_tac ctxt preprocess_rule i state
      |> Seq.maps (SIMPS_TO_UNIF_env_thm_tac norms unif ctxt env lhs))
    else Seq.empty
  in Tactic_Unification.unify tac ctxt end

fun simp_unify norms unif ctxt =
  let
    val simp_tac = safe_simp_tac ctxt
    fun SIMPS_TO_UNIF_env_thm_tac' env i state = SIMPS_TO_UNIF_env_thm_tac norms unif ctxt env
      (Thm.cprem_of state i |> Thm.term_of) state
    fun eq_tac tp i (env, state) =
      (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Solving unification problem via simplification followed by unification ",
        Unification_Util.pretty_unif_problem ctxt tp
      ] |> Pretty.string_of);
      Util.THEN' (
      match_tac ctxt @{thm eq_if_SIMPS_TO_UNIF_if_SIMPS_TO}
      THEN' Simps_To.SIMPS_TO_tac (Simps_To.simp_inst_tac simp_tac) ctxt,
      SIMPS_TO_UNIF_env_thm_tac' env) i state)
  in Tactic_Unification.unify eq_tac ctxt end

fun simp_unify_progress teq simp_unify norm_term norms unif binders ctxt tp env =
  let
    val tp as (lhs, rhs) = apply2 (Binders.replace_binders binders #> norm_term env) tp
    fun unify ctxt (tp' as (lhs', rhs')) = if teq (lhs, lhs') andalso teq (rhs, rhs')
      then (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
          Pretty.str "Simplification of ",
          Unification_Util.pretty_unif_problem ctxt tp,
          Pretty.str " failed (no progress)"
        ] |> Pretty.string_of);
        K Seq.empty)
      else unif binders ctxt (apply2 (Binders.replace_frees binders) tp')
  in simp_unify norms unify ctxt tp env end

end
