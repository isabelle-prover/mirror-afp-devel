(*  Title:      ML_Unification/simplifier_unification.ML
    Author:     Kevin Kappelmann

Solving equations for unification problems with the simplifier.
*)
signature SIMPLIFIER_UNIFICATION =
sig
  include HAS_LOGGER
  (*solves "s \<equiv>\<^sup>? t" via simplification*)
  val simp_unify : Unification_Base.closed_unifier
  (*solves "SIMPS_TO s t \<equiv> rhs" via simplification of s when given a matching theorem
    "SIMPS_TO s t \<Longrightarrow> SIMPS_TO s t \<equiv> rhs"*)
  val SIMPS_TO_unify : thm -> Unification_Base.closed_unifier
  (*solves "SIMPS_TO_UNIF s t \<equiv> rhs" via simplification of s to s', followed by unification of
    "s' \<equiv>\<^sup>? t", when given a matching theorem "SIMPS_TO_UNIF s t \<Longrightarrow> SIMPS_TO_UNIF s t \<equiv> rhs"*)
  val SIMPS_TO_UNIF_unify : thm -> Unification_Base.normalisers -> Unification_Base.e_unifier
end

structure Simplifier_Unification : SIMPLIFIER_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Simplifier_Unification"

(*some "safe" solvers create instantiations via flex-flex pairs, which we disallow*)
val safe_simp_tac = Tactic_Util.safe_simp_tac

fun simp_unify ctxt tp =
  (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
      Pretty.str "Solving unification problem via simplification ",
      Unification_Util.pretty_unif_problem ctxt tp
    ] |> Pretty.string_of);
  Tactic_Unification.unify (Tactic_Unification.env_tac_from_no_inst_tac (safe_simp_tac ctxt) |> K)
    ctxt tp)

fun preprocess_tac ctxt = match_tac ctxt o single

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
      preprocess_tac ctxt preprocess_rule
      THEN' safe_simp_tac ctxt
      THEN' Simps_To.finish_SIMPS_TO_tac ctxt)
    else K no_tac
  in Tactic_Unification.unify (Tactic_Unification.env_tac_from_no_inst_tac o tac) ctxt end

fun SIMPS_TO_UNIF_unify preprocess_rule norms unif binders ctxt =
  let fun tac ctxt (tp as (lhs, _)) i (env, state) =
    (let
      val simps_to_tp = Simps_To_Unif.dest_SIMPS_TO_UNIF lhs
      fun solve_tac state =
        Simps_To_Unif.SIMPS_TO_UNIF_env_thmsq (safe_simp_tac ctxt) norms unif binders ctxt
          simps_to_tp env
        |> Seq.map (fn (env, thm) => (env, #norm_thm norms ctxt env state |> Thm.elim_implies thm))
    in
      (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
          Pretty.str "Solving ",
          Syntax.pretty_term ctxt @{term SIMPS_TO_UNIF},
          Pretty.str " unification problem ",
          Unification_Util.pretty_unif_problem ctxt tp
        ] |> Pretty.string_of);
      preprocess_tac ctxt preprocess_rule i state
      |> Seq.maps solve_tac)
    end)
    handle TERM _ => Seq.empty
  in Tactic_Unification.unify (tac ctxt) ctxt end

end
