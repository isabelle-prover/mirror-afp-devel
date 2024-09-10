(*  Title:      ML_Unification/simplifier_unification.ML
    Author:     Kevin Kappelmann

Solving equations for unification problems with the simplifier.
*)
signature SIMPLIFIER_UNIFICATION =
sig
  include HAS_LOGGER
  (*solves "SIMPS_TO s t \<equiv> rhs" via simplification of s when given a theorem
    "SIMPS_TO s t \<Longrightarrow> SIMPS_TO s t \<equiv> rhs"*)
  val SIMPS_TO_unify : thm -> Unification_Base.unifier
  (*solves "SIMPS_TO_UNIF s t \<equiv> rhs" via simplification of s to s', followed by unification of
    "s' \<equiv>\<^sup>? t", when given a theorem "SIMPS_TO_UNIF s t \<Longrightarrow> SIMPS_TO_UNIF s t \<equiv> rhs"*)
  val SIMPS_TO_UNIF_unify : thm -> Unification_Base.normalisers -> Unification_Base.unifier ->
    Unification_Base.unifier
  (*solves "s \<equiv>\<^sup>? t" via simplification followed by unification*)
  val simp_unify : Unification_Base.normalisers -> Unification_Base.unifier ->
    Unification_Base.normalisers -> Unification_Base.unifier -> Unification_Base.unifier
  (*solves "s \<equiv>\<^sup>? t" via simplification followed by unification; aborts if no progress was made
  during simplification*)
  val simp_unify_progress : (term * term -> bool) ->
    (Unification_Base.unifier -> Unification_Base.unifier) -> Envir_Normalisation.term_normaliser ->
    Unification_Base.e_unifier
end

structure Simplifier_Unification : SIMPLIFIER_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Simplifier_Unification"

structure TUtil = Tactic_Util
structure UUtil = Unification_Util

(*some "safe" solvers create instantiations via flex-flex pairs, which we disallow*)
val safe_simp_tac = TRY oo TUtil.safe_simp_tac

fun match_tac ctxt = Tactic.match_tac ctxt o single

fun SIMPS_TO_unify preprocess_rule binders ctxt (tp as (lhs, _)) =
  if can Simps_To.dest_SIMPS_TO lhs
  then
    let fun tac tp =
      (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
          Pretty.str "Solving ",
          Syntax.pretty_term ctxt @{term SIMPS_TO},
          Pretty.str " unification problem ",
          UUtil.pretty_unif_problem ctxt tp
        ] |> Pretty.string_of);
      match_tac ctxt preprocess_rule
      THEN' Simps_To.SIMPS_TO_tac (safe_simp_tac ctxt) ctxt)
    in
      Tactic_Unification.unify (K I) (Tactic_Unification.env_tac_from_no_inst_tac o tac)
        binders ctxt tp
    end
  else K Seq.empty

fun SIMPS_TO_UNIF_unify preprocess_rule norms unif binders ctxt (tp as (lhs, _)) =
  if can Simps_To_Unif.dest_SIMPS_TO_UNIF lhs
  then
    let fun tac tp i (env, state) =
      (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
          Pretty.str "Solving ",
          Syntax.pretty_term ctxt @{term SIMPS_TO_UNIF},
          Pretty.str " unification problem ",
          UUtil.pretty_unif_problem ctxt tp
        ] |> Pretty.string_of);
      match_tac ctxt preprocess_rule i state
      |> Seq.maps (pair env
        #> Simps_To_Unif.SIMPS_TO_UNIF_env_tac (safe_simp_tac ctxt) norms unif ctxt i))
    in Tactic_Unification.unify (#inst_term norms) tac binders ctxt tp end
  else K Seq.empty

fun simp_unify norms1 unif1 norms2 unif2 binders ctxt =
  let open TUtil
    fun SIMPS_TO_UNIF_env_tac norms unif =
      Simps_To_Unif.SIMPS_TO_UNIF_env_tac (safe_simp_tac ctxt) norms unif ctxt
    fun eq_tac tp i (env, state) =
      (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Solving unification problem via simplification followed by unification ",
        UUtil.pretty_unif_problem ctxt tp
      ] |> Pretty.string_of);
      (match_tac ctxt
        (Thm.incr_indexes (Envir.maxidx_of env + 1) @{thm eq_if_SIMPS_TO_UNIF_if_SIMPS_TO_UNIF})
      THEN' K (fn state => Seq.single (UUtil.update_maxidx_envir (Thm.maxidx_of state) env, state))
      THEN' SIMPS_TO_UNIF_env_tac norms1 unif1
      THEN' SIMPS_TO_UNIF_env_tac norms2 unif2)
      i state)
  in Tactic_Unification.unify (#inst_term norms1) eq_tac binders ctxt end

fun simp_unify_progress teq simp_unify norm_term unif binders ctxt tp env = Seq.make (fn _ =>
  let
    val tp as (lhs, rhs) = apply2 (norm_term env) tp
    fun unify binders ctxt tp' env =
      let val (tp' as (lhs', rhs')) = apply2 (norm_term env) tp'
      in
        if teq (lhs, lhs') andalso teq (rhs, rhs')
        then (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
            Pretty.str "Simplification of ",
            UUtil.pretty_unif_problem ctxt tp,
            Pretty.str " failed (no progress)"
          ] |> Pretty.string_of);
          K Seq.empty) env
        else unif binders ctxt tp' env
      end
  in simp_unify unify binders ctxt tp env |> Seq.pull end)

end
