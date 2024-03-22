(*  Title:      ML_Unification/tactic_unification.ML
    Author:     Kevin Kappelmann

Solving equations for unification problems with environment-aware tactics.
*)
signature TACTIC_UNIFICATION =
sig
  include HAS_LOGGER

  type env_tactic = Envir.env * thm -> (Envir.env * thm) Seq.seq
  (*create environment-aware tactic from a tactic that *DOES NOT* instantiate meta variables*)
  val env_tac_from_no_inst_tac : (int -> tactic) -> int -> env_tactic

  val unify : (term * term -> int -> env_tactic) -> Unification_Base.closed_unifier
end

structure Tactic_Unification : TACTIC_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Tactic_Unification"

type env_tactic = Envir.env * thm -> (Envir.env * thm) Seq.seq
fun env_tac_from_no_inst_tac tac i (env, state) = tac i state |> Seq.map (pair env)

fun unify tac ctxt (tp as (lhs, rhs)) env =
  (Logic.mk_equals tp
  |> Thm.cterm_of ctxt
  |> Goal.init
  |> Tactic_Util.HEADGOAL (tac tp) o pair env
  |> Seq.map_filter (try (apsnd (Goal.finish ctxt))))
  handle TYPE _ => (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
      Pretty.str "Types of terms ",
      Unification_Util.pretty_terms ctxt [lhs, rhs],
      Pretty.str " not equal"
    ] |> Pretty.string_of);
    Seq.empty)

end
