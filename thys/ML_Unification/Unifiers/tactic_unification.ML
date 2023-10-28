(*  Title:      ML_Unification/tactic_unification.ML
    Author:     Kevin Kappelmann

Solving equations for unification problems with environment-aware tactics.
*)
signature TACTIC_UNIFICATION =
sig
  type env_tactic = Envir.env * thm -> (Envir.env * thm) Seq.seq
  (*create environment-aware tactic from a tactic that *DOES NOT* instantiate meta variables*)
  val env_tac_from_no_inst_tac : (int -> tactic) -> int -> env_tactic

  val unify : (term * term -> int -> env_tactic) -> Unification_Base.closed_unifier
end

structure Tactic_Unification : TACTIC_UNIFICATION =
struct

type env_tactic = Envir.env * thm -> (Envir.env * thm) Seq.seq
fun env_tac_from_no_inst_tac tac i (env, state) = tac i state |> Seq.map (pair env)

fun unify tac ctxt tp env =
  (Logic.mk_equals tp
  |> Thm.cterm_of ctxt
  |> Goal.init
  |> Tactic_Util.HEADGOAL (tac tp) o pair env
  |> Seq.map_filter (try (apsnd (Goal.finish ctxt))))
  handle TYPE _ => Seq.empty

end
