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

  val unify : Envir_Normalisation.term_normaliser -> (term * term -> int -> env_tactic) ->
    Unification_Base.unifier
end

structure Tactic_Unification : TACTIC_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Tactic_Unification"

type env_tactic = Envir.env * thm -> (Envir.env * thm) Seq.seq
fun env_tac_from_no_inst_tac tac i (env, state) = tac i state |> Seq.map (pair env)

fun unify normt tac binders ctxt (tp as (lhs, rhs)) env = Seq.make (fn _ =>
  let
    val rev_binders = rev binders
    fun forall_elim (env, state) = Binders.norm_binders (normt env) rev_binders
      |> map (snd #> Thm.cterm_of ctxt)
      |> (fn binders => Drule.forall_elim_list binders state)
      |> pair env
  in
    (Term_Util.mk_equals binders tp
    |> curry Logic.list_all (map fst rev_binders)
    |> Thm.cterm_of ctxt
    |> Goal.init
    |> Tactic_Util.HEADGOAL (tac tp) o pair env
    |> Seq.map_filter (try (apsnd (Goal.finish ctxt)))
    |> Seq.map forall_elim)
    |> Seq.pull
    handle TYPE _ => (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Types of terms ",
        Unification_Util.pretty_terms ctxt [lhs, rhs],
        Pretty.str " not equal"
      ] |> Pretty.string_of);
      NONE)
  end)

end
