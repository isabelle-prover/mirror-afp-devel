(*  Title:      ML_Unification/simps_to.ML
    Author:     Kevin Kappelmann

Create SIMPS_TO theorems.
*)
signature SIMPS_TO =
sig
  include HAS_LOGGER

  val dest_SIMPS_TO : term -> (term * term)
  val cdest_SIMPS_TO : cterm -> (cterm * cterm)

  val mk_SIMPS_TO_cprop : cterm * cterm -> cterm

  val finish_SIMPS_TO_tac : Proof.context -> int -> tactic
  val finish_SIMPS_TO_unif_tac : Proof.context -> int -> tactic
  val SIMPS_TO_tac : (int -> tactic) -> Proof.context -> int -> tactic
  val SIMPS_TO_unif_tac : (int -> tactic) -> Proof.context -> int -> tactic

  val SIMPS_TO_thmsq : (int -> tactic) -> Proof.context -> cterm * cterm -> thm Seq.seq
end

structure Simps_To : SIMPS_TO =
struct

val logger = Logger.setup_new_logger simps_to_base_logger "Simps_To"

structure Util = Tactic_Util

val dest_SIMPS_TO = \<^Const_fn>\<open>SIMPS_TO _ for lhs rhs => \<open>(lhs, rhs)\<close>\<close>
val cdest_SIMPS_TO = Thm.dest_comb #>> Thm.dest_arg

fun mk_SIMPS_TO_cprop (clhs, crhs) = \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm clhs\<close> and clhs and crhs
  in cprop\<open>PROP (SIMPS_TO clhs crhs)\<close> for clhs :: 'a\<close>

val finish_thm = @{thm SIMPS_TOI}

fun finish_SIMPS_TO_tac ctxt = match_tac ctxt [finish_thm]
fun finish_SIMPS_TO_unif_tac ctxt = resolve_tac ctxt [finish_thm]
fun SIMPS_TO_tac simp_tac ctxt = simp_tac THEN' finish_SIMPS_TO_tac ctxt
fun SIMPS_TO_unif_tac simp_tac ctxt = simp_tac THEN' finish_SIMPS_TO_unif_tac ctxt

fun SIMPS_TO_thmsq simp_tac ctxt (ctp as (clhs, crhs)) =
  (let val goal = mk_SIMPS_TO_cprop ctp
  in
    (@{log Logger.TRACE} ctxt (fn _ => Pretty.block [
        Pretty.str "Creating ",
        Syntax.pretty_term ctxt @{term SIMPS_TO},
        Pretty.str " theorems for ",
        Unification_Util.pretty_terms ctxt (map Thm.term_of [clhs, crhs])
      ] |> Pretty.string_of);
    Util.HEADGOAL (Util.apply_tac (SIMPS_TO_tac simp_tac ctxt)) goal)
  end)
  handle TYPE _ => (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
      Pretty.str "Types of terms ",
      Unification_Util.pretty_terms ctxt (map Thm.term_of [clhs, crhs]),
      Pretty.str " not equal"
    ] |> Pretty.string_of);
    Seq.empty)

end