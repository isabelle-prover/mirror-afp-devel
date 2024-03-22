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
  val SIMPS_TO_tac : (int -> tactic) -> Proof.context -> int -> tactic

  val SIMPS_TO_thmsq : (int -> tactic) -> Proof.context -> cterm * cterm -> thm Seq.seq

  val simp_inst_tac : (int -> tactic) -> int -> tactic

  val SIMPS_TO_thm_resultsq : (int -> tactic) -> Proof.context -> cterm -> (thm * cterm) Seq.seq
end

structure Simps_To : SIMPS_TO =
struct

val logger = Logger.setup_new_logger simps_to_base_logger "Simps_To"

structure Util = Tactic_Util

val dest_SIMPS_TO = \<^Const_fn>\<open>SIMPS_TO _ for lhs rhs => \<open>(lhs, rhs)\<close>\<close>
val cdest_SIMPS_TO = Thm.dest_comb #>> Thm.dest_arg

fun mk_SIMPS_TO_cprop (clhs, crhs) = \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm clhs\<close> and clhs and crhs
  in cprop\<open>PROP (SIMPS_TO clhs crhs)\<close> for clhs :: 'a\<close>

fun finish_SIMPS_TO_tac ctxt = match_tac ctxt [@{thm SIMPS_TOI}]
fun SIMPS_TO_tac simp_tac ctxt = simp_tac THEN' finish_SIMPS_TO_tac ctxt

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

fun simp_inst_tac simp_tac =
  let fun inst_tac cconcl =
    PRIMITIVE (cdest_SIMPS_TO cconcl |> swap |> Thm.first_order_match |> Thm.instantiate)
  in simp_tac THEN' Tactic_Util.CSUBGOAL_STRIPPED (snd o snd) (K o inst_tac) end

fun SIMPS_TO_thm_resultsq simp_tac ctxt ct =
  let val cvar = Term_Util.fresh_var "x" (Thm.typ_of_cterm ct) (Thm.maxidx_of_cterm ct)
    |> fst |> Thm.cterm_of ctxt
  in
    SIMPS_TO_thmsq (simp_inst_tac simp_tac) ctxt (ct, cvar)
    |> Seq.map (fn thm => (thm, Thm.cconcl_of thm |> cdest_SIMPS_TO |> snd))
  end

end