(*  Title:      ML_Unification/simps_to.ML
    Author:     Kevin Kappelmann

Create SIMPS_TO theorems.
*)
signature SIMPS_TO =
sig
  include HAS_LOGGER

  val dest_SIMPS_TO : term -> (term * term)
  val cdest_SIMPS_TO : cterm -> (cterm * cterm)

  val mk_SIMPS_TO_cprop : cterm -> cterm -> cterm
  val mk_SIMPS_TO_var_cprop : Proof.context -> cterm -> cterm

  val finish_SIMPS_TO_tac : Proof.context -> int -> tactic

  val SIMPS_TO_thmsq : (int -> tactic) -> Proof.context -> cterm -> thm Seq.seq
  val SIMPS_TO_thm_resultsq : (int -> tactic) -> Proof.context -> cterm ->
    (thm * cterm) Seq.seq
end

structure Simps_To : SIMPS_TO =
struct

val logger = Logger.setup_new_logger simps_to_base_logger "Simps_To"

structure Util = Tactic_Util

val dest_SIMPS_TO = \<^Const_fn>\<open>SIMPS_TO _ for lhs rhs => \<open>(lhs, rhs)\<close>\<close>
val cdest_SIMPS_TO = Thm.dest_comb #>> Thm.dest_arg

fun mk_SIMPS_TO_cprop clhs crhs = \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm clhs\<close> and clhs and crhs
  in cprop\<open>PROP (SIMPS_TO clhs crhs)\<close> for clhs :: 'a\<close>

fun mk_SIMPS_TO_var_cprop ctxt ct =
  Var (("x", Thm.maxidx_of_cterm ct + 1), Thm.typ_of_cterm ct)
  |> Thm.cterm_of ctxt
  |> mk_SIMPS_TO_cprop ct

fun finish_SIMPS_TO_tac ctxt = match_tac ctxt [@{thm SIMPS_TOI}]

fun SIMPS_TO_thmsq simps_to_tac ctxt ct =
  let fun inst_tac cconcl _ =
    PRIMITIVE (cdest_SIMPS_TO cconcl |> swap |> Thm.match |> Thm.instantiate)
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Creating ",
        Syntax.pretty_term ctxt @{term SIMPS_TO},
        Pretty.str " theorems for ",
        Syntax.pretty_term ctxt (Thm.term_of ct)
      ] |> Pretty.string_of);
    mk_SIMPS_TO_var_cprop ctxt ct
    |> Util.HEADGOAL (Util.apply_tac (
      simps_to_tac
      THEN' Tactic_Util.CSUBGOAL_STRIPPED (snd o snd) inst_tac
      THEN' finish_SIMPS_TO_tac ctxt)))
  end

val SIMPS_TO_thm_resultsq =
  Seq.map (fn thm => (thm, Thm.cconcl_of thm |> Thm.dest_arg)) ooo SIMPS_TO_thmsq

end