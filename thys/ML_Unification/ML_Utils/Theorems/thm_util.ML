(*  Title:      ML_Utils/thm_util.ML
    Author:     Kevin Kappelmann

Theorem utilities.
*)
signature THM_UTIL =
sig
  include HAS_LOGGER

  val pretty_THM : Proof.context -> string * int * thm list -> Pretty.T

  (*fails if the equality theorem contains a tpair or implicit Assumption mentioning the bound variables*)
  val abstract_rule : Proof.context -> string -> cterm -> thm -> thm option
  (*"match_implies_elim prem thm" matches the first premise of thm against prem and then removes
    the premise; without lifting*)
  val match_implies_elim : thm -> thm -> thm
  val protect : thm -> thm
end

structure Thm_Util : THM_UTIL =
struct

val logger = Logger.setup_new_logger Logger.root "Thm_Util"

fun pretty_THM ctxt (msg, subgoal, thms) = Pretty.block [
    Pretty.str msg,
    Pretty.fbrk,
    Pretty.str "Subgoal number ",
    Pretty.str (string_of_int subgoal),
    Pretty.fbrk,
    Pretty.str "Theorems ",
    Pretty.list "[" "]" (map (Thm.pretty_thm ctxt) thms)
  ]

fun abstract_rule ctxt n ct thm = SOME (Thm.abstract_rule n ct thm)
  handle THM data => (@{log Logger.DEBUG} ctxt (fn _ => pretty_THM ctxt data |> Pretty.string_of);
    NONE)

fun match_implies_elim prem thm =
  Thm.instantiate (Thm.first_order_match (Thm.cprem_of thm 1, Thm.cprop_of prem)) thm
  |> (fn thm => Thm.implies_elim thm prem)

fun protect thm = Drule.protectI
  |> Thm.instantiate (TVars.empty, Vars.make [((("A", 0), propT), Thm.cprop_of thm)])
  |> Thm.elim_implies thm

end
