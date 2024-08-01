(*  Title:      ML_Utils/thm_util.ML
    Author:     Kevin Kappelmann

Theorem utilities.
*)
signature THM_UTIL =
sig
  include HAS_LOGGER

  val pretty_THM : Proof.context -> string * int * thm list -> Pretty.T

  (*fails if the theorem contains a tpair or implicit Assumption mentioning the bound variable*)
  val abstract_rule : Proof.context -> string -> cterm -> thm -> thm option
  val forall_intr : Proof.context -> cterm -> thm -> thm option

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
fun forall_intr ctxt ct thm = SOME (Thm.forall_intr ct thm)
  handle THM data => (@{log Logger.DEBUG} ctxt (fn _ => pretty_THM ctxt data |> Pretty.string_of);
    NONE)

fun protect thm = Thm.instantiate' [] [SOME (Thm.cprop_of thm)] Drule.protectI
  |> Thm.elim_implies thm

end
