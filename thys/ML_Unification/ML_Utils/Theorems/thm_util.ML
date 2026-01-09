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

  (*creates equality theorem for a subgoal from an equality theorem for the subgoal's conclusion;
    fails if the equality theorem contains a tpair or implicit assumption mentioning one of the bound variables*)
  val eq_subgoal_from_eq_concl : cterm Binders.binders -> cterm list -> Proof.context -> thm ->
    thm option
  (*creates theorem for a subgoal from theorem for the subgoal's conclusion;
    fails if the theorem contains a tpair or implicit assumption mentioning one of the bound variables*)
  val subgoal_thm_from_concl_thm : cterm Binders.binders -> cterm list -> Proof.context -> thm ->
    thm option

  val protect : thm -> thm
end

structure Thm_Util : THM_UTIL =
struct

val logger = Logger.setup_new_logger Logger.root "Thm_Util"

fun pretty_THM ctxt (msg, subgoal, thms) = Pretty.fbreaks [
    Pretty.str msg,
    Pretty.block [Pretty.str "Subgoal number ", Pretty.str (string_of_int subgoal)],
    Pretty.block [Pretty.str "Theorems ", Pretty.list "[" "]" (map (Thm.pretty_thm ctxt) thms)]
  ] |> Pretty.block

fun abstract_rule ctxt n ct thm = SOME (Thm.abstract_rule n ct thm)
  handle THM data => (@{log Logger.DEBUG} ctxt (fn _ => pretty_THM ctxt data |> Pretty.string_of);
    NONE)
fun forall_intr ctxt ct thm = SOME (Thm.forall_intr ct thm)
  handle THM data => (@{log Logger.DEBUG} ctxt (fn _ => pretty_THM ctxt data |> Pretty.string_of);
    NONE)

fun eq_subgoal_from_eq_concl cbinders cprems ctxt eq_thm =
  let fun all_abstract ((x, T), cfree) =
    let val all_const = Logic.all_const T |> Thm.cterm_of ctxt
    in abstract_rule ctxt x cfree #> Option.map (Drule.arg_cong_rule all_const) end
  in
    (*introduce the premises*)
    SOME (fold_rev (Drule.imp_cong_rule o Thm.reflexive) cprems eq_thm)
    (*introduce abstractions for the fresh Frees*)
    |> fold (Option.mapPartial o all_abstract) cbinders
  end

fun subgoal_thm_from_concl_thm cbinders cprems ctxt concl_thm =
  let fun all_abstract (_, cfree) = forall_intr ctxt cfree
  in
    (*introduce the premises*)
    SOME (fold_rev Thm.implies_intr cprems concl_thm)
    (*introduce abstractions for the fresh Frees*)
    |> fold (Option.mapPartial o all_abstract) cbinders
  end

fun protect thm = Thm.instantiate' [] [SOME (Thm.cprop_of thm)] Drule.protectI
  |> Thm.elim_implies thm

end
