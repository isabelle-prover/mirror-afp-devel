(*  Title:      Zippy/zippy_instance_simp.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_INSTANCE_SIMP =
sig
  include ZIPPY_INSTANCE_TACTIC

  structure Simp :
  sig
    val gen_data : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Zippy_Identifier.id -> string ->
      (Proof.context -> int -> tactic) -> (Proof.context -> int -> tactic) ->
      ((Base_Data.GCS.goal_pos * Base_Data.GCS.gcpos list) list ->
        (@{ParaT_args} @{AllT_args} ZLPC.Z1.zipper) emorph) ->
      @{AllT_args} Result_Action.mk_copy_update_data ->
      (Tac_AAM.Meta.Meta.metadata * Tac_AAM.Meta.Meta.metadata -> Tac_AAM.Meta.Meta.metadata) ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z4.zipper, Tac_AAM.mk_meta) morph ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z4.zipper, Tac_AAM.mk_meta) morph ->
      @{AllT_args} PResults.presultsq -> @{AllT_args} PResults.presultsq -> @{AllT_args} Tac.data
  end
end

functor Zippy_Instance_Simp(
    structure Z : ZIPPY_INSTANCE_TACTIC
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
  ) : ZIPPY_INSTANCE_SIMP =
struct
open Z

structure Simp =
struct
local open MU; open Mo A
in
fun gen_data exn id tac_name safe_tac unsafe_tac update_result mk_cud madd_safe mk_meta_safe
  mk_meta_unsafe presultsq_safe
  presultsq_unsafe =
  let
    val safe_tac_name = "safe " ^ tac_name
    fun descr tac = Lazy.lazy (fn _ => Pretty.breaks [
        Pretty.str (implode [safe_tac_name, " ORELSE ", tac_name]),
        Pretty.block [Pretty.str "Current: ", Pretty.str tac]
      ] |> Pretty.block |> Pretty.string_of)
    val empty_action = PAction.disable_action
    val result_action = Result_Action.changed_goals_action update_result mk_cud
    fun unsafe_ztac z focus = mk_meta_unsafe z
      >>= Ctxt.with_ctxt (fn ctxt => arr (fn mk_meta => Tac_AAM.Tac.zSOME_GOAL_FOCUS
        (Tac_AAM.lift_tac mk_meta (unsafe_tac ctxt #> CHANGED)) focus))
    val unsafe_data = {
      empty_action = Library.K empty_action,
      meta = Base_Data.AMeta.metadata (id, descr tac_name),
      result_action = result_action,
      presultsq = presultsq_unsafe,
      tac = unsafe_ztac}
      |> Tac.paction_data_from_data exn

    fun safe_ztac z focus = mk_meta_safe z
      >>= Ctxt.with_ctxt (fn ctxt => arr (fn mk_meta => Tac_AAM.Tac.zTRY_EVERY_FOCUS1 madd_safe
        (Tac_AAM.lift_tac mk_meta (safe_tac ctxt #> CHANGED)) focus))
    val data = {
      empty_action = PResults.orelse_update_action empty_action unsafe_data,
      meta = Mixin_Base4.Meta.Meta.metadata (id, descr safe_tac_name),
      result_action = result_action,
      presultsq = presultsq_safe,
      tac = safe_ztac}
  in data end
end
end
end