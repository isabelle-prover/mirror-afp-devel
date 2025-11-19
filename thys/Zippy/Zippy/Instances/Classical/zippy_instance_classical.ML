(*  Title:      Zippy/zippy_instance_classical.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_INSTANCE_CLASSICAL =
sig
  include ZIPPY_INSTANCE_TACTIC

  structure Classical :
  sig
    val slow_step_data : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Zippy_Identifier.id ->
      ((Base_Data.GCS.goal_pos * Base_Data.GCS.gcpos list) list ->
        (@{ParaT_args} @{AllT_args} ZLPC.Z1.zipper) emorph) ->
      @{AllT_args} Result_Action.mk_copy_update_data ->
      (Tac_AAM.Meta.Meta.metadata * Tac_AAM.Meta.Meta.metadata -> Tac_AAM.Meta.Meta.metadata) ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z4.zipper, Tac_AAM.mk_meta) morph ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z4.zipper, Tac_AAM.mk_meta) morph ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z4.zipper, Tac_AAM.mk_meta) morph ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z4.zipper, Tac_AAM.mk_meta) morph ->
      @{AllT_args} PResults.presultsq -> @{AllT_args} PResults.presultsq ->
      @{AllT_args} PResults.presultsq -> @{AllT_args} PResults.presultsq -> @{AllT_args} Tac.data
    val atomize_prems_data :
      Zippy_Identifier.id -> ((Base_Data.GCS.goal_pos * Base_Data.GCS.gcpos list) list ->
        (@{ParaT_args} @{AllT_args} ZLPC.Z1.zipper) emorph) ->
      @{AllT_args} Result_Action.mk_copy_update_data ->
      (Tac_AAM.Meta.Meta.metadata * Tac_AAM.Meta.Meta.metadata -> Tac_AAM.Meta.Meta.metadata) ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z4.zipper, Tac_AAM.mk_meta) morph ->
      @{AllT_args} PResults.presultsq ->
      @{AllT_args} Tac.data
  end
end

functor Zippy_Instance_Classical(
    structure Z : ZIPPY_INSTANCE_TACTIC
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
  ) : ZIPPY_INSTANCE_CLASSICAL =
struct
open Z

structure Classical =
struct
local open MU; open Mo A
in
fun slow_step_data exn id update_result mk_cud madd_safe mk_meta_safe mk_meta_inst0 mk_meta_instp
  mk_meta_unsafe presultsq_safe presultsq_inst0 presultsq_instp presultsq_unsafe =
  let
    fun descr tac = Lazy.lazy (fn _ => Pretty.breaks [
        Pretty.str "Classical.slow_step",
        Pretty.block [Pretty.str "Current: ", Pretty.str tac]
      ] |> Pretty.block |> Pretty.string_of)

    val empty_action = PAction.disable_action
    val result_action = Result_Action.changed_goals_action update_result mk_cud

    fun unsafe_step_tac ctxt = Classical.appWrappers ctxt (Classical.unsafe_step_tac ctxt)
    fun unsafe_step_ztac z focus = mk_meta_unsafe z
      >>= Ctxt.with_ctxt (fn ctxt => arr (fn mk_meta => Tac_AAM.Tac.zSOME_GOAL_FOCUS
        (Tac_AAM.lift_tac mk_meta (unsafe_step_tac ctxt)) focus))
    val unsafe_step_data = {
      empty_action = Library.K empty_action,
      meta = Mixin_Base4.Meta.Meta.metadata (id, descr "unsafe_step"),
      result_action = result_action,
      presultsq = presultsq_unsafe,
      tac = unsafe_step_ztac}
      |> Tac.paction_data_from_data exn

    fun instp_step_tac ctxt = Classical.appWrappers ctxt (Classical.instp_step_tac ctxt)
    fun instp_step_ztac z focus = mk_meta_instp z
      >>= Ctxt.with_ctxt (fn ctxt => arr (fn mk_meta => Tac_AAM.Tac.zSOME_GOAL_FOCUS
        (Tac_AAM.lift_tac mk_meta (instp_step_tac ctxt)) focus))
    val instp_step_data = {
      empty_action = Library.K (PAction.update_action unsafe_step_data),
      meta = Mixin_Base4.Meta.Meta.metadata (id, descr "instp_step"),
      result_action = result_action,
      presultsq = presultsq_instp,
      tac = instp_step_ztac}
      |> Tac.paction_data_from_data exn

    fun inst0_step_tac ctxt = Classical.appWrappers ctxt (Classical.inst0_step_tac ctxt)
    fun inst0_step_ztac z focus = mk_meta_inst0 z
      >>= Ctxt.with_ctxt (fn ctxt => arr (fn mk_meta => Tac_AAM.Tac.zSOME_GOAL_FOCUS
        (Tac_AAM.lift_tac mk_meta (inst0_step_tac ctxt)) focus))
    val inst0_step_data = {
      empty_action = Library.K (PAction.update_action instp_step_data),
      meta = Mixin_Base4.Meta.Meta.metadata (id, descr "inst0_step"),
      result_action = result_action,
      presultsq = presultsq_inst0,
      tac = inst0_step_ztac}
      |> Tac.paction_data_from_data exn

    val safe_tac = Classical.safe_tac #> SELECT_GOAL
    fun safe_ztac z focus = mk_meta_safe z
      >>= Ctxt.with_ctxt (fn ctxt => arr (fn mk_meta => Tac_AAM.Tac.zTRY_EVERY_FOCUS1 madd_safe
        (Tac_AAM.lift_tac mk_meta (safe_tac ctxt)) focus))
    val data = {
      empty_action = PResults.orelse_update_action empty_action inst0_step_data,
      meta = Mixin_Base4.Meta.Meta.metadata (id, descr "safe_tac"),
      result_action = result_action,
      presultsq = presultsq_safe,
      tac = safe_ztac}
  in data end

fun atomize_prems_data id update_result mk_cud madd mk_meta presultsq =
  let
    val empty_action = PAction.disable_action
    val result_action = Result_Action.changed_goals_action update_result mk_cud

    fun tac ctxt = Object_Logic.atomize_prems_tac ctxt #> CHANGED
    fun ztac z focus = mk_meta z
      >>= Ctxt.with_ctxt (fn ctxt => arr (fn mk_meta => Tac_AAM.Tac.zTRY_EVERY_FOCUS1 madd
        (Tac_AAM.lift_tac mk_meta (tac ctxt)) focus))
    val data = {
      empty_action = Library.K empty_action,
      meta = Mixin_Base4.Meta.Meta.metadata (id, Lazy.value "Object_Logic.atomize_prems"),
      result_action = result_action,
      presultsq = presultsq,
      tac = ztac}
  in data end
end
end
end