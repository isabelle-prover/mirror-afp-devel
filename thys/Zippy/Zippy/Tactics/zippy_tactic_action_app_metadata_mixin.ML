(*  Title:      Zippy/zippy_tactic_action_app_metadata_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_TACTIC_ACTION_APP_METADATA_MIXIN =
sig
  include ZIPPY_TACTIC_ACTION_APP_METADATA_MIXIN_BASE

  type rtactic = Meta.Meta.metadata Tac.RTac.rtactic
  type ztactic = Meta.Meta.metadata Tac.ztactic
  type result = Meta.Meta.metadata Tac.result

  (* liftings *)
  val madd : (Meta.Meta.cost * Meta.Meta.cost -> Meta.Meta.cost) ->
    Meta.Meta.metadata * Meta.Meta.metadata -> Meta.Meta.metadata
  type mk_meta = Tac.GPU.GCS.goal_pos -> Tac.state * Tac.state -> Meta.Meta.metadata
  val lift_tac : mk_meta -> (int -> tactic) -> Tac.GPU.GCS.goal_pos -> ztactic
end

functor Zippy_Tactic_Action_App_Metadata_Mixin(
    Tac_AAM : ZIPPY_TACTIC_ACTION_APP_METADATA_MIXIN_BASE
  ) : ZIPPY_TACTIC_ACTION_APP_METADATA_MIXIN =
struct
open Tac_AAM

local structure Meta = Meta.Meta
in
type rtactic = Meta.metadata Tac.RTac.rtactic
type ztactic = Meta.metadata Tac.ztactic
type result = Meta.metadata Tac.result

(* liftings *)
val madd = Meta.add
type mk_meta = Tac.GPU.GCS.goal_pos -> Tac.state * Tac.state -> Meta.metadata
fun lift_tac mk_meta = Tac.RTac.lift_tac' mk_meta #> Tac.lift_rtac_single_goal
end
end
