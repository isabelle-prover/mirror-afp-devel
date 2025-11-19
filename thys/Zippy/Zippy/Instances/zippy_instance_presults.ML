(*  Title:      Zippy/zippy_instance_presults.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_INSTANCE_PRESULTS =
sig
  include ZIPPY_INSTANCE_PACTION

  structure PResults :
  sig
    include ZIPPY_PRESULTS_MIXIN_BASE
    where type result = Result_Action.result
    where type @{AllT_args} zipper = @{AllT_args} ZLPC.Z4.zipper
    where type prio = Base_Data.PAction.prio
    where type (@{ParaT_args} 'a, 'b, 'c) Co.Co.acoroutine =
      (@{ParaT_args} 'a, 'b, 'c) Co.Co.acoroutine
    where type @{ParaT_args encl: "(" ")"} Co.ME.exn = @{ParaT_args encl: "(" ")"} Exn.ME.exn
    where type (@{ParaT_args} 'a) Co.M.t = (@{ParaT_args} 'a) M.t

    val paction : (int -> @{AllT_args} Base_Data.PAction.action) ->
      (result -> @{AllT_args} Base_Data.PAction.action) ->
      @{AllT_args} presults -> @{AllT_args} Base_Data.PAction.paction

    (*updates with passed paction data if no successful action applications have been made;
    otherwise returns passed action*)
    val orelse_update_action : @{AllT_args} Base_Data.PAction.action -> @{AllT_args} PAction.data ->
      int -> @{AllT_args} Base_Data.PAction.action

    type @{AllT_args} data = {
      meta : Base_Data.AMeta.metadata,
      (*first argument is the number of successful action applications before the empty action*)
      empty_action : int -> @{AllT_args} Base_Data.PAction.action,
      result_action : result -> @{AllT_args} Base_Data.PAction.action,
      presults : Base_Data.GFocus.focus -> (@{ParaT_args} @{AllT_args} ZLPC.Z4.zipper,
        @{AllT_args} presults) morph}

    val paction_data_from_data : @{AllT_args} data -> @{AllT_args} PAction.data
    val cons_action : @{AllT_args} data -> Base_Data.GFocus.focus ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z3.zipper, @{AllT_args} ZLPC.Z4.zipper) morph
    val cons_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.ACMeta.metadata ->
      (Base_Data.GFocus.focus * @{AllT_args} data) list ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper, @{AllT_args} ZLPC.Z3.zipper option) morph
  end
end

functor Zippy_Instance_PResults(
    structure Z : ZIPPY_INSTANCE_PACTION
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    structure Log_PAction : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_PAction_PResults : ZIPPY_LOGGER_MIXIN_BASE
  ) : ZIPPY_INSTANCE_PRESULTS =
struct

open Z; open ZLPC MU
structure ZP = Zippy_Positions_Mixin(structure Z = ZP; structure Exn = Exn)

structure PResults = Zippy_PResults_Mixin(Zippy_PResults_Mixin_Base(
  structure M = ZLPC
  structure Co = Co
  type @{AllT_args} zipper = @{AllT_args} Z4.zipper
  type prio = Base_Data.PAction.prio
  type result = Base_Data.AAMeta.metadata Base_Data.Tac_Res.result
  type @{AllT_args} presults = (@{ParaT_args} @{AllT_args} zipper, prio, result) Co.Co.acoroutine
  val presults = I; val dest_presults = I))

structure PAction_More = Mixin_Base4.PAction
structure PAction_PResults = Zippy_PAction_PResults_Mixin(
  structure PAction_PResults = Zippy_PAction_PResults_Mixin_Base(
    structure PResults = PResults; structure PAction = Base_Data.PAction)
  structure Ctxt = Ctxt
  structure Show_PAction_Zipper = Show.Zipper4
  structure Log_PAction = Log_PAction; structure Log = Log_PAction_PResults)
structure PResults_Pos = Zippy_PResults_Positions_Mixin(
  structure Z = ZP; structure PResults = PResults)
structure Action_App_Num = Zippy_Action_App_Num_Mixin(Mixin_Base4.Action_App_Num)

structure PResults =
struct open PResults

local open A Mo SC
in
fun paction empty_action = PAction_PResults.paction_from_presults empty_action
  (fn _ => fn _ => arr Action_App_Num.inc_action_app_num)

fun orelse_update_action action update_data counter = if counter = 0
  then PAction.update_action update_data else action

local open Base_Data
in
type @{AllT_args} data = {
  meta : AMeta.metadata,
  empty_action : int -> @{AllT_args} PAction.action,
  result_action : result -> @{AllT_args} PAction.action,
  presults : GFocus.focus -> (@{ParaT_args} @{AllT_args} Z4.zipper, @{AllT_args} presults) morph}
end

fun paction_from_data {empty_action, result_action, presults,...} focus =
  (fn z4 => presults focus z4 >>= (paction empty_action result_action
    #> Mixin_Base4.PAction.run_paction #> (fn paction => paction z4)))
  |> Mixin_Base4.PAction.paction

fun paction_data_from_data (data as {meta,...}) = {meta = meta, paction = paction_from_data data}

fun cons_action x = paction_data_from_data x |> Z.PAction.cons_action

fun cons_action_cluster exn meta =
  List.map (apsnd (fn data => fn focus => cons_action data focus >>> Up4.morph))
  #> Node.cons3 exn meta
end
end

end