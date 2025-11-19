(*  Title:      Zippy/zippy_instance_tactic.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_INSTANCE_TACTIC =
sig
  include ZIPPY_INSTANCE_PRESULTS

  structure Tac_AAM : ZIPPY_TACTIC_ACTION_APP_METADATA_MIXIN
  sharing type Tac_AAM.Tac.GPU.GCS.gcpos = Base_Data.GCS.gcpos
  sharing type Tac_AAM.Tac.GPU.GCS.gclusters = Base_Data.GCS.gclusters
  sharing type Tac_AAM.Tac.GPU.F.focus = Base_Data.GFocus.focus
  sharing type Tac_AAM.Meta.Meta.metadata = Base_Data.AAMeta.metadata
  sharing type Tac_AAM.Meta.L.container = ZLPC.Z5.zipper

  structure Tac :
  sig
    val ztactic_resultsq : Tac_AAM.ztactic -> @{AllT_args} ZLPC.Z2.zipper -> Tac_AAM.result Seq.seq

    type @{AllT_args} data = {
      meta : Base_Data.AMeta.metadata,
      empty_action : int -> @{AllT_args} Base_Data.PAction.action,
      result_action : Result_Action.result -> @{AllT_args} Base_Data.PAction.action,
      presultsq : @{AllT_args} PResults.presultsq,
      tac : @{AllT_args} ZLPC.Z4.zipper ->
        (@{ParaT_args} Base_Data.GFocus.focus, Tac_AAM.ztactic) morph}

    val presults_data_from_data : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> @{AllT_args} data ->
      @{AllT_args} PResults.data
    val paction_data_from_data : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> @{AllT_args} data ->
      @{AllT_args} PAction.data
    val cons_action : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> @{AllT_args} data ->
      Base_Data.GFocus.focus -> (@{ParaT_args} @{AllT_args} ZLPC.Z3.zipper,
        @{AllT_args} ZLPC.Z4.zipper) morph
    val cons_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.ACMeta.metadata ->
      (Base_Data.GFocus.focus * @{AllT_args} data) list ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper, @{AllT_args} ZLPC.Z3.zipper option) morph
  end
end

functor Zippy_Instance_Tactic(
    structure Z : ZIPPY_INSTANCE_PRESULTS
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    structure Log_PAction : ZIPPY_LOGGER_MIXIN_BASE
  ) : ZIPPY_INSTANCE_TACTIC =
struct
open Z; open ZLPC MU
structure GCluster = Zippy_Goal_Cluster_Mixin(Mixin_Base2.GCluster)
structure PAction_More = Zippy_PAction_Mixin(
  structure PAction = Mixin_Base4.PAction
  structure Exn = Exn; structure Ctxt = Ctxt; structure Log = Log_PAction
  structure Show = Show.Zipper4)
structure PResults_More = Zippy_PResults_Mixin(PResults)

structure Tac_AAM = Zippy_Tactic_Action_App_Metadata_Mixin(
  Zippy_Tactic_Action_App_Metadata_Mixin_Base(
    structure Meta = Zippy_Action_App_Metadata_Mixin_Base(
      structure Meta = Base_Data.AAMeta; structure L = Lens5.Meta)
    structure Tac = Zippy_ZTactic(
      structure R = Base_Data.Tac_Res; structure RTac = Standard_Zippy_RTactic)))

structure Tac =
struct
fun ztactic_resultsq tac z2 = tac (GCluster.get_state z2)

local open Base_Data
in
type @{AllT_args} data = {
  meta : AMeta.metadata,
  empty_action : int -> @{AllT_args} PAction.action,
  result_action : PResults.result -> @{AllT_args} PAction.action,
  presultsq : @{AllT_args} PResults.presultsq,
  tac : @{AllT_args} ZLPC.Z4.zipper -> (@{ParaT_args} GFocus.focus, Tac_AAM.ztactic) morph}
end

local open SC Mo A
in
fun presults_from_data exn {presultsq, tac,...} focus z4 = Up4.morph z4
  >>= Up3.morph
  >>= (fn z2 => tac z4 focus
  >>= arr (fn tac => ztactic_resultsq tac z2 |> PResults_More.presults_from_resultsq exn presultsq))

fun presults_data_from_data exn (data as {meta, result_action, empty_action,...}) =
  {meta = meta, empty_action = empty_action, result_action = result_action,
    presults = presults_from_data exn data}

fun paction_data_from_data exn = presults_data_from_data exn #> PResults.paction_data_from_data

fun cons_action x = paction_data_from_data x #> Z.PAction.cons_action

fun cons_action_cluster exn meta =
  List.map (apsnd (fn data => fn focus => cons_action exn data focus >>> Up4.morph))
  #> Node.cons3 exn meta
end
end
end
