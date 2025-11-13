(*  Title:      Zippy/zippy_instance_paction.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_INSTANCE_PACTION =
sig
  include ZIPPY_INSTANCE

  structure PAction :
  sig
    val disable_action : @{AllT_args} Base_Data.PAction.action
    type @{AllT_args} data = {
      meta : Base_Data.AMeta.metadata,
      paction : Base_Data.GFocus.focus -> @{AllT_args} Base_Data.PAction.paction}
    val update : @{AllT_args} data -> @{AllT_args} ZLPC.Z4.zipper -> @{AllT_args} ZLPC.Z4.zipper
    val update_action : @{AllT_args} data -> @{AllT_args} Base_Data.PAction.action
    val cons_action : @{AllT_args} data -> Base_Data.GFocus.focus ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z3.zipper, @{AllT_args} ZLPC.Z4.zipper) morph
    val cons_action_cluster : Base_Data.ACMeta.metadata ->
      (Base_Data.GFocus.focus * @{AllT_args} data) list ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper, @{AllT_args} ZLPC.Z3.zipper option) morph
  end

  structure Result_Action :
  sig
    include ZIPPY_LOGGER_MIXIN_BASE
    (* result actions *)
    type result = Base_Data.AAMeta.metadata Base_Data.Tac_Res.result
    val init : Base_Data.PAction.prio -> result -> (@{ParaT_args} @{AllT_args} ZLPC.Z4.zipper,
      @{AllT_args} ZLPC.Z1.zipper) morph

    type @{AllT_args} mk_copy_update_data = result -> (@{ParaT_args} @{AllT_args} ZLPC.Z1.zipper,
      Base_Data.Copy.copy_update_data) morph
    val copy_update_data : @{AllT_args} mk_copy_update_data
    val copy_update_data_changed :
      (Base_Data.GCS.goal_pos list -> Base_Data.GCS.goal_pos Base_Data.Tac_Res.GPU.T.target) ->
      @{AllT_args} mk_copy_update_data
    val copy_update_data_empty_changed : @{AllT_args} mk_copy_update_data

    val init_copy_parents : @{AllT_args} mk_copy_update_data -> Base_Data.PAction.prio ->
      result -> (@{ParaT_args} @{AllT_args} ZLPC.Z4.zipper, @{AllT_args} ZLPC.Z1.zipper) morph

    val action : (result -> (@{ParaT_args} @{AllT_args} ZLPC.Z1.zipper) emorph) ->
      @{AllT_args} mk_copy_update_data -> result -> @{AllT_args} Base_Data.PAction.action
    val changed_goals_action : ((Base_Data.GCS.goal_pos * Base_Data.GCS.gcpos list) list ->
        (@{ParaT_args} @{AllT_args} ZLPC.Z1.zipper) emorph) ->
      @{AllT_args} mk_copy_update_data -> result -> @{AllT_args} Base_Data.PAction.action
    val hom_changed_goals_action :
      (Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper) emorph) list ->
      @{AllT_args} mk_copy_update_data -> result -> @{AllT_args} Base_Data.PAction.action
  end
end

functor Zippy_Instance_PAction(
    structure Z : ZIPPY_INSTANCE
    val mk_exn : (unit -> @{ParaT_args encl: "(" ")"} Z.Exn.ME.exn)
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    structure Log_Base : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_PAction : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_Result_Action : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_LGoals : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_LGoals_Pos_Copy : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_Copy : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_Enum_Copy : ZIPPY_LOGGER_MIXIN_BASE
  ) : ZIPPY_INSTANCE_PACTION =
struct

open Z; open MU
structure ZLP = Zippy_Lists_Positions_Mixin(structure Z = ZLPC; structure Exn = Exn); open ZLP
structure Base_Mixins = struct structure Exn = Exn; structure Co = Co; structure Ctxt = Ctxt end
structure ZL = Zippy_Lists(open Base_Mixins; structure Z = ZLP)
structure ZN = Zippy_Node(open Base_Mixins; structure Z = ZLP)
structure ZE = Zippy_Enum_Mixin(Zippy_Enum_Mixin_Base(open Base_Mixins; structure Z = ZL))

structure Goals = Zippy_Goals_Mixin_Base(open Mixin_Base1 Mixin_Base2)
structure LGoals = Zippy_Lists_Goals_Mixin(open Base_Mixins; structure Z = ZL
  structure Goals = Goals; structure Log = Log_LGoals)
structure Goals_Results = Zippy_Goals_Results_Mixin_Base(open Goals
  structure GClusters_Results = Mixin_Base1.Results; structure GCluster_Results = Mixin_Base2.Results)
structure LGoals_Results = Zippy_Lists_Goals_Results_Mixin(open Base_Mixins; structure Z = ZL
  structure Goals_Results = Goals_Results; structure Log_LGoals = Log_LGoals)
structure Goals_Pos = Zippy_Goals_Pos_Mixin_Base(open Goals; structure GPU = Base_Data.Tac_Res.GPU)
structure Goals_Pos_Copy = Zippy_Goals_Pos_Copy_Mixin(Zippy_Goals_Pos_Copy_Mixin_Base(open Goals_Pos
  structure Copy = Mixin_Base3.Copy))
structure LGoals_Pos_Copy = Zippy_Lists_Goals_Pos_Copy_Mixin(open Base_Mixins; structure Z = ZL
  structure GPC = Goals_Pos_Copy; structure Log = Log_LGoals_Pos_Copy; structure Log_Base = Log_Base
  structure Log_LGoals = Log_LGoals \<^imap>\<open>\<open>{i}\<close> => \<open>structure Show{i} = Show.Zipper{i}\<close>\<close>)
structure PAction_More = Zippy_PAction_Mixin(open Base_Mixins;
  structure PAction = Mixin_Base4.PAction; structure Log = Log_PAction structure Show = Show.Zipper4)
structure Copy = Zippy_Copy_Mixin(open Base_Mixins Mixin_Base3
  structure Log = Log_Copy; structure Show_From = Show.Zipper3; structure Show_To = Show.Zipper1)
structure ECopy = Zippy_Enum_Copy_Mixin(open Base_Mixins; structure Z = ZE
  structure Copy = Copy; structure Log = Log_Enum_Copy; structure Show_To = Show.Zipper1)

local open SC Mo A
in
structure PAction =
struct
local open Base_Data
in
fun disable_action _ = PAction_More.disable_paction (mk_exn ()) >>> arr PAction_More.AResult.Unchanged

type @{AllT_args} data = {
  meta : AMeta.metadata,
  paction : GFocus.focus -> @{AllT_args} PAction.paction}
end
fun update {meta, paction} z = PAction_More.set_paction (paction (Lens4.Focus.getter z)) z
  |> (fn z => Lens4.Meta.modifier (Library.K meta, z))

fun update_action data _ = arr (update data #> Mixin_Base4.PAction.AResult.Unchanged)

fun cons_action {meta, paction} focus = Node.cons4 (mk_exn ()) meta (paction focus) focus

fun cons_action_cluster meta =
  List.map (apsnd (fn data => fn focus => cons_action data focus >>> Up4.morph))
  #> Node.cons3 (mk_exn ()) meta
end

structure Result_Action =
struct
open Log_Result_Action
(* result actions *)
type result = Base_Data.AAMeta.metadata Base_Data.Tac_Res.result

fun init prio {more, gpos_update, state} z =
  let
    fun set_next5 n z = L.set_modify ZN.Node_Next5.modifier (pure n, z)
    fun node_no_next1 gclusters = ZN.node_no_next1 (mk_exn ()) (Node.co1 gclusters)
    fun node_no_next2 parent_top_meta_vars gcluster = ZN.node_no_next2 (mk_exn ())
      (Node.co2 parent_top_meta_vars gcluster)
  in
    Up4.morph z >>= Up3.morph >>= arr Mixin_Base2.Top_Meta_Vars.L.getter
    >>= (fn parent_top_meta_vars => Node.snoc5 (mk_exn ()) more gpos_update prio z
    >>= (fn z => LGoals.init_state (fn gcs => arr (set_next5 (node_no_next1 gcs)) z >>= Down5.morph)
      (node_no_next2 parent_top_meta_vars) state))
  end

type @{AllT_args} mk_copy_update_data = result ->
  (@{ParaT_args} @{AllT_args} Z1.zipper, Mixin_Base3.Copy.copy_update_data) morph

local fun wrap f x z = pure (f (#gpos_update x) (Mixin_Base1.GClusters.L.getter z))
in
fun copy_update_data x = wrap Goals_Pos_Copy.copy_update_data x
fun copy_update_data_changed update = wrap (Goals_Pos_Copy.copy_update_data_changed update)
fun copy_update_data_empty_changed x = wrap Goals_Pos_Copy.copy_update_data_empty_changed x
end

fun init_copy_parents mk_cud prio result = init prio result
  >>> (fn z => mk_cud result z
  >>= (fn cud => ECopy.copy_parents mk_exn cud z))

fun action update mk_cud result prio = init_copy_parents mk_cud prio result
  >>> update result
  >>> Ctxt.with_ctxt (fn ctxt => fn z =>
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
        Pretty.str "Initialising goal results downwards from",
        Show.Zipper1.pretty ctxt z
      ] |> Pretty.block |> Pretty.string_of);
    LGoals_Results.init_goal_results_down1 ctxt z))
  >>> arr fst >>> Up1.morph >>> arr Mixin_Base4.PAction.AResult.Expanded
fun changed_goals_action update = action
  (#gpos_update #> LGoals_Pos_Copy.update_changed_goals_gclusters_gclusters update)
fun hom_changed_goals_action updates = action
  (#gpos_update #> LGoals_Pos_Copy.update_hom_changed_goals_gclusters_gclusters updates)
end
end

end