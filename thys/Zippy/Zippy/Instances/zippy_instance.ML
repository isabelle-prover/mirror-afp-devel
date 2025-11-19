(*  Title:      Zippy/zippy_instance.ML
    Author:     Kevin Kappelmann

Basic infrastructure.
*)
signature ZIPPY_INSTANCE =
sig
  include ZIPPY_INSTANCE_BASE

  (* lenses *)
  structure Lens1 :
  sig
    structure GClusters : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ZLPC.Z1.zipper
    where type @{AllT_args} data = Base_Data.GCS.gclusters
    structure Results : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ZLPC.Z1.zipper
    where type @{AllT_args} data = Base_Data.GResults.results
  end
  structure Lens2 :
  sig
    structure GCluster : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ZLPC.Z2.zipper
    where type @{AllT_args} data = Base_Data.GC.gcluster
    structure Results : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ZLPC.Z2.zipper
    where type @{AllT_args} data = Base_Data.GResults.results
    structure Top_Meta_Vars : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ZLPC.Z2.zipper
    where type @{AllT_args} data = Base_Data.TMV.top_meta_vars
  end
  structure Lens3 :
  sig
    structure Copy : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ZLPC.Z3.zipper
    where type @{AllT_args} data = @{AllT_args} Base_Data.Copy.copy
    structure Meta : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ZLPC.Z3.zipper
    where type @{AllT_args} data = Base_Data.ACMeta.metadata
  end
  structure Lens4 :
  sig
    structure PAction : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ZLPC.Z4.zipper
    where type @{AllT_args} data = @{AllT_args} Base_Data.PAction.paction
    structure Action_App_Num : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ZLPC.Z4.zipper
    where type @{AllT_args} data = Base_Data.AANum.action_app_num
    structure Focus : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ZLPC.Z4.zipper
    where type @{AllT_args} data = Base_Data.GFocus.focus
    structure Meta : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ZLPC.Z4.zipper
    where type @{AllT_args} data = Base_Data.AMeta.metadata
  end
  structure Lens5 :
  sig
    structure Action_App_Num : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ZLPC.Z5.zipper
    where type @{AllT_args} data = Base_Data.AANum.action_app_num
    structure Focus : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ZLPC.Z5.zipper
    where type @{AllT_args} data = Base_Data.GFocus.focus
    structure Prio : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ZLPC.Z5.zipper
    where type @{AllT_args} data = Base_Data.PAction.prio
    structure GPos_Update : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ZLPC.Z5.zipper
    where type @{AllT_args} data = Base_Data.Tac_Res.gpos_update
    structure Meta : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ZLPC.Z5.zipper
    where type @{AllT_args} data = Base_Data.AAMeta.metadata
  end

  (* pretty printing/shows *)
  structure Show :
  sig
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Zipper{i} : ZIPPY_SHOW_MIXIN_BASE
    where type @{AllT_args} t = @{AllT_args} ZLPC.Z{i}.zipper
    structure Container{i} : ZIPPY_SHOW_MIXIN_BASE
    where type @{AllT_args} t = @{AllT_args} ZLPC.Z{i}.ZM.container\<close>\<close>
    structure Prio : ZIPPY_SHOW_MIXIN_BASE
    where type @{AllT_args} t = Base_Data.PAction.prio
  end

  (* mixins *)
  structure MU : ZIPPY_MONAD_UTIL
  sharing type MU.Mo.t = M.t
  structure Co : ZIPPY_COROUTINE_MIXIN_BASE
  sharing type Co.ME.exn = Exn.ME.exn
  sharing type Co.M.t = M.t

  (** data **)
  structure Mixin_Base1 :
  sig
    structure GClusters : ZIPPY_GOAL_CLUSTERS_MIXIN_BASE
    where type @{AllT_args} L.container = @{AllT_args} Lens1.GClusters.container
    where type GCS.gcpos = Base_Data.GCS.gcpos
    where type GCS.gclusters = Base_Data.GCS.gclusters
    structure Results : ZIPPY_GOAL_RESULTS_MIXIN_BASE
    where type @{AllT_args} L.container = @{AllT_args} Lens1.Results.container
    where type R.results = Base_Data.GResults.results
  end
  structure Mixin_Base2 :
  sig
    structure GCluster : ZIPPY_GOAL_CLUSTER_MIXIN_BASE
    where type @{AllT_args} L.container = @{AllT_args} Lens2.GCluster.container
    where type GC.gcluster = Base_Data.GC.gcluster
    where type GC.GCS.gcpos = Base_Data.GCS.gcpos
    where type GC.GCS.gclusters = Base_Data.GCS.gclusters
    structure Results : ZIPPY_GOAL_RESULTS_MIXIN_BASE
    where type @{AllT_args} L.container = @{AllT_args} Lens2.Results.container
    where type R.results = Base_Data.GResults.results
    structure Top_Meta_Vars : ZIPPY_TOP_META_VARS_MIXIN_BASE
    where type @{AllT_args} L.container = @{AllT_args} Lens2.Top_Meta_Vars.container
  end
  structure Mixin_Base3 :
  sig
    structure Copy : ZIPPY_COPY_MIXIN_BASE
    where type @{AllT_args} L.container = @{AllT_args} Lens3.Copy.container
    where type @{AllT_args} copy = @{AllT_args} Base_Data.Copy.copy
    where type @{AllT_args} zipper_from = @{AllT_args} Base_Data.Copy.zipper_from
    where type @{AllT_args} zipper_to = @{AllT_args} Base_Data.Copy.zipper_to
    where type copy_update_data = Base_Data.Copy.copy_update_data
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) M.t
    structure Meta : ZIPPY_ACTION_CLUSTER_METADATA_MIXIN_BASE
    where type @{AllT_args} L.container = @{AllT_args} Lens3.Meta.container
    where type Meta.metadata = Base_Data.ACMeta.metadata
  end
  structure Mixin_Base4 :
  sig
    structure PAction : ZIPPY_PACTION_MIXIN_BASE
    where type @{AllT_args} L.container = @{AllT_args} Lens4.PAction.container
    where type @{AllT_args} paction = @{AllT_args} Base_Data.PAction.paction
    where type @{AllT_args} zipper = @{AllT_args} Base_Data.PAction.zipper
    where type @{AllT_args} zipper_expanded = @{AllT_args} Base_Data.PAction.zipper_expanded
    where type @{AllT_args} zipper_changed = @{AllT_args} Base_Data.PAction.zipper_changed
    where type prio = Base_Data.PAction.prio
    where type ('u, 'e, 'c) AResult.result = ('u, 'e, 'c) Base_Data.PAction.AResult.result
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) M.t
    structure Action_App_Num : ZIPPY_ACTION_APP_NUM_MIXIN_BASE
    where type @{AllT_args} L.container = @{AllT_args} Lens4.Action_App_Num.container
    structure Focus : ZIPPY_GOAL_FOCUS_MIXIN_BASE
    where type @{AllT_args} L.container = @{AllT_args} Lens4.Focus.container
    where type F.focus = Base_Data.GFocus.focus
    where type F.GCS.gcpos = Base_Data.GCS.gcpos
    where type F.GCS.gclusters = Base_Data.GCS.gclusters
    structure Meta : ZIPPY_ACTION_CLUSTER_METADATA_MIXIN_BASE
    where type @{AllT_args} L.container = @{AllT_args} Lens4.Meta.container
    where type Meta.metadata = Base_Data.AMeta.metadata
  end
  structure Mixin_Base5 :
  sig
    structure Action_App_Num : ZIPPY_ACTION_APP_NUM_MIXIN_BASE
    where type @{AllT_args} L.container = @{AllT_args} Lens5.Action_App_Num.container
    structure Focus : ZIPPY_GOAL_FOCUS_MIXIN_BASE
    where type @{AllT_args} L.container = @{AllT_args} Lens5.Focus.container
    where type F.focus = Base_Data.GFocus.focus
    where type F.GCS.gcpos = Base_Data.GCS.gcpos
    where type F.GCS.gclusters = Base_Data.GCS.gclusters
    structure Prio : ZIPPY_PRIO_MIXIN_BASE
    where type @{AllT_args} L.container = @{AllT_args} Lens5.Prio.container
    where type prio = Base_Data.PAction.prio
    structure Meta : ZIPPY_ACTION_APP_METADATA_MIXIN_BASE
    where type @{AllT_args} L.container = @{AllT_args} Lens5.Meta.container
    where type Meta.metadata = Base_Data.AAMeta.metadata
  end

  (* nodes *)
  structure Node :
  sig
    val co1 : Base_Data.GCS.gclusters -> @{AllT_args} ZLPC.ZN.N1.content
    val co2 : Base_Data.TMV.top_meta_vars -> Base_Data.GC.gcluster -> @{AllT_args} ZLPC.ZN.N2.content
    val co3 : Base_Data.ACMeta.metadata -> @{AllT_args} Base_Data.Copy.copy ->
      @{AllT_args} ZLPC.ZN.N3.content
    val co4 : Base_Data.AMeta.metadata -> @{AllT_args} Base_Data.PAction.paction ->
      Base_Data.GFocus.focus -> @{AllT_args} ZLPC.ZN.N4.content
    val co5 : Base_Data.AAMeta.metadata -> Base_Data.Tac_Res.gpos_update ->
      Base_Data.PAction.prio -> @{AllT_args} ZLPC.Z4.zipper -> @{AllT_args} ZLPC.ZN.N5.content

    val cons3 : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.ACMeta.metadata ->
      (Base_Data.GFocus.focus * (Base_Data.GFocus.focus ->
        (@{ParaT_args} @{AllT_args} ZLPC.Z3.zipper) emorph)) list ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z2.zipper, @{AllT_args} ZLPC.Z3.zipper option) morph
    val cons4 : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.AMeta.metadata ->
      @{AllT_args} Base_Data.PAction.paction -> Base_Data.GFocus.focus ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z3.zipper, @{AllT_args} ZLPC.Z4.zipper) morph
    (*Note: results are added to the back since this keeps the paths of existing nodes (e.g. those
    stored in a queue during search) unchanged.*)
    val snoc5 : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> Base_Data.AAMeta.metadata ->
      Base_Data.Tac_Res.gpos_update -> Base_Data.PAction.prio ->
      (@{ParaT_args} @{AllT_args} ZLPC.Z4.zipper, @{AllT_args} ZLPC.Z5.zipper) morph
  end
end

functor Zippy_Instance(
    structure Z : ZIPPY_INSTANCE_BASE
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    structure Log_Base : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_LGoals : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_LGoals_Pos_Copy : ZIPPY_LOGGER_MIXIN_BASE
    structure Show_Prio : ZIPPY_SHOW_MIXIN_BASE
    where type @{AllT_args} t = Z.Base_Data.PAction.prio
  ) : ZIPPY_INSTANCE
  =
struct

open Z
structure ZLP = Zippy_Lists_Positions_Mixin(structure Z = ZLPC; structure Exn = Exn); open ZLP
structure ZN = Zippy_Node(structure Z = ZLP; structure Exn = Exn)

(* lenses *)
local
  open Base_Data
  structure Base =
  struct
    structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens_Kleisli_Identity"\<close>
    fun gen_mk_lens l getter modifier = L.comp (L.mk_lens getter (uncurry modifier)) (l ())
  end
in
local structure Base =
  struct
    open Base
    structure NCB = NCB1
    type @{AllT_args} container = @{AllT_args} Z1.zipper
    fun mk_lens x = gen_mk_lens ZN.Node_Co1.lens x
  end
in
structure Lens1 =
struct
  structure NCB = Base.NCB
  structure GClusters = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = GCS.gclusters
    fun lens _ = mk_lens NCB.get_gclusters NCB.map_gclusters)
  structure Results = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = GResults.results
    fun lens _ = mk_lens NCB.get_results NCB.map_results)
end
end
local structure Base =
  struct
    open Base
    structure NCB = NCB2
    type @{AllT_args} container = @{AllT_args} Z2.zipper
    fun mk_lens x = gen_mk_lens ZN.Node_Co2.lens x
  end
in
structure Lens2 =
struct
  structure NCB = Base.NCB
  structure GCluster = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = GC.gcluster
    fun lens _ = mk_lens NCB.get_gcluster NCB.map_gcluster)
  structure Results = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = GResults.results
    fun lens _ = mk_lens NCB.get_results NCB.map_results)
  structure Top_Meta_Vars = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = TMV.top_meta_vars
    fun lens _ = mk_lens NCB.get_top_meta_vars NCB.map_top_meta_vars)
end
end
local structure Base =
  struct
    open Base
    structure NCB = NCB3
    type @{AllT_args} container = @{AllT_args} Z3.zipper
    fun mk_lens x = gen_mk_lens ZN.Node_Co3.lens x
  end
in
structure Lens3 =
struct
  structure NCB = Base.NCB
  structure Copy = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = @{AllT_args} Copy.copy
    fun lens _ = mk_lens NCB.get_copy NCB.map_copy)
  structure Meta = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = ACMeta.metadata
    fun lens _ = mk_lens NCB.get_meta NCB.map_meta)
end
end
local structure Base =
  struct
    open Base
    structure NCB = NCB4
    type @{AllT_args} container = @{AllT_args} Z4.zipper
    fun mk_lens x = gen_mk_lens ZN.Node_Co4.lens x
  end
in
structure Lens4 =
struct
  structure NCB = Base.NCB
  structure PAction = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = @{AllT_args} PAction.paction
    fun lens _ = mk_lens NCB.get_paction NCB.map_paction)
  structure Action_App_Num = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = AANum.action_app_num
    fun lens _ = mk_lens NCB.get_action_app_num NCB.map_action_app_num)
  structure Focus = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = GFocus.focus
    fun lens _ = mk_lens NCB.get_focus NCB.map_focus)
  structure Meta = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = AMeta.metadata
    fun lens _ = mk_lens NCB.get_meta NCB.map_meta)
end
end
local structure Base =
  struct
    open Base
    structure NCB = NCB5
    type @{AllT_args} container = @{AllT_args} Z5.zipper
    fun mk_lens x = gen_mk_lens ZN.Node_Co5.lens x
  end
in
structure Lens5 =
struct
  structure Action_App_Num = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = AANum.action_app_num
    fun lens _ = mk_lens NCB.get_action_app_num NCB.map_action_app_num)
  structure Focus = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = GFocus.focus
    fun lens _ = mk_lens NCB.get_focus NCB.map_focus)
  structure Prio = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = PAction.prio
    fun lens _ = mk_lens NCB.get_prio NCB.map_prio)
  structure GPos_Update = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = Base_Data.Tac_Res.gpos_update
    fun lens _ = mk_lens NCB.get_gpos_update NCB.map_gpos_update)
  structure Meta = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
    type @{AllT_args} data = AAMeta.metadata
    fun lens _ = mk_lens NCB.get_meta NCB.map_meta)
end
end

(* pretty printing/shows *)
local
  fun with_position pretty_position z p = Pretty.breaks [
      p,
      Pretty.block [Pretty.str "at position ", pretty_position z]
    ] |> Pretty.block0
  structure ZCost = Zippy_Collect_Trace_Mixin(ZLPC.ZCollect)
  fun with_cost_trace get_trace z p = Pretty.breaks [
      p,
      Pretty.block [Pretty.str "with cost trace ",
        ZCost.pretty_trace Base_Data.AAMeta.pretty_cost (get_trace z)]
    ] |> Pretty.block0
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  fun pretty_zipper{i} z = SpecCheck_Show.record
    #> with_position ZLP.pretty_position_zipper{i} z
    #> with_cost_trace ZCost.ZZCollect_Co{i}.getter z\<close>\<close>
in
structure Show =
struct
  structure Prio = Show_Prio
  local structure L = Lens1
  in
  structure Zipper1 = Zippy_Show_Mixin_Base(
    type @{AllT_args} t = @{AllT_args} Z1.zipper
    fun pretty ctxt z = pretty_zipper1 z [
      ("Goal clusters", GCS.pretty_gclusters ctxt (L.GClusters.getter z)),
      ("Results", GResults.pretty_results (L.Results.getter z))
    ])
  end
  local structure L = Lens2
  in
  structure Zipper2 = Zippy_Show_Mixin_Base(
    type @{AllT_args} t = @{AllT_args} Z2.zipper
    fun pretty ctxt z = pretty_zipper2 z [
      ("Goal cluster", GC.pretty_gcluster ctxt (L.GCluster.getter z)),
      ("Results", GResults.pretty_results (L.Results.getter z)),
      ("Top Meta Variables", TMV.pretty ctxt (L.Top_Meta_Vars.getter z))
    ])
  end
  local structure L = Lens3
  in
  structure Zipper3 = Zippy_Show_Mixin_Base(
    type @{AllT_args} t = @{AllT_args} Z3.zipper
    fun pretty _ z = pretty_zipper3 z [
      ("Metadata", ACMeta.pretty_metadata (L.Meta.getter z))
    ])
  end
  local structure L = Lens4
  in
  structure Zipper4 = Zippy_Show_Mixin_Base(
    type @{AllT_args} t = @{AllT_args} Z4.zipper
    fun pretty _ z = pretty_zipper4 z [
      ("Action application number", AANum.pretty (L.Action_App_Num.getter z)),
      ("Focus", GFocus.pretty (L.Focus.getter z)),
      ("Metadata", AMeta.pretty_metadata (L.Meta.getter z))
    ])
  end
  local structure L = Lens5
  in
  structure Zipper5 = Zippy_Show_Mixin_Base(
    type @{AllT_args} t = @{AllT_args} Z5.zipper
    fun pretty ctxt z = pretty_zipper5 z [
      ("Action application number", AANum.pretty (L.Action_App_Num.getter z)),
      ("Focus", GFocus.pretty (L.Focus.getter z)),
      ("Priority", Prio.pretty ctxt (L.Prio.getter z)),
      ("Metadata", AAMeta.pretty_metadata (L.Meta.getter z))
    ])
  end
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Container{i} = Zippy_Show_Mixin_Base(
    type @{AllT_args} t = @{AllT_args} Z{i}.ZM.container
    fun pretty _ c = Pretty.str "container{i}" |> with_position ZLP.pretty_position_container{i} c)\<close>\<close>
  end
end
end

(* mixins *)
structure MU = Zippy_Monad_Util(M)
structure Co = Zippy_Coroutine_Mixin_Base(open Exn
  structure Co = \<^eval>\<open>sfx_ParaT_nargs "Coroutine_Util"\<close>(
    structure AE = AE; structure Co = \<^eval>\<open>sfx_ParaT_nargs "Coroutine"\<close>(AE)))

local open Base_Data
in
(** data **)
local structure L = Lens1
in
structure Mixin_Base1 =
struct
  structure GClusters = Zippy_Goal_Clusters_Mixin_Base(structure GCS = GCS; structure L = L.GClusters)
  structure Results = Zippy_Goal_Results_Mixin_Base(structure R = GResults; structure L = L.Results)
end
end

local structure L = Lens2
in
structure Mixin_Base2 =
struct
  structure GCluster = Zippy_Goal_Cluster_Mixin_Base(structure GC = GC; structure L = L.GCluster)
  structure Results = Zippy_Goal_Results_Mixin_Base(structure R = GResults; structure L = L.Results)
  structure Top_Meta_Vars = Zippy_Top_Meta_Vars_Mixin_Base(
    structure TMV = TMV; structure L = L.Top_Meta_Vars)
end
end

local structure L = Lens3
in
structure Mixin_Base3 =
struct
  structure Copy = Base_Data.Copy
  structure Meta = Zippy_Action_Cluster_Metadata_Mixin_Base(
    structure Meta = ACMeta; structure L = L.Meta)
end
end

local structure L = Lens4
in
structure Mixin_Base4 =
struct
  structure PAction = Base_Data.PAction
  structure Action_App_Num = Zippy_Action_App_Num_Mixin_Base(
    structure AANum = AANum; structure L = L.Action_App_Num)
  structure Focus = Zippy_Goal_Focus_Mixin_Base(structure F = GFocus; structure L = L.Focus)
  structure Meta = Zippy_Action_Cluster_Metadata_Mixin_Base(
    structure Meta = AMeta; structure L = L.Meta)
end
end

local structure L = Lens5
in
structure Mixin_Base5 =
struct
  structure Action_App_Num = Zippy_Action_App_Num_Mixin_Base(
    structure AANum = AANum; structure L = L.Action_App_Num)
  structure Focus = Zippy_Goal_Focus_Mixin_Base(structure F = GFocus; structure L = L.Focus)
  structure Prio = Zippy_Prio_Mixin_Base(type prio = Mixin_Base4.PAction.prio; structure L = L.Prio)
  structure Meta = Zippy_Action_App_Metadata_Mixin_Base(
    structure Meta = AAMeta; structure L = L.Meta)
end
end

(** compound **)
structure Base_Mixins = struct structure Exn = Exn; structure Co = Co; structure Ctxt = Ctxt end
structure ZL = Zippy_Lists(open Base_Mixins; structure Z = ZLP)
structure Goals = Zippy_Goals_Mixin_Base(open Mixin_Base1 Mixin_Base2)
structure Goals_Pos = Zippy_Goals_Pos_Mixin_Base(open Goals; structure GPU = Base_Data.Tac_Res.GPU)
structure Goals_Pos_Copy = Zippy_Goals_Pos_Copy_Mixin(Zippy_Goals_Pos_Copy_Mixin_Base(open Goals_Pos
  structure Copy = Mixin_Base3.Copy))
structure LGoals_Pos_Copy = Zippy_Lists_Goals_Pos_Copy_Mixin(open Base_Mixins; structure Z = ZL
  structure GPC = Goals_Pos_Copy; structure Log = Log_LGoals_Pos_Copy; structure Log_Base = Log_Base
  structure Log_LGoals = Log_LGoals; \<^imap>\<open>\<open>{i}\<close> => \<open>structure Show{i} = Show.Zipper{i}\<close>\<close>)

(* nodes *)
structure Node =
struct
fun co1 gclusters = {
  gclusters = gclusters,
  results = if GCS.is_finished gclusters
    then GResults.non_empty (Seq.single (GCS.get_state gclusters))
    else GResults.empty}

fun co2 parent_top_meta_vars gcluster = {
  gcluster = gcluster,
  results = GResults.empty,
  top_meta_vars = TMV.init parent_top_meta_vars (GC.get_state gcluster)}

fun co3 meta copy = {meta = meta, copy = copy}
fun co4 meta paction focus = {
  action_app_num = AANum.init,
  focus = focus,
  paction = paction,
  meta = meta}

fun co5 meta gpos_update prio z =
  let
    val action_app_num = Lens4.Action_App_Num.getter z
    val focus = Lens4.Focus.getter z
  in
    {action_app_num = action_app_num, focus = focus, prio = prio, gpos_update = gpos_update,
    meta = meta}
  end

fun cons3 exn meta = LGoals_Pos_Copy.cons_action_cluster exn (co3 meta)
fun cons4 exn meta paction focus = ZL.cons_content_move_safe3 exn (co4 meta paction focus)
fun snoc5 exn meta gpu prio z = ZL.snoc_content_move_safe4 exn (co5 meta gpu prio z) z
end

end
end