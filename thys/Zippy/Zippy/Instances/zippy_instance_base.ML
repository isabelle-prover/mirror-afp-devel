(*  Title:      Zippy/zippy_instance_base.ML
    Author:     Kevin Kappelmann

Base data and skeleton of the standard zippy instance.
*)
@{record (sig) ZIPPY_INSTANCE_NODE_CO_BASE1 [gclusters, results]}
@{record (sig) ZIPPY_INSTANCE_NODE_CO_BASE2 [gcluster, results, top_meta_vars]}
@{record (sig) ZIPPY_INSTANCE_NODE_CO_BASE3 [copy, meta]}
@{record (sig) ZIPPY_INSTANCE_NODE_CO_BASE4 [paction, action_app_num, focus, meta]}
@{record (sig) ZIPPY_INSTANCE_NODE_CO_BASE5 [action_app_num, focus, prio, gpos_update, meta]}

signature ZIPPY_INSTANCE_BASE =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  structure Base_Data :
  sig
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure NCB{i} : ZIPPY_INSTANCE_NODE_CO_BASE{i}\<close>\<close>
    structure GCS : ZIPPY_GOAL_CLUSTERS
    structure GResults : ZIPPY_GOAL_RESULTS
    structure GC : ZIPPY_GOAL_CLUSTER
    sharing type GC.GCS.gcpos = GCS.gcpos
    sharing type GC.GCS.gclusters = GCS.gclusters
    structure TMV : ZIPPY_TOP_META_VARS
    structure Tac_Res : ZIPPY_ZTACTIC_RESULT
    sharing type Tac_Res.GPU.GCS.gcpos = GCS.gcpos
    sharing type Tac_Res.GPU.GCS.gclusters = GCS.gclusters
    structure Copy : ZIPPY_COPY_MIXIN_BASE
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) M.t
    where type copy_update_data = Tac_Res.GPU.focus_update
    structure ACMeta : ZIPPY_ACTION_CLUSTER_METADATA
    structure PAction : ZIPPY_PACTION_MIXIN_BASE
    sharing type PAction.M.t = Copy.M.t
    structure AANum : ZIPPY_ACTION_APP_NUM
    structure GFocus : ZIPPY_GOAL_FOCUS
    sharing type GFocus.focus = Tac_Res.GPU.F.focus
    sharing type GFocus.GCS.gcpos = GCS.gcpos
    sharing type GFocus.GCS.gclusters = GCS.gclusters
    structure AMeta : ZIPPY_ACTION_METADATA
    structure AAMeta : ZIPPY_ACTION_APP_METADATA
  end

  structure Exn : ZIPPY_EXCEPTION_MIXIN
  sharing type Exn.M.t = M.t

  structure ZLPC : ZIPPY_LISTS_POSITIONS_COLLECT_TRACE_MIXIN_BASE
  where type @{AllT_args} ZN.N1.content =
    (Base_Data.GCS.gclusters, Base_Data.GResults.results) Base_Data.NCB1.data
  where type @{AllT_args} ZN.N2.content =
    (Base_Data.GC.gcluster, Base_Data.GResults.results, Base_Data.TMV.top_meta_vars)
      Base_Data.NCB2.data
  where type @{AllT_args} ZN.N3.content =
    (@{AllT_args} Base_Data.Copy.copy, Base_Data.ACMeta.metadata) Base_Data.NCB3.data
  where type @{AllT_args} ZN.N4.content =
    (@{AllT_args} Base_Data.PAction.paction, Base_Data.AANum.action_app_num, Base_Data.GFocus.focus,
      Base_Data.AMeta.metadata) Base_Data.NCB4.data
  where type @{AllT_args} ZN.N5.content =
    (Base_Data.AANum.action_app_num, Base_Data.GFocus.focus, Base_Data.PAction.prio,
      Base_Data.Tac_Res.gpos_update, Base_Data.AAMeta.metadata) Base_Data.NCB5.data
  where type @{AllT_args} ZCollect.data = Base_Data.AAMeta.cost
  sharing type ZLPC.Z3.zipper = Base_Data.Copy.zipper_from
  sharing type ZLPC.Z1.zipper = Base_Data.Copy.zipper_to
  sharing type ZLPC.Z4.zipper = Base_Data.PAction.zipper
  sharing type ZLPC.Z5.zipper = Base_Data.PAction.zipper_expanded
  sharing type ZLPC.Z1.zipper = Base_Data.PAction.zipper_changed
  sharing type ZLPC.ZN_AZ2.L.M.exn = Exn.ME.exn
  sharing type ZLPC.M.t = M.t
end

functor Zippy_Instance_Base(
    structure ME : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>
    where type @{ParaT_args encl: "(" ")"} exn = unit
    type prio
    type cost
    val eq_cost : cost * cost -> bool
    val pretty_cost : cost -> Pretty.T
    val update_cost : cost -> (cost * cost list) option -> cost
  ) :
  sig
    include ZIPPY_INSTANCE_BASE
    structure Container :
    sig
      \<^imap>\<open>\<open>{i}\<close> => \<open>
      val container{i} : (cost * cost list) option -> @{AllT_args} ZLPC.ZP.ZGPos.Z{i}.ZM.container ->
        @{AllT_args} ZLPC.ZP.ZLPos.Z{i}.ZM.container ->
        @{AllT_args} ZLPC.ZP.ZDepth.Z{i}.ZM.container -> @{AllT_args} ZLPC.ZN.Z{i}.ZM.container ->
        @{AllT_args} ZLPC.Z{i}.ZM.container
      val init_container{i} : @{AllT_args} ZLPC.ZN.Z{i}.ZM.container ->
        @{AllT_args} ZLPC.Z{i}.ZM.container\<close>\<close>
    end
  end =
struct

structure Base_Data =
struct
  @{record (struct) NCB1 ZIPPY_INSTANCE_NODE_CO_BASE1 [gclusters, results]}
  @{record (struct) NCB2 ZIPPY_INSTANCE_NODE_CO_BASE2 [gcluster, results, top_meta_vars]}
  @{record (struct) NCB3 ZIPPY_INSTANCE_NODE_CO_BASE3 [copy, meta]}
  @{record (struct) NCB4 ZIPPY_INSTANCE_NODE_CO_BASE4 [paction, action_app_num, focus, meta]}
  @{record (struct) NCB5 ZIPPY_INSTANCE_NODE_CO_BASE5 [action_app_num, focus, prio, gpos_update, meta]}
  structure GCS = Standard_Zippy_Goal_Clusters
  structure GResults = Zippy_Goal_Results
  structure GC = Standard_Zippy_Goal_Cluster
  structure Tac_Res = Standard_Zippy_ZTactic_Result
  structure TMV = Zippy_Top_Meta_Vars
  structure ACMeta = Zippy_Action_Cluster_Metadata
  structure AANum = Zippy_Action_App_Num
  structure GFocus = Standard_Zippy_Goal_Focus
  structure AMeta = Zippy_Action_Metadata
  structure AAMeta = Zippy_Action_App_Metadata(
    type cost = cost
    val eq_cost = eq_cost
    val pretty_cost = pretty_cost)
end

structure Exn = Zippy_Exception_Mixin(Zippy_Exception_Mixin_Base(ME))

(* construction of alternating zipper *)
local
  open Base_Data
  (** base skeleton **)
  structure ZLP = Zippy_Lists_Positions_Mixin_Base(
    structure Exn = Exn; structure Z = Zippy_Lists_Base(Exn))

  (** add data **)
  type copy_update_data = Base_Data.Tac_Res.GPU.focus_update
  structure AResult = Zippy_Action_Result

  (*** create recursive datatypes and adjoin dependent zipper types ***)
  local structure Z : ZIPPY_BASE_BASE = ZLP; open Z
  in
  datatype @{AllT_args} copy = Copy of copy_update_data -> @{AllT_args} zipper3 ->
    (@{ParaT_args} @{AllT_args} zipper1) emorph
  and @{AllT_args} paction = PAction of (@{ParaT_args} @{AllT_args} zipper4, prio *
    (prio -> (@{ParaT_args} @{AllT_args} zipper4,
      (@{AllT_args} zipper4, @{AllT_args} zipper5, @{AllT_args} zipper1) AResult.result) morph))
    morph
  withtype
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  @{AllT_args} zipper{i} = (@{ParaT_args}
      (GCS.gclusters, GResults.results) NCB1.data,
      (GC.gcluster, GResults.results, TMV.top_meta_vars) NCB2.data,
      (@{AllT_args} copy, ACMeta.metadata) NCB3.data,
      (@{AllT_args} paction, AANum.action_app_num, GFocus.focus, AMeta.metadata)
        NCB4.data,
      (AANum.action_app_num, GFocus.focus, prio, Tac_Res.gpos_update, AAMeta.metadata) NCB5.data
    ) Z{i}.zipper (*instantiated base skeleton*)
    * (cost * cost list) option (*cost trace*)
  \<close> sep: "and"\<close>
  end
  type @{AllT_args} inst1 = (GCS.gclusters, GResults.results) NCB1.data
  type @{AllT_args} inst2 = (GC.gcluster, GResults.results, TMV.top_meta_vars) NCB2.data
  type @{AllT_args} inst3 = (@{AllT_args} copy, ACMeta.metadata) NCB3.data
  type @{AllT_args} inst4 = (@{AllT_args} paction, AANum.action_app_num, GFocus.focus,
    AMeta.metadata) NCB4.data
  type @{AllT_args} inst5 = (AANum.action_app_num, GFocus.focus, prio, Tac_Res.gpos_update,
    AAMeta.metadata) NCB5.data

  (*** instantiate data in base skeleton ***)
  local open ZLP.ZP
  in
  structure ZP :
    ZIPPY_POSITIONS_MIXIN_BASE
    where type @{AllT_args} ZLPos.Z.ZM.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) ZLPos.Z.ZM.zipper
    where type @{AllT_args} ZLPos.Z.ZD.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) ZLPos.Z.ZD.zcontext
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZLPos.Z{i}.ZM.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) ZLPos.Z{i}.ZM.zipper
    where type @{AllT_args} ZLPos.Z{i}.ZD.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) ZLPos.Z{i}.ZD.content
    where type @{AllT_args} ZLPos.Z{i}.ZD.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) ZLPos.Z{i}.ZD.zcontext
    where type @{AllT_args} ZLPos.pzipper{i} = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) ZLPos.pzipper{i}
    where type @{AllT_args} Z{i}.ZM.container = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) Z{i}.ZM.container
    where type @{AllT_args} Z{i}.ZD.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) Z{i}.ZD.content
    where type @{AllT_args} Z{i}.ZD.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) Z{i}.ZD.zcontext
    where type @{AllT_args} Z{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) Z{i}.zipper\<close>\<close>
    = ZLP.ZP
  end
  local open ZLP
  in
  structure ZL :
    ZIPPY_LISTS_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZN_AZ{i}.ZM.container = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) ZN_AZ{i}.ZM.container\<close>
    stop: 1\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZN_AZ{i}.ZD.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) ZN_AZ{i}.ZD.content
    where type @{AllT_args} ZN_AZ{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) ZN_AZ{i}.zipper\<close>
    start: 2\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZN.A.Z{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) ZN.A.Z{i}.zipper
    where type @{AllT_args} ZN.A.N{i}.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) ZN.A.N{i}.content
    where type @{AllT_args} ZN.Z{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) ZN.Z{i}.zipper
    where type @{AllT_args} ZN.zcontext{i} = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) ZN.zcontext{i}
    where type @{AllT_args} ZN.pzipper{i} = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) ZN.pzipper{i}
    where type @{AllT_args} Z{i}.ZM.container = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) Z{i}.ZM.container
    where type @{AllT_args} Z{i}.ZD.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) Z{i}.ZD.content
    where type @{AllT_args} Z{i}.ZD.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) Z{i}.ZD.zcontext
    where type @{AllT_args} Z{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> sep: ","\<close>) Z{i}.zipper\<close>\<close>
    = ZLP
  end
in
(** adjoin dependent zippers **)
local structure ZN = Zippy_Node(structure Z = ZL; structure Exn = Exn)
in
(*the final zipper*)
structure ZLPC = Zippy_Lists_Positions_Collect_Trace_Mixin_Base5(
  structure Z = Zippy_Lists_Positions_Mixin(
    structure Z = struct open ZL; structure ZP = ZP end; structure Exn = Exn)
  type @{AllT_args} data = cost
  fun update z = ZN.Node_Co5.getter z |> NCB5.get_meta |> Base_Data.AAMeta.Cost.getter |> update_cost
  structure Exn = Exn)
end
local structure Z : ZIPPY_BASE_BASE = ZLPC in open Z end

(* zipper mixins *)
structure ZN = Zippy_Node(structure Z = ZLPC; structure Exn = Exn)

structure Container =
struct
\<^imap>\<open>\<open>{i}\<close> => \<open>
fun container{i} a b c d e = ZLPC.container{i} a (ZLP.container{i} b c d e)
fun init_container{i} x = ZLPC.init_container{i} (ZLP.init_container{i} x)\<close>\<close>
end

(* add missing base data structures *)
structure Base_Data =
struct open Base_Data
  structure Base =
  struct
    structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens_Kleisli_Identity"\<close>
    fun gen_mk_lens l getter modifier = L.comp (L.mk_lens getter (uncurry modifier)) (l ())
  end
  local structure Base =
    struct open Base
      structure NCB = NCB3
      type @{AllT_args} container = @{AllT_args} Z3.zipper
      fun mk_lens x = gen_mk_lens ZN.Node_Co3.lens x
    end
  in
  structure Copy = Zippy_Copy_Mixin_Base(
    structure M = Exn
    structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
      type @{AllT_args} data = @{AllT_args} copy
      fun lens _ = mk_lens NCB.get_copy NCB.map_copy)
    type @{AllT_args} zipper_to = @{AllT_args} Z1.zipper
    type copy_update_data = copy_update_data
    val copy = Copy
    fun run_copy (Copy copy) = copy)
  end

  local structure Base =
    struct open Base
      structure NCB = NCB4
      type @{AllT_args} container = @{AllT_args} Z4.zipper
      fun mk_lens x = gen_mk_lens ZN.Node_Co4.lens x
    end
  in
  structure PAction = Zippy_PAction_Mixin_Base(
    structure M = Exn
    structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(open Base
      type @{AllT_args} data = @{AllT_args} paction
      fun lens _ = mk_lens NCB.get_paction NCB.map_paction)
    structure AResult = AResult
    type @{AllT_args} zipper_expanded = @{AllT_args} Z5.zipper
    type @{AllT_args} zipper_changed = @{AllT_args} Z1.zipper
    type prio = prio
    val paction = PAction
    fun run_paction (PAction paction) = paction)
  end
end
end
end