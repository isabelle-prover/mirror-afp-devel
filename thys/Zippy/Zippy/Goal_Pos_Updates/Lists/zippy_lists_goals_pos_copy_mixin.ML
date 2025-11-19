(*  Title:      Zippy/zippy_lists_goals_pos_copy_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_GOALS_POS_COPY_MIXIN =
sig
  include ZIPPY_GOALS_POS_COPY_MIXIN_BASE
  include ZIPPY_LOGGER_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  sharing type M.t = Copy.M.t
  structure Exn : ZIPPY_EXCEPTION_MIXIN_BASE
  sharing type Exn.M.t = M.t

  val update_gclusters_gclusters :
    (GPU.GCS.cluster_pos * (@{ParaT_args} @{AllT_args} GCluster.L.container) emorph) list ->
    (@{ParaT_args} @{AllT_args} GClusters.L.container) emorph

  val partition_update_gclusters_gclusters :
    ('a list -> (@{ParaT_args} @{AllT_args} GCluster.L.container) emorph) ->
    (GPU.GCS.cluster_pos * 'a) list ->
    (@{ParaT_args} @{AllT_args} GClusters.L.container) emorph

  val partition_update_gcposs_gclusters_gclusters :
    (GPU.GCS.goal_pos list -> (@{ParaT_args} @{AllT_args} GCluster.L.container) emorph) ->
    GPU.GCS.gcpos list -> (@{ParaT_args} @{AllT_args} GClusters.L.container) emorph

  val update_hom_gcposs_gclusters_gclusters :
    (GPU.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} GCluster.L.container) emorph) list ->
    GPU.GCS.gcpos list list -> (@{ParaT_args} @{AllT_args} GClusters.L.container) emorph

  val update_changed_goals_gclusters_gclusters :
    ((GPU.GCS.goal_pos * GPU.GCS.gcpos list) list ->
      (@{ParaT_args} @{AllT_args} GClusters.L.container) emorph) ->
    GPU.GCS.goal_pos GPU.gpos_update -> (@{ParaT_args} @{AllT_args} GClusters.L.container) emorph

  val update_hom_changed_goals_gclusters_gclusters :
    (GPU.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} GCluster.L.container) emorph) list ->
    GPU.GCS.goal_pos GPU.gpos_update -> (@{ParaT_args} @{AllT_args} GClusters.L.container) emorph

  type @{AllT_args} node_co
  val cons_action_cluster : @{ParaT_args encl: "(" ")"} Exn.ME.exn ->
    (*create node content*)
    (@{AllT_args} Copy.copy -> @{AllT_args} node_co) ->
    (*list of pairs of initial focus and updates to perform*)
    (GPU.F.focus * (GPU.F.focus -> (@{ParaT_args} @{AllT_args} Copy.zipper_from) emorph)) list ->
    (@{ParaT_args} @{AllT_args} GCluster.L.container, @{AllT_args} Copy.zipper_from option) morph
end

functor Zippy_Lists_Goals_Pos_Copy_Mixin(
    structure Z : ZIPPY_LISTS
    structure GPC : ZIPPY_GOALS_POS_COPY_MIXIN
    sharing type GPC.GClusters.L.container = Z.Z1.zipper
    sharing type GPC.GCluster.L.container = Z.Z2.zipper
    sharing type GPC.Copy.zipper_from = Z.Z3.zipper
    sharing type GPC.Copy.zipper_to = Z.Z1.zipper
    sharing type GPC.Copy.M.t = Z.M.t
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_Base : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_LGoals : ZIPPY_LOGGER_MIXIN_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Show{i} : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show{i}.t = Z.Z{i}.zipper\<close>\<close>
  ) : ZIPPY_LISTS_GOALS_POS_COPY_MIXIN =
struct

structure PExn = Exn
structure Show = SpecCheck_Show
open Z GPC Log
structure MU = Zippy_Monad_Util(M); open MU
structure Goals_Pos = Zippy_Goals_Pos_Mixin(structure Z = Z; structure Goals_Pos = GPC)
structure LGoals = Zippy_Lists_Goals_Mixin(structure Z = Z; structure Goals = GPC
  structure Ctxt = Ctxt; structure Log = Log_LGoals)
structure Exn = Zippy_Exception_Mixin(Z.Co)
structure ZB = Zippy_Base(structure Z = Z; structure Exn = Exn; structure Ctxt = Ctxt
  structure Log = Log_Base; \<^imap>\<open>\<open>{i}\<close> => \<open>structure Show{i} = Show{i}\<close>\<close>)

local open SC Mo A
in
fun update_gclusters_gclusters updates = updates
  |> List.map (fn (cpos, update) => LGoals.move_cpos cpos >>> update >>> Up2.morph)
  |> ZB.update_zipper1

local structure SA = \<^eval>\<open>sfx_ParaT_nargs "SArrow_Arrow_Apply"\<close>
in
fun partition_update_gclusters_gclusters update = partition_eq (eq_fst (op =))
  #> List.map (SA.A.&&& (hd #> fst, List.map snd #> update))
  #> update_gclusters_gclusters

fun partition_update_gcposs_gclusters_gclusters update =
  List.map (SA.A.&&& (GClusters.GCS.get_gcpos_cluster, GClusters.GCS.get_gcpos_goal))
  #> partition_update_gclusters_gclusters update

fun update_hom_gcposs_gclusters_gclusters updates gcposs =
  (let fun zip_with_pos update = SA.A.&&&
    (GClusters.GCS.get_gcpos_cluster, GClusters.GCS.get_gcpos_goal #> update)
  in
    Library.maps (map2 zip_with_pos updates) gcposs
    |> partition_update_gclusters_gclusters ZB.update_zipper2
  end)
  handle exn as ListPair.UnequalLengths =>
    (warning (Pretty.breaks [
      Pretty.str "Number of updates",
      Pretty.enclose "(" ")" [length updates |> Show.int],
      Pretty.str "does not match with homogeneous number of goal cluster positions",
      Show.list (Show.list GClusters.GCS.pretty_gcpos) gcposs
    ] |> Pretty.block |> Pretty.string_of);
    PExn.reraise exn)

fun update_changed_goals_gclusters_gclusters update gpos_update z =
  Goals_Pos.changed_goals_index gpos_update z >>= (fn iposs => update iposs z)

fun update_hom_changed_goals_gclusters_gclusters updates = update_changed_goals_gclusters_gclusters
  (List.map snd #> update_hom_gcposs_gclusters_gclusters updates)

type @{AllT_args} node_co = @{AllT_args} ZN.N3.content
fun cons_action_cluster exn mk_node update_focus_list = if null update_focus_list
  then Ctxt.with_ctxt (fn ctxt => fn z => (@{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
      Pretty.str "Skipping consing of action cluster with empty updates list",
      Show2.pretty ctxt z
    ] |> Pretty.block |> Pretty.string_of);
    pure NONE))
  else
    let
      fun init_copy cud _ = GPC.focus_list_apply_copy_update_data cud update_focus_list
        |> partition_update_gclusters_gclusters (cons_action_cluster exn mk_node
          #> (fn cons_action => fn z => cons_action z >>= AC.opt (K z) Up3.morph))
      val node = mk_node (Copy.copy init_copy)
      val update_action_cluster = ZB.update_zipper3 (List.map (fn (x, f) => f x) update_focus_list)
    in cons_content_move_safe2 exn node >>> update_action_cluster >>> arr SOME end
end
end
end
