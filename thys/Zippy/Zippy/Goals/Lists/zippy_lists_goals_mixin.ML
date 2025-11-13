(*  Title:      Zippy/zippy_lists_goals_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_GOALS_MIXIN =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  include ZIPPY_GOALS_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  structure Co : ZIPPY_COROUTINE_MIXIN_BASE
  sharing type Co.M.t = M.t

  (* lenses *)
  type @{AllT_args} node_gc
  (*sets goal clusters in order of cluster positions, i.e. [cpos 0, cpos 1,,..]*)
  val set_gcluster_list : (GCluster.GC.gcluster -> @{AllT_args} node_gc) ->
    GCluster.GC.gcluster list -> @{AllT_args} GClusters.L.container ->
    @{AllT_args} GClusters.L.container

  (* initialisation *)
  val init_state :
    (@{ParaT_args} GClusters.GCS.gclusters, @{AllT_args} GClusters.L.container) morph ->
    (GCluster.GC.gcluster -> @{AllT_args} node_gc) -> (@{ParaT_args} GClusters.GCS.state,
      @{AllT_args} GClusters.L.container) morph

  (* movements *)
  val move_cpos : GClusters.GCS.cluster_pos ->
    (@{ParaT_args} @{AllT_args} GClusters.L.container, @{AllT_args} GCluster.L.container) morph

  (* gcluster enumerations *)
  type @{AllT_args} container_gc
  (*returns first zipper and remaining enumeration, respecting the order of cluster positions*)
  val enum_gcluster : (@{ParaT_args} @{AllT_args} container_gc,
    @{AllT_args} GCluster.L.container
    * (@{ParaT_args} @{AllT_args} GCluster.L.container, @{AllT_args} GCluster.L.container)
      Co.Co.coroutine) morph

  (*list in order of cluster positions*)
  val gcluster_list : (@{ParaT_args} @{AllT_args} GCluster.L.container,
    @{AllT_args} GCluster.L.container list) morph
end

functor Zippy_Lists_Goals_Mixin(
    structure Z : ZIPPY_LISTS
    structure Goals : ZIPPY_GOALS_MIXIN_BASE
    sharing type Goals.GClusters.L.container = Z.Z1.zipper
    sharing type Goals.GCluster.L.container = Z.Z2.zipper
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
  ) : ZIPPY_LISTS_GOALS_MIXIN =
struct

open Z Log Goals
structure MU = Zippy_Monad_Util(M); open MU
structure Exn = Zippy_Exception_Mixin(Co)
structure ZNU = Zippy_Node(structure Z = Z; structure Exn = Exn)

local open SC A Mo
in
(* lenses *)
type @{AllT_args} node_gc = @{AllT_args} ZN.N2.node

fun set_gcluster_list mk_node gcs z = List.map mk_node gcs
  |> (fn c => L.set_modify ZNU.Node_Next1.modifier (pure c, z))

(* initialisation *)
fun init_state init_gcs mk_gc_node state = Ctxt.get_ctxt () >>= (fn ctxt =>
  let
    val (gcs, gc_list) = GCluster.GC.init_state state
    val _ = @{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
        Pretty.block [Pretty.str "Initialised state ", Zippy_Thm_State.pretty ctxt state,
          Pretty.str "."],
        Pretty.block [Pretty.str "Resulting goal clusters: ",
          GClusters.GCS.pretty_gclusters ctxt gcs]
      ] |> Pretty.block0 |> Pretty.string_of)
  in init_gcs gcs >>= arr (set_gcluster_list mk_gc_node gc_list) end)

(* movements *)
fun move_cpos cpos = Down1.morph >>> C.repeatn cpos Z2.ZM.Down.morph

(* gcluster enumerations *)
type @{AllT_args} container_gc = @{AllT_args} Z2.ZM.container
val enum_gcluster = enum_zipper2
val gcluster_list = list_container_zippers2
end

end