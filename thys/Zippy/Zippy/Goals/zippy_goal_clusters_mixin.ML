(*  Title:      Zippy/zippy_goal_clusters_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_CLUSTERS_MIXIN =
sig
  include ZIPPY_GOAL_CLUSTERS_MIXIN_BASE
  val get_state : @{AllT_args} L.container -> GCS.state
  val is_finished : @{AllT_args} L.container -> bool
  val has_meta_vars : @{AllT_args} L.container -> bool
  val finish_cluster_states : Proof.context -> GCS.state list -> @{AllT_args} L.container ->
    GCS.state Seq.seq
  val finish_cluster_statesqs : Proof.context -> GCS.state Seq.seq list ->
    @{AllT_args} L.container -> GCS.state Seq.seq
end

functor Zippy_Goal_Clusters_Mixin(
    GClusters : ZIPPY_GOAL_CLUSTERS_MIXIN_BASE
  ) : ZIPPY_GOAL_CLUSTERS_MIXIN =
struct

open GClusters

fun get_state x = x |> (L.getter #> GCS.get_state)
fun is_finished x = x |> (L.getter #> GCS.is_finished)
fun has_meta_vars x = x |> (L.getter #> GCS.has_meta_vars)
fun finish_cluster_states ctxt cluster_states =
  L.getter #> GCS.finish_cluster_states ctxt cluster_states
fun finish_cluster_statesqs ctxt statesqs = L.getter #> GCS.finish_cluster_statesqs ctxt statesqs

end
