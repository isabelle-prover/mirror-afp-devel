(*  Title:      Zippy/zippy_goal_cluster_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_CLUSTER_MIXIN =
sig
  include ZIPPY_GOAL_CLUSTER_MIXIN_BASE
  val get_state : @{AllT_args} L.container -> GC.GCS.state
  val get_goals : @{AllT_args} L.container -> term list
  val get_stripped_goals : @{AllT_args} L.container ->
    ((string * typ) list * (term list * term)) list
  val get_ngoals : @{AllT_args} L.container -> int
  val has_meta_vars : @{AllT_args} L.container -> bool
end

functor Zippy_Goal_Cluster_Mixin(
    GCluster : ZIPPY_GOAL_CLUSTER_MIXIN_BASE
  ) : ZIPPY_GOAL_CLUSTER_MIXIN =
struct

open GCluster

fun get_state x = x |> (L.getter #> GC.get_state)
fun get_goals x = x |> (L.getter #> GC.get_goals)
fun get_stripped_goals x = x |> (L.getter #> GC.get_stripped_goals)
fun get_ngoals x = x |> (L.getter #> GC.get_ngoals)
fun has_meta_vars x = x |> (L.getter #> GC.has_meta_vars)

end
