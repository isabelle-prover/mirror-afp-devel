(*  Title:      Zippy/zippy_goals_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_MIXIN_BASE =
sig
  structure GClusters : ZIPPY_GOAL_CLUSTERS_MIXIN_BASE

  structure GCluster : ZIPPY_GOAL_CLUSTER_MIXIN_BASE
  sharing type GCluster.GC.GCS.gcpos = GClusters.GCS.gcpos
  sharing type GCluster.GC.GCS.gclusters = GClusters.GCS.gclusters
end

functor Zippy_Goals_Mixin_Base(A :
  sig
    structure GClusters : ZIPPY_GOAL_CLUSTERS_MIXIN_BASE

    structure GCluster : ZIPPY_GOAL_CLUSTER_MIXIN_BASE
    sharing type GCluster.GC.GCS.gcpos = GClusters.GCS.gcpos
    sharing type GCluster.GC.GCS.gclusters = GClusters.GCS.gclusters
  end) : ZIPPY_GOALS_MIXIN_BASE
  = A