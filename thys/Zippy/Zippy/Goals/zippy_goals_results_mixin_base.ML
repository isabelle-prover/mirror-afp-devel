(*  Title:      Zippy/zippy_goals_results_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_RESULTS_MIXIN_BASE =
sig
  include ZIPPY_GOALS_MIXIN_BASE
  structure Results : ZIPPY_GOAL_RESULTS
  structure GClusters_Results : ZIPPY_GOAL_RESULTS_MIXIN_BASE
  sharing type GClusters_Results.L.container = GClusters.L.container
  sharing type GClusters_Results.R.results = Results.results
  structure GCluster_Results : ZIPPY_GOAL_RESULTS_MIXIN_BASE
  sharing type GCluster_Results.L.container = GCluster.L.container
  sharing type GCluster_Results.R.results = Results.results
end

functor Zippy_Goals_Results_Mixin_Base(A :
  sig
    include ZIPPY_GOALS_MIXIN_BASE
    structure GClusters_Results : ZIPPY_GOAL_RESULTS_MIXIN_BASE
    sharing type GClusters_Results.L.container = GClusters.L.container
    structure GCluster_Results : ZIPPY_GOAL_RESULTS_MIXIN_BASE
    sharing type GCluster_Results.L.container = GCluster.L.container
    sharing type GCluster_Results.R.results = GClusters_Results.R.results
  end) : ZIPPY_GOALS_RESULTS_MIXIN_BASE
  =
struct
open A
structure Results = GClusters_Results.R
end