(*  Title:      Zippy/zippy_goals_pos_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_POS_MIXIN_BASE =
sig
  include ZIPPY_GOALS_MIXIN_BASE

  structure GPU : ZIPPY_GOAL_POS_UPDATE_UTIL
  sharing type GPU.GCS.gcpos = GClusters.GCS.gcpos
  sharing type GPU.GCS.gclusters = GClusters.GCS.gclusters
end

functor Zippy_Goals_Pos_Mixin_Base(A :
  sig
    include ZIPPY_GOALS_MIXIN_BASE

    structure GPU : ZIPPY_GOAL_POS_UPDATE_UTIL
    sharing type GPU.GCS.gcpos = GClusters.GCS.gcpos
    sharing type GPU.GCS.gclusters = GClusters.GCS.gclusters
  end) : ZIPPY_GOALS_POS_MIXIN_BASE
  = A
