(*  Title:      Zippy/zippy_goals_pos_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_POS_MIXIN =
sig
  include ZIPPY_GOALS_POS_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>

  (*creates index of changed goal indices and its new goal cluster positions from created goal
  clusters zipper and the goal position update information it originated from*)
  val changed_goals_index : GPU.GCS.goal_pos GPU.gpos_update ->
    (@{ParaT_args} @{AllT_args} GClusters.L.container,
      (GPU.GCS.goal_pos * GPU.GCS.gcpos list) list) morph
end

functor Zippy_Goals_Pos_Mixin(
    structure Z : ZIPPY_BASE_BASE
    structure Goals_Pos : ZIPPY_GOALS_POS_MIXIN_BASE
    sharing type Goals_Pos.GClusters.L.container = Z.Z1.zipper
    sharing type Goals_Pos.GCluster.L.container = Z.Z2.zipper
  ) : ZIPPY_GOALS_POS_MIXIN =
struct

open Z Goals_Pos
structure MU = Zippy_Monad_Util(M); open MU
structure GClusters = Zippy_Goal_Clusters_Mixin(GClusters)
structure GCluster = Zippy_Goal_Cluster_Mixin(GCluster)

local open Mo A
in
fun changed_goals_index gpos_update z =
  Up1.morph z >>= Up5.morph >>= Up4.morph >>= Up3.morph >>= arr GCluster.get_ngoals
  >>= arr (fn ngoals =>
    let
      val gcpos_index = GClusters.L.getter z |> GClusters.GCS.get_gcpos_index
      fun collect_changed i =
        let val gpos = i + 1
        in case gpos_update gpos of
          GPU.T.Changed gposs => cons (gpos, List.map gcpos_index gposs)
        | GPU.T.Moved _ => I
        end
    in fold_range collect_changed ngoals [] end)
end

end

