(*  Title:      Zippy/zippy_goals_pos_copy_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_POS_COPY_MIXIN =
sig
  include ZIPPY_GOALS_POS_COPY_MIXIN_BASE

  val focus_list_apply_copy_update_data : Copy.copy_update_data -> (GPU.F.focus * 'a) list ->
    (GClusters.GCS.cluster_pos * (GPU.F.focus * 'a)) list

  (*create copy update data from goal position update of applied action and resulting new gclusters*)
  val copy_update_data : GPU.GCS.goal_pos GPU.gpos_update -> GClusters.GCS.gclusters ->
    Copy.copy_update_data
  val copy_update_data_changed : (GPU.GCS.goal_pos list -> GPU.GCS.goal_pos GPU.T.target) ->
    GPU.GCS.goal_pos GPU.gpos_update -> GClusters.GCS.gclusters -> Copy.copy_update_data
  val copy_update_data_empty_changed : GPU.GCS.goal_pos GPU.gpos_update ->
    GClusters.GCS.gclusters -> Copy.copy_update_data
end

functor Zippy_Goals_Pos_Copy_Mixin(
    GPC : ZIPPY_GOALS_POS_COPY_MIXIN_BASE
  ) : ZIPPY_GOALS_POS_COPY_MIXIN =
struct

open GPC

fun focus_list_apply_copy_update_data cud =
  Library.maps (fn (focus, x) => cud focus |> List.map (fn (cpos, focus) => (cpos, (focus, x))))

fun copy_update_data gpos_update gclusters = GPU.focus_update_comp_gclusters gclusters gpos_update
fun copy_update_data_changed update gpos_update = GPU.update_changed update gpos_update
  |> copy_update_data
val copy_update_data_empty_changed = copy_update_data_changed (Library.K GPU.T.empty_changed)

end

