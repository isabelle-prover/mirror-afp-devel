(*  Title:      Zippy/zippy_goal_pos_update_util.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_POS_UPDATE_UTIL =
sig
  include ZIPPY_GOAL_POS_UPDATE
  structure F : ZIPPY_GOAL_FOCUS
  sharing type F.GCS.gcpos = GCS.gcpos
  sharing type F.GCS.gclusters = GCS.gclusters

  val single_goal_gpos_update : GCS.goal_pos -> int -> GCS.goal_pos gpos_update

  type focus_update = F.focus -> (GCS.cluster_pos * F.focus) list
  val focus_update : GCS.gcpos gpos_update -> focus_update
  val focus_update_comp_gclusters : GCS.gclusters -> GCS.goal_pos gpos_update -> focus_update
end

functor Zippy_Goal_Pos_Update_Util(
    structure GPU : ZIPPY_GOAL_POS_UPDATE
    structure F : ZIPPY_GOAL_FOCUS
    sharing type F.GCS.gcpos = GPU.GCS.gcpos
    sharing type F.GCS.gclusters = GPU.GCS.gclusters
  ) : ZIPPY_GOAL_POS_UPDATE_UTIL =
struct

structure F = F
open GPU

fun single_goal_gpos_update i nnew_goals j = if j < i
  then T.Moved j
  else if j = i then T.Changed (i upto i + nnew_goals - 1)
  else T.Moved (j + nnew_goals - 1)

type focus_update = F.focus -> (GCS.cluster_pos * F.focus) list
local
  structure SA = \<^eval>\<open>sfx_ParaT_nargs "SArrow_Arrow_Apply"\<close>
  fun dest_gpos_update gpos_update gpos = gpos_update gpos
    |> T.map (SA.A.&&& (GCS.get_gcpos_cluster, GCS.get_gcpos_goal))
in
fun focus_update gpos_update (F.Goals gpos) = gpos
  |> Library.maps (dest_gpos_update gpos_update #> (fn T.Moved t => [t] | T.Changed ts => ts))
  |> partition_eq (eq_fst (op =))
  |> map (SA.A.&&& (hd #> fst, map snd #> F.sort_goals))

fun focus_update_comp_gclusters gclusters = comp_gclusters_gpos_update gclusters #> focus_update
end
end

structure Standard_Zippy_Goal_Pos_Update_Util = Zippy_Goal_Pos_Update_Util(
  structure GPU = Standard_Zippy_Goal_Pos_Update
  structure F = Standard_Zippy_Goal_Focus)
