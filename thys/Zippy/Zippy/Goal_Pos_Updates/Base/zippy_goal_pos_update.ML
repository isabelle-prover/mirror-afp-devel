(*  Title:      Zippy/zippy_goal_pos_update.ML
    Author:     Kevin Kappelmann

Goal position updates.
*)
signature ZIPPY_GOAL_POS_UPDATE_TARGET =
sig
  datatype 't target = Moved of 't | Changed of 't list
  val empty_changed : 't target
  val pretty : 't SpecCheck_Show.show -> 't target SpecCheck_Show.show
  include \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  where type (@{ParaT_args} 'a) t = 'a target
end

structure Zippy_Goal_Pos_Update_Target : ZIPPY_GOAL_POS_UPDATE_TARGET =
struct
datatype 't target = Moved of 't | Changed of 't list
val empty_changed = Changed []

fun pretty f (Moved t) = Pretty.breaks [Pretty.str "Moved", Pretty.enclose "(" ")" [f t]]
      |> Pretty.block
  | pretty f (Changed ts) = Pretty.breaks [Pretty.str "Changed", SpecCheck_Show.list f ts]
      |> Pretty.block

type (@{ParaT_args} 'a) t = 'a target
fun map f (Moved t) = Moved (f t)
  | map f (Changed ts) = Changed (List.map f ts)
fun pure x = Moved x
fun bind (Moved t) f = f t
  | bind (Changed ts) f = Library.maps (f #> (fn Moved t => [t] | Changed ts => ts)) ts |> Changed
fun f <*> x = bind f (fn f => map f x)
end

signature ZIPPY_GOAL_POS_UPDATE =
sig
  structure GCS : ZIPPY_GOAL_CLUSTERS
  structure T : ZIPPY_GOAL_POS_UPDATE_TARGET
  structure A : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW"\<close>
  where type (@{ParaT_args} 'a) K.M.t = (@{ParaT_args} 'a) T.t

  type 't gpos_update = GCS.goal_pos -> 't T.target
  val id : GCS.goal_pos gpos_update
  val comp : 't gpos_update -> GCS.goal_pos gpos_update -> 't gpos_update
  val comp_pure : 't gpos_update -> (GCS.goal_pos -> GCS.goal_pos) -> 't gpos_update
  val pure_comp : (GCS.goal_pos -> 't) -> GCS.goal_pos gpos_update -> 't gpos_update

  val update : GCS.goal_pos -> 't T.target -> 't gpos_update -> 't gpos_update
  val update_changed : ('t list -> 't T.target) -> 't gpos_update -> 't gpos_update

  val comp_gclusters_gpos_update : GCS.gclusters -> GCS.goal_pos gpos_update ->
    GCS.gcpos gpos_update
end

functor Zippy_Goal_Pos_Update_Functor(
    structure GCS : ZIPPY_GOAL_CLUSTERS
    structure T : ZIPPY_GOAL_POS_UPDATE_TARGET
  ) : ZIPPY_GOAL_POS_UPDATE =
struct

structure GCS = GCS
structure T = T

type 't gpos_update = GCS.goal_pos -> 't T.target

structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(T)
val id = A.id ()

val comp = A.comp
fun comp_pure f g = f o g
fun pure_comp f g p = g p |> T.map f

fun update p = General_Util.fun_update (equal p)
fun update_changed f gpos_update = gpos_update #> (fn T.Changed ts => f ts | T.Moved x => T.Moved x)

fun comp_gclusters_gpos_update gclusters = pure_comp (GCS.get_gcpos_index gclusters)

end

structure Zippy_Goal_Pos_Update = Zippy_Goal_Pos_Update_Functor(
  structure GCS = Zippy_Goal_Clusters
  structure T = Zippy_Goal_Pos_Update_Target)
