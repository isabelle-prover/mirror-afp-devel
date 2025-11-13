(*  Title:      Zippy/zippy_action_app_metadata.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_APP_METADATA =
sig
  structure P : ZIPPY_ACTION_APP_PROGRESS
  where type progress = Zippy_Action_App_Progress.progress
  type progress = P.progress

  type cost
  val eq_cost : cost * cost -> bool
  val pretty_cost : cost -> Pretty.T

  type metadata
  val metadata : {progress : progress, cost : cost} -> metadata
  val eq_metadata : metadata * metadata -> bool
  val pretty_metadata : metadata SpecCheck_Show.show

  structure Progress : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} container = metadata
  where type @{AllT_args} data = progress

  structure Cost : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} container = metadata
  where type @{AllT_args} data = cost

  val add : (cost * cost -> cost) -> metadata * metadata -> metadata
end

functor Zippy_Action_App_Metadata(
    type cost
    val eq_cost : cost * cost -> bool
    val pretty_cost : cost -> Pretty.T
  ) : ZIPPY_ACTION_APP_METADATA =
struct

structure P = Zippy_Action_App_Progress
type progress = P.progress

type cost = cost
val eq_cost = eq_cost
val pretty_cost = pretty_cost

datatype metadata = Metadata of {
  progress : progress,
  cost : cost
}
val metadata = Metadata

fun eq_metadata (m1 as Metadata {progress = progress1, cost = cost1},
  m2 as Metadata {progress = progress2, cost = cost2}) =
  pointer_eq (m1, m2) orelse progress1 = progress2 orelse eq_cost (cost1, cost2)
fun pretty_metadata (Metadata {progress, cost}) = SpecCheck_Show_Base.record [
    ("progress", P.pretty progress),
    ("cost", pretty_cost cost)
  ]

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens_Kleisli_Identity"\<close>
structure Base = struct open L; type @{AllT_args} container = metadata end
structure Progress =
struct
  open Base
  type @{AllT_args} data = progress
  fun getter (Metadata {progress,...}) = progress
  fun modifier (f, (Metadata {progress, cost})) = Metadata {progress = f progress, cost = cost}
  fun lens _ = L.mk_lens getter modifier
end

structure Cost =
struct
  open Base
  type @{AllT_args} data = cost
  fun getter (Metadata {cost,...}) = cost
  fun modifier (f, (Metadata {progress, cost})) = Metadata {progress = progress, cost = f cost}
  fun lens _ = L.mk_lens getter modifier
end

fun add add_cost (Metadata {progress = progress1, cost = cost1},
  Metadata {progress = progress2, cost = cost2}) =
  let val progress =
    if forall (equal P.promising) [progress1, progress2]
    then P.promising else P.unclear
  in Metadata {progress = progress, cost = add_cost (cost1, cost2)} end

end
