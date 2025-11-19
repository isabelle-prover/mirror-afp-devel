(*  Title:      Zippy/zippy_goal_results_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_RESULTS_MIXIN =
sig
  include ZIPPY_GOAL_RESULTS_MIXIN_BASE
  val get_states : @{AllT_args} L.container -> R.state Seq.seq
  val get_thms : @{AllT_args} L.container -> thm Seq.seq
  val has_results : @{AllT_args} L.container -> bool
  val append_non_empty_states : R.state Seq.seq -> @{AllT_args} L.container ->
    @{AllT_args} L.container
  val set_non_empty_states : R.state Seq.seq -> @{AllT_args} L.container ->
    @{AllT_args} L.container
end

functor Zippy_Goal_Results_Mixin(
    Results : ZIPPY_GOAL_RESULTS_MIXIN_BASE
  ) : ZIPPY_GOAL_RESULTS_MIXIN =
struct

open Results

fun get_states x = x |> (L.getter #> R.get_states)
fun get_thms x = x |> (L.getter #> R.get_thms)
fun has_results x = x |> (L.getter #> R.has_results)
fun append_non_empty_states states x = L.modifier (R.append_non_empty_states states, x)
fun set_non_empty_states states x = L.set_modify L.modifier (R.non_empty states, x)

end
