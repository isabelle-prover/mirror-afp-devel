(*  Title:      Zippy/zippy_goal_results.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_RESULTS =
sig
  type results
  val pretty_results : results SpecCheck_Show.show
  type state = Zippy_Thm_State.state
  val get_states : results -> state Seq.seq
  val get_thms : results -> thm Seq.seq
  val has_results : results -> bool

  val empty : results
  val non_empty : state Seq.seq -> results
  val append_non_empty_states : state Seq.seq -> results -> results
  val append : results -> results -> results
end

structure Zippy_Goal_Results : ZIPPY_GOAL_RESULTS =
struct

structure TS = Zippy_Thm_State
structure Show = SpecCheck_Show_Base

type state = Zippy_Thm_State.state

datatype results = Results of {
    states : state Seq.seq,
    has_results : bool
  }

fun results states has_results = Results {states = states, has_results = has_results}
fun get_states (Results {states,...}) = states
val get_thms = get_states #> Seq.map TS.get_thm
fun has_results (Results {has_results,...}) = has_results

fun pretty_results results = Show.record [
    ("has_results", Show.bool (has_results results))
  ]

val empty = results Seq.empty false
fun non_empty states = results states true
fun append_non_empty_states more_states (Results {states,...}) =
  results (Seq.append states more_states) true
fun append results1 results2 =
  (has_results results2 ? append_non_empty_states (get_states results2)) results1

end
