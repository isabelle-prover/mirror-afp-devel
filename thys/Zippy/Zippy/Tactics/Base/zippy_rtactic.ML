(*  Title:      Zippy/zippy_rtactic.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_RTACTIC =
sig
  include ZIPPY_RTACTIC_RESULT
  (*standard Isabelle tactic, equal to state -> state Seq.seq*)
  type tactic = Tactical.tactic
  (*generalised result tactic*)
  type 'm rtactic = state -> 'm result Seq.seq

  (*creates missing data from input and result state*)
  val lift_tac : (state * state -> 'm) -> tactic -> 'm rtactic
  val lift_tac' : ('a -> state * state -> 'm) -> ('a -> tactic) -> 'a -> 'm rtactic
end

functor Zippy_RTactic_Functor(R : ZIPPY_RTACTIC_RESULT) : ZIPPY_RTACTIC =
struct

open R

type tactic = Tactical.tactic
type 'm rtactic = state -> 'm result Seq.seq

fun lift_tac mk_more tac state = tac state
  |> Seq.map (fn state' => result (mk_more (state, state')) state')
fun lift_tac' mk_more tac i state = tac i state
  |> Seq.map (fn state' => result (mk_more i (state, state')) state')
end

structure Zippy_RTactic = Zippy_RTactic_Functor(Zippy_RTactic_Result)