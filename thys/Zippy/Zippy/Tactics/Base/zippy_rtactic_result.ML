(*  Title:      Zippy/zippy_rtactic_result.ML
    Author:     Kevin Kappelmann

Result of a result tactic (rtactic).
*)
signature ZIPPY_RTACTIC_RESULT =
sig
  type state = Zippy_Thm_State.state
  type 'm result = {state : state, more : 'm}

  val result : 'm -> state -> 'm result
  val pretty : 'm SpecCheck_Show_Base.show -> Proof.context -> ('m result) SpecCheck_Show_Base.show

  val get_state : 'm result -> state
  val map_state : (state -> state) -> 'm result -> 'm result

  val get_more : 'm result -> 'm
  val map_more : ('m -> 'n) -> 'm result -> 'n result
end

structure Zippy_RTactic_Result : ZIPPY_RTACTIC_RESULT =
struct

type state = Zippy_Thm_State.state
type 'm result = {state : state, more : 'm}

fun result more state = {state = state, more = more}
fun pretty f ctxt {state, more} = SpecCheck_Show_Base.record [
    ("state", Zippy_Thm_State.pretty ctxt state),
    ("more", f more)
  ]

fun get_state {state,...} = state
fun map_state f {state, more} = {state = f state, more = more}

fun get_more {more,...} = more
fun map_more f {state, more} = {state = state, more = f more}

end
