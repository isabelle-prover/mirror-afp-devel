(*  Title:      Zippy/zippy_ztactic_result.ML
    Author:     Kevin Kappelmann

Result of a zippy tactic (ztactic).
*)
signature ZIPPY_ZTACTIC_RESULT =
sig
  structure GPU : ZIPPY_GOAL_POS_UPDATE_UTIL
  type state = GPU.GCS.state
  type gpos_update = GPU.GCS.goal_pos GPU.gpos_update
  type 'm result = {state : state, gpos_update : gpos_update, more : 'm}

  val result : 'm -> state -> gpos_update -> 'm result
  val pretty : 'm SpecCheck_Show_Base.show -> Proof.context -> ('m result) SpecCheck_Show_Base.show

  val get_state : 'm result -> state
  val map_state : (state -> state) -> 'm result -> 'm result

  val get_gpos_update : 'm result -> gpos_update
  val map_gpos_update : (gpos_update -> gpos_update) -> 'm result -> 'm result

  val get_more : 'm result -> 'm
  val map_more : ('m -> 'n) -> 'm result -> 'n result
end

functor Zippy_ZTactic_Result_Functor(GPU : ZIPPY_GOAL_POS_UPDATE_UTIL) : ZIPPY_ZTACTIC_RESULT =
struct

structure GPU = GPU
type state = GPU.GCS.state
type gpos_update = GPU.GCS.goal_pos GPU.gpos_update
type 'm result = {state : state, more : 'm, gpos_update : gpos_update}

fun result more state gpos_update = {state = state, more = more, gpos_update = gpos_update}

fun pretty f ctxt {state, more,...} = SpecCheck_Show_Base.record [
    ("state", Zippy_Thm_State.pretty ctxt state),
    ("more", f more)
  ]

fun get_state {state,...} = state
fun map_state f {state, more, gpos_update} = {state = f state, more = more, gpos_update = gpos_update}

fun get_gpos_update {gpos_update,...} = gpos_update
fun map_gpos_update f {state, more, gpos_update} =
  {state = state, more = more, gpos_update = f gpos_update}

fun get_more {more,...} = more
fun map_more f {state, more, gpos_update} = {state = state, more = f more, gpos_update = gpos_update}

end

structure Zippy_ZTactic_Result = Zippy_ZTactic_Result_Functor(Zippy_Goal_Pos_Update_Util)