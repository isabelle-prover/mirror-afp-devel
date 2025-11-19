(*  Title: state_result.ML
    Author: Kevin Kappelmann

Types that contain a state and a result value.
*)
signature STATE_RESULT_BASE =
sig

type ('s, 'a) result
val interp : ('s, 'a) result -> ('a * 's)
val result : 's -> 'a -> ('s, 'a) result

val state : ('s, 'a) result -> 's
val value : ('s, 'a) result -> 'a

end

signature STATE_RESULT =
sig

include STATE_RESULT_BASE
val map : ('a -> 's -> ('t, 'b) result) -> ('s, 'a) result -> ('t, 'b) result
val map_state : ('s -> 't) -> ('s, 'a) result -> ('t, 'a) result
val map_value : ('a -> 'b) -> ('s, 'a) result -> ('s, 'b) result
val empty_state_result : 'a -> (unit, 'a) result
val empty_value_result : 's -> ('s, unit) result

end

functor State_Result(S : STATE_RESULT_BASE) : STATE_RESULT =
struct

open S
fun map f = uncurry f o interp
fun map_state f = uncurry result o swap o apsnd f o interp
fun map_value f = uncurry result o swap o apfst f o interp
fun empty_value_result s = result s ()
fun empty_state_result x = result () x

end

(*instances*)

structure Pair_State_Result_Base : STATE_RESULT_BASE =
struct

type ('s, 'a) result = ('a * 's)
val interp = I
val result = rpair
val state = snd
val value = fst

end
