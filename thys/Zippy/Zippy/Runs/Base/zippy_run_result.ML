(*  Title:      Zippy/zippy_run_result.ML
    Author:     Kevin Kappelmann

Meta variables shared with top-level goal.
*)
signature ZIPPY_RUN_RESULT =
sig
  datatype ('f, 'u) result = Finished of 'f | Unfinished of 'u
  val cases : ('f -> 'a) -> ('u -> 'a) -> ('f, 'u) result -> 'a
  val is_finished : ('f, 'u) result -> bool
  val get_data : ('a, 'a) result -> 'a
end

structure Zippy_Run_Result : ZIPPY_RUN_RESULT =
struct

datatype ('f, 'u) result = Finished of 'f | Unfinished of 'u
fun cases f _ (Finished x) = f x
  | cases _ g (Unfinished x) = g x

fun is_finished (Finished _) = true
  | is_finished (Unfinished _) = false

fun get_data x = cases I I x

end
