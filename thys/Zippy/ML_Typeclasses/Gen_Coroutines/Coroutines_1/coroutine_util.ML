(*  Title:      Zippy/coroutine_util.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "COROUTINE"\<close>
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "ARROW_EXCEPTION_REPEAT"\<close>
  sharing type AE.morph = C.morph
  val throw : @{ParaT_args encl: "(" ")"} AE.exn -> (@{ParaT_args} 'a, 'b, 'c) acoroutine
  val cons : (@{ParaT_args} 'a, 'b) C.morph -> (@{ParaT_args} 'a, 'c, 'b) acoroutine ->
    (@{ParaT_args} 'a, 'b, 'c) acoroutine
  val append : (@{ParaT_args} 'a, 'b, 'c) acoroutine -> (@{ParaT_args} 'a, 'b, 'c) acoroutine ->
    (@{ParaT_args} 'a, 'c, 'b) acoroutine -> (@{ParaT_args} 'a, 'b, 'c) acoroutine
  val append_co : (@{ParaT_args} 'a, 'b) coroutine -> (@{ParaT_args} 'a, 'b) coroutine ->
    (@{ParaT_args} 'a, 'b) coroutine
  val otherwise : (@{ParaT_args} 'a, 'b, 'c) acoroutine -> (@{ParaT_args} 'a, 'b, 'c) acoroutine ->
    (@{ParaT_args} 'a, 'c, 'b) acoroutine -> (@{ParaT_args} 'a, 'b, 'c) acoroutine
  val otherwise_co : (@{ParaT_args} 'a, 'b) coroutine -> (@{ParaT_args} 'a, 'b) coroutine ->
    (@{ParaT_args} 'a, 'b) coroutine

  val map : (@{ParaT_args} 'b1, 'b2) C.morph -> (@{ParaT_args}  'c1, 'c2) C.morph ->
    (@{ParaT_args} 'a, 'b1, 'c1) acoroutine -> (@{ParaT_args} 'a, 'b2, 'c2) acoroutine
  val map_co : (@{ParaT_args} 'b1, 'b2) C.morph -> (@{ParaT_args} 'a, 'b1) coroutine ->
    (@{ParaT_args} 'a, 'b2) coroutine

  val enum : (@{ParaT_args} 'a) C.emorph -> (@{ParaT_args} unit, 'a) C.morph ->
    (@{ParaT_args} unit, 'a) coroutine
  val enum' : (@{ParaT_args} 'a) C.emorph -> (@{ParaT_args} 'a, 'a) coroutine
  val enum_co : (@{ParaT_args} 'a, 'a) coroutine -> 'a -> (@{ParaT_args} unit, 'a) coroutine

  val flat : (@{ParaT_args} 'a, (@{ParaT_args} 'a, 'b) coroutine) coroutine ->
    (@{ParaT_args} 'a, 'b) coroutine

  (*repeated result collection/folding*)
  type 'a res
  val stop : 'a -> 'a res
  val continue : 'a -> 'a res
  val dest_res : 'a res -> 'a
  val map_res : ('a -> 'b) -> 'a res -> 'b res

  val repeat_res : (@{ParaT_args} 'r, 'a) C.morph -> (@{ParaT_args} 'b, 'r res) C.morph ->
    (@{ParaT_args} 'a, 'b) coroutine -> (@{ParaT_args} 'a, 'r res) C.morph

  val repeat_step_res : (@{ParaT_args} 'b * 'r, 'a) C.morph ->
    (@{ParaT_args} 'b * 'r, 'r res) C.morph -> (@{ParaT_args} 'a, 'b) coroutine ->
    (@{ParaT_args} 'a * 'r, ('b * 'r) res) C.morph

  val repeat_step_res_init : (@{ParaT_args} 'b * 'r, 'a) C.morph ->
    (@{ParaT_args} 'b * 'r, 'r res) C.morph -> (@{ParaT_args} 'b, 'a) C.morph ->
    (@{ParaT_args} 'b, 'r res) C.morph -> (@{ParaT_args} 'a, 'b) coroutine ->
    (@{ParaT_args} 'a, ('b * 'r) res) C.morph
end

functor \<^eval>\<open>sfx_ParaT_nargs "Coroutine_Util"\<close>(
    structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REPEAT"\<close>
    structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE"\<close>
    where type (@{ParaT_args} 'a, 'b) C.morph = (@{ParaT_args} 'a, 'b) AE.morph
  ) : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close> =
struct

open Co
structure AE = AE

local
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(AE); open SC
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(AE.K.M); open M
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Arrow"\<close>(AE); open A
in
fun throw e = AE.throw' e |> acoroutine

fun cons f c = f >>> arr (rpair c) |> acoroutine
fun append c1 c2 c2' =
  AE.catch' (resume c1 >>> second (arr (fn c1 => append_aux c1 c2' c2))) (resume c2) |> acoroutine
and append_aux c1 c2 c2' =
  AE.catch' (resume c1 >>> second (arr (fn c1 => append c1 c2' c2))) (resume c2) |> acoroutine
fun append_co c1 c2 = append c1 c2 c2
fun otherwise c1 c2 c2' =
  AE.catch' (resume c1 >>> second (arr (fn c1 => AE.catch' (resume c1) (resume c2') |> acoroutine)))
    (resume c2)
  |> acoroutine
fun otherwise_co c1 c2 = AE.catch' (resume c1) (resume c2) |> coroutine

fun map f g c = resume c >>> (f *** arr (map2 g f)) |> acoroutine
and map2 f g c = resume c >>> (f *** arr (map g f)) |> acoroutine

fun map_co f = map f f

fun enum next init = init >>> arr (fn x => (x, enum next (fn _ => next x))) |> coroutine
fun enum' next = next >>> arr (fn x => (x, enum' next)) |> coroutine
fun enum_co co x = (fn _ => Co.resume co x >>= (arr fst &&& arr (fn (x, co) => enum_co co x)))
  |> Co.coroutine

fun flat coco = (fn x => Co.resume coco x >>= (fn (co, coco) => resume (append_co co (flat coco)) x))
  |> Co.coroutine

datatype 'a res = Stop of 'a | Continue of 'a

val stop = Stop
val continue = Continue
fun dest_res (Stop x) = x
  | dest_res (Continue x) = x
fun map_res f (Stop x) = Stop (f x)
  | map_res f (Continue x) = Continue (f x)

fun repeat_res_step _ _ (res as Stop _, _) = M.pure res
  | repeat_res_step step cont (x, co) = AE.catch' (arr dest_res >>> step >>> cont co) (id ()) x

fun repeat_res step update co = Co.resume co
  >>> first update
  >>> repeat_res_step step (repeat_res step update)

fun repeat_step_res step update =
  let fun update_co co = first (Co.resume co)
    >>> arr (fn ((x, co), r) => ((x, r), update_co co)) |> coroutine
  in
    update_co
    #> repeat_res (step &&& arr snd) (fn p as (x, _) => update p >>= arr (map_res (pair x)))
  end

fun repeat_step_res_init step update init_step init co = Co.resume co
  >>> AE.try_step (first (fn x => init x >>= arr (map_res (pair x))))
    (first init_step >>> (fn (x, co) => Co.resume co x))
  >>> repeat_res_step (step &&& arr snd) (repeat_step_res step update)
end
end
