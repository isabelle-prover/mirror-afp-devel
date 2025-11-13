(*  Title:      Zippy/zippy_presults_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PRESULTS_MIXIN =
sig
  include ZIPPY_PRESULTS_MIXIN_BASE

  val empty_presults : @{ParaT_args encl: "(" ")"} Co.ME.exn -> @{AllT_args} presults

  val run_presults : @{AllT_args} presults -> (@{ParaT_args} @{AllT_args} zipper,
    prio * (@{ParaT_args} @{AllT_args} zipper, result, prio) Co.Co.acoroutine) morph

  val gen_presults_from_resultsq :
    (*acoroutine in case of an empty sequence*)
    (@{ParaT_args} @{AllT_args} zipper, result, prio) Co.Co.acoroutine ->
    @{AllT_args} presultsq -> result Seq.seq -> @{AllT_args} presults

  val presults_from_resultsq : @{ParaT_args encl: "(" ")"} Co.ME.exn -> @{AllT_args} presultsq ->
    result Seq.seq -> @{AllT_args} presults

  val pure_presultsq : (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio) Co.Co.coroutine ->
    @{AllT_args} presultsq
  val enum_presultsq : (@{ParaT_args} prio) emorph -> prio -> @{AllT_args} presultsq
end

functor Zippy_PResults_Mixin(
    PResults : ZIPPY_PRESULTS_MIXIN_BASE
  ) : ZIPPY_PRESULTS_MIXIN =
struct

open PResults
structure MU = Zippy_Monad_Util(M); open MU

local open Mo SC A Co
in
fun empty_presults exn = presults (Co.throw exn)

fun run_presults presults = dest_presults presults |> Co.resume

fun gen_aco_from_sq aco_empty_sq presultsq sq =
  let
    fun update pure_presultsq sq =
      arr (fn z => Seq.pull sq |> Either.of_opt |> Either.map_left (Library.K z))
      >>> AC.merge (Co.resume aco_empty_sq)
        (second (arr (gen_aco_from_sq aco_empty_sq pure_presultsq)))
      |> Co.acoroutine
  in
    arr (rpair sq)
    >>> Co.resume presultsq
    >>> arr (fn ((prio, sq), pure_presultsq) => (prio, update pure_presultsq sq))
    |> Co.acoroutine
  end

fun gen_presults_from_resultsq aco_empty_sq presultsq = gen_aco_from_sq aco_empty_sq presultsq
  #> presults

fun presults_from_resultsq exn = gen_presults_from_resultsq (Co.throw exn)

fun pure_presultsq prio_co = (fn (z, sq) => Co.resume prio_co (z, sq)
  >>= arr (fn (p, prio_co) => ((p, sq), pure_presultsq prio_co)))
  |> Co.coroutine

fun enum_presultsq next p =
  let
    val prio_co = Co.enum next (A.K p)
    fun mk_co prio_co = (fn _ => Co.resume prio_co () >>= A.second (arr mk_co)) |> Co.coroutine
  in pure_presultsq (mk_co prio_co) end
end
end
