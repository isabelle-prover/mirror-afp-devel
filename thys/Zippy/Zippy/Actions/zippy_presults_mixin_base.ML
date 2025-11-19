(*  Title:      Zippy/zippy_presults_mixin_base.ML
    Author:     Kevin Kappelmann

Results with priorities.
*)
signature ZIPPY_PRESULTS_MIXIN_BASE =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  type @{AllT_args} presults
  type @{AllT_args} zipper
  type prio
  type result
  structure Co : ZIPPY_COROUTINE_MIXIN_BASE
  sharing type Co.M.t = M.t
  (*(prio, result) acoroutine*)
  val presults : (@{ParaT_args} @{AllT_args} zipper, prio, result) Co.Co.acoroutine ->
    @{AllT_args} presults
  val dest_presults : @{AllT_args} presults ->
    (@{ParaT_args} @{AllT_args} zipper, prio, result) Co.Co.acoroutine
  (*(prio * result sequence) coroutine*)
  type @{AllT_args} presultsq =
    (*return next prio (estimate) while (optionally) updating the sequence*)
    (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) Co.Co.coroutine
end

functor Zippy_PResults_Mixin_Base(A :
  sig
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
    type @{AllT_args} presults
    type @{AllT_args} zipper
    type prio
    type result
    structure Co : ZIPPY_COROUTINE_MIXIN_BASE
    sharing type Co.M.t = M.M.t
    val presults : (@{ParaT_args} @{AllT_args} zipper, prio, result) Co.Co.acoroutine ->
      @{AllT_args} presults
    val dest_presults : @{AllT_args} presults ->
      (@{ParaT_args} @{AllT_args} zipper, prio, result) Co.Co.acoroutine
  end
  ) : ZIPPY_PRESULTS_MIXIN_BASE
  =
struct
open A A.M
type @{AllT_args} presultsq =
  (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) Co.Co.coroutine
end
