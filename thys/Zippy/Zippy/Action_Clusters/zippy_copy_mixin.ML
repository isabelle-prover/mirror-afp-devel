(*  Title:      Zippy/zippy_copy_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_COPY_MIXIN =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  include ZIPPY_COPY_MIXIN_BASE

  val get_run_copy : copy_update_data -> @{AllT_args} zipper_from ->
    (@{ParaT_args} @{AllT_args} zipper_to) emorph
end

functor Zippy_Copy_Mixin(
    structure Copy : ZIPPY_COPY_MIXIN_BASE
    structure Exn : ZIPPY_EXCEPTION_MIXIN
    sharing type Exn.M.t = Copy.M.t
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Copy.M.t
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
    structure Show_From : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show_From.t = Copy.zipper_from
    structure Show_To : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show_To.t = Copy.zipper_to
  ) : ZIPPY_COPY_MIXIN =
struct

open Copy Log
structure MU = Zippy_Monad_Util(M); open MU

local open Mo
in
fun get_run_copy cud z3 z1 = Ctxt.get_ctxt () >>= (fn ctxt =>
  (@{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
      Pretty.block [Pretty.str "Running copy from ", Show_From.pretty ctxt z3],
      Pretty.block [Pretty.str "to ", Show_To.pretty ctxt z1]
    ] |> Pretty.block |> Pretty.string_of);
  L.getter z3 |> (run_copy #> (fn copy => copy cud z3 z1))))
end
end