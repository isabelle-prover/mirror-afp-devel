(*  Title:      Zippy/zippy_enum_copy_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ENUM_COPY_MIXIN =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  include ZIPPY_COPY_MIXIN_BASE
  structure Co : ZIPPY_COROUTINE_MIXIN_BASE
  sharing type Co.M.t = M.t

  val copy_parents : (unit -> @{ParaT_args encl: "(" ")"} Co.ME.exn) ->
    copy_update_data -> (@{ParaT_args} @{AllT_args} zipper_to) emorph
end

functor Zippy_Enum_Copy_Mixin(
    structure Z : ZIPPY_ENUM_MIXIN
    structure Copy : ZIPPY_COPY_MIXIN
    sharing type Copy.zipper_from = Z.Z3.zipper
    sharing type Copy.zipper_to = Z.Z1.zipper
    sharing type Copy.M.t = Z.M.t
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Copy.M.t
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
    structure Show_To : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show_To.t = Copy.zipper_to
  ) : ZIPPY_ENUM_COPY_MIXIN =
struct

open Z Copy Log
structure MU = Zippy_Monad_Util(M); open MU
structure Co = Co
structure Exn = Zippy_Exception_Mixin(Co)

local open SC Mo Co
in
fun copy_parents mk_exn cud z1 = Ctxt.get_ctxt () >>= (fn ctxt =>
  (@{log Logger.TRACE} ctxt (fn _ => [
      Pretty.block [Pretty.str "Copying parents of ", Show_To.pretty ctxt z1]
    ] |> Pretty.breaks |> Pretty.block |> Pretty.string_of);
  (Up1.morph >>> Up5.morph >>> Up4.morph >>> Z3.ZM.Unzip.morph >>> Z3.ZM.Zip.morph) z1
  >>= (fn z3 => Co.repeat_step_res (K.arr fst)
    (AA.uncurry (Copy.get_run_copy cud) >>> K.arr Co.continue) (DF_Post3.enum_zipper mk_exn)
    (z3, z1))
  >>= K.arr (Co.dest_res #> snd)))
end

end

