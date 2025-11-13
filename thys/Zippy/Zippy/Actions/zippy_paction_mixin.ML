(*  Title:      Zippy/zippy_paction_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PACTION_MIXIN =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  include ZIPPY_PACTION_MIXIN_BASE
  structure Exn : ZIPPY_EXCEPTION_MIXIN
  sharing type Exn.M.t = M.t

  val no_action : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> @{AllT_args} action
  val no_paction : @{ParaT_args encl: "(" ")"} Exn.ME.exn -> @{AllT_args} paction

  val set_paction : @{AllT_args} paction -> @{AllT_args} zipper -> @{AllT_args} zipper

  val disable_paction : @{ParaT_args encl: "(" ")"} Exn.ME.exn ->
    (@{ParaT_args} @{AllT_args} zipper) emorph

  val get_run_paction : (@{ParaT_args} @{AllT_args} zipper, prio * @{AllT_args} action) morph
  val run_action : prio * @{AllT_args} action -> (@{ParaT_args} @{AllT_args} zipper,
    @{AllT_args} action_result) morph
end

functor Zippy_PAction_Mixin(
    structure PAction : ZIPPY_PACTION_MIXIN_BASE
    structure Exn : ZIPPY_EXCEPTION_MIXIN
    sharing type Exn.M.t = PAction.M.t
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = PAction.M.t
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
    structure Show : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show.t = PAction.zipper
  ) : ZIPPY_PACTION_MIXIN =
struct

open PAction Log
structure MU = Zippy_Monad_Util(M); open MU
structure Exn = Exn; open Exn

fun no_action exn _ = AE.throw' exn
fun no_paction exn = AE.throw' exn |> PAction.paction

local open Mo SC A
in
fun set_paction paction z = L.set_modify L.modifier (paction, z)

fun disable_paction exn z = Ctxt.get_ctxt () >>= arr (fn ctxt =>
  (@{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
      Pretty.str "Disabling paction of",
      Show.pretty ctxt z
    ] |> Pretty.block |> Pretty.string_of);
  set_paction (no_paction exn) z))

fun get_run_paction z = Ctxt.get_ctxt () >>= (fn ctxt =>
  (@{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
      Pretty.str "Running paction of",
      Show.pretty ctxt z
    ] |> Pretty.block |> Pretty.string_of);
  L.getter z |> (fn paction => PAction.run_paction paction z)))

fun run_action (p, action) z = Ctxt.get_ctxt () >>= (fn ctxt =>
  (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
      Pretty.str "Running action of",
      Show.pretty ctxt z
    ] |> Pretty.block |> Pretty.string_of);
  action p z))
end
end
