(*  Title:      Zippy/zippy_ctxt_state_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_CTXT_STATE_MIXIN =
sig
  include ZIPPY_CTXT_STATE_MIXIN_BASE
  structure AS : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_STATE"\<close>
  sharing type AS.K.M.t = MS.t

  val with_ctxt : (Proof.context -> (@{ParaT_args} 'a, 'b) morph) -> (@{ParaT_args} 'a, 'b) morph
  val get_ctxt : unit -> (@{ParaT_args} Proof.context) M.t
  val with_context : (Context.generic -> (@{ParaT_args} 'a, 'b) morph) -> (@{ParaT_args} 'a, 'b) morph
  val get_context : unit -> (@{ParaT_args} Context.generic) M.t
end

functor Zippy_Ctxt_State_Mixin(
    Ctxt : ZIPPY_CTXT_STATE_MIXIN_BASE
  ) : ZIPPY_CTXT_STATE_MIXIN =
struct
open Ctxt
structure AS = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_State"\<close>(MS)

fun with_ctxt f = AS.access (fn (x, s) => f s x)
fun get_ctxt _ = MS.get ()
fun with_context f = with_ctxt (Context.Proof #> f)
fun get_context _ = get_ctxt () |> M.map Context.Proof
end
