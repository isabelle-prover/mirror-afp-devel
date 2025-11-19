(*  Title:      Zippy/zippy_state_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_STATE_MIXIN =
sig
  include ZIPPY_STATE_MIXIN_BASE
  structure AS : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_STATE"\<close>
  where type (@{ParaT_args} 'i, 'j, 'a) K.M.t = (@{ParaT_args} 'i, 'j, 'a) MS.t

  val with_state_select : (@{ParaT_arg 0} -> 's) -> ('s -> (@{ParaT_args} 'a, 'b) morph) ->
    (@{ParaT_args} 'a, 'b) morph
  val with_state : (@{ParaT_arg 0} -> (@{ParaT_args} 'a, 'b) morph) -> (@{ParaT_args} 'a, 'b) morph
end

functor Zippy_State_Mixin(
    State : ZIPPY_STATE_MIXIN_BASE
  ) : ZIPPY_STATE_MIXIN =
struct
open State
structure AS = \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_State"\<close>(MS)

fun with_state_select select f = AS.access (fn (x, s) => f (select s) x)
fun with_state f = with_state_select I f

end
