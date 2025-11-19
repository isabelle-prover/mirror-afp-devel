(*  Title:      Zippy/zippy_paction_mixin_base.ML
    Author:     Kevin Kappelmann

Actions with priority.
*)
signature ZIPPY_PACTION_MIXIN_BASE =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  type @{AllT_args} paction
  type @{AllT_args} zipper
  type @{AllT_args} zipper_expanded
  type @{AllT_args} zipper_changed

  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type L.container = zipper
  sharing type L.data = paction

  structure AResult : ZIPPY_ACTION_RESULT

  type prio
  type @{AllT_args} action_result =
    (@{AllT_args} zipper, @{AllT_args} zipper_expanded, @{AllT_args} zipper_changed) AResult.result
  type @{AllT_args} action = prio -> (@{ParaT_args} @{AllT_args} zipper,
    @{AllT_args} action_result) morph

  val paction : (@{ParaT_args} @{AllT_args} zipper, prio * @{AllT_args} action) morph ->
    @{AllT_args} paction
  val run_paction : @{AllT_args} paction ->
    (@{ParaT_args} @{AllT_args} zipper, prio * @{AllT_args} action) morph
end

functor Zippy_PAction_Mixin_Base(A :
  sig
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    type @{AllT_args} zipper_expanded
    type @{AllT_args} zipper_changed
    structure AResult : ZIPPY_ACTION_RESULT
    type prio
    val paction : (@{ParaT_args} @{AllT_args} L.container, prio *
        (prio -> (@{ParaT_args} @{AllT_args} L.container,
          (@{AllT_args} L.container, @{AllT_args} zipper_expanded, @{AllT_args} zipper_changed)
            AResult.result) M.morph)) M.morph ->
      @{AllT_args} L.data
    val run_paction : @{AllT_args} L.data -> (@{ParaT_args} @{AllT_args} L.container, prio *
      (prio -> (@{ParaT_args} @{AllT_args} L.container,
        (@{AllT_args} L.container, @{AllT_args} zipper_expanded, @{AllT_args} zipper_changed)
          AResult.result) M.morph)) M.morph
  end
  ) : ZIPPY_PACTION_MIXIN_BASE
  =
struct
open A A.M

type @{AllT_args} zipper = @{AllT_args} L.container
type @{AllT_args} paction = @{AllT_args} L.data
type @{AllT_args} action_result =
  (@{AllT_args} zipper, @{AllT_args} zipper_expanded, @{AllT_args} zipper_changed) AResult.result
type @{AllT_args} action = prio -> (@{ParaT_args} @{AllT_args} zipper,
  @{AllT_args} action_result) morph
end