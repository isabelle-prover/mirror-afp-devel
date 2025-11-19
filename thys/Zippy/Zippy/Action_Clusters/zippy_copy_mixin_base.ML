(*  Title:      Zippy/zippy_copy_mixin_base.ML
    Author:     Kevin Kappelmann

Copy mechanism.
*)
signature ZIPPY_COPY_MIXIN_BASE =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>

  type @{AllT_args} copy
  type @{AllT_args} zipper_from
  type @{AllT_args} zipper_to

  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type L.container = zipper_from
  sharing type L.data = copy

  type copy_update_data

  val copy : (copy_update_data -> @{AllT_args} zipper_from ->
    (@{ParaT_args} @{AllT_args} zipper_to) emorph) -> @{AllT_args} copy
  val run_copy : @{AllT_args} copy -> copy_update_data ->
    @{AllT_args} zipper_from -> (@{ParaT_args} @{AllT_args} zipper_to) emorph
end

functor Zippy_Copy_Mixin_Base(A :
  sig
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    type @{AllT_args} zipper_to
    type copy_update_data
    val copy : (copy_update_data -> @{AllT_args} L.container ->
      (@{ParaT_args} @{AllT_args} zipper_to) M.emorph) -> @{AllT_args} L.data
    val run_copy : @{AllT_args} L.data -> copy_update_data ->
      @{AllT_args} L.container -> (@{ParaT_args} @{AllT_args} zipper_to) M.emorph
  end
  ) : ZIPPY_COPY_MIXIN_BASE
  =
struct
open A A.M
type @{AllT_args} zipper_from = @{AllT_args} L.container
type @{AllT_args} copy = @{AllT_args} L.data
end
