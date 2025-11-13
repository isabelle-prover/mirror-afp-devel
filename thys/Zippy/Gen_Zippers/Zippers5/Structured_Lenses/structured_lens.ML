(*  Title:  Zippy/structured_lens.ML
    Author: Kevin Kappelmann

Lenses with fixed, explicit types.
*)
signature \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close> =
sig
  (*we stick to Kleisli lenses such that getters and modifers can be typed polymorphically without
  using a unit argument (as needed for the lens)*)
  include \<^eval>\<open>sfx_ParaT_nargs "LENS_KLEISLI"\<close>

  type @{AllT_args} container
  type @{AllT_args} data

  val lens : unit -> (@{ParaT_args} @{AllT_args} container, @{AllT_args} data) slens
  val getter : (@{ParaT_args} @{AllT_args} container, @{AllT_args} data) getter
  val modifier : (@{ParaT_args} @{AllT_args} container, @{AllT_args} data) smodifier
end

functor \<^eval>\<open>sfx_T_nargs "Structured_Lens"\<close>(
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS_KLEISLI"\<close>
    type @{AllT_args} container
    type @{AllT_args} data
    val lens : unit -> (@{ParaT_args} @{AllT_args} container, @{AllT_args} data) L.slens
  ) :
    \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} container
    where type @{AllT_args} data = @{AllT_args} data
  =
struct

open L
type @{AllT_args} container = @{AllT_args} container
type @{AllT_args} data = @{AllT_args} data

val lens = lens
fun getter x = get (lens ()) x
fun modifier x = modify (lens ()) x

end
