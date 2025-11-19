(*  Title:      Zippy/zippy_state_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_STATE_MIXIN_BASE =
sig
  structure MS : \<^eval>\<open>sfx_ParaT_nargs "IMONAD_STATE_BASE"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  where type (@{ParaT_args} 'a) M.t = (unit, @{ParaT_arg 0}, @{ParaT_arg 0}, 'a) MS.t
end

functor Zippy_State_Mixin_Base(
    MS : \<^eval>\<open>sfx_ParaT_nargs "IMONAD_STATE_BASE"\<close>
  ) : ZIPPY_STATE_MIXIN_BASE
  =
struct
structure MS = MS
structure MB = \<^eval>\<open>sfx_ParaT_nargs "Morph_Base"\<close>(open MS
  type (@{ParaT_args} 'a) t = (unit, @{ParaT_arg 0}, @{ParaT_arg 0}, 'a) MS.t)
open MB
end