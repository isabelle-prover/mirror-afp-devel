(*  Title:      Zippy/zippy_ctxt_state_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_CTXT_STATE_MIXIN_BASE =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  structure MS : \<^eval>\<open>sfx_ParaT_nargs "MONAD_STATE_BASE"\<close>
  where type s = Proof.context
  sharing type MS.t = M.t
end

functor Zippy_Ctxt_State_Mixin_Base(
    MS : \<^eval>\<open>sfx_ParaT_nargs "MONAD_STATE_BASE"\<close>
    where type s = Proof.context
  ) : ZIPPY_CTXT_STATE_MIXIN_BASE
  =
struct
structure MS = MS
structure MB = \<^eval>\<open>sfx_ParaT_nargs "Morph_Base"\<close>(MS)
open MB
end