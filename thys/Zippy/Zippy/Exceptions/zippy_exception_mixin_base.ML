(*  Title:      Zippy/zippy_exception_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_EXCEPTION_MIXIN_BASE =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  structure ME : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>
  sharing type ME.t = M.t
end

functor Zippy_Exception_Mixin_Base(
    ME : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>
  ) : ZIPPY_EXCEPTION_MIXIN_BASE
  =
struct
structure ME = ME
structure MB = \<^eval>\<open>sfx_ParaT_nargs "Morph_Base"\<close>(ME)
open MB
end