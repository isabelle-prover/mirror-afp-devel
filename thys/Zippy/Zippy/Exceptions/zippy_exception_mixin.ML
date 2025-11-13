(*  Title:      Zippy/zippy_exception_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_EXCEPTION_MIXIN =
sig
  include ZIPPY_EXCEPTION_MIXIN_BASE
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REPEAT"\<close>
  sharing type AE.K.M.t = M.t
  sharing type AE.exn = ME.exn
end

functor Zippy_Exception_Mixin(
    Exn : ZIPPY_EXCEPTION_MIXIN_BASE
  ) : ZIPPY_EXCEPTION_MIXIN =
struct
open Exn
structure AE = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception_Repeat"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception"\<close>(ME))
end
