(*  Title:      Zippy/zippy_coroutine_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_COROUTINE_MIXIN_BASE =
sig
  include ZIPPY_EXCEPTION_MIXIN_BASE
  structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
  where type (@{ParaT_args} 'a, 'b) C.morph = (@{ParaT_args} 'a, 'b) morph
  sharing type Co.AE.exn = ME.exn
end

functor Zippy_Coroutine_Mixin_Base(A :
  sig
    include ZIPPY_EXCEPTION_MIXIN_BASE
    structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
    where type (@{ParaT_args} 'a, 'b) C.morph = (@{ParaT_args} 'a, 'b) morph
    sharing type Co.AE.exn = ME.exn
  end
  ) : ZIPPY_COROUTINE_MIXIN_BASE
  = A