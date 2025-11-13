(*  Title:      Zippy/coroutine.ML
    Author:     Kevin Kappelmann

(Alternating) coroutines.
Note: could be generalised to indexed categories if needed.
*)
signature \<^eval>\<open>sfx_ParaT_nargs "COROUTINE"\<close> =
sig
  structure C : \<^eval>\<open>sfx_ParaT_nargs "CATEGORY_BASE"\<close>

  type (@{ParaT_args} 'a, 'b, 'c) acoroutine
  type (@{ParaT_args} 'a, 'b) coroutine = (@{ParaT_args} 'a, 'b, 'b) acoroutine

  val acoroutine : (@{ParaT_args} 'a, 'b * (@{ParaT_args} 'a, 'c, 'b) acoroutine) C.morph ->
    (@{ParaT_args} 'a, 'b, 'c) acoroutine
  val coroutine : (@{ParaT_args} 'a, 'b * (@{ParaT_args} 'a, 'b) coroutine) C.morph ->
    (@{ParaT_args} 'a, 'b) coroutine
  val resume : (@{ParaT_args} 'a, 'b, 'c) acoroutine -> (@{ParaT_args} 'a, 'b *
    (@{ParaT_args} 'a, 'c, 'b) acoroutine) C.morph
end

functor \<^eval>\<open>sfx_ParaT_nargs "Coroutine"\<close>(C : \<^eval>\<open>sfx_ParaT_nargs "CATEGORY_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE"\<close> =
struct
structure C = C

datatype (@{ParaT_args} 'a, 'b, 'c) acoroutine =
  Coroutine of (@{ParaT_args} 'a, 'b * (@{ParaT_args} 'a, 'c, 'b) acoroutine) C.morph

type (@{ParaT_args} 'a, 'b) coroutine = (@{ParaT_args} 'a, 'b, 'b) acoroutine

fun acoroutine c = Coroutine c
fun coroutine c = acoroutine c
fun resume (Coroutine c) = c

end
