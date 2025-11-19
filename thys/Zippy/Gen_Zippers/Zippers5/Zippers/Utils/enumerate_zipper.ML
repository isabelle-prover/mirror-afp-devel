(*  Title:      Zippy/enumerate_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "ENUMERATE_ZIPPER"\<close> =
sig
  structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
  structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
  where type (@{ParaT_args} 'a, 'b) C.morph = (@{ParaT_args} 'a, 'b) Z.morph
  (*enumerate zippers starting from the first passed zipper*)
  val enum_zipper :
    (*exception for empty coroutine*)
    (unit -> @{ParaT_args encl: "(" ")"} Co.AE.exn) ->
    (@{ParaT_args} @{AllT_args} Z.zipper, @{AllT_args} Z.zipper) Co.coroutine
  (*enumerate zippers below and including the first passed zipper*)
  val enum_zipper_down : (unit -> @{ParaT_args encl: "(" ")"} Co.AE.exn) ->
    (@{ParaT_args} @{AllT_args} Z.zipper, @{AllT_args} Z.zipper) Co.coroutine
end