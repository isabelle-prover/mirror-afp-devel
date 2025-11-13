(*  Title:      Zippy/enumerate_alternating_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>mk_name ["ENUMERATE", pfx_sfx_nargs "ALTERNATING_ZIPPER"]\<close> =
sig
  structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
  where type (@{ParaT_args} 'a, 'b) C.morph = (@{ParaT_args} 'a, 'b) Z.morph
  (*enumerate zippers starting from the first passed zipper*)
  val enum_zipper1 :
    (*exception for empty coroutine*)
    (unit -> @{ParaT_args encl: "(" ")"} Co.AE.exn) ->
    (@{ParaT_args} @{AllT_args} Z.Z1.zipper, @{AllT_args} Z.Z1.zipper) Co.coroutine
  (*returns first zipper and remaining enumeration*)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val enum_zipper{i} : (unit -> @{ParaT_args encl: "(" ")"} Co.AE.exn) ->
    (@{ParaT_args} @{AllT_args} Z.Z{i}.zipper, @{AllT_args} Z.Z1.zipper *
      (@{ParaT_args} @{AllT_args} Z.Z1.zipper, @{AllT_args} Z.Z1.zipper) Co.coroutine) Z.morph
  \<close> start: 2\<close>
end