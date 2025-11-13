(*  Title:      Zippy/alternating_zipper_util.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_UTIL"\<close> =
sig
  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>

  (* movements *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val top{i} : (@{ParaT_args} @{AllT_args} Z{i}.zipper, @{AllT_args} Z1.zipper) morph\<close>\<close>
end

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Util"\<close>(
    structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
    structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REPEAT"\<close>
    sharing type AE.K.M.t = Z.M.t
  ) : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_UTIL"\<close> =
struct

open Z

local
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(Z.M)
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A)
  open SC
in
(* movements *)
fun top1 x = x |> (AE.repeat
  (\<^imap>\<open>\<open>{j}\<close> =>\<open>Up\<^eval>\<open>ML_Gen.sub_mod_nzippers' 1 ({j} - 1) ^ "."\<close>morph\<close> sep: ">>>"\<close>))
\<^imap>\<open>\<open>{i}\<close> => \<open>
fun top{i} x = x |> (Up{i}.morph >>> top\<^eval>\<open>string_of_int ({i} - 1)\<close>)
\<close> start: 2\<close>

end

end
