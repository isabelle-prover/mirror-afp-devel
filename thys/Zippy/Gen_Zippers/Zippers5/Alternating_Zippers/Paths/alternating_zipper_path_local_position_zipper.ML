(*  Title:      Zippy/alternating_zipper_path_local_position_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_PATH_LOCAL_POSITION_ZIPPER"\<close> =
sig
  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_PATH"\<close>
  structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_LOCAL_POSITION_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val path_from_zipper{i} : (@{ParaT_args} @{AllT_args} Z.Z{i}.zipper, path{i}) Z.morph\<close>\<close>
end

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Path_Local_Position_Zipper"\<close>(
    structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_LOCAL_POSITION_ZIPPER"\<close>
    structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION"\<close>
    sharing type AE.K.M.t = Z.M.t
  ) : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_PATH_LOCAL_POSITION_ZIPPER"\<close> =
struct

open \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Path"\<close>
structure AE = AE
structure Z = Z

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(AE); open SC AE Z
in
fun path_from_zipper1 z =
  let val get_pos = Z1.ZD.Co.getter #> N1.Co.getter
  in
    catch'
      (Up1.morph >>> \<^eval>\<open>"path_from_zipper" ^ pred_mod_nzippers 1\<close>
        >>> arr (fn p => Path1 (get_pos z, p)))
      (arr (fn _ => Pos (get_pos z))) z
  end
\<^imap>\<open>\<open>{i}\<close> => \<open>
and path_from_zipper{i} z = z |>
  let val get_pos = Z{i}.ZD.Co.getter #> N{i}.Co.getter
  in
    Up{i}.morph >>> path_from_zipper\<^eval>\<open>pred_mod_nzippers {i}\<close>
    >>> arr (fn p => Path{i} (get_pos z, p))
  end
\<close> start: 2\<close>
end
end

