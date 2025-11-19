(*  Title:      Zippy/alternating_zipper_path_util.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_PATH_UTIL"\<close> =
sig
  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_PATH"\<close>
  structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val move_path{i} : path{i} ->
    (@{ParaT_args} @{AllT_args} Z.Z1.zipper, @{AllT_args} Z.Z{i}.zipper) Z.morph
  val move_path_from_root_rev{i} : Zipper_Position.pos list ->
    (@{ParaT_args} @{AllT_args} Z.Z1.zipper, @{AllT_args} Z.Z{i}.zipper) Z.morph
  val move_path_from_root{i} : Zipper_Position.pos list ->
    (@{ParaT_args} @{AllT_args} Z.Z1.zipper, @{AllT_args} Z.Z{i}.zipper) Z.morph\<close>\<close>
end

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Path_Util"\<close>(
    Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  ) : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_PATH_UTIL"\<close> =
struct

open \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Path"\<close>
structure Z = Z; open Z
structure PosU = \<^eval>\<open>sfx_ParaT_nargs "Zipper_Position_Util"\<close>(M)

local
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(M)
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A)
  open SC
in
fun move_path1 (Pos pos) = PosU.move_pos Z1.ZM.Left.morph Z1.ZM.Right.morph Z1.ZM.Down.morph pos
  | move_path1 (Path1 (pos, p)) = \<^eval>\<open>"move_path" ^ pred_mod_nzippers 1\<close> p
    >>> \<^eval>\<open>"Down" ^ pred_mod_nzippers 1 ^ ".morph"\<close>
    >>> move_path1 (Pos pos)
\<^imap>\<open>\<open>{i}\<close> => \<open>
and move_path{i} (Path{i} (pos, p)) = move_path\<^eval>\<open>pred_mod_nzippers {i}\<close> p
  >>> Down\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>morph
  >>> PosU.move_pos Z{i}.ZM.Left.morph Z{i}.ZM.Right.morph Z{i}.ZM.Down.morph pos
\<close> start: 2\<close>
end

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun move_path_from_root_rev{i} x = path_from_root_rev{i} x |> move_path{i}
fun move_path_from_root{i} x = path_from_root{i} x |> move_path{i}\<close>\<close>

end
