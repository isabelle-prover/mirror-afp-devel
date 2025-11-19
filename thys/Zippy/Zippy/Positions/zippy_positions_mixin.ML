(*  Title:      Zippy/zippy_positions_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_POSITIONS_MIXIN =
sig
  include ZIPPY_POSITIONS_MIXIN_BASE
  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_PATH_UTIL"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  sharing type Z.Z{i}.ZM.zipper = Z{i}.ZM.zipper
  sharing type Z.Z{i}.ZM.container = Z{i}.ZM.container
  sharing type Z.Z{i}.ZD.zcontext = Z{i}.ZD.zcontext
  sharing type Z.Z{i}.ZD.content = Z{i}.ZD.content\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val path_from_zipper{i} : @{AllT_args} Z{i}.zipper -> path{i}
  val move_zipper{i} : @{AllT_args} Z{i}.zipper ->
    (@{ParaT_args} @{AllT_args} Z1.zipper, @{AllT_args} Z{i}.zipper) morph\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure ZZGPos_Co{i} : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} ZGPos.Z{i}.ZD.content
  sharing type ZZGPos_Co{i}.container = Z{i}.zipper

  structure ZZLPos_Co{i} : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} ZLPos.Z{i}.ZD.content
  sharing type ZZLPos_Co{i}.container = Z{i}.zipper

  structure ZZDepth_Co{i} : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} ZDepth.Z{i}.ZD.content
  sharing type ZZDepth_Co{i}.container = Z{i}.zipper\<close>\<close>
end

functor Zippy_Positions_Mixin(
    structure Z : ZIPPY_POSITIONS_MIXIN_BASE
    structure Exn : ZIPPY_EXCEPTION_MIXIN
    sharing type Exn.M.t = Z.M.t
  ) : ZIPPY_POSITIONS_MIXIN =
struct

open Z
structure MU = Zippy_Monad_Util(Z.M); open MU
structure Path_Util = \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Path_Util"\<close>(Z); open Path_Util

local open Mo
in
\<^imap>\<open>\<open>{i}\<close> => \<open>
fun path_from_zipper{i} z = SZGPos.SZ{i}.Zipper.getter z |> path_from_root_rev{i}
fun move_zipper{i} z_to = path_from_zipper{i} z_to |> move_path{i}\<close>\<close>
end

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure ZZGPos_Co{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Z{i}.ZD.Co
  structure L2 = SZGPos.SZ{i}.Content)

structure ZZLPos_Co{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Z{i}.ZD.Co
  structure L2 = SZLPos.SZ{i}.Content)

structure ZZDepth_Co{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Z{i}.ZD.Co
  structure L2 = SZDepth.SZ{i}.Content)\<close>\<close>

end
