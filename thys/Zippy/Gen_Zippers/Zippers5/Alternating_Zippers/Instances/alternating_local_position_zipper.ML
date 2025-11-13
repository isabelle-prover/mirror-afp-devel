(*  Title:      Zippy/alternating_local_position_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_LOCAL_POSITION_ZIPPER"\<close> =
sig
  structure Z : \<^eval>\<open>sfx_T_nargs "POSITION_ZIPPER"\<close>
  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} A.N{i}.content = @{AllT_args} Z.ZD.content
  where type @{AllT_args} A.Z{i}.ZM.container = @{AllT_args} Z.ZM.container
  where type @{AllT_args} A.Z{i}.ZD.zcontext = @{AllT_args} Z.ZD.zcontext
  where type @{AllT_args} A.Z{i}.zipper = @{AllT_args} Z.zipper\<close>\<close>
  sharing type M.t = Z.M.t
end

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Local_Position_Zipper"\<close>(
    Z : \<^eval>\<open>sfx_T_nargs "POSITION_ZIPPER"\<close>
  ) : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_LOCAL_POSITION_ZIPPER"\<close> =
struct
structure Z = Z
structure AZN = \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes"\<close>(
  \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes_Base_Args_Zippers"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Z{i} = Z
    type @{AllT_args} ncontent{i} = @{AllT_args} Z{i}.ZD.content
    fun ncontent{i} x = x
    fun next{i} _ = Z.M.pure ()
    fun content{i} x _ = x
    \<close>\<close>))
open AZN
end
