(*  Title:      Zippy/zippy_node_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_NODE_BASE =
sig
  include ZIPPY_BASE_BASE
  (*zipper containing the core data*)
  structure ZN : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES"\<close>
  sharing type ZN.M.t = M.t

  structure SZN : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} ZSub.Z{i}.ZM.container = @{AllT_args} ZN.Z{i}.ZM.container
  where type @{AllT_args} ZSub.Z{i}.zipper = @{AllT_args} ZN.Z{i}.zipper
  where type @{AllT_args} ZSub.Z{i}.ZD.content = @{AllT_args} ZN.Z{i}.ZD.content
  where type @{AllT_args} ZSub.Z{i}.ZD.zcontext = @{AllT_args} ZN.Z{i}.ZD.zcontext\<close>\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  sharing type SZN.SZ{i}.Container.container = Z{i}.ZM.container
  sharing type SZN.SZ{i}.Zipper.container = Z{i}.zipper
  sharing type SZN.SZ{i}.Content.container = Z{i}.ZD.content
  sharing type SZN.SZ{i}.ZCtxt.container = Z{i}.ZD.zcontext\<close>\<close>
  sharing type SZN.ZSub.M.t = M.t
end
