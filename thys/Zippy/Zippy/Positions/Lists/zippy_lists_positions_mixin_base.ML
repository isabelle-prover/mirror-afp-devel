(*  Title:      Zippy/zippy_lists_positions_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_POSITIONS_MIXIN_BASE =
sig
  include ZIPPY_LISTS_BASE

  structure ZP : ZIPPY_POSITIONS_MIXIN_BASE
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  sharing type ZP.Z{i}.ZM.container = Z{i}.ZM.container
  sharing type ZP.Z{i}.ZD.content = Z{i}.ZD.content
  sharing type ZP.Z{i}.ZD.zcontext = Z{i}.ZD.zcontext
  sharing type ZP.Z{i}.zipper = Z{i}.zipper\<close>\<close>
  sharing type ZP.M.t = M.t
end

functor Zippy_Lists_Positions_Mixin_Base(
    structure Z : ZIPPY_LISTS_BASE
    structure Exn : ZIPPY_EXCEPTION_MIXIN
    where type @{ParaT_args encl: "(" ")"} ME.exn = unit
    sharing type Exn.M.t = Z.M.t
  ) :
  sig
    include ZIPPY_LISTS_POSITIONS_MIXIN_BASE
    structure SZ : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZSub.Z{i}.ZM.container = @{AllT_args} Z.Z{i}.ZM.container
    where type @{AllT_args} ZSub.Z{i}.zipper = @{AllT_args} Z.Z{i}.zipper
    where type @{AllT_args} ZSub.Z{i}.ZD.content = @{AllT_args} Z.Z{i}.ZD.content
    where type @{AllT_args} ZSub.Z{i}.ZD.zcontext = @{AllT_args} Z.Z{i}.ZD.zcontext\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    sharing type SZ.SZ{i}.Container.container = Z{i}.ZM.container
    sharing type SZ.SZ{i}.Zipper.container = Z{i}.zipper
    sharing type SZ.SZ{i}.Content.container = Z{i}.ZD.content
    sharing type SZ.SZ{i}.ZCtxt.container = Z{i}.ZD.zcontext\<close>\<close>
    sharing type SZ.ZSub.M.t = M.t
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    val container{i} : @{AllT_args} ZP.ZGPos.Z{i}.ZM.container ->
      @{AllT_args} ZP.ZLPos.Z{i}.ZM.container -> @{AllT_args} ZP.ZDepth.Z{i}.ZM.container ->
      @{AllT_args} Z.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container
    val init_container{i} : @{AllT_args} Z.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container\<close>\<close>
  end
  =
struct
open Z
structure Z = Zippy_Node_Positions_Mixin_Base(structure Z = Z; structure Exn = Exn)
open Z
end
