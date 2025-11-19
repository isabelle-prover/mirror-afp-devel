(*  Title:      Zippy/zippy_node_collect_trace_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_NODE_COLLECT_TRACE_MIXIN_BASE =
sig
  include ZIPPY_NODE_BASE

  structure ZCollect : ZIPPY_COLLECT_TRACE_MIXIN_BASE
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  sharing type ZCollect.Z{i}.zipper = Z{i}.zipper
  sharing type ZCollect.Z{i}.ZM.container = Z{i}.ZM.container
  sharing type ZCollect.Z{i}.ZD.content = Z{i}.ZD.content
  sharing type ZCollect.Z{i}.ZD.zcontext = Z{i}.ZD.zcontext\<close>\<close>
  sharing type ZCollect.M.t = M.t
end

\<^imap>\<open>\<open>{j}\<close> => \<open>
functor Zippy_Node_Collect_Trace_Mixin_Base{j}(A :
  sig
    structure Z : ZIPPY_NODE_BASE
    type @{AllT_args} data
    val update : @{AllT_args} Z.Z{j}.zipper -> (@{AllT_args} data * @{AllT_args} data list) option ->
      @{AllT_args} data
    structure Exn : ZIPPY_EXCEPTION_MIXIN
    sharing type Exn.M.t = Z.M.t
  end) :
  sig
    include ZIPPY_NODE_COLLECT_TRACE_MIXIN_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.ZM.container = @{AllT_args} A.Z.Z{i}.ZM.container *
      (@{AllT_args} A.data * @{AllT_args} A.data list) option
    where type @{AllT_args} Z{i}.zipper = @{AllT_args} A.Z.Z{i}.zipper *
      (@{AllT_args} A.data * @{AllT_args} A.data list) option
    where type @{AllT_args} Z{i}.ZD.content = @{AllT_args} A.Z.Z{i}.ZD.content *
      (@{AllT_args} A.data * @{AllT_args} A.data list) option
    where type @{AllT_args} Z{i}.ZD.zcontext = @{AllT_args} A.Z.Z{i}.ZD.zcontext * unit\<close>\<close>
    structure SZ : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZSub.Z{i}.ZM.container = @{AllT_args} A.Z.Z{i}.ZM.container
    where type @{AllT_args} ZSub.Z{i}.zipper = @{AllT_args} A.Z.Z{i}.zipper
    where type @{AllT_args} ZSub.Z{i}.ZD.content = @{AllT_args} A.Z.Z{i}.ZD.content
    where type @{AllT_args} ZSub.Z{i}.ZD.zcontext = @{AllT_args} A.Z.Z{i}.ZD.zcontext
    where type @{AllT_args} SZ{i}.Container.container = @{AllT_args} Z{i}.ZM.container
    where type @{AllT_args} SZ{i}.Zipper.container = @{AllT_args} Z{i}.zipper
    where type @{AllT_args} SZ{i}.Content.container = @{AllT_args} Z{i}.ZD.content
    where type @{AllT_args} SZ{i}.ZCtxt.container = @{AllT_args} Z{i}.ZD.zcontext\<close>\<close>
    sharing type SZ.ZSub.M.t = M.t
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    val container{i} : @{AllT_args} ZCollect.trace -> @{AllT_args} A.Z.Z{i}.ZM.container ->
      @{AllT_args} Z{i}.ZM.container
    val init_container{i} : @{AllT_args} A.Z.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container\<close>\<close>
  end
  =
struct
open A; open Z
structure ZCollect = Zippy_Collect_Trace_Mixin_Base{j}(A)
open ZCollect
structure SZN = \<^eval>\<open>pfx_sfx_nargs "Sub_Alternating_Zipper_Trans"\<close>(
  structure ASZ1 = SZ; structure ASZ2 = Z.SZN)
end\<close>\<close>
