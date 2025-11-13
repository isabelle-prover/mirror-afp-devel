(*  Title:      Zippy/zippy_lists_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_BASE =
sig
  structure ZN_AZ1 : \<^eval>\<open>sfx_T_nargs "SINGLE_CONTENT_ZIPPER"\<close>
  sharing type ZN_AZ1.container = ZN_AZ1.content

  structure ZN_AZ2 : \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
  where type 'a L.t = 'a list
  sharing type ZN_AZ2.M.t = ZN_AZ1.M.t

  structure ZN_AZ3 : \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
  where type 'a L.t = 'a list
  sharing type ZN_AZ3.M.t = ZN_AZ1.M.t
  sharing type ZN_AZ3.L.M.exn = ZN_AZ2.L.M.exn

  structure ZN_AZ4 : \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
  where type 'a L.t = 'a list
  sharing type ZN_AZ4.M.t = ZN_AZ1.M.t
  sharing type ZN_AZ4.L.M.exn = ZN_AZ2.L.M.exn

  structure ZN_AZ5 : \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
  where type 'a L.t = 'a list
  sharing type ZN_AZ5.M.t = ZN_AZ1.M.t
  sharing type ZN_AZ5.L.M.exn = ZN_AZ2.L.M.exn

  include ZIPPY_NODE_BASE
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} ZN.A.Z{i}.ZM.container = @{AllT_args} ZN_AZ{i}.ZM.container
  where type @{AllT_args} ZN.A.Z{i}.ZD.content = @{AllT_args} ZN_AZ{i}.ZD.content
  where type @{AllT_args} ZN.A.Z{i}.ZD.zcontext = @{AllT_args} ZN_AZ{i}.ZD.zcontext\<close>\<close>
  sharing type M.t = ZN_AZ1.M.t
end

functor Zippy_Lists_Base(
    Exn : ZIPPY_EXCEPTION_MIXIN
    where type @{ParaT_args encl: "(" ")"} ME.exn = unit
  ) :
    ZIPPY_LISTS_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>where type @{AllT_args} ZN.N{i}.content = @{ZipperT_arg \<open>{i} - 1\<close>}\<close>\<close>
  =
struct

structure M = Exn.ME
structure MU = Zippy_Monad_Util(M); open MU

structure ZN_AZ1 = \<^eval>\<open>sfx_T_nargs "Single_Content_Zipper"\<close>(
  structure AE = Exn.AE
  type @{AllT_args} container = @{ZipperT_arg 0}
  type @{AllT_args} content = @{ZipperT_arg 0}
  val zip = M.pure
  val unzip = M.pure)

structure LZ = \<^eval>\<open>sfx_T_nargs "List_Zipper"\<close>(
  structure L = \<^eval>\<open>sfx_ParaT_nargs "GList"\<close>(M)
  type @{AllT_args} content = @{ZipperT_arg 0}
  fun mk_exn_horizontal x = A.K () x)
structure ZN_AZ2 = LZ
structure ZN_AZ3 = LZ
structure ZN_AZ4 = LZ
structure ZN_AZ5 = LZ

structure ZN = \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes"\<close>(
  \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes_Base_Args_Simple_Zippers"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>structure Z{i} = ZN_AZ{i}\<close>\<close>))
structure ZB = Zippy_Base_Base(\<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Util"\<close>(
  structure Z = ZN
  structure AE = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception_Repeat"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception"\<close>(M))))
open ZB

structure SZN =
struct
  structure Z = ZN
  structure ZSub = Z
  structure Base = struct fun lens _ = \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".id"\<close> () end
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure SZ{i} =
  struct
    structure Z = Z{i}
    structure ZSub = Z
    structure Zipper = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
      open Base
      type @{AllT_args} container = @{AllT_args} Z.zipper
      type @{AllT_args} data = @{AllT_args} ZSub.zipper)
    structure Container = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
      open Base
      type @{AllT_args} container = @{AllT_args} Z.ZM.container
      type @{AllT_args} data = @{AllT_args} ZSub.ZM.container)
    structure Content = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
      open Base
      type @{AllT_args} container = @{AllT_args} Z.ZD.content
      type @{AllT_args} data = @{AllT_args} ZSub.ZD.content)
    structure ZCtxt = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
      open Base
      type @{AllT_args} container = @{AllT_args} Z.ZD.zcontext
      type @{AllT_args} data = @{AllT_args} ZSub.ZD.zcontext)
  end\<close>\<close>
end

(*instantiate the base zippers*)
structure ZN_AZ1 : \<^eval>\<open>sfx_T_nargs "SINGLE_CONTENT_ZIPPER"\<close>
  where type @{AllT_args} ZM.container = @{AllT_args} ZN.A.Z1.ZM.container
  where type @{AllT_args} ZD.content = @{AllT_args} ZN.A.Z1.ZD.content
= ZN_AZ1

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure ZN_AZ{i} : \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
  where type @{AllT_args} ZD.content = @{AllT_args} ZN.A.Z{i}.ZD.content
= struct open ZN_AZ{i} ZN.A.Z{i} end\<close>
start: 2\<close>

end
