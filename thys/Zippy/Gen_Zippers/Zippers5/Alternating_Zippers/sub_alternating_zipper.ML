(*  Title:      Zippy/sub_alternating_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_DEP_ZIPPER"\<close> =
sig
  structure ZSub : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_DEP_ZIPPER"\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure SZ{i} : \<^eval>\<open>sfx_T_nargs "SUB_DEP_ZIPPER"\<close>
  sharing type SZ{i}.ZSub.zipper = ZSub.Z{i}.zipper
  sharing type SZ{i}.ZSub.ZM.container = ZSub.Z{i}.ZM.container
  sharing type SZ{i}.ZSub.ZM.Zip.dep = ZSub.Z{i}.ZM.Zip.dep
  sharing type SZ{i}.ZSub.ZM.Unzip.dep = ZSub.Z{i}.ZM.Unzip.dep
  sharing type SZ{i}.ZSub.ZM.Up.dep = ZSub.Z{i}.ZM.Up.dep
  sharing type SZ{i}.ZSub.ZM.Down.dep = ZSub.Z{i}.ZM.Down.dep
  sharing type SZ{i}.ZSub.ZM.Left.dep = ZSub.Z{i}.ZM.Left.dep
  sharing type SZ{i}.ZSub.ZM.Right.dep = ZSub.Z{i}.ZM.Right.dep
  sharing type SZ{i}.ZSub.ZD.content = ZSub.Z{i}.ZD.content
  sharing type SZ{i}.ZSub.ZD.zcontext = ZSub.Z{i}.ZD.zcontext
  sharing type SZ{i}.ZSub.M.t = ZSub.M.t\<close>\<close>
end

signature \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close> =
sig
  structure ZSub : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure SZ{i} : \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close>
  sharing type SZ{i}.ZSub.zipper = ZSub.Z{i}.zipper
  sharing type SZ{i}.ZSub.ZM.container = ZSub.Z{i}.ZM.container
  sharing type SZ{i}.ZSub.ZD.content = ZSub.Z{i}.ZD.content
  sharing type SZ{i}.ZSub.ZD.zcontext = ZSub.Z{i}.ZD.zcontext
  sharing type SZ{i}.ZSub.M.t = ZSub.M.t\<close>\<close>
end

functor \<^eval>\<open>pfx_sfx_nargs "Sub_Alternating_Dep_Zipper_Sub_Alternating_Zipper"\<close>(
    structure Z : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{AllT_args} dep{i}_zip
    type @{AllT_args} dep{i}_unzip
    type @{AllT_args} dep{i}_up
    type @{AllT_args} dep{i}_down
    type @{AllT_args} dep{i}_left
    type @{AllT_args} dep{i}_right
    type @{AllT_args} dep_down{i}
    type @{AllT_args} dep_up{i}\<close>\<close>
  ) :
    \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_DEP_ZIPPER"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZSub.Z{i}.ZM.Zip.dep = @{AllT_args} dep{i}_zip
    where type @{AllT_args} ZSub.Z{i}.ZM.Unzip.dep = @{AllT_args} dep{i}_unzip
    where type @{AllT_args} ZSub.Z{i}.ZM.Up.dep = @{AllT_args} dep{i}_up
    where type @{AllT_args} ZSub.Z{i}.ZM.Down.dep = @{AllT_args} dep{i}_down
    where type @{AllT_args} ZSub.Z{i}.ZM.Left.dep = @{AllT_args} dep{i}_left
    where type @{AllT_args} ZSub.Z{i}.ZM.Right.dep = @{AllT_args} dep{i}_right
    where type @{AllT_args} ZSub.Down{i}.dep = @{AllT_args} dep_down{i}
    where type @{AllT_args} ZSub.Up{i}.dep = @{AllT_args} dep_up{i}\<close>\<close> =
struct
open Z
structure ZSub = \<^eval>\<open>pfx_sfx_nargs "Alternating_Dep_Zipper_Alternating_Zipper"\<close>(
  structure Z = ZSub
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  type @{AllT_args} dep{i}_zip = @{AllT_args} dep{i}_zip
  type @{AllT_args} dep{i}_unzip = @{AllT_args} dep{i}_unzip
  type @{AllT_args} dep{i}_up = @{AllT_args} dep{i}_up
  type @{AllT_args} dep{i}_down = @{AllT_args} dep{i}_down
  type @{AllT_args} dep{i}_left = @{AllT_args} dep{i}_left
  type @{AllT_args} dep{i}_right = @{AllT_args} dep{i}_right
  type @{AllT_args} dep_down{i} = @{AllT_args} dep_down{i}
  type @{AllT_args} dep_up{i} = @{AllT_args} dep_up{i}\<close>\<close>)

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure SZ{i} = \<^eval>\<open>sfx_T_nargs "Sub_Dep_Zipper_Sub_Zipper"\<close>(
  structure Z = SZ{i}
  type @{AllT_args} dep_zip = @{AllT_args} dep{i}_zip
  type @{AllT_args} dep_unzip = @{AllT_args} dep{i}_unzip
  type @{AllT_args} dep_up = @{AllT_args} dep{i}_up
  type @{AllT_args} dep_down = @{AllT_args} dep{i}_down
  type @{AllT_args} dep_left = @{AllT_args} dep{i}_left
  type @{AllT_args} dep_right = @{AllT_args} dep{i}_right)\<close>\<close>
end

functor \<^eval>\<open>pfx_sfx_nargs "Sub_Alternating_Zipper_Sub_Alternating_Dep_Zipper"\<close>(
    Z : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_DEP_ZIPPER"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZSub.Z{i}.ZM.Zip.dep = unit
    where type @{AllT_args} ZSub.Z{i}.ZM.Unzip.dep = unit
    where type @{AllT_args} ZSub.Z{i}.ZM.Up.dep = unit
    where type @{AllT_args} ZSub.Z{i}.ZM.Down.dep = unit
    where type @{AllT_args} ZSub.Z{i}.ZM.Left.dep = unit
    where type @{AllT_args} ZSub.Z{i}.ZM.Right.dep = unit
    where type @{AllT_args} ZSub.Down{i}.dep = unit
    where type @{AllT_args} ZSub.Up{i}.dep = unit\<close>\<close>
  ) : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close> =
struct
open Z
structure ZSub = \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Alternating_Dep_Zipper"\<close>(ZSub)
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure SZ{i} = \<^eval>\<open>sfx_T_nargs "Sub_Zipper_Sub_Dep_Zipper"\<close>(SZ{i})\<close>\<close>
end

functor \<^eval>\<open>pfx_sfx_nargs "Sub_Alternating_Zipper_Trans"\<close>(
    structure ASZ1 : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
    structure ASZ2 : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    sharing type ASZ2.SZ{i}.Zipper.container = ASZ1.ZSub.Z{i}.zipper
    sharing type ASZ2.SZ{i}.Container.container = ASZ1.ZSub.Z{i}.ZM.container
    sharing type ASZ2.SZ{i}.Content.container = ASZ1.ZSub.Z{i}.ZD.content
    sharing type ASZ2.SZ{i}.ZCtxt.container = ASZ1.ZSub.Z{i}.ZD.zcontext\<close>\<close>
    sharing type ASZ1.ZSub.M.t = ASZ2.ZSub.M.t
  ) :
    \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} SZ{i}.Zipper.container = @{AllT_args} ASZ1.SZ{i}.Zipper.container
    where type @{AllT_args} SZ{i}.Container.container = @{AllT_args} ASZ1.SZ{i}.Container.container
    where type @{AllT_args} SZ{i}.Content.container = @{AllT_args} ASZ1.SZ{i}.Content.container
    where type @{AllT_args} SZ{i}.ZCtxt.container = @{AllT_args} ASZ1.SZ{i}.ZCtxt.container
    where type @{AllT_args} ZSub.Z{i}.zipper = @{AllT_args} ASZ2.ZSub.Z{i}.zipper
    where type @{AllT_args} ZSub.Z{i}.ZM.container = @{AllT_args} ASZ2.ZSub.Z{i}.ZM.container
    where type @{AllT_args} ZSub.Z{i}.ZD.content = @{AllT_args} ASZ2.ZSub.Z{i}.ZD.content
    where type @{AllT_args} ZSub.Z{i}.ZD.zcontext = @{AllT_args} ASZ2.ZSub.Z{i}.ZD.zcontext\<close>\<close>
    where type (@{ParaT_args} 'a) ZSub.M.t = (@{ParaT_args} 'a) ASZ1.ZSub.M.t
=
struct
structure ZSub = ASZ2.ZSub
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure SZ{i} = \<^eval>\<open>sfx_T_nargs "Sub_Zipper_Trans"\<close>(
  structure SZ1 = ASZ1.SZ{i}
  structure SZ2 = ASZ2.SZ{i})\<close>\<close>
end