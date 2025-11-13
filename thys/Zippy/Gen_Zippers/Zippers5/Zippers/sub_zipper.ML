(*  Title:      Zippy/sub_zipper.ML
    Author:     Kevin Kappelmann

Structures with lenses to zippers.
*)
signature \<^eval>\<open>sfx_T_nargs "SUB_DEP_ZIPPER"\<close> =
sig
  structure ZSub : \<^eval>\<open>sfx_T_nargs "DEP_ZIPPER"\<close>

  structure Zipper : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type Zipper.data = ZSub.zipper

  structure Container : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type Container.data = ZSub.ZM.container

  structure Content : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type Content.data = ZSub.ZD.content

  structure ZCtxt : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type ZCtxt.data = ZSub.ZD.zcontext
end

signature \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close> =
sig
  structure ZSub : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>

  structure Zipper : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type Zipper.data = ZSub.zipper

  structure Container : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type Container.data = ZSub.ZM.container

  structure Content : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type Content.data = ZSub.ZD.content

  structure ZCtxt : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type ZCtxt.data = ZSub.ZD.zcontext
end

functor \<^eval>\<open>sfx_T_nargs "Sub_Dep_Zipper_Sub_Zipper"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close>
    type @{AllT_args} dep_zip
    type @{AllT_args} dep_unzip
    type @{AllT_args} dep_up
    type @{AllT_args} dep_down
    type @{AllT_args} dep_left
    type @{AllT_args} dep_right
  ) :
    \<^eval>\<open>sfx_T_nargs "SUB_DEP_ZIPPER"\<close>
    where type @{AllT_args} ZSub.ZM.Zip.dep = @{AllT_args} dep_zip
    where type @{AllT_args} ZSub.ZM.Unzip.dep = @{AllT_args} dep_unzip
    where type @{AllT_args} ZSub.ZM.Up.dep = @{AllT_args} dep_up
    where type @{AllT_args} ZSub.ZM.Down.dep = @{AllT_args} dep_down
    where type @{AllT_args} ZSub.ZM.Left.dep = @{AllT_args} dep_left
    where type @{AllT_args} ZSub.ZM.Right.dep = @{AllT_args} dep_right =
struct
open Z
structure ZSub = \<^eval>\<open>sfx_T_nargs "Dep_Zipper_Zipper"\<close>(
  structure Z = ZSub
  type @{AllT_args} dep_zip = @{AllT_args} dep_zip
  type @{AllT_args} dep_unzip = @{AllT_args} dep_unzip
  type @{AllT_args} dep_up = @{AllT_args} dep_up
  type @{AllT_args} dep_down = @{AllT_args} dep_down
  type @{AllT_args} dep_left = @{AllT_args} dep_left
  type @{AllT_args} dep_right = @{AllT_args} dep_right)
end

functor \<^eval>\<open>sfx_T_nargs "Sub_Zipper_Sub_Dep_Zipper"\<close>(
    Z : \<^eval>\<open>sfx_T_nargs "SUB_DEP_ZIPPER"\<close>
    where type @{AllT_args} ZSub.ZM.Zip.dep = unit
    where type @{AllT_args} ZSub.ZM.Unzip.dep = unit
    where type @{AllT_args} ZSub.ZM.Up.dep = unit
    where type @{AllT_args} ZSub.ZM.Down.dep = unit
    where type @{AllT_args} ZSub.ZM.Left.dep = unit
    where type @{AllT_args} ZSub.ZM.Right.dep = unit
  ) : \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close> =
struct
open Z
structure ZSub = \<^eval>\<open>sfx_T_nargs "Zipper_Dep_Zipper"\<close>(ZSub)
end

functor \<^eval>\<open>sfx_T_nargs "Sub_Zipper_Trans"\<close>(
    structure SZ1 : \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close>
    structure SZ2 : \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close>
    sharing type SZ2.Zipper.container = SZ1.ZSub.zipper
    sharing type SZ2.Container.container = SZ1.ZSub.ZM.container
    sharing type SZ2.Content.container = SZ1.ZSub.ZD.content
    sharing type SZ2.ZCtxt.container = SZ1.ZSub.ZD.zcontext
    sharing type SZ2.ZSub.M.t = SZ1.ZSub.M.t
  ) :
    \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close>
    where type @{AllT_args} Zipper.container = @{AllT_args} SZ1.Zipper.container
    where type @{AllT_args} Container.container = @{AllT_args} SZ1.Container.container
    where type @{AllT_args} Content.container = @{AllT_args} SZ1.Content.container
    where type @{AllT_args} ZCtxt.container = @{AllT_args} SZ1.ZCtxt.container
    where type @{AllT_args} ZSub.zipper = @{AllT_args} SZ2.ZSub.zipper
    where type @{AllT_args} ZSub.ZM.container = @{AllT_args} SZ2.ZSub.ZM.container
    where type @{AllT_args} ZSub.ZD.content = @{AllT_args} SZ2.ZSub.ZD.content
    where type @{AllT_args} ZSub.ZD.zcontext = @{AllT_args} SZ2.ZSub.ZD.zcontext
    where type (@{ParaT_args} 'a) ZSub.M.t = (@{ParaT_args} 'a) SZ1.ZSub.M.t =
struct
structure ZSub = SZ2.ZSub
structure Zipper = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = SZ1.Zipper; structure L2 = SZ2.Zipper)
structure Container = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = SZ1.Container; structure L2 = SZ2.Container)
structure Content = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = SZ1.Content; structure L2 = SZ2.Content)
structure ZCtxt = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = SZ1.ZCtxt; structure L2 = SZ2.ZCtxt)
end
