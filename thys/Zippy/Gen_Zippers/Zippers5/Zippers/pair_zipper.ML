(*  Title:      Zippy/pair_zipper5.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER_DEP_ZIPPER"\<close> =
sig
  structure SZ1 : \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close>
  structure SZ2 : \<^eval>\<open>sfx_T_nargs "SUB_DEP_ZIPPER"\<close>
  where type @{AllT_args} ZSub.ZM.Zip.dep =
    @{AllT_args} SZ1.ZSub.ZM.Zip.from * @{AllT_args} SZ1.ZSub.ZM.Zip.to
  where type @{AllT_args} ZSub.ZM.Unzip.dep =
    @{AllT_args} SZ1.ZSub.ZM.Unzip.from * @{AllT_args} SZ1.ZSub.ZM.Unzip.to
  where type @{AllT_args} ZSub.ZM.Up.dep =
    @{AllT_args} SZ1.ZSub.ZM.Up.from * @{AllT_args} SZ1.ZSub.ZM.Up.to
  where type @{AllT_args} ZSub.ZM.Down.dep =
    @{AllT_args} SZ1.ZSub.ZM.Down.from * @{AllT_args} SZ1.ZSub.ZM.Down.to
  where type @{AllT_args} ZSub.ZM.Left.dep =
    @{AllT_args} SZ1.ZSub.ZM.Left.from * @{AllT_args} SZ1.ZSub.ZM.Left.to
  where type @{AllT_args} ZSub.ZM.Right.dep =
    @{AllT_args} SZ1.ZSub.ZM.Right.from * @{AllT_args} SZ1.ZSub.ZM.Right.to
  sharing type SZ2.Zipper.container = SZ1.Zipper.container
  sharing type SZ2.Container.container = SZ1.Container.container
  sharing type SZ2.Content.container = SZ1.Content.container
  sharing type SZ2.ZCtxt.container = SZ1.ZCtxt.container
  sharing type SZ2.ZSub.M.t = SZ1.ZSub.M.t

  include \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZD.zipper = @{AllT_args} SZ1.ZSub.zipper * @{AllT_args} SZ2.ZSub.zipper
  where type @{AllT_args} ZM.container =
    @{AllT_args} SZ1.ZSub.ZM.container * @{AllT_args} SZ2.ZSub.ZM.container
  where type @{AllT_args} ZD.content =
    @{AllT_args} SZ1.ZSub.ZD.content * @{AllT_args} SZ2.ZSub.ZD.content
  where type @{AllT_args} ZD.zcontext =
    @{AllT_args} SZ1.ZSub.ZD.zcontext * @{AllT_args} SZ2.ZSub.ZD.zcontext
  sharing type M.t = SZ1.ZSub.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Dep_Zipper"\<close>(
    structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    structure Z2 : \<^eval>\<open>sfx_T_nargs "DEP_ZIPPER"\<close>
    where type @{AllT_args} ZM.Zip.dep = @{AllT_args} Z1.ZM.Zip.from * @{AllT_args} Z1.ZM.Zip.to
    where type @{AllT_args} ZM.Unzip.dep = @{AllT_args} Z1.ZM.Unzip.from * @{AllT_args} Z1.ZM.Unzip.to
    where type @{AllT_args} ZM.Up.dep = @{AllT_args} Z1.ZM.Up.from * @{AllT_args} Z1.ZM.Up.to
    where type @{AllT_args} ZM.Down.dep = @{AllT_args} Z1.ZM.Down.from * @{AllT_args} Z1.ZM.Down.to
    where type @{AllT_args} ZM.Left.dep = @{AllT_args} Z1.ZM.Left.from * @{AllT_args} Z1.ZM.Left.to
    where type @{AllT_args} ZM.Right.dep = @{AllT_args} Z1.ZM.Right.from * @{AllT_args} Z1.ZM.Right.to
    sharing type Z2.M.t = Z1.M.t
  ) :
    \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER_DEP_ZIPPER"\<close>
    where type @{AllT_args} SZ1.Zipper.container = @{AllT_args} Z1.zipper * @{AllT_args} Z2.zipper
    where type @{AllT_args} SZ1.Container.container =
      @{AllT_args} Z1.ZM.container * @{AllT_args} Z2.ZM.container
    where type @{AllT_args} SZ1.Content.container =
      @{AllT_args} Z1.ZD.content * @{AllT_args} Z2.ZD.content
    where type @{AllT_args} SZ1.ZCtxt.container =
      @{AllT_args} Z1.ZD.zcontext * @{AllT_args} Z2.ZD.zcontext =
struct

structure Z = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure ZM = \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Morphs_Dep_Zipper_Morphs"\<close>(
    structure Z1 = Z1.ZM; structure Z2 = Z2.ZM)
  structure ZD = \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Data"\<close>(
    structure Z1 = Z1.ZD; structure Z2 = Z2.ZD))
open Z

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>
structure SZ1 =
struct
  structure ZSub = Z1
  structure Zipper = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
    type @{AllT_args} container = @{AllT_args} Z.zipper
    type @{AllT_args} data = @{AllT_args} ZSub.zipper
    fun lens _ = L.lens_fst (L.id ()))
  structure Container = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
    type @{AllT_args} container = @{AllT_args} Z.ZM.container
    type @{AllT_args} data = @{AllT_args} ZSub.ZM.container
    fun lens _ = L.lens_fst (L.id ()))
  structure Content = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
    type @{AllT_args} container = @{AllT_args} Z.ZD.content
    type @{AllT_args} data = @{AllT_args} ZSub.ZD.content
    fun lens _ = L.lens_fst (L.id ()))
  structure ZCtxt = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
    type @{AllT_args} container = @{AllT_args} Z.ZD.zcontext
    type @{AllT_args} data = @{AllT_args} ZSub.ZD.zcontext
    fun lens _ = L.lens_fst (L.id ()))
end
structure SZ2 =
struct
  structure ZSub = Z2
  structure Zipper = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
    type @{AllT_args} container = @{AllT_args} Z.zipper
    type @{AllT_args} data = @{AllT_args} ZSub.zipper
    fun lens _ = L.lens_snd (L.id ()))
  structure Container = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
    type @{AllT_args} container = @{AllT_args} Z.ZM.container
    type @{AllT_args} data = @{AllT_args} ZSub.ZM.container
    fun lens _ = L.lens_snd (L.id ()))
  structure Content = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
    type @{AllT_args} container = @{AllT_args} Z.ZD.content
    type @{AllT_args} data = @{AllT_args} ZSub.ZD.content
    fun lens _ = L.lens_snd (L.id ()))
  structure ZCtxt = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
    type @{AllT_args} container = @{AllT_args} Z.ZD.zcontext
    type @{AllT_args} data = @{AllT_args} ZSub.ZD.zcontext
    fun lens _ = L.lens_snd (L.id ()))
end
end

signature \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER"\<close> =
sig
  structure SZ1 : \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close>
  structure SZ2 : \<^eval>\<open>sfx_T_nargs "SUB_ZIPPER"\<close>
  sharing type SZ2.Zipper.container = SZ1.Zipper.container
  sharing type SZ2.Container.container = SZ1.Container.container
  sharing type SZ2.Content.container = SZ1.Content.container
  sharing type SZ2.ZCtxt.container = SZ1.ZCtxt.container
  sharing type SZ2.ZSub.M.t = SZ1.ZSub.M.t

  include \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZD.zipper = @{AllT_args} SZ1.ZSub.zipper * @{AllT_args} SZ2.ZSub.zipper
  where type @{AllT_args} ZM.container =
    @{AllT_args} SZ1.ZSub.ZM.container * @{AllT_args} SZ2.ZSub.ZM.container
  where type @{AllT_args} ZD.content =
    @{AllT_args} SZ1.ZSub.ZD.content * @{AllT_args} SZ2.ZSub.ZD.content
  where type @{AllT_args} ZD.zcontext =
    @{AllT_args} SZ1.ZSub.ZD.zcontext * @{AllT_args} SZ2.ZSub.ZD.zcontext
  sharing type M.t = SZ1.ZSub.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Pair_Zipper"\<close>(
    structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    structure Z2 : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    sharing type Z2.M.t = Z1.M.t
  ) :
    \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER"\<close>
    where type @{AllT_args} SZ1.Zipper.container = @{AllT_args} Z1.zipper * @{AllT_args} Z2.zipper
    where type @{AllT_args} SZ1.Container.container =
      @{AllT_args} Z1.ZM.container * @{AllT_args} Z2.ZM.container
    where type @{AllT_args} SZ1.Content.container =
      @{AllT_args} Z1.ZD.content * @{AllT_args} Z2.ZD.content
    where type @{AllT_args} SZ1.ZCtxt.container =
      @{AllT_args} Z1.ZD.zcontext * @{AllT_args} Z2.ZD.zcontext =
struct
structure PZ = \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Dep_Zipper"\<close>(
  structure Z1 = Z1
  structure Z2 = \<^eval>\<open>sfx_T_nargs "Dep_Zipper_Zipper"\<close>(
    structure Z = Z2
    type @{AllT_args} dep_zip = @{AllT_args} Z1.ZM.Zip.from * @{AllT_args} Z1.ZM.Zip.to
    type @{AllT_args} dep_unzip = @{AllT_args} Z1.ZM.Unzip.from * @{AllT_args} Z1.ZM.Unzip.to
    type @{AllT_args} dep_up = @{AllT_args} Z1.ZM.Up.from * @{AllT_args} Z1.ZM.Up.to
    type @{AllT_args} dep_down = @{AllT_args} Z1.ZM.Down.from * @{AllT_args} Z1.ZM.Down.to
    type @{AllT_args} dep_left = @{AllT_args} Z1.ZM.Left.from * @{AllT_args} Z1.ZM.Left.to
    type @{AllT_args} dep_right = @{AllT_args} Z1.ZM.Right.from * @{AllT_args} Z1.ZM.Right.to))
open PZ
structure SZ2 = struct open SZ2; structure ZSub = Z2 end
end