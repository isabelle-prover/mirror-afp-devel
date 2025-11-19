(*  Title:      Zippy/pair_zipper_morphs.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER_MORPHS_DEP_ZIPPER_MORPHS"\<close> =
sig
  structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
  structure Z2 : \<^eval>\<open>sfx_T_nargs "DEP_ZIPPER_MORPHS"\<close>
  where type @{AllT_args} Zip.dep = @{AllT_args} Z1.Zip.from * @{AllT_args} Z1.Zip.to
  where type @{AllT_args} Unzip.dep = @{AllT_args} Z1.Unzip.from * @{AllT_args} Z1.Unzip.to
  where type @{AllT_args} Up.dep = @{AllT_args} Z1.Up.from * @{AllT_args} Z1.Up.to
  where type @{AllT_args} Down.dep = @{AllT_args} Z1.Down.from * @{AllT_args} Z1.Down.to
  where type @{AllT_args} Left.dep = @{AllT_args} Z1.Left.from * @{AllT_args} Z1.Left.to
  where type @{AllT_args} Right.dep = @{AllT_args} Z1.Right.from * @{AllT_args} Z1.Right.to
  sharing type Z2.M.t = Z1.M.t

  include \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
  where type @{AllT_args} container = @{AllT_args} Z1.container * @{AllT_args} Z2.container
  where type @{AllT_args} zipper = @{AllT_args} Z1.zipper * @{AllT_args} Z2.zipper
  sharing type M.t = Z1.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Morphs_Dep_Zipper_Morphs"\<close>(
    structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
    structure Z2 : \<^eval>\<open>sfx_T_nargs "DEP_ZIPPER_MORPHS"\<close>
    where type @{AllT_args} Zip.dep = @{AllT_args} Z1.Zip.from * @{AllT_args} Z1.Zip.to
    where type @{AllT_args} Unzip.dep = @{AllT_args} Z1.Unzip.from * @{AllT_args} Z1.Unzip.to
    where type @{AllT_args} Up.dep = @{AllT_args} Z1.Up.from * @{AllT_args} Z1.Up.to
    where type @{AllT_args} Down.dep = @{AllT_args} Z1.Down.from * @{AllT_args} Z1.Down.to
    where type @{AllT_args} Left.dep = @{AllT_args} Z1.Left.from * @{AllT_args} Z1.Left.to
    where type @{AllT_args} Right.dep = @{AllT_args} Z1.Right.from * @{AllT_args} Z1.Right.to
    sharing type Z2.M.t = Z1.M.t
  ) : \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER_MORPHS_DEP_ZIPPER_MORPHS"\<close> =
struct

structure Z1 = Z1
structure Z2 = Z2

type @{AllT_args} container = @{AllT_args} Z1.container * @{AllT_args} Z2.container
type @{AllT_args} zipper = @{AllT_args} Z1.zipper * @{AllT_args} Z2.zipper

structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close> = Z1
open M

structure Zip = \<^eval>\<open>sfx_T_nargs "Pair_Morph_Dep_Morph"\<close>(
  structure M1 = Z1.Zip; structure M2 = Z2.Zip)
structure Unzip = \<^eval>\<open>sfx_T_nargs "Pair_Morph_Dep_Morph"\<close>(
  structure M1 = Z1.Unzip; structure M2 = Z2.Unzip)
structure Up = \<^eval>\<open>sfx_T_nargs "Pair_Morph_Dep_Morph"\<close>(
  structure M1 = Z1.Up; structure M2 = Z2.Up)
structure Down = \<^eval>\<open>sfx_T_nargs "Pair_Morph_Dep_Morph"\<close>(
  structure M1 = Z1.Down; structure M2 = Z2.Down)
structure Left = \<^eval>\<open>sfx_T_nargs "Pair_Morph_Dep_Morph"\<close>(
  structure M1 = Z1.Left; structure M2 = Z2.Left)
structure Right = \<^eval>\<open>sfx_T_nargs "Pair_Morph_Dep_Morph"\<close>(
  structure M1 = Z1.Right; structure M2 = Z2.Right)
end

signature \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER_MORPHS"\<close> =
sig
  structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
  structure Z2 : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
  sharing type Z2.M.t = Z1.M.t

  include \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
  where type @{AllT_args} container = @{AllT_args} Z1.container * @{AllT_args} Z2.container
  where type @{AllT_args} zipper = @{AllT_args} Z1.zipper * @{AllT_args} Z2.zipper
  sharing type M.t = Z1.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Morphs"\<close>(
    structure Z1 : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
    structure Z2 : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
    sharing type Z2.M.t = Z1.M.t
  ) : \<^eval>\<open>sfx_T_nargs "PAIR_ZIPPER_MORPHS"\<close> =
struct
structure Z2In = Z2
structure PZ = \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Morphs_Dep_Zipper_Morphs"\<close>(
  structure Z1 = Z1
  structure Z2 = \<^eval>\<open>sfx_T_nargs "Dep_Zipper_Morphs_Zipper_Morphs"\<close>(
    structure Z = Z2
    type @{AllT_args} dep_zip = @{AllT_args} Z1.Zip.from * @{AllT_args} Z1.Zip.to
    type @{AllT_args} dep_unzip = @{AllT_args} Z1.Unzip.from * @{AllT_args} Z1.Unzip.to
    type @{AllT_args} dep_up = @{AllT_args} Z1.Up.from * @{AllT_args} Z1.Up.to
    type @{AllT_args} dep_down = @{AllT_args} Z1.Down.from * @{AllT_args} Z1.Down.to
    type @{AllT_args} dep_left = @{AllT_args} Z1.Left.from * @{AllT_args} Z1.Left.to
    type @{AllT_args} dep_right = @{AllT_args} Z1.Right.from * @{AllT_args} Z1.Right.to))
open PZ
structure Z2 = Z2In
end