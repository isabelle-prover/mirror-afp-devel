(*  Title:      Zippy/zipper_morphs.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "DEP_ZIPPER_MORPHS"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  type @{AllT_args} container
  type @{AllT_args} zipper

  structure Zip : \<^eval>\<open>sfx_T_nargs "DEP_MORPH"\<close>
  sharing type Zip.from = container
  sharing type Zip.to = zipper
  sharing type Zip.M.t = M.t
  structure Unzip : \<^eval>\<open>sfx_T_nargs "DEP_MORPH"\<close>
  sharing type Unzip.from = zipper
  sharing type Unzip.to = container
  sharing type Unzip.M.t = M.t

  structure Up : \<^eval>\<open>sfx_T_nargs "DEP_EMORPH"\<close>
  sharing type Up.from = zipper
  sharing type Up.M.t = M.t
  structure Down : \<^eval>\<open>sfx_T_nargs "DEP_EMORPH"\<close>
  sharing type Down.from = zipper
  sharing type Down.M.t = M.t
  structure Left : \<^eval>\<open>sfx_T_nargs "DEP_EMORPH"\<close>
  sharing type Left.from = zipper
  sharing type Left.M.t = M.t
  structure Right : \<^eval>\<open>sfx_T_nargs "DEP_EMORPH"\<close>
  sharing type Right.from = zipper
  sharing type Right.M.t = M.t
end

functor \<^eval>\<open>sfx_T_nargs "Dep_Zipper_Morphs"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
    type @{AllT_args} dep_zip
    type @{AllT_args} dep_unzip
    type @{AllT_args} dep_up
    type @{AllT_args} dep_down
    type @{AllT_args} dep_left
    type @{AllT_args} dep_right
    type @{AllT_args} container
    type @{AllT_args} zipper
    val zip : @{AllT_args} dep_zip ->
      (@{ParaT_args} @{AllT_args} container, @{AllT_args} zipper) M.morph
    val unzip : @{AllT_args} dep_unzip ->
      (@{ParaT_args} @{AllT_args} zipper, @{AllT_args} container) M.morph
    val up : @{AllT_args} dep_up ->
      (@{ParaT_args} @{AllT_args} zipper) M.emorph
    val down : @{AllT_args} dep_down ->
      (@{ParaT_args} @{AllT_args} zipper) M.emorph
    val left : @{AllT_args} dep_left ->
      (@{ParaT_args} @{AllT_args} zipper) M.emorph
    val right : @{AllT_args} dep_right ->
      (@{ParaT_args} @{AllT_args} zipper) M.emorph
  ) : \<^eval>\<open>sfx_T_nargs "DEP_ZIPPER_MORPHS"\<close> =
struct

structure Min = M
open M
type @{AllT_args} container = @{AllT_args} container
type @{AllT_args} zipper = @{AllT_args} zipper

structure Zip =
struct
  open Min
  type @{AllT_args} dep = @{AllT_args} dep_zip
  type @{AllT_args} from = @{AllT_args} container
  type @{AllT_args} to = @{AllT_args} zipper
  val morph = zip
end
structure Unzip =
struct
  open Min
  type @{AllT_args} dep = @{AllT_args} dep_unzip
  type @{AllT_args} from = @{AllT_args} zipper
  type @{AllT_args} to = @{AllT_args} container
  val morph = unzip
end

structure Base = struct
  structure M = Min
  type @{AllT_args} data = @{AllT_args} zipper
end
structure Up = \<^eval>\<open>sfx_T_nargs "Dep_EMorph"\<close>(open Base
  type @{AllT_args} dep = @{AllT_args} dep_up; val morph = up)
structure Down = \<^eval>\<open>sfx_T_nargs "Dep_EMorph"\<close>(open Base
  type @{AllT_args} dep = @{AllT_args} dep_down; val morph = down)
structure Left = \<^eval>\<open>sfx_T_nargs "Dep_EMorph"\<close>(open Base
  type @{AllT_args} dep = @{AllT_args} dep_left; val morph = left)
structure Right = \<^eval>\<open>sfx_T_nargs "Dep_EMorph"\<close>(open Base
  type @{AllT_args} dep = @{AllT_args} dep_right; val morph = right)
end

signature \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  type @{AllT_args} container
  type @{AllT_args} zipper

  structure Zip : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  sharing type Zip.from = container
  sharing type Zip.to = zipper
  sharing type Zip.M.t = M.t
  structure Unzip : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  sharing type Unzip.from = zipper
  sharing type Unzip.to = container
  sharing type Unzip.M.t = M.t

  structure Up : \<^eval>\<open>sfx_T_nargs "EMORPH"\<close>
  sharing type Up.from = zipper
  sharing type Up.M.t = M.t
  structure Down : \<^eval>\<open>sfx_T_nargs "EMORPH"\<close>
  sharing type Down.from = zipper
  sharing type Down.M.t = M.t
  structure Left : \<^eval>\<open>sfx_T_nargs "EMORPH"\<close>
  sharing type Left.from = zipper
  sharing type Left.M.t = M.t
  structure Right : \<^eval>\<open>sfx_T_nargs "EMORPH"\<close>
  sharing type Right.from = zipper
  sharing type Right.M.t = M.t
end

functor \<^eval>\<open>sfx_T_nargs "Dep_Zipper_Morphs_Zipper_Morphs"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
    type @{AllT_args} dep_zip
    type @{AllT_args} dep_unzip
    type @{AllT_args} dep_up
    type @{AllT_args} dep_down
    type @{AllT_args} dep_left
    type @{AllT_args} dep_right
  ) :
    \<^eval>\<open>sfx_T_nargs "DEP_ZIPPER_MORPHS"\<close>
    where type @{AllT_args} Zip.dep = @{AllT_args} dep_zip
    where type @{AllT_args} Unzip.dep = @{AllT_args} dep_unzip
    where type @{AllT_args} Up.dep = @{AllT_args} dep_up
    where type @{AllT_args} Down.dep = @{AllT_args} dep_down
    where type @{AllT_args} Left.dep = @{AllT_args} dep_left
    where type @{AllT_args} Right.dep = @{AllT_args} dep_right =
struct
open Z
structure Zip = \<^eval>\<open>sfx_T_nargs "Dep_Morph_Morph"\<close>(
  structure M = Zip; type @{AllT_args} dep = @{AllT_args} dep_zip)
structure Unzip = \<^eval>\<open>sfx_T_nargs "Dep_Morph_Morph"\<close>(
  structure M = Unzip; type @{AllT_args} dep = @{AllT_args} dep_unzip)
structure Up = \<^eval>\<open>sfx_T_nargs "Dep_Morph_Morph"\<close>(
  structure M = Up; type @{AllT_args} dep = @{AllT_args} dep_up)
structure Down = \<^eval>\<open>sfx_T_nargs "Dep_Morph_Morph"\<close>(
  structure M = Down; type @{AllT_args} dep = @{AllT_args} dep_down)
structure Left = \<^eval>\<open>sfx_T_nargs "Dep_Morph_Morph"\<close>(
  structure M = Left; type @{AllT_args} dep = @{AllT_args} dep_left)
structure Right = \<^eval>\<open>sfx_T_nargs "Dep_Morph_Morph"\<close>(
  structure M = Right; type @{AllT_args} dep = @{AllT_args} dep_right)
end

functor \<^eval>\<open>sfx_T_nargs "Zipper_Morphs_Dep_Zipper_Morphs"\<close>(
    Z : \<^eval>\<open>sfx_T_nargs "DEP_ZIPPER_MORPHS"\<close>
    where type @{AllT_args} Zip.dep = unit
    where type @{AllT_args} Unzip.dep = unit
    where type @{AllT_args} Up.dep = unit
    where type @{AllT_args} Down.dep = unit
    where type @{AllT_args} Left.dep = unit
    where type @{AllT_args} Right.dep = unit
  ) : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close> =
struct
open Z
structure Zip = \<^eval>\<open>sfx_T_nargs "Morph_Dep_Morph"\<close>(Zip)
structure Unzip = \<^eval>\<open>sfx_T_nargs "Morph_Dep_Morph"\<close>(Unzip)
structure Up = \<^eval>\<open>sfx_T_nargs "Morph_Dep_Morph"\<close>(Up)
structure Down = \<^eval>\<open>sfx_T_nargs "Morph_Dep_Morph"\<close>(Down)
structure Left = \<^eval>\<open>sfx_T_nargs "Morph_Dep_Morph"\<close>(Left)
structure Right = \<^eval>\<open>sfx_T_nargs "Morph_Dep_Morph"\<close>(Right)
end

functor \<^eval>\<open>sfx_T_nargs "Zipper_Morphs"\<close>(A :
  sig
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
    type @{AllT_args} container
    type @{AllT_args} zipper
    val zip : (@{ParaT_args} @{AllT_args} container, @{AllT_args} zipper) M.morph
    val unzip : (@{ParaT_args} @{AllT_args} zipper, @{AllT_args} container) M.morph
    val up : (@{ParaT_args} @{AllT_args} zipper) M.emorph
    val down : (@{ParaT_args} @{AllT_args} zipper) M.emorph
    val left : (@{ParaT_args} @{AllT_args} zipper) M.emorph
    val right : (@{ParaT_args} @{AllT_args} zipper) M.emorph
  end) : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close> =
\<^eval>\<open>sfx_T_nargs "Zipper_Morphs_Dep_Zipper_Morphs"\<close>(\<^eval>\<open>sfx_T_nargs "Dep_Zipper_Morphs"\<close>(
  open A
  type @{AllT_args} dep_zip = unit
  type @{AllT_args} dep_unzip = unit
  type @{AllT_args} dep_up = unit
  type @{AllT_args} dep_down = unit
  type @{AllT_args} dep_left = unit
  type @{AllT_args} dep_right = unit
  fun zip _ = A.zip
  fun unzip _ = A.unzip
  fun up _ = A.up
  fun down _ = A.down
  fun left _ = A.left
  fun right _ = A.right))
