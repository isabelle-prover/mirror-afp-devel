(*  Title:      Zippy/zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "DEP_ZIPPER"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  type @{AllT_args} zipper
  structure ZM : \<^eval>\<open>sfx_T_nargs "DEP_ZIPPER_MORPHS"\<close>
  sharing type ZM.zipper = zipper
  sharing type ZM.M.t = M.t
  structure ZD : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
  sharing type ZD.zipper = zipper
end

functor \<^eval>\<open>sfx_T_nargs "Dep_Zipper"\<close>(
    structure ZM : \<^eval>\<open>sfx_T_nargs "DEP_ZIPPER_MORPHS"\<close>
    structure ZD : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    sharing type ZD.zipper = ZM.zipper
  ) : \<^eval>\<open>sfx_T_nargs "DEP_ZIPPER"\<close> =
struct
structure ZM = ZM
structure ZD = ZD
open ZM
end

signature \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  type @{AllT_args} zipper
  structure ZM : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
  sharing type ZM.zipper = zipper
  sharing type ZM.M.t = M.t
  structure ZD : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
  sharing type ZD.zipper = zipper
end

functor \<^eval>\<open>sfx_T_nargs "Dep_Zipper_Zipper"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    type @{AllT_args} dep_zip
    type @{AllT_args} dep_unzip
    type @{AllT_args} dep_up
    type @{AllT_args} dep_down
    type @{AllT_args} dep_left
    type @{AllT_args} dep_right
  ) :
    \<^eval>\<open>sfx_T_nargs "DEP_ZIPPER"\<close>
    where type @{AllT_args} ZM.Zip.dep = @{AllT_args} dep_zip
    where type @{AllT_args} ZM.Unzip.dep = @{AllT_args} dep_unzip
    where type @{AllT_args} ZM.Up.dep = @{AllT_args} dep_up
    where type @{AllT_args} ZM.Down.dep = @{AllT_args} dep_down
    where type @{AllT_args} ZM.Left.dep = @{AllT_args} dep_left
    where type @{AllT_args} ZM.Right.dep = @{AllT_args} dep_right =
struct
open Z
structure ZM = \<^eval>\<open>sfx_T_nargs "Dep_Zipper_Morphs_Zipper_Morphs"\<close>(
  structure Z = ZM
  type @{AllT_args} dep_zip = @{AllT_args} dep_zip
  type @{AllT_args} dep_unzip = @{AllT_args} dep_unzip
  type @{AllT_args} dep_up = @{AllT_args} dep_up
  type @{AllT_args} dep_down = @{AllT_args} dep_down
  type @{AllT_args} dep_left = @{AllT_args} dep_left
  type @{AllT_args} dep_right = @{AllT_args} dep_right)
end

functor \<^eval>\<open>sfx_T_nargs "Zipper_Dep_Zipper"\<close>(
    Z : \<^eval>\<open>sfx_T_nargs "DEP_ZIPPER"\<close>
    where type @{AllT_args} ZM.Zip.dep = unit
    where type @{AllT_args} ZM.Unzip.dep = unit
    where type @{AllT_args} ZM.Up.dep = unit
    where type @{AllT_args} ZM.Down.dep = unit
    where type @{AllT_args} ZM.Left.dep = unit
    where type @{AllT_args} ZM.Right.dep = unit
  ) : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close> =
struct
open Z
structure ZM = \<^eval>\<open>sfx_T_nargs "Zipper_Morphs_Dep_Zipper_Morphs"\<close>(ZM)
end

functor \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
    structure ZM : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
    structure ZD : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    sharing type ZD.zipper = ZM.zipper
  ) : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close> =
struct
structure ZM = ZM
structure ZD = ZD
open ZM
end

\<^imap>\<open>\<open>{i}\<close> => \<open>
functor \<^eval>\<open>sfx_inst_T_nargs "Instantiate_Zipper" {i}\<close>(
    type @{AllT_args} inst
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    where type @{AllT_args} ZM.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.ZM.container
    where type @{AllT_args} ZD.content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.ZD.content
    where type @{AllT_args} ZD.zcontext = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.ZD.zcontext
    where type @{AllT_args} zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.zipper
  = Z\<close>\<close>
