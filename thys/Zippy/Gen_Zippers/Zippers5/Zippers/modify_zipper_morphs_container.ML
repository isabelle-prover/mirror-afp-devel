(*  Title:      Zippy/modify_zipper_morphs_container.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Modify_Zipper_Morphs_Container"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
    type @{AllT_args} ncontainer
    val ncontainer : (@{ParaT_args} @{AllT_args} Z.container, @{AllT_args} ncontainer) Z.morph
    val dest_ncontainer : (@{ParaT_args} @{AllT_args} ncontainer, @{AllT_args} Z.container) Z.morph
  )
  : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
    where type @{AllT_args} container = @{AllT_args} ncontainer
    where type @{AllT_args} zipper = @{AllT_args} Z.zipper
  =
\<^eval>\<open>sfx_T_nargs "Zipper_Morphs"\<close>(
  open Z
  structure M = Z
  type @{AllT_args} container = @{AllT_args} ncontainer
  structure Base = struct
    type @{AllT_args} nfrom = @{AllT_args} ncontainer
    type @{AllT_args} nto = @{AllT_args} ncontainer
    val dest_nfrom = dest_ncontainer
    val nto = ncontainer
  end
  structure Zip = \<^eval>\<open>sfx_T_nargs "Modify_Morph_From"\<close>(
    open Base; structure M = Z.Zip)
  val zip = Zip.morph
  structure Unzip = \<^eval>\<open>sfx_T_nargs "Modify_Morph_To"\<close>(
    open Base; structure M = Z.Unzip)
  val unzip = Unzip.morph
  val up = Z.Up.morph
  val down = Z.Down.morph
  val left = Z.Left.morph
  val right = Z.Right.morph
)
