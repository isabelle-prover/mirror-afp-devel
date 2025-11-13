(*  Title:      Zippy/modify_zipper_morphs_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Modify_Zipper_Morphs_Zipper"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
    type @{AllT_args} nzipper
    val nzipper : (@{ParaT_args} @{AllT_args} Z.zipper, @{AllT_args} nzipper) Z.morph
    val dest_nzipper : (@{ParaT_args} @{AllT_args} nzipper, @{AllT_args} Z.zipper) Z.morph
  )
  : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
    where type @{AllT_args} container = @{AllT_args} Z.container
    where type @{AllT_args} zipper = @{AllT_args} nzipper
  =
\<^eval>\<open>sfx_T_nargs "Zipper_Morphs"\<close>(
  open Z
  structure M = Z
  type @{AllT_args} zipper = @{AllT_args} nzipper
  structure Base =
  struct
    type @{AllT_args} nfrom = @{AllT_args} nzipper
    type @{AllT_args} nto = @{AllT_args} nzipper
    val dest_nfrom = dest_nzipper
    val nto = nzipper
  end
  structure Zip = \<^eval>\<open>sfx_T_nargs "Modify_Morph_To"\<close>(open Base; structure M = Z.Zip)
  val zip = Zip.morph
  structure Unzip = \<^eval>\<open>sfx_T_nargs "Modify_Morph_From"\<close>(open Base; structure M = Z.Unzip)
  val unzip = Unzip.morph
  structure Up = \<^eval>\<open>sfx_T_nargs "Modify_Morph_From_To"\<close>(open Base; structure M = Z.Up)
  val up = Up.morph
  structure Down = \<^eval>\<open>sfx_T_nargs "Modify_Morph_From_To"\<close>(open Base; structure M = Z.Down)
  val down = Down.morph
  structure Left = \<^eval>\<open>sfx_T_nargs "Modify_Morph_From_To"\<close>(open Base; structure M = Z.Left)
  val left = Left.morph
  structure Right = \<^eval>\<open>sfx_T_nargs "Modify_Morph_From_To"\<close>(open Base; structure M = Z.Right)
  val right = Right.morph
)