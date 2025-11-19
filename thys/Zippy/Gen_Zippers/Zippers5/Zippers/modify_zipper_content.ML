(*  Title:      Zippy/modify_zipper_content.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Modify_Zipper_Content"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    type @{AllT_args} ncontent
    val ncontent : @{AllT_args} Z.ZD.content -> @{AllT_args} ncontent
    val dest_ncontent : @{AllT_args} ncontent -> @{AllT_args} Z.ZD.content
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    where type @{AllT_args} ZM.container = @{AllT_args} Z.ZM.container
    where type @{AllT_args} ZD.content = @{AllT_args} ncontent
    where type @{AllT_args} ZD.zcontext = @{AllT_args} Z.ZD.zcontext
    where type @{AllT_args} zipper = @{AllT_args} Z.zipper
  =
\<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure ZM = Z.ZM
  structure ZD = \<^eval>\<open>sfx_T_nargs "Modify_Zipper_Data_Content"\<close>(
    structure Z = Z.ZD
    type @{AllT_args} ncontent = @{AllT_args} ncontent
    val ncontent = ncontent
    val dest_ncontent = dest_ncontent)
)
