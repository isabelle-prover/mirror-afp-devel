(*  Title:      Zippy/modify_zipper_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Modify_Zipper_Zipper"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    type @{AllT_args} nzipper
    val nzipper : @{AllT_args} Z.zipper -> @{AllT_args} nzipper
    val dest_nzipper : @{AllT_args} nzipper -> @{AllT_args} Z.zipper
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    where type @{AllT_args} ZM.container = @{AllT_args} Z.ZM.container
    where type @{AllT_args} ZD.content = @{AllT_args} Z.ZD.content
    where type @{AllT_args} ZD.zcontext = @{AllT_args} Z.ZD.zcontext
    where type @{AllT_args} zipper = @{AllT_args} nzipper
  =
\<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure Base =
  struct
    type @{AllT_args} nzipper = @{AllT_args} nzipper
    val nzipper = nzipper
    val dest_nzipper = dest_nzipper
  end
  structure ZM = \<^eval>\<open>sfx_T_nargs "Modify_Zipper_Morphs_Zipper"\<close>(
    open Base;
    fun nzipper x = Z.K.arr Base.nzipper x
    fun dest_nzipper x = Z.K.arr Base.dest_nzipper x
    structure Z = Z.ZM)
  structure ZD = \<^eval>\<open>sfx_T_nargs "Modify_Zipper_Data_Zipper"\<close>(open Base; structure Z = Z.ZD)
)
