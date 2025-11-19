(*  Title:      Zippy/modify_zipper_data_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Modify_Zipper_Data_Zipper"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    type @{AllT_args} nzipper
    val nzipper : @{AllT_args} Z.zipper -> @{AllT_args} nzipper
    val dest_nzipper : @{AllT_args} nzipper -> @{AllT_args} Z.zipper
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    where type @{AllT_args} content = @{AllT_args} Z.content
    where type @{AllT_args} zcontext = @{AllT_args} Z.zcontext
    where type @{AllT_args} zipper = @{AllT_args} nzipper
  =
struct

open Z

type @{AllT_args} zipper = @{AllT_args} nzipper
fun zipper x = Z.zipper x |> nzipper

structure Base =
struct
  type @{AllT_args} ncontainer = @{AllT_args} nzipper
  val ncontainer = nzipper
  val dest_ncontainer = dest_nzipper
end
structure Co = \<^eval>\<open>sfx_T_nargs "Modify_Structured_Lens_Container"\<close>(
  open Base; structure L = Co)
structure ZCtxt = \<^eval>\<open>sfx_T_nargs "Modify_Structured_Lens_Container"\<close>(
  open Base; structure L = ZCtxt)

end
