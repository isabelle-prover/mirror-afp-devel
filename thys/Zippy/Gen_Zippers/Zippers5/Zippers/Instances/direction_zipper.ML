(*  Title:      Zippy/direction_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Direction_Zipper"\<close>(M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    where type @{AllT_args} ZD.content = Zipper_Direction.direction
    where type @{AllT_args} ZD.zcontext = unit
    where type @{AllT_args} ZM.container = Zipper_Direction.direction
    where type @{AllT_args} ZM.zipper = Zipper_Direction.direction
  =
\<^eval>\<open>sfx_T_nargs "Content_Zipper"\<close>(
  structure M = M
  type @{AllT_args} container = Zipper_Direction.direction
  type @{AllT_args} content = Zipper_Direction.direction
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(M.M)
  fun zip x = x |> A.K Zipper_Direction.Zip
  fun unzip x = x |> A.K Zipper_Direction.Unzip
  fun up x = x |> A.K Zipper_Direction.Up
  fun down x = x |> A.K Zipper_Direction.Down
  fun left x = x |> A.K Zipper_Direction.Left
  fun right x = x |> A.K Zipper_Direction.Right
)
