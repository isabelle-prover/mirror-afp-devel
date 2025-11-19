(*  Title:      Zippy/position_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "POSITION_ZIPPER"\<close> =
  \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZM.container = unit
  where type @{AllT_args} ZD.content = Zipper_Position.pos

functor \<^eval>\<open>sfx_T_nargs "Position_Zipper"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>
    where type @{ParaT_args encl: "(" ")"} exn = unit
  ) : \<^eval>\<open>sfx_T_nargs "POSITION_ZIPPER"\<close> =
\<^eval>\<open>sfx_T_nargs "Content_Zipper"\<close>(
  structure Pos = Zipper_Position
  structure ME = M
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Morph_Base"\<close>(M)
  type @{AllT_args} container = unit
  type @{AllT_args} content = Pos.pos
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(M.M)
  fun zip x = x |> A.K Pos.init
  fun unzip x = x |> A.K ()
  fun up x = x |> (Pos.up #> (fn NONE => ME.throw () | SOME p => ME.pure p))
  fun down x = x |> A.arr Pos.down
  fun left x = x |> A.arr Pos.left
  fun right x = x |> A.arr Pos.right
)