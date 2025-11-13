(*  Title:      Zippy/zipper_position_util.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_ParaT_nargs "ZIPPER_POSITION_UTIL"\<close> =
sig
  structure C : \<^eval>\<open>sfx_ParaT_nargs "CATEGORY_BASE"\<close>
  val move_xpos : (@{ParaT_args} 'a) C.emorph -> (@{ParaT_args}  'a) C.emorph -> int ->
    (@{ParaT_args}  'a) C.emorph
  val move_pos : (@{ParaT_args} 'a) C.emorph -> (@{ParaT_args} 'a) C.emorph ->
    (@{ParaT_args} 'a) C.emorph -> Zipper_Position.pos -> (@{ParaT_args} 'a) C.emorph
end

functor \<^eval>\<open>sfx_ParaT_nargs "Zipper_Position_Util"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "ZIPPER_POSITION_UTIL"\<close> =
struct
structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(M)
structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A)
structure C = \<^eval>\<open>sfx_ParaT_nargs "Category"\<close>(A)
structure LF = \<^eval>\<open>sfx_ParaT_nargs "Foldable_Monad"\<close>(
  structure F = \<^eval>\<open>sfx_ParaT_nargs "List_Foldable_Trans"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Identity_Foldable"\<close>)
  structure M = M)
local open SC C
in
fun move_xpos left right x =
  if x = 0 then id ()
  else if x < 0 then C.repeatn (Int.abs x) left
  else C.repeatn x right

fun move_pos _ _ _ [] = id ()
  | move_pos left right down (x :: xs) =
      LF.foldrM (fn x => move_xpos left right x >>> down) xs
      >>> move_xpos left right x
end
end
