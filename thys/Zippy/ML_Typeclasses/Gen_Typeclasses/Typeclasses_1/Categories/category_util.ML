(*  Title:  category_util.ML
    Author: Kevin Kappelmann

Utilities on categories
*)
signature \<^eval>\<open>sfx_ParaT_nargs "ARROW_EXCEPTION_REPEAT"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_EXCEPTION"\<close>
  val repeat : (@{ParaT_args} 'a) emorph -> (@{ParaT_args} 'a) emorph
  val repeatn_safe : int -> (@{ParaT_args} 'a) emorph -> (@{ParaT_args} 'a) emorph
  val try_step : (@{ParaT_args} 'a, 'b) morph -> (@{ParaT_args} 'a) emorph ->
    (@{ParaT_args} 'a, 'b) morph
end

signature \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REPEAT"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_EXCEPTION_REPEAT"\<close>
  where type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception_Repeat"\<close>(
    AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REPEAT"\<close> =
struct

open AE
local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(AE); open SC
in
fun repeat move x = x |> try (move >>> repeat move)
fun repeatn_safe fuel move x = x |>
  (if fuel <= 0 then id ()
  else try (move >>> repeatn_safe (fuel - 1) move))
fun try_step f step x = x |> catch' f (step >>> try_step f step)
end

end