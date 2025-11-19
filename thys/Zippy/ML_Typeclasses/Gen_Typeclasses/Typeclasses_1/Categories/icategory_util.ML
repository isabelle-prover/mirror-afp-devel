(*  Title:  icategory_util.ML
    Author: Kevin Kappelmann

Utilities on indexed categories
*)
signature \<^eval>\<open>sfx_ParaT_nargs "IARROW_EXCEPTION_REPEAT"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_EXCEPTION"\<close>
  val repeat : (@{ParaT_args} 'i, 'i, 'a) emorph -> (@{ParaT_args} 'i, 'i, 'a) emorph
  val repeatn_safe : int -> (@{ParaT_args} 'i, 'i, 'a) emorph -> (@{ParaT_args} 'i, 'i, 'a) emorph
  val try_step : (@{ParaT_args} 'i, 'j, 'a, 'b) morph -> (@{ParaT_args} 'i, 'i, 'a) emorph ->
    (@{ParaT_args} 'i, 'j, 'a, 'b) morph
end

signature \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_EXCEPTION_REPEAT"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_EXCEPTION_REPEAT"\<close>
  where type (@{ParaT_args} 'i, 'j, 'a, 'b) morph = (@{ParaT_args} 'i, 'j, 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Exception_Repeat"\<close>(
    AE : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_EXCEPTION"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_EXCEPTION_REPEAT"\<close> =
struct

open AE
local structure SC = \<^eval>\<open>sfx_ParaT_nargs "ISemi_Category"\<close>(AE); open SC
in
fun repeat move x = x |> try (move >>> repeat move)
fun repeatn_safe fuel move x = x |>
  (if fuel <= 0 then id ()
  else try (move >>> repeatn_safe (fuel - 1) move))
fun try_step f step x = x |> catch' f (step >>> try_step f step)
end

end
