(*  Title:      Zippy/morph_base.ML
    Author:     Kevin Kappelmann

Kleisli morphisms
*)
signature \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close> =
sig
  structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_BASE"\<close>
  sharing type K.K.M.t = M.t
  type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) K.morph
  type (@{ParaT_args} 'a) emorph = (@{ParaT_args} 'a) K.emorph
end

functor \<^eval>\<open>sfx_ParaT_nargs "Morph_Base"\<close>(M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close> =
struct
structure M = M
structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply_Base"\<close>(M)
open A
structure K = A
end
