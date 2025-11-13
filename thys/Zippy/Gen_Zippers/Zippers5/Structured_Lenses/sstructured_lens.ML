(*  Title:  Zippy/sstructured_lens.ML
    Author: Kevin Kappelmann

Standard function space lenses
*)
signature \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close> =
  \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type (@{ParaT_args} 'a) K.M.t = 'a
  where type (@{ParaT_args} 't, 'o, 's, 'i) lens =
    (@{ParaT_args} 't, 'o, 's, 'i) \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".lens"\<close>

structure \<^eval>\<open>sfx_ParaT_nargs "SLens_Kleisli_Identity"\<close> =
  \<^eval>\<open>sfx_ParaT_nargs "Lens_Kleisli"\<close>(
    structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>
    structure K = \<^eval>\<open>sfx_ParaT_nargs "Kleisli"\<close>(\<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>))

functor \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(A :
  sig
    type @{AllT_args} container
    type @{AllT_args} data
    val lens : unit -> (@{ParaT_args} @{AllT_args} container, @{AllT_args} data)
      \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".slens"\<close>
  end
  ) :
    \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} A.container
    where type @{AllT_args} data = @{AllT_args} A.data
  = \<^eval>\<open>sfx_T_nargs "Structured_Lens"\<close>(
  structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens_Kleisli_Identity"\<close>
  open A)
