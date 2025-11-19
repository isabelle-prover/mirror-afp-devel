\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Lenses\<close>
theory ML_Lenses
  imports
    ML_ICategories
begin

ML_gen_file\<open>lens.ML\<close>

(*standard function space lense*)
ML\<open>
structure \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close> =
\<^eval>\<open>sfx_ParaT_nargs "Lens"\<close>(
  structure L = \<^eval>\<open>sfx_ParaT_nargs "Lens_Base"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Arrow_Apply"\<close>(
      \<^eval>\<open>sfx_ParaT_nargs "SArrow_Apply"\<close>))
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Arrow"\<close>(\<^eval>\<open>sfx_ParaT_nargs "SArrow_Apply"\<close>))

signature \<^eval>\<open>sfx_ParaT_nargs "SLENS"\<close> =
  \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  where type (@{ParaT_args} 'a, 'b) C.morph = 'a -> 'b
  where type (@{ParaT_args} 't, 'o, 's, 'i) lens =
    (@{ParaT_args} 't, 'o, 's, 'i) \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".lens"\<close>
\<close>

end