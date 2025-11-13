(*  Title:      Zippy/zippy_monad_util.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_MONAD_UTIL =
sig
  structure Mo : \<^eval>\<open>sfx_ParaT_nargs "MONAD"\<close>
  structure MB : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  sharing type MB.M.t = Mo.t
  structure A : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW"\<close>
  sharing type A.K.M.t = Mo.t
  structure SC : \<^eval>\<open>sfx_ParaT_nargs "SEMI_CATEGORY"\<close>
  where type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) A.morph
  structure C : \<^eval>\<open>sfx_ParaT_nargs "CATEGORY"\<close>
  where type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) A.morph
  structure AA : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_APPLY"\<close>
  sharing type AA.K.M.t = Mo.t
  structure AC : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_CHOICE"\<close>
  sharing type AC.K.M.t = Mo.t
end

functor Zippy_Monad_Util(M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>) : ZIPPY_MONAD_UTIL =
struct
structure Mo = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(M)
structure MB = \<^eval>\<open>sfx_ParaT_nargs "Morph_Base"\<close>(Mo)
structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(M)
structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A)
structure C = \<^eval>\<open>sfx_ParaT_nargs "Category"\<close>(A)
structure AA = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply"\<close>(M)
structure AC = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Choice"\<close>(M)
end