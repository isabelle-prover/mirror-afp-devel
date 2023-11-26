(*
  File:     Cardinality_Continuum/Cardinality_Euclidean_Space.thy
  Author:   Manuel Eberl (University of Innsbruck)

  The cardinality of a Euclidean space.
  This is a separate file because we need HOL-Analysis for Euclidean spaces, which is a 
  rather hefty library to import.
*)
theory Cardinality_Euclidean_Space
  imports "HOL-Analysis.Analysis" Cardinality_Continuum
begin

text \<open>
  With these results, it is now easy to see that any Euclidean space 
  (i.e.\ finite-dimensional real vector space) has the same cardinality as \<open>\<real>\<close>:
\<close>
corollary card_of_UNIV_euclidean_space:
  "|UNIV :: 'a :: euclidean_space set| =o ctwo ^c natLeq"
proof -
  have "|span Basis :: 'a set| =o |UNIV :: real set|"
    by (rule card_of_span_finite_dim_infinite_field) 
       (simp_all add: independent_Basis infinite_UNIV_char_0)
  also have "|UNIV :: real set| =o ctwo ^c natLeq"
    by (rule card_of_UNIV_real)
  finally show ?thesis
    by simp
qed

text \<open>
  In particular, this applies to \<open>\<complex>\<close> and $\mathbb{R}^n$:
\<close>
corollary card_of_complex: "|UNIV :: complex set| =o ctwo ^c natLeq"
  by (rule card_of_UNIV_euclidean_space)

corollary card_of_real_vec: "|UNIV :: (real ^ 'n :: finite) set| =o ctwo ^c natLeq"
  by (rule card_of_UNIV_euclidean_space)

end