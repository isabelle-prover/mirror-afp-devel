\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Setup for HOL\<close>
theory ML_Unification_HOL_Setup
  imports
    HOL.HOL
    ML_Unification_Hints
begin

lemma eq_eq_True: "P \<equiv> (P \<equiv> Trueprop True)" by standard+ simp_all
declare [[uhint where hint_preprocessor = \<open>Unification_Hints_Base.obj_logic_hint_preprocessor
  @{thm atomize_eq[symmetric]} (Conv.rewr_conv @{thm eq_eq_True})\<close>]]
and [[rec_uhint where hint_preprocessor = \<open>Unification_Hints_Base.obj_logic_hint_preprocessor
  @{thm atomize_eq[symmetric]} (Conv.rewr_conv @{thm eq_eq_True})\<close>]]

lemma eq_TrueI: "PROP P \<Longrightarrow> PROP P \<equiv> Trueprop True" by (standard) simp
declare [[ucombine add = \<open>Standard_Unification_Combine.eunif_data
  (Simplifier_Unification.SIMPS_TO_unify @{thm eq_TrueI}
  |> Unification_Combinator.norm_unifier (Unification_Util.inst_norm_term'
      Standard_Mixed_Unification.norms_first_higherp_decomp_comb_higher_unify)
  |> K)
  (Standard_Unification_Combine.metadata \<^binding>\<open>SIMPS_TO_unif\<close> Prio.HIGH)\<close>]]

declare [[ucombine add = \<open>
  let
    open Term_Normalisation
    (*ignore changes of schematic variables to avoid loops due to index-raising of some tactics*)
    val eq_beta_eta_dummy_vars = apply2 (beta_eta_short #> dummy_vars) #> op aconv
  in
    Standard_Unification_Combine.eunif_data
      (Simplifier_Unification.simp_unify_progress eq_beta_eta_dummy_vars
        (Simplifier_Unification.SIMPS_TO_UNIF_unify @{thm eq_TrueI}
          Standard_Mixed_Unification.norms_first_higherp_decomp_comb_higher_unify)
        (Unification_Util.inst_norm_term'
          Standard_Mixed_Unification.norms_first_higherp_decomp_comb_higher_unify)
        Standard_Mixed_Unification.first_higherp_decomp_comb_higher_unify
      |> K)
      (Standard_Unification_Combine.metadata \<^binding>\<open>SIMPS_TO_UNIF_unif\<close> Prio.HIGH)
  end\<close>]]


end
