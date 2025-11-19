\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_Unifiers
  imports
    ML_Costs_Priorities
    ML_Functor_Instances
    ML_Unifiers_Base
    Simps_To
begin

paragraph \<open>Summary\<close>
text \<open>More unifiers.\<close>

paragraph \<open>Derived Unifiers\<close>

ML_file\<open>var_higher_order_pattern_unification.ML\<close>

subparagraph \<open>Unification via Simplification\<close>

lemma eq_if_SIMPS_TO_UNIF_if_SIMPS_TO_UNIF:
  assumes "PROP SIMPS_TO_UNIF t t'"
  and "PROP SIMPS_TO_UNIF s t'"
  shows "s \<equiv> t"
  using assms by (simp add: SIMPS_TO_eq SIMPS_TO_UNIF_eq)

ML_file\<open>simplifier_unification.ML\<close>

paragraph \<open>Combining Unifiers\<close>

ML_file\<open>unification_combine.ML\<close>
ML\<open>
\<^functor_instance>\<open>struct_name: Standard_Unification_Combine
  functor_name: Unification_Combine
  id: \<open>""\<close>\<close>
\<close>
local_setup \<open>Standard_Unification_Combine.setup_attribute NONE\<close>

paragraph \<open>Mixture of Unifiers\<close>

ML_file\<open>mixed_unification.ML\<close>
ML\<open>
\<^functor_instance>\<open>struct_name: Standard_Mixed_Comb_Unification
  functor_name: Mixed_Comb_Unification
  id: \<open>""\<close>
  more_args: \<open>structure UC = Standard_Unification_Combine\<close>\<close>
\<close>

declare [[ucombine \<open>Standard_Unification_Combine.eunif_data
  (Standard_Unification_Combine.metadata \<^binding>\<open>var_hop_unif\<close> Prio.HIGH1,
  Var_Higher_Order_Pattern_Unification.e_unify
  #> Unification_Combinator.norm_unifier (Unification_Util.inst_norm_term'
    Standard_Mixed_Comb_Unification.norms_first_higherp_comb_unify))\<close>]]

declare [[ucombine \<open>
  let open Term_Normalisation
    (*ignore changes of schematic variables to avoid loops due to index-raising of some tactics*)
    val eq_beta_eta_dummy_vars = apply2 (beta_eta_short #> dummy_vars) #> op aconv
    val e_unif = Standard_Mixed_Comb_Unification.first_higherp_comb_e_unify
    val norms = Standard_Mixed_Comb_Unification.norms_first_higherp_comb_unify
    fun simp_unif unify_theory = Simplifier_Unification.simp_unify_progress eq_beta_eta_dummy_vars
      (Simplifier_Unification.simp_unify norms (e_unif Unification_Combinator.fail_unify) norms)
        (Unification_Util.inst_norm_term' norms) (e_unif unify_theory)
      |> Type_Unification.e_unify Unification_Util.unify_types
    val metadata = Standard_Unification_Combine.default_metadata \<^binding>\<open>simp_unif\<close>
  in Standard_Unification_Combine.eunif_data (metadata, simp_unif) end\<close>]]

end
