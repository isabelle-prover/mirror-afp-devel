\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_Unifiers
  imports
    ML_Functor_Instances
    ML_Priorities
    ML_Unifiers_Base
    Simps_To
begin

paragraph \<open>Summary\<close>
text \<open>More unifiers.\<close>

paragraph \<open>Derived Unifiers\<close>

ML_file\<open>higher_order_pattern_decomp_unification.ML\<close>
ML_file\<open>var_higher_order_pattern_unification.ML\<close>

paragraph \<open>Unification via Tactics\<close>

ML_file\<open>tactic_unification.ML\<close>

subparagraph \<open>Unification via Simplification\<close>

lemma eq_if_SIMPS_TO_UNIF_if_SIMPS_TO:
  assumes "PROP SIMPS_TO t t'"
  and "PROP SIMPS_TO_UNIF s t'"
  shows "s \<equiv> t"
  using assms by (simp add: SIMPS_TO_eq SIMPS_TO_UNIF_eq)

ML_file\<open>simplifier_unification.ML\<close>

paragraph \<open>Combining Unifiers\<close>

ML_file\<open>unification_combine.ML\<close>
ML\<open>
  @{functor_instance struct_name = Standard_Unification_Combine
    and functor_name = Unification_Combine
    and id = \<open>""\<close>}
\<close>
local_setup \<open>Standard_Unification_Combine.setup_attribute NONE\<close>

paragraph \<open>Mixture of Unifiers\<close>

ML_file\<open>mixed_unification.ML\<close>
ML\<open>
  @{functor_instance struct_name = Standard_Mixed_Unification
    and functor_name = Mixed_Unification
    and id = \<open>""\<close>
    and more_args = \<open>structure UC = Standard_Unification_Combine\<close>}
\<close>

declare [[ucombine add = \<open>Standard_Unification_Combine.eunif_data
  (Var_Higher_Order_Pattern_Unification.e_unify Unification_Combinator.fail_unify
  |> Unification_Combinator.norm_unifier
    (#norm_term Standard_Mixed_Unification.norms_first_higherp_decomp_comb_higher_unify)
  |> K)
  (Standard_Unification_Combine.metadata \<^binding>\<open>var_hop_unif\<close> Prio.HIGH)\<close>]]

declare [[ucombine add = \<open>Standard_Unification_Combine.eunif_data
  (Simplifier_Unification.simp_unify_progress Envir.aeconv Simplifier_Unification.simp_unify
    (#norm_term Standard_Mixed_Unification.norms_first_higherp_decomp_comb_higher_unify)
    Standard_Mixed_Unification.norms_first_higherp_decomp_comb_higher_unify
    Standard_Mixed_Unification.first_higherp_decomp_comb_higher_unify
  |> Type_Unification.e_unify Unification_Util.unify_types
  |> K)
  (Standard_Unification_Combine.default_metadata \<^binding>\<open>simp_unif\<close>)
  \<close>]]

end
