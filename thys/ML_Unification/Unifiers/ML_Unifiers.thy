\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>ML Unifiers\<close>
theory ML_Unifiers
  imports
    ML_Unification_Base
    ML_Functor_Instances
    ML_Priorities
    Simps_To
begin

paragraph \<open>Summary\<close>
text \<open>Unification modulo equations and combinators for unifiers.\<close>

paragraph \<open>Combinators\<close>

ML_file\<open>unification_combinator.ML\<close>

ML_file\<open>unification_combine.ML\<close>
ML\<open>
  @{functor_instance struct_name = Standard_Unification_Combine
    and functor_name = Unification_Combine
    and id = \<open>""\<close>}
\<close>
local_setup \<open>Standard_Unification_Combine.setup_attribute NONE\<close>


paragraph \<open>Standard Unifiers\<close>

ML_file\<open>higher_order_unification.ML\<close>
ML_file\<open>higher_order_pattern_unification.ML\<close>
ML_file\<open>first_order_unification.ML\<close>

subparagraph \<open>Derived Unifiers\<close>

ML_file\<open>higher_order_pattern_decomp_unification.ML\<close>
ML_file\<open>var_higher_order_pattern_unification.ML\<close>


paragraph \<open>Unification via Tactics\<close>

ML_file\<open>tactic_unification.ML\<close>

subparagraph \<open>Unification via Simplification\<close>

ML_file\<open>simplifier_unification.ML\<close>

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
  (Simplifier_Unification.simp_unify
  |> Unification_Combinator.norm_closed_unifier
    (#norm_term Standard_Mixed_Unification.norms_first_higherp_decomp_comb_higher_unify)
  |> Unification_Combinator.unifier_from_closed_unifier
  |> K)
  (Standard_Unification_Combine.default_metadata \<^binding>\<open>simp_unif\<close>)\<close>]]


end
