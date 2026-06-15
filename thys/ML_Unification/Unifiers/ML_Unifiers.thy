\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_Unifiers
  imports
    ML_Costs_Priorities
    ML_Generic_Data_Utils
    ML_Unifiers_Base
    Simps_To
begin

paragraph \<open>Summary\<close>
text \<open>More unifiers.\<close>

paragraph \<open>Derived Unifiers\<close>

ML_file\<open>higher_order_pattern_var_unification.ML\<close>

subparagraph \<open>Unification via Simplification\<close>

lemma eq_if_SIMPS_TO_UNIF_if_SIMPS_TO_UNIF:
  assumes "t \<equiv>\<^sup>?> t'"
  and "s \<equiv>\<^sup>?> t'"
  shows "s \<equiv> t"
  using assms by (simp add: SIMPS_TO_eq SIMPS_TO_UNIF_eq)

ML_file\<open>simplifier_unification.ML\<close>

paragraph \<open>Combining Unifiers\<close>

ML_file\<open>unification_combine.ML\<close>
ML\<open>
\<^functor_instance>\<open>struct_name: Unification_Combine
  functor_name: Unification_Combine_Functor
  id: \<open>"ucombine"\<close>\<close>
\<close>
local_setup \<open>Unification_Combine.setup_attribute NONE\<close>

paragraph \<open>Mixture of Unifiers\<close>

ML_file\<open>mixed_unification.ML\<close>
ML\<open>
\<^functor_instance>\<open>struct_name: Mixed_Comb_Unification
  functor_name: Mixed_Comb_Unification_Functor
  id: \<open>"mixed_unif"\<close>
  more_args: \<open>structure UC = Unification_Combine\<close>\<close>
\<close>

declare [[ucombine \<open>Unification_Combine.eunif_data
  (Unification_Combine.metadata (\<^binding>\<open>hop_var_unify\<close>, Prio.HIGH1),
  Higher_Order_Pattern_Var_Unification.e_unify
  #> Unification_Combinator.norm_unifier (Unification_Util.inst_norm_term'
    Mixed_Comb_Unification.norms_fo_hop_comb_unify))\<close>]]

ML\<open>
structure Unification_Combine :
  sig
    include UNIFICATION_COMBINE
    structure HO_Unify : EXTENDED_HIGHER_ORDER_UNIFICATION_DATA
  end =
struct open Unification_Combine
\<^functor_instance>\<open>struct_name: HO_Unify
  functor_name: Extended_Higher_Order_Unification_Data
  path: FI.long_name
  id: \<open>FI.prefix_id "ho_unify"\<close>
  more_args: \<open>
    val parent_logger = logger
    val init_args = {
      search_bound = SOME (Config.get @{context} Unify.search_bound),
      results_bound = SOME 10,
      silence_bound_exceeded = SOME false
    }\<close>\<close>
end
\<close>
local_setup\<open>Unification_Combine.HO_Unify.setup_attribute NONE\<close>

declare [[ucombine \<open>Unification_Combine.eunif_data
  (Unification_Combine.metadata (Unification_Combine.HO_Unify.binding, Prio.VERY_LOW),
  K Unification_Combine.HO_Unify.unify)\<close>]]

declare [[ucombine \<open>
  let open Term_Normalisation
    (*quick check: ignore changes of schematic variables to avoid loops due to index-raising of some
    tactics; this check is not precise, but quick. The precise version is Term_Util.are_beta_eta_variants*)
    val eq_beta_eta_dummy_vars = apply2 (Same.commit beta_eta_short #> dummy_vars) #> op aconv
    val e_unif = Mixed_Comb_Unification.fo_hop_comb_e_unify
    val norms = Mixed_Comb_Unification.norms_fo_hop_comb_unify
    fun simp_unif unify_theory = Simplifier_Unification.simp_unify_progress eq_beta_eta_dummy_vars
      (Unification_Util.inst_norm_term' norms) (Simplifier_Unification.simp_unify norms)
      (e_unif unify_theory)
      |> Unification_Combinator.norm_unifier (#inst_term norms)
    val metadata = Unification_Combine.metadata (\<^binding>\<open>simp_unify\<close>, Prio.MEDIUM)
  in Unification_Combine.eunif_data (metadata, simp_unif) end\<close>]]

end
