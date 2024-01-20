section \<open>Indexed Products of Probability Mass Functions\<close>

theory Product_PMF_Ext
  imports
    Probability_Ext
    Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
begin

text \<open>The following aliases are here to prevent possible merge-conflicts. The lemmas have been
moved to @{theory Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF}.\<close>

abbreviation prod_pmf where "prod_pmf \<equiv> Universal_Hash_Families_More_Product_PMF.prod_pmf"
abbreviation restrict_dfl where "restrict_dfl \<equiv> Universal_Hash_Families_More_Product_PMF.restrict_dfl"

lemmas pmf_prod_pmf = pmf_prod_pmf
lemmas PiE_defaut_undefined_eq = PiE_defaut_undefined_eq
lemmas set_prod_pmf = set_prod_pmf
lemmas prob_prod_pmf' = prob_prod_pmf'
lemmas prob_prod_pmf_slice = prob_prod_pmf_slice
lemmas pi_pmf_decompose = pi_pmf_decompose
lemmas restrict_dfl_iter = restrict_dfl_iter
lemmas indep_vars_restrict' = indep_vars_restrict'
lemmas indep_vars_restrict_intro' = indep_vars_restrict_intro'
lemmas integrable_Pi_pmf_slice = integrable_Pi_pmf_slice
lemmas expectation_Pi_pmf_slice = expectation_Pi_pmf_slice
lemmas expectation_prod_Pi_pmf = expectation_prod_Pi_pmf
lemmas variance_prod_pmf_slice = variance_prod_pmf_slice
lemmas Pi_pmf_bind_return = Pi_pmf_bind_return

end