theory Abs_SAIS_Verification       
  imports Abs_SAIS_Verification_With_Valid_Precondition
begin

section "Final Theorem: Verification of a generalised SAIS construction algorithm"

text "The {@term \<open>abs_sais\<close>} implementation produces an output that is equivalent to that of a
      suffix array construction algorithm for lists of any type that can be linearly 
      ordered. This lifts the restriction that the algorithm only operates on natural 
      numbers terminated by a bottom element."

interpretation abs_sais_gen: Suffix_Array_General "sa_nat_wrapper map_to_nat abs_sais"
  by (simp add: Suffix_Array_Restricted_imp_General abs_sais.Suffix_Array_Restricted_axioms)

theorem abs_sais_gen_is_Suffix_Array_General:
  "Suffix_Array_General sa \<longleftrightarrow> sa = sa_nat_wrapper map_to_nat abs_sais"
  using Suffix_Array_General_determinism abs_sais_gen.Suffix_Array_General_axioms by auto

end