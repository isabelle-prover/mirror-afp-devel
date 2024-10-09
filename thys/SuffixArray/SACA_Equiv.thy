theory SACA_Equiv
  imports "sais/abs-proof/Abs_SAIS_Verification"
          "simple/Simple_SACA_Verification"
          "sais/proof/SAIS_Verification"
begin

lemma Suffix_Array_General_imp_suffix_array:
  "Suffix_Array_General sa \<Longrightarrow> 
   sa s = simple_saca s"
  using Suffix_Array_General_determinism simple_saca.Suffix_Array_General_axioms by blast

theorem Suffix_Array_General_equiv_spec:
  "Suffix_Array_General sa \<longleftrightarrow>
   sa = simple_saca"
  using Suffix_Array_General_imp_suffix_array simple_saca.Suffix_Array_General_axioms by blast

corollary abs_sais_equiv_simple_saca:
  "sa_nat_wrapper map_to_nat abs_sais = simple_saca"
  using Suffix_Array_General_equiv_spec abs_sais_gen.Suffix_Array_General_axioms by auto

corollary sais_equiv_simple_saca:
  "sa_nat_wrapper map_to_nat sais = simple_saca"
  using sais_gen_is_Suffix_Array_General 
        Suffix_Array_General_equiv_spec  
  by auto
 
end
