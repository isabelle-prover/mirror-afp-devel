(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Code Generation\<close>

theory Export_Code
  imports Main LTL_CAVA_Compat LTL_Rabin_Impl "../Aux/AList_Mapping2" "~~/src/HOL/Library/Code_Target_Numeral" "~~/src/HOL/Library/Code_Char"
begin

subsection \<open>External Interface\<close>

--\<open>Fix the type to match the type of the LTL parser\<close>
definition 
  "ltlc_to_rabin (\<phi> :: String.literal ltlc) \<equiv> ltl_to_generalized_rabin\<^sub>C_af_simp (ltlc_to_ltl False \<phi>)"

definition 
  "ltlc_to_rabin\<^sub>\<UU> (\<phi> :: String.literal ltlc) \<equiv> ltl_to_generalized_rabin\<^sub>C_af\<^sub>\<UU>_simp (ltlc_to_ltl False \<phi>)"

theorem ltlc_to_rabin_exec_correct:
  assumes "range w \<subseteq> Pow (ltlc_aprops \<phi>)"
  shows "w \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> accept\<^sub>G\<^sub>R_LTS (ltlc_to_rabin \<phi>) w" (is ?t1)
    and "w \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> accept\<^sub>G\<^sub>R_LTS (ltlc_to_rabin\<^sub>\<UU> \<phi>) w" (is ?t2)
proof -
  have "ltlc_aprops \<phi> = vars (ltlc_to_ltl True \<phi>)" "ltlc_aprops \<phi> = vars (ltlc_to_ltl False \<phi>)"
    by (induction \<phi>) auto                            
  thus ?t1 ?t2
    using assms ltl_to_generalized_rabin\<^sub>C_af_simp_correct ltl_to_generalized_rabin\<^sub>C_af\<^sub>\<UU>_simp_correct 
    using translation_correct(1) ltlc_to_rabin_def ltlc_to_rabin\<^sub>\<UU>_def by metis+
qed

subsection \<open>Register Code Equations\<close>

lemma [code]:
  "\<up>\<Delta>\<^sub>\<times> f (AList_Mapping.Mapping xs) c = AList_Mapping.Mapping (map_ran (\<lambda>a b. f a b c) xs)"
proof -
  have "\<And>x. (\<Delta>\<^sub>\<times> f (map_of xs) c) x = (map_of (map (\<lambda>(k, v). (k, f k v c)) xs)) x"
    by (induction xs) auto
  thus ?thesis
    by (transfer; simp add: map_ran_def)
qed

lemmas ltl_to_rabin_base_code_export [code, code_unfold] =
  ltl_to_rabin_base_code_def.ltl_to_generalized_rabin\<^sub>C.simps
  ltl_to_rabin_base_code_def.reachable_transitions\<^sub>C_def 
  ltl_to_rabin_base_code_def.mappings\<^sub>C_code 
  ltl_to_rabin_base_code_def.delta\<^sub>C.simps
  ltl_to_rabin_base_code_def.initial\<^sub>C.simps 
  ltl_to_rabin_base_code_def.Acc_inf\<^sub>C.simps 
  ltl_to_rabin_base_code_def.Acc_fin\<^sub>C.simps
  ltl_to_rabin_base_code_def.max_rank_of\<^sub>C_def

lemmas M_fin\<^sub>C_lhs [code del, code_unfold] = 
  M_fin\<^sub>C_af\<^sub>\<UU>_lhs_def M_fin\<^sub>C_af_lhs_def 

--\<open>Export translator (and also constructors)\<close>
export_code true\<^sub>c true Abs AList_Mapping.Mapping set ltlc_to_rabin ltlc_to_rabin\<^sub>\<UU> 
  in SML module_name LTL_to_DRA_Translator file "../Code/LTL_to_DRA_Translator.sml"

end