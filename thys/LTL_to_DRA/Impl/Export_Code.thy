(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Code Generation\<close>

theory Export_Code
  imports Main LTL_Compat LTL_Rabin_Impl 
    "../Aux/AList_Mapping2" 
    "../../LTL/LTL_Rewrite"
    "~~/src/HOL/Library/Code_Target_Numeral" 
    "~~/src/HOL/Library/Code_Char"
begin

subsection \<open>External Interface\<close>

--\<open>Fix the type to match the type of the LTL parser\<close>

definition 
  "ltlc_to_rabin eager mode (\<phi>\<^sub>c :: String.literal ltlc) \<equiv>
    (let
      \<phi>\<^sub>n = ltlc_to_ltln \<phi>\<^sub>c;
      \<Sigma> = map set (sublists (atoms_list \<phi>\<^sub>n));
      \<phi> = ltln_to_ltl (simplify mode \<phi>\<^sub>n)
     in
      (if eager then ltl_to_generalized_rabin\<^sub>C_af\<^sub>\<UU> \<Sigma> \<phi> else ltl_to_generalized_rabin\<^sub>C_af \<Sigma> \<phi>))"

theorem ltlc_to_rabin_exec_correct:
  assumes "range w \<subseteq> Pow (atoms_ltlc \<phi>\<^sub>c)"
  shows "w \<Turnstile>\<^sub>c \<phi>\<^sub>c \<longleftrightarrow> accept\<^sub>G\<^sub>R_LTS (ltlc_to_rabin eager mode \<phi>\<^sub>c) w" 
  (is "?lhs = ?rhs")
proof -
  let ?\<phi>\<^sub>n = "ltlc_to_ltln \<phi>\<^sub>c"
  let ?\<Sigma> = "map set (sublists (atoms_list ?\<phi>\<^sub>n))"
  let ?\<phi> = "ltln_to_ltl (simplify mode ?\<phi>\<^sub>n)"

  have "set ?\<Sigma> = Pow (atoms_ltln ?\<phi>\<^sub>n)"
    unfolding atoms_list_correct[symmetric] sublists_powset[symmetric] list.set_map ..  
  hence R: "range w \<subseteq> set ?\<Sigma>"
    using assms ltlc_to_ltln_atoms[symmetric] by metis

  have "w \<Turnstile>\<^sub>c \<phi>\<^sub>c \<longleftrightarrow> w \<Turnstile> ?\<phi>"
    by (simp only: ltlc_to_ltln_semantics simplify_correct ltln_to_ltl_semantics)
  also
  have "\<dots> \<longleftrightarrow> ?rhs"
    using ltl_to_generalized_rabin\<^sub>C_af\<^sub>\<UU>_correct[OF R] ltl_to_generalized_rabin\<^sub>C_af_correct[OF R] 
    unfolding ltlc_to_rabin_def Let_def by auto
  finally
  show ?thesis
    by simp
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
export_code true\<^sub>c Iff_ltlc Nop true Abs AList_Mapping.Mapping set ltlc_to_rabin 
  in SML module_name LTL file "../Code/LTL_to_DRA_Translator.sml"

end
