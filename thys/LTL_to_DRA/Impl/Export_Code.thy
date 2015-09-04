(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Code Generation\<close>

theory Export_Code
  imports Main LTL_CAVA_Compat LTL_Rabin_Impl "~~/src/HOL/Library/Code_Target_Numeral" "~~/src/HOL/Library/Code_Char"
begin

--\<open>Fix the type to match the type of the LTL parser\<close>
definition "ltlc_to_rabin (\<phi> :: String.literal ltlc) \<equiv> ltl_to_rabin_exec_simp (ltlc_to_ltl False \<phi>)"

theorem ltlc_to_rabin_exec_correct:
  "range w \<subseteq> Pow (ltlc_aprops \<phi>) \<Longrightarrow> w \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> accept\<^sub>G\<^sub>R_LTS (ltlc_to_rabin \<phi>) w"
proof -
  assume "range w \<subseteq> Pow (ltlc_aprops \<phi>)"
  moreover
  have "ltlc_aprops \<phi> = vars (ltlc_to_ltl True \<phi>)" "ltlc_aprops \<phi> = vars (ltlc_to_ltl False \<phi>)"
    by (induction \<phi>) auto
  ultimately
  show ?thesis
    by (simp add: ltl_to_rabin_exec_simp_correct translation_correct(1) ltlc_to_rabin_def)
qed

--\<open>Export @{term true\<^sub>c} to make the @{type ltlc} type accessible to outside code\<close>
export_code true\<^sub>c ltlc_to_rabin in SML module_name LTL_to_DRA_Translator file "../Code/LTL_to_DRA_Translator.sml"

end