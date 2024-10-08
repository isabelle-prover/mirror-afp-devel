section \<open>Examples for WS1S (Singleton Semantics)\<close>

(*<*)
theory WS1S_Alt_Examples
imports Formula_Derivatives.WS1S_Alt_Formula
begin
(*>*)

abbreviation (input) FImp where "FImp \<phi> \<psi> \<equiv> FOr (FNot \<phi>) \<psi>"

definition "Thm idx \<phi> = check_eqv idx \<phi> (FBool True)"

export_code Thm in SML module_name Thm

abbreviation FTrue (\<open>\<top>\<close>) where "FTrue \<equiv> FBool True"
abbreviation FFalse (\<open>\<bottom>\<close>) where "FFalse \<equiv> FBool False"

notation FImp (infixr \<open>-->\<close> 25)
notation (output) FO (\<open>1\<close>)
notation (output) SO (\<open>2\<close>)
notation FEx (\<open>\<exists>\<^sub>_ _\<close> [10] 10)
notation FAll (\<open>\<forall>\<^sub>_ _\<close> [10] 10)
notation FNot (\<open>\<not> _\<close> [40] 40)
notation FOr (infixr \<open>\<or>\<close> 30)
notation FAnd (infixr \<open>\<and>\<close> 35)
abbreviation FLess (\<open>x\<^sub>_ < x\<^sub>_\<close> [65, 66] 65) where "FLess m1 m2 \<equiv> FBase (Less m1 m2)"
abbreviation FIn (\<open>x\<^sub>_ \<in> X\<^bsub>_\<^esub>\<close> [65, 66] 65) where "FIn m M \<equiv> FBase (In m M)"
abbreviation FQ (\<open>[x\<^sub>_]\<close> [66] 65) where "FQ m \<equiv> FBase (Fo m)"

declare check_eqv_code[code del]

(*true in M2L, false in WS1S*)
definition "M2L = (FEx SO (FAll FO (FBase (In 0 0))) :: formula)"
(*false in M2L, true in WS1S*)
definition "\<Phi> = (FAll FO (FEx FO (FBase (Less 1 0))) :: formula)"

lemma "Thm (Abs_idx (0, 1)) (FNot M2L)"
  by (simp add: M2L_def Thm_def) check_equiv

lemma "Thm (Abs_idx (0, 0)) \<Phi>"
  by (simp add: Thm_def \<Phi>_def) check_equiv

abbreviation Globally (\<open>\<box>_\<close> [40] 40) where "Globally P == %n. FAll FO (FImp (FNot (FBase (Less (n+1) 0))) (P 0))"
abbreviation Future (\<open>\<diamond>_\<close> [40] 40) where "Future P == %n. FEx FO (FAnd (FNot (FBase (Less (n+1) 0))) (P 0))"
abbreviation IMP (infixr \<open>\<rightarrow>\<close> 50) where "IMP P1 P2 == %n. FImp (P1 n) (P2 n)"

definition \<Psi> :: "nat \<Rightarrow> formula" where
  "\<Psi> n = FAll FO (((\<box>(foldr (\<lambda>i \<phi>. (\<lambda>m. FBase (In m i)) \<rightarrow> \<phi>) [0..<n] (\<lambda>m. FBase (In m n)))) \<rightarrow>
     foldr (\<lambda>i \<phi>. (\<box>(\<lambda>m. FBase (In m i))) \<rightarrow> \<phi>) [0..<n] (\<box>(\<lambda>m. FBase (In m n)))) 0)"

lemma "Thm (Abs_idx (0, 1)) (\<Psi> 0)"
  by (simp add: Thm_def \<Psi>_def) check_equiv

lemma "Thm (Abs_idx (0, 2)) (\<Psi> 1)"
  by (simp add: Thm_def \<Psi>_def) check_equiv

lemma "Thm (Abs_idx (0, 3)) (\<Psi> 2)"
  by (simp add: Thm_def \<Psi>_def numeral_nat) check_equiv

lemma "Thm (Abs_idx (0, 4)) (\<Psi> 3)"
  by (simp add: Thm_def \<Psi>_def numeral_nat) check_equiv

lemma "Thm (Abs_idx (0, 5)) (\<Psi> 4)"
  by (simp add: Thm_def \<Psi>_def numeral_nat) check_equiv

lemma "Thm (Abs_idx (0, 6)) (\<Psi> 5)"
  by (simp add: Thm_def \<Psi>_def numeral_nat) check_equiv

(*<*)
end
(*>*)
