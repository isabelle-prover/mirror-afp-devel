section \<open>Examples for Nameful WS1S Formulas\<close>

(*<*)
theory WS1S_Nameful_Examples
imports WS1S_Nameful "../Show/Show_Instances"
begin
(*>*)

export_code eqv checking SML

lift_definition x :: fo is "''x''" by simp
lift_definition y :: fo is "''y''" by simp
lift_definition z :: fo is "''z''" by simp
lift_definition X :: so is "''X''" by simp
lift_definition Y :: so is "''Y''" by simp
lift_definition Z :: so is "''Z''" by simp
lift_definition Xi :: "nat \<Rightarrow> so" is "\<lambda>i. ''X'' @ show i" by simp

abbreviation Imp where "Imp \<phi> \<psi> \<equiv> Or (Not \<phi>) \<psi>"
(*true in M2L, false in WS1S*)
definition "M2L = Ex2 X (All1 x (In x X))"
(*false in M2L, true in WS1S*)
definition "\<Phi> = All1 x (Ex1 y (Lt x y))"

abbreviation Globally ("\<box>_" [40] 40) where
 "Globally P t ==  All1 z (Imp (Not (Lt t z)) (P z))"
abbreviation Future ("\<diamond>_" [40] 40) where
  "Future P t == Ex1 z (And (Not (Lt t z)) (P z))"
abbreviation IMP (infixr "\<rightarrow>" 50) where "IMP P1 P2 t == Imp (P1 t) (P2 t)"

definition \<Psi> :: "nat \<Rightarrow> ws1s" where
  "\<Psi> n = All1 x
     (((\<box>(foldr (\<lambda>i \<phi>. (\<lambda>m. In m (Xi i)) \<rightarrow> \<phi>) [0..<n] (\<lambda>m. (In m (Xi n))))) \<rightarrow>
     foldr (\<lambda>i \<phi>. (\<box>(\<lambda>m. (In m (Xi i)))) \<rightarrow> \<phi>) [0..<n]
       (\<box>(\<lambda>m. (In m (Xi n))))) x)"

declare check_eqv_code[code del] (*use code_reflect hack*)

lemma "Thm (Not M2L)" by eval
lemma "Thm \<Phi>" by eval
lemma "eqv (And (Eq_Const x 10) (Eq_Const x 10000)) F" by eval

lemma "Thm (\<Psi> 0)" by eval
lemma "Thm (\<Psi> 1)" by eval
lemma "Thm (\<Psi> 2)" by eval
lemma "Thm (\<Psi> 3)" by eval
lemma "Thm (\<Psi> 4)" by eval
lemma "Thm (\<Psi> 5)" by eval
lemma "Thm (\<Psi> 10)" by eval
lemma "Thm (\<Psi> 15)" by eval

(*<*)
end
(*>*)