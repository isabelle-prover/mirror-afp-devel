(* Formalization adapted from: 
   Fabián Fernando Serrano Suárez, "Formalización en Isar de la
   Meta-Lógica de Primer Orden." PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidad de Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish 
   Last modified: 11 Aug, 2025.
 *)


theory UniformNotation
imports SyntaxAndSemantics
begin       

fun FormulaLiteral :: "'b formula \<Rightarrow> bool" where
  "FormulaLiteral \<bottom>. = True"
| "FormulaLiteral (\<not>. \<bottom>.) = True"
| "FormulaLiteral \<top>. = True"
| "FormulaLiteral (\<not>. \<top>.) = True"
| "FormulaLiteral (atom P) = True" 
| "FormulaLiteral (\<not>.(atom P)) = True" 
| "FormulaLiteral F = False"

fun FormulaNegNeg :: "'b formula \<Rightarrow> bool" where
  "FormulaNegNeg (\<not>. (\<not>. F)) = True"
| "FormulaNegNeg F = False" 

fun FormulaAlpha :: "'b formula \<Rightarrow> bool" where
  "FormulaAlpha (F \<and>. G) = True"
| "FormulaAlpha (\<not>. (F \<or>. G)) = True"
| "FormulaAlpha (\<not>. (F \<rightarrow>. G)) =  True" 
| "FormulaAlpha F = False"

fun FormulaBeta :: "'b formula \<Rightarrow> bool" where
  "FormulaBeta (F \<or>. G) = True"
| "FormulaBeta (\<not>. (F \<and>. G)) = True"
| "FormulaBeta (F \<rightarrow>. G) =  True" 
| "FormulaBeta F = False"

lemma Literal:
  assumes "FormulaLiteral F"
  shows "F = \<bottom>. \<or> F = \<top>. \<or> F = (\<not>. \<bottom>.) \<or> F = (\<not>. \<top>.) \<or> (\<exists>n. F = (atom n) \<or> F = (\<not>. (atom n)))"
using assms 
by (induct F rule: FormulaLiteral.induct, auto) 

lemma NegNeg:
  assumes "FormulaNegNeg F"
  shows "\<exists>G. F = (\<not>. (\<not>. G))"
using assms
by (induct F rule: FormulaNegNeg.induct, auto) 

lemma Alpha:
  assumes "FormulaAlpha F"
  shows "\<exists>G H.  F = (G \<and>. H) \<or> F = (\<not>. (G \<or>. H)) \<or> F = (\<not>. (G \<rightarrow>. H))"
using assms
by (induct F rule: FormulaAlpha.induct, auto) 

lemma Beta:
  assumes "FormulaBeta F"
  shows "\<exists>G H. F = (G \<or>. H) \<or> F = (\<not>. (G \<and>. H)) \<or> F = (G \<rightarrow>. H)"
using assms
by (induct F rule: FormulaBeta.induct, auto) 

lemma noLiteralNegNeg:
  assumes "FormulaLiteral formula"
  shows "\<not>(FormulaNegNeg formula)"
using assms Literal NegNeg  
by (induct formula rule: FormulaLiteral.induct, auto)


lemma noLiteralAlpha:
  assumes "FormulaLiteral formula"
  shows "\<not>(FormulaAlpha formula)"
using assms Literal Alpha
by (induct formula rule: FormulaLiteral.induct, auto)  


lemma noLiteralBeta:
  assumes "FormulaLiteral formula"
  shows "\<not>(FormulaBeta formula)"
using assms Literal Beta  
by (induct formula rule: FormulaLiteral.induct, auto)


lemma noAlphaNegNeg:
  assumes "FormulaAlpha formula"
  shows "\<not>(FormulaNegNeg formula)"
using assms Alpha NegNeg 
by (induct formula rule: FormulaAlpha.induct, auto)


lemma noBetaNegNeg:
  assumes "FormulaBeta formula"
  shows "\<not>(FormulaNegNeg formula)"
using assms Beta NegNeg 
by (induct formula rule: FormulaBeta.induct, auto)


lemma noAlphaBeta:
  assumes "FormulaAlpha formula"
  shows "\<not>(FormulaBeta formula)"
using assms Alpha Beta 
by (induct formula rule: FormulaAlpha.induct, auto)

fun components  :: "'b formula \<Rightarrow> 'b formula list" where 
  "components \<bottom>. = []"
| "components \<top>. = []"
| "components (\<not>. \<bottom>.) =[]"
| "components (\<not>. \<top>.) =[]"
| "components (atom p) =[]"
| "components (\<not>.(atom p)) =[]"
| "components (\<not>. (\<not>. G)) = [G]"
| "components (G \<and>. H) = [G, H]"
| "components (\<not>. (G \<or>. H)) = [\<not>. G, \<not>. H]"
| "components (\<not>. (G \<rightarrow>. H)) = [G, \<not>. H]"
| "components (G \<or>. H) = [G, H]"
| "components (\<not>. (G \<and>. H)) = [\<not>. G, \<not>. H]"
| "components (G \<rightarrow>. H) = [\<not>.G,  H]"

definition Comp1 :: "'b formula \<Rightarrow> 'b formula" where 
  "Comp1 F = hd (components F)"

definition Comp2 :: "'b formula \<Rightarrow> 'b formula" where 
  "Comp2 F =  hd (tl (components F))"

primrec t_v_evaluationDisjunctionG :: "('b \<Rightarrow> bool) \<Rightarrow> ('b formula list) \<Rightarrow> bool" where
  "t_v_evaluationDisjunctionG I [] = False"
| "t_v_evaluationDisjunctionG I (F#Fs) = (if t_v_evaluation I F = True 
   then True else t_v_evaluationDisjunctionG I Fs)"

primrec t_v_evaluationConjunctionG :: "('b \<Rightarrow> bool) \<Rightarrow> ('b formula list) list \<Rightarrow> bool " where
  "t_v_evaluationConjunctionG I [] = True"
| "t_v_evaluationConjunctionG I (D#Ds) = 
     (if t_v_evaluationDisjunctionG I D = False then False else t_v_evaluationConjunctionG I Ds)"

definition equivalentG :: "('b formula list) list  \<Rightarrow> ('b formula list) list \<Rightarrow> bool" where
 "equivalentG C1 C2 \<equiv> (\<forall>I. ((t_v_evaluationConjunctionG I C1) = (t_v_evaluationConjunctionG I C2)))" 

lemma EquivImpliesEquivG :
  assumes "equivalent F G"
  shows "equivalentG [[F]] [[G]]"
  using assms unfolding equivalentG_def equivalent_def by simp

lemma DoubleNegationEquiv : "equivalent (\<not>. \<not>. F) F"  
  unfolding equivalent_def by auto

lemma EquiNegNeg: 
  assumes "FormulaNegNeg F" 
  shows "equivalent F (Comp1 F)"
  using NegNeg[OF assms] DoubleNegationEquiv
  unfolding Comp1_def
  using equivalent_def by auto

lemma EquiAlphab1: "equivalent (\<not>. (G \<or>. H)) (\<not>. G \<and>. \<not>. H)" 
  unfolding equivalent_def by simp

lemma EquiAlphab2: "equivalent (\<not>. (G \<rightarrow>. H)) (G \<and>. \<not>. H)"
    unfolding equivalent_def by simp

lemma EquivAlpha:
  assumes "FormulaAlpha F"
  shows "equivalent F (Comp1 F \<and>. Comp2 F)"
  using Alpha[OF assms]  EquiAlphab1  EquiAlphab2 
  unfolding Comp1_def Comp2_def
  using equivalent_def by fastforce

lemma EquiBetaa: "equivalent (\<not>.(G \<and>. H)) (\<not>.G \<or>. \<not>.H)" 
  unfolding equivalent_def by simp

lemma EquiBetab: "equivalent (G \<rightarrow>. H) (\<not>. G \<or>. H)" 
  unfolding equivalent_def by simp

lemma EquivBetaComp: 
  assumes "FormulaBeta F"
  shows "equivalent F (Comp1 F \<or>. Comp2 F)"
  using Beta[OF assms] EquiBetaa  EquiBetab 
  unfolding Comp1_def Comp2_def 
  using equivalent_def by fastforce

end