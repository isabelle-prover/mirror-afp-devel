(* Formalization adapted from: 
   Fabián Fernando Serrano Suárez, "Formalización en Isar de la
   Meta-Lógica de Primer Orden." PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidad de Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish  *)

(*<*)
theory UniformNotation
imports SyntaxAndSemantics
       
begin 
(*>*)



fun FormulaLiteral :: "'b formula \<Rightarrow> bool" where
  "FormulaLiteral FF = True"
| "FormulaLiteral (\<not>. FF) = True"
| "FormulaLiteral TT = True"
| "FormulaLiteral (\<not>. TT) = True"
| "FormulaLiteral (atom P) = True" 
| "FormulaLiteral (\<not>.(atom P)) = True" 
| "FormulaLiteral F = False"



fun FormulaNoNo :: "'b formula \<Rightarrow> bool" where
  "FormulaNoNo (\<not>. (\<not>. F)) = True"
| "FormulaNoNo F = False" 


fun FormulaAlfa :: "'b formula \<Rightarrow> bool" where
  "FormulaAlfa (F \<and>. G) = True"
| "FormulaAlfa (\<not>. (F \<or>. G)) = True"
| "FormulaAlfa (\<not>. (F \<rightarrow>. G)) =  True" 
| "FormulaAlfa F = False"


fun FormulaBeta :: "'b formula \<Rightarrow> bool" where
  "FormulaBeta (F \<or>. G) = True"
| "FormulaBeta (\<not>. (F \<and>. G)) = True"
| "FormulaBeta (F \<rightarrow>. G) =  True" 
| "FormulaBeta F = False"

(*<*)

lemma Literal:
  assumes "FormulaLiteral F"
  shows "F = FF \<or> F = TT \<or> F = (\<not>. FF) \<or> F = (\<not>. TT) \<or> (\<exists>n. F = (atom n) \<or> F = (\<not>. (atom n)))"
using assms 
by (induct F rule: FormulaLiteral.induct, auto) 


lemma NoNo:
  assumes "FormulaNoNo F"
  shows "\<exists>G. F = (\<not>. (\<not>. G))"
using assms
by (induct F rule: FormulaNoNo.induct, auto) 


lemma Alfa:
  assumes "FormulaAlfa F"
  shows "\<exists>G H.  F = (G \<and>. H) \<or> F = (\<not>. (G \<or>. H)) \<or> F = (\<not>. (G \<rightarrow>. H))"
using assms
by (induct F rule: FormulaAlfa.induct, auto) 


lemma Beta:
  assumes "FormulaBeta F"
  shows "\<exists>G H. F = (G \<or>. H) \<or> F = (\<not>. (G \<and>. H)) \<or> F = (G \<rightarrow>. H)"
using assms
by (induct F rule: FormulaBeta.induct, auto) 

(*>*)

lemma noLiteralNoNo:
  assumes "FormulaLiteral formula"
  shows "\<not>(FormulaNoNo formula)"
using assms Literal NoNo  
by (induct formula rule: FormulaLiteral.induct, auto)


lemma noLiteralAlfa:
  assumes "FormulaLiteral formula"
  shows "\<not>(FormulaAlfa formula)"
using assms Literal Alfa
by (induct formula rule: FormulaLiteral.induct, auto)  


lemma noLiteralBeta:
  assumes "FormulaLiteral formula"
  shows "\<not>(FormulaBeta formula)"
using assms Literal Beta  
by (induct formula rule: FormulaLiteral.induct, auto)


lemma noAlfaNoNo:
  assumes "FormulaAlfa formula"
  shows "\<not>(FormulaNoNo formula)"
using assms Alfa NoNo 
by (induct formula rule: FormulaAlfa.induct, auto)


lemma noBetaNoNo:
  assumes "FormulaBeta formula"
  shows "\<not>(FormulaNoNo formula)"
using assms Beta NoNo 
by (induct formula rule: FormulaBeta.induct, auto)


lemma noAlfaBeta:
  assumes "FormulaAlfa formula"
  shows "\<not>(FormulaBeta formula)"
using assms Alfa Beta 
by (induct formula rule: FormulaAlfa.induct, auto)


lemma UniformNotation:
 "FormulaLiteral F \<or> FormulaNoNo F \<or> FormulaAlfa F \<or> FormulaBeta F"
(*<*)
by (induct F rule: FormulaLiteral.induct, 
    induct F rule: FormulaNoNo.induct,
    induct F rule: FormulaAlfa.induct, 
    induct F rule: FormulaBeta.induct,
    induct F, 
    auto)
(*>*)


datatype typeUniformNotation = Literal | NoNo | Alfa| Beta 


fun typeFormula :: "'b formula \<Rightarrow> typeUniformNotation" where
"typeFormula F = 
  (if FormulaBeta F then Beta 
   else if FormulaNoNo F then NoNo
   else if FormulaAlfa F then Alfa
   else Literal)"

(*<*)

lemma typeLiteral: 
  assumes "typeFormula F = Literal"
  shows "FormulaLiteral F"
(*<*)
  by (metis UniformNotation assms 
      typeFormula.simps typeUniformNotation.distinct(1) typeUniformNotation.distinct(3) typeUniformNotation.distinct(5))
(*>*)


lemma typeAlfa:
  assumes "typeFormula F = Alfa"
  shows "FormulaAlfa F"
(*<*)
by (metis UniformNotation 
          assms 
          typeUniformNotation.distinct 
          typeFormula.simps)
(*>*)


lemma typeBeta:
  assumes "typeFormula F = Beta"
  shows "FormulaBeta F"
(*<*)
by (metis UniformNotation 
          assms 
          typeUniformNotation.distinct 
          typeFormula.simps)
(*>*)


lemma typeNoNo:
  assumes "typeFormula F = NoNo"
  shows "FormulaNoNo F"
(*<*)
by (metis UniformNotation 
          assms 
          typeUniformNotation.distinct 
          typeFormula.simps)
(*>*)


lemma UniformNotation1:
  "FormulaLiteral F \<or> FormulaNoNo F \<or> FormulaAlfa F \<or> FormulaBeta F"
using typeLiteral typeNoNo typeAlfa typeBeta typeUniformNotation.exhaust
by blast
(*>*)


fun componentes  :: "'b formula \<Rightarrow> 'b formula list" where 
  "componentes (\<not>. (\<not>. G)) = [G]"
| "componentes (G \<and>. H) = [G, H]"
| "componentes (\<not>. (G \<or>. H)) = [\<not>. G, \<not>. H]"
| "componentes (\<not>. (G \<rightarrow>. H)) = [G, \<not>. H]"
| "componentes (G \<or>. H) = [G, H]"
| "componentes (\<not>. (G \<and>. H)) = [\<not>. G, \<not>. H]"
| "componentes (G \<rightarrow>. H) = [\<not>.G,  H]"


definition Comp1 :: "'b formula \<Rightarrow> 'b formula" where 
  "Comp1 F = hd (componentes F)"


definition Comp2 :: "'b formula \<Rightarrow> 'b formula" where 
  "Comp2 F =  hd (tl (componentes F))"



primrec t_v_evaluationDisyuncionG :: "('b \<Rightarrow> v_truth) \<Rightarrow> ('b formula list) \<Rightarrow> v_truth" where
  "t_v_evaluationDisyuncionG I [] = Ffalse"
| "t_v_evaluationDisyuncionG I (F#Fs) = (if t_v_evaluation I F = Ttrue then Ttrue else t_v_evaluationDisyuncionG I Fs)"


primrec t_v_evaluationConjuncionG :: "('b \<Rightarrow> v_truth) \<Rightarrow> ('b formula list) list \<Rightarrow> v_truth" where
  "t_v_evaluationConjuncionG I [] = Ttrue"
| "t_v_evaluationConjuncionG I (D#Ds) = 
     (if t_v_evaluationDisyuncionG I D = Ffalse then Ffalse else t_v_evaluationConjuncionG I Ds)"


definition equivalentesG :: "('b formula list) list  \<Rightarrow> ('b formula list) list \<Rightarrow> bool" where
 "equivalentesG C1 C2 \<equiv> (\<forall>I. ((t_v_evaluationConjuncionG I C1) = (t_v_evaluationConjuncionG I C2)))" 


(*<*) 
lemma EquiNoNoa: "equivalentesG [[\<not>. \<not>. F]] [[F]]"
proof (unfold equivalentesG_def)
  show "\<forall>I. t_v_evaluationConjuncionG I [[\<not>. \<not>. F]] = t_v_evaluationConjuncionG I [[F]]" 
  proof 
    fix I
    show  "t_v_evaluationConjuncionG I [[\<not>. \<not>. F]] = t_v_evaluationConjuncionG I [[F]]" 
    proof (cases "t_v_evaluation I F")
      text  \<open> Caso 1:  \<close>          
      { assume 1:"t_v_evaluation I F = Ttrue"        
        thus ?thesis by (simp add: v_negation_def) }     
    next
       text  \<open> Caso 2:  \<close> 
      { assume "t_v_evaluation I F = Ffalse"    
        thus ?thesis by (simp add: v_negation_def) }     
    qed 
  qed
qed  
(*>*)


lemma EquiNoNo: 
  assumes "typeFormula F = NoNo" 
  shows "equivalentesG [[F]] [[Comp1 F]]"
(*<*)
proof -
  have 1: "\<exists>G. F = \<not>. \<not>. G" using assms typeNoNo NoNo by auto
  obtain G where "F = \<not>. \<not>. G" using 1 by auto
  moreover
  hence "Comp1 F = G" by(simp add: Comp1_def)
  ultimately
  have "equivalentesG [[F]] [[Comp1 F]] = equivalentesG [[\<not>. \<not>. G]] [[G]]" 
    by simp
  thus ?thesis using EquiNoNoa by simp
qed
(*>*)

(*<*)
lemma EquiAlfaa: "equivalentesG [[G \<and>. H]] [[G],[H]]"
proof (unfold equivalentesG_def)
  show "\<forall>I. t_v_evaluationConjuncionG I [[G \<and>. H]] = t_v_evaluationConjuncionG I [[G], [H]]" 
  proof 
    fix I
    show  "t_v_evaluationConjuncionG I [[G \<and>. H]] = t_v_evaluationConjuncionG I [[G], [H]]" 
    proof (cases "t_v_evaluation I G")
            text  \<open> Caso 1:  \<close> 
      { assume 1:"t_v_evaluation I G = Ttrue"        
        thus ?thesis
        proof(cases "t_v_evaluation I H")
          assume  "t_v_evaluation I H = Ttrue"        
          thus ?thesis using 1  by (simp add: v_conjunction_def)              
        next 
          assume  "t_v_evaluation I H = Ffalse"        
          thus ?thesis using 1  by (simp add: v_conjunction_def)
        qed }
    next
       text  \<open> Caso 2:  \<close> 
      { assume "t_v_evaluation I G = Ffalse"    
        thus ?thesis by (simp add: v_conjunction_def) }     
    qed 
  qed
qed  

lemma EquiAlfab: "equivalentesG [[\<not>. (G \<or>. H)]] [[\<not>. G],[\<not>. H]]"
proof (unfold equivalentesG_def)
  show "\<forall>I. t_v_evaluationConjuncionG I [[\<not>. (G \<or>. H)]] = 
            t_v_evaluationConjuncionG I [[\<not>. G], [\<not>. H]]" 
  proof 
    fix I
    show "t_v_evaluationConjuncionG I [[\<not>. (G \<or>. H)]] = 
          t_v_evaluationConjuncionG I [[\<not>. G], [\<not>. H]]" 
    proof (cases "t_v_evaluation I G")
           text  \<open> Caso 1:  \<close> 
      { assume 1:"t_v_evaluation I G = Ttrue"        
        thus ?thesis
        proof (cases "t_v_evaluation I H")
          assume  "t_v_evaluation I H = Ttrue"        
          thus ?thesis using 1  
            by (simp add: v_negation_def, simp add: v_disjunction_def)
        next 
          assume  "t_v_evaluation I H = Ffalse"        
          thus ?thesis using 1  
            by (simp add: v_negation_def, simp add: v_disjunction_def)
        qed }
    next
        text  \<open> Caso 2:  \<close> 
      { assume "t_v_evaluation I G = Ffalse"    
        thus ?thesis 
          by (simp add: v_negation_def, simp add: v_disjunction_def) }     
    qed 
  qed
qed  

lemma EquiAlfac: "equivalentesG [[\<not>. (G \<rightarrow>. H)]] [[G],[\<not>. H]]"
proof (unfold equivalentesG_def)
  show "\<forall>I. t_v_evaluationConjuncionG I [[\<not>. (G \<rightarrow>. H)]] = 
            t_v_evaluationConjuncionG I [[G], [\<not>. H]]" 
  proof 
    fix I
    show  "t_v_evaluationConjuncionG I [[\<not>. (G \<rightarrow>. H)]] = 
           t_v_evaluationConjuncionG I [[G], [\<not>. H]]" 
    proof (cases "t_v_evaluation I G")
               text  \<open> Caso 1:  \<close> 
      { assume 1:"t_v_evaluation I G = Ttrue"        
        thus ?thesis
        proof(cases "t_v_evaluation I H")
          assume  "t_v_evaluation I H = Ttrue"        
          thus ?thesis using 1  
            by (simp add: v_negation_def, simp add: v_implication_def)
        next 
          assume  "t_v_evaluation I H = Ffalse"        
          thus ?thesis using 1  
            by (simp add: v_negation_def, simp add: v_implication_def)
        qed }
    next
        text  \<open> Caso 2:  \<close> 
      { assume "t_v_evaluation I G = Ffalse"    
        thus ?thesis 
          by (simp add: v_negation_def, simp add: v_implication_def) }     
    qed 
  qed
qed 
(*>*)
 

lemma EquiAlfa:
  assumes "typeFormula F = Alfa" 
  shows "equivalentesG [[F]] [[Comp1 F],[Comp2 F]]"
(*<*)
proof -
  have 1: "\<exists>G H. F = (G \<and>. H) \<or> F = (\<not>. (G \<or>. H)) \<or> F = (\<not>. (G \<rightarrow>. H))" 
    using assms typeAlfa Alfa by auto
  obtain G and H 
    where H: "F = (G \<and>. H) \<or> F = (\<not>. (G \<or>. H)) \<or> F = (\<not>. (G \<rightarrow>. H))" 
    using 1 by auto
  moreover 
  { assume hip: "F = G \<and>. H"  
    hence "Comp1 F = G" and "Comp2 F = H" 
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiAlfaa by simp }
  moreover
  { assume hip:  "F = \<not>. (G \<or>. H)"
    hence "Comp1 F = \<not>. G" and "Comp2 F = \<not>. H" 
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiAlfab by simp }
  moreover
  { assume hip:  "F = \<not>. (G \<rightarrow>. H)"
    hence "Comp1 F = G" and "Comp2 F = \<not>. H" 
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiAlfac by simp }
  ultimately show ?thesis by blast  
qed
(*>*) 

(*<*)
lemma EquiBetaa: "equivalentesG [[G \<or>. H]] [[G, H]]"
proof (unfold equivalentesG_def)
  show "\<forall>I. t_v_evaluationConjuncionG I [[G \<or>. H]] = t_v_evaluationConjuncionG I [[G, H]]" 
  proof 
    fix I
    show  "t_v_evaluationConjuncionG I [[G \<or>. H]] = t_v_evaluationConjuncionG I [[G, H]]" 
    proof (cases "t_v_evaluation I G")
        text  \<open> Caso 1:  \<close> 
      { assume 1:"t_v_evaluation I G = Ttrue"        
        thus ?thesis by (simp add: v_disjunction_def) }    
    next
        text  \<open> Caso 2:  \<close> 
      { assume 2: "t_v_evaluation I G = Ffalse"  
        thus ?thesis
        proof(cases "t_v_evaluation I H")
          assume  "t_v_evaluation I H = Ttrue"        
          thus ?thesis by (simp add: v_disjunction_def)              
        next 
          assume  "t_v_evaluation I H = Ffalse"        
          thus ?thesis using 2 by (simp add: v_disjunction_def)
        qed }
    qed     
  qed
qed  

lemma EquiBetab: "equivalentesG [[\<not>. (G \<and>. H)]] [[\<not>. G, \<not>. H]]"
proof (unfold equivalentesG_def)
  show "\<forall>I. t_v_evaluationConjuncionG I [[\<not>. (G \<and>. H)]] = 
            t_v_evaluationConjuncionG I [[\<not>. G, \<not>. H]]" 
  proof 
    fix I
    show "t_v_evaluationConjuncionG I [[\<not>. (G \<and>. H)]] = 
          t_v_evaluationConjuncionG I [[\<not>. G, \<not>. H]]" 
    proof (cases "t_v_evaluation I G")
             text  \<open> Caso 1:  \<close> 
      { assume 1:"t_v_evaluation I G = Ttrue"        
        thus ?thesis
        proof(cases "t_v_evaluation I H")
          assume  "t_v_evaluation I H = Ttrue"        
          thus ?thesis using 1  
            by (simp add: v_negation_def, simp add: v_conjunction_def)
        next 
          assume  "t_v_evaluation I H = Ffalse"        
          thus ?thesis using 1  
            by (simp add: v_negation_def, simp add: v_conjunction_def)
        qed }
    next
         text  \<open> Caso 2:  \<close> 
      { assume "t_v_evaluation I G = Ffalse"    
        thus ?thesis 
          by (simp add: v_negation_def, simp add: v_conjunction_def) }     
    qed 
  qed
qed  

lemma EquiBetac: "equivalentesG [[G \<rightarrow>. H]] [[\<not>. G, H]]"
proof (unfold equivalentesG_def)
  show "\<forall>I. t_v_evaluationConjuncionG I [[G \<rightarrow>. H]] = t_v_evaluationConjuncionG I [[\<not>. G, H]]" 
  proof 
    fix I
    show  "t_v_evaluationConjuncionG I [[G \<rightarrow>. H]] = t_v_evaluationConjuncionG I [[\<not>. G, H]]" 
    proof (cases "t_v_evaluation I G")
           text  \<open> Caso 1:  \<close> 
      { assume 1:"t_v_evaluation I G = Ttrue"        
        thus ?thesis
        proof(cases "t_v_evaluation I H")
          assume  "t_v_evaluation I H = Ttrue"        
          thus ?thesis using 1  
            by (simp add: v_negation_def, simp add: v_implication_def)
        next 
          assume  "t_v_evaluation I H = Ffalse"        
          thus ?thesis using 1  
            by (simp add: v_negation_def, simp add: v_implication_def)
        qed }
    next
        text  \<open> Caso 2:  \<close> 
      { assume "t_v_evaluation I G = Ffalse"    
        thus ?thesis 
          by (simp add: v_negation_def, simp add: v_implication_def) }     
    qed 
  qed
qed  
(*>*)


lemma EquiBeta:
  assumes "typeFormula F = Beta" 
  shows "equivalentesG [[F]] [[Comp1 F, Comp2 F]]"
(*<*)
proof -
  have 1: "\<exists>G H. F = (G  \<or>. H) \<or> F = (\<not>. (G \<and>. H)) \<or> F = (G \<rightarrow>. H)" 
    using assms typeBeta Beta by blast
  obtain G and H
    where H: "F = (G \<or>. H) \<or> F = (\<not>. (G \<and>. H)) \<or> F =  (G \<rightarrow>. H)" 
    using 1 by auto
  moreover 
  { assume hip: "F = G \<or>. H"  
    hence "Comp1 F = G" and "Comp2 F = H" 
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiBetaa by simp }
  moreover
  { assume hip:  "F = \<not>. (G \<and>. H)"
    hence "Comp1 F = \<not>. G" and "Comp2 F = \<not>. H" 
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiBetab by simp }
  moreover
  { assume hip:  "F = G \<rightarrow>. H"
    hence "Comp1 F = \<not>. G" and "Comp2 F = H" 
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiBetac by simp }  
  ultimately show ?thesis by blast  
qed
(*>*)
 

lemma EquivNoNoComp:
  assumes "typeFormula F = NoNo"
  shows "equivalent F (Comp1 F)"
(*<*)
proof (unfold equivalent_def)
  show "\<forall>I. t_v_evaluation I F = t_v_evaluation I (Comp1 F)"  
  proof (rule allI)+
    fix I
    have "equivalentesG [[F]] [[Comp1 F]]" using EquiNoNo assms by simp 
    hence 1: "t_v_evaluationConjuncionG I [[F]] = t_v_evaluationConjuncionG I [[Comp1 F]]" 
      by (unfold equivalentesG_def, simp)   
    show "t_v_evaluation I F = t_v_evaluation I (Comp1 F)" 
    proof (cases "t_v_evaluation I F")
      assume hip1: "t_v_evaluation I F =  Ttrue"
      hence "t_v_evaluationConjuncionG I [[F]] = Ttrue" by simp
      hence 2: "t_v_evaluationConjuncionG I [[Comp1 F]] = Ttrue" using 1 by simp 
      have "t_v_evaluation I (Comp1 F) = Ttrue" 
      proof -
        { assume "t_v_evaluation I (Comp1 F) \<noteq> Ttrue" 
          hence  "t_v_evaluation I (Comp1 F) = Ffalse" using Bivaluation by auto
          hence "t_v_evaluationConjuncionG I [[Comp1 F]] = Ffalse" by simp
          hence "False" using 2 by simp}
        thus "t_v_evaluation I (Comp1 F) = Ttrue" by auto
      qed
      thus "t_v_evaluation I F = t_v_evaluation I (Comp1 F)" using hip1 by simp
    next
      assume hip2: "t_v_evaluation I F =  Ffalse"
      hence "t_v_evaluationConjuncionG I [[F]] = Ffalse" by simp
      hence 2: "t_v_evaluationConjuncionG I [[Comp1 F]] = Ffalse" using 1 by simp 
      have "t_v_evaluation I (Comp1 F) = Ffalse"  
      proof -
       { assume "t_v_evaluation I (Comp1 F) \<noteq> Ffalse" 
         hence  "t_v_evaluation I (Comp1 F) = Ttrue" using Bivaluation by auto
         hence "t_v_evaluationConjuncionG I [[Comp1 F]] = Ttrue" by simp
         hence "False" using 2 by simp}
       thus "t_v_evaluation I (Comp1 F) = Ffalse" by auto
     qed
     thus "t_v_evaluation I F = t_v_evaluation I (Comp1 F)" using hip2 by simp
   qed
 qed
qed
(*>*)


lemma EquivAlfaComp:
  assumes "typeFormula F = Alfa"
  shows "equivalent F (Comp1 F \<and>. Comp2 F)"
(*<*)
proof(unfold equivalent_def)
  show "\<forall> I. t_v_evaluation I F = t_v_evaluation I (Comp1 F \<and>. Comp2 F)"  
  proof (rule allI)+
    fix I
    have "equivalentesG [[F]] [[Comp1 F], [Comp2 F]]" 
      using EquiAlfa assms by simp 
    hence 1: "t_v_evaluationConjuncionG I [[F]] = 
              t_v_evaluationConjuncionG I [[Comp1 F], [Comp2 F]]"
      by (unfold equivalentesG_def,simp)  
    show "t_v_evaluation I F = t_v_evaluation I (Comp1 F \<and>. Comp2 F)" 
    proof (cases "t_v_evaluation I F")
      assume hip1: "t_v_evaluation I F =  Ttrue"
      have "t_v_evaluation I (Comp1 F \<and>. Comp2 F) = Ttrue" 
      proof -
        have "t_v_evaluationConjuncionG I [[F]] = Ttrue" using hip1 by simp 
        hence 2:"t_v_evaluationConjuncionG I [[Comp1 F], [Comp2 F]] = Ttrue"  
          using 1 by simp
        have 3: "t_v_evaluation I (Comp1 F) = Ttrue" 
        proof -
         { assume "t_v_evaluation I (Comp1 F) = Ffalse"
           hence "t_v_evaluationConjuncionG I [[Comp1 F], [Comp2 F]] = Ffalse" by simp
           hence "False" using 2 by simp}
         hence "t_v_evaluation I (Comp1 F) \<noteq> Ffalse" by auto
         thus "t_v_evaluation I (Comp1 F) = Ttrue" using Bivaluation by auto
       qed
       have "t_v_evaluation I (Comp2 F) = Ttrue" 
       proof -
         { assume "t_v_evaluation I (Comp2 F) = Ffalse"
           hence "t_v_evaluationConjuncionG I [[Comp1 F], [Comp2 F]] = Ffalse" by simp
           hence "False" using 2 by simp}
         hence "t_v_evaluation I (Comp2 F) \<noteq> Ffalse" by auto
         thus "t_v_evaluation I (Comp2 F) = Ttrue" using Bivaluation by auto
       qed    
       thus "t_v_evaluation I (Comp1 F \<and>. Comp2 F) = Ttrue" using 3 
         by (auto, unfold v_conjunction_def, simp)
     qed
     thus "t_v_evaluation I F = t_v_evaluation I (Comp1 F \<and>. Comp2 F)" using hip1 by simp
   next
     assume hip2: "t_v_evaluation I F = Ffalse"
     show "t_v_evaluation I F = t_v_evaluation I (Comp1 F \<and>. Comp2 F)"  
     proof - 
       have  "t_v_evaluation I (Comp1 F \<and>. Comp2 F) = Ffalse" 
       proof -
         have "t_v_evaluationConjuncionG I [[F]] = Ffalse" using hip2 by simp 
         hence 4: "t_v_evaluationConjuncionG I [[Comp1 F], [Comp2 F]] = Ffalse"  
           using 1 by simp
         have "t_v_evaluation I (Comp1 F) = Ffalse \<or> t_v_evaluation I (Comp2 F) = Ffalse" 
         proof -
           { assume "\<not>(t_v_evaluation I (Comp1 F) = Ffalse \<or> 
                       t_v_evaluation I (Comp2 F) = Ffalse)"
             hence "(t_v_evaluation I (Comp1 F) \<noteq> Ffalse \<and> 
                     t_v_evaluation I (Comp2 F) \<noteq> Ffalse)" 
               by simp
             hence  "(t_v_evaluation I (Comp1 F) = Ttrue \<and>  
                      t_v_evaluation I (Comp2 F) = Ttrue)" 
               using Bivaluation by auto          
             hence "t_v_evaluation I (Comp1 F) = Ttrue" and 
               "t_v_evaluation I (Comp2 F) = Ttrue" 
               by auto       
             hence  "t_v_evaluationConjuncionG I [[Comp1 F], [Comp2 F]] = Ttrue" by auto
             hence "False" using 4 by auto}
           thus "t_v_evaluation I (Comp1 F) = Ffalse \<or> t_v_evaluation I (Comp2 F) = Ffalse" 
             by auto 
         qed
         thus "t_v_evaluation I (Comp1 F \<and>. Comp2 F) = Ffalse" 
           by (auto, unfold v_conjunction_def, auto)
       qed     
       thus "t_v_evaluation I F = t_v_evaluation I (Comp1 F \<and>. Comp2 F)" using hip2 by simp
     qed
   qed
 qed
qed
(*>*)


lemma EquivBetaComp:
  assumes "typeFormula F = Beta"
  shows "equivalent F (Comp1 F \<or>. Comp2 F)"
(*<*)
proof (unfold equivalent_def)
  show "\<forall> I. t_v_evaluation I F = t_v_evaluation I (Comp1 F \<or>. Comp2 F)"  
  proof(rule allI)+
    fix I
    have "equivalentesG [[F]] [[Comp1 F, Comp2 F]]" 
      using EquiBeta assms by simp 
    hence 1: "t_v_evaluationConjuncionG I [[F]] = 
              t_v_evaluationConjuncionG I [[Comp1 F, Comp2 F]]" 
      by (unfold equivalentesG_def,simp)   
    show "t_v_evaluation I F = t_v_evaluation I (Comp1 F \<or>. Comp2 F)"
    proof (cases "t_v_evaluation I F")
      assume hip1: "t_v_evaluation I F =  Ttrue"
      have "t_v_evaluation I (Comp1 F \<or>. Comp2 F) = Ttrue" 
      proof -
        have "t_v_evaluationConjuncionG I [[F]] = Ttrue" using hip1 by simp 
        hence 2:"t_v_evaluationConjuncionG I [[Comp1 F, Comp2 F]] = Ttrue"  
          using 1 by simp
        hence "(t_v_evaluation I (Comp1 F) = Ttrue) \<or> (t_v_evaluation I (Comp2 F) = Ttrue)" 
        proof -
         { assume  "\<not>((t_v_evaluation I (Comp1 F) = Ttrue) \<or> 
                      (t_v_evaluation I (Comp2 F) = Ttrue))"
           hence  "(t_v_evaluation I (Comp1 F) \<noteq> Ttrue \<and> 
                    t_v_evaluation I (Comp2 F) \<noteq> Ttrue)" 
            by simp
          hence  "(t_v_evaluation I (Comp1 F) = Ffalse \<and>  
                   t_v_evaluation I (Comp2 F) = Ffalse)" 
            using Bivaluation by auto                 
          hence  "t_v_evaluationConjuncionG I [[Comp1 F, Comp2 F]] = Ffalse" by auto
          hence "False" using 2 by auto}
          thus "(t_v_evaluation I (Comp1 F) = Ttrue) \<or> (t_v_evaluation I (Comp2 F) = Ttrue)" 
            by auto
        qed
        thus "t_v_evaluation I (Comp1 F \<or>. Comp2 F) = Ttrue" 
          by (auto, unfold v_disjunction_def, auto)
      qed     
      thus "t_v_evaluation I F = t_v_evaluation I (Comp1 F \<or>. Comp2 F)" using hip1 by simp
    next
      assume hip2: "t_v_evaluation I F =  Ffalse"
      have "t_v_evaluation I (Comp1 F \<or>. Comp2 F) = Ffalse" 
      proof -
        have "t_v_evaluationConjuncionG I [[F]] = Ffalse" using hip2 by simp 
        hence 3:"t_v_evaluationConjuncionG I [[Comp1 F, Comp2 F]] = Ffalse"  
          using 1 by simp
        have  4:"t_v_evaluation I (Comp1 F) = Ffalse" 
        proof -
         { assume "t_v_evaluation I (Comp1 F) = Ttrue"
           hence "t_v_evaluationConjuncionG I [[Comp1 F, Comp2 F]] = Ttrue" by simp
           hence "False" using 3 by simp}
         hence "t_v_evaluation I (Comp1 F) \<noteq> Ttrue" by auto
         thus "t_v_evaluation I (Comp1 F) = Ffalse" using Bivaluation by auto
       qed
       have "t_v_evaluation I (Comp2 F) = Ffalse" 
       proof -
         { assume "t_v_evaluation I (Comp2 F) = Ttrue"
           hence "t_v_evaluationConjuncionG I [[Comp1 F, Comp2 F]] = Ttrue" by simp
           hence "False" using 3 by simp}
         hence "t_v_evaluation I (Comp2 F) \<noteq> Ttrue" by auto
         thus "t_v_evaluation I (Comp2 F) = Ffalse" using Bivaluation by auto
       qed    
       thus "t_v_evaluation I (Comp1 F \<or>. Comp2 F) = Ffalse" using 4  
         by (auto, unfold v_disjunction_def, simp)
     qed
     thus "t_v_evaluation I F = t_v_evaluation I (Comp1 F \<or>. Comp2 F)" using hip2 by simp
   qed 
 qed
qed

(*>*)

(*<*)
end
(*>*)
