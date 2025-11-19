(* Formalization adapted from: 
   Fabián Fernando Serrano Suárez, "Formalización en Isar de la
   Meta-Lógica de Primer Orden." PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidad de Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish 
   Last modified: 29 Sep, 2025 *)

theory PropCompactness

imports Main 
"HOL-Library.Countable_Set"
"ModelExistence" 

begin

section    \<open>Compactness Theorem for Propositional Logic  \<close>

text   \<open>This theory formalises the compactness theorem based on the existence model theorem.  The formalisation, initially published as \cite{Serrano2011} in Spanish, was adapted to extend several combinatorial theorems over finite structures to the infinite case (e.g., see Serrano, Ayala-Rincón, and de Lima formalizations of Hall's Theorem for infinite families of sets and infinite graphs \cite{SARdL2022,SARdL2024}.)  

The formalization shows first Hintikka's Lemma: Hintikka sets of propositional formulas are satisfiable. Such a set is defined as a set of propositional formulas that does neither include both $A$ and $\neg A$ for a propositional letter nor $\bot$, or $\neg\top$. Additionally, if it includes $\neg\neg F$, $F$ is included; if it includes a conjunctive formula, which is an $\alpha$ formula, then the two components of the conjunction are included; and finally, if it includes a disjunction, which is a $\beta$ formula, at least one of the components of the disjunction is included. 

The satisfiability of any Hintikka set is proved by assuming a valuation that maps all propositional letters in the set to true and all other propositional letters to false.  The second step consists in proving that families of sets of propositional formulas, which hold the so-called ``propositional consistency property,'' consist of satisfiable sets. The last is indeed the model existence theorem. The model existence theorem compiles the essence of completeness: a family of sets of propositional formulas that holds the propositional consistency property can be extended, preserving this property to a set collection that is closed for subsets and satisfies the finite character property. The finite character property states that a set belongs to the family if and only if each of its finite subsets belongs to the family. With the model existence theorem in hands, the compactness theorem is obtained easily:  given a set of propositional formulas $S$ such that all its finite subsets are satisfiable, one considers the family $\cal C$ of subsets in $S$ such that all their finite subsets are satisfiable.  $S$ belongs to the family $\cal C$ and the latter holds the propositional consistence property.  

The auxiliary lemma of Consistence Compactness is required to apply the Model Existence Theorem to obtain the compactness theorem. This lemma states the general fact that the collection $\mathcal{C}$ of all sets of propositional formulas such that all their subsets are satisfiable is a propositional consistency property.  
\<close>
lemma UnsatisfiableAtom:
  shows "\<not> (satisfiable {F, \<not>.F})"
proof (rule notI)
  assume hip: "satisfiable {F, \<not>.F}" 
  show "False"
  proof -
    have  "\<exists>I. I model {F, \<not>.F}" using hip by(unfold satisfiable_def, auto) 
    then obtain I where I: "(t_v_evaluation I F)" and "(t_v_evaluation I (\<not>.F))"  
      by(unfold model_def, auto)
    thus "False" by auto
  qed
qed
 

lemma consistenceP_Prop1:
  assumes "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A"
  shows "(\<forall>P. \<not> (Atom P \<in> W \<and> (\<not>. Atom P) \<in> W))"
proof (rule allI notI)+
  fix P
  assume h1: "Atom P \<in> W \<and> (\<not>.Atom P) \<in> W"
  show "False"
  proof - 
    have "{Atom P, (\<not>.Atom P)} \<subseteq> W" using h1 by simp 
    moreover
    have "finite {Atom P, (\<not>.Atom P)}" by simp  
    ultimately
    have "{Atom P, (\<not>.Atom P)} \<subseteq> W \<and> finite {Atom P, (\<not>.Atom P)}" by simp  
    thus "False" using UnsatisfiableAtom assms
      by metis
  qed
qed

lemma UnsatisfiableFF:
  shows "\<not> (satisfiable {\<bottom>.})"
proof -
  have "\<not>(\<forall> I. t_v_evaluation I \<bottom>.)" by simp
  hence "\<forall> I. \<not> (I model {\<bottom>.})"  by(unfold model_def, auto) 
  thus ?thesis by(unfold satisfiable_def, auto)
qed

lemma consistenceP_Prop2:
  assumes "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A"
  shows "\<bottom>. \<notin> W"
proof (rule notI)
  assume hip: "\<bottom>. \<in> W"
  show "False"
  proof -
    have "{\<bottom>.} \<subseteq> W" using hip by simp 
    moreover
    have "finite {\<bottom>.}" by simp  
    ultimately
    have "{\<bottom>.} \<subseteq> W \<and> finite {\<bottom>.}" by simp  
    moreover
    have "({\<bottom>.::'b formula} \<subseteq> W \<and> finite {\<bottom>.}) \<longrightarrow> satisfiable {\<bottom>.::'b formula}" 
      using assms by auto
    ultimately show "False" using UnsatisfiableFF by auto
  qed
qed  

lemma Unsatisfiable1:
  shows "\<not> (satisfiable {\<not>.\<top>.})"
proof -
  have "\<forall> I. t_v_evaluation I \<top>. = True" by simp  
  have "\<not>(\<forall> I. t_v_evaluation I (\<not>.\<top>.))" by auto
  hence "\<forall> I. \<not> (I model {\<not>.\<top>.})"  by(unfold model_def, auto) 
  thus ?thesis by(unfold satisfiable_def, auto)
qed

lemma consistenceP_Prop3:
  assumes "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A"
  shows "\<not>.\<top>. \<notin> W"
proof (rule notI)
  assume hip: "\<not>.\<top>. \<in> W"
  show "False"
  proof -
    have "{\<not>.\<top>.} \<subseteq> W" using hip by simp 
    moreover
    have "finite {\<not>.\<top>.}" by simp  
    ultimately
    have "{\<not>.\<top>.} \<subseteq> W \<and> finite {\<not>.\<top>.}" by simp  
    moreover
    have "({\<not>.\<top>.::'b formula} \<subseteq> W \<and> finite {\<not>.\<top>.}) \<longrightarrow> 
          satisfiable {\<not>.\<top>.::'b formula}" 
      using assms by auto
    thus "False" using Unsatisfiable1
      using \<open>{\<not>.\<top>.} \<subseteq> W\<close> by auto
  qed
qed

lemma Subset_Sat:
  assumes hip1: "satisfiable S" and hip2: "S'\<subseteq> S"
  shows "satisfiable S'"
  using assms satisfiable_subset by blast

text\<open> \<close>
lemma satisfiableUnion1:
  assumes "satisfiable (A \<union> {\<not>.\<not>.F})" 
  shows "satisfiable (A \<union> {F})"
proof -
  have "\<exists>I. \<forall> G \<in> (A \<union> {\<not>.\<not>.F}). t_v_evaluation I G = True"  
    using assms by(unfold satisfiable_def, unfold model_def, auto)
  then obtain I where I: "\<forall> G \<in> (A \<union> {\<not>.\<not>.F}). t_v_evaluation I G = True" 
    by auto      
  hence 1: "\<forall> G \<in> A. t_v_evaluation I G = True" 
    and 2: "t_v_evaluation I (\<not>.\<not>.F) = True" 
    by auto        
  hence "\<forall> G \<in> A \<union> {F}. t_v_evaluation I G = True" using 1 by auto  
  thus "satisfiable (A \<union> {F})" 
    by(unfold satisfiable_def, unfold model_def, auto)
qed

lemma consistenceP_Prop4:
  assumes hip1: "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A" 
  and hip2: "\<not>.\<not>.F \<in> W"
  shows "\<forall> (A::'b formula set). (A\<subseteq> W \<union> {F} \<and> finite A) \<longrightarrow> satisfiable A"
proof (rule allI, rule impI)+
  fix A
  assume hip: "A \<subseteq> W \<union> {F} \<and> finite A"
  show "satisfiable A"
  proof -
    have "A-{F} \<subseteq> W \<and> finite (A-{F})" using hip by auto
    hence "(A-{F}) \<union> {\<not>.\<not>.F} \<subseteq> W \<and> finite ((A-{F}) \<union> {\<not>.\<not>.F})" 
      using hip2 by auto  
    hence "satisfiable ((A-{F}) \<union> {\<not>.\<not>.F})" using hip1 by auto
    hence "satisfiable ((A-{F}) \<union> {F})" using  satisfiableUnion1 by blast
    moreover
    have "A\<subseteq> (A-{F}) \<union> {F}" by auto
    ultimately
    show "satisfiable A" using Subset_Sat by auto
  qed
qed

lemma satisfiableUnion2:
  assumes hip1: "FormulaAlpha F" and hip2: "satisfiable (A \<union> {F})" 
  shows "satisfiable (A \<union> {Comp1 F,Comp2 F})"
proof -   
  have "\<exists>I.\<forall> G \<in> A \<union> {F}. t_v_evaluation I G = True"  
    using hip2 by(unfold satisfiable_def, unfold model_def, auto)
  then obtain I where I:  "\<forall> G \<in> A \<union> {F}. t_v_evaluation I G" by auto      
  hence 1: "\<forall> G \<in> A. t_v_evaluation I G" and 2: "t_v_evaluation I F" by auto
  hence  "t_v_evaluation I (Comp1 F \<and>. Comp2 F)"
    using EquivAlpha equivalent_def hip1 by blast  
  hence "t_v_evaluation I (Comp1 F) \<and> t_v_evaluation I (Comp2 F)" by auto 
  hence "\<forall> G \<in> A \<union> {Comp1 F, Comp2 F} . t_v_evaluation I G" using 1 by auto
  thus "satisfiable (A \<union> {Comp1 F,Comp2 F})" 
    by (unfold satisfiable_def, unfold model_def, auto)
qed

lemma consistenceP_Prop5:
  assumes hip0: "FormulaAlpha F" 
  and hip1: "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A" 
  and hip2: "F \<in> W"
  shows "\<forall> (A::'b formula set). (A\<subseteq> W \<union> {Comp1 F, Comp2 F} \<and> finite A) \<longrightarrow> 
  satisfiable A"
proof (intro allI impI)
  fix A
  assume hip: "A \<subseteq> W \<union> {Comp1 F, Comp2 F} \<and> finite A"
  show "satisfiable A"
  proof -
    have "A-{Comp1 F, Comp2 F} \<subseteq> W \<and> finite (A-{Comp1 F, Comp2 F})" 
      using hip by auto
    hence "(A-{Comp1 F, Comp2 F}) \<union> {F} \<subseteq> W \<and> 
           finite ((A-{Comp1 F, Comp2 F}) \<union> {F})" 
      using hip2 by auto  
    hence "satisfiable ((A-{Comp1 F, Comp2 F}) \<union> {F})" 
      using hip1 by auto
    hence "satisfiable ((A-{Comp1 F, Comp2 F}) \<union> {Comp1 F, Comp2 F})"
      using hip0 satisfiableUnion2 by auto
    moreover
    have  "A \<subseteq> (A-{Comp1 F, Comp2 F}) \<union> {Comp1 F, Comp2 F}" by auto
    ultimately
    show "satisfiable A" using Subset_Sat by auto
  qed
qed

lemma satisfiableUnion3:
  assumes hip1: "FormulaBeta F" and hip2: "satisfiable (A \<union> {F})" 
  shows "satisfiable (A \<union> {Comp1 F}) \<or> satisfiable (A \<union> {Comp2 F})" 
proof - 
  obtain I where I: "\<forall>G \<in> (A \<union> {F}). t_v_evaluation I G"
  using hip2 by(unfold satisfiable_def, unfold model_def, auto) 
  hence S1: "\<forall>G \<in> A. t_v_evaluation I G" 
    and S2: " t_v_evaluation I F" 
    by auto
  have V: "t_v_evaluation I (Comp1 F) \<or> t_v_evaluation I (Comp2 F)"
    by (metis EquivBetaComp S2 equivalent_def hip1 t_v_evaluation.simps(6))       
  have "((\<forall>G \<in> A. t_v_evaluation I G) \<and> t_v_evaluation I (Comp1 F)) \<or>
        ((\<forall>G \<in> A. t_v_evaluation I G ) \<and> t_v_evaluation I (Comp2 F))" 
    using V S1 by blast
  thus "satisfiable (A \<union> {Comp1 F}) \<or> satisfiable (A \<union> {Comp2 F})"
    by (unfold satisfiable_def, unfold model_def, auto)
qed

lemma consistenceP_Prop6:
  assumes hip0: "FormulaBeta F" 
  and hip1: "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A" 
  and hip2: "F \<in> W"
  shows "(\<forall> (A::'b formula set). (A\<subseteq> W \<union> {Comp1 F} \<and> finite A) \<longrightarrow> 
  satisfiable A) \<or>
  (\<forall> (A::'b formula set). (A\<subseteq> W \<union> {Comp2 F} \<and> finite A) \<longrightarrow> 
  satisfiable A)"
proof -
  { assume hip3:"\<not>((\<forall> (A::'b formula set). (A\<subseteq> W \<union> {Comp1 F} \<and> finite A) \<longrightarrow> 
    satisfiable A) \<or>
    (\<forall> (A::'b formula set). (A\<subseteq> W \<union> {Comp2 F} \<and> finite A) \<longrightarrow> 
    satisfiable A))" 
    have "False"
    proof - 
      obtain A B where A1: "A \<subseteq> W \<union> {Comp1 F}" 
        and A2: "finite A" 
        and A3:" \<not> satisfiable A" 
        and B1: "B \<subseteq> W \<union> {Comp2 F}" 
        and B2: "finite B" 
        and B3: "\<not> satisfiable B" 
        using hip3 by auto     
      have a1: "A - {Comp1 F} \<subseteq> W" 
        and a2: "finite (A - {Comp1 F})" 
        using A1 and A2 by auto
      hence "satisfiable (A - {Comp1 F})" using hip1 by simp  
      have b1: "B - {Comp2 F} \<subseteq> W" 
        and b2: "finite (B - {Comp2 F})" 
        using B1 and B2 by auto
      hence "satisfiable (B - {Comp2 F})" using hip1 by simp
      moreover
      have "(A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {F} \<subseteq> W" 
        and "finite ((A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {F})"
        using a1 a2 b1 b2 hip2 by auto
      hence "satisfiable ((A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {F})" 
        using hip1 by simp
      hence "satisfiable ((A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {Comp1 F})
      \<or> satisfiable ((A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {Comp2 F})"
        using hip0 satisfiableUnion3 by auto  
      moreover
      have "A \<subseteq> (A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {Comp1 F}" 
        and "B \<subseteq> (A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {Comp2 F}" 
        by auto
      ultimately
      have "satisfiable A \<or> satisfiable B" using Subset_Sat by auto
      thus "False" using A3 B3 by simp
    qed } 
  thus ?thesis by auto
qed

lemma ConsistenceCompactness1:   
  shows "consistenceP{W::'b formula set. \<forall>A. (A\<subseteq> W \<and> finite A) \<longrightarrow> 
  satisfiable A}"
proof (unfold consistenceP_def, rule allI, rule impI)  
  let ?C = "{W::'b formula set.  \<forall>A. (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A}"
  fix W ::" 'b formula set"  
  assume "W \<in> ?C"  
  hence  hip: "\<forall>A. (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A" by simp
  show "(\<forall>P. \<not> (atom P \<in> W \<and> (\<not>.atom P ) \<in> W)) \<and>
        FF \<notin> W \<and>
        \<not>.\<top>. \<notin> W \<and>
        (\<forall>F. \<not>.\<not>.F \<in> W \<longrightarrow> W \<union> {F} \<in> ?C) \<and>
        (\<forall>F. (FormulaAlpha F) \<and> F \<in> W \<longrightarrow> 
        (W \<union>  {Comp1 F, Comp2 F} \<in> ?C)) \<and>
        (\<forall>F. (FormulaBeta F) \<and> F \<in> W \<longrightarrow> 
        (W \<union> {Comp1 F} \<in> ?C \<or> W \<union> {Comp2 F} \<in> ?C))"
  proof -   
    have "(\<forall>P. \<not> (atom P \<in> W \<and> (\<not>. atom P) \<in> W))" 
      using hip  consistenceP_Prop1 by simp
    moreover
    have "FF \<notin> W" using hip consistenceP_Prop2 by auto
    moreover 
    have "\<not>. \<top>. \<notin> W" using hip consistenceP_Prop3 by auto
    moreover
    have "\<forall>F. (\<not>.\<not>.F) \<in> W \<longrightarrow> W \<union> {F} \<in> ?C"
    proof (rule allI impI)+
      fix F
      assume hip1: "\<not>.\<not>.F \<in> W"    
      show "W \<union> {F} \<in> ?C" using hip hip1 consistenceP_Prop4 by simp
    qed
    moreover
    have
    "\<forall>F. (FormulaAlpha F) \<and> F \<in> W \<longrightarrow> (W \<union>  {Comp1 F, Comp2 F} \<in> ?C)" 
    proof (rule allI impI)+
      fix F 
      assume "FormulaAlpha F \<and> F \<in> W"      
      thus "W \<union> {Comp1 F, Comp2 F} \<in> ?C" using hip consistenceP_Prop5[of F] by blast
    qed
    moreover         
    have "\<forall>F. (FormulaBeta F) \<and> F \<in> W \<longrightarrow> 
              (W \<union> {Comp1 F} \<in> ?C \<or> W \<union> {Comp2 F} \<in> ?C)"
    proof (rule allI impI)+
      fix F 
      assume "(FormulaBeta F) \<and> F \<in> W" 
      thus "W \<union> {Comp1 F} \<in> ?C \<or> W \<union> {Comp2 F} \<in> ?C" 
        using hip consistenceP_Prop6[of F] by blast      
    qed 
    ultimately 
    show ?thesis by auto
  qed
qed
  

lemma ConsistenceCompactness:   
  shows "consistenceP{W::'b formula set. \<forall>A. (A\<subseteq> W \<and> finite A) \<longrightarrow> 
  satisfiable A}"
  using ConsistenceCompactness1  consistenceEq by auto 

lemma countable_enumeration_formula:
  shows  "\<exists>f. enumeration (f:: nat \<Rightarrow>'a::countable formula)" 
  by (metis(full_types) EnumerationFormulasP1
       enumeration_def surj_def surj_from_nat)  

theorem Compactness_Theorem:
  assumes "\<forall>A. (A \<subseteq> (S:: 'a::countable formula set) \<and> finite A) \<longrightarrow> satisfiable A" 
  shows "satisfiable S"
proof -
  have enum: "\<exists>g. enumeration (g:: nat \<Rightarrow> 'a formula)"
    using countable_enumeration_formula by auto 
    let ?C = "{W:: 'a formula set.  \<forall>A. (A \<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A}"
  have "consistenceP ?C"
    using ConsistenceCompactness by simp 
  moreover
  have "S \<in> ?C" using assms by simp
  ultimately 
  show "satisfiable S" using enum and Theo_ExistenceModels[of ?C S] by auto
qed 

end
