(* Formalization adapted from: 
   Fabián Fernando Serrano Suárez, "Formalización en Isar de la
   Meta-Lógica de Primer Orden." PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidad de Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish  *)


(*<*)
theory FinitenessClosedCharProp 
imports Closedness 
begin
(*>*)

section  \<open> Finiteness Character Property  \<close>

text  \<open> This theory formalises the theorem that states that subset closed propositional consistency properties can be extended to satisfy the finite character property. 

The proof is by induction on the structure of propositional formulas based on the analysis of cases for the possible different types of formula in the sets of the collection of sets that hold the propositional consistency property. 
  \<close>



definition finite_character :: "'a set set \<Rightarrow> bool" where
  "finite_character \<C> = (\<forall>S. S \<in> \<C> = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>))"


theorem finite_character_closed: 
  assumes "finite_character \<C>"
  shows "subset_closed \<C>"
proof -  
  { fix S T
    assume "S \<in> \<C>" and  "T \<subseteq> S"
    have "T \<in> \<C>" using "finite_character_def"
    proof -
      { fix U             
        assume "finite U" and "U \<subseteq> T"
        have "U \<in> \<C>"
        proof -
          have "U \<subseteq> S" using `U \<subseteq> T` and `T \<subseteq> S` by simp
          thus "U \<in> \<C>" using `S \<in> \<C>` and `finite U` and assms 
            by (unfold finite_character_def) blast
        qed} 
      thus ?thesis using assms by( unfold finite_character_def) blast
    qed }
  thus ?thesis  by(unfold  subset_closed_def) blast
qed     
    



definition closure_cfinite :: "'a set set \<Rightarrow> 'a set set" (\<open>_⁻\<close> [1000] 999) where
  "\<C>⁻ = {S. \<forall>S'. S' \<subseteq> S \<longrightarrow> finite S' \<longrightarrow> S' \<in> \<C>}"



lemma finite_character_subset:
  assumes "subset_closed \<C>"
  shows "\<C> \<subseteq> \<C>⁻"
proof -
  { fix S
    assume "S \<in> \<C>"
    have "S \<in> \<C>⁻" 
    proof -
      { fix S'
        assume "S' \<subseteq> S" and "finite S'"
        hence "S' \<in> \<C>" using  `subset_closed \<C>` and `S \<in> \<C>`
          by (simp add: subset_closed_def)}
      thus ?thesis by (simp add: closure_cfinite_def) 
    qed}
  thus ?thesis by auto
qed


lemma finite_character: "finite_character (\<C>⁻)"
proof (unfold finite_character_def)
  show "\<forall>S. (S \<in> \<C>⁻) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>⁻)"
  proof
    fix  S
    { assume  "S \<in> \<C>⁻"
      hence "\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>⁻" 
        by(simp add: closure_cfinite_def)} 
    moreover
    { assume "\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>⁻"
      hence  "S \<in> \<C>⁻" by(simp add: closure_cfinite_def)}
    ultimately
    show "(S \<in> \<C>⁻) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>⁻)"
      by blast
  qed
qed
 

lemma cond_characterP1:
  assumes "consistenceP \<C>" 
  and "subset_closed \<C>" 
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "(\<forall>P. \<not>(atom P \<in> S \<and> (\<not>.atom P) \<in> S))"
(*<*)
proof (rule allI)+  
  fix P t
  show "\<not>(atom P  \<in> S \<and> (\<not>.atom P) \<in> S)"
  proof (rule notI)
    assume "atom P \<in> S \<and> (\<not>.atom P) \<in> S"
    hence "{atom P , \<not>.atom P} \<subseteq> S" by simp
    hence "{atom P, \<not>.atom P} \<in> \<C>" using hip by simp
    moreover
    have "\<forall>S. S \<in> \<C> \<longrightarrow> (\<forall>P ts. \<not>(atom P \<in> S \<and> (\<not>.atom P) \<in> S))"
      using `consistenceP \<C>`
      by (simp add: consistenceP_def)
    ultimately
    have "\<not>(atom P \<in> {atom P , \<not>.atom P} \<and> 
          (\<not>.atom P) \<in> {atom P, \<not>.atom P})"
      by auto 
    thus False by simp
  qed
qed  
(*>*)

lemma cond_characterP2:
  assumes "consistenceP \<C>" 
  and "subset_closed \<C>" 
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "FF \<notin> S \<and> (\<not>.TT)\<notin> S"
(*<*)
proof -
  have "FF \<notin> S"
  proof(rule notI)
    assume "FF \<in> S"
    hence "{FF} \<subseteq> S" by simp
    hence "{FF}\<in> \<C>" using hip by simp
    moreover
    have "\<forall>S. S \<in> \<C> \<longrightarrow> FF \<notin> S" using `consistenceP \<C>` 
      by (simp add: consistenceP_def)
    ultimately 
    have "FF \<notin> {FF}" by auto    
    thus False by simp
  qed   
  moreover
  have "(\<not>.TT)\<notin> S"
  proof(rule notI)    
    assume "(\<not>.TT) \<in> S"
    hence "{\<not>.TT} \<subseteq> S" by simp
    hence "{\<not>.TT}\<in> \<C>" using hip by simp
    moreover
    have "\<forall>S. S \<in> \<C> \<longrightarrow> (\<not>.TT) \<notin> S" using `consistenceP \<C>` 
      by (simp add: consistenceP_def)
    ultimately 
    have "(\<not>.TT) \<notin> {(\<not>.TT)}" by auto    
    thus False by simp
  qed
  ultimately show ?thesis by simp   
qed   
(*>*)
text\<open> \<close>
lemma cond_characterP3:
  assumes "consistenceP \<C>" 
  and "subset_closed \<C>" 
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow>  S \<union> {F} \<in> \<C>⁻"
(*<*)
proof (rule allI)        
  fix F
  show "(\<not>.\<not>.F) \<in> S \<longrightarrow>  S \<union> {F} \<in> \<C>⁻"
  proof (rule impI)
    assume "(\<not>.\<not>.F) \<in> S"
    show "S \<union> {F} \<in> \<C>⁻"  
    proof (unfold closure_cfinite_def)
      show "S \<union> {F} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>}"
      proof (rule allI impI CollectI)+
        fix S'
        assume "S' \<subseteq> S \<union> {F}" and "finite S'"  
        show "S' \<in> \<C>"
        proof -          
          have "S' - {F} \<union> {\<not>.\<not>.F}  \<subseteq> S"  
            using `(\<not>.\<not>.F) \<in> S` and  `S'\<subseteq> S \<union> {F}` by auto 
          moreover
          have "finite (S' - {F} \<union> {\<not>.\<not>.F})" using `finite S'` by auto
          ultimately
          have "(S' - {F} \<union> {\<not>.\<not>.F}) \<in> \<C>" using hip  by simp
          moreover
          have "(\<not>.\<not>.F) \<in> (S' - {F} \<union> {\<not>.\<not>.F})" by simp
          ultimately  
          have "(S' - {F} \<union> {\<not>.\<not>.F})\<union> {F} \<in> \<C>" 
            using `consistenceP \<C>` by (simp add: consistenceP_def)
          moreover
          have "(S' - {F} \<union> {\<not>.\<not>.F})\<union> {F} = (S' \<union> {\<not>.\<not>.F})\<union> {F}"
            by auto
          ultimately 
          have "(S' \<union> {\<not>.\<not>.F})\<union> {F} \<in> \<C>" by simp
          moreover
          have  "S' \<subseteq> (S' \<union> {\<not>.\<not>.F})\<union> {F}" by auto
          ultimately
          show "S'\<in> \<C>" using `subset_closed \<C>` 
            by (simp add: subset_closed_def)
        qed
      qed
    qed
  qed
qed     
(*>*)

lemma cond_characterP4:
  assumes "consistenceP \<C>" 
  and "subset_closed \<C>" 
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "(\<forall>F. ((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> (S \<union> {Comp1 F, Comp2 F}) \<in> \<C>⁻)"
(*<*) 
proof (rule allI) 
  fix F 
  show "((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> S \<union> {Comp1 F, Comp2 F} \<in> \<C>⁻"
  proof (rule impI)
    assume "(FormulaAlfa F) \<and> F \<in> S"
    hence "(FormulaAlfa F)" and "F \<in> S" by auto
    show "S \<union> {Comp1 F, Comp2 F} \<in> \<C>⁻"  
    proof (unfold closure_cfinite_def)
      show "S \<union> {Comp1 F, Comp2 F} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>}"
      proof (rule allI impI CollectI)+
        fix S'
        assume "S' \<subseteq> S \<union> {Comp1 F, Comp2 F}"  and  "finite S'"  
        show "S' \<in> \<C>"
        proof -          
          have "S' - {Comp1 F, Comp2 F} \<union> {F}  \<subseteq> S"  
            using `F \<in> S` and  `S'\<subseteq> S \<union> {Comp1 F, Comp2 F}` by auto 
          moreover
          have "finite (S' - {Comp1 F, Comp2 F} \<union> {F})" 
            using `finite S'` by auto
          ultimately
          have "(S' - {Comp1 F, Comp2 F} \<union> {F}) \<in> \<C>" using hip  by simp
          moreover
          have "F \<in> (S' - {Comp1 F, Comp2 F} \<union> {F})" by simp
          ultimately  
          have "(S' - {Comp1 F, Comp2 F} \<union> {F}) \<union> {Comp1 F, Comp2 F} \<in> \<C>" 
            using `consistenceP \<C>` `FormulaAlfa F` 
            by (simp add: consistenceP_def)
          moreover
          have "(S' - {Comp1 F, Comp2 F} \<union> {F}) \<union> {Comp1 F, Comp2 F} = 
                (S' \<union> {F}) \<union> {Comp1 F, Comp2 F}"
            by auto
          ultimately 
          have "(S' \<union> {F}) \<union> {Comp1 F, Comp2 F} \<in> \<C>" by simp
          moreover
          have "S' \<subseteq> (S' \<union> {F}) \<union> {Comp1 F, Comp2 F}" by auto
          ultimately
          show "S'\<in> \<C>" using `subset_closed \<C>` 
            by (simp add: subset_closed_def)
        qed
      qed
    qed
  qed
qed     
(*>*)

lemma cond_characterP5:
  assumes "consistenceP \<C>" 
  and "subset_closed \<C>" 
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "\<forall>F. FormulaBeta F \<and> F \<in> S \<longrightarrow> S \<union> {Comp1 F} \<in> \<C>⁻ \<or> S \<union> {Comp2 F} \<in> \<C>⁻"
(*<*)
proof (rule allI) 
  fix F 
  show "FormulaBeta F \<and> F \<in> S \<longrightarrow> S \<union> {Comp1 F} \<in> \<C>⁻ \<or> S \<union> {Comp2 F} \<in> \<C>⁻"
  proof (rule impI)
    assume "(FormulaBeta F) \<and> F \<in> S" 
    hence "FormulaBeta F" and "F \<in> S" by auto 
    show "S \<union> {Comp1 F} \<in> \<C>⁻ \<or> S \<union> {Comp2 F} \<in> \<C>⁻"
    proof (rule ccontr)
      assume "\<not>(S \<union> {Comp1 F} \<in> \<C>⁻ \<or> S \<union> {Comp2 F} \<in> \<C>⁻)"
      hence "S \<union> {Comp1 F} \<notin> \<C>⁻ \<and> S \<union> {Comp2 F} \<notin> \<C>⁻" by simp    
      hence 1: "\<exists> S1. (S1 \<subseteq> S \<union> {Comp1 F} \<and> finite S1 \<and> S1 \<notin> \<C>)" 
        and 2: "\<exists> S2. (S2 \<subseteq> S \<union> {Comp2 F} \<and> finite S2 \<and> S2 \<notin> \<C>)"
        by (auto simp add: closure_cfinite_def) 
      obtain S1  where S1: "S1 \<subseteq> S \<union> {Comp1 F} \<and> finite S1 \<and> S1 \<notin> \<C>" 
        using 1 by auto
      obtain S2 where  S2: "S2 \<subseteq> S \<union> {Comp2 F} \<and> finite S2 \<and> S2 \<notin> \<C>" 
        using 2 by auto         
      have "(S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<subseteq> S"
        using `F \<in> S` S1 S2 by auto
      moreover
      have "finite ((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F})" 
        using S1 and S2 by simp
      ultimately
      have "(S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<in> \<C>" using hip by simp
      moreover
      have "F \<in> (S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F}" by simp    
      ultimately 
      have 3: "((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp1 F}) \<in> \<C> \<or> 
               ((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp2 F}) \<in> \<C>"
        using `consistenceP \<C>` `FormulaBeta F` 
        by (simp add: consistenceP_def)  
      hence "S1 \<in> \<C> \<or> S2 \<in> \<C>"
      proof (cases)
        assume "((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp1 F}) \<in> \<C>"
        moreover
        have "S1 \<subseteq> ((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp1 F})" 
          by auto       
        ultimately
        have "S1 \<in> \<C>"  using `subset_closed \<C>` 
          by (simp add: subset_closed_def) 
        thus ?thesis by simp
      next 
        assume "\<not>((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp1 F}) \<in> \<C>"
        hence "((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp2 F}) \<in> \<C>" 
          using 3 by simp
        moreover
        have "S2 \<subseteq> ((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp2 F})" 
          by auto       
        ultimately
        have "S2 \<in> \<C>"  using `subset_closed \<C>` 
          by (simp add: subset_closed_def) 
        thus ?thesis by simp
      qed
      thus False using S1 and S2 by simp
    qed
  qed
qed
(*>*)

 

theorem cfinite_consistenceP:
  assumes hip1: "consistenceP \<C>" and hip2: "subset_closed \<C>" 
  shows "consistenceP (\<C>⁻)"
proof - 
  { fix S
    assume "S \<in> \<C>⁻" 
    hence hip3: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>" 
      by (simp add: closure_cfinite_def) 
    have "(\<forall>P.  \<not>(atom P \<in> S \<and> (\<not>.atom P) \<in> S)) \<and>
          FF \<notin> S \<and> (\<not>.TT) \<notin> S \<and>
          (\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow> S \<union> {F} \<in> \<C>⁻) \<and>
          (\<forall>F. ((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> (S \<union> {Comp1 F, Comp2 F}) \<in> \<C>⁻) \<and>
          (\<forall>F. ((FormulaBeta F) \<and> F \<in> S) \<longrightarrow> 
               (S \<union> {Comp1 F} \<in> \<C>⁻) \<or> (S \<union> {Comp2 F} \<in> \<C>⁻))"
      using 
        cond_characterP1[OF hip1 hip2 hip3]  cond_characterP2[OF hip1 hip2 hip3] 
        cond_characterP3[OF hip1 hip2 hip3]  cond_characterP4[OF hip1 hip2 hip3] 
        cond_characterP5[OF hip1 hip2 hip3]  by auto }
  thus ?thesis by (simp add: consistenceP_def) 
qed

(*<*)
end
(*>*)
