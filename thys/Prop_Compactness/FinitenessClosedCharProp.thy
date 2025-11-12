(* Formalization adapted from: 
   Fabián Fernando Serrano Suárez, "Formalización en Isar de la
   Meta-Lógica de Primer Orden." PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidad de Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish 
   Last modified: 11 Aug, 2025
 *)


(*<*)
theory FinitenessClosedCharProp 
imports Closedness 
begin
(*>*)

section  \<open> Finiteness Character Property  \<close>

text  \<open> This theory formalises the theorem that states that subset closed propositional consistency properties can be extended to satisfy the finite character property. 

The proof is by induction on the structure of propositional formulas based on the analysis of cases for the possible different types of formula in the sets of the collection of sets that hold the propositional consistency property. 
  \<close>

definition finite_character_property :: "'a set set \<Rightarrow> bool" where
  "finite_character_property \<C> = (\<forall>S. S \<in> \<C> = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>))"

theorem finite_character_closed: 
  assumes "finite_character_property \<C>"
  shows "subset_closed \<C>"
proof -  
  { fix S T
    assume "S \<in> \<C>" and  "T \<subseteq> S"
    have "T \<in> \<C>" using "finite_character_property_def"
    proof -
      { fix U             
        assume "finite U" and "U \<subseteq> T"
        have "U \<in> \<C>"
        proof -
          have "U \<subseteq> S" using `U \<subseteq> T` and `T \<subseteq> S` by simp
          thus "U \<in> \<C>" using `S \<in> \<C>` and `finite U` and assms 
            by (unfold finite_character_property_def) blast
        qed} 
      thus ?thesis using assms by(unfold finite_character_property_def) blast
    qed }
  thus ?thesis  by(unfold  subset_closed_def) blast
qed     
    
definition closure_cfinite :: "'a set set \<Rightarrow> 'a set set" (\<open>_\<^sup>-\<close> [1000] 999) where
  "\<C>\<^sup>- = {S. \<forall>S'. S' \<subseteq> S \<longrightarrow> finite S' \<longrightarrow> S' \<in> \<C>}"

lemma finite_character_subset:
  assumes "subset_closed \<C>"
  shows "\<C> \<subseteq> \<C>\<^sup>-"
proof -
  { fix S
    assume "S \<in> \<C>"
    have "S \<in> \<C>\<^sup>-" 
    proof -
      { fix S'
        assume "S' \<subseteq> S" and "finite S'"
        hence "S' \<in> \<C>" using  `subset_closed \<C>` and `S \<in> \<C>`
          by (simp add: subset_closed_def)}
      thus ?thesis by (simp add: closure_cfinite_def) 
    qed}
  thus ?thesis by auto
qed

lemma finite_character: "finite_character_property (\<C>\<^sup>-)"
proof (unfold finite_character_property_def)
  show "\<forall>S. (S \<in> \<C>\<^sup>-) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>\<^sup>-)"
  proof
    fix  S
    { assume  "S \<in> \<C>\<^sup>-"
      hence "\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>\<^sup>-" 
        by(simp add: closure_cfinite_def)} 
    moreover
    { assume "\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>\<^sup>-"
      hence  "S \<in> \<C>\<^sup>-" by(simp add: closure_cfinite_def)}
    ultimately
    show "(S \<in> \<C>\<^sup>-) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>\<^sup>-)"
      by blast
  qed
qed
 
lemma  (in consistProp) cond_characterP1:
  assumes "subset_closed \<C>" 
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
      by (simp add: cond_consistP)
    ultimately
    have "\<not>(atom P \<in> {atom P , \<not>.atom P} \<and> 
          (\<not>.atom P) \<in> {atom P, \<not>.atom P})"
      by auto 
    thus False by simp
  qed
qed  
(*>*)

lemma  (in consistProp) cond_characterP2:
  assumes  "subset_closed \<C>" 
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "\<bottom>. \<notin> S \<and> (\<not>.\<top>.)\<notin> S"
(*<*)
proof -
  have "\<bottom>. \<notin> S"
  proof(rule notI)
    assume "\<bottom>. \<in> S"
    hence "{\<bottom>.} \<subseteq> S" by simp
    hence "{\<bottom>.}\<in> \<C>" using hip by simp
    moreover
    have "\<forall>S. S \<in> \<C> \<longrightarrow> \<bottom>. \<notin> S" 
      by (simp add: cond_consistP2) 
    ultimately 
    have "\<bottom>. \<notin> {\<bottom>.}" by auto    
    thus False by simp
  qed   
  moreover
  have "(\<not>.\<top>.)\<notin> S"
  proof(rule notI)    
    assume "(\<not>.\<top>.) \<in> S"
    hence "{\<not>.\<top>.} \<subseteq> S" by simp
    hence "{\<not>.\<top>.}\<in> \<C>" using hip by simp
    moreover
    have "\<forall>S. S \<in> \<C> \<longrightarrow> (\<not>.\<top>.) \<notin> S" using cond_consistP2 by blast 
    ultimately 
    have "(\<not>.\<top>.) \<notin> {(\<not>.\<top>.)}" by auto    
    thus False by simp
  qed
  ultimately show ?thesis by simp   
qed   
(*>*)
text\<open> \<close>
lemma  (in consistProp) cond_characterP3:
  assumes  "subset_closed \<C>" 
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow>  S \<union> {F} \<in> \<C>\<^sup>-"
(*<*)
proof (rule allI)        
  fix F
  show "(\<not>.\<not>.F) \<in> S \<longrightarrow>  S \<union> {F} \<in> \<C>\<^sup>-"
  proof (rule impI)
    assume "(\<not>.\<not>.F) \<in> S"
    show "S \<union> {F} \<in> \<C>\<^sup>-"  
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
          have 1: "finite (S' - {F} \<union> {\<not>.\<not>.F})" using `finite S'` by auto
          ultimately
          have "(S' - {F} \<union> {\<not>.\<not>.F}) \<in> \<C>" using hip  by simp
          moreover
          have "(\<not>.\<not>.F) \<in> (S' - {F} \<union> {\<not>.\<not>.F})" by simp
          ultimately  
          have "(S' - {F} \<union> {\<not>.\<not>.F})\<union> {F} \<in> \<C>"
          proof -
            show ?thesis
              using \<open>S' - {F} \<union> {\<not>.\<not>.F} \<in> \<C>\<close> consistProp_axioms consistProp_def consistenceEq consistenceP_def by fastforce
          qed
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
  shows "(\<forall>F. ((FormulaAlpha F) \<and> F \<in> S) \<longrightarrow> (S \<union> {Comp1 F, Comp2 F}) \<in> \<C>\<^sup>-)"
(*<*) 
proof (rule allI) 
  fix F 
  show "((FormulaAlpha F) \<and> F \<in> S) \<longrightarrow> S \<union> {Comp1 F, Comp2 F} \<in> \<C>\<^sup>-"
  proof (rule impI)
    assume "(FormulaAlpha F) \<and> F \<in> S"
    hence "(FormulaAlpha F)" and "F \<in> S" by auto
    show "S \<union> {Comp1 F, Comp2 F} \<in> \<C>\<^sup>-"  
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
            using `consistenceP \<C>` `FormulaAlpha F`  consistenceP_def
            by metis            
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
  shows "\<forall>F. FormulaBeta F \<and> F \<in> S \<longrightarrow> S \<union> {Comp1 F} \<in> \<C>\<^sup>- \<or> S \<union> {Comp2 F} \<in> \<C>\<^sup>-"
(*<*)
proof (rule allI) 
  fix F 
  show "FormulaBeta F \<and> F \<in> S \<longrightarrow> S \<union> {Comp1 F} \<in> \<C>\<^sup>- \<or> S \<union> {Comp2 F} \<in> \<C>\<^sup>-"
  proof (rule impI)
    assume "(FormulaBeta F) \<and> F \<in> S" 
    hence "FormulaBeta F" and "F \<in> S" by auto 
    show "S \<union> {Comp1 F} \<in> \<C>\<^sup>- \<or> S \<union> {Comp2 F} \<in> \<C>\<^sup>-"
    proof (rule ccontr)
      assume "\<not>(S \<union> {Comp1 F} \<in> \<C>\<^sup>- \<or> S \<union> {Comp2 F} \<in> \<C>\<^sup>-)"
      hence "S \<union> {Comp1 F} \<notin> \<C>\<^sup>- \<and> S \<union> {Comp2 F} \<notin> \<C>\<^sup>-" by simp    
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
        using `consistenceP \<C>` `FormulaBeta F`  consistenceP_def
        by metis   
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

theorem  (in consistProp) cfinite_consistenceP:
  assumes hip1: "subset_closed \<C>" 
  shows "consistenceP (\<C>\<^sup>-)"
(*  by (smt (verit, del_insts) closure_cfinite_def cond_characterP4 cond_characterP5
      consistProp.cond_characterP1 consistProp.cond_characterP2 consistProp.cond_characterP3
      consistProp_axioms consistProp_def consistenceEq consistenceP1_def hip1 mem_Collect_eq) *)
proof - 
  { fix S
    assume "S \<in> \<C>\<^sup>-" 
    hence hip2: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>" 
      by (simp add: closure_cfinite_def) 
    have "(\<forall>P.  \<not>(atom P \<in> S \<and> (\<not>.atom P) \<in> S)) \<and>
          \<bottom>. \<notin> S \<and> (\<not>.\<top>.) \<notin> S \<and>
          (\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow> S \<union> {F} \<in> \<C>\<^sup>-) \<and>
          (\<forall>F. ((FormulaAlpha F) \<and> F \<in> S) \<longrightarrow> (S \<union> {Comp1 F, Comp2 F}) \<in> \<C>\<^sup>-) \<and>
          (\<forall>F. ((FormulaBeta F) \<and> F \<in> S) \<longrightarrow> 
               (S \<union> {Comp1 F} \<in> \<C>\<^sup>-) \<or> (S \<union> {Comp2 F} \<in> \<C>\<^sup>-))"
      using cond_characterP1 cond_characterP2 cond_characterP3 cond_characterP4 cond_characterP5
        consistProp_axioms consistProp_def hip1 hip2
      by (smt (verit, ccfv_threshold) consistenceEq) 
  }
  thus ?thesis
    using consistenceEq consistenceP_def by blast
qed

(*<*)
end
(*>*)
