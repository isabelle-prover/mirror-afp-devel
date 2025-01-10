(* Formalization adapted from: 
   Fabián Fernando Serrano Suárez, "Formalización en Isar de la
   Meta-Lógica de Primer Orden." PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidad de Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish  *)

(*<*)
theory ModelExistence
imports FormulaEnumeration
begin
(*>*)
section    \<open> Model Existence Theorem  \<close>

text   \<open> This theory formalises the Model Existence Theorem according to Smullyan's textbook \cite{Smullyan} as presented by Fitting in \cite{Fitting}.  \<close>


theorem ExtensionCharacterFinitoP:
  shows "\<C> \<subseteq> \<C>\<^sup>+\<^sup>-" 
  and "finite_character (\<C>\<^sup>+\<^sup>-)" 
  and "consistenceP \<C> \<longrightarrow> consistenceP (\<C>\<^sup>+\<^sup>-)"  
proof -  
show "\<C> \<subseteq> \<C>\<^sup>+\<^sup>-"
  proof -
    have "\<C> \<subseteq> \<C>\<^sup>+" using closed_subset by auto    
    also
    have "... \<subseteq> \<C>\<^sup>+\<^sup>-"
    proof -
      have "subset_closed (\<C>\<^sup>+)" using closed_closed by auto     
      thus ?thesis using finite_character_subset  by auto
    qed
    finally show ?thesis by simp
  qed
next
  show "finite_character (\<C>\<^sup>+\<^sup>-)" using finite_character by auto
next
  show "consistenceP \<C> \<longrightarrow> consistenceP (\<C>\<^sup>+\<^sup>-)"
  proof(rule impI)   
    assume "consistenceP \<C>"
    hence  "consistenceP (\<C>\<^sup>+)" using closed_consistenceP by auto      
    moreover
    have "subset_closed (\<C>\<^sup>+)" using  closed_closed by auto  
    ultimately 
    show "consistenceP (\<C>\<^sup>+\<^sup>-)" using cfinite_consistenceP
      by auto
  qed
qed     
 

lemma ExtensionConsistenteP1:
  assumes h: "enumeration g"
  and h1: "consistenceP \<C>" 
  and h2: "S \<in> \<C>" 
  shows "S \<subseteq> MsucP S (\<C>\<^sup>+\<^sup>-) g" 
  and "maximal (MsucP S (\<C>\<^sup>+\<^sup>-)  g) (\<C>\<^sup>+\<^sup>-)" 
  and "MsucP S  (\<C>\<^sup>+\<^sup>-)  g \<in> \<C>\<^sup>+\<^sup>-" 

proof -  
  have "consistenceP (\<C>\<^sup>+\<^sup>-)"
    using h1 and ExtensionCharacterFinitoP by auto
  moreover   
  have "finite_character (\<C>\<^sup>+\<^sup>-)" using ExtensionCharacterFinitoP by auto
  moreover
  have "S \<in> \<C>\<^sup>+\<^sup>-"
    using h2 and ExtensionCharacterFinitoP by auto    
  ultimately
  show "S \<subseteq> MsucP S (\<C>\<^sup>+\<^sup>-) g" 
    and "maximal (MsucP S (\<C>\<^sup>+\<^sup>-) g) (\<C>\<^sup>+\<^sup>-)" 
    and "MsucP S (\<C>\<^sup>+\<^sup>-) g \<in> \<C>\<^sup>+\<^sup>-"
    using h ConsistentExtensionP[of "\<C>\<^sup>+\<^sup>-"] by auto
qed
  

theorem HintikkaP:  
  assumes h0:"enumeration g" and h1: "consistenceP \<C>" and h2: "S \<in> \<C>"
  shows "hintikkaP (MsucP S (\<C>\<^sup>+\<^sup>-) g)"
proof -
  have 1: "consistenceP (\<C>\<^sup>+\<^sup>-)" 
  using h1 ExtensionCharacterFinitoP by auto
  have 2: "subset_closed (\<C>\<^sup>+\<^sup>-)"
  proof -
    have "finite_character (\<C>\<^sup>+\<^sup>-)" 
      using ExtensionCharacterFinitoP by auto 
    thus "subset_closed (\<C>\<^sup>+\<^sup>-)" by (rule finite_character_closed)
  qed 
  have 3: "maximal (MsucP S (\<C>\<^sup>+\<^sup>-) g) (\<C>\<^sup>+\<^sup>-)" 
    and 4: "MsucP S (\<C>\<^sup>+\<^sup>-) g \<in> \<C>\<^sup>+\<^sup>-" 
    using ExtensionConsistenteP1[OF h0 h1 h2] by auto
  show ?thesis 
    using 1 and 2 and 3 and 4 and MaximalHintikkaP[of "\<C>\<^sup>+\<^sup>-"] by simp 
qed 


theorem ExistenceModelP:
  assumes h0: "enumeration g"
  and h1: "consistenceP \<C>" 
  and h2: "S \<in> \<C>" 
  and h3: "F \<in> S"
  shows "t_v_evaluation (IH (MsucP S (\<C>\<^sup>+\<^sup>-) g)) F = Ttrue" 
proof (rule ModeloHintikkaPa)     
  show "hintikkaP (MsucP S (\<C>\<^sup>+\<^sup>-) g)"
    using h0 and h1 and h2 by(rule HintikkaP)
next
  show "F \<in> MsucP S (\<C>\<^sup>+\<^sup>-) g"
    using h3  Max_subsetuntoP by auto  
qed


theorem Theo_ExistenceModels:
  assumes h1: "\<exists>g. enumeration (g:: nat \<Rightarrow> 'b formula)"  
  and h2: "consistenceP \<C>" 
  and h3: "(S:: 'b formula set) \<in> \<C>"
  shows "satisfiable S"
proof -
  obtain g where g: "enumeration (g:: nat \<Rightarrow> 'b formula)" 
    using h1 by auto
  { fix F
    assume hip: "F \<in> S"
    have  "t_v_evaluation (IH (MsucP S (\<C>\<^sup>+\<^sup>-) g)) F = Ttrue" 
      using g h2 h3 ExistenceModelP hip by blast }
  hence "\<forall>F\<in>S. t_v_evaluation (IH (MsucP S (\<C>\<^sup>+\<^sup>-) g)) F = Ttrue" 
    by (rule ballI)
  hence "\<exists> I. \<forall> F \<in> S. t_v_evaluation I F = Ttrue" by auto
  thus "satisfiable S" by(unfold satisfiable_def, unfold model_def)
qed 



corollary Satisfiable_SetP1:
  assumes h0:  "\<exists>g. enumeration (g:: nat \<Rightarrow> 'b)"
  and h1: "consistenceP \<C>"
  and h2: "(S:: 'b formula set) \<in> \<C>"
  shows "satisfiable S"
proof -
  obtain g where g: "enumeration (g:: nat \<Rightarrow> 'b )" 
    using h0 by auto
  have "enumeration ((\<Delta>P g):: nat \<Rightarrow> 'b formula)" using g  EnumerationFormulasP1 by auto
  hence  h'0: "\<exists>g. enumeration (g:: nat \<Rightarrow> 'b formula)" by auto
  show ?thesis using Theo_ExistenceModels[OF h'0 h1 h2] by auto
qed


corollary Satisfiable_SetP2:
  assumes "consistenceP \<C>" and "(S:: nat formula set) \<in> \<C>"
  shows "satisfiable S"
  using  enum_nat assms Satisfiable_SetP1 by auto 
(*<*)
end
(*>*)
