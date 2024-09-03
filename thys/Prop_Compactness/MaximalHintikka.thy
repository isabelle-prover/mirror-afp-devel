(* Formalization adapted from: 
   Fabián Fernando Serrano Suárez, "Formalización en Isar de la
   Meta-Lógica de Primer Orden." PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidad de Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish  *)

(*<*)
theory MaximalHintikka
imports HintikkaTheory   
begin
(*>*)

section    \<open>Maximal Hintikka  \<close>
text   \<open>This theory formalises maximality of Hintikka sets according to Smullyan's textbook \cite{Smullyan}. Specifically, following \cite{Fitting} (page 55) this theory formalises 
the fact that if $\mathcal {C}$ is a propositional consistence property closed by subsets, and $M$ 
a maximal set belonging to $\mathcal{C}$ then $M$ is a Hintikka set.
\<close> 


lemma ext_hintikkaP1:
  assumes  hip1: "consistenceP \<C>" and hip2: "M \<in> \<C>"
  shows   "\<forall>p. \<not> (atom p \<in> M \<and> (\<not>.atom p) \<in> M)"
(*<*)
proof -
  show ?thesis using hip1 hip2 by(unfold consistenceP_def) simp 
qed
(*>*)

text \<open> \<close>

lemma ext_hintikkaP2: 
  assumes hip1: "consistenceP \<C>" and hip2: "M \<in> \<C>"  
  shows "FF \<notin> M"
(*<*)
proof -
  show ?thesis using hip1 hip2 by(unfold consistenceP_def) simp 
qed
(*>*)

text \<open> \<close>

lemma ext_hintikkaP3:
  assumes  hip1: "consistenceP \<C>" and hip2: "M \<in> \<C>"  
  shows "(\<not>.TT) \<notin> M"
(*<*)
proof -
  show ?thesis using hip1 hip2 by(unfold consistenceP_def) simp
qed
(*>*)

text \<open> \<close>

lemma ext_hintikkaP4:
  assumes  hip1: "consistenceP \<C>" and hip2: "maximal M \<C>" and hip3: "M \<in> \<C>"  
  shows "\<forall>F. (\<not>.\<not>.F) \<in> M \<longrightarrow> F \<in> M" 
(*<*)
proof (rule allI impI)+  
  fix F 
  assume h1: "(\<not>.\<not>.F) \<in> M"
  show "F \<in> M"
  proof -   
    have "(\<not>.\<not>.F) \<in> M \<longrightarrow> M \<union> {F} \<in> \<C>"
      using hip1 hip3 by (unfold consistenceP_def) simp    
    hence "M \<union> {F} \<in> \<C>" using h1 by simp  
    moreover 
    have  "\<forall>M'\<in>\<C>. M \<subseteq> M' \<longrightarrow> M = M'" using hip2 by (unfold maximal_def)
    moreover
    have "M \<subseteq> M \<union> {F}" by auto
    ultimately
    have "M = M \<union> {F}" by auto 
    thus "F \<in> M" by auto
  qed
qed
(*>*)

text \<open> \<close>

lemma ext_hintikkaP5:
  assumes hip1: "consistenceP \<C>" and hip2: "maximal M \<C>" and hip3: "M \<in> \<C>"  
  shows "\<forall>F. (FormulaAlfa F) \<and> F \<in> M \<longrightarrow> (Comp1 F \<in> M \<and> Comp2 F \<in> M)"
(*<*)      
proof (rule allI impI)+  
  fix F 
  assume h1: "(FormulaAlfa F) \<and> F \<in> M"
  show "Comp1 F \<in> M \<and> Comp2 F \<in> M"
  proof -
    have "(FormulaAlfa F) \<and> F \<in> M \<longrightarrow> M \<union> {Comp1 F, Comp2 F} \<in> \<C>"
      using hip1 hip3 by (unfold consistenceP_def) simp
    hence  "M \<union> {Comp1 F, Comp2 F} \<in> \<C>" using h1 by simp
    moreover
    have "\<forall>M'\<in>\<C>. M \<subseteq> M' \<longrightarrow> M = M'" using hip2 by (unfold maximal_def) 
    moreover
    have "M \<subseteq> M \<union> {Comp1 F, Comp2 F}" by auto
    ultimately     
    have "M = M \<union> {Comp1 F, Comp2 F}"  by simp     
    thus "Comp1 F \<in> M \<and> Comp2 F \<in> M" by auto
  qed
qed
(*>*)

text \<open> \<close>

lemma ext_hintikkaP6:
  assumes hip1: "consistenceP \<C>" and hip2: "maximal M \<C>" and  hip3: "M \<in> \<C>"  
  shows "\<forall>F. (FormulaBeta F) \<and> F \<in> M \<longrightarrow> Comp1 F \<in> M \<or> Comp2 F \<in> M" 
(*<*)     
proof (rule allI impI)+  
  fix F 
  assume h1: "(FormulaBeta F) \<and> F \<in> M"
  show "Comp1 F \<in> M \<or> Comp2 F \<in> M"
  proof -    
    have "(FormulaBeta F) \<and> F \<in> M \<longrightarrow> M \<union> {Comp1 F} \<in> \<C> \<or> M \<union> {Comp2 F} \<in> \<C>"
      using hip1 hip3 by (unfold consistenceP_def) simp
    hence  "M \<union> {Comp1 F} \<in> \<C> \<or> M \<union> {Comp2 F} \<in> \<C>" using h1 by simp
    thus ?thesis
    proof (rule disjE)
      assume "M \<union> {Comp1 F} \<in> \<C>"
      moreover  
      have "\<forall>M'\<in>\<C>. M \<subseteq> M' \<longrightarrow> M = M'" using hip2 by (unfold maximal_def)
      moreover
      have "M \<subseteq> M \<union> {Comp1 F}" by auto
      ultimately
      have "M = M \<union> {Comp1 F}" by simp
      hence "Comp1 F \<in> M" by auto
      thus "Comp1 F \<in> M \<or> Comp2 F \<in> M" by simp
    next 
      assume "M \<union> {Comp2 F} \<in> \<C>"
      moreover  
      have "\<forall>M'\<in>\<C>. M \<subseteq> M' \<longrightarrow> M = M'" using hip2 by (unfold maximal_def)
      moreover
      have "M \<subseteq> M \<union> {Comp2 F}" by auto
      ultimately
      have "M = M \<union> {Comp2 F}" by simp
      hence "Comp2 F \<in> M" by auto
      thus "Comp1 F \<in> M \<or> Comp2 F \<in> M" by simp
    qed
  qed
qed
(*>*)


theorem MaximalHintikkaP:
  assumes hip1: "consistenceP \<C>" and hip2: "maximal M \<C>" and  hip3: "M \<in> \<C>"
  shows "hintikkaP M"
proof (unfold hintikkaP_def)     
  show "(\<forall>P. \<not> (atom P \<in> M \<and> \<not>.atom P \<in> M)) \<and>
        FF \<notin> M \<and>
        \<not>.TT \<notin> M \<and>
        (\<forall>F. \<not>.\<not>.F \<in> M \<longrightarrow> F \<in> M) \<and>
        (\<forall>F. FormulaAlfa F \<and> F \<in> M \<longrightarrow> Comp1 F \<in> M \<and> Comp2 F \<in> M) \<and>
        (\<forall>F. FormulaBeta F \<and> F \<in> M \<longrightarrow> Comp1 F \<in> M \<or> Comp2 F \<in> M)"
    using ext_hintikkaP1[OF hip1 hip3] 
          ext_hintikkaP2[OF hip1 hip3] 
          ext_hintikkaP3[OF hip1 hip3] 
          ext_hintikkaP4[OF hip1 hip2 hip3]
          ext_hintikkaP5[OF hip1 hip2 hip3] 
          ext_hintikkaP6[OF hip1 hip2 hip3]         
    by blast
qed   
   
(*<*)         
end
(*<*)
