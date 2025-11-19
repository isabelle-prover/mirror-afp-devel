(* Formalization adapted from: 
   Fabián Fernando Serrano Suárez, "Formalización en Isar de la
   Meta-Lógica de Primer Orden." PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidad de Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780. In Spanish;
   Last modified: 29 Sep, 2025
  *)

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

lemma   (in consistProp) ext_HintikkaP1:
  assumes   hip: "M \<in> \<C>"
  shows   "\<forall>p. \<not> (atom p \<in> M \<and> (\<not>.atom p) \<in> M)"
(*<*)
proof -
  show ?thesis using hip by (simp add: cond_consistP)  
qed
(*>*)

text \<open> \<close>

lemma  (in consistProp) ext_HintikkaP2: 
  assumes hip: "M \<in> \<C>"  
  shows "\<bottom>. \<notin> M"
(*<*)
proof -
  show ?thesis using hip by (simp add: cond_consistP2) 
qed
(*>*)

text \<open> \<close>

lemma  (in consistProp) ext_HintikkaP3:
  assumes  hip: "M \<in> \<C>"  
  shows "(\<not>.\<top>.) \<notin> M"
(*<*)
proof -
  show ?thesis using hip by (simp add: cond_consistP2)
qed
(*>*)

text \<open> \<close>

lemma  (in consistProp) ext_HintikkaP4:
  assumes  hip1: "maximal M \<C>" and hip2: "M \<in> \<C>"  
  shows "\<forall>F. (\<not>.\<not>.F) \<in> M \<longrightarrow> F \<in> M"
 (* by (metis (no_types, opaque_lifting) Un_insert_right consistProp_axioms consistProp_def consistenceEq
      consistenceP1_def hip1 hip2 insertI1 maximal_def subset_insertI sup_bot.right_neutral) *)
(*<*)
proof (rule allI impI)+  
  fix F 
  assume h1: "(\<not>.\<not>.F) \<in> M"
  show "F \<in> M"
  proof -   
    have "(\<not>.\<not>.F) \<in> M \<longrightarrow> M \<union> {F} \<in> \<C>"
    proof -
      have "consistenceP \<C>"
        using consistProp_axioms consistProp_def consistenceEq by blast  
      then show ?thesis
        by (simp add: consistenceEq consistenceP_def hip2)
    qed
    hence "M \<union> {F} \<in> \<C>" using h1 by simp  
    moreover 
    have  "\<forall> M'\<in> \<C>. M \<subseteq> M' \<longrightarrow> M = M'" using hip1 by (unfold maximal_def)
    moreover
    have "M \<subseteq> M \<union> {F}" by auto
    ultimately
    have "M = M \<union> {F}" by auto 
    thus "F \<in> M" by auto
  qed
qed
(*>*)

text \<open> \<close>

lemma ext_HintikkaP5:
  assumes hip1: "consistenceP \<C>" and hip2: "maximal M \<C>" and hip3: "M \<in> \<C>"  
  shows "\<forall>F. (FormulaAlpha F) \<and> F \<in> M \<longrightarrow> (Comp1 F \<in> M \<and> Comp2 F \<in> M)"
(*<*)      
proof (rule allI impI)+  
  fix F 
  assume h1: "(FormulaAlpha F) \<and> F \<in> M"
  show "Comp1 F \<in> M \<and> Comp2 F \<in> M"
  proof -
    have "(FormulaAlpha F) \<and> F \<in> M \<longrightarrow> M \<union> {Comp1 F, Comp2 F} \<in> \<C>"
      using hip1 hip3 consistenceEq consistenceP_def by auto
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

lemma ext_HintikkaP6:
  assumes hip1: "consistenceP \<C>" and hip2: "maximal M \<C>" and  hip3: "M \<in> \<C>"  
  shows "\<forall>F. (FormulaBeta F) \<and> F \<in> M \<longrightarrow> Comp1 F \<in> M \<or> Comp2 F \<in> M" 
(*<*)     
proof (rule allI impI)+  
  fix F 
  assume h1: "(FormulaBeta F) \<and> F \<in> M"
  show "Comp1 F \<in> M \<or> Comp2 F \<in> M"
  proof -    
    have "(FormulaBeta F) \<and> F \<in> M \<longrightarrow> M \<union> {Comp1 F} \<in> \<C> \<or> M \<union> {Comp2 F} \<in> \<C>"
      using hip1 hip3
      by (simp add: consistenceEq consistenceP_def) 
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

theorem  (in consistProp) MaximalHintikkaP:
  assumes  hip1: "maximal M \<C>" and  hip2: "M \<in> \<C>"
  shows "HintikkaP M"
(*  by (metis consistProp_axioms consistProp_def ext_HintikkaP1 ext_HintikkaP2 ext_HintikkaP3
      ext_HintikkaP4 ext_HintikkaP5 ext_HintikkaP6 HintikkaEq HintikkaP1_def hip1 hip2)*)
proof-
  have "(\<forall>P. \<not> (atom P \<in> M \<and> \<not>.atom P \<in> M)) \<and>
        \<bottom>. \<notin> M \<and>
        \<not>.\<top>. \<notin> M \<and>
        (\<forall>F. \<not>.\<not>.F \<in> M \<longrightarrow> F \<in> M) \<and>
        (\<forall>F. FormulaAlpha F \<and> F \<in> M \<longrightarrow> Comp1 F \<in> M \<and> Comp2 F \<in> M) \<and>
        (\<forall>F. FormulaBeta F \<and> F \<in> M \<longrightarrow> Comp1 F \<in> M \<or> Comp2 F \<in> M)"
    by (meson consistProp_axioms consistenceEq ext_HintikkaP1 ext_HintikkaP2 ext_HintikkaP3 ext_HintikkaP4 ext_HintikkaP5 ext_HintikkaP6
        hip1 hip2)
  thus ?thesis
    using HintikkaEq HintikkaP_def by auto
qed   
  
(*<*)         
end
(*<*)
