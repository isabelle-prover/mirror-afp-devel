(* Model Existence Theorem *)

(* Formalization adapted from: 
   Fabián Fernando Serrano Suárez, "Formalización en Isar de la
   Meta-Lógica de Primer Orden." PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidad de Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish  *)

(*<*)
theory Closedness
imports SyntaxAndSemantics UniformNotation
begin
(*>*)


definition consistenceP :: "'b formula set set \<Rightarrow> bool" where
  "consistenceP \<C> = 
     (\<forall>S. S \<in> \<C> \<longrightarrow> (\<forall>P. \<not> (atom P \<in> S \<and> (\<not>.atom P) \<in> S)) \<and>
     FF \<notin> S \<and> (\<not>.TT) \<notin> S \<and>
     (\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow> S \<union> {F} \<in>  \<C>) \<and>
     (\<forall>F. ((FormulaAlfa F) \<and> F\<in>S) \<longrightarrow> (S\<union>{Comp1 F, Comp2 F}) \<in> \<C>) \<and>
     (\<forall>F. ((FormulaBeta F) \<and> F\<in>S) \<longrightarrow> (S\<union>{Comp1 F}\<in>\<C>) \<or> (S\<union>{Comp2 F}\<in>\<C>)))"     


definition subset_closed :: "'a set set \<Rightarrow> bool" where
  "subset_closed \<C> = (\<forall>S \<in> \<C>. \<forall>S'. S' \<subseteq> S \<longrightarrow> S' \<in> \<C>)"


definition closure_subset :: "'a set set \<Rightarrow> 'a set set" ("_⁺"[1000] 1000) where
  "\<C>⁺ = {S. \<exists>S' \<in> \<C>. S \<subseteq> S'}"


lemma closed_subset: "\<C> \<subseteq> \<C>⁺"
proof -
  { fix S
    assume "S \<in> \<C>" 
    moreover 
    have "S \<subseteq> S" by simp
    ultimately
    have "S \<in> \<C>⁺"
      by (unfold closure_subset_def, auto) }
  thus ?thesis by auto
qed 


lemma closed_closed: "subset_closed (\<C>⁺)"
proof -
 { fix S T
   assume "S \<in> \<C>⁺" and "T \<subseteq> S"
   obtain S1 where "S1 \<in> \<C>" and "S \<subseteq> S1" using `S \<in> \<C>⁺` 
     by (unfold closure_subset_def, auto)
   have "T \<subseteq> S1" using `T \<subseteq> S` and `S \<subseteq> S1`  by simp
   hence "T \<in> \<C>⁺" using `S1 \<in> \<C>` 
     by (unfold closure_subset_def, auto)}
 thus ?thesis by (unfold subset_closed_def, auto) 
qed 

lemma cond_consistP1:
  assumes "consistenceP \<C>" and "T \<in> \<C>" and "S \<subseteq> T"  
  shows "(\<forall>P. \<not>(atom P \<in> S \<and> (\<not>.atom P) \<in> S))"
(*<*) 
proof (rule allI)+  
  fix P 
  show "\<not>(atom P  \<in> S \<and> (\<not>.atom P) \<in> S)"
  proof -
    have "\<not>(atom P \<in> T \<and> (\<not>.atom P) \<in> T)" 
      using `consistenceP \<C>` and `T \<in> \<C>`
      by(simp add: consistenceP_def)
    thus "\<not>(atom P \<in> S \<and> (\<not>.atom P) \<in> S)" using `S \<subseteq> T` by auto
  qed
qed 
(*>*)

lemma cond_consistP2:
  assumes "consistenceP \<C>" and "T \<in> \<C>" and "S \<subseteq> T"   
  shows "FF \<notin> S \<and> (\<not>.TT)\<notin> S"
(*<*)
proof -
  have "FF \<notin> T \<and> (\<not>.TT)\<notin> T" 
    using `consistenceP \<C>` and `T \<in> \<C>` 
    by(simp add: consistenceP_def)
  thus "FF \<notin> S \<and> (\<not>.TT)\<notin> S" using `S \<subseteq> T` by auto
qed
(*>*)

lemma cond_consistP3:
  assumes "consistenceP \<C>" and "T \<in> \<C>" and "S \<subseteq> T"   
  shows "\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow> S \<union> {F} \<in> \<C>⁺"
proof(rule allI) 
(*<*)       
  fix F
  show "(\<not>.\<not>.F) \<in> S \<longrightarrow>  S \<union> {F} \<in> \<C>⁺"
  proof (rule impI)
    assume "(\<not>.\<not>.F) \<in> S"
    hence "(\<not>.\<not>.F) \<in> T" using `S \<subseteq> T` by auto   
    hence "T \<union> {F} \<in> \<C>" using `consistenceP \<C>` and `T \<in> \<C>` 
      by(simp add: consistenceP_def)
    moreover 
    have "S \<union> {F} \<subseteq>  T \<union> {F}" using `S \<subseteq> T` by auto
    ultimately   
    show "S \<union> {F} \<in> \<C>⁺"
      by (auto simp add: closure_subset_def)
  qed
qed
(*>*)

lemma cond_consistP4:
  assumes "consistenceP \<C>" and "T \<in> \<C>" and "S \<subseteq> T" 
  shows "\<forall>F. ((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> (S \<union> {Comp1 F, Comp2 F}) \<in> \<C>⁺"
(*<*)
proof (rule allI) 
  fix F 
  show "((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> S \<union> {Comp1 F, Comp2 F} \<in> \<C>⁺"
  proof (rule impI)
    assume "((FormulaAlfa F) \<and> F \<in> S)"
    hence "FormulaAlfa F" and  "F \<in> T" using `S \<subseteq> T` by auto 
    hence  "T \<union> {Comp1 F, Comp2 F} \<in> \<C>" 
      using `consistenceP \<C>` and `FormulaAlfa F` and `T \<in> \<C>` 
      by (auto simp add: consistenceP_def)
    moreover
    have "S \<union> {Comp1 F, Comp2 F} \<subseteq> T \<union> {Comp1 F, Comp2 F}" 
      using `S \<subseteq> T` by auto
    ultimately
    show  "S \<union> {Comp1 F, Comp2 F} \<in> \<C>⁺" 
      by (auto simp add: closure_subset_def)
  qed
qed
(*>*)
text\<open> \<close>
lemma cond_consistP5:
  assumes "consistenceP \<C>" and "T \<in> \<C>" and "S \<subseteq> T" 
  shows "(\<forall>F. ((FormulaBeta F) \<and> F \<in> S) \<longrightarrow> 
              (S \<union> {Comp1 F} \<in> \<C>⁺) \<or> (S \<union> {Comp2 F} \<in> \<C>⁺))" 
(*<*)
proof (rule allI) 
  fix F 
  show "((FormulaBeta F) \<and> F \<in> S) \<longrightarrow> S \<union> {Comp1 F} \<in> \<C>⁺ \<or> S \<union> {Comp2 F} \<in> \<C>⁺" 
  proof (rule impI)
    assume "(FormulaBeta F) \<and> F \<in> S"
    hence "FormulaBeta F" and "F \<in> T" using `S \<subseteq> T` by auto 
    hence "T \<union> {Comp1 F} \<in> \<C> \<or> T \<union> {Comp2 F} \<in> \<C>" 
      using `consistenceP \<C>` and `FormulaBeta F` and `T \<in> \<C>` 
      by(simp add: consistenceP_def)
    moreover
    have "S \<union> {Comp1 F} \<subseteq> T \<union> {Comp1 F}" and "S \<union> {Comp2 F} \<subseteq> T \<union> {Comp2 F}" 
      using `S \<subseteq> T` by auto
    ultimately
    show "S \<union> {Comp1 F} \<in> \<C>⁺ \<or> S \<union> {Comp2 F} \<in> \<C>⁺"
      by(auto simp add: closure_subset_def)
  qed
qed
(*>*)

theorem closed_consistenceP:
  assumes hip1: "consistenceP \<C>"
  shows "consistenceP (\<C>⁺)"
proof -
  { fix S
    assume "S \<in> \<C>⁺" 
    hence "\<exists>T\<in>\<C>. S \<subseteq> T" by(simp add: closure_subset_def)
    then obtain T where hip2: "T \<in> \<C>" and hip3: "S \<subseteq> T" by auto
    have "(\<forall>P. \<not> (atom P \<in> S \<and> (\<not>.atom P) \<in> S)) \<and>
               FF \<notin> S \<and> (\<not>.TT) \<notin> S \<and>
               (\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow> S \<union> {F} \<in> \<C>⁺) \<and>
               (\<forall>F. ((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> 
                    (S \<union> {Comp1 F, Comp2 F}) \<in> \<C>⁺) \<and>
               (\<forall>F. ((FormulaBeta F) \<and> F \<in> S) \<longrightarrow> 
                    (S \<union> {Comp1 F} \<in> \<C>⁺) \<or> (S \<union> {Comp2 F} \<in> \<C>⁺))"
      using 
        cond_consistP1[OF hip1 hip2 hip3]  cond_consistP2[OF hip1 hip2 hip3]
        cond_consistP3[OF hip1 hip2 hip3]  cond_consistP4[OF hip1 hip2 hip3]
        cond_consistP5[OF hip1 hip2 hip3] 
      by blast}
  thus ?thesis by (simp add: consistenceP_def)
qed

(*<*)
end
(*>*)