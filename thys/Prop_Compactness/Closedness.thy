(* Formalization adapted from: 
   Fabián Fernando Serrano Suárez, "Formalización en Isar de la
   Meta-Lógica de Primer Orden." PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidad de Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780. In Spanish; 
   Last modified: 29 Sep, 2025
*)

(*<*)
theory Closedness
imports UniformNotation
begin
(*>*)

definition AtomPredicate where
     "AtomPredicate P X at = (\<not> (P X (atom at) \<and> P X (\<not>. atom at)))"

definition ConstPredicate where 
  "ConstPredicate P X = (\<not> P X \<bottom>. \<and> \<not> P X (\<not>. \<top>.))"

definition DNegPredicate where
    "DNegPredicate P Q X F = (P X (\<not>. \<not>. F) \<longrightarrow> Q X F)"

definition AlphaPredicate where
    "AlphaPredicate P Q X F = (FormulaAlpha F \<and> P X F \<longrightarrow> Q X (Comp1 F) (Comp2 F))"

definition BetaPredicate where
    "BetaPredicate P Q X F = (FormulaBeta F \<and> P X F \<longrightarrow> Q X (Comp1 F) (Comp2 F))"

definition ClosedPredicate where
    "ClosedPredicate H P QDNeg QAlpha QBeta =
                    ((\<forall> at. AtomPredicate P H at) \<and>
                    (ConstPredicate P H) \<and>  
                    (\<forall>F. DNegPredicate P QDNeg H F) \<and>
                    (\<forall>F. AlphaPredicate P QAlpha H F) \<and>
                    (\<forall>F. BetaPredicate P QBeta H F))"

(* definition consistenceP :: "'b formula set set \<Rightarrow> bool" where
    "consistenceP \<C> =
       (\<forall>S. S \<in> \<C> \<longrightarrow> ClosedPredicate S
            (\<lambda> S' F . F \<in> S')
            (\<lambda> S' F . S' \<union> {F} \<in> \<C>)
            (\<lambda> S' F G . S' \<union> {F, G} \<in> \<C>)
            (\<lambda> S' F G . S' \<union> {F} \<in> \<C> \<or> S' \<union> {G} \<in> \<C>))" *)

locale consistProp = 
fixes \<C>  :: "'b formula set set"
assumes " (\<forall>S. S \<in> \<C> \<longrightarrow> ClosedPredicate S
            (\<lambda> S' F . F \<in> S')
            (\<lambda> S' F . S' \<union> {F} \<in> \<C>)
            (\<lambda> S' F G . S' \<union> {F, G} \<in> \<C>)
            (\<lambda> S' F G . S' \<union> {F} \<in> \<C> \<or> S' \<union> {G} \<in> \<C>))" 

definition consistenceP :: "'b formula set set \<Rightarrow> bool" where
  "consistenceP \<C> = 
     (\<forall>S. S \<in> \<C> \<longrightarrow> (\<forall>P. \<not> (atom P \<in> S \<and> (\<not>.atom P) \<in> S)) \<and>
     \<bottom>. \<notin> S \<and> (\<not>.\<top>.) \<notin> S \<and>
     (\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow> S \<union> {F} \<in>  \<C>) \<and>
     (\<forall>F. ((FormulaAlpha F) \<and> F\<in>S) \<longrightarrow> (S\<union>{Comp1 F, Comp2 F}) \<in> \<C>) \<and>
     (\<forall>F. ((FormulaBeta F) \<and> F\<in>S) \<longrightarrow> (S\<union>{Comp1 F}\<in>\<C>) \<or> (S\<union>{Comp2 F}\<in>\<C>)))"     

lemma consistenceEq : "consistProp C = consistenceP C"
    unfolding consistProp_def consistenceP_def ClosedPredicate_def
    AtomPredicate_def ConstPredicate_def DNegPredicate_def AlphaPredicate_def
    BetaPredicate_def by simp

definition subset_closed :: "'a set set \<Rightarrow> bool" where
  "subset_closed \<C> = (\<forall>S \<in> \<C>. \<forall>S'. S' \<subseteq> S \<longrightarrow> S' \<in> \<C>)"

unbundle no trancl_syntax

definition closure_subset :: "'a set set \<Rightarrow> 'a set set" (\<open>_\<^sup>+\<close>[1000] 1000) where
  "\<C>\<^sup>+ = {S. \<exists>S' \<in> \<C>. S \<subseteq> S'}"

lemma closed_subset: "\<C> \<subseteq> \<C>\<^sup>+"
proof -
  { fix S
    assume "S \<in> \<C>" 
    moreover 
    have "S \<subseteq> S" by simp
    ultimately
    have "S \<in> \<C>\<^sup>+"
      by (unfold closure_subset_def, auto) }
  thus ?thesis by auto
qed 

lemma closed_closed: "subset_closed (\<C>\<^sup>+)"
proof -
 { fix S T
   assume "S \<in> \<C>\<^sup>+" and "T \<subseteq> S"
   obtain S1 where "S1 \<in> \<C>" and "S \<subseteq> S1" using `S \<in> \<C>\<^sup>+` 
     by (unfold closure_subset_def, auto)
   have "T \<subseteq> S1" using `T \<subseteq> S` and `S \<subseteq> S1`  by simp
   hence "T \<in> \<C>\<^sup>+" using `S1 \<in> \<C>` 
     by (unfold closure_subset_def, auto)}
 thus ?thesis by (unfold subset_closed_def, auto) 
qed 

lemma (in consistProp) cond_consistP :
  assumes  "T \<in> \<C>" and "S \<subseteq> T"  
  shows "(\<forall>P. \<not>(atom P \<in> S \<and> (\<not>.atom P) \<in> S))"
(*<*) 
proof (rule allI)+  
  fix P 
  show "\<not>(atom P  \<in> S \<and> (\<not>.atom P) \<in> S)"
  proof -
    have "\<not>(atom P \<in> T \<and> (\<not>.atom P) \<in> T)"
      using AtomPredicate_def ClosedPredicate_def assms(1) consistProp_axioms
          consistProp_def 
      by (metis (lifting))
    thus "\<not>(atom P \<in> S \<and> (\<not>.atom P) \<in> S)" using `S \<subseteq> T` by auto
  qed
qed 
(*>*)

lemma  (in consistProp) cond_consistP2:
  assumes  "T \<in> \<C>" and "S \<subseteq> T"   
  shows "\<bottom>. \<notin> S \<and> (\<not>.\<top>.)\<notin> S"
(*<*)
proof -
  have "\<bottom>. \<notin> T \<and> (\<not>.\<top>.)\<notin> T"
  proof -
    have "consistenceP \<C>"
      using consistProp_axioms consistProp_def
      by (simp add: consistenceEq) 
    then show ?thesis
      by (simp add: ClosedPredicate_def ConstPredicate_def assms(1) consistenceP_def)
  qed 
  thus "\<bottom>. \<notin> S \<and> (\<not>.\<top>.)\<notin> S" using `S \<subseteq> T` by auto
qed
(*>*)

lemma  (in consistProp) cond_consistP3:
  assumes "T \<in> \<C>" and "S \<subseteq> T"   
  shows "\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow> S \<union> {F} \<in> \<C>\<^sup>+"
proof(rule allI) 
(*<*)       
  fix F
  show "(\<not>.\<not>.F) \<in> S \<longrightarrow>  S \<union> {F} \<in> \<C>\<^sup>+"
  proof (rule impI)
    assume "(\<not>.\<not>.F) \<in> S"
    hence "(\<not>.\<not>.F) \<in> T" using `S \<subseteq> T` by auto   
    hence "T \<union> {F} \<in> \<C>" using `T \<in> \<C>`
    proof -
      have "consistenceP \<C>"
        using consistProp_axioms consistProp_def
        using consistenceEq by blast 
      then show ?thesis
        by (simp add: \<open>\<not>.\<not>.F \<in> T\<close> assms(1) consistenceP_def)
    qed
    moreover 
    have "S \<union> {F} \<subseteq>  T \<union> {F}" using `S \<subseteq> T` by auto
    ultimately   
    show "S \<union> {F} \<in> \<C>\<^sup>+"
      by (auto simp add: closure_subset_def)
  qed
qed
(*>*)

lemma  (in consistProp) cond_consistP4:
  assumes "T \<in> \<C>" and "S \<subseteq> T" 
  shows "\<forall>F. ((FormulaAlpha F) \<and> F \<in> S) \<longrightarrow> (S \<union> {Comp1 F, Comp2 F}) \<in> \<C>\<^sup>+"
(*<*)
proof (rule allI) 
  fix F 
  show "((FormulaAlpha F) \<and> F \<in> S) \<longrightarrow> S \<union> {Comp1 F, Comp2 F} \<in> \<C>\<^sup>+"
  proof (rule impI)
    assume "((FormulaAlpha F) \<and> F \<in> S)"
    hence "FormulaAlpha F" and  "F \<in> T" using `S \<subseteq> T` by auto 
    hence  "T \<union> {Comp1 F, Comp2 F} \<in> \<C>"
    proof -
      have "consistenceP \<C>"
        using consistProp_axioms consistProp_def
        by (simp add: consistenceEq) 
      then show ?thesis
        using \<open>F \<in> T\<close> \<open>FormulaAlpha F \<and> F \<in> S\<close> assms(1) consistenceP_def by blast
    qed  
    moreover
    have "S \<union> {Comp1 F, Comp2 F} \<subseteq> T \<union> {Comp1 F, Comp2 F}" 
      using `S \<subseteq> T` by auto
    ultimately
    show  "S \<union> {Comp1 F, Comp2 F} \<in> \<C>\<^sup>+" 
      by (auto simp add: closure_subset_def)
  qed
qed
(*>*)
text\<open> \<close>
lemma  (in consistProp) cond_consistP5:
  assumes "T \<in> \<C>" and "S \<subseteq> T" 
  shows "(\<forall>F. ((FormulaBeta F) \<and> F \<in> S) \<longrightarrow> 
              (S \<union> {Comp1 F} \<in> \<C>\<^sup>+) \<or> (S \<union> {Comp2 F} \<in> \<C>\<^sup>+))" 

(*<*)
proof (rule allI) 
  fix F 
  show "((FormulaBeta F) \<and> F \<in> S) \<longrightarrow> S \<union> {Comp1 F} \<in> \<C>\<^sup>+ \<or> S \<union> {Comp2 F} \<in> \<C>\<^sup>+" 
  proof (rule impI)
    assume "(FormulaBeta F) \<and> F \<in> S"
    hence "FormulaBeta F" and "F \<in> T" using `S \<subseteq> T` by auto 
    hence "T \<union> {Comp1 F} \<in> \<C> \<or> T \<union> {Comp2 F} \<in> \<C>" 
      using `FormulaBeta F` and `T \<in> \<C>`
    proof -
      show ?thesis
        using \<open>F \<in> T\<close> \<open>FormulaBeta F\<close> assms(1) consistProp_axioms consistProp_def consistenceEq
              consistenceP_def by fastforce 
    qed
    moreover
    have "S \<union> {Comp1 F} \<subseteq> T \<union> {Comp1 F}" and "S \<union> {Comp2 F} \<subseteq> T \<union> {Comp2 F}" 
      using `S \<subseteq> T` by auto
    ultimately
    show "S \<union> {Comp1 F} \<in> \<C>\<^sup>+ \<or> S \<union> {Comp2 F} \<in> \<C>\<^sup>+"
      by(auto simp add: closure_subset_def)
  qed
qed
(*>*)

theorem  (in consistProp) closed_consistenceP:
  shows "consistenceP (\<C>\<^sup>+)"
  by (smt (verit, ccfv_SIG) closure_subset_def consistProp.cond_consistP consistProp.cond_consistP2 consistProp.cond_consistP3
      consistProp.cond_consistP4 consistProp.cond_consistP5 consistProp_axioms consistenceP_def mem_Collect_eq)

(*<*)
end
(*>*)