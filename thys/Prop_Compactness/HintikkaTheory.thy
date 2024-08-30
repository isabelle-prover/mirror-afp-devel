(* Formalization adapted from: 
   Fabián Fernando Serrano Suárez, "Formalización en Isar de la
   Meta-Lógica de Primer Orden." PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidad de Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish  *)


(*<*)
theory  HintikkaTheory
  imports MaximalSet 


begin 
(*>*)
section   \<open> Hintikka Theorem  \<close>

text \<open>
The formalization of Hintikka's lemma is by induction on the structure of the formulas in a Hintikka set $H$ by applying the technical theorem {\tt hintikkaP\_model\_aux}. This theorem applies a series of lemmas to address the evaluation of all possible cases of formulas in $H$. Indeed,   considering the Boolean evaluation $IH$ that maps all propositional letters in $H$ to true and all other letters to false, the most interesting cases of the inductive proof are those related to implicational formulas in $H$ and the negation of arbitrary formulas in $H$. These cases are not straightforward since implicational and negation formulas are not considered in the definition of Hintikka sets. For an implicational formula, say $F_1 \longrightarrow F_2$, it is necessary to prove that if it belongs to $H$, its evaluation by $IH$ is true. Also, whenever  $\neg(F_1 \longrightarrow F_2)$ belongs to $H$ its evaluation is false. The proof is obtained by relating such formulas, respectively, with $\beta$ and $\alpha$ formulas (case P6). The second interesting case is the one related to arbitrary negations. In this case, it is proved that if $\neg F$ belongs to $H$, its evaluation by $IH$ is true, and in the case that $\neg\neg F$ belongs to $H$, its evaluation by $IH$ is also true (Case P7).
\<close>




definition hintikkaP :: "'b formula set \<Rightarrow> bool" where 
  "hintikkaP H = ((\<forall>P. \<not> (atom P \<in> H \<and> (\<not>.atom P) \<in> H)) \<and>
                 FF \<notin> H \<and> (\<not>.TT) \<notin> H \<and>
                 (\<forall>F. (\<not>.\<not>.F) \<in> H \<longrightarrow> F \<in> H) \<and>
                 (\<forall>F. ((FormulaAlfa F) \<and> F \<in> H) \<longrightarrow> 
                      ((Comp1 F) \<in> H \<and> (Comp2 F) \<in> H)) \<and>
                 (\<forall>F. ((FormulaBeta F) \<and> F \<in> H) \<longrightarrow> 
                      ((Comp1 F) \<in> H \<or> (Comp2 F) \<in> H)))"
    

fun IH :: "'b formula set  \<Rightarrow> 'b \<Rightarrow> v_truth" where
  "IH H P = (if atom P \<in> H then Ttrue else Ffalse)"


(*<*)
primrec f_size :: "'b formula \<Rightarrow> nat" where
  "f_size FF = 1"
| "f_size TT = 1"
| "f_size (atom P) = 1" 
| "f_size (\<not>. F) = (f_size F) + 1" 
| "f_size (F \<and>. G) = (f_size F) + (f_size G) + 1"
| "f_size (F \<or>. G) = (f_size F) + (f_size G) + 1"             
| "f_size (F \<rightarrow>. G) = (f_size F) + (f_size G) + 1"

lemma pf_size: "0 < f_size F"
by (induct F) auto
(*>*)


(*<*)

(*>*)

lemma case_P1:
assumes hip1: "hintikkaP H" and
hip2: "\<forall>G. (G, FF) \<in> measure f_size \<longrightarrow>
(G \<in> H \<longrightarrow> t_v_evaluation (IH H) G = Ttrue) \<and> ((\<not>.G) \<in> H  \<longrightarrow> t_v_evaluation (IH H) (\<not>.G)= Ttrue)"
shows "(FF \<in> H \<longrightarrow> t_v_evaluation (IH H) FF = Ttrue) \<and> ((\<not>.FF) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.FF)=Ttrue)" 
(*<*)          
proof(rule conjI)
  show "(FF \<in> H \<longrightarrow>  t_v_evaluation (IH H) FF = Ttrue)"
  proof -
    have "FF \<notin> H" using hip1 by (unfold hintikkaP_def) auto
    thus "FF \<in> H \<longrightarrow> t_v_evaluation (IH H) FF = Ttrue" by simp 
  qed 
  next  
  show "(\<not>.FF) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.FF)=Ttrue" 
  proof -
    have "t_v_evaluation (IH H) (\<not>.FF)= Ttrue" by(simp add: v_negation_def)
    thus ?thesis by simp
  qed
qed 
(*>*)
text\<open> \<close>  
lemma case_P2:
assumes hip1: "hintikkaP H" and
hip2: "\<forall>G. (G, TT) \<in> measure f_size \<longrightarrow>
(G \<in> H \<longrightarrow> t_v_evaluation (IH H) G = Ttrue) \<and> ((\<not>.G) \<in> H  \<longrightarrow> t_v_evaluation (IH H) (\<not>.G)= Ttrue)"                 
shows 
"(TT \<in> H \<longrightarrow> t_v_evaluation (IH H) TT = Ttrue) \<and> ((\<not>.TT) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.TT)=Ttrue)"
(*<*)  
proof(rule conjI)
  show "TT \<in> H \<longrightarrow> t_v_evaluation (IH H) TT = Ttrue"
  by simp
  next
  show "(\<not>.TT) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.TT)=Ttrue" 
  proof -         
    have "(\<not>.TT) \<notin> H" using hip1 by (unfold hintikkaP_def) auto
    thus "(\<not>.TT) \<in> H  \<longrightarrow> t_v_evaluation (IH H) (\<not>.TT)=Ttrue" 
    by simp
  qed
qed
(*>*)
text\<open> \<close>
lemma case_P3:
assumes hip1: "hintikkaP H" and
hip2: "\<forall>G. (G, atom P) \<in> measure f_size \<longrightarrow>
(G \<in> H \<longrightarrow> t_v_evaluation (IH H) G = Ttrue) \<and> ((\<not>.G) \<in> H  \<longrightarrow> t_v_evaluation (IH H) (\<not>.G)= Ttrue)"     
shows "(atom P \<in> H  \<longrightarrow> t_v_evaluation (IH H) (atom P) = Ttrue) \<and>
((\<not>.atom P) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.atom P) = Ttrue)"
(*<*)
proof(rule conjI)
  show "(atom P)  \<in> H \<longrightarrow> t_v_evaluation (IH H) (atom P) = Ttrue" by simp
  next
  show "(\<not>.atom P) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.atom P) = Ttrue" 
  proof(rule conjI impI)
    assume h1: "\<not>.atom P \<in> H"
    show "t_v_evaluation (IH H) (\<not>.atom P) = Ttrue"    
    proof -
      have "\<forall>p. \<not> (atom p \<in> H \<and> (\<not>.atom p) \<in> H)"
      using hip1 conjunct1 by(unfold hintikkaP_def)
      hence "atom P \<notin> H" using h1 by auto
      hence "t_v_evaluation (IH H) (atom P) = Ffalse" by simp
      thus ?thesis by(simp add: v_negation_def)
    qed
  qed
qed
(*>*)
text\<open> \<close>
lemma case_P4:
assumes hip1: "hintikkaP H" and
hip2: "\<forall>G. (G, F1 \<and>. F2) \<in> measure f_size \<longrightarrow> 
(G \<in> H \<longrightarrow> t_v_evaluation (IH H) G = Ttrue) \<and> ((\<not>.G) \<in> H  \<longrightarrow> t_v_evaluation (IH H) (\<not>.G) = Ttrue)"   
shows "((F1 \<and>. F2) \<in> H \<longrightarrow> t_v_evaluation (IH H) (F1 \<and>. F2) = Ttrue) \<and>
((\<not>.(F1 \<and>. F2)) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.(F1 \<and>. F2)) = Ttrue)"
(*<*)
proof(rule conjI)                               
  show "((F1 \<and>. F2) \<in> H \<longrightarrow> t_v_evaluation (IH H) (F1 \<and>. F2) = Ttrue)"    
  proof(rule conjI impI)
    assume h2: "(F1 \<and>. F2) \<in> H" 
    show  "t_v_evaluation (IH H) (F1 \<and>. F2) = Ttrue"
    proof - 
      have "FormulaAlfa (F1 \<and>. F2)" by simp 
      hence "Comp1 (F1 \<and>. F2) \<in> H \<and> Comp2 (F1 \<and>. F2) \<in> H"
      using hip1 h2 by(auto simp add: hintikkaP_def)         
      hence "F1 \<in> H" and "F2 \<in> H" by(unfold Comp1_def, unfold Comp2_def, auto)
      moreover     
      have "(F1, F1 \<and>. F2) \<in> measure f_size" and
      "(F2, F1 \<and>. F2) \<in> measure f_size"
      by auto
      hence "(F1 \<in> H \<longrightarrow> t_v_evaluation (IH H) F1 = Ttrue)" and
      "(F2 \<in> H \<longrightarrow> t_v_evaluation (IH H) F2 = Ttrue)" 
      using hip2 by auto      
      ultimately
      have "t_v_evaluation (IH H) F1 = Ttrue" and "t_v_evaluation (IH H) F2 = Ttrue"
      by auto
      thus ?thesis by (simp add: v_conjunction_def)      
    qed 
  qed
  next
  show "\<not>.(F1 \<and>. F2) \<in> H \<longrightarrow> t_v_evaluation (IH H)  (\<not>.(F1 \<and>. F2)) = Ttrue" 
  proof(rule impI)
    assume h2: "(\<not>.(F1 \<and>. F2)) \<in> H" 
    show "t_v_evaluation (IH H) (\<not>.(F1 \<and>. F2)) = Ttrue"
    proof - 
      have "FormulaBeta (\<not>.(F1 \<and>. F2))" by simp 
      hence "Comp1 (\<not>.(F1 \<and>. F2)) \<in> H \<or> Comp2 (\<not>.(F1 \<and>. F2)) \<in> H"
      using hip1 h2 by(auto simp add: hintikkaP_def)              
      hence "(\<not>.F1) \<in> H \<or> (\<not>.F2) \<in> H" by(unfold Comp1_def, unfold Comp2_def, auto)
      thus ?thesis
      proof(rule disjE)
        assume "(\<not>.F1) \<in> H"
        moreover        
        have "(\<not>.F1, (F1 \<and>. F2)) \<in> measure f_size" using pf_size by simp         
        hence "(\<not>.F1) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.F1) = Ttrue" 
        using hip2 by simp    
        ultimately 
        have 1: "t_v_evaluation (IH H) (\<not>.F1) = Ttrue" by simp       
        hence "t_v_evaluation (IH H) F1 = Ffalse" using NegationValues2 by auto                  
        thus "t_v_evaluation (IH H) (\<not>.(F1 \<and>. F2)) = Ttrue" 
        by (simp add: v_negation_def, simp add: v_conjunction_def)          next  
        assume "(\<not>.F2) \<in> H"
        moreover 
        have "(\<not>.F2, (F1 \<and>. F2)) \<in> measure f_size" using pf_size by simp
        hence " (\<not>.F2) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.F2)= Ttrue" 
        using hip2 by simp    
        ultimately 
        have 1: "t_v_evaluation (IH H) (\<not>.F2) = Ttrue" by simp
        hence "t_v_evaluation (IH H) F2 = Ffalse" using NegationValues2 by auto          
        thus "t_v_evaluation (IH H) (\<not>.(F1 \<and>. F2)) = Ttrue"
        by (simp add: v_negation_def, simp add: v_conjunction_def)                
      qed 
    qed
  qed
qed
(*>*)
text\<open> \<close>      
lemma case_P5:
assumes hip1: "hintikkaP H" and
hip2: "\<forall>G. (G, F1 \<or>. F2) \<in> measure f_size \<longrightarrow>
(G \<in> H \<longrightarrow> t_v_evaluation (IH H) G = Ttrue) \<and> ((\<not>.G) \<in> H  \<longrightarrow> t_v_evaluation (IH H) (\<not>.G) = Ttrue)"             
shows "((F1 \<or>. F2) \<in> H \<longrightarrow> t_v_evaluation (IH H) (F1 \<or>. F2) = Ttrue) \<and>
((\<not>.(F1 \<or>. F2)) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.(F1 \<or>. F2)) = Ttrue)"
(*<*)
proof(rule conjI) 
  show "(F1 \<or>. F2) \<in> H \<longrightarrow> t_v_evaluation (IH H) (F1 \<or>. F2) = Ttrue"
  proof(rule conjI impI)
    assume h2: "(F1  \<or>. F2) \<in> H" 
    show "t_v_evaluation (IH H) (F1 \<or>. F2) = Ttrue"
    proof -     
      have "FormulaBeta (F1 \<or>.F2)" by simp 
      hence "Comp1 (F1 \<or>.F2) \<in> H \<or> Comp2 (F1 \<or>.F2) \<in> H"
      using hip1 h2 by(auto simp add: hintikkaP_def)              
      hence "F1 \<in> H \<or> F2 \<in> H" by(unfold Comp1_def, unfold Comp2_def, auto)     
      thus ?thesis
      proof(rule disjE)
        assume "F1 \<in> H"
        moreover         
        have "(F1, F1 \<or>. F2) \<in> measure f_size" by simp
        hence "(F1 \<in> H \<longrightarrow>  t_v_evaluation (IH H) F1 = Ttrue)" 
        using hip2 by simp    
        ultimately 
        have "t_v_evaluation (IH H) F1 = Ttrue" by simp
        thus "t_v_evaluation (IH H) (F1 \<or>. F2) = Ttrue" by (simp add: v_disjunction_def)   
        next  
        assume "F2 \<in> H"
        moreover        
        have "(F2, (F1 \<or>. F2)) \<in> measure f_size" by simp
        hence "F2 \<in> H \<longrightarrow>  t_v_evaluation (IH H) F2 =Ttrue" 
        using hip2 by simp    
        ultimately 
        have "t_v_evaluation (IH H) F2 = Ttrue" by simp
        thus "t_v_evaluation (IH H) (F1 \<or>. F2) = Ttrue" by (simp add: v_disjunction_def)            
      qed 
    qed
  qed
  next
  show "(\<not>.(F1 \<or>. F2)) \<in> H \<longrightarrow>
  t_v_evaluation (IH H) (\<not>.(F1 \<or>. F2)) = Ttrue"
  proof(rule impI)
    assume h2: "(\<not>.(F1  \<or>. F2)) \<in> H" 
    show "t_v_evaluation (IH H) (\<not>.(F1  \<or>. F2)) = Ttrue"
    proof -
      have "FormulaAlfa(\<not>.(F1 \<or>. F2))" by simp 
      hence "Comp1 (\<not>.(F1 \<or>. F2)) \<in> H \<and> Comp2 (\<not>.(F1 \<or>. F2)) \<in> H"
      using hip1 h2 by(auto simp add: hintikkaP_def)              
      hence "\<not>.F1 \<in> H \<and> \<not>.F2 \<in> H" by(unfold Comp1_def, unfold Comp2_def, auto) 
      hence "(\<not>.F1) \<in> H" and "(\<not>.F2) \<in> H" by auto
      moreover     
      have "(\<not>.F1, F1 \<or>. F2) \<in> measure f_size" and
     "(\<not>.F2, F1 \<or>. F2) \<in> measure f_size" using pf_size
      by auto
      hence "((\<not>.F1) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.F1) = Ttrue)" and
           "((\<not>.F2) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.F2) = Ttrue)" 
      using hip2 by auto      
      ultimately
      have 1: "t_v_evaluation (IH H) (\<not>.F1) = Ttrue" and
           2: "t_v_evaluation (IH H) (\<not>.F2) = Ttrue" by auto
      have "t_v_evaluation (IH H) F1 = Ffalse" using 1 NegationValues2 by auto              
      moreover
      have "t_v_evaluation (IH H) F2 = Ffalse" using 2 NegationValues2 by auto      
      ultimately   
      show  "t_v_evaluation (IH H) (\<not>.(F1 \<or>. F2)) = Ttrue"
      by (simp add: v_disjunction_def, simp add: v_negation_def)      
    qed 
  qed
qed
(*>*)
text\<open> \<close>
lemma case_P6:
assumes hip1: "hintikkaP H" and 
hip2: "\<forall>G. (G, F1  \<rightarrow>. F2) \<in> measure f_size \<longrightarrow>
(G \<in> H \<longrightarrow> t_v_evaluation (IH H) G = Ttrue) \<and> ((\<not>.G) \<in> H  \<longrightarrow> t_v_evaluation (IH H) (\<not>.G) = Ttrue)"           
shows "((F1  \<rightarrow>. F2) \<in> H \<longrightarrow> t_v_evaluation (IH H) (F1  \<rightarrow>. F2) = Ttrue) \<and>
((\<not>.(F1  \<rightarrow>. F2)) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.(F1  \<rightarrow>. F2)) = Ttrue)"
(*<*)
proof(rule conjI impI)+
  assume h2: "(F1 \<rightarrow>.F2) \<in> H"
  show " t_v_evaluation (IH H) (F1 \<rightarrow>. F2) = Ttrue"
  proof -    
    have "FormulaBeta (F1 \<rightarrow>. F2)" by simp  
    hence "Comp1(F1 \<rightarrow>. F2) \<in> H \<or> Comp2 (F1 \<rightarrow>. F2)\<in> H" 
    using hip1 h2 by(auto simp add: hintikkaP_def) 
    hence "(\<not>.F1) \<in> H \<or> F2 \<in> H" by(unfold Comp1_def, unfold Comp2_def, auto) 
    thus " t_v_evaluation (IH H) (F1 \<rightarrow>. F2) = Ttrue"
    proof(rule disjE)           
      assume "(\<not>.F1) \<in> H"             
      moreover
      have "(\<not>.F1, F1  \<rightarrow>. F2) \<in> measure f_size" using pf_size by auto 
      hence " (\<not>.F1) \<in> H \<longrightarrow>  t_v_evaluation (IH H) (\<not>.F1) = Ttrue" 
      using hip2 by simp
      ultimately
      have 1: "t_v_evaluation (IH H) (\<not>.F1) = Ttrue" by simp
      hence "t_v_evaluation (IH H) F1 = Ffalse" using NegationValues2 by auto       
      thus "t_v_evaluation (IH H) (F1 \<rightarrow>. F2) = Ttrue"  by(simp add: v_implication_def)
      next
      assume "F2 \<in> H"
      moreover       
      have "(F2, F1  \<rightarrow>. F2) \<in> measure f_size" by simp
      hence "(F2 \<in> H \<longrightarrow>  t_v_evaluation (IH H) F2 = Ttrue)" 
      using hip2 by simp    
      ultimately 
      have "t_v_evaluation (IH H) F2 = Ttrue" by simp
      thus "t_v_evaluation (IH H) (F1 \<rightarrow>. F2) = Ttrue" by(simp add: v_implication_def)
    qed
  qed
  next
  show "(\<not>.(F1 \<rightarrow>. F2)) \<in> H \<longrightarrow>        
        t_v_evaluation (IH H) (\<not>.(F1 \<rightarrow>. F2)) = Ttrue"
  proof(rule impI)
    assume h2: "(\<not>.(F1 \<rightarrow>. F2)) \<in> H"
    show "t_v_evaluation (IH H) (\<not>.(F1 \<rightarrow>. F2)) = Ttrue"
    proof -                      
      have "FormulaAlfa (\<not>.(F1 \<rightarrow>. F2))" by auto
      hence "Comp1(\<not>.(F1 \<rightarrow>. F2)) \<in> H \<and> Comp2(\<not>.(F1 \<rightarrow>. F2))\<in> H"
      using hip1 h2 by (auto simp add: hintikkaP_def)   
      hence "F1 \<in> H \<and> (\<not>.F2) \<in> H" by(unfold Comp1_def, unfold Comp2_def, auto)                        
      moreover
      have "(F1, F1  \<rightarrow>. F2) \<in> measure f_size" and
      "(\<not>.F2, F1  \<rightarrow>. F2) \<in> measure f_size" using pf_size
      by auto
      hence "F1 \<in> H \<longrightarrow> t_v_evaluation (IH H) F1 = Ttrue"
      and "(\<not>.F2) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.F2) = Ttrue"
      using hip2 by auto   
      ultimately
      have "t_v_evaluation (IH H) F1 = Ttrue" 
      and
     "t_v_evaluation (IH H) (\<not>.F2) = Ttrue"  by auto 
      thus       
     "t_v_evaluation (IH H) (\<not>.(F1 \<rightarrow>. F2)) = Ttrue" by(simp add: v_implication_def)
    qed
  qed
qed
(*>*)
text\<open> \<close>
lemma case_P7:
assumes hip1: "hintikkaP H" and
hip2: "\<forall>G. (G, (\<not>.form)) \<in> measure f_size \<longrightarrow> 
(G \<in> H \<longrightarrow> t_v_evaluation (IH H) G = Ttrue) \<and> ((\<not>.G) \<in> H  \<longrightarrow> t_v_evaluation (IH H) (\<not>.G) = Ttrue)"            
shows "((\<not>.form) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.form) = Ttrue) \<and>
((\<not>.(\<not>.form)) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.(\<not>.form)) = Ttrue)"
(*<*)
proof(intro conjI)       
  show  "\<not>.form \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.form) = Ttrue"
  proof(rule impI)
    assume h1: "(\<not>.form) \<in> H"     
    moreover
    have "(form, (\<not>.form)) \<in> measure f_size" by simp
    hence "((\<not>.form) \<in> H \<longrightarrow>
           t_v_evaluation (IH H) (\<not>.form)= Ttrue)" 
    using hip2 by simp
    ultimately
    show "t_v_evaluation (IH H) (\<not>.form) = Ttrue" using h1 by simp
  qed
  next     
  show "(\<not>.\<not>.form) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.\<not>.form) = Ttrue" 
  proof(rule impI)
    assume h2: "(\<not>.\<not>.form) \<in> H"         
    have "\<forall>Z. (\<not>.\<not>.Z) \<in> H \<longrightarrow> Z \<in> H" using hip1 
    by(unfold hintikkaP_def) blast
    hence "(\<not>.\<not>.form) \<in> H \<longrightarrow> form \<in> H" by simp    
    hence "form \<in> H" using h2 by simp   
    moreover
    have "(form, (\<not>.form)) \<in> measure f_size" by simp
    hence "form \<in> H \<longrightarrow> t_v_evaluation (IH H) form = Ttrue" 
    using hip2 by simp
    ultimately
    have "t_v_evaluation (IH H) form = Ttrue" by simp
    thus  "t_v_evaluation (IH H) (\<not>.\<not>.form) = Ttrue" using h2 by (simp add: v_negation_def)
  qed
qed
(*>*)

theorem hintikkaP_model_aux: 
  assumes hip: "hintikkaP H"
  shows "(F \<in> H \<longrightarrow>  t_v_evaluation (IH H) F = Ttrue) \<and> 
                    ((\<not>.F) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.F) = Ttrue)" 
proof (rule wf_induct [where r="measure f_size" and a=F])    
  show "wf(measure f_size)" by simp
next
  fix F  
  assume hip1: "\<forall>G. (G, F) \<in> measure f_size \<longrightarrow>
                    (G \<in> H \<longrightarrow> t_v_evaluation (IH H) G = Ttrue) \<and>
                    ((\<not>.G) \<in> H  \<longrightarrow> t_v_evaluation (IH H) (\<not>.G) = Ttrue)"         
  show "(F \<in> H \<longrightarrow> t_v_evaluation (IH H) F = Ttrue) \<and>
        ((\<not>.F) \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>.F) = Ttrue)"
  proof (cases F)    
    assume "F=FF"   
    thus ?thesis using case_P1 hip hip1 by simp
  next 
    assume "F=TT" 
    thus ?thesis using case_P2 hip hip1 by auto
  next
    fix P 
    assume "F = atom P"
    thus ?thesis using hip hip1 case_P3[of H P] by simp
  next
    fix F1  F2
    assume "F= (F1 \<and>. F2)"
    thus ?thesis using hip hip1 case_P4[of H F1 F2] by simp
  next
    fix F1 F2
    assume "F= (F1 \<or>. F2)"
    thus ?thesis using hip hip1 case_P5[of H F1 F2] by simp
  next
    fix F1 F2
    assume "F= (F1 \<rightarrow>. F2)"
    thus ?thesis using hip hip1 case_P6[of H F1 F2] by simp
  next
    fix F1
    assume "F=(\<not>.F1)"
    thus ?thesis using hip hip1 case_P7[of H F1] by simp    
  qed
qed


corollary ModeloHintikkaPa: 
  assumes "hintikkaP H" and "F \<in> H"  
  shows "t_v_evaluation (IH H) F = Ttrue"
  using assms hintikkaP_model_aux by auto 


corollary ModeloHintikkaP: 
  assumes "hintikkaP H"
  shows "(IH H) model H"
proof (unfold model_def)
  show "\<forall>F\<in>H. t_v_evaluation (IH H) F = Ttrue"
  proof (rule ballI)
    fix F
    assume "F \<in> H"
    thus "t_v_evaluation (IH H) F = Ttrue" using assms ModeloHintikkaPa  by auto
  qed 
qed 


corollary Hintikkasatisfiable:
  assumes "hintikkaP H"
  shows "satisfiable H"
using assms ModeloHintikkaP
by (unfold satisfiable_def, auto)
 
(*<*)
end
(*>*)