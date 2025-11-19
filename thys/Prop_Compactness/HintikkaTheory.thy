(* Formalization adapted from: 
   Fabián Fernando Serrano Suárez, "Formalización en Isar de la
   Meta-Lógica de Primer Orden." PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidad de Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.In Spanish; 
   Last modified: 11 Aug, 2025
 *)


(*<*)
theory  HintikkaTheory
  imports MaximalSet 
begin 
(*>*)
section   \<open> Hintikka Theorem  \<close>

text \<open>
The formalization of Hintikka's lemma is by induction on the structure of the formulas in a Hintikka
set $H$ by applying the technical theorem {\tt HintikkaP\_model\_aux}. This theorem applies a series 
of lemmas to address the evaluation of all possible cases of formulas in $H$. Indeed,   considering
the Boolean evaluation $IH$ that maps all propositional letters in $H$ to true and all other letters 
to false, the most interesting cases of the inductive proof are those related to implicational 
formulas in $H$ and the negation of arbitrary formulas in $H$. These cases are not straightforward 
since implicational and negation formulas are not considered in the definition of Hintikka sets. 
For an implicational formula, say $F_1 \longrightarrow F_2$, it is necessary to prove that if it 
belongs to $H$, its evaluation by $IH$ is true. Also, whenever  
$\neg(F_1 \longrightarrow F_2)$ belongs to $H$ its evaluation is false. The proof is obtained by 
relating such formulas, respectively, with $\beta$ and $\alpha$ formulas (case P6). 
The second interesting case is the one related to arbitrary negations. In this case, it is proved 
that if $\neg F$ belongs to $H$, its evaluation by $IH$ is true, and in the case that 
$\neg\neg F$ belongs to $H$, its evaluation by $IH$ is also true (Case P7).
\<close>

locale HintikkaProp =
  fixes H :: "'b formula set"
assumes "ClosedPredicate H
        (\<lambda> H G . G \<in> H) 
        (\<lambda> H G . G \<in> H)
        (\<lambda> H F G . F \<in> H \<and> G \<in> H)
        (\<lambda> H F G . F \<in> H \<or> G \<in> H)" 

fun IH :: "'b formula set  \<Rightarrow> 'b \<Rightarrow> bool" where
  "IH H P = (if atom P \<in> H then True else False)"

(*
d. You claim to follow Fitting's book, but your proof that every Hintikka set is
satisfiable is more complicated than needed. Here is an alternative method that
use the suggestion in the book to proceed by structural induction in formulas
(your strengthening is needed for negation and implication).


 - First prove that a Hintikka set ``realises'' the canonical version of each
 formula. For instance, if "\<not>. (F \<and>. G) \<in> H", then "\<not>. F \<in> H \<or> \<not>.G \<in> H".
*)

lemma (in HintikkaProp) HintikkaConj:
  assumes "(F \<and>. G) \<in> H"
  shows "F \<in> H \<and> G \<in> H"
proof-
  have "FormulaAlpha  (F \<and>. G)" by auto
  have 1: "Comp1 (F \<and>. G) = F"
    by (simp add: Comp1_def)
  have "Comp2  (F \<and>. G) = G"
    by (simp add: Comp2_def)
  thus ?thesis using 1 assms  AlphaPredicate_def ClosedPredicate_def HintikkaProp_def
    by (metis (no_types, lifting) FormulaAlpha.simps(1) HintikkaProp_axioms) 
qed

lemma (in HintikkaProp) HintikkaNegConj:
  assumes  "\<not>.(F \<and>. G) \<in> H"
  shows "\<not>.F \<in> H \<or> \<not>.G \<in> H"
proof-
  have 1: "FormulaBeta (\<not>. (F \<and>. G))" by auto
  have 2: "Comp1 (\<not>. (F \<and>. G)) = \<not>.F"
    by (simp add: Comp1_def)
  have "Comp2 (\<not>. (F \<and>. G)) = \<not>.G"
    by (simp add: Comp2_def)
  thus ?thesis using "1" "2" assms BetaPredicate_def ClosedPredicate_def
                     HintikkaProp_def
    by (metis (lifting) HintikkaProp_axioms)
qed

lemma (in HintikkaProp) HintikkaDisj:
  assumes  "(F \<or>. G) \<in> H"
  shows "F \<in> H \<or> G \<in> H"
proof-
  have 1: "FormulaBeta (F \<or>. G)" by auto
  have 2: "Comp1 (F \<or>. G) = F"
    by (simp add: Comp1_def)
  have "Comp2 (F \<or>. G) = G"
    by (simp add: Comp2_def)
  thus ?thesis using  "1" "2" BetaPredicate_def ClosedPredicate_def HintikkaProp_axioms
    HintikkaProp_def assms
    by (metis (lifting)) 
qed

lemma (in HintikkaProp) HintikkaNegDisj:
  assumes "\<not>.(F \<or>. G) \<in> H"
  shows "\<not>.F \<in> H \<and> \<not>.G \<in> H"
proof-
  have 1: "FormulaAlpha (\<not>.(F \<or>. G))" by auto
  have 2: "Comp1 (\<not>.(F \<or>. G)) = \<not>.F"
    by (simp add: Comp1_def)
  have   "Comp2 (\<not>. (F \<or>. G)) = \<not>.G"
    by (simp add: Comp2_def)
  thus ?thesis using  "1" "2"  AlphaPredicate_def ClosedPredicate_def  HintikkaProp_axioms
    HintikkaProp_def assms
    by (metis (no_types, lifting)) 
qed

lemma  (in HintikkaProp) HintikkaImp:
  assumes  "(F1 \<rightarrow>. F2) \<in> H"
  shows  "\<not>.F1 \<in> H \<or> F2 \<in> H" 
proof-
  have 1: "FormulaBeta (F1 \<rightarrow>. F2)" by auto
  have 2: "Comp1 (F1 \<rightarrow>. F2) = \<not>.F1"
    by (simp add: Comp1_def)
  have "Comp2 (F1 \<rightarrow>. F2) = F2" 
    by (simp add: Comp2_def) 
  thus ?thesis
    by (metis (no_types, lifting) "1" "2" BetaPredicate_def ClosedPredicate_def HintikkaProp_axioms
        HintikkaProp_def assms)  
qed

lemma  (in HintikkaProp) HintikkaNegImp:
  assumes "\<not>.(F1 \<rightarrow>. F2) \<in> H"
  shows   "F1 \<in> H \<and> \<not>.F2\<in>H"  
proof-
  have 1: "FormulaAlpha (\<not>.(F1 \<rightarrow>. F2))" by auto
  have 2: "Comp1 (\<not>.(F1 \<rightarrow>. F2)) = F1"
    by (simp add: Comp1_def)
  have  "Comp2 (\<not>.(F1 \<rightarrow>. F2)) = \<not>.F2" 
    by (simp add: Comp2_def) 
  thus ?thesis
    by (metis (lifting) "1" "2" AlphaPredicate_def ClosedPredicate_def HintikkaProp_axioms HintikkaProp_def assms) 
qed

lemma (in HintikkaProp) HintikkaP_model_aux:
  shows "(F \<in> H \<longrightarrow> t_v_evaluation (IH H) F) \<and> (\<not>. F \<in> H \<longrightarrow> t_v_evaluation (IH H) (\<not>. F))"
proof(induction F)
  case FF
  then show ?case
    using HintikkaProp_axioms HintikkaProp_def ClosedPredicate_def ConstPredicate_def
    by fastforce  
next
  case TT
  then show ?case
    using HintikkaProp_axioms HintikkaProp_def ClosedPredicate_def ConstPredicate_def t_v_evaluation.simps(2)
    by (metis (no_types, lifting)) 
next
  case (atom x)
  then show ?case
    using HintikkaProp_axioms HintikkaProp_def AtomPredicate_def ClosedPredicate_def IH.elims(1)  t_v_evaluation.simps(3,4)
    by (metis (no_types, lifting))
next
  case (Negation F)
  then show ?case 
    using  HintikkaProp_axioms HintikkaProp_def ClosedPredicate_def DNegPredicate_def
        t_v_evaluation.simps(4)
    by (metis (lifting)) 
next
  case (Conjunction F1 F2)
  then show ?case
    by (metis HintikkaConj HintikkaNegConj t_v_evaluation.simps(4,5)) 
next
  case (Disjunction F1 F2)
  then show ?case
    by (metis HintikkaDisj HintikkaNegDisj t_v_evaluation.simps(4,6)) 
next
  case (Implication F1 F2)
  then show ?case
    by (metis HintikkaImp HintikkaNegImp t_v_evaluation.simps(4,7)) 
qed

corollary (in HintikkaProp) ModelHintikkaPa: 
  assumes  "F \<in> H"  
  shows "t_v_evaluation (IH H) F"
  using assms HintikkaP_model_aux by auto 

corollary (in HintikkaProp) ModelHintikkaP:
  shows "(IH H) model H"
proof (unfold model_def)
  show "\<forall>F\<in>H. t_v_evaluation (IH H) F"
  proof (rule ballI)
    fix F
    assume "F \<in> H"
    thus "t_v_evaluation (IH H) F" using ModelHintikkaPa by auto
  qed 
qed 

corollary  (in HintikkaProp) HintikkaSatisfiable:
  shows "satisfiable H"
using ModelHintikkaP
by (unfold satisfiable_def, auto)

definition HintikkaP :: "'b formula set \<Rightarrow> bool" where 
  "HintikkaP H = ((\<forall>P. \<not> (atom P \<in> H \<and> (\<not>.atom P) \<in> H)) \<and>
                 \<bottom>. \<notin> H \<and> (\<not>.\<top>.) \<notin> H \<and>
                 (\<forall>F. (\<not>.\<not>.F) \<in> H \<longrightarrow> F \<in> H) \<and>
                 (\<forall>F. ((FormulaAlpha F) \<and> F \<in> H) \<longrightarrow> 
                      ((Comp1 F) \<in> H \<and> (Comp2 F) \<in> H)) \<and>
                 (\<forall>F. ((FormulaBeta F) \<and> F \<in> H) \<longrightarrow> 
                      ((Comp1 F) \<in> H \<or> (Comp2 F) \<in> H)))"    

lemma HintikkaEq :  "HintikkaP H = HintikkaProp H" 
    unfolding HintikkaP_def HintikkaProp_def AtomPredicate_def ConstPredicate_def
    DNegPredicate_def AlphaPredicate_def BetaPredicate_def ClosedPredicate_def
    by simp

(*
lemma consistenceEq : "consistenceP' C = consistenceP C"
    unfolding consistenceP'_def consistenceP_def ClosedPredicate_def
    AtomPredicate_def ConstPredicate_def DNegPredicate_def AlphaPredicate_def
    BetaPredicate_def by simp


Why bother to do this? Because now is clearer that you are doing almost the same
thing in several theories: in HintikkaTheory, in Closedness, in
FinitenessClosedCharProp, in MaximalHintikka, and in PropCompactness.


Let us say that, at least, the names of each of the properties would become more
significant.


f. You might use locales, for example in FinitenessClosedCharProp to assume
the consistent set \<C>.


g. You use finite_character both to name a property and for a lemma; I find this
a bit confusing.


h. I understand that you want to keep your formalization self-contained but
it would be ok to import HOL.Relation.


i. I would rename nodes_formulas to atoms and put it in SyntaxAndSemantics.


Minor issues:
-------------

*)

(*<*)
end
(*>*)