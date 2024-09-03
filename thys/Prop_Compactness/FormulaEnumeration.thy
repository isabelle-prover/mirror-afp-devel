(* Propositional formula  *)

(* Formalization adapted from: 
   Fabián Fernando Serrano Suárez, "Formalización en Isar de la
   Meta-Lógica de Primer Orden." PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidad de Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish  *)

(*<*)
theory FormulaEnumeration
imports BinaryTreeEnumeration
begin
(*>*)

 
fun formulaP_from_tree_b :: "(nat \<Rightarrow> 'b) \<Rightarrow> tree_b \<Rightarrow> 'b formula" where
  "formulaP_from_tree_b g (Leaf 0) = FF"
| "formulaP_from_tree_b g (Leaf (Suc 0)) = TT"
| "formulaP_from_tree_b g (Leaf (Suc (Suc n))) = (atom (g n))"
| "formulaP_from_tree_b g (Tree (Leaf (Suc 0)) (Tree T1 T2)) =
   ((formulaP_from_tree_b g T1) \<and>. (formulaP_from_tree_b g T2))"
| "formulaP_from_tree_b g (Tree (Leaf (Suc (Suc 0))) (Tree T1 T2)) =
   ((formulaP_from_tree_b g T1) \<or>. (formulaP_from_tree_b g T2))"
| "formulaP_from_tree_b g (Tree (Leaf (Suc (Suc (Suc 0)))) (Tree T1 T2)) =
   ((formulaP_from_tree_b g T1) \<rightarrow>. (formulaP_from_tree_b g T2))"
| "formulaP_from_tree_b g (Tree (Leaf (Suc (Suc (Suc (Suc 0))))) T) =
   (\<not>. (formulaP_from_tree_b g T))"
(*<*)

lemma "formulaP_from_tree_b  (\<lambda>n. n) (Leaf  0) = FF"
by simp
(*
normal_form 
  "formulaP_from_tree_b (\<lambda>n. n) (Tree (Leaf (Suc 0)) (Tree (Leaf 0) (Leaf 0)))"
*)
lemma 
  "formulaP_from_tree_b 
   (\<lambda>n. n) (Tree (Leaf (Suc 0)) (Tree (Leaf 0) (Leaf 0))) = FF \<and>. FF" 
by simp 
(*
normal_form 
  "formulaP_from_tree_b g (Tree (Leaf (Suc 0)) (Tree (Leaf 0) (Leaf 0)))"
*)
lemma 
  "formulaP_from_tree_b g (Tree (Leaf (Suc 0)) (Tree (Leaf 0) (Leaf 0))) 
   = FF \<and>. FF" 
by simp
(*
normal_form  "formulaP_from_tree_b (\<lambda>n. n) (Leaf  0) = FF"
normal_form  "formulaP_from_tree_b (\<lambda>n. n) (Leaf  0)"
normal_form 
  "formulaP_from_tree_b  
   (\<lambda>n. n) (Tree (Leaf (Suc (Suc (Suc (Suc 0))))) (Leaf 0))"
*)
lemma 
  "formulaP_from_tree_b 
  (\<lambda>n. n) (Tree (Leaf (Suc (Suc (Suc (Suc 0))))) (Leaf 0)) = (\<not>. FF)"
by simp
(*>*)


primrec tree_b_from_formulaP :: "('b \<Rightarrow> nat) \<Rightarrow>  'b formula \<Rightarrow> tree_b" where
  "tree_b_from_formulaP  g FF = Leaf 0"
| "tree_b_from_formulaP g TT = Leaf (Suc 0)"
| "tree_b_from_formulaP g (atom P) = Leaf (Suc (Suc (g P)))"
| "tree_b_from_formulaP g (F \<and>. G) = Tree (Leaf (Suc 0))
   (Tree (tree_b_from_formulaP g F) (tree_b_from_formulaP g G))"
| "tree_b_from_formulaP g (F \<or>. G) = Tree (Leaf (Suc (Suc 0)))
   (Tree (tree_b_from_formulaP g F) (tree_b_from_formulaP g G))"
| "tree_b_from_formulaP g (F \<rightarrow>. G) = Tree (Leaf (Suc (Suc (Suc 0))))
   (Tree (tree_b_from_formulaP g F) (tree_b_from_formulaP g G))"
| "tree_b_from_formulaP g (\<not>. F) = Tree (Leaf (Suc (Suc (Suc (Suc 0)))))
   (tree_b_from_formulaP g F)"



definition \<Delta>P :: "(nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'b formula" where
  "\<Delta>P g n = formulaP_from_tree_b g (diag_tree_b n)"

definition \<Delta>P' :: "('b \<Rightarrow> nat) \<Rightarrow> 'b formula \<Rightarrow> nat" where
  "\<Delta>P' g' F = undiag_tree_b (tree_b_from_formulaP g' F)"

theorem enumerationformulasP[simp]:
  assumes "\<forall>x. g(g' x) = x" 
  shows "\<Delta>P g (\<Delta>P' g' F) = F"
using assms 
by (induct F)(simp_all add: \<Delta>P_def \<Delta>P'_def)


corollary EnumerationFormulasP:
  assumes "\<forall>P. \<exists> n. P = g n" 
  shows "\<forall>F. \<exists>n. F = \<Delta>P g n"
proof (rule allI)
  fix F
  { have "\<forall>P. P = g (SOME n. P = (g n))"  
    proof(rule allI)
      fix P
      obtain n where n: "P=g(n)" using assms by auto
      thus "P = g (SOME n. P = (g n))" by (rule someI)
    qed }
  hence "\<forall>P. g((\<lambda>P. SOME n. P = (g n)) P) = P" by simp
  hence "F = \<Delta>P g (\<Delta>P' (\<lambda>P. SOME n. P = (g n)) F)" 
    using enumerationformulasP by simp
  thus "\<exists>n. F = \<Delta>P g n"
    by blast
qed



corollary EnumerationFormulasP1:
  assumes "enumeration (g:: nat \<Rightarrow> 'b)"
  shows "enumeration ((\<Delta>P g):: nat \<Rightarrow> 'b formula)"
proof -
  have "\<forall>P. \<exists> n. P = g n" using assms by(unfold enumeration_def)
  hence "\<forall>F. \<exists>n. F = \<Delta>P g n" using EnumerationFormulasP by auto
  thus ?thesis by(unfold enumeration_def)
qed 

corollary EnumeracionFormulasNat:
  shows "\<exists> f. enumeration (f:: nat \<Rightarrow> nat formula)" 
  proof -
    obtain g where g: "enumeration (g:: nat \<Rightarrow> nat)" using enum_nat by auto 
    thus  "\<exists> f. enumeration (f:: nat \<Rightarrow> nat formula)"  
      using  enum_nat EnumerationFormulasP1 by auto
qed
(*<*)
end
(*>*)