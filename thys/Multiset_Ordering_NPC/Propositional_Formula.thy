section \<open>Propositional Formulas and CNFs\<close>

text \<open>We provide a straight-forward definition of propositional formulas, defined as arbitray formulas
  using variables, negations, conjunctions and disjunctions. CNFs are represented as lists of lists of 
  literals and then converted into formulas.\<close>

theory Propositional_Formula
  imports Main
begin

subsection \<open>Propositional Formulas\<close>

datatype 'a formula = 
  Prop 'a | 
  Conj "'a formula list" | 
  Disj "'a formula list" | 
  Neg "'a formula" |
  Impl "'a formula" "'a formula" |
  Equiv "'a formula" "'a formula" 

fun eval :: "('a \<Rightarrow> bool) \<Rightarrow> 'a formula \<Rightarrow> bool" where
  "eval v (Prop x) = v x" 
| "eval v (Neg f) = (\<not> eval v f)" 
| "eval v (Conj fs) = (\<forall> f \<in> set fs. eval v f)"  
| "eval v (Disj fs) = (\<exists> f \<in> set fs. eval v f)"  
| "eval v (Impl f g) = (eval v f \<longrightarrow> eval v g)"  
| "eval v (Equiv f g) = (eval v f \<longleftrightarrow> eval v g)"  

text \<open>Definition of propositional formula size: number of connectives\<close>

fun size_pf :: "'a formula \<Rightarrow> nat" where
  "size_pf (Prop x) = 1" 
| "size_pf (Neg f) = 1 + size_pf f" 
| "size_pf (Conj fs) = 1 + sum_list (map size_pf fs)"  
| "size_pf (Disj fs) = 1 + sum_list (map size_pf fs)"  
| "size_pf (Impl f g) = 1 + size_pf f + size_pf g"  
| "size_pf (Equiv f g) = 1 + size_pf f + size_pf g"  

subsection \<open>Conjunctive Normal Forms\<close>

type_synonym 'a clause = "('a \<times> bool) list" 
type_synonym 'a cnf = "'a clause list" 

fun formula_of_lit :: "'a \<times> bool \<Rightarrow> 'a formula" where
  "formula_of_lit (x,True) = Prop x" 
| "formula_of_lit (x,False) = Neg (Prop x)" 

definition formula_of_cnf :: "'a cnf \<Rightarrow> 'a formula" where
  "formula_of_cnf = (Conj o map (Disj o map formula_of_lit))" 

definition eval_cnf :: "('a \<Rightarrow> bool) \<Rightarrow> 'a cnf \<Rightarrow> bool" where
  "eval_cnf \<alpha> cnf = eval \<alpha> (formula_of_cnf cnf)" 

lemma eval_cnf_alt_def: "eval_cnf \<alpha> cnf = Ball (set cnf) (\<lambda> c. Bex (set c) (\<lambda> l. \<alpha> (fst l) = snd l))" 
  unfolding eval_cnf_def formula_of_cnf_def o_def eval.simps set_map Ball_image_comp bex_simps
  apply (intro ball_cong bex_cong refl)
  subgoal for c l by (cases l; cases "snd l", auto) 
  done


text \<open>The size of a CNF is the number of literals + the number of clauses, i.e., 
  the sum of the lengths of all clauses + the length.\<close>

definition size_cnf :: "'a cnf \<Rightarrow> nat" where
  "size_cnf cnf = sum_list (map length cnf) + length cnf"


end

