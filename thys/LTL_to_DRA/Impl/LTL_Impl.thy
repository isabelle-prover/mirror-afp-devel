(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>LTL Code Equations\<close>

theory LTL_Impl
  imports Main "../LTL" "../../Boolean_Expression_Checkers/Boolean_Expression_Checkers"
begin

subsection \<open>Subformulae\<close>

fun G_list :: "'a ltl \<Rightarrow>'a ltl list"
where 
  "G_list (\<phi> and \<psi>) = List.union (G_list \<phi>) (G_list \<psi>)"
| "G_list (\<phi> or \<psi>) = List.union (G_list \<phi>) (G_list \<psi>)"
| "G_list (F \<phi>) = G_list \<phi>"
| "G_list (G \<phi>) = List.insert (G \<phi>) (G_list \<phi>)"
| "G_list (X \<phi>) = G_list \<phi>"
| "G_list (\<phi> U \<psi>) = List.union (G_list \<phi>) (G_list \<psi>)"
| "G_list \<phi> = []"

lemma G_eq_G_list:
  "\<^bold>G \<phi> = set (G_list \<phi>)"
  by (induction \<phi>) auto

lemma G_list_distinct:
  "distinct (G_list \<phi>)"
  by (induction \<phi>) auto

subsection \<open>Vars\<close>

fun vars_list :: "'a ltl \<Rightarrow>'a list"
where 
  "vars_list (\<phi> and \<psi>) = List.union (vars_list \<phi>) (vars_list \<psi>)"
| "vars_list (\<phi> or \<psi>) = List.union (vars_list \<phi>) (vars_list \<psi>)"
| "vars_list (F \<phi>) = vars_list \<phi>"
| "vars_list (G \<phi>) = vars_list \<phi>"
| "vars_list (X \<phi>) = vars_list \<phi>"
| "vars_list (\<phi> U \<psi>) = List.union (vars_list \<phi>) (vars_list \<psi>)"
| "vars_list p(a) = [a]"
| "vars_list (np(a)) = [a]"
| "vars_list _ = []"

lemma vars_eq_vars_list:
  "vars \<phi> = set (vars_list \<phi>)"
  by (induction \<phi>) auto

lemma vars_list_distinct:
  "distinct (vars_list \<phi>)"
  by (induction \<phi>) auto

subsection \<open>Propositional Equivalence\<close>

fun bool_expr_of_ltl :: "'a ltl \<Rightarrow> 'a ltl bool_expr" 
where
  "bool_expr_of_ltl true = Const_bool_expr True"
| "bool_expr_of_ltl false = Const_bool_expr False"
| "bool_expr_of_ltl (\<phi> and \<psi>) = And_bool_expr (bool_expr_of_ltl \<phi>) (bool_expr_of_ltl \<psi>)"
| "bool_expr_of_ltl (\<phi> or \<psi>) = Or_bool_expr (bool_expr_of_ltl \<phi>) (bool_expr_of_ltl \<psi>)"
| "bool_expr_of_ltl \<phi> = Atom_bool_expr \<phi>"

lemma val_preservation: 
  "val_bool_expr (bool_expr_of_ltl b) s = op \<Turnstile>\<^sub>P {x. s x} b"
  by (induction b) auto

lemma [code]: 
  "(\<phi> \<equiv>\<^sub>P \<psi>) = equiv_test (bool_expr_of_ltl \<phi>) (bool_expr_of_ltl \<psi>)"
  by (fastforce simp add: val_preservation equiv_test ltl_prop_equiv_def)

lemma [code]: 
  "(\<phi> \<longrightarrow>\<^sub>P \<psi>) = taut_test (Imp_bool_expr (bool_expr_of_ltl \<phi>) (bool_expr_of_ltl \<psi>))"
  by (force simp add: val_preservation ltl_prop_implies_def taut_test)

-- \<open>Test Code Export\<close> 
export_code "op \<equiv>\<^sub>P" in SML module_name prop_equiv
export_code "op \<longrightarrow>\<^sub>P" in SML module_name prop_implies

subsection \<open>Remove Constants\<close>

fun remove_constants\<^sub>P :: "'a ltl \<Rightarrow> 'a ltl"
where
  "remove_constants\<^sub>P (\<phi> and \<psi>) = (
    case (remove_constants\<^sub>P \<phi>) of
        false \<Rightarrow> false
      | true \<Rightarrow> remove_constants\<^sub>P \<psi>
      | \<phi>' \<Rightarrow> (case remove_constants\<^sub>P \<psi> of 
          false \<Rightarrow> false 
        | true \<Rightarrow> \<phi>' 
        | \<psi>' \<Rightarrow> \<phi>' and \<psi>'))"
| "remove_constants\<^sub>P (\<phi> or \<psi>) = (
    case (remove_constants\<^sub>P \<phi>) of
        true \<Rightarrow> true
      | false \<Rightarrow> remove_constants\<^sub>P \<psi>
      | \<phi>' \<Rightarrow> (case remove_constants\<^sub>P \<psi> of 
          true \<Rightarrow> true 
        | false \<Rightarrow> \<phi>' 
        | \<psi>' \<Rightarrow> \<phi>' or \<psi>'))"
| "remove_constants\<^sub>P \<phi> = \<phi>"

lemma remove_constants_correct: 
  "S \<Turnstile>\<^sub>P \<phi> \<longleftrightarrow> S \<Turnstile>\<^sub>P remove_constants\<^sub>P \<phi>"
  by (induction \<phi> arbitrary: S) (auto split: ltl.split)

end
