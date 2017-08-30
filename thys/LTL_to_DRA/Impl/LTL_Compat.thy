(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>LTL Translation Layer\<close>

theory LTL_Compat
  imports Main LTL.LTL "../LTL_FGXU"
begin

--\<open>The following infrastructure translates the generic @{datatype ltln} datatype to special structure used in this project\<close>

fun ltln_to_ltl :: "'a ltln \<Rightarrow> 'a ltl"
where
  "ltln_to_ltl true\<^sub>n  = true"
| "ltln_to_ltl false\<^sub>n = false"
| "ltln_to_ltl prop\<^sub>n(q) = p(q)"
| "ltln_to_ltl nprop\<^sub>n(q) = np(q)"
| "ltln_to_ltl (\<phi> and\<^sub>n \<psi>) = ltln_to_ltl \<phi> and ltln_to_ltl \<psi>"
| "ltln_to_ltl (\<phi> or\<^sub>n \<psi>) = ltln_to_ltl \<phi> or ltln_to_ltl \<psi>"
| "ltln_to_ltl (\<phi> U\<^sub>n \<psi>) = (if \<phi> = true\<^sub>n then F (ltln_to_ltl \<psi>) else ltln_to_ltl \<phi> U ltln_to_ltl \<psi>)"
| "ltln_to_ltl (\<phi> V\<^sub>n \<psi>) = (if \<phi> = false\<^sub>n then G (ltln_to_ltl \<psi>) else G (ltln_to_ltl \<psi>) or (ltln_to_ltl \<psi> U (ltln_to_ltl \<phi> and ltln_to_ltl \<psi>)))"
| "ltln_to_ltl (X\<^sub>n \<phi>) = X (ltln_to_ltl \<phi>)"

lemma ltln_to_ltl_semantics:
  "w \<Turnstile> ltln_to_ltl \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
  by (induction \<phi> arbitrary: w)
     (simp del: semantics_ltln.simps(9); unfold ltln_Release_alterdef; auto)+

lemma ltln_to_ltl_atoms:
  "vars (ltln_to_ltl \<phi>) = atoms_ltln \<phi>"
  by (induction \<phi>) auto

fun atoms_list :: "'a ltln \<Rightarrow>'a list"
where 
  "atoms_list (\<phi> and\<^sub>n \<psi>) = List.union (atoms_list \<phi>) (atoms_list \<psi>)"
| "atoms_list (\<phi> or\<^sub>n \<psi>) = List.union (atoms_list \<phi>) (atoms_list \<psi>)"
| "atoms_list (\<phi> U\<^sub>n \<psi>) = List.union (atoms_list \<phi>) (atoms_list \<psi>)"
| "atoms_list (\<phi> V\<^sub>n \<psi>) = List.union (atoms_list \<phi>) (atoms_list \<psi>)"
| "atoms_list (X\<^sub>n \<phi>) = atoms_list \<phi>"
| "atoms_list (prop\<^sub>n(a)) = [a]"
| "atoms_list (nprop\<^sub>n(a)) = [a]"
| "atoms_list _ = []"

lemma atoms_list_correct:
  "set (atoms_list \<phi>) = atoms_ltln \<phi>"
  by (induction \<phi>) auto

lemma atoms_list_distinct:
  "distinct (atoms_list \<phi>)"
  by (induction \<phi>) auto

end