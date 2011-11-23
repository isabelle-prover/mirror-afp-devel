(*  Title:      JinjaThreads/Basic/Cset_without_equal.thy
    Author:     Andreas Lochbihler
*)

theory Cset_without_equal
imports "List_Cset"
begin

text {*
  Adapt @{text "Cset"} code setup such that @{term "Cset.insert"}, 
  @{term "sup :: 'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set"},
  and @{term "cset_of_pred"} do not generate sort constraint @{text equal}.
*}

locale Cset begin

definition insert' :: "'a \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set"
where "insert' = Cset.insert"

definition union' :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set"
where "union' A B = sup A B"

end

declare
  Cset.insert'_def[symmetric, code_unfold]
  Cset.union'_def[symmetric, code_unfold]

locale List_Cset begin

lemma insert'_code:
  "Cset.insert' x (Cset.set xs) = Cset.set (x # xs)"
by(rule Cset.set_eqI)(simp add: Cset.insert'_def)

lemma union'_code:
  "Cset.union' (Cset.set xs) (Cset.set ys) = Cset.set (xs @ ys)"
by(rule Cset.set_eqI)(simp add: Cset.union'_def fun_eq_iff)

end

declare
  List_Cset.insert'_code [code]
  List_Cset.union'_code [code]

text {* Merge name spaces to avoid cyclic module dependencies *}

code_modulename SML
  Cset Cset
  List_Cset Cset
  Cset_without_equal Cset

code_modulename Haskell
  Cset Cset
  List_Cset Cset
  Cset_without_equal Cset

code_modulename OCaml
  Cset Cset
  List_Cset Cset
  Cset_without_equal Cset

end

