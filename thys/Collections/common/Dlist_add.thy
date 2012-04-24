header {* \isaheader{Additions to Distinct Lists} *}
theory Dlist_add imports "~~/src/HOL/Library/Dlist" Misc "../iterator/SetIteratorOperations" 
begin

primrec remove1' :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "remove1' x z [] = z"
| "remove1' x z (y # ys) = (if x = y then z @ ys else remove1' x (y # z) ys)"

definition remove' :: "'a \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist"
where "remove' a xs = Dlist (remove1' a [] (list_of_dlist xs))"

lemma distinct_remove1': "distinct (xs @ ys) \<Longrightarrow> distinct (remove1' x xs ys)"
by(induct ys arbitrary: xs) simp_all

lemma set_remove1': "distinct ys \<Longrightarrow> set (remove1' x xs ys) = set xs \<union> (set ys - {x})"
by(induct ys arbitrary: xs) auto

lemma list_of_dlist_remove' [simp, code abstract]:
  "list_of_dlist (remove' a xs) = remove1' a [] (list_of_dlist xs)"
by(simp add: remove'_def distinct_remove1')

lemma remove'_correct: "y \<in> set (list_of_dlist (remove' x xs)) 
  \<longleftrightarrow> (if x = y then False else y \<in> set (list_of_dlist xs))"
  by(simp add: remove'_def Dlist.member_def List.member_def set_remove1')

definition iteratei :: "'a dlist \<Rightarrow> ('a, 'b) set_iterator"
where "iteratei xs = foldli (list_of_dlist xs)"

lemma iteratei_correct:
  "set_iterator (iteratei xs) (set (list_of_dlist xs))"
using distinct_list_of_dlist[of xs] 
      set_iterator_foldli_correct[of "list_of_dlist xs"]
unfolding Dlist.member_def List.member_def iteratei_def
by simp

lemma member_empty: "(set (list_of_dlist Dlist.empty)) = {}"
by(simp add: empty_def)

lemma member_insert [simp]: "set (list_of_dlist (Dlist.insert x xs)) 
  = insert x (set (list_of_dlist xs))"
  by(simp add: Dlist.insert_def Dlist.member_def )

lemma finite_member [simp, intro!]: "finite (set (list_of_dlist xs))"
by(simp add: member_def )

end
