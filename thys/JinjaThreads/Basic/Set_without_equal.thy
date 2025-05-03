(*  Title:      JinjaThreads/Basic/Set_without_equal.thy
    Author:     Andreas Lochbihler
*)

theory Set_without_equal
imports Main
begin

text \<open>
  Adapt @{type "set"} code setup such that @{const "insert"}, 
  @{const "union"}, and @{term "set_of_pred"} do not generate
  sort constraint @{class equal}.
\<close>

declare [[code drop: insert union]]

lemma insert_code [code]:
  \<open>insert x (set xs) = set (x # xs)\<close>
  by simp

lemma union_code [code]:
  \<open>set xs \<union> set ys = set (xs @ ys)\<close>
  by simp

end
