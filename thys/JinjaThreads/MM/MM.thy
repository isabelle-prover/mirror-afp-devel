(*  Title:      JinjaThreads/MM/MM.thy
    Author:     Andreas Lochbihler
*)

header {* \chapter{Memory Models} *}

theory MM imports "../Common/Heap" begin

definition new_Addr :: "(addr \<rightharpoonup> 'b) \<Rightarrow> addr option"
where "new_Addr h \<equiv> if \<exists>a. h a = None then Some(LEAST a. h a = None) else None"

lemma new_Addr_SomeD:
  "new_Addr h = Some a \<Longrightarrow> h a = None"
by(auto simp add:new_Addr_def split:if_splits intro: LeastI)

subsection {* Code generation *}

definition gen_new_Addr :: "(addr \<rightharpoonup> 'b) \<Rightarrow> addr \<Rightarrow> addr option"
where "gen_new_Addr h n \<equiv> if \<exists>a. a \<ge> n \<and> h a = None then Some(LEAST a. a \<ge> n \<and> h a = None) else None"

lemma new_Addr_code_code [code]:
  "new_Addr h = gen_new_Addr h 0"
by(simp add: new_Addr_def gen_new_Addr_def)

lemma gen_new_Addr_code [code]:
  "gen_new_Addr h n = (if h n = None then Some n else gen_new_Addr h (Suc n))"
apply(simp add: gen_new_Addr_def)
apply(rule impI)
apply(rule conjI)
 apply safe[1]
  apply(auto intro: Least_equality)[2]
 apply(rule arg_cong[where f=Least])
 apply(rule ext)
 apply auto[1]
 apply(case_tac "n = ab")
  apply simp
 apply simp
apply clarify
apply(subgoal_tac "a = n")
 apply simp
 apply(rule Least_equality)
 apply auto[2]
apply(rule ccontr)
apply(erule_tac x="a" in allE)
apply simp
done

end


