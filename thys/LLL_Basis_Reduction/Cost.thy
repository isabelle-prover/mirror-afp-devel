(*
    Authors:    Maximilian Haslbeck
                René Thiemann
    License:    BSD
*)
subsection \<open>Representing Computation Costs as Pairs of Results and Costs\<close>
theory Cost
  imports Main
begin

type_synonym 'a cost = "'a \<times> nat" 

definition cost :: "'a cost \<Rightarrow> nat" where "cost = snd" 
definition result :: "'a cost \<Rightarrow> 'a" where "result = fst" 

lemma cost_simps: "cost (a,c) = c" "result (a,c) = a" 
  unfolding cost_def result_def by auto

end