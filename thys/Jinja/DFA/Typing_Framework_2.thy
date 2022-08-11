(*  Title:      HOL/MicroJava/BV/Typing_Framework.thy
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

section \<open>Typing and Dataflow Analysis Framework\<close>

theory Typing_Framework_2 imports Typing_Framework_1 begin

text \<open>
  The relationship between dataflow analysis and a welltyped-instruction predicate. 
\<close>

definition is_bcv :: "'s ord \<Rightarrow> 's \<Rightarrow> 's step_type \<Rightarrow> nat \<Rightarrow> 's set \<Rightarrow> ('s list \<Rightarrow> 's list) \<Rightarrow> bool"
where
  "is_bcv r T step n A bcv \<longleftrightarrow> (\<forall>\<tau>s\<^sub>0 \<in> nlists n A.
  (\<forall>p<n. (bcv \<tau>s\<^sub>0)!p \<noteq> T) = (\<exists>\<tau>s \<in> nlists n A. \<tau>s\<^sub>0 [\<sqsubseteq>\<^sub>r] \<tau>s \<and> wt_step r T step \<tau>s))"

end
