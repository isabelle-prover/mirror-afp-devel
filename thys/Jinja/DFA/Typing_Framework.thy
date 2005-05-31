(*  Title:      HOL/MicroJava/BV/Typing_Framework.thy
    ID:         $Id: Typing_Framework.thy,v 1.1 2005-05-31 23:21:04 lsf37 Exp $
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

header {* \isaheader{Typing and Dataflow Analysis Framework} *}

theory Typing_Framework = Semilattices:

text {* 
  The relationship between dataflow analysis and a welltyped-instruction predicate. 
*}
types
  's step_type = "nat \<Rightarrow> 's \<Rightarrow> (nat \<times> 's) list"

constdefs
  stable :: "'s ord \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> nat \<Rightarrow> bool"
  "stable r step \<tau>s p \<equiv> \<forall>(q,\<tau>) \<in> set (step p (\<tau>s!p)). \<tau> \<sqsubseteq>\<^sub>r \<tau>s!q"

  stables :: "'s ord \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> bool"
  "stables r step \<tau>s \<equiv> \<forall>p < size \<tau>s. stable r step \<tau>s p"

  wt_step :: "'s ord \<Rightarrow> 's \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> bool"
  "wt_step r T step \<tau>s \<equiv> \<forall>p<size \<tau>s. \<tau>s!p \<noteq> T \<and> stable r step \<tau>s p"

  is_bcv :: "'s ord \<Rightarrow> 's \<Rightarrow> 's step_type \<Rightarrow> nat \<Rightarrow> 's set \<Rightarrow> ('s list \<Rightarrow> 's list) \<Rightarrow> bool"
  "is_bcv r T step n A bcv \<equiv> \<forall>\<tau>s\<^isub>0 \<in> list n A.
  (\<forall>p<n. (bcv \<tau>s\<^isub>0)!p \<noteq> T) = (\<exists>\<tau>s \<in> list n A. \<tau>s\<^isub>0 [\<sqsubseteq>\<^sub>r] \<tau>s \<and> wt_step r T step \<tau>s)"

end
