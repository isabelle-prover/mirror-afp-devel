section \<open>An Interface for Solvers for a Subset of Finite Integer Difference Logic\<close>

theory Finite_IDL_Solver_Interface
  imports Main
begin

text \<open>We require a solver for (a subset of) integer-difference-logic (IDL). We basically just need
  comparisons of variables against constants, and difference of two variables.

  Note that all variables can be assumed to be finitely bounded, so we only need a solver for 
  finite IDL search problems.
  Moreover, it suffices to consider inputs where only those variables are put in comparison that 
  share the same sort
  (the second parameter of a variable),
  and the bounds are completely determined by the sorts.\<close>

type_synonym ('v,'s)fidl_input = "(('v \<times> 's) \<times> int) list \<times> (('v \<times> 's) \<times> 'v \<times> 's) list list" 

definition fidl_input :: "('v,'s)fidl_input \<Rightarrow> bool" where 
  "fidl_input = (\<lambda> (bnds, diffs).
     distinct (map fst bnds) \<and> (\<forall> v w u. (v,w) \<in> set (concat diffs) \<longrightarrow> u \<in> {v,w} \<longrightarrow> u \<in> fst ` set bnds) 
     \<and> (\<forall> v w. (v,w) \<in> set (concat diffs) \<longrightarrow> snd v = snd w) 
     \<and> (\<forall> v w. (v,w) \<in> set (concat diffs) \<longrightarrow> v \<noteq> w) 
     \<and> (\<forall> v w b1 b2. (v,b1) \<in> set bnds \<longrightarrow> (w,b2) \<in> set bnds \<longrightarrow> snd v = snd w \<longrightarrow> b1 = b2) 
     \<and> (\<forall> v b. (v,b) \<in> set bnds \<longrightarrow> b \<ge> 0))" 

definition fidl_solvable :: "('v,'s)fidl_input \<Rightarrow> bool" where
  "fidl_solvable = (\<lambda> (bnds, diffs). (\<exists>\<alpha> :: 'v \<times> 's \<Rightarrow> int.
    (\<forall> (v,b) \<in> set bnds. 0 \<le> \<alpha> v \<and> \<alpha> v \<le> b) \<and>
    (\<forall> c \<in> set diffs. \<exists> (v,w) \<in> set c. \<alpha> v \<noteq> \<alpha> w)))" 

definition finite_idl_solver where  "finite_idl_solver solver = (\<forall> input.
   fidl_input input \<longrightarrow> solver input = fidl_solvable input)"

definition dummy_fidl_solver where 
  "dummy_fidl_solver input = fidl_solvable input" 

lemma dummy_fidl_solver: "finite_idl_solver dummy_fidl_solver" 
  unfolding dummy_fidl_solver_def finite_idl_solver_def by simp

lemma dummy_fidl_solver_code[code]: "dummy_fidl_solver input = Code.abort (STR ''dummy fidl solver'') (\<lambda> _. dummy_fidl_solver input)" 
  by simp

end
