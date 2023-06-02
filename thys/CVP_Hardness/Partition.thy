theory Partition

imports 
  Main
  Reduction
begin

section \<open>Partition Problem\<close>
text \<open>The Partition Problem is a widely known NP-hard problem.
TODO: Reduction proof to SAT\<close>

definition is_partition :: "int list \<Rightarrow> nat set \<Rightarrow> bool" where
  "is_partition a I = (I \<subseteq> {0..<length a} \<and> (\<Sum>i\<in>I. a ! i) = (\<Sum>i\<in>({0..<length a}-I). a ! i))"

definition partition_problem :: "(int list) set " where
  "partition_problem = {a. \<exists>I. I \<subseteq> {0..<length a} \<and> 
          (\<Sum>i\<in>I. a ! i) = (\<Sum>i\<in>({0..<length a}-I). a ! i)}"

definition partition_problem_nonzero :: "(int list) set " where
  "partition_problem_nonzero = {a. \<exists>I. I \<subseteq> {0..<length a} \<and> length a > 0 \<and>
          (\<Sum>i\<in>I. a ! i) = (\<Sum>i\<in>({0..<length a}-I). a ! i)}"

(* text \<open>Reduction partition problem to SAT(?).\<close>*)


end