(* Author: Joshua Schneider, ETH Zurich *)

subsection \<open>Set with Cartesian product\<close>

theory Applicative_Set imports
  Applicative
  "~~/src/Tools/Adhoc_Overloading"
begin

definition ap_set :: "('a \<Rightarrow> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set"
  where "ap_set F X = {f x | f x. f \<in> F \<and> x \<in> X}"

adhoc_overloading Applicative.ap ap_set

applicative set (C)
for
  pure: "\<lambda>x. {x}"
  ap: ap_set
unfolding ap_set_def by fast+

end