theory Greedy_Step_Spec
  imports
    "../Algorithms/Greedy_Submodular_Construct"
begin

text \<open>
  Step-specification interface for greedy-style algorithms.

  The main construction locale is \<open>Greedy_Setup\<close>. The following locale is an
  intentionally thin named view of this setup, using the name \<open>select\<close> for an
  oracle that chooses a maximum-marginal-gain element from every finite
  non-empty candidate set. This keeps later corollaries independent of the
  concrete choice-based oracle used for the basic greedy construction.
\<close>

locale Greedy_Step_Oracle =
  Greedy_Setup V f k select
  for V :: "'a set"
    and f :: "'a set \<Rightarrow> real"
    and k :: nat
    and select :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a"
begin

end

end