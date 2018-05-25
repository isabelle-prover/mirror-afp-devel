theory Simple_List_Memory
  imports Main
    "Monad_Memo_DP.Memory"
    "HOL-Library.AList"
begin

text \<open>
  Implements memories as mappings, which in turn are implemented as association lists.
  Better performance could be achieved by implementing the mappings as red-black trees
  (see @{locale dp_consistency_rbt}).
  However, they require the key type to be linearly ordered.
  Unfortunately, \<open>HOL-Analysis\<close> fixes the product order to the element-wise order
  and thus we cannot restore a linear order, and the red-black tree implementation
  (from \<open>HOL-Library\<close>) cannot be used.
\<close>

lemma mem_correct_list_mapping:
  "mem_correct
    (\<lambda> k. do {(m::('k \<times> 'v) list) \<leftarrow> State_Monad.get; State_Monad.return (map_of m k)})
    (\<lambda> k v. do {m \<leftarrow> State_Monad.get; State_Monad.set (AList.update k v m)})
    (\<lambda> _. True)"
  by standard
     (auto simp:
        map_le_def state_mem_defs.map_of_def DP_CRelVS.lift_p_def
        State_Monad.bind_def State_Monad.get_def State_Monad.return_def State_Monad.set_def
        update_Some_unfold
     )

lemma mem_correct_list_empty_mapping:
  "mem_correct_empty
    (\<lambda> k. do {(m::('k \<times> 'v) list) \<leftarrow> State_Monad.get; State_Monad.return (map_of m k)})
    (\<lambda> k v. do {m \<leftarrow> State_Monad.get; State_Monad.set (AList.update k v m)})
    (\<lambda> _. True)
    []"
  by (intro mem_correct_empty.intro[OF mem_correct_list_mapping] mem_correct_empty_axioms.intro)
     (auto simp: state_mem_defs.map_of_def map_le_def State_Monad.bind_def State_Monad.get_def)

locale dp_consistency_list =
  fixes dp :: "'k \<Rightarrow> 'v"
begin

sublocale dp_consistency_empty
  "(\<lambda> k. do {(m::('k \<times> 'v) list) \<leftarrow> State_Monad.get; State_Monad.return (map_of m k)})"
  "(\<lambda> k v. do {m \<leftarrow> State_Monad.get; State_Monad.set (AList.update k v m)})"
  "(\<lambda> _::('k \<times> 'v) list. True)" dp "[]:: ('k \<times> 'v) list"
  by (intro
      dp_consistency_empty.intro dp_consistency.intro
      mem_correct_list_mapping mem_correct_list_empty_mapping
     )

end

end