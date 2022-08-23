section \<open>An Always-Empty Convergence Graph\<close>

text \<open>This theory implements a convergence graph that always returns an empty list for any lookup.
      By using this graph it is possible to represent methods via the SPY and H-Frameworks
      that do not distribute distinguishing traces over converging traces.\<close>


theory Empty_Convergence_Graph
imports Convergence_Graph
begin

type_synonym empty_cg = unit

definition empty_cg_empty :: "empty_cg" where
  "empty_cg_empty = ()"

definition empty_cg_initial :: "(('a,'b,'c) fsm \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> empty_cg)" where
  "empty_cg_initial M T = empty_cg_empty"

definition empty_cg_insert :: "(empty_cg \<Rightarrow> ('b\<times>'c) list \<Rightarrow> empty_cg)" where
  "empty_cg_insert G v = empty_cg_empty"

definition empty_cg_lookup :: "(empty_cg \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list)" where
  "empty_cg_lookup G v = [v]"

definition empty_cg_merge :: "(empty_cg \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list \<Rightarrow> empty_cg)" where
  "empty_cg_merge G u v = empty_cg_empty"

lemma empty_graph_initial_invar: "convergence_graph_initial_invar M1 M2 empty_cg_lookup empty_cg_initial"
  unfolding convergence_graph_initial_invar_def convergence_graph_lookup_invar_def empty_cg_lookup_def empty_cg_initial_def
  by auto

lemma empty_graph_insert_invar: "convergence_graph_insert_invar M1 M2 empty_cg_lookup empty_cg_insert"
  unfolding convergence_graph_insert_invar_def convergence_graph_lookup_invar_def empty_cg_lookup_def empty_cg_insert_def
  by auto

lemma empty_graph_merge_invar: "convergence_graph_merge_invar M1 M2 empty_cg_lookup empty_cg_merge"
  unfolding convergence_graph_merge_invar_def convergence_graph_lookup_invar_def empty_cg_lookup_def empty_cg_merge_def
  by auto

end