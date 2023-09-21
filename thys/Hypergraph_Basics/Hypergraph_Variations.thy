(* Theory: Hypergraph_Variations
   Author: Chelsea Edmonds *)

section \<open>Hypergraph Variations\<close>

text \<open>This section presents many different types of hypergraphs, introducing conditions such as
non-triviality, regularity, and uniform. Additionally, it briefly formalises decompositions \<close>

theory Hypergraph_Variations 
  imports 
    Hypergraph 
    Undirected_Graph_Theory.Bipartite_Graphs
begin

subsection \<open>Non-trivial hypergraphs\<close>

text \<open>Non empty (ne) implies that the vertex (and edge) set is not empty. Non trivial typically
requires at least two edges \<close>

locale hyper_system_vne = hypersystem + 
  assumes V_nempty: "\<V> \<noteq> {}"

locale hyper_system_ne = hyper_system_vne + 
  assumes E_nempty: "E \<noteq> {#}"

locale hypergraph_ne = hypergraph +
  assumes E_nempty: "E \<noteq> {#}"
begin

lemma V_nempty: "\<V> \<noteq> {}"
  using wellformed E_nempty blocks_nempty by fastforce 

lemma sizeE_not_zero: "size E \<noteq> 0"
  using E_nempty by auto

end

sublocale hypergraph_ne \<subseteq> hyper_system_ne
  by (unfold_locales) (simp_all add: V_nempty E_nempty)

locale hyper_system_ns = hypersystem + 
  assumes V_not_single: "\<not> is_singleton \<V>"

locale hypersystem_nt = hyper_system_ne + hyper_system_ns

locale hypergraph_nt = hypergraph_ne + hyper_system_ns

sublocale hypergraph_nt \<subseteq> hypersystem_nt
  by (unfold_locales)

locale fin_hypersystem_vne = fin_hypersystem + hyper_system_vne
begin

lemma order_gt_zero: "horder > 0"
  using V_nempty finite_sets by auto

lemma order_ge_one: "horder \<ge> 1"
  using order_gt_zero by auto

end

locale fin_hypersystem_nt = fin_hypersystem_vne + hypersystem_nt
begin

lemma order_gt_one: "horder > 1"
  using V_nempty V_not_single
  by (simp add: finite_sets is_singleton_altdef nat_neq_iff) 

lemma order_ge_two: "horder \<ge> 2"
  using order_gt_one by auto

end

locale fin_hypergraph_ne = fin_hypergraph + hypergraph_ne

sublocale fin_hypergraph_ne \<subseteq> fin_hypersystem_vne
  by unfold_locales


locale fin_hypergraph_nt = fin_hypergraph + hypergraph_nt

sublocale fin_hypergraph_nt \<subseteq> fin_hypersystem_nt
  by (unfold_locales)

sublocale fin_hypergraph_ne \<subseteq> proper_design \<V> E
  using blocks_nempty sizeE_not_zero by unfold_locales simp

sublocale proper_design \<subseteq> fin_hypergraph_ne \<V> \<B>
  using blocks_nempty design_blocks_nempty by unfold_locales simp

subsection \<open>Regular and Uniform Hypergraphs\<close>
locale dregular_hypergraph = hypergraph + 
  fixes d 
  assumes const_degree: "\<And> x. x \<in> \<V> \<Longrightarrow> hdegree x = d"

locale fin_dregular_hypergraph = dregular_hypergraph + fin_hypergraph

locale kuniform_hypergraph = hypergraph + 
  fixes k :: nat
  assumes uniform: "\<And> e . e \<in># E \<Longrightarrow> card e = k"

locale fin_kuniform_hypergraph = kuniform_hypergraph + fin_hypergraph

locale almost_regular_hypergraph = hypergraph + 
  assumes "\<And> x y . x \<in> \<V> \<Longrightarrow> y \<in> \<V> \<Longrightarrow> \<bar> hdegree x - hdegree y \<bar> \<le> 1"

locale kuniform_regular_hypgraph = kuniform_hypergraph \<V> E k + dregular_hypergraph  \<V> E k
  for  \<V> E k


locale fin_kuniform_regular_hypgraph_nt = kuniform_regular_hypgraph \<V> E k + fin_hypergraph_nt \<V> E 
  for \<V> E k

sublocale fin_kuniform_regular_hypgraph_nt \<subseteq> fin_kuniform_hypergraph \<V> E k
  by unfold_locales

sublocale fin_kuniform_regular_hypgraph_nt \<subseteq> fin_dregular_hypergraph \<V> E k
  by unfold_locales

locale block_balanced_design = block_design + t_wise_balance

locale regular_block_design = block_design + constant_rep_design

sublocale t_design \<subseteq> block_balanced_design 
  by unfold_locales

locale fin_kuniform_hypergraph_nt = fin_kuniform_hypergraph + fin_hypergraph_nt

sublocale fin_kuniform_regular_hypgraph_nt \<subseteq> fin_kuniform_hypergraph_nt \<V> E k
  by unfold_locales

text \<open>Note that block designs are defined as non-trivial and finite as they automatically build on 
the proper design locale \<close>
sublocale fin_kuniform_hypergraph_nt \<subseteq> block_design \<V> E k
  rewrites "point_replication_number E v = hdegree v" and "points_index E vs = hdegree_set vs"
  using uniform by (unfold_locales)
  (simp_all add: point_replication_number_def hdegree_def hdegree_set_def points_index_def E_nempty)

sublocale fin_kuniform_regular_hypgraph_nt \<subseteq> regular_block_design \<V> E k k
  rewrites "point_replication_number E v =hdegree v" and "points_index E vs = hdegree_set vs"
  using const_degree by (unfold_locales) 
    (simp_all add: point_replication_number_def hdegree_def hdegree_set_def points_index_def)

subsection \<open>Factorisations\<close>
locale d_factor = spanning_hypergraph + dregular_hypergraph \<V>H EH d for d

context hypergraph 
begin

definition is_d_factor :: "'a hyp_graph \<Rightarrow> bool" where
"is_d_factor H \<equiv> (\<exists> d. d_factor (hyp_verts H) (hyp_edges H) \<V> E d)"

definition d_factorisation :: "'a hyp_graph multiset \<Rightarrow> bool" where
"d_factorisation S \<equiv> hypergraph_decomposition S \<and> (\<forall> h \<in># S. is_d_factor h)"
end


subsection \<open>Sample Graph Theory Connections\<close>

sublocale fin_graph_system \<subseteq> fin_hypersystem V "mset_set E"
  rewrites "hedge_adjacent = edge_adj"
proof (unfold_locales)
  show "\<And>b. b \<in># mset_set E \<Longrightarrow> b \<subseteq> V" using wellformed fin_edges by simp
  then interpret hs: hypersystem V "mset_set E"
    by unfold_locales (simp add: fin_edges) 
  show  "hs.hedge_adjacent = edge_adj"
    unfolding hs.hedge_adjacent_def edge_adj_def
    by (simp add: fin_edges) 
qed(simp add: finV)

sublocale fin_bipartite_graph \<subseteq> fin_hypersystem_vne V "mset_set E"
  using X_not_empty Y_not_empty partitions_ss(2) by unfold_locales (auto)

end