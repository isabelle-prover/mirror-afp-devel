section \<open>Graph Theory Inheritance\<close>
text \<open> This theory aims to demonstrate the use of locales to transfer theorems between different 
graph/combinatorial structure representations \<close>

theory Graph_Theory_Relations imports Undirected_Graph_Basics Bipartite_Graphs 
"Design_Theory.Block_Designs" "Design_Theory.Group_Divisible_Designs"
begin

subsection \<open> Design Inheritance \<close>
text \<open>A graph is a type of incidence system, and more specifically a type of combinatorial design. 
This section demonstrates the correspondence between designs and graphs \<close>

sublocale graph_system \<subseteq> inc: incidence_system V "mset_set E"
  by (unfold_locales) (metis wellformed elem_mset_set ex_in_conv infinite_set_mset_mset_set) 

sublocale fin_graph_system \<subseteq> finc: finite_incidence_system V "mset_set E"
  using finV by unfold_locales

sublocale fin_ulgraph \<subseteq> d: design V "mset_set E"
  using edge_size empty_not_edge fin_edges by unfold_locales auto 

sublocale fin_ulgraph \<subseteq> d: simple_design V "mset_set E"
  by unfold_locales (simp add: fin_edges) 

locale graph_has_edges = graph_system + 
  assumes edges_nempty: "E \<noteq> {}"

locale fin_sgraph_wedges = fin_sgraph + graph_has_edges

text \<open>The simple graph definition of degree overlaps with the definition of a point replication number \<close>
sublocale fin_sgraph_wedges \<subseteq> bd: block_design V "mset_set E" 2
  rewrites "point_replication_number (mset_set E) x = degree x" 
    and "points_index (mset_set E) vs = degree_set vs"
proof (unfold_locales) 
  show "inc.\<b> \<noteq> 0"  by (simp add: edges_nempty fin_edges)
  show "\<And>bl. bl \<in># mset_set E \<Longrightarrow> card bl = 2" by (simp add: fin_edges two_edges)
  show "mset_set E index vs = degree_set vs"
    unfolding degree_set_def points_index_def by (simp add: fin_edges) 
next
  have "size {#b \<in># (mset_set E) . x \<in> b#} = card (incident_edges x)"
    unfolding incident_edges_def vincident_def
    by (simp add: fin_edges) 
  then show "mset_set E rep x = degree x" using alt_degree_def point_replication_number_def
    by metis
qed

locale fin_bipartite_graph_wedges = fin_bipartite_graph + fin_sgraph_wedges

sublocale fin_bipartite_graph_wedges \<subseteq> group_design V "mset_set E" "{X, Y}"
  by unfold_locales (simp_all add: partition ne)


subsection \<open>Adjacency Relation Definition \<close>

text \<open> Another common formal representation of graphs is as a vertex set and an adjacency relation
This is a useful representation in some contexts - we use locales to enable the transfer of 
results between the two representations, specifically the mutual sublocales approach \<close>

locale graph_rel = 
  fixes vertices :: "'a set" ("V")
  fixes adj_rel :: "'a rel"
  assumes wf: "\<And> u v. (u, v) \<in> adj_rel \<Longrightarrow> u \<in> V \<and> v \<in> V"
begin 

abbreviation "adj u v \<equiv> (u, v) \<in> adj_rel"

lemma wf_alt: "adj u v \<Longrightarrow> (u, v) \<in> V \<times> V"
  using wf by blast

end


locale ulgraph_rel = graph_rel + 
  assumes sym_adj: "sym adj_rel"
begin

text \<open> This definition makes sense in the context of an undirected graph \<close>
definition edge_set:: "'a edge set" where
"edge_set \<equiv> {{u, v} | u v. adj u v}"

lemma obtain_edge_pair_adj:
  assumes "e \<in> edge_set"
  obtains u v where "e = {u, v}" and "adj u v" 
  using assms edge_set_def mem_Collect_eq
  by fastforce 

lemma adj_to_edge_set_card: 
  assumes "e \<in> edge_set"
  shows "card e = 1 \<or> card e = 2"
proof -
  obtain u v where "e = {u, v}" and "adj u v" using obtain_edge_pair_adj assms by blast 
  then show ?thesis by (cases "u = v", simp_all)
qed

lemma adj_to_edge_set_card_lim: 
  assumes "e \<in> edge_set"
  shows "card e > 0 \<and> card e \<le> 2"
proof -
  obtain u v where "e = {u, v}" and "adj u v" using obtain_edge_pair_adj assms by blast 
  then show ?thesis by (cases "u = v", simp_all)
qed

lemma edge_set_wf: "e \<in> edge_set \<Longrightarrow> e \<subseteq> V"
  using obtain_edge_pair_adj wf by (metis insert_iff singletonD subsetI) 

lemma is_graph_system: "graph_system V edge_set"
  by (unfold_locales) (simp add: edge_set_wf)

lemma sym_alt: "adj u v \<longleftrightarrow> adj v u"
  using sym_adj by (meson symE)

lemma is_ulgraph: "ulgraph V edge_set"
  using ulgraph_axioms_def is_graph_system adj_to_edge_set_card_lim 
  by (intro_locales) auto

end

context ulgraph
begin

definition adj_relation :: "'a rel" where
"adj_relation \<equiv> {(u, v) | u v . vert_adj u v}"

lemma adj_relation_wf: "(u, v) \<in> adj_relation \<Longrightarrow> {u, v} \<subseteq> V"
  unfolding adj_relation_def using vert_adj_imp_inV by auto

lemma adj_relation_sym: "sym adj_relation"
  unfolding adj_relation_def sym_def using vert_adj_sym by auto

lemma is_ulgraph_rel: "ulgraph_rel V adj_relation"
  using adj_relation_wf adj_relation_sym by (unfold_locales) auto

text \<open> Temporary interpretation - mutual sublocale setup \<close>

interpretation ulgraph_rel V adj_relation by (rule is_ulgraph_rel)

lemma vert_adj_rel_iff: 
  assumes "u \<in> V" "v \<in> V"
  shows "vert_adj u v \<longleftrightarrow> adj u v"
  using adj_relation_def by auto

lemma edges_rel_is: "E = edge_set"
proof -
  have "E = {{u, v} | u v . vert_adj u v}"
  proof (intro subset_antisym subsetI)
    show "\<And>x. x \<in> {{u, v} |u v. vert_adj u v} \<Longrightarrow> x \<in> E"
      using vert_adj_def by fastforce
  next 
    fix x assume "x \<in> E"
    then have "x \<subseteq> V" and "card x > 0" and "card x \<le> 2" using wellformed edge_size by auto 
    then obtain u v where "x = {u, v}" and "{u, v} \<in> E"
      by (metis \<open>x \<in> E\<close> alt_edge_size card_1_singletonE card_2_iff insert_absorb2) 
    then show "x \<in> {{u, v} |u v. vert_adj u v}" unfolding vert_adj_def by blast    
  qed
  then have "E = {{u, v} | u v . adj u v}" using vert_adj_rel_iff Collect_cong
    by (smt (verit) local.wf vert_adj_imp_inV) 
  thus ?thesis using edge_set_def by simp
qed

end

context ulgraph_rel 
begin

text \<open> Temporary interpretation - mutual sublocale setup \<close>
interpretation ulgraph V edge_set by (rule is_ulgraph)

lemma rel_vert_adj_iff:  "vert_adj u v \<longleftrightarrow> adj u v"
proof (intro iffI)
  assume "vert_adj u v"
  then have "{u, v} \<in> edge_set" by (simp add: vert_adj_def)
  then show "adj u v" using edge_set_def
    by (metis (no_types, lifting) doubleton_eq_iff obtain_edge_pair_adj sym_alt) 
next
  assume "adj u v"
  then have "{u, v} \<in> edge_set" using edge_set_def by auto
  then show "vert_adj u v" by (simp add: vert_adj_def)
qed

lemma rel_item_is: "(u, v) \<in> adj_rel \<longleftrightarrow> (u, v) \<in> adj_relation"
  unfolding adj_relation_def using rel_vert_adj_iff by auto

lemma rel_edges_is: "adj_rel = adj_relation"
  using rel_item_is by auto

end

sublocale ulgraph_rel \<subseteq> ulgraph "V" "edge_set"
  rewrites "ulgraph.adj_relation edge_set = adj_rel"
  using local.is_ulgraph rel_edges_is by simp_all

sublocale ulgraph \<subseteq> ulgraph_rel "V" "adj_relation"
  rewrites "ulgraph_rel.edge_set adj_relation = E"
  using is_ulgraph_rel edges_rel_is by simp_all

locale sgraph_rel = ulgraph_rel +
  assumes irrefl_adj: "irrefl adj_rel"
begin

lemma irrefl_alt: "adj u v \<Longrightarrow> u \<noteq> v"
  using irrefl_adj irrefl_def by fastforce 

lemma edge_is_card2: 
  assumes "e \<in> edge_set"
  shows "card e = 2"
proof -
  obtain u v where eq: "e = {u, v}" and "adj u v" using assms edge_set_def by blast
  then have "u \<noteq> v" using irrefl_alt by simp
  thus ?thesis using eq by simp
qed

lemma is_sgraph: "sgraph V edge_set"
  using is_graph_system edge_is_card2 sgraph_axioms_def by (intro_locales) auto

end

context sgraph
begin

lemma is_rel_irrefl_alt: 
  assumes "(u, v) \<in> adj_relation"
  shows "u \<noteq> v"
proof -
  have "vert_adj u v" using adj_relation_def assms by blast
  then have "{u, v} \<in> E" using vert_adj_def by simp
  then have "card {u, v} = 2" using two_edges by simp
  thus ?thesis by auto
qed

lemma is_rel_irrefl: "irrefl adj_relation"
  using irrefl_def is_rel_irrefl_alt by auto

lemma is_sgraph_rel: "sgraph_rel V adj_relation"
  by (unfold_locales) (simp add: is_rel_irrefl)

end

sublocale sgraph_rel \<subseteq> sgraph V "edge_set"
  rewrites "ulgraph.adj_relation edge_set = adj_rel"
  using is_sgraph rel_edges_is by simp_all

sublocale sgraph \<subseteq> sgraph_rel V "adj_relation"
  rewrites "ulgraph_rel.edge_set adj_relation = E"
  using is_sgraph_rel edges_rel_is by simp_all

end