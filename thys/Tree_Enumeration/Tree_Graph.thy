section \<open>Graphs and Trees\<close>

theory Tree_Graph
  imports Undirected_Graph_Theory.Undirected_Graphs_Root
begin

subsection \<open>Miscellaneous\<close>

definition (in ulgraph) loops :: "'a edge set" where
  "loops = {e\<in>E. is_loop e}"

definition (in ulgraph) sedges :: "'a edge set" where
  "sedges = {e\<in>E. is_sedge e}"

lemma (in ulgraph) union_loops_sedges: "loops \<union> sedges = E"
  unfolding loops_def sedges_def is_loop_def is_sedge_def using alt_edge_size by blast

lemma (in ulgraph) disjnt_loops_sedges: "disjnt loops sedges"
  unfolding disjnt_def loops_def sedges_def is_loop_def is_sedge_def by auto

lemma (in fin_ulgraph) finite_loops: "finite loops"
  unfolding loops_def using fin_edges by auto

lemma (in fin_ulgraph) finite_sedges: "finite sedges"
  unfolding sedges_def using fin_edges by auto

lemma (in ulgraph) edge_incident_vert: "e \<in> E \<Longrightarrow> \<exists>v\<in>V. vincident v e"
  using edge_size wellformed by (metis empty_not_edge equals0I vincident_def incident_edge_in_wf)

lemma (in ulgraph) Union_incident_edges: "(\<Union>v\<in>V. incident_edges v) = E"
  unfolding incident_edges_def using edge_incident_vert by auto


lemma (in ulgraph) induced_edges_mono: "V\<^sub>1 \<subseteq> V\<^sub>2 \<Longrightarrow> induced_edges V\<^sub>1 \<subseteq> induced_edges V\<^sub>2"
  using induced_edges_def by auto

definition (in graph_system) remove_vertex :: "'a \<Rightarrow> 'a pregraph" where
  "remove_vertex v = (V - {v}, {e\<in>E. \<not> vincident v e})"

lemma (in ulgraph) ex_neighbor_degree_not_0:
  assumes degree_non_0: "degree v \<noteq> 0"
    shows "\<exists>u\<in>V. vert_adj v u"
proof-
  have "\<exists>e\<in>E. v \<in> e" using degree_non_0 elem_exists_non_empty_set
    unfolding degree_def incident_sedges_def incident_loops_def vincident_def by auto
  then show ?thesis
    by (metis degree_non_0 in_mono is_isolated_vertex_def is_isolated_vertex_degree0 vert_adj_sym wellformed)
qed

lemma (in ulgraph) ex1_neighbor_degree_1:
  assumes degree_1: "degree v = 1"
  shows "\<exists>!u. vert_adj v u"
proof-
  have "card (incident_loops v) = 0" using degree_1 unfolding degree_def by auto
  then have incident_loops: "incident_loops v = {}" by (simp add: finite_incident_loops)
  then have card_incident_sedges: "card (incident_sedges v) = 1" using degree_1 unfolding degree_def by simp
  obtain u where vert_adj: "vert_adj v u" using degree_1 ex_neighbor_degree_not_0 by force
  then have "u \<noteq> v" using incident_loops unfolding incident_loops_def vert_adj_def by blast
  then have u_incident: "{v,u} \<in> incident_sedges v" using vert_adj unfolding incident_sedges_def vert_adj_def vincident_def by simp
  then have incident_sedges: "incident_sedges v = {{v,u}}" using card_incident_sedges
    by (simp add: comp_sgraph.card1_incident_imp_vert comp_sgraph.vincident_def)
  have "vert_adj v u' \<Longrightarrow> u' = u" for u'
  proof-
    assume v_u'_adj: "vert_adj v u'"
    then have "u' \<noteq> v" using incident_loops unfolding incident_loops_def vert_adj_def by blast
    then have "{v,u'} \<in> incident_sedges v" using v_u'_adj unfolding incident_sedges_def vert_adj_def vincident_def by simp
    then show "u' = u" using incident_sedges by force
  qed
  then show ?thesis using vert_adj by blast
qed

lemma (in ulgraph) degree_1_edge_partition:
  assumes degree_1: "degree v = 1"
  shows "E = {{THE u. vert_adj v u, v}} \<union> {e \<in> E. v \<notin> e}"
proof-
  have "card (incident_loops v) = 0" using degree_1 unfolding degree_def by auto
  then have incident_loops: "incident_loops v = {}" by (simp add: finite_incident_loops)
  then have "card (incident_sedges v) = 1" using degree_1 unfolding degree_def by simp
  then have card_incident_edges: "card (incident_edges v) = 1" using incident_loops incident_edges_union by simp
  obtain u where vert_adj: "vert_adj v u" using ex1_neighbor_degree_1 degree_1 by blast
  then have "{v, u} \<in> {e \<in> E. v \<in> e}" unfolding vert_adj_def by blast
  then have edges_incident_v: "{e \<in> E. v \<in> e} = {{v, u}}" using card_incident_edges card_1_singletonE singletonD
    unfolding incident_edges_def vincident_def by metis
  have u: "u = (THE u. vert_adj v u)" using vert_adj ex1_neighbor_degree_1 degree_1
    by (simp add: the1_equality)
  show ?thesis using edges_incident_v u by blast
qed

lemma (in sgraph) vert_adj_not_eq: "vert_adj u v \<Longrightarrow> u \<noteq> v"
  unfolding vert_adj_def using edge_vertices_not_equal by blast

subsection \<open>Degree\<close>

lemma (in ulgraph) empty_E_degree_0: "E = {} \<Longrightarrow> degree v = 0"
  using incident_edges_empty degree0_inc_edges_empt_iff unfolding incident_edges_def by simp

lemma (in fin_ulgraph) handshaking: "(\<Sum>v\<in>V. degree v) = 2 * card E"
  using fin_edges fin_ulgraph_axioms
proof (induction E)
  case empty
  then interpret g: fin_ulgraph V "{}" .
  show ?case using g.empty_E_degree_0 by simp
next
  case (insert e E')
  then interpret g': fin_ulgraph V "insert e E'" by blast
  interpret g: fin_ulgraph V E' using g'.wellformed g'.edge_size finV by (unfold_locales, auto)
  show ?case
  proof (cases "is_loop e")
    case True
    then obtain u where e: "e = {u}" using card_1_singletonE is_loop_def by blast
    then have inc_sedges: "\<And>v. g'.incident_sedges v = g.incident_sedges v" unfolding g'.incident_sedges_def g.incident_sedges_def by auto
    have "\<And>v. v \<noteq> u \<Longrightarrow> g'.incident_loops v = g.incident_loops v" unfolding g'.incident_loops_def g.incident_loops_def using e by auto
    then have degree_not_u: "\<And>v. v \<noteq> u \<Longrightarrow> g'.degree v = g.degree v" using inc_sedges unfolding g'.degree_def g.degree_def by auto
    have "g'.incident_loops u = g.incident_loops u \<union> {e}" unfolding g'.incident_loops_def g.incident_loops_def using e by auto
    then have degree_u: "g'.degree u = g.degree u + 2" using inc_sedges insert(2) g.finite_incident_loops g.incident_loops_def unfolding g'.degree_def g.degree_def by auto
    have "u \<in> V" using e g'.wellformed by blast
    then have "(\<Sum>v\<in>V. g'.degree v) = g'.degree u + (\<Sum>v\<in>V-{u}. g'.degree v)"
      by (simp add: finV sum.remove)
    also have "\<dots> = (\<Sum>v\<in>V. g.degree v) + 2" using degree_not_u degree_u sum.remove[OF finV \<open>u\<in>V\<close>, of g.degree] by auto
    also have "\<dots> = 2 * card (insert e E')" using insert g.fin_ulgraph_axioms by auto
    finally show ?thesis .
  next
    case False
    obtain u w where e: "e = {u,w}" using g'.obtain_edge_pair_adj by fastforce
    then have card_e: "card e = 2" using False g'.alt_edge_size is_loop_def by auto
    then have "u \<noteq> w" using card_2_iff using e by fastforce
    have inc_loops: "\<And>v. g'.incident_loops v = g.incident_loops v"
      unfolding g'.incident_loops_alt g.incident_loops_alt using False is_loop_def by auto
    have "\<And>v. v \<noteq> u \<Longrightarrow> v \<noteq> w \<Longrightarrow> g'.incident_sedges v = g.incident_sedges v"
      unfolding g'.incident_sedges_def g.incident_sedges_def g.vincident_def using e by auto
    then have degree_not_u_w: "\<And>v. v \<noteq> u \<Longrightarrow> v \<noteq> w \<Longrightarrow> g'.degree v = g.degree v"
      unfolding g'.degree_def g.degree_def using inc_loops by auto
    have "g'.incident_sedges u = g.incident_sedges u \<union> {e}"
      unfolding g'.incident_sedges_def g.incident_sedges_def g.vincident_def using e card_e by auto
    then have degree_u: "g'.degree u = g.degree u + 1"
      using inc_loops insert(2) g.fin_edges g.finite_inc_sedges g.incident_sedges_def
      unfolding g'.degree_def g.degree_def by auto
    have "g'.incident_sedges w = g.incident_sedges w \<union> {e}"
      unfolding g'.incident_sedges_def g.incident_sedges_def g.vincident_def using e card_e by auto
    then have degree_w: "g'.degree w = g.degree w + 1"
      using inc_loops insert(2) g.fin_edges g.finite_inc_sedges g.incident_sedges_def
      unfolding g'.degree_def g.degree_def by auto
    have inV: "u \<in> V" "w \<in> V-{u}" using e g'.wellformed \<open>u\<noteq>w\<close> by auto
    then have "(\<Sum>v\<in>V. g'.degree v) = g'.degree u + g'.degree w + (\<Sum>v\<in>V-{u}-{w}. g'.degree v)"
      using sum.remove finV by (metis add.assoc finite_Diff)
    also have "\<dots> = g.degree u + g.degree w + (\<Sum>v\<in>V-{u}-{w}. g.degree v) + 2"
      using degree_not_u_w degree_u degree_w by simp
    also have "\<dots> = (\<Sum>v\<in>V. g.degree v) + 2" using sum.remove finV inV by (metis add.assoc finite_Diff)
    also have "\<dots> = 2 * card (insert e E')" using insert g.fin_ulgraph_axioms by auto
    finally show ?thesis .
  qed
qed

lemma (in fin_ulgraph) degree_remove_adj_ne_vert:
  assumes "u \<noteq> v"
    and vert_adj: "vert_adj u v"
    and remove_vertex: "remove_vertex u = (V',E')"
  shows "ulgraph.degree E' v = degree v - 1"
proof-
  interpret G': fin_ulgraph V' E' using remove_vertex wellformed edge_size finV unfolding remove_vertex_def vincident_def
    by (unfold_locales, auto)
  have E': "E' = {e \<in> E. u \<notin> e}" using remove_vertex unfolding remove_vertex_def vincident_def by simp
  have incident_loops': "G'.incident_loops v = incident_loops v" unfolding incident_loops_def
    using \<open>u\<noteq>v\<close> E' G'.incident_loops_def by auto
  have uv_incident: "{u,v} \<in> incident_sedges v" using vert_adj \<open>u\<noteq>v\<close> unfolding vert_adj_def incident_sedges_def vincident_def by simp
  have uv_incident': "{u, v} \<notin> G'.incident_sedges v" unfolding G'.incident_sedges_def vincident_def using E' by blast
  have "e \<in> E \<Longrightarrow> u \<in> e \<Longrightarrow> v \<in> e \<Longrightarrow> card e = 2 \<Longrightarrow> e = {u,v}" for e
    using \<open>u\<noteq>v\<close> obtain_edge_pair_adj by blast
  then have "{e \<in> E. u \<in> e \<and> v \<in> e \<and> card e = 2} = {{u,v}}" using uv_incident unfolding incident_sedges_def by blast
  then have "incident_sedges v = G'.incident_sedges v \<union> {{u,v}}" unfolding G'.incident_sedges_def incident_sedges_def vincident_def using E' by blast
  then show ?thesis unfolding G'.degree_def degree_def using incident_loops' uv_incident' G'.finite_inc_sedges G'.fin_edges by auto
qed

lemma (in ulgraph) degree_remove_non_adj_vert:
  assumes "u \<noteq> v"
    and vert_non_adj: "\<not> vert_adj u v"
    and remove_vertex: "remove_vertex u = (V', E')"
  shows "ulgraph.degree E' v = degree v"
proof-
  interpret G': ulgraph V' E' using remove_vertex wellformed edge_size unfolding remove_vertex_def vincident_def
    by (unfold_locales, auto)
  have E': "E' = {e \<in> E. u \<notin> e}" using remove_vertex unfolding remove_vertex_def vincident_def by simp
  have incident_loops': "G'.incident_loops v = incident_loops v" unfolding incident_loops_def
    using \<open>u\<noteq>v\<close> E' G'.incident_loops_def by auto
  have "G'.incident_sedges v = incident_sedges v" unfolding G'.incident_sedges_def incident_sedges_def vincident_def
    using E' \<open>u\<noteq>v\<close> vincident_def vert_adj_edge_iff2 vert_non_adj by auto
  then show ?thesis using incident_loops' unfolding G'.degree_def degree_def by simp
qed

subsection \<open>Walks\<close>

lemma (in ulgraph) walk_edges_induced_edges: "is_walk p \<Longrightarrow> set (walk_edges p) \<subseteq> induced_edges (set p)"
  unfolding induced_edges_def is_walk_def by (induction p rule: walk_edges.induct) auto

lemma (in ulgraph) walk_edges_in_verts: "e \<in> set (walk_edges xs) \<Longrightarrow> e \<subseteq> set xs"
  by (induction xs rule: walk_edges.induct) auto

lemma (in ulgraph) is_walk_prefix: "is_walk (xs@ys) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> is_walk xs"
  unfolding is_walk_def using walk_edges_append_ss2 by fastforce

lemma (in ulgraph) split_walk_edge: "{x,y} \<in> set (walk_edges p) \<Longrightarrow>
  \<exists>xs ys. p = xs @ x # y # ys \<or> p = xs @ y # x # ys"
  by (induction p rule: walk_edges.induct) (auto, metis append_Nil doubleton_eq_iff, (metis append_Cons)+)

subsection \<open>Paths\<close>

lemma (in ulgraph) is_gen_path_wf: "is_gen_path p \<Longrightarrow> set p \<subseteq> V"
  unfolding is_gen_path_def using is_walk_wf by auto

lemma (in ulgraph) path_wf: "is_path p \<Longrightarrow> set p \<subseteq> V"
  by (simp add: is_path_walk is_walk_wf)

lemma (in fin_ulgraph) length_gen_path_card_V: "is_gen_path p \<Longrightarrow> walk_length p \<le> card V"
  by (metis card_mono distinct_card distinct_tl finV is_gen_path_def is_walk_def length_tl
      list.exhaust_sel order_trans set_subset_Cons walk_length_conv)

lemma (in fin_ulgraph) length_path_card_V: "is_path p \<Longrightarrow> length p \<le> card V"
  by (metis path_wf card_mono distinct_card finV is_path_def)

lemma (in ulgraph) is_gen_path_prefix: "is_gen_path (xs@ys) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> is_gen_path (xs)"
  unfolding is_gen_path_def using is_walk_prefix
  by (auto, metis Int_iff distinct.simps(2) emptyE last_appendL last_appendR last_in_set list.collapse)

lemma (in ulgraph) connecting_path_append: "connecting_path u w (xs@ys) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> connecting_path u (last xs) xs"
  unfolding connecting_path_def using is_gen_path_prefix by auto

lemma (in ulgraph) connecting_path_tl: "connecting_path u v (u # w # xs) \<Longrightarrow> connecting_path w v (w # xs)"
  unfolding connecting_path_def is_gen_path_def using is_walk_drop_hd distinct_tl by auto

lemma (in fin_ulgraph) obtain_longest_path:
  assumes "e \<in> E"
    and sedge: "is_sedge e"
  obtains p where "is_path p" "\<forall>s. is_path s \<longrightarrow> length s \<le> length p"
proof-
  let ?longest_path = "ARG_MAX length p. is_path p"
  obtain u v where e: "u \<noteq> v" "e = {u,v}" using sedge card_2_iff unfolding is_sedge_def by metis
  then have inV: "u \<in> V" "v \<in> V" using \<open>e\<in>E\<close> wellformed by auto
  then have path_ex: "is_path [u,v]" using e \<open>e\<in>E\<close> unfolding is_path_def is_open_walk_def is_walk_def by simp
  obtain p where p_is_path: "is_path p" and p_longest_path: "\<forall>s. is_path s \<longrightarrow> length s \<le> length p"
    using path_ex length_path_card_V ex_has_greatest_nat[of is_path "[u,v]" length gorder] by force
  then show ?thesis ..
qed

subsection \<open>Cycles\<close>

context ulgraph
begin

definition is_cycle2 :: "'a list \<Rightarrow> bool" where
  "is_cycle2 xs \<longleftrightarrow> is_cycle xs \<and> distinct (walk_edges xs)"

lemma loop_is_cycle2: "{v} \<in> E \<Longrightarrow> is_cycle2 [v, v]"
  unfolding is_cycle2_def is_cycle_alt is_walk_def using wellformed walk_length_conv by auto

end

lemma (in sgraph) cycle2_min_length:
  assumes cycle: "is_cycle2 c"
  shows "walk_length c \<ge> 3"
proof-
  consider "c = []" | "\<exists>v1. c = [v1]" | "\<exists>v1 v2. c = [v1, v2]" | "\<exists>v1 v2 v3. c = [v1, v2, v3]" | "\<exists>v1 v2 v3 v4 vs. c = v1#v2#v3#v4#vs"
    by (metis list.exhaust_sel)
  then show ?thesis using cycle walk_length_conv singleton_not_edge unfolding is_cycle2_def is_cycle_alt is_walk_def by (cases, auto)
qed

lemma (in fin_ulgraph) length_cycle_card_V: "is_cycle c \<Longrightarrow> walk_length c \<le> Suc (card V)"
  using length_gen_path_card_V unfolding is_gen_path_def is_cycle_alt by fastforce

lemma (in ulgraph) is_cycle_connecting_path: "is_cycle (u#v#xs) \<Longrightarrow> connecting_path v u (v#xs)"
  unfolding is_cycle_def connecting_path_def is_closed_walk_def is_gen_path_def using is_walk_drop_hd by auto

lemma (in ulgraph) cycle_edges_notin_tl: "is_cycle2 (u#v#xs) \<Longrightarrow> {u,v} \<notin> set (walk_edges (v#xs))"
  unfolding is_cycle2_def by simp

subsection \<open>Subgraphs\<close>

locale ulsubgraph = subgraph V\<^sub>H E\<^sub>H V\<^sub>G E\<^sub>G +
  G: ulgraph V\<^sub>G E\<^sub>G for V\<^sub>H E\<^sub>H V\<^sub>G E\<^sub>G
begin

interpretation H: ulgraph V\<^sub>H E\<^sub>H
  using is_subgraph_ulgraph G.ulgraph_axioms by auto

lemma is_walk: "H.is_walk xs \<Longrightarrow> G.is_walk xs"
  unfolding H.is_walk_def G.is_walk_def using verts_ss edges_ss by blast

lemma is_closed_walk: "H.is_closed_walk xs \<Longrightarrow> G.is_closed_walk xs"
  unfolding H.is_closed_walk_def G.is_closed_walk_def using is_walk by blast

lemma is_gen_path: "H.is_gen_path p \<Longrightarrow> G.is_gen_path p"
  unfolding H.is_gen_path_def G.is_gen_path_def using is_walk by blast

lemma connecting_path: "H.connecting_path u v p \<Longrightarrow> G.connecting_path u v p"
  unfolding H.connecting_path_def G.connecting_path_def using is_gen_path by blast

lemma is_cycle: "H.is_cycle c \<Longrightarrow> G.is_cycle c"
  unfolding H.is_cycle_def G.is_cycle_def using is_closed_walk by blast

lemma is_cycle2: "H.is_cycle2 c \<Longrightarrow> G.is_cycle2 c"
  unfolding H.is_cycle2_def G.is_cycle2_def using is_cycle by blast

lemma vert_connected: "H.vert_connected u v \<Longrightarrow> G.vert_connected u v"
  unfolding H.vert_connected_def G.vert_connected_def using connecting_path by blast

lemma is_connected_set: "H.is_connected_set V' \<Longrightarrow> G.is_connected_set V'"
  unfolding H.is_connected_set_def G.is_connected_set_def using vert_connected by blast

end

lemma (in graph_system) subgraph_remove_vertex: "remove_vertex v = (V', E') \<Longrightarrow> subgraph V' E' V E"
  using wellformed unfolding remove_vertex_def vincident_def by (unfold_locales, auto)

subsection \<open>Connectivity\<close>

lemma (in ulgraph) connecting_path_connected_set:
  assumes conn_path: "connecting_path u v p"
  shows "is_connected_set (set p)"
proof-
  have "\<forall>w\<in>set p. vert_connected u w"
  proof
    fix w assume "w \<in> set p"
    then obtain xs ys where "p = xs@[w]@ys" using split_list by fastforce
    then have "connecting_path u w (xs@[w])" using conn_path unfolding connecting_path_def using is_gen_path_prefix by (auto simp: hd_append)
    then show "vert_connected u w" unfolding vert_connected_def by blast
  qed
  then show ?thesis using vert_connected_rev vert_connected_trans unfolding is_connected_set_def by blast
qed

lemma (in ulgraph) vert_connected_neighbors:
  assumes "{v,u} \<in> E"
  shows "vert_connected v u"
proof-
  have "connecting_path v u [v,u]" unfolding connecting_path_def is_gen_path_def is_walk_def using assms wellformed by auto
  then show ?thesis unfolding vert_connected_def by auto
qed

lemma (in ulgraph) connected_empty_E:
  assumes empty: "E = {}"
    and connected: "vert_connected u v"
  shows "u = v"
proof (rule ccontr)
  assume "u \<noteq> v"
  then obtain p where conn_path: "connecting_path u v p" using connected unfolding vert_connected_def by blast
  then obtain e where "e \<in> set (walk_edges p)" using \<open>u\<noteq>v\<close> connecting_path_length_bound unfolding walk_length_def by fastforce
  then have "e \<in> E" using conn_path unfolding connecting_path_def is_gen_path_def is_walk_def by blast
  then show False using empty by blast
qed

lemma (in fin_ulgraph) degree_0_not_connected:
  assumes degree_0: "degree v = 0"
    and "u \<noteq> v"
  shows "\<not> vert_connected v u"
proof
  assume connected: "vert_connected v u"
  then obtain p where conn_path: "connecting_path v u p" unfolding vert_connected_def by blast
  then have "walk_length p \<ge> 1" using \<open>u\<noteq>v\<close> connecting_path_length_bound by metis
  then have "length p \<ge> 2" using walk_length_conv by simp
  then obtain w p' where "p = v#w#p'" using walk_length_conv conn_path unfolding connecting_path_def
    by (metis assms(2) is_gen_path_def is_walk_not_empty2 last_ConsL list.collapse)
  then have inE: "{v,w} \<in> E" using conn_path unfolding connecting_path_def is_gen_path_def is_walk_def by simp
  then have "{v,w} \<in> incident_edges v" unfolding incident_edges_def vincident_def by simp
  then show False using degree0_inc_edges_empt_iff fin_edges degree_0 by blast
qed

lemma (in fin_connected_ulgraph) degree_not_0:
  assumes "card V \<ge> 2"
    and inV: "v \<in> V"
  shows "degree v \<noteq> 0"
proof-
  obtain u where "u \<in> V" and "u \<noteq> v" using assms
    by (metis card_eq_0_iff card_le_Suc0_iff_eq less_eq_Suc_le nat_less_le not_less_eq_eq numeral_2_eq_2)
  then show ?thesis using degree_0_not_connected inV vertices_connected by blast
qed

lemma (in connected_ulgraph) V_E_empty: "E = {} \<Longrightarrow> \<exists>v. V = {v}"
  using connected_empty_E connected not_empty unfolding is_connected_set_def
  by (metis ex_in_conv insert_iff mk_disjoint_insert)

lemma (in connected_ulgraph) vert_connected_remove_edge:
  assumes e: "{u,v} \<in> E"
  shows "\<forall>w\<in>V. ulgraph.vert_connected V (E - {{u,v}}) w u \<or> ulgraph.vert_connected V (E - {{u,v}}) w v"
proof
  fix w assume "w\<in>V"
  interpret g': ulgraph V "E - {{u,v}}" using wellformed edge_size by (unfold_locales, auto)
  have inV: "u \<in> V" "v \<in> V" using e wellformed by auto
  obtain p where conn_path: "connecting_path w v p" using connected inV \<open>w\<in>V\<close> unfolding is_connected_set_def vert_connected_def by blast
  then show "g'.vert_connected w u \<or> g'.vert_connected w v"
  proof (cases "{u,v} \<in> set (walk_edges p)")
    case True
    assume walk_edge: "{u,v} \<in> set (walk_edges p)"
    then show ?thesis
    proof (cases "w = v")
      case True
      then show ?thesis using inV g'.vert_connected_id by blast
    next
      case False
      then have distinct: "distinct p" using conn_path by (simp add: connecting_path_def is_gen_path_distinct)
      have "u \<in> set p" using walk_edge walk_edges_in_verts by blast
      obtain xs ys where p_split: "p = xs @ u # v # ys \<or> p = xs @ v # u # ys" using split_walk_edge[OF walk_edge] by blast
      have v_notin_ys: "v \<notin> set ys" using distinct p_split by auto
      have "last p = v" using conn_path unfolding connecting_path_def by simp
      then have p: "p = (xs@[u]) @ [v]" using v_notin_ys p_split last_in_set last_appendR
        by (metis append.assoc append_Cons last.simps list.discI self_append_conv2)
      then have conn_path_u: "connecting_path w u (xs@[u])" using connecting_path_append conn_path by fastforce
      have "v \<notin> set (xs@[u])" using p distinct by auto
      then have "{u,v} \<notin> set (walk_edges (xs@[u]))" using walk_edges_in_verts by blast
      then have "g'.connecting_path w u (xs@[u])" using conn_path_u
        unfolding g'.connecting_path_def connecting_path_def g'.is_gen_path_def is_gen_path_def g'.is_walk_def is_walk_def by blast
      then show ?thesis unfolding g'.vert_connected_def by blast
    qed
  next
    case False
    then have "g'.connecting_path w v p" using conn_path
      unfolding g'.connecting_path_def connecting_path_def g'.is_gen_path_def is_gen_path_def g'.is_walk_def is_walk_def by blast
    then show ?thesis unfolding g'.vert_connected_def by blast
  qed
qed

lemma (in ulgraph) vert_connected_remove_cycle_edge:
  assumes cycle: "is_cycle2 (u#v#xs)"
    shows "ulgraph.vert_connected V (E - {{u,v}}) u v"
proof-
  interpret g': ulgraph V "E - {{u,v}}" using wellformed edge_size by (unfold_locales, auto)
  have conn_path: "connecting_path v u (v#xs)" using cycle is_cycle_connecting_path unfolding is_cycle2_def by blast
  have "{u,v} \<notin> set (walk_edges (v#xs))" using cycle unfolding is_cycle2_def by simp
  then have "g'.connecting_path v u (v#xs)" using conn_path
    unfolding g'.connecting_path_def connecting_path_def g'.is_gen_path_def is_gen_path_def g'.is_walk_def is_walk_def by blast
  then show ?thesis using g'.vert_connected_rev unfolding g'.vert_connected_def by blast
qed

lemma (in connected_ulgraph) connected_remove_cycle_edges:
  assumes cycle: "is_cycle2 (u#v#xs)"
  shows "connected_ulgraph V (E - {{u,v}})"
proof-
  interpret g': ulgraph V "E - {{u,v}}" using wellformed edge_size by (unfold_locales, auto)
  have "g'.vert_connected x y" if inV: "x \<in> V" "y \<in> V" for x y
  proof-
    have e: "{u,v} \<in> E" using cycle unfolding is_cycle2_def is_cycle_alt is_walk_def by auto
    show ?thesis using vert_connected_remove_cycle_edge[OF cycle] vert_connected_remove_edge[OF e] g'.vert_connected_trans g'.vert_connected_rev inV by metis
  qed
  then show ?thesis using not_empty by (unfold_locales, auto simp: g'.is_connected_set_def)
qed

lemma (in connected_ulgraph) connected_remove_leaf:
  assumes degree: "degree l = 1"
    and remove_vertex: "remove_vertex l = (V', E')"
  shows "ulgraph.is_connected_set V' E' V'"
proof-
  interpret g': ulgraph V' E' using remove_vertex wellformed edge_size
    unfolding remove_vertex_def vincident_def by (unfold_locales, auto)
  have V': "V' = V - {l}" using remove_vertex unfolding remove_vertex_def by simp
  have E': "E' = {e\<in>E. l \<notin> e}" using remove_vertex unfolding remove_vertex_def vincident_def by simp
  have "u \<in> V' \<Longrightarrow> v \<in> V' \<Longrightarrow> g'.vert_connected u v" for u v
  proof-
    assume inV': "u \<in> V'" "v \<in> V'"
    then have inV: "u \<in> V" "v \<in> V" using remove_vertex unfolding remove_vertex_def by auto
    then obtain p where conn_path: "connecting_path u v p" using vertices_connected_path by blast
    show ?thesis
    proof (cases "u = v")
      case True
      then show ?thesis using g'.vert_connected_id inV' by simp
    next
      case False
      then have distinct: "distinct p" using conn_path unfolding connecting_path_def is_gen_path_def by blast
      have l_notin_p: "l \<notin> set p"
      proof
        assume l_in_p: "l \<in> set p"
        then obtain xs ys where p: "p = xs @ l # ys" by (meson split_list)
        have "l \<noteq> u" "l \<noteq> v" using inV' remove_vertex unfolding remove_vertex_def by auto
        then have "xs \<noteq> []" using p conn_path unfolding connecting_path_def by fastforce
        then obtain x where last_xs: "last xs = x" by simp
        then have "x \<noteq> l" using distinct p \<open>xs\<noteq>[]\<close> by auto
        have "{x,l} \<in> set (walk_edges p)" using walk_edges_append_union \<open>xs\<noteq>[]\<close> unfolding p
          by (simp add: walk_edges_append_union last_xs)
        then have xl_incident: "{x,l} \<in> incident_sedges l" using conn_path \<open>x\<noteq>l\<close>
          unfolding connecting_path_def is_gen_path_def is_walk_def incident_sedges_def vincident_def by auto

        have "ys \<noteq> []" using \<open>l\<noteq>v\<close> p conn_path unfolding connecting_path_def by fastforce
        then obtain y ys' where ys: "ys = y # ys'" by (meson list.exhaust)
        then have "y \<noteq> l" using distinct p by auto
        then have "{y,l} \<in> set (walk_edges p)" using p ys conn_path walk_edges_append_ss1 by fastforce
        then have yl_incident: "{y,l} \<in> incident_sedges l" using conn_path \<open>y\<noteq>l\<close>
          unfolding connecting_path_def is_gen_path_def is_walk_def incident_sedges_def vincident_def by auto

        have card_loops: "card (incident_loops l) = 0" using degree unfolding degree_def by auto
        have "x \<noteq> y" using distinct last_xs \<open>xs\<noteq>[]\<close> unfolding p ys by fastforce
        then have "{x,l} \<noteq> {y,l}" by (metis doubleton_eq_iff)
        then have "card (incident_sedges l) \<noteq> 1" using xl_incident yl_incident
          by (metis card_1_singletonE singletonD)
        then have "degree l \<noteq> 1" using card_loops unfolding degree_def by simp
        then show False using degree ..
      qed
      then have "set (walk_edges p) \<subseteq> E'" using walk_edges_in_verts conn_path E' unfolding connecting_path_def is_gen_path_def is_walk_def by blast
      then have "g'.connecting_path u v p" using conn_path V' l_notin_p
        unfolding g'.connecting_path_def connecting_path_def g'.is_gen_path_def is_gen_path_def g'.is_walk_def is_walk_def by blast
      then show ?thesis unfolding g'.vert_connected_def by blast
    qed
  qed
  then show ?thesis unfolding g'.is_connected_set_def by blast
qed

lemma (in connected_sgraph) connected_two_graph_edges:
  assumes "u \<noteq> v"
    and V: "V = {u,v}"
  shows "E = {{u,v}}"
proof-
  obtain p where conn_path: "connecting_path u v p" using V vertices_connected_path by blast
  then obtain p' where p: "p = u # p' @ [v]" using \<open>u\<noteq>v\<close> unfolding connecting_path_def is_gen_path_def 
    by (metis append_Nil is_walk_not_empty2 list.exhaust_sel list.sel(1) snoc_eq_iff_butlast tl_append2)
  have "distinct p" using conn_path \<open>u\<noteq>v\<close> unfolding connecting_path_def is_gen_path_def by auto
  then have "p' = []" using V conn_path is_gen_path_wf append_is_Nil_conv last_in_set self_append_conv2
    unfolding connecting_path_def p by fastforce
  then have edge_in_E: "{u,v} \<in> E" using \<open>u\<noteq>v\<close> conn_path
    unfolding p connecting_path_def is_gen_path_def is_walk_def by simp
  have "E \<subseteq> {{}, {u}, {v}, {u,v}}" using wellformed V by blast
  then show ?thesis using two_edges edge_in_E by fastforce
qed

subsection "Connected components"

context ulgraph
begin

abbreviation "vert_connected_rel \<equiv> {(u,v). vert_connected u v}"

definition connected_components :: "'a set set" where
  "connected_components = V // vert_connected_rel"

definition connected_component_of :: "'a \<Rightarrow> 'a set" where
  "connected_component_of v = vert_connected_rel `` {v}"

lemma vert_connected_rel_on_V: "vert_connected_rel \<subseteq> V \<times> V"
  using vert_connected_wf by auto

lemma vert_connected_rel_refl: "refl_on V vert_connected_rel"
  unfolding refl_on_def using vert_connected_rel_on_V vert_connected_id by simp

lemma vert_connected_rel_sym: "sym vert_connected_rel"
  unfolding sym_def using vert_connected_rev by simp

lemma vert_connected_rel_trans: "trans vert_connected_rel"
  unfolding trans_def using vert_connected_trans by blast

lemma equiv_vert_connected: "equiv V vert_connected_rel"
  unfolding equiv_def using vert_connected_rel_refl vert_connected_rel_sym vert_connected_rel_trans by blast

lemma connected_component_non_empty: "V' \<in> connected_components \<Longrightarrow> V' \<noteq> {}"
  unfolding connected_components_def using equiv_vert_connected in_quotient_imp_non_empty by auto

lemma connected_component_connected: "V' \<in> connected_components \<Longrightarrow> is_connected_set V'"
  unfolding connected_components_def is_connected_set_def using quotient_eq_iff[OF equiv_vert_connected, of V' V'] by simp

lemma connected_component_wf: "V' \<in> connected_components \<Longrightarrow> V' \<subseteq> V"
  by (simp add: connected_component_connected is_connected_set_wf)

lemma connected_component_of_self: "v \<in> V \<Longrightarrow> v \<in> connected_component_of v"
  unfolding connected_component_of_def using vert_connected_id by blast

lemma conn_comp_of_conn_comps: "v \<in> V \<Longrightarrow> connected_component_of v \<in> connected_components"
  unfolding connected_components_def quotient_def connected_component_of_def by blast

lemma Un_connected_components: "connected_components = connected_component_of ` V"
  unfolding connected_components_def connected_component_of_def quotient_def by blast

lemma connected_component_subgraph: "V' \<in> connected_components \<Longrightarrow> subgraph V' (induced_edges V') V E"
  using induced_is_subgraph connected_component_wf by simp

lemma connected_components_connected2:
  assumes conn_comp: "V' \<in> connected_components"
  shows "ulgraph.is_connected_set V' (induced_edges V') V'"
proof-
  interpret subg: subgraph V' "induced_edges V'" V E using connected_component_subgraph conn_comp by simp
  interpret g': ulgraph V' "induced_edges V'" using subg.is_subgraph_ulgraph ulgraph_axioms by simp
  have "\<And>u v. u \<in> V' \<Longrightarrow> v \<in> V' \<Longrightarrow> g'.vert_connected u v"
  proof-
    fix u v assume "u \<in> V'" "v \<in> V'"
    then obtain p where conn_path: "connecting_path u v p" using connected_component_connected conn_comp unfolding is_connected_set_def vert_connected_def by blast
    then have u_in_p: "u \<in> set p" unfolding connecting_path_def is_gen_path_def is_walk_def by force
    then have set_p: "set p \<subseteq> V'" using connecting_path_connected_set[OF conn_path]
        in_quotient_imp_closed[OF equiv_vert_connected] conn_comp \<open>u \<in> V'\<close>
      unfolding is_connected_set_def connected_components_def by blast
    then have "set (g'.walk_edges p) \<subseteq> induced_edges V'"
      using walk_edges_induced_edges induced_edges_mono conn_path unfolding connecting_path_def is_gen_path_def by blast
    then have "g'.connecting_path u v p"
      using set_p conn_path
      unfolding g'.connecting_path_def g'.connecting_path_def g'.is_gen_path_def g'.is_walk_def
      unfolding connecting_path_def connecting_path_def is_gen_path_def is_walk_def by auto
    then show "g'.vert_connected u v" unfolding g'.vert_connected_def by blast
  qed
  then show ?thesis unfolding g'.is_connected_set_def by blast
qed

lemma vert_connected_connected_component: "C \<in> connected_components \<Longrightarrow> u \<in> C \<Longrightarrow> vert_connected u v \<Longrightarrow> v \<in> C"
  unfolding connected_components_def using equiv_vert_connected in_quotient_imp_closed by fastforce

lemma connected_components_connected_ulgraphs:
  assumes conn_comp: "V' \<in> connected_components"
  shows "connected_ulgraph V' (induced_edges V')"
proof-
  interpret subg: subgraph V' "induced_edges V'" V E using connected_component_subgraph conn_comp by simp
  interpret g': ulgraph V' "induced_edges V'" using subg.is_subgraph_ulgraph ulgraph_axioms by simp
  show ?thesis using conn_comp connected_component_non_empty connected_components_connected2 by (unfold_locales, auto)
qed

lemma connected_components_partition_on_V: "partition_on V connected_components"
  using partition_on_quotient equiv_vert_connected unfolding connected_components_def by blast

lemma Union_connected_components: "\<Union>connected_components = V"
  using connected_components_partition_on_V unfolding partition_on_def by blast

lemma disjoint_connected_components: "disjoint connected_components"
  using connected_components_partition_on_V unfolding partition_on_def by blast

lemma Union_induced_edges_connected_components: "\<Union>(induced_edges ` connected_components) = E"
proof-
  have "\<exists>C\<in>connected_components. e \<in> induced_edges C" if "e \<in> E" for e
  proof-
    obtain u v where e: "e = {u,v}" by (meson \<open>e \<in> E\<close> obtain_edge_pair_adj)
    then have "vert_connected u v" using that vert_connected_neighbors by blast
    then have "v \<in> connected_component_of u" unfolding connected_component_of_def by simp
    then have "e \<in> induced_edges (connected_component_of u)" using connected_component_of_self wellformed \<open>e\<in>E\<close> unfolding e induced_edges_def by auto
    then show ?thesis using conn_comp_of_conn_comps e wellformed \<open>e\<in>E\<close> by auto
  qed 
  then show ?thesis using connected_component_wf induced_edges_ss by blast
qed

lemma connected_components_empty_E:
  assumes empty: "E = {}"
  shows "connected_components = {{v} | v. v\<in>V}"
proof-
  have "\<forall>v\<in>V. vert_connected_rel``{v} = {v}" using vert_connected_id connected_empty_E empty by auto
  then show ?thesis unfolding connected_components_def quotient_def by auto
qed

lemma connected_iff_connected_components:
  assumes non_empty: "V \<noteq> {}"
    shows "is_connected_set V \<longleftrightarrow> connected_components = {V}"
proof
  assume "is_connected_set V"
  then have "\<forall>v\<in>V. connected_component_of v = V" unfolding connected_component_of_def is_connected_set_def using vert_connected_wf by blast
  then show "connected_components = {V}" unfolding quotient_def connected_component_of_def connected_components_def using non_empty by auto
next
  show "connected_components = {V} \<Longrightarrow> is_connected_set V"
    using connected_component_connected unfolding connected_components_def is_connected_set_def by auto
qed

end

lemma (in connected_ulgraph) connected_components[simp]: "connected_components = {V}"
  using connected connected_iff_connected_components not_empty by simp

lemma (in fin_ulgraph) finite_connected_components: "finite connected_components"
  unfolding connected_components_def using finV vert_connected_rel_on_V finite_quotient by blast

lemma (in fin_ulgraph) finite_connected_component: "C \<in> connected_components \<Longrightarrow> finite C"
  using connected_component_wf finV finite_subset by blast

lemma (in connected_ulgraph) connected_components_remove_edges:
  assumes edge: "{u,v} \<in> E"
  shows "ulgraph.connected_components V (E - {{u,v}}) =
    {ulgraph.connected_component_of V (E - {{u,v}}) u, ulgraph.connected_component_of V (E - {{u,v}}) v}"
proof-
  interpret g': ulgraph V "E - {{u,v}}" using wellformed edge_size by (unfold_locales, auto)
  have inV: "u \<in> V" "v \<in> V" using edge wellformed by auto
  have "\<forall>w\<in>V. g'.connected_component_of w = g'.connected_component_of u \<or> g'.connected_component_of w = g'.connected_component_of v"
    using vert_connected_remove_edge[OF edge] g'.equiv_vert_connected equiv_class_eq unfolding g'.connected_component_of_def by fast
  then show ?thesis unfolding g'.connected_components_def quotient_def g'.connected_component_of_def using inV by auto
qed

lemma (in ulgraph) connected_set_connected_component:
  assumes conn_set: "is_connected_set C"
    and non_empty: "C \<noteq> {}"
    and "\<And>u v. {u,v} \<in> E \<Longrightarrow> u \<in> C \<Longrightarrow> v \<in> C"
  shows "C \<in> connected_components"
proof-
  have walk_subset_C: "is_walk xs \<Longrightarrow>  hd xs \<in> C \<Longrightarrow> set xs \<subseteq> C" for xs
  proof (induction xs rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc x xs)
    then show ?case
    proof (cases xs rule: rev_exhaust)
      case Nil
      then show ?thesis using snoc by auto
    next
      fix ys y assume xs: "xs = ys @ [y]"
      then have "is_walk xs" using is_walk_prefix snoc(2) by blast
      then have set_xs_C: "set xs \<subseteq> C" using snoc xs is_walk_not_empty2 hd_append2 by metis
      have yx_E: "{y,x} \<in> E" using snoc(2) walk_edges_app unfolding xs is_walk_def by simp
      have "x \<in> C" using assms(3)[OF yx_E] set_xs_C unfolding xs by simp
      then show ?thesis using set_xs_C by simp
    qed
  qed
  obtain u where "u \<in> C" using non_empty by blast
  then have "u \<in> V" using conn_set is_connected_set_wf by blast
  have "v \<in> C" if vert_connected: "vert_connected u v" for v
  proof-
    obtain p where "connecting_path u v p" using vert_connected unfolding vert_connected_def by blast
    then show ?thesis using walk_subset_C[of p] \<open>u\<in>C\<close> is_walk_def last_in_set unfolding connecting_path_def is_gen_path_def by auto
  qed
  then have "connected_component_of u = C" using assms \<open>u\<in>C\<close> unfolding connected_component_of_def is_connected_set_def by auto
  then show ?thesis using conn_comp_of_conn_comps \<open>u\<in>V\<close> by blast
qed

lemma (in ulgraph) subset_conn_comps_if_Union:
  assumes A_subset_conn_comps: "A \<subseteq> connected_components"
    and Un_A: "\<Union>A = V"
  shows "A = connected_components"
proof (rule ccontr)
  assume "A \<noteq> connected_components"
  then obtain C where C_conn_comp: "C \<in> connected_components " "C \<notin> A" using A_subset_conn_comps by blast
  then obtain v where "v \<in> C" using connected_component_non_empty by blast
  then have "v \<notin> V" using A_subset_conn_comps Un_A connected_components_partition_on_V C_conn_comp
    using partition_onD4 by fastforce
  then show False using C_conn_comp connected_component_wf \<open>v\<in>C\<close> by auto
qed

lemma (in connected_ulgraph) exists_adj_vert_removed:
  assumes "v \<in> V"
    and remove_vertex: "remove_vertex v = (V',E')"
    and conn_component: "C \<in> ulgraph.connected_components V' E'"
  shows "\<exists>u\<in>C. vert_adj v u"
proof-
  have V': "V' = V - {v}" and E': "E' = {e\<in>E. v \<notin> e}" using remove_vertex unfolding remove_vertex_def vincident_def by auto
  interpret subg: subgraph "V - {v}" "{e\<in>E. v \<notin> e}" V E using subgraph_remove_vertex remove_vertex V' E' by metis
  interpret g': ulgraph "V - {v}" "{e\<in>E. v \<notin> e}" using subg.is_subgraph_ulgraph ulgraph_axioms by blast
  obtain c where "c \<in> C" using g'.connected_component_non_empty conn_component V' E' by blast
  then have "c \<in> V'" using g'.connected_component_wf conn_component V' E' by blast
  then have "c \<in> V" using subg.verts_ss V' by blast
  then obtain p where conn_path: "connecting_path v c p" using \<open>v\<in>V\<close> vertices_connected_path by blast  
  have "v \<noteq> c" using \<open>c\<in>V'\<close> remove_vertex unfolding remove_vertex_def by blast
  then obtain u p' where p: "p = v # u # p'" using conn_path
    by (metis connecting_path_def is_gen_path_def is_walk_def last.simps list.exhaust_sel)
  then have conn_path_uc: "connecting_path u c (u#p')" using conn_path connecting_path_tl unfolding p by blast
  have v_notin_p': "v \<notin> set (u#p')" using conn_path \<open>v\<noteq>c\<close> unfolding p connecting_path_def is_gen_path_def by auto
  then have "g'.connecting_path u c (u#p')" using conn_path_uc v_notin_p' walk_edges_in_verts
    unfolding g'.connecting_path_def connecting_path_def g'.is_gen_path_def is_gen_path_def g'.is_walk_def is_walk_def
    by blast 
  then have "g'.vert_connected u c" unfolding g'.vert_connected_def by blast
  then have "u \<in> C" using \<open>c\<in>C\<close> conn_component g'.vert_connected_connected_component g'.vert_connected_rev unfolding V' E' by blast
  have "vert_adj v u" using conn_path unfolding p connecting_path_def is_gen_path_def is_walk_def vert_adj_def by auto
  then show ?thesis using \<open>u\<in>C\<close> by blast
qed

subsection \<open>Trees\<close>

locale tree = fin_connected_ulgraph +
  assumes no_cycles: "\<not> is_cycle2 c"
begin

sublocale fin_connected_sgraph
  using alt_edge_size no_cycles loop_is_cycle2 card_1_singletonE connected
  by (unfold_locales, metis, simp)

end

locale spanning_tree = ulgraph V E + T: tree V T for V E T +
  assumes subgraph: "T \<subseteq> E"

lemma (in fin_connected_ulgraph) has_spanning_tree: "\<exists>T. spanning_tree V E T"
  using fin_connected_ulgraph_axioms
proof (induction "card E" arbitrary: E)
  case 0
  then interpret g: fin_connected_ulgraph V edges by blast
  have edges: "edges = {}" using g.fin_edges 0 by simp
  then obtain v where V: "V = {v}" using g.V_E_empty by blast
  interpret g': fin_connected_sgraph V edges using g.connected edges by (unfold_locales, auto)
  interpret t: tree V edges using g.length_cycle_card_V g'.cycle2_min_length g.is_cycle2_def V by (unfold_locales, fastforce)
  have "spanning_tree V edges edges" by (unfold_locales, auto) 
  then show ?case by blast
next
  case (Suc m)
  then interpret g: fin_connected_ulgraph V edges by blast
  show ?case
  proof (cases "\<forall>c. \<not>g.is_cycle2 c")
    case True
    then have "spanning_tree V edges edges" by (unfold_locales, auto)
    then show ?thesis by blast
  next
    case False
    then obtain c where cycle: "g.is_cycle2 c" by blast
    then have "length c \<ge> 2" unfolding g.is_cycle2_def g.is_cycle_alt walk_length_conv by auto
    then obtain u v xs where c: "c = u#v#xs" by (metis Suc_le_length_iff numeral_2_eq_2)
    then have g': "fin_connected_ulgraph V (edges - {{u,v}})" using finV g.connected_remove_cycle_edges
      by (metis connected_ulgraph_def cycle fin_connected_ulgraph_def fin_graph_system.intro fin_graph_system_axioms.intro fin_ulgraph.intro ulgraph_def)
    have "{u,v} \<in> edges" using cycle unfolding c g.is_cycle2_def g.is_cycle_alt g.is_walk_def by auto
    then obtain T where "spanning_tree V (edges - {{u,v}}) T" using Suc card_Diff_singleton g' by fastforce
    then have "spanning_tree V edges T" unfolding spanning_tree_def spanning_tree_axioms_def using g.ulgraph_axioms by blast
    then show ?thesis by blast
  qed
qed

context tree
begin

definition leaf :: "'a \<Rightarrow> bool" where
  "leaf v \<longleftrightarrow> degree v = 1"

definition leaves :: "'a set" where
  "leaves = {v. leaf v}"

definition non_trivial :: "bool" where
  "non_trivial \<longleftrightarrow> card V \<ge> 2"

lemma obtain_2_verts:
  assumes "non_trivial"
  obtains u v where "u \<in> V" "v \<in> V" "u \<noteq> v"
  using assms unfolding non_trivial_def
  by (meson diameter_obtains_path_vertices)

lemma leaf_in_V: "leaf v \<Longrightarrow> v \<in> V"
  unfolding leaf_def using degree_none by force

lemma exists_leaf:
  assumes "non_trivial"
  shows "\<exists>v\<in>V. leaf v"
proof-
  obtain p where is_path: "is_path p" and longest_path: "\<forall>s. is_path s \<longrightarrow> length s \<le> length p"
    using obtain_longest_path 
    by (metis One_nat_def assms connected connected_sgraph_axioms connected_sgraph_def degree_0_not_connected
        is_connected_setD is_edge_or_loop is_isolated_vertex_def is_isolated_vertex_degree0 is_loop_def
        n_not_Suc_n numeral_2_eq_2 obtain_2_verts sgraph.two_edges vert_adj_def)
  then obtain l v xs where p: "p = l#v#xs"
    by (metis is_open_walk_def is_path_def is_walk_not_empty2 last_ConsL list.exhaust_sel)
  then have lv_incident: "{l,v} \<in> incident_edges l" using is_path
    unfolding incident_edges_def vincident_def is_path_def is_open_walk_def is_walk_def by simp
  have "\<And>e. e\<in>E \<Longrightarrow> e \<noteq> {l,v} \<Longrightarrow> e \<notin> incident_edges l"
  proof
    fix e
    assume e_in_E: "e \<in> E"
      and not_lv: "e \<noteq> {l,v}"
      and incident: "e \<in> incident_edges l"
    obtain u where e: "e = {l,u}" using e_in_E obtain_edge_pair_adj incident
      unfolding incident_edges_def vincident_def by auto
    then have "u \<noteq> l" using e_in_E edge_vertices_not_equal by blast
    have "u \<noteq> v" using e not_lv by auto
    have u_in_V: "u \<in> V" using e_in_E e wellformed by blast
    then show False
    proof (cases "u \<in> set p")
      case True
      then have "u \<in> set xs" using \<open>u\<noteq>l\<close> \<open>u\<noteq>v\<close> p by simp
      then obtain ys zs where "xs = ys@u#zs" by (meson split_list)
      then have "is_cycle2 (u#l#v#ys@[u])"
        using is_path \<open>u\<noteq>l\<close> \<open>u\<noteq>v\<close> e_in_E distinct_edgesI walk_edges_append_ss2 walk_edges_in_verts
        unfolding is_cycle2_def is_cycle_def p is_path_def is_closed_walk_def is_open_walk_def is_walk_def e walk_length_conv
        by (auto, metis insert_commute, fastforce+)
      then show ?thesis using no_cycles by blast
    next
      case False
      then have "is_path (u#p)" using is_path u_in_V e_in_E
        unfolding is_path_def is_open_walk_def is_walk_def e p by (auto, (metis insert_commute)+)
      then show False using longest_path by auto
    qed
  qed
  then have "incident_edges l = {{l,v}}" using lv_incident unfolding incident_edges_def by blast
  then have leaf: "leaf l" unfolding leaf_def alt_degree_def by simp
  then show ?thesis using leaf_in_V by blast
qed

lemma tree_remove_leaf:
  assumes leaf: "leaf l"
    and remove_vertex: "remove_vertex l = (V',E')"
  shows "tree V' E'"
proof-
  interpret g': ulgraph V' E' using remove_vertex wellformed edge_size unfolding remove_vertex_def vincident_def
    by (unfold_locales, auto)
  interpret subg: ulsubgraph V' E' V E using subgraph_remove_vertex ulgraph_axioms remove_vertex
    unfolding ulsubgraph_def by blast
  have V': "V' = V - {l}" using remove_vertex unfolding remove_vertex_def by blast
  have E': "E' = {e\<in>E. l \<notin> e}" using remove_vertex unfolding remove_vertex_def vincident_def by blast
  have "\<exists>v\<in>V. v \<noteq> l" using leaf unfolding leaf_def
    by (metis One_nat_def is_independent_alt is_isolated_vertex_def is_isolated_vertex_degree0
        n_not_Suc_n radius_obtains singletonI singleton_independent_set)
  then have "V' \<noteq> {}" using remove_vertex unfolding remove_vertex_def vincident_def by blast
  then have "g'.is_connected_set V'" using connected_remove_leaf leaf remove_vertex unfolding leaf_def by blast
  then show ?thesis using \<open>V'\<noteq>{}\<close> finV subg.is_cycle2 V' E' no_cycles by (unfold_locales, auto)
qed

end

lemma tree_induct [case_names singolton insert, induct set: tree]:
  assumes tree: "tree V E"
    and trivial: "\<And>v. tree {v} {} \<Longrightarrow> P {v} {}"
    and insert: "\<And>l v V E. tree V E \<Longrightarrow> P V E \<Longrightarrow> l \<notin> V \<Longrightarrow> v \<in> V \<Longrightarrow> {l,v} \<notin> E \<Longrightarrow> tree.leaf (insert {l,v} E) l \<Longrightarrow> P (insert l V) (insert {l,v} E)"
  shows "P V E"
  using tree
proof (induction "card V" arbitrary: V E)
  case 0
  then interpret tree V E by simp
  have "V = {}" using finV 0(1) by simp
  then show ?case using not_empty by blast
next
  case (Suc n)
  then interpret t: tree V E by simp
  show ?case
  proof (cases "card V = 1")
    case True
    then obtain v where V: "V = {v}" using card_1_singletonE by blast
    then have "E = {}"
      using True subset_antisym t.edge_incident_vert t.vincident_def t.singleton_not_edge t.wellformed
      by fastforce
    then show ?thesis using trivial t.tree_axioms V by simp
  next
    case False
    then have card_V: "card V \<ge> 2" using Suc by simp
    then obtain l where leaf: "t.leaf l" using t.exists_leaf t.non_trivial_def by blast
    then obtain e where inc_edges: "t.incident_edges l = {e}"
      unfolding t.leaf_def t.alt_degree_def using card_1_singletonE by blast
    then have e_in_E: "e \<in> E" unfolding t.incident_edges_def by blast
    then obtain u where e: "e = {l,u}" using t.two_edges card_2_iff inc_edges unfolding t.incident_edges_def t.vincident_def
      by (metis (no_types, lifting) empty_iff insert_commute insert_iff mem_Collect_eq)
    then have "l \<noteq> u" using e_in_E t.edge_vertices_not_equal by blast
    have "u \<in> V" using e e_in_E t.wellformed by blast
    let ?V' = "V - {l}"
    let ?E' = "E - {{l,u}}"
    have remove_vertex: "t.remove_vertex l = (?V', ?E')"
      using inc_edges e unfolding t.remove_vertex_def t.incident_edges_def by blast
    then have t': "tree ?V' ?E'" using t.tree_remove_leaf leaf by blast
    have "l \<in> V" using leaf t.leaf_in_V by blast
    then have P': "P ?V' ?E'" using Suc t' by auto
    show ?thesis using insert[OF t' P'] Suc leaf \<open>u\<in>V\<close> \<open>l\<noteq>u\<close> \<open>l \<in> V\<close> e e_in_E by (auto, metis insert_Diff)
  qed
qed

context tree
begin

lemma card_V_card_E: "card V = Suc (card E)"
  using tree_axioms
proof (induction V E)
  case (singolton v)
  then show ?case by auto
next
  case (insert l v V' E')
  then interpret t': tree V' E' by simp
  show ?case using t'.finV t'.fin_edges insert by simp
qed

end

lemma card_E_treeI:
  assumes fin_conn_sgraph: "fin_connected_ulgraph V E"
    and card_V_E: "card V = Suc (card E)"
  shows "tree V E"
proof-
  interpret G: fin_connected_ulgraph V E using fin_conn_sgraph .
  obtain T where T: "spanning_tree V E T" using G.has_spanning_tree by blast
  show ?thesis
  proof (cases "E = T")
    case True
    then show ?thesis using T unfolding spanning_tree_def by blast
  next
    case False
    then have "card E > card T" using T G.fin_edges unfolding spanning_tree_def spanning_tree_axioms_def
      by (simp add: psubsetI psubset_card_mono)
    then show ?thesis using tree.card_V_card_E T card_V_E unfolding spanning_tree_def by fastforce
  qed
qed

context tree
begin

lemma add_vertex_tree:
  assumes "v \<notin> V"
    and  "w \<in> V"
  shows "tree (insert v V) (insert {v,w} E)"
proof -
  let ?V' = "insert v V" and ?E' = "insert {v,w} E"

  have cardV: "card {v,w} = 2" using card_2_iff assms by auto
  then interpret t': ulgraph ?V' ?E'
    using wellformed assms two_edges by (unfold_locales, auto)

  interpret subg: ulsubgraph V E ?V' ?E' by (unfold_locales, auto)

  have connected: "t'.is_connected_set ?V'"
    unfolding t'.is_connected_set_def
    using subg.vert_connected t'.vert_connected_neighbors t'.vert_connected_trans
      t'.vert_connected_id vertices_connected t'.ulgraph_axioms ulgraph_axioms assms t'.vert_connected_rev
    by simp metis

  then have fin_connected_ulgraph: "fin_connected_ulgraph ?V' ?E'" using finV by (unfold_locales, auto)

  from assms have "{v,w} \<notin> E" using wellformed_alt_fst by auto
  then have "card ?E' = Suc (card E)" using fin_edges card_insert_if by auto
  then have "card ?V' = Suc (card ?E')" using card_V_card_E assms wellformed_alt_fst finV card_insert_if by auto

  then show ?thesis using card_E_treeI fin_connected_ulgraph by auto
qed

lemma tree_connected_set:
  assumes non_empty: "V' \<noteq> {}"
    and subg: "V' \<subseteq> V"
    and connected_V': "ulgraph.is_connected_set V' (induced_edges V') V'"
  shows "tree V' (induced_edges V')"
proof-
  interpret subg: subgraph V' "induced_edges V'" V E using induced_is_subgraph subg by simp
  interpret g': ulgraph V' "induced_edges V'" using subg.is_subgraph_ulgraph ulgraph_axioms by blast
  interpret subg: ulsubgraph V' "induced_edges V'" V E by unfold_locales
  show ?thesis using connected_V' subg.is_cycle2 no_cycles finV subg non_empty rev_finite_subset by (unfold_locales) (auto, blast)
qed

lemma unique_adj_vert_removed:
  assumes "v \<in> V"
    and remove_vertex: "remove_vertex v = (V',E')"
    and conn_component: "C \<in> ulgraph.connected_components V' E'"
  shows "\<exists>!u\<in>C. vert_adj v u"
proof-
  interpret subg: ulsubgraph V' E' V E using remove_vertex subgraph_remove_vertex ulgraph_axioms ulsubgraph.intro by metis
  interpret g': ulgraph V' E' using subg.is_subgraph_ulgraph ulgraph_axioms by simp
  obtain u where "u \<in> C" and adj_vu: "vert_adj v u" using exists_adj_vert_removed using assms by blast
  have "w = u" if "w \<in> C" and adj_vw: "vert_adj v w" for w
  proof (rule ccontr)
    assume "w \<noteq> u"
    obtain p where g'_conn_path: "g'.connecting_path w u p" using \<open>u\<in>C\<close> \<open>w\<in>C\<close> conn_component
        g'.connected_component_connected g'.is_connected_setD g'.vert_connected_def by blast
    then have v_notin_p: "v \<notin> set p" using remove_vertex unfolding g'.connecting_path_def g'.is_gen_path_def g'.is_walk_def remove_vertex_def by blast
    have conn_path: "connecting_path w u p" using g'_conn_path subg.connecting_path by simp
    then obtain p' where p: "p = w # p' @ [u]" unfolding connecting_path_def using \<open>w\<noteq>u\<close>
      by (metis hd_Cons_tl last.simps last_rev rev_is_Nil_conv snoc_eq_iff_butlast)
    then have "walk_edges (v#p@[v]) = {v,w} # walk_edges ((w # p') @ [u,v])" by simp
    also have "\<dots> = {v,w} # walk_edges p @ [{u,v}]" unfolding p using walk_edges_app by (metis Cons_eq_appendI)
    finally have walk_edges: "walk_edges (v#p@[v]) = {v,w} # walk_edges p @ [{v,u}]" by (simp add: insert_commute)
    then have "is_cycle (v#p@[v])" using conn_path adj_vu adj_vw \<open>w\<noteq>u\<close> \<open>v\<in>V\<close> g'.walk_length_conv singleton_not_edge v_notin_p
      unfolding connecting_path_def is_cycle_def is_gen_path_def is_closed_walk_def is_walk_def p vert_adj_def by auto
    then have "is_cycle2 (v#p@[v])" using \<open>w\<noteq>u\<close> v_notin_p walk_edges_in_verts unfolding is_cycle2_def walk_edges
      by (auto simp: doubleton_eq_iff is_cycle_alt distinct_edgesI)
    then show False using no_cycles by blast
  qed
  then show ?thesis using \<open>u\<in>C\<close> adj_vu by blast
qed

lemma non_trivial_card_E: "non_trivial \<Longrightarrow> card E \<ge> 1"
  using card_V_card_E unfolding non_trivial_def by simp

lemma V_Union_E: "non_trivial \<Longrightarrow> V = \<Union>E"
  using tree_axioms
proof (induction V E)
  case (singolton v) 
  then interpret t: tree "{v}" "{}" by simp
  show ?case using singolton unfolding t.non_trivial_def by simp
next
  case (insert l v V' E')
  then interpret t: tree V' E' by simp
  show ?case
  proof (cases "card V' = 1")
    case True
    then have V: "V' = {v}" using insert(3) card_1_singletonE by blast
    then have E: "E' = {}" using t.fin_edges t.card_V_card_E by fastforce
    then show ?thesis unfolding E V by simp
  next
    case False
    then have "t.non_trivial" using t.card_V_card_E unfolding t.non_trivial_def by simp
    then show ?thesis using insert by blast
  qed
qed

end

lemma singleton_tree: "tree {v} {}"
proof-
  interpret g: fin_ulgraph "{v}" "{}" by (unfold_locales, auto)
  show ?thesis using g.is_walk_def g.walk_length_def by (unfold_locales, auto simp: g.is_connected_set_singleton g.is_cycle2_def g.is_cycle_alt)
qed

lemma tree2:
  assumes "u \<noteq> v"
    shows "tree {u,v} {{u,v}}"
proof-
  interpret ulgraph "{u,v}" "{{u,v}}" using \<open>u\<noteq>v\<close> by unfold_locales auto
  have "fin_connected_ulgraph {u,v} {{u,v}}" by unfold_locales
    (auto simp: is_connected_set_def vert_connected_id vert_connected_neighbors vert_connected_rev)
  then show ?thesis using card_E_treeI \<open>u\<noteq>v\<close> by fastforce
qed

subsection \<open>Graph Isomorphism\<close>

locale graph_isomorphism =
  G: graph_system V\<^sub>G E\<^sub>G for V\<^sub>G E\<^sub>G +
  fixes V\<^sub>H E\<^sub>H f
  assumes bij_f: "bij_betw f V\<^sub>G V\<^sub>H"
  and edge_preserving: "((`) f) ` E\<^sub>G = E\<^sub>H"
begin

lemma inj_f: "inj_on f V\<^sub>G"
  using bij_f unfolding bij_betw_def by blast

lemma V\<^sub>H_def: "V\<^sub>H = f ` V\<^sub>G"
  using bij_f unfolding bij_betw_def by blast

definition "inv_iso \<equiv> the_inv_into V\<^sub>G f"

lemma graph_system_H: "graph_system V\<^sub>H E\<^sub>H"
  using G.wellformed edge_preserving bij_f bij_betw_imp_surj_on by unfold_locales blast

interpretation H: graph_system V\<^sub>H E\<^sub>H using graph_system_H .

lemma graph_isomorphism_inv: "graph_isomorphism V\<^sub>H E\<^sub>H V\<^sub>G E\<^sub>G inv_iso"
proof (unfold_locales)
  show "bij_betw inv_iso V\<^sub>H V\<^sub>G" unfolding inv_iso_def using bij_betw_the_inv_into bij_f by blast
next
  have "\<forall>v\<in>V\<^sub>G. the_inv_into V\<^sub>G f (f v) = v" using bij_f by (simp add: bij_betw_imp_inj_on the_inv_into_f_f)
  then have "\<forall>e\<in>E\<^sub>G. (\<lambda>v. the_inv_into V\<^sub>G f (f v)) ` e = e" using G.wellformed
    by (simp add: subset_iff)
  then show "((`) inv_iso)` E\<^sub>H = E\<^sub>G" unfolding inv_iso_def by (simp add: edge_preserving[symmetric] image_comp)
qed

interpretation inv_iso: graph_isomorphism V\<^sub>H E\<^sub>H V\<^sub>G E\<^sub>G inv_iso using graph_isomorphism_inv .

end

fun graph_isomorph :: "'a pregraph \<Rightarrow> 'b pregraph \<Rightarrow> bool" (infix "\<simeq>" 50) where
  "(V\<^sub>G,E\<^sub>G) \<simeq> (V\<^sub>H,E\<^sub>H) \<longleftrightarrow> (\<exists>f. graph_isomorphism V\<^sub>G E\<^sub>G V\<^sub>H E\<^sub>H f)"

lemma (in graph_system) graph_isomorphism_id: "graph_isomorphism V E V E id"
  by unfold_locales auto

lemma (in graph_system) graph_isomorph_refl: "(V,E) \<simeq> (V,E)"
  using graph_isomorphism_id by auto

lemma graph_isomorph_sym: "symp (\<simeq>)"
  using graph_isomorphism.graph_isomorphism_inv unfolding symp_def by fastforce

lemma graph_isomorphism_trans: "graph_isomorphism V\<^sub>G E\<^sub>G V\<^sub>H E\<^sub>H f \<Longrightarrow> graph_isomorphism V\<^sub>H E\<^sub>H V\<^sub>F E\<^sub>F g \<Longrightarrow> graph_isomorphism V\<^sub>G E\<^sub>G V\<^sub>F E\<^sub>F (g o f)"
  unfolding graph_isomorphism_def graph_isomorphism_axioms_def using bij_betw_trans by (auto, blast)

lemma graph_isomorph_trans: "transp (\<simeq>)"
  using graph_isomorphism_trans unfolding transp_def by fastforce

end