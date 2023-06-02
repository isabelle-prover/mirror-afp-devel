section \<open>Rooted Trees\<close>

theory Rooted_Tree
imports Tree_Graph "HOL-Library.FSet"
begin

datatype tree = Node "tree list"

fun tree_size :: "tree \<Rightarrow> nat" where
  "tree_size (Node ts) = Suc (\<Sum>t\<leftarrow>ts. tree_size t)"

fun height :: "tree \<Rightarrow> nat" where
  "height (Node []) = 0"
| "height (Node ts) = Suc (Max (height ` set ts))"

text \<open>Convenient case splitting and induction for trees\<close>

lemma tree_cons_exhaust[case_names Nil Cons]:
  "(t = Node [] \<Longrightarrow> P) \<Longrightarrow> (\<And>r ts. t = Node (r # ts) \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases t) (metis list.exhaust)

lemma tree_rev_exhaust[case_names Nil Snoc]:
  "(t = Node [] \<Longrightarrow> P) \<Longrightarrow> (\<And>ts r. t = Node (ts @ [r]) \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases t) (metis rev_exhaust)

lemma tree_cons_induct[case_names Nil Cons]:
  assumes "P (Node [])"
    and "\<And>t ts. P t \<Longrightarrow> P (Node ts) \<Longrightarrow> P (Node (t#ts))"
  shows "P t"
proof (induction "size_tree t" arbitrary: t rule: less_induct)
  case less
  then show ?case using assms by (cases t rule: tree_cons_exhaust) auto
qed

fun lexord_tree where
  "lexord_tree t (Node []) \<longleftrightarrow> False"
| "lexord_tree (Node []) r \<longleftrightarrow> True"
| "lexord_tree (Node (t#ts)) (Node (r#rs)) \<longleftrightarrow> lexord_tree t r \<or> (t = r \<and> lexord_tree (Node ts) (Node rs))"

fun mirror :: "tree \<Rightarrow> tree" where
  "mirror (Node ts) = Node (map mirror (rev ts))"

instantiation tree :: linorder
begin

definition
  tree_less_def: "(t::tree) < r \<longleftrightarrow> lexord_tree (mirror t) (mirror r)"

definition
  tree_le_def: "(t :: tree) \<le> r \<longleftrightarrow> t < r \<or> t = r"  

lemma lexord_tree_empty2[simp]: "lexord_tree (Node []) r \<longleftrightarrow> r \<noteq> Node []"
  by (cases r rule: tree_cons_exhaust) auto

lemma mirror_empty[simp]: "mirror t = Node [] \<longleftrightarrow> t = Node []"
  by (cases t) auto

lemma mirror_not_empty[simp]: "mirror t \<noteq> Node [] \<longleftrightarrow> t \<noteq> Node []"
  by (cases t) auto

lemma tree_le_empty[simp]: "Node [] \<le> t"
  unfolding tree_le_def tree_less_def using mirror_not_empty by auto

lemma tree_less_empty_iff: "Node [] < t \<longleftrightarrow> t \<noteq> Node []"
  unfolding tree_less_def by simp

lemma not_tree_less_empty[simp]: "\<not> t < Node []"
  unfolding tree_less_def by simp

lemma tree_le_empty2_iff[simp]: "t \<le> Node [] \<longleftrightarrow> t = Node []"
  unfolding tree_le_def by simp

lemma lexord_tree_antisym: "lexord_tree t r \<Longrightarrow> \<not> lexord_tree r t"
  by (induction r t rule: lexord_tree.induct) auto

lemma tree_less_antisym: "(t::tree) < r \<Longrightarrow> \<not> r < t"
  unfolding tree_less_def using lexord_tree_antisym by blast

lemma lexord_tree_not_eq: "lexord_tree t r \<Longrightarrow> t \<noteq> r"
  by (induction r t rule: lexord_tree.induct) auto

lemma tree_less_not_eq: "(t::tree) < r \<Longrightarrow> t \<noteq> r"
  unfolding tree_less_def using lexord_tree_not_eq by blast

lemma lexord_tree_irrefl: "\<not> lexord_tree t t"
  using lexord_tree_not_eq by blast

lemma tree_less_irrefl: "\<not> (t::tree) < t"
  unfolding tree_less_def using lexord_tree_irrefl by blast

lemma lexord_tree_eq_iff: "\<not> lexord_tree t r \<and> \<not> lexord_tree r t \<longleftrightarrow> t = r"
  using lexord_tree_empty2 by (induction t r rule: lexord_tree.induct, fastforce+)

lemma mirror_mirror: "mirror (mirror t) = t"
  by (induction t rule: mirror.induct) (simp add: map_idI rev_map)

lemma mirror_inj: "mirror t = mirror r \<Longrightarrow> t = r"
  using mirror_mirror by metis

lemma tree_less_eq_iff: "\<not> (t::tree) < r \<and> \<not> r < t \<longleftrightarrow> t = r"
  unfolding tree_less_def using lexord_tree_eq_iff mirror_inj by blast

lemma lexord_tree_trans: "lexord_tree t r \<Longrightarrow> lexord_tree r s \<Longrightarrow> lexord_tree t s"
proof (induction t s arbitrary: r rule: lexord_tree.induct)
  case (1 t)
  then show ?case by auto
next
  case (2 va vb)
  then show ?case by auto
next
  case (3 t ts s ss)
  then show ?case by (cases r rule: tree_cons_exhaust) auto
qed

instance
proof
  fix t r s :: tree
  show "t < r \<longleftrightarrow> t \<le> r \<and> \<not> r \<le> t" unfolding tree_le_def using tree_less_antisym tree_less_irrefl by auto
  show "t \<le> t" unfolding tree_le_def by simp
  show "t \<le> r \<Longrightarrow> r \<le> t \<Longrightarrow> t = r" unfolding tree_le_def using tree_less_antisym by blast
  show "t \<le> r \<or> r \<le> t" unfolding tree_le_def using tree_less_eq_iff by blast
  show "t \<le> r \<Longrightarrow> r \<le> s \<Longrightarrow> t \<le> s" unfolding tree_le_def tree_less_def using lexord_tree_trans by blast
qed

end

lemma tree_size_children: "tree_size (Node ts) = Suc n \<Longrightarrow> t \<in> set ts \<Longrightarrow> tree_size t \<le> n"
  by (auto simp: le_add1 sum_list_map_remove1)

lemma tree_size_ge_1: "tree_size t \<ge> 1"
  by (cases t) auto

lemma tree_size_ne_0: "tree_size t \<noteq> 0"
  by (cases t) auto

lemma tree_size_1_iff: "tree_size t = 1 \<longleftrightarrow> t = Node []"
  using tree_size_ne_0 by (cases t rule: tree_cons_exhaust) auto

lemma length_children: "tree_size (Node ts) = Suc n \<Longrightarrow> length ts \<le> n"
  by (induction ts arbitrary: n, auto, metis add_mono plus_1_eq_Suc tree_size_ge_1)


lemma height_Node_cons: "height (Node (t#ts)) \<ge> Suc (height t)"
  by auto

lemma height_0_iff: "height t = 0 \<Longrightarrow> t = Node []"
  using height.elims by blast

lemma height_children: "height (Node ts) = Suc n \<Longrightarrow> t \<in> set ts \<Longrightarrow> height t \<le> n"
  by (metis List.finite_set Max_ge diff_Suc_1 finite_imageI height.elims imageI nat.simps(3) tree.inject)

lemma height_children_le_height: "\<forall>t \<in> set ts. height t \<le> n \<Longrightarrow> height (Node ts) \<le> Suc n"
  by (cases ts) auto


lemma mirror_iff: "mirror t = Node ts \<longleftrightarrow> t = Node (map mirror (rev ts))"
  by (metis mirror.simps mirror_mirror)

lemma mirror_append: "mirror (Node (ts@rs)) = Node (map mirror (rev rs) @ map mirror (rev ts))"
  by (induction ts) auto


lemma lexord_tree_snoc: "lexord_tree (Node ts) (Node (ts@[t]))"
  by (induction ts) auto

lemma tree_less_cons: "Node ts < Node (t#ts)"
  unfolding tree_less_def using lexord_tree_snoc by simp

lemma tree_le_cons: "Node ts \<le> Node (t#ts)"
  unfolding tree_le_def using tree_less_cons by simp

lemma tree_less_cons': "t \<le> Node rs \<Longrightarrow> t < Node (r#rs)"
  using tree_less_cons by (simp add: order_le_less_trans)

lemma tree_less_snoc2_iff[simp]: "Node (ts@[t]) < Node (rs@[r]) \<longleftrightarrow> t < r \<or> (t = r \<and> Node ts < Node rs)"
  unfolding tree_less_def using mirror_inj by auto

lemma tree_le_snoc2_iff[simp]: "Node (ts@[t]) \<le> Node (rs@[r]) \<longleftrightarrow> t < r \<or> (t = r \<and> Node ts \<le> Node rs)"
  unfolding tree_le_def by auto

lemma lexord_tree_cons2[simp]: "lexord_tree (Node (ts@[t])) (Node (ts@[r])) \<longleftrightarrow> lexord_tree t r"
  by (induction ts) (auto simp: lexord_tree_irrefl)

lemma tree_less_cons2[simp]: "Node (t#ts) < Node (r#ts) \<longleftrightarrow> t < r"
  unfolding tree_less_def using lexord_tree_cons2 by simp

lemma tree_le_cons2[simp]: "Node (t#ts) \<le> Node (r#ts) \<longleftrightarrow> t \<le> r"
  unfolding tree_le_def using tree_less_cons2 by blast

lemma tree_less_sorted_snoc: "sorted (ts@[r]) \<Longrightarrow> Node ts < Node (ts@[r])"
  unfolding tree_less_def by (induction ts rule: rev_induct, auto,
      metis leD lexord_tree_eq_iff sorted2 sorted_wrt_append tree_less_def,
      metis dual_order.strict_iff_not list.set_intros(2) nle_le sorted2 sorted_append tree_less_def)

lemma lexord_tree_comm_prefix[simp]: "lexord_tree (Node (ss@ts)) (Node (ss@rs)) \<longleftrightarrow> lexord_tree (Node ts) (Node rs)"
  using lexord_tree_antisym by (induction ss) auto

lemma less_tree_comm_suffix[simp]: "Node (ts@ss) < Node (rs@ss) \<longleftrightarrow> Node ts < Node rs"
  unfolding tree_less_def by simp

lemma tree_le_comm_suffix[simp]: "Node (ts@ss) \<le> Node (rs@ss) \<longleftrightarrow> Node ts \<le> Node rs"
  unfolding tree_le_def by simp

lemma tree_less_comm_suffix2: "t < r \<Longrightarrow> Node (ts@t#ss) < Node (r#ss)"
  unfolding tree_less_def using lexord_tree_comm_prefix by simp

lemma lexord_tree_append[simp]: "lexord_tree (Node ts) (Node (ts@rs)) \<longleftrightarrow> rs \<noteq> []"
  using lexord_tree_irrefl by (induction ts) auto

lemma tree_less_append[simp]: "Node ts < Node (rs@ts) \<longleftrightarrow> rs \<noteq> []"
  unfolding tree_less_def by simp

lemma tree_le_append: "Node ts \<le> Node (ss@ts)"
  unfolding tree_le_def by simp

lemma tree_less_singleton_iff[simp]: "Node (ts@[t]) < Node [r] \<longleftrightarrow> t < r"
  unfolding tree_less_def by simp

lemma tree_le_singleton_iff[simp]: "Node (ts@[t]) \<le> Node [r] \<longleftrightarrow> t < r \<or> (t = r \<and> ts = [])"
  unfolding tree_le_def by auto

lemma lexord_tree_nested: "lexord_tree t (Node [t])"
proof (induction t rule: tree_cons_induct)
  case Nil
  then show ?case by auto
next
  case (Cons t ts)
  then show ?case by (cases t rule: tree_cons_exhaust) auto
qed

lemma tree_less_nested: "t < Node [t]"
  unfolding tree_less_def using lexord_tree_nested by auto

lemma tree_le_nested: "t \<le> Node [t]"
  unfolding tree_le_def using tree_less_nested by auto

lemma lexord_tree_iff:
  "lexord_tree t r \<longleftrightarrow> (\<exists>ts t' ss rs r'. t = Node (ss @ t' # ts) \<and> r = Node (ss @ r' # rs) \<and> lexord_tree t' r') \<or> (\<exists>ts rs. rs \<noteq> [] \<and> t = Node ts \<and> r = Node (ts @ rs))" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
  proof-
    assume lexord: "lexord_tree t r"
    obtain ts where ts: "t = Node ts" by (cases t) auto
    obtain rs where rs: "r = Node rs" by (cases r) auto
    obtain ss ts' rs' where prefix: "ts = ss @ ts' \<and> rs = ss @ rs' \<and> (ts' = [] \<or> rs' = [] \<or> hd ts' \<noteq> hd rs')" using longest_common_prefix by blast
    then have "ts' = [] \<or> lexord_tree (hd ts') (hd rs')" using lexord unfolding ts rs
      by (auto, metis lexord_tree.simps(1) lexord_tree.simps(3) list.exhaust_sel)
    then show ?thesis using prefix
      by (metis append.right_neutral lexord lexord_tree.simps(1) lexord_tree_comm_prefix list.exhaust_sel rs ts)
  qed
  show "?r \<Longrightarrow> ?l" by auto
qed

lemma tree_less_iff: "t < r \<longleftrightarrow> (\<exists>ts t' ss rs r'. t = Node (ts @ t' # ss) \<and> r = Node (rs @ r' # ss) \<and> t' < r') \<or> (\<exists>ts rs. rs \<noteq> [] \<and> t = Node ts \<and> r = Node (rs @ ts))" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
    unfolding tree_less_def using lexord_tree_iff[of "mirror t" "mirror r", unfolded mirror_iff] 
    by (simp, metis append_Nil lexord_tree_eq_iff mirror_mirror)
next
  show "?r \<Longrightarrow> ?l"
    by (auto simp: order_le_neq_trans tree_le_append,
        meson dual_order.strict_trans1 tree_le_append tree_less_comm_suffix2)
qed

lemma tree_empty_cons_lt_le: "r < Node (Node [] # ts) \<Longrightarrow> r \<le> Node ts"
proof (induction ts arbitrary: r rule: rev_induct)
  case Nil
  then show ?case by (cases r rule: tree_rev_exhaust) auto
next
  case (snoc x xs)
  then show ?case
  proof (cases r rule: tree_rev_exhaust)
    case Nil
    then show ?thesis by auto
  next
    case (Snoc rs r1)
    then show ?thesis using snoc by (auto, (metis append_Cons tree_less_snoc2_iff)+)
  qed
qed


fun regular :: "tree \<Rightarrow> bool" where
  "regular (Node ts) \<longleftrightarrow> sorted ts \<and> (\<forall>t\<in>set ts. regular t)"

definition n_trees :: "nat \<Rightarrow> tree set" where
  "n_trees n = {t. tree_size t = n}"

definition regular_n_trees :: "nat \<Rightarrow> tree set" where
  "regular_n_trees n = {t. tree_size t = n \<and> regular t}"


subsection \<open>Rooted Graphs\<close>

type_synonym 'a rpregraph = "('a set) \<times> ('a edge set) \<times> 'a" 

locale rgraph = graph_system +
  fixes r
  assumes root_wf: "r \<in> V"

locale rtree = tree + rgraph
begin

definition subtrees :: "'a rpregraph set" where
  "subtrees =
    (let (V',E') = remove_vertex r
    in (\<lambda>C. (C, graph_system.induced_edges E' C, THE r'. r' \<in> C \<and> vert_adj r r')) ` ulgraph.connected_components V' E')"

lemma rtree_subtree:
  assumes subtree: "(S,E\<^sub>S,r\<^sub>S) \<in> subtrees"
  shows "rtree S E\<^sub>S r\<^sub>S"
proof-
  obtain V' E' where remove_vertex: "remove_vertex r = (V', E')" by fastforce
  interpret subg: ulsubgraph V' E' V E unfolding ulsubgraph_def using subgraph_remove_vertex subtree ulgraph_axioms remove_vertex by blast
  interpret g': fin_ulgraph V' E'
    by (simp add: fin_graph_system_axioms fin_ulgraph_def subg.is_finite_subgraph subg.is_subgraph_ulgraph ulgraph_axioms)
  have conn_component: "S \<in> g'.connected_components" using subtree remove_vertex unfolding subtrees_def by auto
  then interpret subg': subgraph S E\<^sub>S V' E' using g'.connected_component_subgraph subtree remove_vertex unfolding subtrees_def by auto
  interpret subg': ulsubgraph S E\<^sub>S V' E' by unfold_locales
  interpret S: connected_ulgraph S E\<^sub>S using g'.connected_components_connected_ulgraphs conn_component subtree remove_vertex unfolding subtrees_def by auto
  interpret S: fin_connected_ulgraph S E\<^sub>S using subg'.verts_ss g'.finV by unfold_locales (simp add: finite_subset)
  interpret S: tree S E\<^sub>S using subg.is_cycle2 subg'.is_cycle2 no_cycles by (unfold_locales, blast)
  show ?thesis using theI'[OF unique_adj_vert_removed[OF root_wf remove_vertex conn_component]]
      subtree remove_vertex by unfold_locales (auto simp: subtrees_def)
qed

lemma finite_subtrees: "finite subtrees"
proof-
  obtain V' E' where remove_vertex: "remove_vertex r = (V', E')" by fastforce
  then interpret subg: subgraph V' E' V E using subgraph_remove_vertex by auto
  interpret g': fin_ulgraph V' E'
    by (simp add: fin_graph_system_axioms fin_ulgraph_def subg.is_finite_subgraph subg.is_subgraph_ulgraph ulgraph_axioms)
  show ?thesis using g'.finite_connected_components remove_vertex unfolding subtrees_def by simp
qed

lemma remove_root_subtrees:
  assumes remove_vertex: "remove_vertex r = (V',E')"
    and conn_component: "C \<in> ulgraph.connected_components V' E'"
  shows "rtree C (graph_system.induced_edges E' C) (THE r'. r' \<in> C \<and> vert_adj r r')"
proof-
  interpret subg: ulsubgraph V' E' V E unfolding ulsubgraph_def using subgraph_remove_vertex remove_vertex ulgraph_axioms by blast
  interpret g': fin_ulgraph V' E'
    by (simp add: fin_graph_system_axioms fin_ulgraph_def subg.is_finite_subgraph subg.is_subgraph_ulgraph ulgraph_axioms)
  interpret subg': ulsubgraph C "graph_system.induced_edges E' C" V' E'
    by (simp add: conn_component g'.connected_component_subgraph g'.ulgraph_axioms ulsubgraph.intro)
  interpret C: fin_connected_ulgraph C "graph_system.induced_edges E' C"
    by (simp add: fin_connected_ulgraph.intro fin_ulgraph.intro g'.fin_graph_system_axioms
        g'.ulgraph_axioms subg'.is_finite_subgraph subg'.is_subgraph_ulgraph conn_component
        g'.connected_components_connected_ulgraphs)
  interpret C: tree C "graph_system.induced_edges E' C" using subg.is_cycle2 subg'.is_cycle2 no_cycles by (unfold_locales, blast)
  show ?thesis using theI'[OF unique_adj_vert_removed[OF root_wf remove_vertex conn_component]] by unfold_locales simp
qed

end

subsection \<open>Rooted Graph Isomorphism\<close>

fun app_rgraph_isomorphism :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a rpregraph \<Rightarrow> 'b rpregraph" where
  "app_rgraph_isomorphism f (V,E,r) = (f ` V, ((`) f) ` E, f r)"

locale rgraph_isomorphism =
  G: rgraph V\<^sub>G E\<^sub>G r\<^sub>G + graph_isomorphism V\<^sub>G E\<^sub>G V\<^sub>H E\<^sub>H f for V\<^sub>G E\<^sub>G r\<^sub>G V\<^sub>H E\<^sub>H r\<^sub>H f +
  assumes root_preserving: "f r\<^sub>G = r\<^sub>H"
begin

interpretation H: graph_system V\<^sub>H E\<^sub>H using graph_system_H .

lemma rgraph_H: "rgraph V\<^sub>H E\<^sub>H r\<^sub>H"
  using root_preserving bij_f G.root_wf V\<^sub>H_def by unfold_locales blast

interpretation H: rgraph V\<^sub>H E\<^sub>H r\<^sub>H using rgraph_H .

lemma rgraph_isomorphism_inv: "rgraph_isomorphism V\<^sub>H E\<^sub>H r\<^sub>H V\<^sub>G E\<^sub>G r\<^sub>G inv_iso" 
proof-
  interpret iso: graph_isomorphism V\<^sub>H E\<^sub>H V\<^sub>G E\<^sub>G inv_iso using graph_isomorphism_inv .
  show ?thesis using G.root_wf inj_f inv_iso_def root_preserving the_inv_into_f_f
    by unfold_locales fastforce
qed

end

fun rgraph_isomorph :: "'a rpregraph \<Rightarrow> 'b rpregraph \<Rightarrow> bool" (infix "\<simeq>\<^sub>r" 50) where
  "(V\<^sub>G,E\<^sub>G,r\<^sub>G) \<simeq>\<^sub>r (V\<^sub>H,E\<^sub>H,r\<^sub>H) \<longleftrightarrow> (\<exists>f. rgraph_isomorphism V\<^sub>G E\<^sub>G r\<^sub>G V\<^sub>H E\<^sub>H r\<^sub>H f)"

lemma (in rgraph) rgraph_isomorphism_id: "rgraph_isomorphism V E r V E r id"
  using graph_isomorphism_id rgraph_isomorphism.intro rgraph_axioms
  unfolding rgraph_isomorphism_axioms_def by fastforce

lemma (in rgraph) rgraph_isomorph_refl: "(V,E,r) \<simeq>\<^sub>r (V,E,r)"
  using rgraph_isomorphism_id by auto

lemma rgraph_isomorph_sym: "G \<simeq>\<^sub>r H \<Longrightarrow> H \<simeq>\<^sub>r G"
  using rgraph_isomorphism.rgraph_isomorphism_inv by (cases G, cases H) fastforce

lemma rgraph_isomorphism_trans: "rgraph_isomorphism V\<^sub>G E\<^sub>G r\<^sub>G V\<^sub>H E\<^sub>H r\<^sub>H f \<Longrightarrow> rgraph_isomorphism V\<^sub>H E\<^sub>H r\<^sub>H V\<^sub>F E\<^sub>F r\<^sub>F g \<Longrightarrow> rgraph_isomorphism V\<^sub>G E\<^sub>G r\<^sub>G V\<^sub>F E\<^sub>F r\<^sub>F (g o f)"
  using graph_isomorphism_trans unfolding rgraph_isomorphism_def rgraph_isomorphism_axioms_def by fastforce

lemma rgraph_isomorph_trans: "transp (\<simeq>\<^sub>r)"
  using rgraph_isomorphism_trans unfolding transp_def by fastforce

lemma (in rtree) rgraph_isomorphis_app_iso: "inj_on f V \<Longrightarrow> app_rgraph_isomorphism f (V,E,r) = (V',E',r') \<Longrightarrow> rgraph_isomorphism V E r V' E' r' f"
  by unfold_locales (auto simp: bij_betw_def)

lemma (in rtree) rgraph_isomorph_app_iso: "inj_on f V \<Longrightarrow> (V, E, r) \<simeq>\<^sub>r app_rgraph_isomorphism f (V, E, r)"
  using rgraph_isomorphis_app_iso by fastforce

subsection \<open>Conversion between unlabeled, ordered, rooted trees and tree graphs\<close>

datatype 'a ltree = LNode 'a "'a ltree list"

fun ltree_size :: "'a ltree \<Rightarrow> nat" where
  "ltree_size (LNode r ts) = Suc (\<Sum>t\<leftarrow>ts. ltree_size t)"

fun root_ltree :: "'a ltree \<Rightarrow> 'a" where
  "root_ltree (LNode r ts) = r"

fun nodes_ltree :: "'a ltree \<Rightarrow> 'a set" where
  "nodes_ltree (LNode r ts) = {r} \<union> (\<Union>t\<in>set ts. nodes_ltree t)"

fun relabel_ltree :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ltree \<Rightarrow> 'b ltree" where
  "relabel_ltree f (LNode r ts) = LNode (f r) (map (relabel_ltree f) ts)"

fun distinct_ltree_nodes :: "'a ltree \<Rightarrow> bool" where
  "distinct_ltree_nodes (LNode a ts) \<longleftrightarrow> (\<forall>t\<in>set ts. a \<notin> nodes_ltree t) \<and> distinct ts \<and> disjoint_family_on nodes_ltree (set ts) \<and> (\<forall>t\<in>set ts. distinct_ltree_nodes t)"

fun postorder_label_aux :: "nat \<Rightarrow> tree \<Rightarrow> nat \<times> nat ltree" where
  "postorder_label_aux n (Node []) = (n, LNode n [])"
| "postorder_label_aux n (Node (t#ts)) =
  (let (n', t') = postorder_label_aux n t in
    case postorder_label_aux (Suc n') (Node ts) of
      (n'', LNode r ts') \<Rightarrow> (n'', LNode r (t'#ts')))"

definition postorder_label :: "tree \<Rightarrow> nat ltree" where
  "postorder_label t = snd (postorder_label_aux 0 t)"

fun tree_ltree :: "'a ltree \<Rightarrow> tree" where
  "tree_ltree (LNode r ts) = Node (map tree_ltree ts)"

fun regular_ltree :: "'a ltree \<Rightarrow> bool" where
  "regular_ltree (LNode r ts) \<longleftrightarrow> sorted_wrt (\<lambda>t s. tree_ltree t \<le> tree_ltree s) ts \<and> (\<forall>t\<in>set ts. regular_ltree t)"

datatype 'a stree = SNode 'a "'a stree fset"

lemma stree_size_child_lt[termination_simp]: "t |\<in>| ts \<Longrightarrow> size t < Suc (\<Sum>s\<in>fset ts. Suc (size s))"
  using sum_nonneg_leq_bound zero_le finite_fset fmember.rep_eq Suc_le_eq less_SucI by metis

lemma stree_size_child_lt'[termination_simp]: "t \<in> fset ts \<Longrightarrow> size t < Suc (\<Sum>s\<in>fset ts. Suc (size s))"
  using stree_size_child_lt fmember.rep_eq by metis

fun stree_size :: "'a stree \<Rightarrow> nat" where
  "stree_size (SNode r ts) = Suc (fsum stree_size ts)"

definition n_strees :: "nat \<Rightarrow> 'a stree set" where
  "n_strees n = {t. stree_size t = n}"

fun root_stree :: "'a stree \<Rightarrow> 'a" where
  "root_stree (SNode a ts) = a"

fun nodes_stree :: "'a stree \<Rightarrow> 'a set" where
  "nodes_stree (SNode a ts) = {a} \<union> (\<Union>t\<in>fset ts. nodes_stree t)"

fun tree_graph_edges :: "'a stree \<Rightarrow> 'a edge set" where
  "tree_graph_edges (SNode a ts) = ((\<lambda>t. {a, root_stree t}) ` fset ts) \<union> (\<Union>t\<in>fset ts. tree_graph_edges t)"

fun distinct_stree_nodes :: "'a stree \<Rightarrow> bool" where
  "distinct_stree_nodes (SNode a ts) \<longleftrightarrow> (\<forall>t\<in>fset ts. a \<notin> nodes_stree t) \<and> disjoint_family_on nodes_stree (fset ts) \<and> (\<forall>t\<in>fset ts. distinct_stree_nodes t)"

fun ltree_stree :: "'a stree \<Rightarrow> 'a ltree" where
  "ltree_stree (SNode r ts) = LNode r (SOME xs. fset_of_list xs = ltree_stree |`| ts \<and> distinct xs \<and> sorted_wrt (\<lambda>t s. tree_ltree t \<le> tree_ltree s) xs)"

fun stree_ltree :: "'a ltree \<Rightarrow> 'a stree" where
  "stree_ltree (LNode r ts) = SNode r (fset_of_list (map stree_ltree ts))"

definition tree_graph_stree :: "'a stree \<Rightarrow> 'a rpregraph" where
  "tree_graph_stree t = (nodes_stree t, tree_graph_edges t, root_stree t)"

function stree_of_graph :: "'a rpregraph \<Rightarrow> 'a stree" where
  "stree_of_graph (V,E,r) =
    (if \<not> rtree V E r then undefined else
    SNode r (Abs_fset (stree_of_graph ` rtree.subtrees V E r)))"
  by pat_completeness auto

termination
proof (relation "measure (\<lambda>p. card (fst p))", auto)
  fix r :: 'a and V :: "'a set" and E :: "'a edge set" and S :: "'a set" and E\<^sub>S :: "'a edge set" and r\<^sub>S :: 'a
  assume rtree: "rtree V E r"
  assume subtree: "(S, E\<^sub>S, r\<^sub>S) \<in> rtree.subtrees V E r"
  interpret rtree V E r using rtree .
  obtain V' E' where remove_vertex: "remove_vertex r = (V', E')" by fastforce
  then interpret subg: subgraph V' E' V E using subgraph_remove_vertex by simp
  interpret g': fin_ulgraph V' E' using fin_ulgraph.intro subg.is_finite_subgraph fin_graph_system_axioms subg.is_subgraph_ulgraph ulgraph_axioms by blast
  have "S \<in> g'.connected_components" using subtree remove_vertex unfolding subtrees_def by auto
  then have card_C_V':"card S \<le> card V'" using g'.connected_component_wf g'.finV card_mono by metis
  have "card V' < card V" using remove_vertex root_wf finV card_Diff1_less unfolding remove_vertex_def by fast
  then show "card S < card V" using card_C_V' by simp
qed

definition tree_graph :: "tree \<Rightarrow> nat rpregraph" where
  "tree_graph t = tree_graph_stree (stree_ltree (postorder_label t))"

fun relabel_stree :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a stree \<Rightarrow> 'b stree" where
  "relabel_stree f (SNode r ts) = SNode (f r) ((relabel_stree f) |`| ts)"

lemma root_ltree_wf: "root_ltree t \<in> nodes_ltree t"
  by (cases t) auto

lemma root_relabel_ltree[simp]: "root_ltree (relabel_ltree f t) = f (root_ltree t)"
  by (cases t) simp

lemma nodes_relabel_ltree[simp]: "nodes_ltree (relabel_ltree f t) = f ` nodes_ltree t"
  by (induction t) auto

lemma finite_nodes_ltree: "finite (nodes_ltree t)"
  by (induction t) auto

lemma root_stree_wf: "root_stree t \<in> nodes_stree t"
  by (cases t) auto

lemma tree_graph_edges_wf: "e \<in> tree_graph_edges t \<Longrightarrow> e \<subseteq> nodes_stree t"
  using root_stree_wf by (induction t rule: tree_graph_edges.induct) auto

lemma card_tree_graph_edges_distinct: "distinct_stree_nodes t \<Longrightarrow> e \<in> tree_graph_edges t \<Longrightarrow> card e = 2"
  using root_stree_wf card_2_iff by (induction t rule: tree_graph_edges.induct) (auto, fast+)

lemma nodes_stree_non_empty: "nodes_stree t \<noteq> {}"
  by (cases t rule: nodes_stree.cases) auto

lemma finite_nodes_stree: "finite (nodes_stree t)"
  by (induction t rule: nodes_stree.induct) auto

lemma finite_tree_graph_edges: "finite (tree_graph_edges t)"
  by (induction t rule: tree_graph_edges.induct) auto

lemma root_relabel_stree[simp]: "root_stree (relabel_stree f t) = f (root_stree t)"
  by (cases t) auto

lemma nodes_stree_relabel_stree[simp]: "nodes_stree (relabel_stree f t) = f ` nodes_stree t"
  by (induction t) auto

lemma tree_graph_edges_relabel_stree[simp]: "tree_graph_edges (relabel_stree f t) = ((`) f) ` tree_graph_edges t"
  by (induction t) (simp add: image_image image_Un image_Union)

lemma nodes_stree_ltree[simp]: "nodes_stree (stree_ltree t) = nodes_ltree t"
  by (induction t) (auto simp: fset_of_list.rep_eq)

lemma distinct_sorted_wrt_list: "\<exists>xs. fset_of_list xs = A \<and> distinct xs \<and> sorted_wrt (\<lambda>t s. (f t :: 'b::linorder) \<le> f s) xs"
proof-
  obtain xs where "fset_of_list xs = A \<and> distinct xs"
    by (metis finite_distinct_list finite_fset fset_cong fset_of_list.rep_eq)
  then have "fset_of_list (sort_key f xs) = A \<and> distinct (sort_key f xs) \<and> sorted_wrt (\<lambda>t s. f t \<le> f s) (sort_key f xs)"
    using sorted_sort_key sorted_wrt_map by (simp add: fset_of_list.abs_eq, blast)
  then show ?thesis by blast
qed

abbreviation "ltree_stree_subtrees ts \<equiv> SOME xs. fset_of_list xs = ltree_stree |`| ts \<and> distinct xs \<and> sorted_wrt (\<lambda>t s. tree_ltree t \<le> tree_ltree s) xs"

lemma fset_of_list_ltree_stree_subtrees[simp]: "fset_of_list (ltree_stree_subtrees ts) = ltree_stree |`| ts"
  using someI_ex[OF distinct_sorted_wrt_list] by fast

lemma set_ltree_stree_subtrees[simp]: "set (ltree_stree_subtrees ts) = ltree_stree ` fset ts"
  using fset_of_list_ltree_stree_subtrees by (metis (mono_tags, lifting) fset.set_map fset_of_list.rep_eq)

lemma distinct_ltree_stree_subtrees: "distinct (ltree_stree_subtrees ts)"
  using someI_ex[OF distinct_sorted_wrt_list] by blast

lemma sorted_wrt_ltree_stree_subtrees: "sorted_wrt (\<lambda>t s. tree_ltree t \<le> tree_ltree s) (ltree_stree_subtrees ts)"
  using someI_ex[OF distinct_sorted_wrt_list] by blast

lemma nodes_ltree_stree[simp]: "nodes_ltree (ltree_stree t) = nodes_stree t"
  by (induction t) auto

lemma stree_ltree_stree[simp]: "stree_ltree (ltree_stree t) = t"
  by (induction t)  (simp add: fset.map_ident_strong)

lemma nodes_tree_graph_stree: "tree_graph_stree t = (V, E, r) \<Longrightarrow> V = nodes_stree t"
  by (induction t) (simp add: tree_graph_stree_def)

lemma relabel_stree_stree_ltree: "relabel_stree f (stree_ltree t) = stree_ltree (relabel_ltree f t)"
  by (induction t) (auto simp add: fset_of_list_elem, metis comp_apply fimage_eqI fset_of_list_elem)

lemma relabel_stree_relabel_ltree: "relabel_ltree f t1 = t2 \<Longrightarrow> relabel_stree f (stree_ltree t1) = stree_ltree t2"
  using relabel_stree_stree_ltree by blast


lemma app_rgraph_iso_tree_graph_stree: "app_rgraph_isomorphism f (tree_graph_stree t) = tree_graph_stree (relabel_stree f t)"
  unfolding tree_graph_stree_def using image_iff mk_disjoint_insert
  by (induction t) (auto, fastforce+)

lemma (in rtree) root_stree_of_graph[simp]: "root_stree (stree_of_graph (V,E,r)) = r"
  using rtree_axioms by (simp split: prod.split)

lemma (in rtree) nodes_stree_stree_of_graph[simp]: "nodes_stree (stree_of_graph (V,E,r)) = V"
  using rtree_axioms
proof (induction "(V,E,r)" arbitrary: V E r rule: stree_of_graph.induct)
  case (1 V\<^sub>T E\<^sub>T r)
  then interpret t: rtree V\<^sub>T E\<^sub>T r by simp
  obtain V' E' where VE': "t.remove_vertex r = (V', E')" by (simp add: t.remove_vertex_def)
  interpret subg: subgraph V' E' V\<^sub>T E\<^sub>T using t.subgraph_remove_vertex VE' by metis
  interpret g': fin_ulgraph V' E' using fin_ulgraph.intro subg.is_finite_subgraph t.fin_graph_system_axioms subg.is_subgraph_ulgraph t.ulgraph_axioms by blast

  have "finite (stree_of_graph ` t.subtrees)" using t.finite_subtrees by blast
  then have "nodes_stree (stree_of_graph (V\<^sub>T, E\<^sub>T, r)) = {r} \<union> V'"
    using 1 using VE' t.rtree_subtree g'.Union_connected_components by (simp add: Abs_fset_inverse t.subtrees_def)
  then show ?case using VE' t.root_wf unfolding t.remove_vertex_def by auto
qed

lemma (in rtree) tree_graph_edges_stree_of_graph[simp]: "tree_graph_edges (stree_of_graph (V,E,r)) = E"
  using rtree_axioms
proof (induction "(V,E,r)" arbitrary: V E r rule: stree_of_graph.induct)
  case (1 V\<^sub>T E\<^sub>T r)
  then interpret t: rtree V\<^sub>T E\<^sub>T r by simp
  obtain V' E' where VE': "t.remove_vertex r = (V', E')" by (simp add: t.remove_vertex_def)
  interpret subg: subgraph V' E' V\<^sub>T E\<^sub>T using t.subgraph_remove_vertex VE' by metis
  interpret g': fin_ulgraph V' E' using fin_ulgraph.intro subg.is_finite_subgraph t.fin_graph_system_axioms subg.is_subgraph_ulgraph t.ulgraph_axioms by blast

  have "finite (stree_of_graph ` t.subtrees)" using t.finite_subtrees by blast
  then have fset_Abs_fset_subtrees[simp]: "fset (Abs_fset (stree_of_graph ` t.subtrees)) = stree_of_graph ` t.subtrees" by (simp add: Abs_fset_inverse)

  have root_edges: "(\<lambda>x. {r, root_stree x}) ` stree_of_graph ` t.subtrees = {e\<in>E\<^sub>T. r \<in> e}" (is "?l = ?r")
  proof-
    have "e \<in> ?l" if "e \<in> ?r" for e
    proof-
      obtain r' where e: "e = {r, r'}" using \<open>e\<in>?r\<close>
        by (metis (no_types, lifting) CollectD insert_commute insert_iff singleton_iff t.obtain_edge_pair_adj)
      then have "r' \<noteq> r" using t.singleton_not_edge \<open>e\<in>?r\<close> by force
      then have "r' \<in> V'" using e \<open>e\<in>?r\<close> VE' t.remove_vertex_def t.wellformed_alt_snd by fastforce
      then obtain C where C_conn_component: "C \<in> g'.connected_components" and "r' \<in> C" using g'.Union_connected_components by auto
      have "t.vert_adj r r'" unfolding t.vert_adj_def using \<open>e\<in>?r\<close> e by blast
      then have "(THE r'. r' \<in> C \<and> t.vert_adj r r') = r'" using t.unique_adj_vert_removed[OF t.root_wf VE' C_conn_component] \<open>r'\<in>C\<close> by auto
      then show ?thesis using e \<open>r'\<in>C\<close> C_conn_component rtree.root_stree_of_graph t.rtree_subtree VE' unfolding t.subtrees_def by (auto simp: image_comp)
    qed
    then show ?thesis using t.unique_adj_vert_removed[OF t.root_wf VE'] t.rtree_subtree VE'
      unfolding t.subtrees_def t.vert_adj_def by (auto, metis (no_types, lifting) theI)
  qed
  have "(\<Union>S\<in>t.subtrees. tree_graph_edges (stree_of_graph S)) = E'" 
    using 1 VE' t.rtree_subtree g'.Union_induced_edges_connected_components
    unfolding t.subtrees_def by simp
  then have "tree_graph_edges (stree_of_graph (V\<^sub>T,E\<^sub>T,r)) = {e\<in>E\<^sub>T. r \<in> e} \<union> E'"
    using root_edges 1(2) by simp
  then show ?case using VE' unfolding t.remove_vertex_def t.incident_def by blast
qed

lemma (in rtree) tree_graph_stree_of_graph[simp]: "tree_graph_stree (stree_of_graph (V,E,r)) = (V,E,r)"
  using nodes_stree_stree_of_graph tree_graph_edges_stree_of_graph root_stree_of_graph unfolding tree_graph_stree_def by blast


lemma postorder_label_aux_mono: "fst (postorder_label_aux n t) \<ge> n"
  by (induction n t rule: postorder_label_aux.induct) (auto split: prod.split ltree.split, fastforce)

lemma nodes_postorder_label_aux_ge: "postorder_label_aux n t = (n', t') \<Longrightarrow> v \<in> nodes_ltree t' \<Longrightarrow> v \<ge> n"
  by (induction n t arbitrary: n' t' rule: postorder_label_aux.induct,
      auto split: prod.splits ltree.splits,
      (metis fst_conv le_SucI order.trans postorder_label_aux_mono)+)

lemma nodes_postorder_label_aux_le: "postorder_label_aux n t = (n', t') \<Longrightarrow> v \<in> nodes_ltree t' \<Longrightarrow> v \<le> n'"
  by (induction n t arbitrary: n' t' rule: postorder_label_aux.induct,
      auto split: prod.splits ltree.splits,
      metis Suc_leD fst_conv order_trans postorder_label_aux_mono,
      blast)

lemma distinct_nodes_postorder_label_aux: "distinct_ltree_nodes (snd (postorder_label_aux n t))"
proof (induction n t rule: postorder_label_aux.induct)
  case (1 n)
  then show ?case by (simp add: disjoint_family_on_def)
next
  case (2 n t ts)
  obtain n' t' where t': "postorder_label_aux n t = (n', t')" by fastforce
  obtain n'' r ts' where ts': "postorder_label_aux (Suc n') (Node ts) = (n'', LNode r ts')" by (metis eq_snd_iff ltree.exhaust)
  then have "r \<ge> Suc n'" using nodes_postorder_label_aux_ge by auto
  then have r_notin_t': "r \<notin> nodes_ltree t'" using nodes_postorder_label_aux_le[OF t'] by fastforce
  have distinct_subtrees: "distinct (t'#ts')" using 2 t' ts' nodes_postorder_label_aux_le[OF t']
      nodes_postorder_label_aux_ge[OF ts'] by (auto, meson not_less_eq_eq root_ltree_wf)
  have "disjoint_family_on nodes_ltree (set (t'#ts'))" using 2 t' ts' nodes_postorder_label_aux_le[OF t']
      nodes_postorder_label_aux_ge[OF ts'] by (simp add: disjoint_family_on_def, meson disjoint_iff not_less_eq_eq)
  then show ?case using 2 t' ts' r_notin_t' distinct_subtrees by simp
qed

lemma distinct_nodes_postorder_label: "distinct_ltree_nodes (postorder_label t)"
  unfolding postorder_label_def using distinct_nodes_postorder_label_aux by simp

lemma distinct_nodes_stree_ltree: "distinct_ltree_nodes t \<Longrightarrow> distinct_stree_nodes (stree_ltree t)"
  by (induction t) (auto simp: fset_of_list.rep_eq disjoint_family_on_def, fast)

fun distinct_edges :: "'a stree \<Rightarrow> bool" where
  "distinct_edges (SNode a ts) \<longleftrightarrow> inj_on (\<lambda>t. {a, root_stree t}) (fset ts)
    \<and> (\<forall>t\<in>fset ts. disjnt ((\<lambda>t. {a, root_stree t}) ` fset ts) (tree_graph_edges t))
    \<and> disjoint_family_on tree_graph_edges (fset ts)
    \<and> (\<forall>t\<in>fset ts. distinct_edges t)"

lemma distinct_nodes_inj_on_root_stree: "distinct_stree_nodes (SNode r ts) \<Longrightarrow> inj_on root_stree (fset ts)"
  by (auto simp: disjoint_family_on_def, metis IntI emptyE inj_onI root_stree_wf)

lemma distinct_nodes_disjoint_edges:
  assumes distinct_nodes: "distinct_stree_nodes (SNode a ts)"
  shows "disjoint_family_on tree_graph_edges (fset ts)"
proof-
  have "tree_graph_edges t1 \<inter> tree_graph_edges t2 = {}"
    if t1_in_ts: "t1 \<in> fset ts" and t2_in_ts: "t2 \<in> fset ts" and "t1 \<noteq> t2" for t1 t2
  proof-
    have "\<forall>e\<in>tree_graph_edges t1. e \<notin> tree_graph_edges t2"
    proof
      fix e assume e_in_edges_t1: "e \<in> tree_graph_edges t1"
      then have "e \<noteq> {}" using t1_in_ts card_tree_graph_edges_distinct distinct_nodes by fastforce
      then have "\<exists>v\<in>nodes_stree t1. v \<in> e" using tree_graph_edges_wf e_in_edges_t1 by blast
      then show "e \<notin> tree_graph_edges t2" using \<open>t1\<noteq>t2\<close> distinct_nodes t1_in_ts t2_in_ts tree_graph_edges_wf
        by (auto simp: disjoint_family_on_def, blast)
    qed
    then show ?thesis by blast
  qed
  then show ?thesis unfolding disjoint_family_on_def by blast
qed

lemma card_nodes_edges: "distinct_stree_nodes t \<Longrightarrow> card (nodes_stree t) = Suc (card (tree_graph_edges t))"
proof (induction t rule: tree_graph_edges.induct)
  case (1 a ts)
  let ?t = "SNode a ts"
  have "inj_on (\<lambda>t. {a, root_stree t}) (fset ts)" using distinct_nodes_inj_on_root_stree[OF 1(2)]
    unfolding inj_on_def doubleton_eq_iff by blast
  then have card_root_edges: "card ((\<lambda>t. {a, root_stree t}) ` fset ts) = card (fset ts)"
    using card_image by blast
  have finite_Un: "finite (\<Union>t\<in>fset ts. nodes_stree t)" using finite_Union finite_nodes_stree finite_fset by auto
  then have "card (nodes_stree ?t) = Suc (card (\<Union>t\<in>fset ts. nodes_stree t))" using 1(2) card_insert_disjoint finite_Un by simp
  also have "\<dots> = Suc (\<Sum>t\<in>fset ts. card (nodes_stree t))" using 1(2) card_UN_disjoint' finite_nodes_stree finite_fset by fastforce
  also have "\<dots> = Suc (\<Sum>t\<in>fset ts. Suc (card (tree_graph_edges t)))" using 1 by simp
  also have "\<dots> = Suc (card (fset ts) + (\<Sum>t\<in>fset ts. card (tree_graph_edges t)))" by (metis add.commute sum_Suc)
  also have "\<dots> = Suc (card ((\<lambda>t. {a, root_stree t}) ` fset ts) + (\<Sum>t\<in>fset ts. card (tree_graph_edges t)))"
    using card_root_edges by simp
  also have "\<dots> = Suc (card ((\<lambda>x. {a, root_stree x}) ` fset ts) + card (\<Union> (tree_graph_edges ` fset ts)))"
    using distinct_nodes_disjoint_edges[OF 1(2)] card_UN_disjoint' finite_tree_graph_edges by fastforce
  also have "\<dots> = Suc (card ((\<lambda>x. {a, root_stree x}) ` fset ts \<union> (\<Union> (tree_graph_edges ` fset ts))))" (is "Suc (card ?r + card ?Un) = Suc (card (?r \<union> ?Un))")
  proof-
    have "\<forall>t \<in> fset ts. \<forall>e \<in> tree_graph_edges t. a \<notin> e" using 1(2) tree_graph_edges_wf by auto
    then have disjnt: "disjnt ?r ?Un" using disjoint_UN_iff by (auto simp: disjnt_def)
    show ?thesis using card_Un_disjnt[OF _ _ disjnt] finite_tree_graph_edges by fastforce
  qed
  finally show ?case by simp
qed

lemma tree_tree_graph_edges: "distinct_stree_nodes t \<Longrightarrow> tree (nodes_stree t) (tree_graph_edges t)"
proof (induction t rule: tree_graph_edges.induct)
  case (1 a ts)
  let ?t = "SNode a ts"
  have "\<And>e. e \<in> tree_graph_edges ?t \<Longrightarrow> 0 < card e \<and> card e \<le> 2" using card_tree_graph_edges_distinct 1 by (metis order_refl pos2)
  then interpret g: fin_ulgraph "nodes_stree ?t" "tree_graph_edges ?t" using tree_graph_edges_wf finite_nodes_stree by (unfold_locales) blast+
  have "g.vert_connected a v" if t: "t \<in> fset ts" and v: "v \<in> nodes_stree t" for t v
  proof-
    interpret t: tree "nodes_stree t" "tree_graph_edges t" using 1 t by auto
    interpret subg: ulsubgraph "nodes_stree t" "tree_graph_edges t" "nodes_stree ?t" "tree_graph_edges ?t" using t by unfold_locales auto
    have conn_root_v: "g.vert_connected (root_stree t) v" using subg.vert_connected v root_stree_wf t.vertices_connected by blast
    have "{a, root_stree t} \<in> tree_graph_edges ?t" using t by auto
    then have "g.vert_connected a (root_stree t)" using g.vert_connected_neighbors by blast
    then show ?thesis using conn_root_v g.vert_connected_trans by blast
  qed
  then have "\<forall>v\<in>nodes_stree ?t. g.vert_connected a v" using g.vert_connected_id by auto
  then have "g.is_connected_set (nodes_stree ?t)" using g.vert_connected_trans g.vert_connected_rev unfolding g.is_connected_set_def by blast 
  then interpret g: fin_connected_ulgraph "nodes_stree ?t" "tree_graph_edges ?t" by unfold_locales auto
  show ?case using card_E_treeI card_nodes_edges 1(2) g.fin_connected_ulgraph_axioms by blast
qed

lemma rtree_tree_graph_edges:
  assumes distinct_nodes: "distinct_stree_nodes t"
  shows "rtree (nodes_stree t) (tree_graph_edges t) (root_stree t)"
proof-
  interpret tree "nodes_stree t" "tree_graph_edges t" using distinct_nodes tree_tree_graph_edges by blast
  show ?thesis using root_stree_wf by unfold_locales blast
qed

lemma rtree_tree_graph_stree: "distinct_stree_nodes t \<Longrightarrow> tree_graph_stree t = (V,E,r) \<Longrightarrow> rtree V E r"
  using rtree_tree_graph_edges unfolding tree_graph_stree_def by blast

lemma rtree_tree_graph: "tree_graph t = (V,E,r) \<Longrightarrow> rtree V E r"
  unfolding tree_graph_def using distinct_nodes_postorder_label rtree_tree_graph_stree distinct_nodes_stree_ltree by fast

text "Cardinality of the resulting rooted tree is correct"

lemma ltree_size_postorder_label_aux: "ltree_size (snd (postorder_label_aux n t)) = tree_size t"
  by (induction n t rule: postorder_label_aux.induct) (auto split: prod.split ltree.split)

lemma ltree_size_postorder_label: "ltree_size (postorder_label t) = tree_size t"
  unfolding postorder_label_def using ltree_size_postorder_label_aux by blast

lemma distinct_nodes_ltree_size_card_nodes: "distinct_ltree_nodes t \<Longrightarrow> ltree_size t = card (nodes_ltree t)"
proof (induction t)
  case (LNode r ts)
  have "finite (\<Union> (nodes_ltree ` set ts))" using finite_nodes_ltree by blast
  then show ?case using LNode disjoint_family_on_disjoint_image
    by (auto simp: sum_list_distinct_conv_sum_set card_UN_disjoint')
qed

lemma distinct_nodes_stree_size_card_nodes: "distinct_stree_nodes t \<Longrightarrow> stree_size t = card (nodes_stree t)"
proof (induction t)
  case (SNode r ts)
  have "finite (\<Union> (nodes_stree ` fset ts))" using finite_nodes_stree by auto
  then show ?case using SNode disjoint_family_on_disjoint_image
    by (auto simp: fsum.F.rep_eq card_UN_disjoint')
qed

lemma stree_size_stree_ltree: "distinct_ltree_nodes t \<Longrightarrow> stree_size (stree_ltree t) = ltree_size t"
  by (simp add: distinct_nodes_ltree_size_card_nodes distinct_nodes_stree_ltree distinct_nodes_stree_size_card_nodes)

lemma card_tree_graph_stree: "distinct_stree_nodes t \<Longrightarrow> tree_graph_stree t = (V,E,r) \<Longrightarrow> card V = stree_size t"
  by (simp add: distinct_nodes_stree_size_card_nodes) (metis nodes_tree_graph_stree)

lemma card_tree_graph: "tree_graph t = (V,E,r) \<Longrightarrow> card V = tree_size t"
  unfolding tree_graph_def using ltree_size_postorder_label stree_size_stree_ltree card_tree_graph_stree
  by (metis distinct_nodes_postorder_label distinct_nodes_stree_ltree)


lemma [termination_simp]: "(t, s) \<in> set (zip ts ss) \<Longrightarrow> size t < Suc (size_list size ts)"
  by (metis less_not_refl not_less_eq set_zip_leftD size_list_estimation)

fun obtain_ltree_isomorphism :: "'a ltree \<Rightarrow> 'b ltree \<Rightarrow> ('a \<rightharpoonup> 'b)" where
  "obtain_ltree_isomorphism (LNode r1 ts) (LNode r2 ss) = fold (++) (map2 obtain_ltree_isomorphism ts ss) [r1\<mapsto>r2]"

fun postorder_relabel_aux :: "nat \<Rightarrow> 'a ltree \<Rightarrow> nat \<times> (nat \<rightharpoonup> 'a)" where
  "postorder_relabel_aux n (LNode r []) = (n, [n \<mapsto> r])"
| "postorder_relabel_aux n (LNode r (t#ts)) =
  (let (n', f\<^sub>t) = postorder_relabel_aux n t;
      (n'', f\<^sub>t\<^sub>s) = postorder_relabel_aux (Suc n') (LNode r ts) in
      (n'', f\<^sub>t ++ f\<^sub>t\<^sub>s))"

definition postorder_relabel :: "'a ltree \<Rightarrow> (nat \<rightharpoonup> 'a)" where
  "postorder_relabel t = snd (postorder_relabel_aux 0 t)"

lemma fst_postorder_label_aux_tree_ltree: "fst (postorder_label_aux n (tree_ltree t)) = fst (postorder_relabel_aux n t)"
  by (induction n t rule: postorder_relabel_aux.induct) (auto split: prod.split ltree.split)

lemma dom_postorder_relabel_aux: "dom (snd (postorder_relabel_aux n t)) = nodes_ltree (snd (postorder_label_aux n (tree_ltree t)))"
proof (induction n t rule: postorder_relabel_aux.induct)
case (1 n r)
  then show ?case by (auto split: if_splits)
next
  case (2 n r t ts)
  obtain n' f_t where f_t: "postorder_relabel_aux n t = (n', f_t)" by fastforce
  then obtain t' where t': "postorder_label_aux n (tree_ltree t) = (n', t')"
    using fst_postorder_label_aux_tree_ltree by (metis fst_eqD prod.exhaust_sel)
  obtain n'' f_ts where f_ts: "postorder_relabel_aux (Suc n') (LNode r ts) = (n'', f_ts)" by fastforce
  then obtain ts' r' where ts': "postorder_label_aux (Suc n') (tree_ltree (LNode r ts)) = (n'', LNode r' ts')"
    using fst_postorder_label_aux_tree_ltree by (metis fst_eqD prod.exhaust_sel ltree.exhaust)
  show ?case using 2 f_t f_ts t' ts' by auto
qed

lemma ran_postorder_relabel_aux: "ran (snd (postorder_relabel_aux n t)) = nodes_ltree t"
proof (induction n t rule: postorder_relabel_aux.induct)
  case (1 n r)
  then show ?case by (simp add: ran_def)
next
  case (2 n r t ts)
  obtain n' f_t where f_t: "postorder_relabel_aux n t = (n', f_t)" by fastforce
  obtain n'' f_ts where f_ts: "postorder_relabel_aux (Suc n') (LNode r ts) = (n'', f_ts)" by fastforce
  have "dom f_t \<inter> dom f_ts = {}" using dom_postorder_relabel_aux f_t f_ts
    by (metis disjoint_iff fst_eqD fst_postorder_label_aux_tree_ltree nodes_postorder_label_aux_ge
        nodes_postorder_label_aux_le not_less_eq_eq prod.exhaust_sel snd_conv)
  then show ?case using 2 f_t f_ts by (simp add: ran_map_add)
qed

lemma relabel_ltree_eq: "\<forall>v\<in>nodes_ltree t. f v = g v \<Longrightarrow> relabel_ltree f t = relabel_ltree g t"
  by (induction t) auto

lemma relabel_postorder_relabel_aux: "relabel_ltree (the o snd (postorder_relabel_aux n t)) (snd (postorder_label_aux n (tree_ltree t))) = t"
proof (induction n t rule: postorder_relabel_aux.induct)
  case (1 n r)
  then show ?case by auto
next
  case (2 n r t ts)
  obtain n' f_t where f_t: "postorder_relabel_aux n t = (n', f_t)" by fastforce
  then obtain t' where t': "postorder_label_aux n (tree_ltree t) = (n', t')"
    using fst_postorder_label_aux_tree_ltree by (metis fst_eqD prod.exhaust_sel)
  obtain n'' f_ts where f_ts: "postorder_relabel_aux (Suc n') (LNode r ts) = (n'', f_ts)" by fastforce
  then obtain ts' r' where ts': "postorder_label_aux (Suc n') (tree_ltree (LNode r ts)) = (n'', LNode r' ts')"
    using fst_postorder_label_aux_tree_ltree by (metis fst_eqD prod.exhaust_sel ltree.exhaust)
  have ts'_in_f_ts: "\<forall>v\<in>nodes_ltree (LNode r' ts'). v \<in> dom f_ts" using f_ts ts' dom_postorder_relabel_aux
    by (metis snd_conv)
  have "\<forall>v\<in>nodes_ltree t'. v \<notin> dom f_ts" using f_ts t' ts' f_t dom_postorder_relabel_aux
    by (metis nodes_postorder_label_aux_ge nodes_postorder_label_aux_le not_less_eq_eq snd_conv)
  then show ?case using 2 f_t f_ts t' ts' ts'_in_f_ts
    by (auto intro!: relabel_ltree_eq simp: map_add_dom_app_simps(3) map_add_dom_app_simps(1),
        smt (verit, ccfv_threshold) map_add_dom_app_simps(1) map_eq_conv relabel_ltree_eq)
qed

lemma relabel_postorder_relabel: "relabel_ltree (the o postorder_relabel t) (postorder_label (tree_ltree t)) = t"
  unfolding postorder_relabel_def postorder_label_def using relabel_postorder_relabel_aux by auto

lemma relabel_postorder_aux_inj: "distinct_ltree_nodes t \<Longrightarrow> inj_on (the o snd (postorder_relabel_aux n t)) (nodes_ltree (snd (postorder_label_aux n (tree_ltree t))))"
proof (induction n t rule: postorder_relabel_aux.induct)
  case (1 n r)
  then show ?case by auto
next
  case (2 n r t ts)
  have disjoint_family_on_ts: "disjoint_family_on nodes_ltree (set ts)" using 2(3) by (simp add: disjoint_family_on_def)
  obtain n' f_t where f_t: "postorder_relabel_aux n t = (n', f_t)" by fastforce
  then obtain t' where t': "postorder_label_aux n (tree_ltree t) = (n', t')"
    using fst_postorder_label_aux_tree_ltree by (metis fst_eqD prod.exhaust_sel)
  obtain n'' f_ts where f_ts: "postorder_relabel_aux (Suc n') (LNode r ts) = (n'', f_ts)" by fastforce
  then obtain ts' r' where ts': "postorder_label_aux (Suc n') (tree_ltree (LNode r ts)) = (n'', LNode r' ts')"
    using fst_postorder_label_aux_tree_ltree by (metis fst_eqD prod.exhaust_sel ltree.exhaust)

  have t'_in_dom_f_t: "nodes_ltree t' \<subseteq> dom f_t" using f_t t' dom_postorder_relabel_aux
    by (metis order_refl snd_conv)
  have "\<forall>v\<in>nodes_ltree t'. v \<notin> dom f_ts" using f_ts ts' t' dom_postorder_relabel_aux
    by (metis nodes_postorder_label_aux_ge nodes_postorder_label_aux_le not_less_eq_eq snd_conv)
  then have f_t': "\<forall>v\<in>nodes_ltree t'. the ((f_t ++ f_ts) v) = the (f_t v)"
    by (simp add: map_add_dom_app_simps(3))
  have "inj_on (\<lambda>v. the (f_t v)) (nodes_ltree t')" using 2 ts' f_ts f_t t' disjoint_family_on_ts by auto
  then have inj_on_t': "inj_on (\<lambda>v. the ((f_t ++ f_ts) v)) (nodes_ltree t')"
    by (metis (mono_tags, lifting) inj_on_cong f_t')
  have ts'_in_dom_f_ts: "\<forall>v\<in>nodes_ltree (LNode r' ts'). v \<in> dom f_ts" using f_ts ts' dom_postorder_relabel_aux
    by (metis snd_conv)
  then have f_ts': "\<forall>v\<in>nodes_ltree (LNode r' ts'). the ((f_t ++ f_ts) v) = the (f_ts v)"
    by (simp add: map_add_dom_app_simps(1))
  have "inj_on (\<lambda>v. the (f_ts v)) (nodes_ltree (LNode r' ts'))" using 2 ts' f_ts f_t disjoint_family_on_ts by simp
  then have inj_on_ts': "inj_on (\<lambda>v. the ((f_t ++ f_ts) v)) (nodes_ltree (LNode r' ts'))" using f_ts' inj_on_cong by fast

  have "(\<lambda>v. the ((f_t ++ f_ts) v)) ` nodes_ltree t' \<inter> (\<lambda>v. the ((f_t ++ f_ts) v)) ` nodes_ltree (LNode r' ts') = {}"
  proof-
    have "(\<lambda>v. the ((f_t ++ f_ts) v)) ` nodes_ltree t' = (\<lambda>v. the (f_t v)) ` nodes_ltree t'" using f_t' by simp
    also have "\<dots> \<subseteq> ran f_t" using t'_in_dom_f_t ran_def by fastforce
    also have "\<dots> = nodes_ltree t" by (metis f_t ran_postorder_relabel_aux snd_conv)
    finally have f_nodes_t': "(\<lambda>v. the ((f_t ++ f_ts) v)) ` nodes_ltree t' \<subseteq> nodes_ltree t" .

    have "(\<lambda>v. the ((f_t ++ f_ts) v)) ` nodes_ltree (LNode r' ts') = (\<lambda>v. the (f_ts v)) ` nodes_ltree (LNode r' ts')"
      using f_ts' by (simp del: nodes_ltree.simps)
    also have "\<dots> \<subseteq> ran f_ts" using ts'_in_dom_f_ts ran_def by fastforce
    also have "\<dots> = nodes_ltree (LNode r ts)" by (metis f_ts ran_postorder_relabel_aux snd_conv)
    finally have f_nodes_ts': "(\<lambda>v. the ((f_t ++ f_ts) v)) ` nodes_ltree (LNode r' ts') \<subseteq> nodes_ltree (LNode r ts)" .

    have "nodes_ltree t \<inter> nodes_ltree (LNode r ts) = {}" using 2(3) by (auto simp add: disjoint_family_on_def)
    then show ?thesis using f_nodes_t' f_nodes_ts' by blast
  qed
  then have "inj_on (\<lambda>v. the ((f_t ++ f_ts) v)) (nodes_ltree t' \<union> nodes_ltree (LNode r' ts'))" using inj_on_t' inj_on_ts' inj_on_Un by fast
  then show ?case using f_t t' f_ts ts' by simp
qed

lemma relabel_postorder_inj: "distinct_ltree_nodes t \<Longrightarrow> inj_on (the o postorder_relabel t) (nodes_ltree (postorder_label (tree_ltree t)))"
  unfolding postorder_relabel_def postorder_label_def using relabel_postorder_aux_inj by blast

lemma (in rtree) distinct_nodes_stree_of_graph: "distinct_stree_nodes (stree_of_graph (V,E,r))"
  using rtree_axioms
proof (induction "(V,E,r)" arbitrary: V E r rule: stree_of_graph.induct)
  case (1 V\<^sub>T E\<^sub>T r)
  then interpret t: rtree V\<^sub>T E\<^sub>T r by simp
  obtain V' E' where VE': "t.remove_vertex r = (V', E')" by (simp add: t.remove_vertex_def)
  interpret subg: subgraph V' E' V\<^sub>T E\<^sub>T using t.subgraph_remove_vertex VE' by metis
  interpret g': fin_ulgraph V' E' using fin_ulgraph.intro subg.is_finite_subgraph t.fin_graph_system_axioms subg.is_subgraph_ulgraph t.ulgraph_axioms by blast

  have "finite (stree_of_graph ` t.subtrees)" using t.finite_subtrees by blast
  then have fset_Abs_fset_subtrees[simp]: "fset (Abs_fset (stree_of_graph ` t.subtrees)) = stree_of_graph ` t.subtrees" by (simp add: Abs_fset_inverse)

  have r_notin_subtrees: "\<forall>s\<in>t.subtrees. r \<notin> nodes_stree (stree_of_graph s)"
  proof
    fix s assume subtree: "s \<in> t.subtrees"
    then obtain S E\<^sub>S r\<^sub>S where s: "s = (S,E\<^sub>S,r\<^sub>S)" using prod.exhaust by metis
    then interpret s: rtree S E\<^sub>S r\<^sub>S using t.rtree_subtree subtree by blast
    have "S \<in> g'.connected_components" using subtree VE' unfolding s t.subtrees_def by auto
    then have "nodes_stree (stree_of_graph (S,E\<^sub>S,r\<^sub>S)) \<subseteq> V'" using s.nodes_stree_stree_of_graph g'.connected_component_wf by auto
    then show "r \<notin> nodes_stree (stree_of_graph s)" using VE' unfolding s t.remove_vertex_def by blast
  qed

  have "nodes_stree (stree_of_graph s1) \<inter> nodes_stree (stree_of_graph s2) = {}"
    if s1_subtree: "s1 \<in> t.subtrees" and s2_subtree: "s2 \<in> t.subtrees" and ne: "stree_of_graph s1 \<noteq> stree_of_graph s2" for s1 s2
  proof-
    obtain V1 E1 r1 where s1: "s1 = (V1,E1,r1)" using prod.exhaust by metis
    then interpret s1: rtree V1 E1 r1 using t.rtree_subtree s1_subtree by blast
    have V1_conn_comp: "V1 \<in> g'.connected_components" using s1_subtree VE' unfolding t.subtrees_def s1 by auto
    then have s1_conn_comp: "nodes_stree (stree_of_graph s1) \<in> g'.connected_components" unfolding s1 using s1.nodes_stree_stree_of_graph by auto
    obtain V2 E2 r2 where s2: "s2 = (V2,E2,r2)" using prod.exhaust by metis
    then interpret s2: rtree V2 E2 r2 using t.rtree_subtree s2_subtree by blast
    have V2_conn_comp: "V2 \<in> g'.connected_components" using s2_subtree VE' unfolding t.subtrees_def s2 by auto
    have "V1 \<noteq> V2" using s1 s2 s1_subtree s2_subtree VE' ne unfolding t.subtrees_def by auto
    then have "V1 \<inter> V2 = {}" using V1_conn_comp V2_conn_comp g'.disjoint_connected_components unfolding disjoint_def by blast
    then show ?thesis using s1 s2 s1.nodes_stree_stree_of_graph s2.nodes_stree_stree_of_graph by simp
  qed
  then have "disjoint_family_on nodes_stree (stree_of_graph ` t.subtrees)"
    unfolding disjoint_family_on_def by blast
  then show ?case using 1 t.rtree_subtree r_notin_subtrees by auto
qed

lemma disintct_nodes_ltree_stree: "distinct_stree_nodes t \<Longrightarrow> distinct_ltree_nodes (ltree_stree t)"
  using distinct_ltree_stree_subtrees by (induction t) (auto simp: disjoint_family_on_def, metis disjoint_iff)

lemma (in rtree) tree_graph_tree_of_graph: "tree_graph (tree_ltree (ltree_stree (stree_of_graph (V,E,r)))) \<simeq>\<^sub>r (V,E,r)"
proof-
  define t where "t = (V,E,r)"
  define s where "s = stree_of_graph t"
  define l where "l = ltree_stree s"
  define l' where "l' = postorder_label (tree_ltree l)"
  define s' where "s' = stree_ltree l'"
  define t' where "t' = tree_graph_stree s'"
  obtain V' E' r' where t': "t' = (V',E',r')" using prod.exhaust by metis
  interpret t': rtree V' E' r' using t' rtree_tree_graph unfolding tree_graph_def t'_def s'_def l'_def by simp 
  have "distinct_ltree_nodes l" using distinct_nodes_stree_of_graph disintct_nodes_ltree_stree
    unfolding l_def s_def t_def by blast
  then obtain f where inj_on_l': "inj_on f (nodes_ltree l')" and relabel_l': "relabel_ltree f l' = l"
    unfolding l'_def using relabel_postorder_relabel relabel_postorder_inj by blast
  then have "relabel_stree f s' = s" unfolding l_def s'_def
    using relabel_stree_relabel_ltree by fastforce
  then have app_rgraph_iso: "app_rgraph_isomorphism f t' = t" unfolding s_def t'_def t_def
    using t' tree_graph_stree_of_graph by (simp add: app_rgraph_iso_tree_graph_stree)
  have "inj_on f (nodes_stree s')" unfolding s'_def using inj_on_l' by simp
  then have inj_on_V': "inj_on f V'" using t' nodes_tree_graph_stree unfolding t'_def by fast
  have "(V',E',r') \<simeq>\<^sub>r (V,E,r)" using app_rgraph_iso t'.rgraph_isomorph_app_iso inj_on_V' unfolding t' t_def by auto
  then show ?thesis using t' unfolding tree_graph_def t_def s_def l_def l'_def s'_def t'_def by auto
qed

lemma (in rtree) stree_size_stree_of_graph[simp]: "stree_size (stree_of_graph (V,E,r)) = card V"
  using distinct_nodes_stree_of_graph by (simp add: distinct_nodes_stree_size_card_nodes del: stree_of_graph.simps)

lemma inj_ltree_stree: "inj ltree_stree"
proof
  fix t1 :: "'a stree"
    and t2 :: "'a stree"
  assume "ltree_stree t1 =  ltree_stree t2"
  then show "t1 = t2"
  proof (induction t1 arbitrary: t2)
    case (SNode r1 ts1)
    obtain r2 ts2 where t2: "t2 = SNode r2 ts2" using stree.exhaust by blast
    then show ?case using SNode by (simp, metis SNode.prems stree.inject stree_ltree_stree)
  qed
qed

lemma ltree_size_ltree_stree[simp]: "ltree_size (ltree_stree t) = stree_size t"
  using inj_ltree_stree by (induction t) (auto simp: sum_list_distinct_conv_sum_set[OF distinct_ltree_stree_subtrees] fsum.F.rep_eq,
      smt (verit, best) inj_on_def stree_ltree_stree sum.reindex_cong)

lemma tree_size_tree_ltree[simp]: "tree_size (tree_ltree t) = ltree_size t"
  by (induction t) (auto, metis comp_eq_dest_lhs map_cong)

lemma regular_ltree_stree: "regular_ltree (ltree_stree t)"
  using sorted_wrt_ltree_stree_subtrees by (induction t) auto

lemma regular_tree_ltree: "regular_ltree t \<Longrightarrow> regular (tree_ltree t)"
  by (induction t) (auto simp: sorted_map)

lemma (in rtree) tree_of_graph_regular_n_tree: "tree_ltree (ltree_stree (stree_of_graph (V,E,r))) \<in> regular_n_trees (card V)" (is "?t \<in> ?A")
proof-
  have size_t: "tree_size ?t = card V" by (simp del: stree_of_graph.simps)
  have "regular ?t" using regular_ltree_stree regular_tree_ltree by blast
  then show ?thesis using size_t unfolding regular_n_trees_def by blast
qed

lemma (in rtree) ex_regular_n_tree: "\<exists>t\<in>regular_n_trees (card V). tree_graph t \<simeq>\<^sub>r (V,E,r)"
  using tree_graph_tree_of_graph tree_of_graph_regular_n_tree by blast

subsection "Injectivity with respect to isomorphism"

lemma app_rgraph_isomorphism_relabel_stree: "app_rgraph_isomorphism f (tree_graph_stree t) = tree_graph_stree (relabel_stree f t)"
  unfolding tree_graph_stree_def by simp

text \<open>Lemmas relating the connected components of the tree graph with the root removed to the subtrees of an stree.\<close>
context
  fixes t r ts V' E'
  assumes t: "t = SNode r ts"
  assumes distinct_nodes: "distinct_stree_nodes t"
  and remove_vertex: "graph_system.remove_vertex (nodes_stree t) (tree_graph_edges t) r = (V',E')"
begin

interpretation t: rtree "nodes_stree t" "tree_graph_edges t" r using rtree_tree_graph_edges[OF distinct_nodes] unfolding t by simp

interpretation subg: ulsubgraph V' E' "nodes_stree t" "tree_graph_edges t" using remove_vertex t.subgraph_remove_vertex t.ulgraph_axioms ulsubgraph_def t by blast

interpretation g': ulgraph V' E' using subg.is_subgraph_ulgraph t.ulgraph_axioms by blast

lemma neighborhood_root: "t.neighborhood r = root_stree ` fset ts"
  unfolding t.neighborhood_def t.vert_adj_def using distinct_nodes tree_graph_edges_wf root_stree_wf t
    by (auto, blast, fastforce, blast, blast)

lemma V': "V' = nodes_stree t - {r}"
  using remove_vertex distinct_nodes unfolding t.remove_vertex_def by blast

lemma E': "E' = \<Union> (tree_graph_edges ` fset ts)"
  using tree_graph_edges_wf distinct_nodes remove_vertex t unfolding t.remove_vertex_def t.incident_def by auto

lemma subtrees_not_connected:
  assumes s_in_ts: "s \<in> fset ts"
    and e: "{u, v} \<in> E'"
    and u_in_s: "u \<in> nodes_stree s"
  shows "v \<in> nodes_stree s"
proof-
  have "{u,v} \<in> tree_graph_edges s" using e u_in_s tree_graph_edges_wf s_in_ts distinct_nodes t unfolding E'
    by (auto simp: disjoint_family_on_def,
        smt (verit, del_insts) insert_absorb insert_disjoint(2) insert_subset tree_graph_edges_wf)
  then show ?thesis using tree_graph_edges_wf u_in_s by blast
qed

lemma subtree_connected_components:
  assumes s_in_ts: "s \<in> fset ts"
  shows "nodes_stree s \<in> g'.connected_components"
proof-
  interpret s: rtree "nodes_stree s" "tree_graph_edges s" "root_stree s" using rtree_tree_graph_edges distinct_nodes s_in_ts t by auto
  interpret subg': ulsubgraph "nodes_stree s" "tree_graph_edges s" V' E' using distinct_nodes s_in_ts t by unfold_locales (auto simp: V' E')
  have conn_set: "g'.is_connected_set (nodes_stree s)" using s.connected subg'.is_connected_set by blast
  then show ?thesis using subtrees_not_connected s_in_ts g'.connected_set_connected_component nodes_stree_non_empty by fast
qed

lemma connected_components_subtrees: "g'.connected_components = nodes_stree ` fset ts"
proof-
  have nodes_ts_ss_conn_comps: "nodes_stree ` fset ts \<subseteq> g'.connected_components" using subtree_connected_components by blast
  have Un_nodes_ts: "\<Union>(nodes_stree ` fset ts) = V'" unfolding V' using distinct_nodes t by auto
  show ?thesis using g'.subset_conn_comps_if_Union[OF nodes_ts_ss_conn_comps Un_nodes_ts] by simp
qed

lemma induced_edges_subtree:
  assumes s_in_ts: "s \<in> fset ts"
  shows "graph_system.induced_edges E' (nodes_stree s) = tree_graph_edges s"
proof-
  have "graph_system.induced_edges E' (nodes_stree s) = {e \<in> \<Union> (tree_graph_edges ` fset ts). e \<subseteq> nodes_stree s}" using subg.H.induced_edges_def E' by auto
  also have "\<dots> = tree_graph_edges s"
    using s_in_ts distinct_nodes tree_graph_edges_wf t
    by (auto simp: disjoint_family_on_def,
        metis card.empty card_tree_graph_edges_distinct inf.bounded_iff nat.simps(3) numeral_2_eq_2 subset_empty)
  finally show ?thesis .
qed

lemma root_subtree:
  assumes s_in_ts: "s \<in> fset ts"
  shows "(THE r'. r' \<in> (nodes_stree s) \<and> t.vert_adj r r') = root_stree s"
proof
  show "root_stree s \<in> nodes_stree s \<and> t.vert_adj r (root_stree s)" unfolding t.vert_adj_def using t root_stree_wf s_in_ts by auto
next
  fix r'
  assume r': "r' \<in> nodes_stree s \<and> t.vert_adj r r'"
  then have edge_in_root_edges: "{r, r'} \<in> (\<lambda>t. {r, root_stree t}) ` fset ts"
    unfolding t.vert_adj_def using distinct_nodes tree_graph_edges_wf t by fastforce
  have "\<forall>s'\<in>fset ts. s' \<noteq> s \<longrightarrow> r' \<notin> nodes_stree s'"
    using distinct_nodes s_in_ts r' unfolding t by (auto simp: disjoint_family_on_def)
  then show "r' = root_stree s" using edge_in_root_edges root_stree_wf by (smt (verit) doubleton_eq_iff image_iff)
qed

lemma subtrees_tree_subtrees: "t.subtrees = tree_graph_stree ` fset ts"
  unfolding t.subtrees_def tree_graph_stree_def using remove_vertex
  by (simp add: connected_components_subtrees image_comp induced_edges_subtree root_subtree)

end

lemma stree_of_graph_tree_graph_stree[simp]: "distinct_stree_nodes t \<Longrightarrow> stree_of_graph (tree_graph_stree t) = t"
proof (induction t)
  case (SNode r ts)
  define t where t: "t = SNode r ts"
  then have root_t[simp]: "root_stree t = r" by simp
  have distinct_t: "distinct_stree_nodes t" using SNode(2) t by blast
  interpret t: rtree "nodes_stree t" "tree_graph_edges t" r using SNode(2) rtree_tree_graph_edges t by (metis root_stree.simps)
  obtain V' E' where remove_vertex: "t.remove_vertex r = (V',E')" by fastforce

  have "stree_of_graph (tree_graph_stree t) = SNode r ts" unfolding tree_graph_stree_def
    using SNode t.rtree_axioms t.rtree_subtree
    by (simp add: subtrees_tree_subtrees[OF t distinct_t remove_vertex] image_comp fset_inverse)
  then show ?case unfolding t .
qed

lemma distinct_nodes_relabel: "distinct_stree_nodes t \<Longrightarrow> inj_on f (nodes_stree t) \<Longrightarrow> distinct_stree_nodes (relabel_stree f t)"
  by (induction t) (auto simp: image_UN disjoint_family_on_def inj_on_def, metis IntI empty_iff)

lemma relabel_stree_app_rgraph_isomorphism:
  assumes "distinct_stree_nodes t"
    and "inj_on f (nodes_stree t)"
  shows "relabel_stree f t = stree_of_graph (app_rgraph_isomorphism f (tree_graph_stree t))"
  using assms by (auto simp: app_rgraph_isomorphism_relabel_stree distinct_nodes_relabel)

lemma (in rgraph_isomorphism) app_rgraph_isomorphism_G: "app_rgraph_isomorphism f (V\<^sub>G,E\<^sub>G,r\<^sub>G) = (V\<^sub>H,E\<^sub>H,r\<^sub>H)"
  using bij_f edge_preserving root_preserving unfolding bij_betw_def by simp

lemma tree_graphs_iso_strees_iso:
  assumes "tree_graph_stree t1 \<simeq>\<^sub>r tree_graph_stree t2"
    and distinct_t1: "distinct_stree_nodes t1"
    and distinct_t2: "distinct_stree_nodes t2"
  shows "\<exists>f. inj_on f (nodes_stree t1) \<and> relabel_stree f t1 = t2"
proof-
  obtain f where "rgraph_isomorphism (nodes_stree t1) (tree_graph_edges t1) (root_stree t1) (nodes_stree t2) (tree_graph_edges t2) (root_stree t2) f"
    using assms unfolding tree_graph_stree_def by auto
  then interpret rgraph_isomorphism "nodes_stree t1" "tree_graph_edges t1" "root_stree t1" "nodes_stree t2" "tree_graph_edges t2" "root_stree t2" f .
  have inj: "inj_on f (nodes_stree t1)" using bij_f bij_betw_imp_inj_on by blast
  have "relabel_stree f t1 = t2"
    unfolding relabel_stree_app_rgraph_isomorphism[OF distinct_t1 inj] tree_graph_stree_def app_rgraph_isomorphism_G
    using stree_of_graph_tree_graph_stree[OF distinct_t2, unfolded tree_graph_stree_def] by blast
  then show ?thesis using inj by blast
qed

text \<open>Skip the ltree representation as it introduces complications with the proofs\<close>

fun tree_stree :: "'a stree \<Rightarrow> tree" where
  "tree_stree (SNode r ts) = Node (sorted_list_of_multiset (image_mset tree_stree (mset_set (fset ts))))"

fun postorder_label_stree_aux :: "nat \<Rightarrow> tree \<Rightarrow> nat \<times> nat stree" where
  "postorder_label_stree_aux n (Node []) = (n, SNode n {||})"
| "postorder_label_stree_aux n (Node (t#ts)) =
  (let (n', t') = postorder_label_stree_aux n t in
    case postorder_label_stree_aux (Suc n') (Node ts) of
      (n'', SNode r ts') \<Rightarrow> (n'', SNode r (finsert t' ts')))"

definition postorder_label_stree :: "tree \<Rightarrow> nat stree" where
  "postorder_label_stree t = snd (postorder_label_stree_aux 0 t)"

lemma fst_postorder_label_stree_aux_eq: "fst (postorder_label_stree_aux n t) = fst (postorder_label_aux n t)"
  by (induction n t rule: postorder_label_stree_aux.induct) (auto split: prod.split stree.split ltree.split)

lemma postorder_label_stree_aux_eq: "snd (postorder_label_stree_aux n t) = stree_ltree (snd (postorder_label_aux n t))"
  by (induction n t rule: postorder_label_aux.induct) (simp, simp split: prod.split stree.split ltree.split,
      metis fset_of_list_map fst_conv fst_postorder_label_stree_aux_eq sndI stree.inject stree_ltree.simps)

lemma postorder_label_stree_eq: "postorder_label_stree t = stree_ltree (postorder_label t)"
  using postorder_label_stree_aux_eq unfolding postorder_label_stree_def postorder_label_def by blast

lemma postorder_label_stree_aux_mono: "fst (postorder_label_stree_aux n t) \<ge> n"
  by (induction n t rule: postorder_label_stree_aux.induct) (auto split: prod.split stree.split, fastforce)

lemma nodes_postorder_label_stree_aux_ge: "postorder_label_stree_aux n t = (n', t') \<Longrightarrow> v \<in> nodes_stree t' \<Longrightarrow> v \<ge> n"
  by (induction n t arbitrary: n' t' rule: postorder_label_stree_aux.induct,
      auto split: prod.splits stree.splits,
      (metis fst_conv le_SucI order.trans postorder_label_stree_aux_mono)+)

lemma nodes_postorder_label_stree_aux_le: "postorder_label_stree_aux n t = (n', t') \<Longrightarrow> v \<in> nodes_stree t' \<Longrightarrow> v \<le> n'"
  by (induction n t arbitrary: n' t' rule: postorder_label_stree_aux.induct,
      auto split: prod.splits stree.splits,
      metis Suc_leD fst_conv order_trans postorder_label_stree_aux_mono,
      blast)

lemma distinct_nodes_postorder_label_stree_aux: "distinct_stree_nodes (snd (postorder_label_stree_aux n t))"
proof (induction n t rule: postorder_label_stree_aux.induct)
  case (1 n)
  then show ?case by (simp add: disjoint_family_on_def)
next
  case (2 n t ts)
  obtain n' t' where t': "postorder_label_stree_aux n t = (n', t')" by fastforce
  obtain n'' r ts' where ts': "postorder_label_stree_aux (Suc n') (Node ts) = (n'', SNode r ts')"
    by (metis eq_snd_iff stree.exhaust)
  then have "r \<ge> Suc n'" using nodes_postorder_label_stree_aux_ge by auto
  then have r_notin_t': "r \<notin> nodes_stree t'" using nodes_postorder_label_stree_aux_le[OF t'] by fastforce
  have "disjoint_family_on nodes_stree (insert t' (fset ts'))"
    using 2 t' ts' nodes_postorder_label_stree_aux_le[OF t'] nodes_postorder_label_stree_aux_ge[OF ts']
    by (auto simp add: disjoint_family_on_def, fastforce+)
  then show ?case using 2 t' ts' r_notin_t' by simp
qed

lemma distinct_nodes_postorder_label_stree: "distinct_stree_nodes (postorder_label_stree t)"
  unfolding postorder_label_stree_def using distinct_nodes_postorder_label_stree_aux by simp

lemma tree_stree_postorder_label_stree_aux: "regular t \<Longrightarrow> tree_stree (snd (postorder_label_stree_aux n t)) = t"
proof (induction t rule: postorder_label_stree_aux.induct)
  case (1 n)
  then show ?case by auto
next
  case (2 n t ts)
  obtain n' t' where nt': "postorder_label_stree_aux n t = (n', t')" by fastforce
  obtain n'' r ts' where nt'': "postorder_label_stree_aux (Suc n') (Node ts) = (n'', SNode r ts')"
    using stree.exhaust prod.exhaust by metis
  have "t' \<notin> fset ts'" using nodes_postorder_label_stree_aux_le[OF nt'] nodes_postorder_label_stree_aux_ge[OF nt'']
    by (auto, meson not_less_eq_eq root_stree_wf)
  then show ?case using 2 nt' nt'' by (auto simp: insort_is_Cons)
qed

lemma tree_ltree_postorder_label_stree[simp]: "regular t \<Longrightarrow> tree_stree (postorder_label_stree t) = t"
  using tree_stree_postorder_label_stree_aux unfolding postorder_label_stree_def by blast

lemma inj_relabel_subtrees:
  assumes distinct_nodes: "distinct_stree_nodes (SNode r ts)"
    and inj_on_nodes: "inj_on f (nodes_stree (SNode r ts))"
  shows "inj_on (relabel_stree f) (fset ts)"
proof
  fix t1 t2
  assume t1_subtree: "t1 \<in> fset ts"
    and t2_subtree: "t2 \<in> fset ts"
    and relabel_eq: "relabel_stree f t1 = relabel_stree f t2"
  then have "nodes_stree (relabel_stree f t1) = nodes_stree (relabel_stree f t2)" by simp
  then have "f ` nodes_stree t1 = f ` nodes_stree t2" by simp
  then have "nodes_stree t1 = nodes_stree t2" using inj_on_nodes t1_subtree t2_subtree inj_on_image[of f "nodes_stree ` fset ts"]
    by (simp, meson image_eqI inj_onD)
  then show "t1 = t2" using distinct_nodes nodes_stree_non_empty t1_subtree t2_subtree
    by (auto simp add: disjoint_family_on_def, force)
qed

lemma inj_on_subtree: "inj_on f (nodes_stree (SNode r ts)) \<Longrightarrow> t \<in> fset ts \<Longrightarrow> inj_on f (nodes_stree t)"
  unfolding inj_on_def by simp

lemma tree_stree_relabel_stree: "distinct_stree_nodes t \<Longrightarrow> inj_on f (nodes_stree t) \<Longrightarrow> tree_stree (relabel_stree f t) = tree_stree t"
proof (induction t)
  case (SNode r ts)
  then have IH: "\<forall>t\<in># mset_set (fset ts). tree_stree (relabel_stree f t) = tree_stree t"
    using inj_on_subtree[OF SNode(3)] elem_mset_set finite_fset by auto
  show ?case using inj_relabel_subtrees[OF SNode(2) SNode(3)]
    by (auto simp add: mset_set_image_inj, metis IH image_mset_cong)
qed

lemma tree_ltree_relabel_ltree_postorder_label_stree: "regular t \<Longrightarrow> inj_on f (nodes_stree (postorder_label_stree t)) \<Longrightarrow> tree_stree (relabel_stree f (postorder_label_stree t)) = t"
  using tree_stree_relabel_stree distinct_nodes_postorder_label_stree by fastforce

lemma postorder_label_stree_inj: "regular t1 \<Longrightarrow> regular t2 \<Longrightarrow> inj_on f (nodes_stree (postorder_label_stree t1)) \<Longrightarrow> relabel_stree f (postorder_label_stree t1) = postorder_label_stree t2 \<Longrightarrow> t1 = t2"
  using tree_ltree_relabel_ltree_postorder_label_stree by fastforce

lemma tree_graph_inj_iso: "regular t1 \<Longrightarrow> regular t2 \<Longrightarrow> tree_graph t1 \<simeq>\<^sub>r tree_graph t2 \<Longrightarrow> t1 = t2"
  using postorder_label_stree_inj tree_graphs_iso_strees_iso distinct_nodes_postorder_label
    distinct_nodes_stree_ltree postorder_label_stree_eq unfolding tree_graph_def by metis

lemma tree_graph_inj:
  assumes regular_t1: "regular t1"
    and regular_t2: "regular t2"
    and tree_graph_eq: "tree_graph t1 = tree_graph t2"
  shows "t1 = t2"
proof-
  obtain V E r where g: "tree_graph t1 = (V,E,r)" using prod.exhaust by metis
  then interpret rtree V E r using rtree_tree_graph by auto
  have "tree_graph t1 \<simeq>\<^sub>r tree_graph t2" using tree_graph_eq g rgraph_isomorph_refl by simp
  then show ?thesis using tree_graph_inj_iso regular_t1 regular_t2 by simp
qed

end