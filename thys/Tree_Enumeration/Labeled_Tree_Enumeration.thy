section \<open>Enumeration of Labeled Trees\<close>

theory Labeled_Tree_Enumeration
  imports Tree_Graph
begin

definition labeled_trees :: "'a set \<Rightarrow> 'a pregraph set" where
  "labeled_trees V = {(V,E)| E. tree V E}"

subsection \<open>Algorithm\<close>

text \<open>Prüfer sequence to tree\<close>

definition prufer_sequences :: "'a list \<Rightarrow> 'a list set" where
  "prufer_sequences verts = {xs. length xs = length verts - 2 \<and> set xs \<subseteq> set verts}"

fun tree_edges_of_prufer_seq :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a edge set" where
  "tree_edges_of_prufer_seq [u,v] [] = {{u,v}}"
| "tree_edges_of_prufer_seq verts (b#seq) =
    (case find (\<lambda>x. x \<notin> set (b#seq)) verts of
      Some a \<Rightarrow> insert {a,b} (tree_edges_of_prufer_seq (remove1 a verts) seq))"

definition tree_of_prufer_seq :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a pregraph" where
  "tree_of_prufer_seq verts seq = (set verts, tree_edges_of_prufer_seq verts seq)"

definition labeled_tree_enum :: "'a list \<Rightarrow> 'a pregraph list" where
  "labeled_tree_enum verts = map (tree_of_prufer_seq verts) (List.n_lists (length verts - 2) verts)"


subsection \<open>Correctness\<close>

text \<open>Tree to Prüfer sequence\<close>

definition remove_vertex_edges :: "'a \<Rightarrow> 'a edge set \<Rightarrow> 'a edge set" where
  "remove_vertex_edges v E = {e\<in>E. \<not> graph_system.incident v e}"

lemma find_in_list[termination_simp]: "find P verts = Some v \<Longrightarrow> v \<in> set verts"
  by (metis find_Some_iff nth_mem)

lemma [termination_simp]: "find P verts = Some v \<Longrightarrow> length verts - Suc 0 < length verts"
  by (meson diff_Suc_less length_pos_if_in_set find_in_list)

fun prufer_seq_of_tree :: "'a list \<Rightarrow> 'a edge set \<Rightarrow> 'a list" where
  "prufer_seq_of_tree verts E =
    (if length verts \<le> 2 then []
    else (case find (tree.leaf E) verts of
      Some leaf \<Rightarrow> (THE v. ulgraph.vert_adj E leaf v) # prufer_seq_of_tree (remove1 leaf verts) (remove_vertex_edges leaf E)))"

locale valid_verts =
  fixes verts
  assumes length_verts: "length verts \<ge> 2"
  and distinct_verts: "distinct verts"

locale tree_of_prufer_seq_ctx = valid_verts +
  fixes seq
  assumes prufer_seq: "seq \<in> prufer_sequences verts"

lemma (in valid_verts) card_verts: "card (set verts) = length verts"
  using length_verts distinct_verts distinct_card by blast

lemma length_gt_find_not_in_ys:
  assumes "length xs > length ys"
    and "distinct xs"
  shows "\<exists>x. find (\<lambda>x. x \<notin> set ys) xs = Some x"
proof-
  have "card (set xs) > card (set ys)"
    by (metis assms card_length distinct_card le_neq_implies_less order_less_trans)
  then have "\<exists>x\<in>set xs. x \<notin> set ys"
    by (meson finite_set card_subset_not_gt_card subsetI)
  then show ?thesis by (metis find_None_iff2 not_Some_eq)
qed

lemma (in tree_of_prufer_seq_ctx) tree_edges_of_prufer_seq_induct':
  assumes "\<And>u v. P [u, v] []"
    and "\<And>verts b seq a.
            find (\<lambda>x. x \<notin> set (b # seq)) verts = Some a
            \<Longrightarrow> a \<in> set verts \<Longrightarrow> a \<notin> set (b # seq) \<Longrightarrow> seq \<in> prufer_sequences (remove1 a verts)
            \<Longrightarrow> tree_of_prufer_seq_ctx (remove1 a verts) seq \<Longrightarrow> P (remove1 a verts) seq \<Longrightarrow> P verts (b # seq)"
  shows "P verts seq"
  using tree_of_prufer_seq_ctx_axioms
proof (induction verts seq rule: tree_edges_of_prufer_seq.induct)
  case (2 verts b seq)
  then interpret tree_of_prufer_seq_ctx verts "b # seq" by simp
  obtain a where a_find: "find (\<lambda>x. x \<notin> set (b # seq)) verts = Some a"
    using length_gt_find_not_in_ys[of "b#seq" verts] distinct_verts prufer_seq
    unfolding prufer_sequences_def by fastforce
  then have a_in_verts: "a \<in> set verts" by (simp add: find_in_list)
  have a_not_in_seq: "a \<notin> set (b#seq)" using a_find by (metis find_Some_iff)
  have prufer_seq': "seq \<in> prufer_sequences (remove1 a verts)"
    using prufer_seq a_in_verts set_remove1_eq length_verts a_not_in_seq distinct_verts
    unfolding prufer_sequences_def by (auto simp: length_remove1)
  have "length verts \<ge> 3" using prufer_seq unfolding prufer_sequences_def by auto
  then have "length (remove1 a verts) \<ge> 2" by (auto simp: length_remove1)
  then have valid_verts_seq': "tree_of_prufer_seq_ctx (remove1 a verts) seq"
    using prufer_seq' distinct_verts by unfold_locales auto
  then show ?case using a_find assms(2) a_in_verts a_not_in_seq prufer_seq' 2(1) by blast
qed (auto simp: assms tree_of_prufer_seq_ctx_def tree_of_prufer_seq_ctx_axioms_def valid_verts_def prufer_sequences_def)

lemma (in tree_of_prufer_seq_ctx) tree_edges_of_prufer_seq_tree:
  shows "tree (set verts) (tree_edges_of_prufer_seq verts seq)"
  using tree_of_prufer_seq_ctx_axioms
proof (induction rule: tree_edges_of_prufer_seq_induct')
  case (1 u v)
  then show ?case using tree2 unfolding tree_of_prufer_seq_ctx_def valid_verts_def by fastforce
next
  case (2 verts b seq a)
  interpret tree_of_prufer_seq_ctx verts "b # seq" using 2(7) .
  interpret tree "set (remove1 a verts)" "tree_edges_of_prufer_seq (remove1 a verts) seq"
    using 2(5,6) by simp
  have a_not_in_verts': "a \<notin> set (remove1 a verts)" using distinct_verts by simp
  have "a \<noteq> b" using 2 by auto
  then have b_in_verts': "b \<in> set (remove1 a verts)" using prufer_seq unfolding prufer_sequences_def by auto
  then show ?case using a_not_in_verts' add_vertex_tree[OF a_not_in_verts' b_in_verts'] 2(1,2) distinct_verts
    by (auto simp: insert_absorb insert_commute)
qed

lemma (in tree_of_prufer_seq_ctx) tree_of_prufer_seq_tree: "(V,E) = tree_of_prufer_seq verts seq \<Longrightarrow> tree V E"
  unfolding tree_of_prufer_seq_def using tree_edges_of_prufer_seq_tree by auto

lemma (in valid_verts) labeled_tree_enum_trees:
  assumes VE_in_labeled_tree_enum: "(V,E) \<in> set (labeled_tree_enum verts)"
  shows "tree V E"
proof-
  obtain seq where "seq \<in> set (List.n_lists (length verts - 2) verts)" and tree_of_seq: "tree_of_prufer_seq verts seq = (V,E)"
    using VE_in_labeled_tree_enum unfolding labeled_tree_enum_def by auto
  then interpret tree_of_prufer_seq_ctx verts seq
    using List.set_n_lists by (unfold_locales) (auto simp: prufer_sequences_def)
  show ?thesis using tree_of_prufer_seq_tree using tree_of_seq by simp
qed

subsection \<open>Totality\<close>

locale prufer_seq_of_tree_context =
  valid_verts verts + tree "set verts" E for verts E
begin

lemma prufer_seq_of_tree_induct':
  assumes "\<And>u v. P [u,v] {{u,v}}"
    and "\<And>verts E l. \<not> length verts \<le> 2 \<Longrightarrow> find (tree.leaf E) verts = Some l \<Longrightarrow> tree.leaf E l
        \<Longrightarrow> l \<in> set verts \<Longrightarrow> prufer_seq_of_tree_context (remove1 l verts) (remove_vertex_edges l E)
        \<Longrightarrow> P (remove1 l verts) (remove_vertex_edges l E) \<Longrightarrow> P verts E"
  shows "P verts E"
  using prufer_seq_of_tree_context_axioms
proof (induction verts E rule: prufer_seq_of_tree.induct)
  case (1 verts E)
  then interpret ctx: prufer_seq_of_tree_context verts E by simp
  show ?case
  proof (cases "length verts \<le> 2")
    case True
    then have length_verts: "length verts = 2" using ctx.length_verts by simp
    then obtain u w where verts: "verts = [u,w]"
      unfolding numeral_2_eq_2 by (metis length_0_conv length_Suc_conv)
    then have "E = {{u,w}}" using ctx.connected_two_graph_edges ctx.distinct_verts by simp
    then show ?thesis using assms(1) verts by blast
  next
    case False
    then have "ctx.non_trivial" using ctx.distinct_verts distinct_card
      unfolding ctx.non_trivial_def by fastforce
    then obtain l where l: "find ctx.leaf verts = Some l" using ctx.exists_leaf
      by (metis find_None_iff2 not_Some_eq)
    then have leaf_l: "ctx.leaf l" by (metis find_Some_iff)
    then have l_in_verts: "l \<in> set verts" using ctx.leaf_in_V by simp
    then have length_verts': "length (remove1 l verts) \<ge> 2" using False unfolding length_remove1 by simp
    have "tree (set (remove1 l verts)) (remove_vertex_edges l E)" using ctx.tree_remove_leaf[OF leaf_l]
      unfolding ctx.remove_vertex_def remove_vertex_edges_def using ctx.distinct_verts by simp
    then have ctx': "prufer_seq_of_tree_context (remove1 l verts) (remove_vertex_edges l E)"
      unfolding prufer_seq_of_tree_context_def valid_verts_def
      using ctx.distinct_verts length_verts' by simp
    then have "P (remove1 l verts) (remove_vertex_edges l E)" using 1 False l by simp
    then show ?thesis using assms(2)[OF False l leaf_l l_in_verts ctx'] by simp
  qed
qed

lemma prufer_seq_of_tree_wf: "set (prufer_seq_of_tree verts E) \<subseteq> set verts"
  using prufer_seq_of_tree_context_axioms
proof (induction rule: prufer_seq_of_tree_induct')
  case (1 u v)
  then show ?case by simp
next
  case (2 verts E l)
  then interpret ctx: prufer_seq_of_tree_context verts E by simp
  let ?u = "THE u. ctx.vert_adj l u"
  have l_u_adj: "ctx.vert_adj l ?u" using ctx.ex1_neighbor_degree_1 2(3) unfolding ctx.leaf_def by (metis theI)
  then have "?u \<in> set verts" unfolding ctx.vert_adj_def using ctx.wellformed_alt_snd by blast
  then show ?case using 2 ctx.ex1_neighbor_degree_1 2(3)
    by (auto, meson in_mono notin_set_remove1)
qed

lemma length_prufer_seq_of_tree: "length (prufer_seq_of_tree verts E) = length verts - 2"
proof (induction rule: prufer_seq_of_tree_induct')
  case (1 u v)
  then show ?case by simp
next
  case (2 verts E l)
  then show ?case unfolding prufer_seq_of_tree.simps[of verts] by (simp add: length_remove1)
qed

lemma prufer_seq_of_tree_prufer_seq: "prufer_seq_of_tree verts E \<in> prufer_sequences verts"
  using prufer_seq_of_tree_wf length_prufer_seq_of_tree unfolding prufer_sequences_def by blast

lemma count_list_prufer_seq_degree: "v \<in> set verts \<Longrightarrow> Suc (count_list (prufer_seq_of_tree verts E) v) = degree v"
  using prufer_seq_of_tree_context_axioms
proof (induction rule: prufer_seq_of_tree_induct')
  case (1 u v)
  then interpret ctx: prufer_seq_of_tree_context "[u, v]" "{{u, v}}" by simp
  show ?case using 1(1) unfolding ctx.alt_degree_def ctx.incident_edges_def ctx.incident_def
    by (simp add: Collect_conv_if)
next
  case (2 verts E l)
  then interpret ctx: prufer_seq_of_tree_context verts E by simp
  interpret ctx': prufer_seq_of_tree_context "remove1 l verts" "remove_vertex_edges l E" using 2(5) by simp
  let ?u = "THE u. ctx.vert_adj l u"
  have l_u_adj: "ctx.vert_adj l ?u" using ctx.ex1_neighbor_degree_1 2(3) unfolding ctx.leaf_def by (metis theI)
  show ?case
  proof (cases "v = ?u")
    case True
    then have "v \<noteq> l" using l_u_adj ctx.vert_adj_not_eq by blast
    then have "count_list (prufer_seq_of_tree verts E) v = ulgraph.degree (remove_vertex_edges l E) v"
      using 2 True by simp
    then show ?thesis using 2 ctx.degree_remove_adj_ne_vert \<open>v\<noteq>l\<close> True l_u_adj
      unfolding ctx.remove_vertex_def remove_vertex_edges_def prufer_seq_of_tree.simps[of verts] by simp
  next
    case False
    then show ?thesis
    proof (cases "v = l")
      case True
      then have "l \<notin> set (remove1 l verts)" using ctx.distinct_verts by simp
      then have "l \<notin> set (prufer_seq_of_tree (remove1 l verts) (remove_vertex_edges l E))" using ctx'.prufer_seq_of_tree_wf by blast
      then show ?thesis using 2 False True unfolding ctx.leaf_def prufer_seq_of_tree.simps[of verts] by simp
    next
      case False
      then have "\<not> ctx.vert_adj l v" using \<open>v\<noteq>?u\<close> ctx.ex1_neighbor_degree_1 2(3) l_u_adj
        unfolding ctx.leaf_def by blast
      then show ?thesis using False 2 \<open>v\<noteq>?u\<close> ctx.degree_remove_non_adj_vert
        unfolding prufer_seq_of_tree.simps[of verts] ctx'.remove_vertex_def remove_vertex_edges_def ctx.remove_vertex_def by auto
    qed
  qed
qed

lemma not_in_prufer_seq_iff_leaf: "v \<in> set verts \<Longrightarrow> v \<notin> set (prufer_seq_of_tree verts E) \<longleftrightarrow> leaf v"
  using count_list_prufer_seq_degree[symmetric] unfolding leaf_def by (simp add: count_list_0_iff)

lemma tree_edges_of_prufer_seq_of_tree: "tree_edges_of_prufer_seq verts (prufer_seq_of_tree verts E) = E"
  using prufer_seq_of_tree_context_axioms
proof (induction rule: prufer_seq_of_tree_induct')
  case (1 u v)
  then show ?case by simp
next
  case (2 verts E l)
  then interpret ctx: prufer_seq_of_tree_context verts E by simp
  have "tree_edges_of_prufer_seq verts (prufer_seq_of_tree verts E)
    = tree_edges_of_prufer_seq verts ((THE v. ctx.vert_adj l v) # prufer_seq_of_tree (remove1 l verts) (remove_vertex_edges l E))" using 2 by simp
  have "find (\<lambda>x. x \<notin> set (prufer_seq_of_tree verts E)) verts = Some l" using ctx.not_in_prufer_seq_iff_leaf 2(2)
    by (metis (no_types, lifting) find_cong)
  then have "tree_edges_of_prufer_seq verts (prufer_seq_of_tree verts E)
    = insert {The (ctx.vert_adj l), l} (tree_edges_of_prufer_seq (remove1 l verts) (prufer_seq_of_tree (remove1 l verts) (remove_vertex_edges l E)))"
    using 2 by auto
  also have "\<dots> = E" using 2 ctx.degree_1_edge_partition unfolding remove_vertex_edges_def incident_def ctx.leaf_def by simp
  finally show ?case .
qed

lemma tree_in_labeled_tree_enum: "(set verts, E) \<in> set (labeled_tree_enum verts)"
  using prufer_seq_of_tree_prufer_seq tree_edges_of_prufer_seq_of_tree List.set_n_lists
    unfolding prufer_sequences_def labeled_tree_enum_def tree_of_prufer_seq_def by fastforce

end

lemma (in valid_verts) V_labeled_tree_enum_verts: "(V,E) \<in> set (labeled_tree_enum verts) \<Longrightarrow> V = set verts"
  unfolding labeled_tree_enum_def by (metis Pair_inject ex_map_conv tree_of_prufer_seq_def)

theorem (in valid_verts) labeled_tree_enum_correct: "set (labeled_tree_enum verts) = labeled_trees (set verts)"
  using labeled_tree_enum_trees V_labeled_tree_enum_verts prufer_seq_of_tree_context.tree_in_labeled_tree_enum valid_verts_axioms
  unfolding labeled_trees_def prufer_seq_of_tree_context_def by fast

subsection \<open>Distinction\<close>

lemma (in tree_of_prufer_seq_ctx) count_prufer_seq_degree:
  assumes v_in_verts: "v \<in> set verts"
  shows "Suc (count_list seq v) = ulgraph.degree (tree_edges_of_prufer_seq verts seq) v"
  using v_in_verts tree_of_prufer_seq_ctx_axioms
proof (induction rule: tree_edges_of_prufer_seq_induct')
  case (1 u w)
  then interpret tree_of_prufer_seq_ctx "[u, w]" "[]" by simp
  interpret tree "{u,w}" "{{u,w}}" using tree_edges_of_prufer_seq_tree by simp
  show ?case using 1(1) by (auto simp add: incident_edges_def incident_def Collect_conv_if)
next
  case (2 verts b seq a)
  interpret tree_of_prufer_seq_ctx verts "b # seq" using 2(8) .
  interpret tree "set verts" "tree_edges_of_prufer_seq verts (b#seq)"
    using tree_edges_of_prufer_seq_tree by simp
  interpret ctx': tree_of_prufer_seq_ctx "remove1 a verts" seq using 2(5) .
  interpret T': tree "set (remove1 a verts)" "tree_edges_of_prufer_seq (remove1 a verts) seq"
    using ctx'.tree_edges_of_prufer_seq_tree by simp
  show ?case
  proof (cases "v = b")
    case True
    have ab_not_in_T': "{a, b} \<notin> tree_edges_of_prufer_seq (remove1 a verts) seq"
      using T'.wellformed_alt_snd distinct_verts by (auto, metis doubleton_eq_iff)
    have "incident_edges v = insert {a,b} {e \<in> tree_edges_of_prufer_seq (remove1 a verts) seq. v \<in> e}"
      unfolding incident_edges_def incident_def using 2(1) True by auto
    then have "degree v = Suc (T'.degree v)"
      unfolding T'.alt_degree_def alt_degree_def T'.incident_edges_def incident_def
      using ab_not_in_T' T'.fin_edges by (simp del: tree_edges_of_prufer_seq.simps)
    then show ?thesis using 2 True by auto
  next
    case False
    then show ?thesis
    proof (cases "v = a")
      case True
      also have "incident_edges a = {{a,b}}" unfolding incident_edges_def incident_def
        using 2(1) T'.wellformed distinct_verts by auto
      then show ?thesis unfolding alt_degree_def True using 2(3) by auto
    next
      case False
      then have "incident_edges v = T'.incident_edges v"
        unfolding incident_edges_def T'.incident_edges_def incident_def using 2(1) \<open>v \<noteq> b\<close> by auto
      then show ?thesis using False \<open>v \<noteq> b\<close> 2 unfolding alt_degree_def by simp
    qed
  qed
qed

lemma (in tree_of_prufer_seq_ctx) notin_prufer_seq_iff_leaf:
  assumes "v \<in> set verts"
  shows "v \<notin> set seq \<longleftrightarrow> tree.leaf (tree_edges_of_prufer_seq verts seq) v"
proof-
  interpret tree "set verts" "tree_edges_of_prufer_seq verts seq"
    using tree_edges_of_prufer_seq_tree by auto
  show ?thesis using count_prufer_seq_degree assms count_list_0_iff unfolding leaf_def by fastforce
qed

lemma (in valid_verts) inj_tree_edges_of_prufer_seq: "inj_on (tree_edges_of_prufer_seq verts) (prufer_sequences verts)"
proof
  fix seq1 seq2
  assume prufer_seq1: "seq1 \<in> prufer_sequences verts"
  assume prufer_seq2: "seq2 \<in> prufer_sequences verts"
  assume trees_eq: "tree_edges_of_prufer_seq verts seq1 = tree_edges_of_prufer_seq verts seq2"
  interpret tree_of_prufer_seq_ctx verts seq1 using prufer_seq1 by unfold_locales simp
  have length_eq: "length seq1 = length seq2" using prufer_seq1 prufer_seq2 unfolding prufer_sequences_def by simp
  show "seq1 = seq2"
    using prufer_seq1 prufer_seq2 trees_eq length_eq tree_of_prufer_seq_ctx_axioms
  proof (induction arbitrary: seq2 rule: tree_edges_of_prufer_seq_induct')
    case (1 u v)
    then show ?case by simp
  next
    case (2 verts b seq a)
    then interpret ctx1: tree_of_prufer_seq_ctx verts "b # seq" by simp
    interpret ctx2: tree_of_prufer_seq_ctx verts seq2 using 2 by unfold_locales blast
    obtain b' seq2' where seq2: "seq2 = b' # seq2'" using 2(10) by (metis length_Suc_conv)
    then have "find (\<lambda>x. x \<notin> set seq2) verts = Some a"
      using ctx2.notin_prufer_seq_iff_leaf 2(9) 2(1) ctx1.notin_prufer_seq_iff_leaf[symmetric] find_cong by force
    then have edges_eq: "insert {a, b} (tree_edges_of_prufer_seq (remove1 a verts) seq)
        = insert {a, b'} (tree_edges_of_prufer_seq (remove1 a verts) seq2')"
      using 2 seq2 by simp
    interpret ctx1': tree_of_prufer_seq_ctx "remove1 a verts" seq using 2(5) .
    interpret T1: tree "set (remove1 a verts)" "tree_edges_of_prufer_seq (remove1 a verts) seq"
      using ctx1'.tree_edges_of_prufer_seq_tree by blast
    have "a \<notin> set seq2'" using seq2 2 ctx1.notin_prufer_seq_iff_leaf ctx2.notin_prufer_seq_iff_leaf by auto
    then interpret ctx2': tree_of_prufer_seq_ctx "remove1 a verts" seq2'
      using seq2 2(8) 2(2) ctx1.distinct_verts
      by unfold_locales (auto simp: length_remove1 prufer_sequences_def)
    interpret T2: tree "set (remove1 a verts)" "tree_edges_of_prufer_seq (remove1 a verts) seq2'"
      using ctx2'.tree_edges_of_prufer_seq_tree by blast

    have a_notin_verts': "a \<notin> set (remove1 a verts)" using ctx1.distinct_verts by simp
    then have ab'_notin_edges: "{a,b'} \<notin> tree_edges_of_prufer_seq (remove1 a verts) seq" using T1.wellformed by blast
    then have "b = b'" using edges_eq by (metis doubleton_eq_iff insert_iff)

    have "{a,b} \<notin> tree_edges_of_prufer_seq (remove1 a verts) seq2'" using T2.wellformed a_notin_verts' by blast
    then have "(tree_edges_of_prufer_seq (remove1 a verts) seq) = tree_edges_of_prufer_seq (remove1 a verts) seq2'"
      using edges_eq ab'_notin_edges
      by (simp add: \<open>b = b'\<close> insert_eq_iff)
    then have "seq = seq2'" using "2.IH"[of seq2'] ctx1'.prufer_seq ctx2'.prufer_seq 2(10) ctx1'.tree_of_prufer_seq_ctx_axioms
      unfolding seq2 by simp
    then show ?case using \<open>b = b'\<close> seq2 by simp
  qed
qed

theorem (in valid_verts) distinct_labeld_tree_enum: "distinct (labeled_tree_enum verts)"
  using inj_tree_edges_of_prufer_seq distinct_n_lists distinct_verts
  unfolding  labeled_tree_enum_def prufer_sequences_def tree_of_prufer_seq_def
  by (auto simp add: distinct_map set_n_lists inj_on_def)

lemma (in valid_verts) cayleys_formula: "card (labeled_trees (set verts)) = length verts ^ (length verts - 2)"
proof-
  have "card (labeled_trees (set verts)) = length (labeled_tree_enum verts)"
    using distinct_labeld_tree_enum labeled_tree_enum_correct distinct_card by fastforce
  also have "\<dots> = length verts ^ (length verts - 2)" unfolding labeled_tree_enum_def using length_n_lists by auto
  finally show ?thesis .
qed

end