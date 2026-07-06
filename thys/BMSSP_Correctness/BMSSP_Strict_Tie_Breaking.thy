theory BMSSP_Strict_Tie_Breaking
  imports BMSSP_Direct_Insert_Costed
begin

section \<open>Strict Tie-Breaking Consequences\<close>

text \<open>
  Lexicographic tie-breaking removes distance ties by comparing extended path
  values.  The existing development abstracts uniqueness of shortest paths, but
  source progress for the base case also needs strict growth along the selected
  shortest-path tree.  This file records exactly that consequence, so the
  remaining complexity proof can be connected either to a formal extended-
  distance construction or to any graph model that already provides the same
  strict tree order.

  The cost recurrence uses progress statements of the form "a source set is no
  larger than the output range that completed it".  For non-base recursive
  calls this comes from the BMSSP threshold: either the call succeeds with the
  old bound, or it completes enough vertices.  The base case is subtler.  It
  takes the first \<open>k + 1\<close> vertices in distance order from a singleton source.
  To know that the singleton source itself is included, the proof needs the
  source to be the strict first element of that order.

  The strict tie-breaking locale supplies this missing monotonicity.  Along the
  chosen shortest-path tree, descendants have strictly larger distance than
  ancestors.  Consequently, in the singleton bound tree rooted at \<open>x\<close>, the
  root \<open>x\<close> is the unique minimum-distance vertex.  This is the formal
  counterpart of the paper's assumption that ties can be perturbed away without
  changing the combinatorial structure of the algorithm.

  The later half of the theory threads this progress fact through the exact
  range-costed and direct-insert costed relations.  It closes the source-
  progress side condition required by the local-budget theorems, then packages
  the resulting level and amortised graph bounds for the top-level run.
\<close>

context finite_weighted_digraph
begin

lemma walk_weight_pos_if_positive_edges:
  assumes positive: "\<And>u v. (u, v) \<in> E \<Longrightarrow> 0 < w u v"
    and walk_p: "walk p"
    and len: "1 < length p"
  shows "0 < walk_weight p"
proof (cases p)
  case Nil
  then show ?thesis
    using len by simp
next
  case (Cons x xs)
  then show ?thesis
  proof (cases xs)
    case Nil
    then show ?thesis
      using Cons len by simp
  next
    case (Cons y ys)
    have p_def: "p = x # y # ys"
      using \<open>p = x # xs\<close> Cons by simp
    have edge: "(x, y) \<in> E"
      using walk_p p_def by simp
    have tail_walk: "walk (y # ys)"
      using walk_p p_def by simp
    have "0 < w x y"
      by (rule positive[OF edge])
    moreover have "0 \<le> walk_weight (y # ys)"
      by (rule walk_weight_nonneg[OF tail_walk])
    ultimately show ?thesis
      using p_def by simp
  qed
qed

end

context unique_shortest_digraph
begin

lemma tree_path_strict_dist_if_positive_edges:
  assumes positive: "\<And>u v. (u, v) \<in> E \<Longrightarrow> 0 < w u v"
    and tree: "tree_path u v"
    and neq: "u \<noteq> v"
  shows "dist s u < dist s v"
proof -
  let ?p = "shortest_path_to v"
  have reach_v: "reachable s v" and u_path: "u \<in> set ?p"
    using tree by (auto dest: tree_pathD)
  obtain i where i: "i < length ?p" "?p ! i = u"
    using u_path by (auto simp: in_set_conv_nth)
  have sp: "shortest_walk s ?p v"
    by (rule shortest_path_to_shortest[OF reach_v])
  have simple_p: "simple_walk_betw s ?p v"
    using sp unfolding shortest_walk_def by blast
  have weight_p: "walk_weight ?p = dist s v"
    using sp unfolding shortest_walk_def by blast
  have p_ne: "?p \<noteq> []" and last_p: "last ?p = v"
    using sp unfolding shortest_walk_def simple_walk_betw_def walk_betw_def
    by blast+
  have suc_i: "Suc i < length ?p"
  proof (rule ccontr)
    assume "\<not> Suc i < length ?p"
    then have last_i: "i = length ?p - 1"
      using i(1) by simp
    have "?p ! i = last ?p"
      using p_ne last_i by (simp add: last_conv_nth)
    then show False
      using i(2) last_p neq by simp
  qed
  let ?pref = "take (Suc i) ?p"
  let ?suf = "drop i ?p"
  have pref_short: "shortest_walk s ?pref u"
    using shortest_walk_prefix_shortest[OF sp i(1)] i(2) by simp
  have pref_weight: "walk_weight ?pref = dist s u"
    using pref_short unfolding shortest_walk_def by blast
  have pref_betw: "walk_betw s ?pref u"
    using pref_short unfolding shortest_walk_def simple_walk_betw_def by blast
  have suf_betw0: "walk_betw (?p ! i) ?suf v"
    by (rule walk_suffix_from_index[OF simple_p i(1)])
  have suf_betw: "walk_betw u ?suf v"
    using suf_betw0 i(2) by simp
  have suf_walk: "walk ?suf"
    using suf_betw unfolding walk_betw_def by blast
  have suf_len: "1 < length ?suf"
    using suc_i by simp
  have suf_pos: "0 < walk_weight ?suf"
    by (rule walk_weight_pos_if_positive_edges[OF positive suf_walk suf_len])
  have split_p: "?pref @ tl ?suf = ?p"
    using take_Suc_append_tl_drop[OF i(1)] .
  have "walk_weight ?p = walk_weight ?pref + walk_weight ?suf"
    using walk_weight_append_tl_betw[OF pref_betw suf_betw] split_p by simp
  then show ?thesis
    using weight_p pref_weight suf_pos by linarith
qed

end

locale strict_tie_breaking_digraph = unique_shortest_digraph +
  assumes tree_path_strict_dist:
    "\<lbrakk>tree_path u v; u \<noteq> v\<rbrakk> \<Longrightarrow> dist s u < dist s v"

locale positive_unique_shortest_digraph = unique_shortest_digraph +
  assumes positive_weight: "(u, v) \<in> E \<Longrightarrow> 0 < w u v"
begin

sublocale strict_tie_breaking_digraph
proof
  show "\<And>u v. \<lbrakk>tree_path u v; u \<noteq> v\<rbrakk> \<Longrightarrow> dist s u < dist s v"
    by (rule tree_path_strict_dist_if_positive_edges[OF positive_weight])
qed

end

text \<open>
  The first locale bridge shows one concrete way to obtain strict tree growth:
  positive edge weights imply every non-empty suffix of a shortest path has
  positive weight, and therefore every proper descendant in the selected
  shortest-path tree has strictly larger distance.  The abstract
  \<open>strict_tie_breaking_digraph\<close> locale records only the consequence needed by
  the runtime proof, avoiding a commitment to any particular perturbation or
  tie-breaking construction.
\<close>

context strict_tie_breaking_digraph
begin

lemma bound_tree_singleton_tree_path:
  assumes "y \<in> bound_tree {x} B"
  shows "tree_path x y"
proof -
  have reach_y: "reachable s y" and through_y: "through {x} y"
    using assms unfolding bound_tree_def by auto
  then show ?thesis
    using through_iff_tree_path[OF reach_y, of "{x}"] by auto
qed

lemma bound_tree_singleton_root_strict_min:
  assumes x_bound: "x \<in> bound_tree {x} B"
    and y_bound: "y \<in> bound_tree {x} B"
    and neq: "y \<noteq> x"
  shows "dist s x < dist s y"
proof -
  have "tree_path x y"
    by (rule bound_tree_singleton_tree_path[OF y_bound])
  then show ?thesis
    using tree_path_strict_dist neq by blast
qed

lemma base_case_order_hd_root:
  assumes x_bound: "x \<in> bound_tree {x} B"
  shows "base_case_order x B \<noteq> [] \<and> hd (base_case_order x B) = x"
proof -
  let ?xs = "base_case_order x B"
  have set_xs: "set ?xs = bound_tree {x} B"
    by (rule base_case_order_set)
  have x_set: "x \<in> set ?xs"
    using x_bound set_xs by simp
  then have xs_ne: "?xs \<noteq> []"
    by auto
  have hd_in: "hd ?xs \<in> bound_tree {x} B"
    using xs_ne set_xs by (metis hd_in_set)
  have sorted: "sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) ?xs"
    by (rule base_case_order_sorted)
  have hd_eq: "hd ?xs = x"
  proof (rule ccontr)
    assume hd_neq: "hd ?xs \<noteq> x"
    obtain i where i: "i < length ?xs" "?xs ! i = x"
      using x_set by (auto simp: in_set_conv_nth)
    have i_pos: "0 < i"
    proof (rule ccontr)
      assume "\<not> 0 < i"
      then have "i = 0"
        by simp
      then show False
        using i xs_ne hd_neq by (simp add: hd_conv_nth)
    qed
    have hd_nth: "?xs ! 0 = hd ?xs"
      using xs_ne by (simp add: hd_conv_nth)
    have "dist s (hd ?xs) \<le> dist s x"
      using sorted_wrt_nth_less[OF sorted i_pos i(1)] i(2) hd_nth by simp
    moreover have "dist s x < dist s (hd ?xs)"
      by (rule bound_tree_singleton_root_strict_min[OF x_bound hd_in hd_neq])
    ultimately show False
      by simp
  qed
  show ?thesis
    using xs_ne hd_eq by blast
qed

lemma source_in_base_case_vertices:
  assumes x_bound: "x \<in> bound_tree {x} B"
    and k_pos: "0 < k"
  shows "x \<in> base_case_vertices k x B"
proof (cases "length (base_case_order x B) \<le> k")
  case True
  then show ?thesis
    using x_bound base_case_success[of x B k] by simp
next
  case False
  let ?xs = "base_case_order x B"
  have len: "k < length ?xs"
    using False by simp
  have hd_root: "hd ?xs = x" and xs_ne: "?xs \<noteq> []"
    using base_case_order_hd_root[OF x_bound] by blast+
  have x_take: "x \<in> set (take (Suc k) ?xs)"
  proof -
    have "?xs ! 0 = x"
      using hd_root xs_ne by (simp add: hd_conv_nth)
    moreover have "0 < length (take (Suc k) ?xs)"
      using len by simp
    ultimately show ?thesis
      using nth_mem[of 0 "take (Suc k) ?xs"] by simp
  qed
  have kth_bound: "?xs ! k \<in> bound_tree {x} B"
    using len base_case_order_set[of x B] nth_mem by metis
  have kth_neq: "?xs ! k \<noteq> x"
  proof
    assume kth_eq: "?xs ! k = x"
    have distinct: "distinct ?xs"
      by (rule base_case_order_distinct)
    have "?xs ! 0 = ?xs ! k"
      using kth_eq hd_root xs_ne by (simp add: hd_conv_nth)
    moreover have "0 < length ?xs" "k < length ?xs" "0 \<noteq> k"
      using xs_ne len k_pos by auto
    ultimately show False
      using distinct by (meson nth_eq_iff_index_eq)
  qed
  have dist_lt: "dist s x < dist s (?xs ! k)"
    by (rule bound_tree_singleton_root_strict_min[OF x_bound kth_bound kth_neq])
  have "base_case_vertices k x B =
      {v \<in> set (take (Suc k) ?xs). dist s v < dist s (?xs ! k)}"
    using len unfolding base_case_vertices_def by (simp add: Let_def)
  then show ?thesis
    using x_take dist_lt by simp
qed

text \<open>
  The base-case lemmas turn strict tree growth into the concrete progress fact
  used by the recurrence.  In a singleton problem, every vertex in
  \<open>bound_tree {x} B\<close> lies below \<open>x\<close> in the selected shortest-path tree.
  Strictness makes \<open>x\<close> the first element of \<open>base_case_order x B\<close>.  Hence
  the bounded base scan always includes its source whenever \<open>k > 0\<close>.

  This small fact is what lets the base case participate in the same source
  accounting as the recursive cases: the source set has cardinality one and is
  contained in the returned base-case vertex set.
\<close>

lemma tree_path_tight_successor:
  assumes tight: "tight_edge_step u v"
  shows "tree_path u v"
proof (cases "u = v")
  case True
  have reach_u: "reachable s u"
    using tight unfolding tight_edge_step_def by blast
  have sp_u: "shortest_walk s (shortest_path_to u) u"
    by (rule shortest_path_to_shortest[OF reach_u])
  have "u \<in> set (shortest_path_to u)"
  proof -
    have "shortest_path_to u \<noteq> []" "last (shortest_path_to u) = u"
      using shortest_walk_hd[OF sp_u] by blast+
    then show ?thesis
      by (metis last_in_set)
  qed
  then show ?thesis
    using True reach_u unfolding tree_path_def by blast
next
  case False
  have edge: "(u, v) \<in> E"
    using tight unfolding tight_edge_step_def by blast
  have reach_u: "reachable s u"
    using tight unfolding tight_edge_step_def by blast
  have dist_v: "dist s v = dist s u + w u v"
    using tight unfolding tight_edge_step_def by blast
  let ?p = "shortest_path_to u"
  have sp_u: "shortest_walk s ?p u"
    by (rule shortest_path_to_shortest[OF reach_u])
  have simple_p: "simple_walk_betw s ?p u"
    using sp_u unfolding shortest_walk_def by blast
  have weight_p: "walk_weight ?p = dist s u"
    using sp_u unfolding shortest_walk_def by blast
  have p_ne: "?p \<noteq> []" and last_p: "last ?p = u"
    using shortest_walk_hd[OF sp_u] by blast+
  have v_notin: "v \<notin> set ?p"
  proof
    assume v_in: "v \<in> set ?p"
    have tree_vu: "tree_path v u"
      by (rule tree_pathI[OF reach_u v_in])
    have vu_neq: "v \<noteq> u"
      using False by simp
    have "dist s v < dist s u"
      by (rule tree_path_strict_dist[OF tree_vu vu_neq])
    moreover have "dist s u \<le> dist s v"
      using dist_v nonneg_weight[OF edge] by linarith
    ultimately show False
      by simp
  qed
  have simple_q: "simple_walk_betw s (?p @ [v]) v"
    by (rule simple_walk_snoc[OF simple_p edge v_notin])
  have weight_q: "walk_weight (?p @ [v]) = dist s v"
    using weight_p p_ne last_p dist_v
    by (simp add: walk_weight_snoc)
  have sp_q: "shortest_walk s (?p @ [v]) v"
    using simple_q weight_q unfolding shortest_walk_def by blast
  have reach_v: "reachable s v"
    by (rule dist_triangle_edge(1)[OF edge reach_u])
  have sp_v: "shortest_walk s (shortest_path_to v) v"
    by (rule shortest_path_to_shortest[OF reach_v])
  have path_eq: "shortest_path_to v = ?p @ [v]"
    using unique_shortest_walk[OF sp_v sp_q] .
  have "u \<in> set ?p"
    using p_ne last_p by (metis last_in_set)
  then have "u \<in> set (?p @ [v])"
    by simp
  then have "u \<in> set (shortest_path_to v)"
    using path_eq by simp
  then show ?thesis
    by (rule tree_pathI[OF reach_v])
qed

lemma fp_next_bound_tree:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and F_bound: "F \<subseteq> bound_tree S B"
    and v_next: "v \<in> fp_next d F B"
  shows "v \<in> bound_tree S B"
proof -
  obtain u where uF: "u \<in> F"
    and edge: "(u, v) \<in> E"
    and relax: "d u + w u v \<le> d v"
    and below_cand: "below_bound (d u + w u v) B"
    using v_next unfolding fp_next_def by blast
  have u_bound: "u \<in> bound_tree S B"
    using F_bound uF by blast
  have reach_u: "reachable s u"
    using u_bound unfolding bound_tree_def by blast
  have reach_v: "reachable s v"
    by (rule dist_triangle_edge(1)[OF edge reach_u])
  have dist_triangle: "dist s v \<le> dist s u + w u v"
    by (rule dist_triangle_edge(2)[OF edge reach_u])
  have vV: "v \<in> V"
    using edge_in_V[OF edge] by simp
  have uV: "u \<in> V"
    using u_bound unfolding bound_tree_def by blast
  have dist_u_le: "dist s u \<le> d u"
    using sound uV reach_u unfolding sound_label_def by blast
  have dist_v_le_cand: "dist s v \<le> d u + w u v"
    using dist_triangle dist_u_le by linarith
  have below_v: "below_bound (dist s v) B"
    by (rule below_bound_le_trans[OF dist_v_le_cand below_cand])
  have through_v: "through S v"
  proof (cases "d v = dist s v")
    case True
    have cand_le_dist: "d u + w u v \<le> dist s v"
      using relax True by simp
    have dist_v_eq: "dist s v = dist s u + w u v"
      using dist_triangle dist_u_le cand_le_dist by linarith
    have tight_uv: "tight_edge_step u v"
      using edge reach_u dist_v_eq unfolding tight_edge_step_def by blast
    have tree_uv: "tree_path u v"
      by (rule tree_path_tight_successor[OF tight_uv])
    have through_u: "through S u"
      using u_bound unfolding bound_tree_def by blast
    obtain x where xS: "x \<in> S" and tree_xu: "tree_path x u"
      using through_iff_tree_path[OF reach_u, of S] through_u by blast
    have tree_xv: "tree_path x v"
      by (rule tree_path_trans[OF tree_uv tree_xu])
    show ?thesis
      using through_iff_tree_path[OF reach_v, of S] xS tree_xv by blast
  next
    case False
    have "through_complete d S v"
      using pre vV reach_v below_v False unfolding bmssp_pre_full_def by blast
    then show ?thesis
      unfolding through_complete_def through_def by blast
  qed
  show ?thesis
    using vV reach_v through_v below_v unfolding bound_tree_def by blast
qed

lemma fp_iter_capped_seen_subset_bound_tree:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and F_bound: "F \<subseteq> bound_tree S B"
    and W_bound: "W \<subseteq> bound_tree S B"
  shows "fp_seen (fp_iter_capped n cap d F W B) \<subseteq> bound_tree S B"
  using assms
proof (induction n arbitrary: d F W)
  case 0
  then show ?case
    unfolding fp_seen_def by simp
next
  case (Suc n)
  let ?d' = "relax_frontier d F"
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  have F_reaches: "\<And>u. u \<in> F \<Longrightarrow> reachable s u"
    using Suc.prems(3) unfolding bound_tree_def by blast
  have sound': "sound_label ?d'"
    by (rule relax_frontier_sound[OF Suc.prems(1) F_reaches])
  have pre': "bmssp_pre_full ?d' S B"
    by (rule relax_frontier_preserves_bmssp_pre_full
      [OF Suc.prems(1,2) F_reaches])
  have F'_bound: "?F' \<subseteq> bound_tree S B"
  proof
    fix v
    assume "v \<in> ?F'"
    then show "v \<in> bound_tree S B"
      by (rule fp_next_bound_tree[OF Suc.prems(1,2,3)])
  qed
  have W'_bound: "?W' \<subseteq> bound_tree S B"
    using Suc.prems(4) F'_bound by blast
  show ?case
  proof (cases "card ?W' > cap")
    case True
    then show ?thesis
      using W'_bound by (simp add: fp_seen_def Let_def)
  next
    case False
    show ?thesis
      using Suc.IH[OF sound' pre' F'_bound W'_bound] False
      by (simp add: fp_seen_def Let_def)
  qed
qed

lemma find_pivots_seen_capped_subset_bound_tree:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
  shows "find_pivots_seen_capped k cap d S B \<subseteq> bound_tree S B"
proof -
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have below_dist: "\<And>x. x \<in> S \<Longrightarrow> below_bound (dist s x) B"
  proof -
    fix x
    assume xS: "x \<in> S"
    have "dist s x \<le> d x"
      using sound S_subset xS S_reaches[OF xS]
      unfolding sound_label_def by blast
    then show "below_bound (dist s x) B"
      by (rule below_bound_le_trans[OF _ below[OF xS]])
  qed
  have S_bound: "S \<subseteq> bound_tree S B"
    by (rule sources_subset_bound_tree[OF S_reaches below_dist])
  show ?thesis
    unfolding find_pivots_seen_capped_def
    by (rule fp_iter_capped_seen_subset_bound_tree
      [OF sound pre S_bound S_bound])
qed

text \<open>
  The next block connects FindPivots' "seen" set to completed output ranges.
  When a non-base call succeeds with the original bound, the final assembly
  theorem says that the loop output together with already-complete labelled
  vertices is exactly the parent bound tree.  Since the seen set is contained in
  that tree, successful calls can charge the number of seen vertices to the
  returned output.

  The same argument is stated for both exact split-range runs and direct-insert
  runs.  The direct-insert version first forgets its extra accounting structure
  down to the exact range trace, then applies the same assembly reasoning.
  These lemmas are later paired with threshold lemmas for the unsuccessful
  branch.
\<close>

theorem exact_split_range_costed_step_seen_success:
  assumes loop:
      "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
        Us U_loop c_loop child_costs"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v =
          dist s v}"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and success: "B' = B"
  shows "card (find_pivots_seen_capped k cap d S B) \<le> card U"
proof -
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  have sound_fp: "sound_label ?d_fp"
    unfolding find_pivots_label_capped_def
    by (rule fp_iter_capped_label_sound[OF sound S_reaches])
  have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
    using find_pivots_capped_establishes_pivot_pre_concrete
      [OF sound pre S_reaches] .
  have P_subset_S: "?P \<subseteq> S"
    unfolding find_pivots_pivots_capped_def by (auto split: if_splits)
  have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
    using P_subset_S S_reaches by blast
  have split_loop:
    "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
      ?d_fp ?P B d' D a betas bs B' Us U_loop c_loop child_costs"
    by (rule exact_split_range_costed_refines_split_range_costed(1)[OF loop])
  have trace:
    "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
    by (rule split_range_costed_partition_loop_state_trace
      [OF split_loop sound_fp pivot_pre P_reaches])
  have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
    by (rule concrete_partition_loop_trace_post[OF trace])
  have assembly:
    "U_loop \<union>
      {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v =
        dist s v} =
      bound_tree S B'"
    by (rule concrete_capped_find_pivots_final_tree_assembly
      [OF sound pre S_reaches loop_post])
  have U_tree: "U = bound_tree S B"
    using U_def assembly success by simp
  have seen_subset:
    "find_pivots_seen_capped k cap d S B \<subseteq> U"
    using find_pivots_seen_capped_subset_bound_tree
      [OF sound pre S_reaches below] U_tree by simp
  have finite_U: "finite U"
    unfolding U_tree bound_tree_def using finite_V by auto
  show ?thesis
    by (rule card_mono[OF finite_U seen_subset])
qed

theorem direct_insert_costed_step_seen_success:
  assumes loop:
      "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
        Us U_loop c_loop child_costs"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v =
          dist s v}"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and success: "B' = B"
  shows "card (find_pivots_seen_capped k cap d S B) \<le> card U"
proof -
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  have sound_fp: "sound_label ?d_fp"
    unfolding find_pivots_label_capped_def
    by (rule fp_iter_capped_label_sound[OF sound S_reaches])
  have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
    using find_pivots_capped_establishes_pivot_pre_concrete
      [OF sound pre S_reaches] .
  have P_subset_S: "?P \<subseteq> S"
    unfolding find_pivots_pivots_capped_def by (auto split: if_splits)
  have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
    using P_subset_S S_reaches by blast
  have trace:
    "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
    by (rule direct_insert_costed_partition_loop_state_trace
      [OF loop sound_fp pivot_pre P_reaches])
  have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
    by (rule concrete_partition_loop_trace_post[OF trace])
  have assembly:
    "U_loop \<union>
      {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v =
        dist s v} =
      bound_tree S B'"
    by (rule concrete_capped_find_pivots_final_tree_assembly
      [OF sound pre S_reaches loop_post])
  have U_tree: "U = bound_tree S B"
    using U_def assembly success by simp
  have seen_subset:
    "find_pivots_seen_capped k cap d S B \<subseteq> U"
    using find_pivots_seen_capped_subset_bound_tree
      [OF sound pre S_reaches below] U_tree by simp
  have finite_U: "finite U"
    unfolding U_tree bound_tree_def using finite_V by auto
  show ?thesis
    by (rule card_mono[OF finite_U seen_subset])
qed

theorem direct_insert_costed_step_seen_success_subset:
  assumes loop:
      "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
        Us U_loop c_loop child_costs"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v =
          dist s v}"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and success: "B' = B"
  shows "find_pivots_seen_capped k cap d S B \<subseteq> U"
proof -
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  have sound_fp: "sound_label ?d_fp"
    unfolding find_pivots_label_capped_def
    by (rule fp_iter_capped_label_sound[OF sound S_reaches])
  have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
    using find_pivots_capped_establishes_pivot_pre_concrete
      [OF sound pre S_reaches] .
  have P_subset_S: "?P \<subseteq> S"
    unfolding find_pivots_pivots_capped_def by (auto split: if_splits)
  have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
    using P_subset_S S_reaches by blast
  have trace:
    "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
    by (rule direct_insert_costed_partition_loop_state_trace
      [OF loop sound_fp pivot_pre P_reaches])
  have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
    by (rule concrete_partition_loop_trace_post[OF trace])
  have assembly:
    "U_loop \<union>
      {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v =
        dist s v} =
      bound_tree S B'"
    by (rule concrete_capped_find_pivots_final_tree_assembly
      [OF sound pre S_reaches loop_post])
  have U_tree: "U = bound_tree S B"
    using U_def assembly success by simp
  show ?thesis
    using find_pivots_seen_capped_subset_bound_tree
      [OF sound pre S_reaches below] U_tree by simp
qed

theorem direct_insert_costed_capped_step_threshold_if_not_success:
  assumes loop:
      "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
        Us U_loop c_loop child_costs"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v =
          dist s v}"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and not_success: "B' \<noteq> B"
  shows "k * cap \<le> card U"
proof -
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  have sound_fp: "sound_label ?d_fp"
    unfolding find_pivots_label_capped_def
    by (rule fp_iter_capped_label_sound[OF sound S_reaches])
  have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
    using find_pivots_capped_establishes_pivot_pre_concrete
      [OF sound pre S_reaches] .
  have P_subset_S: "?P \<subseteq> S"
    unfolding find_pivots_pivots_capped_def by auto
  have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
    using P_subset_S S_reaches by blast
  have loop_class:
    "B' = B \<or> k * cap \<le> card U_loop"
    by (rule direct_insert_costed_partition_loop_state_success_or_threshold
      [OF loop sound_fp pivot_pre P_reaches])
  have threshold_loop: "k * cap \<le> card U_loop"
    using loop_class not_success by blast
  have trace: "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
    by (rule direct_insert_costed_partition_loop_state_trace
      [OF loop sound_fp pivot_pre P_reaches])
  have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
    by (rule concrete_partition_loop_trace_post[OF trace])
  have finite_U_loop: "finite U_loop"
    using loop_post unfolding bmssp_post_full_def by simp
  have finite_U: "finite U"
    unfolding U_def using finite_U_loop by simp
  have U_loop_subset: "U_loop \<subseteq> U"
    unfolding U_def by blast
  have "card U_loop \<le> card U"
    by (rule card_mono[OF finite_U U_loop_subset])
  then show ?thesis
    using threshold_loop by linarith
qed

theorem direct_insert_costed_capped_step_scan_insert_budget_from_scaled_seen_or_threshold:
  assumes degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and insert:
      "partition_initial_insert_cost_bound c_insert t
        (find_pivots_pivots_capped k cap d S B)"
    and loop:
      "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
        Us U_loop c_loop child_costs"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v =
          dist s v}"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and S_k_cap: "k * card S \<le> cap"
    and anti: "tree_antichain S"
    and k_pos: "0 < k"
    and seen_success:
      "B' = B \<Longrightarrow>
       card (find_pivots_seen_capped k cap d S B) \<le> card U"
  shows "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
    2 * A * card U"
proof (cases "B' = B")
  case True
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  show ?thesis
    by (rule find_pivots_scan_and_initial_insert_budget_from_seen_scaled
      [OF S_subset degree anti S_k_cap insert insert_scaled_factor
        seen_scaled_factor seen_success[OF True]])
next
  case False
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have S_cap: "card S \<le> cap"
  proof -
    have "card S \<le> k * card S"
      using k_pos by (cases k) simp_all
    then show ?thesis
      using S_k_cap by linarith
  qed
  have progress: "k * cap \<le> card U"
    by (rule direct_insert_costed_capped_step_threshold_if_not_success
      [OF loop U_def sound pre S_reaches False])
  show ?thesis
    by (rule find_pivots_scan_and_initial_insert_budget_from_progress
      [OF S_subset degree S_cap insert degree_factor insert_factor progress])
qed

theorem split_range_costed_bmssp_zero_source_card_le_from_label_below:
  assumes run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and k_pos: "0 < k"
  shows "card S \<le> card U"
  using run
proof cases
  case (Split_Range_Cost_Base x)
  have S_eq: "S = {x}"
    using Split_Range_Cost_Base by simp
  have xS: "x \<in> S"
    using S_eq by simp
  have xV: "x \<in> V"
    using pre xS unfolding bmssp_pre_full_def by blast
  have reach_x: "reachable s x"
    by (rule S_reaches[OF xS])
  have dist_le: "dist s x \<le> d x"
    using sound xV reach_x unfolding sound_label_def by blast
  have below_dist: "below_bound (dist s x) B"
    using below_bound_le_trans[OF dist_le below[OF xS]] .
  have x_bound: "x \<in> bound_tree {x} B"
    by (rule source_in_own_bound_tree[OF _ reach_x below_dist]) simp
  have xU: "x \<in> U"
    using source_in_base_case_vertices[OF x_bound k_pos]
    using Split_Range_Cost_Base by simp
  have singleton_subset: "{x} \<subseteq> U"
    using xU by blast
  have finite_U: "finite U"
    using Split_Range_Cost_Base by simp
  have "card {x} \<le> card U"
    by (rule card_mono[OF finite_U singleton_subset])
  then show ?thesis
    using S_eq by simp
qed

theorem split_range_costed_bmssp_source_card_le_from_label_below_all_levels:
  assumes run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and S_cap: "card S \<le> cap"
    and k_pos: "0 < k"
  shows "card S \<le> card U"
proof (cases l)
  case 0
  have run0:
    "split_range_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
    using run 0 by simp
  show ?thesis
    by (rule split_range_costed_bmssp_zero_source_card_le_from_label_below
      [OF run0 sound pre S_reaches below k_pos])
next
  case (Suc l')
  have run_suc:
    "split_range_costed_bmssp \<Delta> M_of t h k cap (Suc l') d S B d' B' U c"
    using run Suc by simp
  show ?thesis
    by (rule split_range_costed_bmssp_Suc_source_card_le_from_label_below
      [OF run_suc sound pre S_reaches below S_cap k_pos])
qed

theorem exact_split_range_costed_bmssp_source_card_le_from_label_below_all_levels:
  assumes run:
      "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and S_cap: "card S \<le> cap"
    and k_pos: "0 < k"
  shows "card S \<le> card U"
  by (rule split_range_costed_bmssp_source_card_le_from_label_below_all_levels
    [OF exact_split_range_costed_refines_split_range_costed(2)[OF run]
      sound pre S_reaches below S_cap k_pos])

theorem direct_insert_costed_bmssp_zero_source_card_le_from_label_below:
  assumes run:
      "direct_insert_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and k_pos: "0 < k"
  shows "card S \<le> card U"
  using run
proof cases
  case (Direct_Insert_Costed_Base x)
  have S_eq: "S = {x}"
    using Direct_Insert_Costed_Base by simp
  have xS: "x \<in> S"
    using S_eq by simp
  have xV: "x \<in> V"
    using pre xS unfolding bmssp_pre_full_def by blast
  have reach_x: "reachable s x"
    by (rule S_reaches[OF xS])
  have dist_le: "dist s x \<le> d x"
    using sound xV reach_x unfolding sound_label_def by blast
  have below_dist: "below_bound (dist s x) B"
    using below_bound_le_trans[OF dist_le below[OF xS]] .
  have x_bound: "x \<in> bound_tree {x} B"
    by (rule source_in_own_bound_tree[OF _ reach_x below_dist]) simp
  have xU: "x \<in> U"
    using source_in_base_case_vertices[OF x_bound k_pos]
    using Direct_Insert_Costed_Base by simp
  have singleton_subset: "{x} \<subseteq> U"
    using xU by blast
  have finite_U: "finite U"
    using Direct_Insert_Costed_Base by simp
  have "card {x} \<le> card U"
    by (rule card_mono[OF finite_U singleton_subset])
  then show ?thesis
    using S_eq by simp
qed

theorem direct_insert_costed_bmssp_source_card_le_from_label_below_all_levels:
  assumes run:
      "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and S_cap: "card S \<le> cap"
    and k_pos: "0 < k"
  shows "card S \<le> card U"
proof (cases l)
  case 0
  have run0:
    "direct_insert_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
    using run 0 by simp
  show ?thesis
    by (rule direct_insert_costed_bmssp_zero_source_card_le_from_label_below
      [OF run0 sound pre S_reaches below k_pos])
next
  case (Suc l')
  have run_suc:
    "direct_insert_costed_bmssp \<Delta> M_of t h k cap (Suc l') d S B d' B' U c"
    using run Suc by simp
  show ?thesis
    by (rule direct_insert_costed_bmssp_Suc_source_card_le_from_label_below
      [OF run_suc sound pre S_reaches below S_cap k_pos])
qed

text \<open>
  From here the theory closes the recurrence under the strict progress
  assumptions.  The source-progress hypothesis in the direct-insert cost layer
  is discharged by a case split on the recursion level.  At level zero, the
  strict base-case order gives the source in the returned base set.  At positive
  levels, the success-or-threshold lemmas and the seen-set bound show that a
  child call's sources are dominated by its output.

  The resulting loop-closing theorems are wrappers around the direct-insert
  cost lemmas from the previous file.  Their purpose is to remove the abstract
  source-progress assumption and replace it by explicit invariants:
  bounded child source size, tree antichains, and the scaled cardinality
  condition that the BMSSP schedule maintains.
\<close>

theorem direct_insert_costed_partition_loop_state_closes_level_bound_from_child_bound_with_invariants_and_edge_ranges:
  assumes run:
    "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and P_k_cap: "k * card P \<le> cap"
    and P_anti: "tree_antichain P"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child;
          k * card S_child \<le> cap;
          tree_antichain S_child\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and M_cap: "M_of l \<le> cap"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
  shows "c \<le>
    A * Suc L * card U + R * card (outgoing_edges U) +
    t * sum_list
      (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
    h * sum_list
      (map card (range_tree_child_edge_range_list P a betas bs))"
proof -
  have P_subset: "P \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have child_cost_bounds:
    "list_all2 (\<lambda>c_child U_child.
      c_child \<le> level_range_cost_bound A R L U_child)
      child_costs (range_tree_child_list P a bs)"
    by (rule direct_insert_costed_partition_loop_state_child_cost_bounds_with_invariants
      [OF run P_subset P_k_cap P_anti child_bound])
  have source_progress:
    "\<And>S_child B_child d_child B_child' U_child c_child.
      \<lbrakk>direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child;
        bmssp_pre_full d S_child B_child;
        \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
        card S_child \<le> M_of l;
        \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child\<rbrakk>
      \<Longrightarrow> card S_child \<le> card U_child"
  proof -
    fix S_child B_child d_child B_child' U_child c_child
    assume child:
        "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child"
      and child_pre: "bmssp_pre_full d S_child B_child"
      and child_reaches: "\<And>x. x \<in> S_child \<Longrightarrow> reachable s x"
      and child_card: "card S_child \<le> M_of l"
      and child_below: "\<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child"
    have child_cap: "card S_child \<le> cap"
      using child_card M_cap by linarith
    show "card S_child \<le> card U_child"
      by (rule direct_insert_costed_bmssp_source_card_le_from_label_below_all_levels
        [OF child sound child_pre child_reaches child_below child_cap k_pos])
  qed
  show ?thesis
    by (rule direct_insert_costed_partition_loop_state_closes_level_bound_from_child_costs_and_edge_ranges
      [OF run sound pre P_reaches child_cost_bounds source_factor
        source_progress])
qed

theorem direct_insert_costed_partition_loop_state_closes_amortized_bound_from_child_bound_with_invariants:
  assumes run:
    "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and P_k_cap: "k * card P \<le> cap"
    and P_anti: "tree_antichain P"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child;
          k * card S_child \<le> cap;
          tree_antichain S_child\<rbrakk>
        \<Longrightarrow> c_child \<le>
          bmssp_amortized_cost_bound A R h t q L B_child U_child"
    and M_cap: "M_of l \<le> cap"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
  shows "c \<le> bmssp_amortized_cost_bound A R h t (Suc q) (Suc L) B U"
proof -
  have P_subset: "P \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have child_cost_bounds:
    "list_all2 (\<lambda>c_child UB. case UB of (U_child, B_child) \<Rightarrow>
      c_child \<le> bmssp_amortized_cost_bound A R h t q L B_child U_child)
      child_costs (range_tree_child_bound_pair_list P a betas bs)"
    by (rule direct_insert_costed_partition_loop_state_child_amortized_cost_bounds_with_invariants
      [OF run P_subset P_k_cap P_anti child_bound])
  have source_progress:
    "\<And>S_child B_child d_child B_child' U_child c_child.
      \<lbrakk>direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child;
        bmssp_pre_full d S_child B_child;
        \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
        card S_child \<le> M_of l;
        \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child\<rbrakk>
      \<Longrightarrow> card S_child \<le> card U_child"
  proof -
    fix S_child B_child d_child B_child' U_child c_child
    assume child:
        "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child"
      and child_pre: "bmssp_pre_full d S_child B_child"
      and child_reaches: "\<And>x. x \<in> S_child \<Longrightarrow> reachable s x"
      and child_card: "card S_child \<le> M_of l"
      and child_below: "\<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child"
    have child_cap: "card S_child \<le> cap"
      using child_card M_cap by linarith
    show "card S_child \<le> card U_child"
      by (rule direct_insert_costed_bmssp_source_card_le_from_label_below_all_levels
        [OF child sound child_pre child_reaches child_below child_cap k_pos])
  qed
  show ?thesis
    by (rule direct_insert_costed_partition_loop_state_closes_amortized_bound_from_child_costs
      [OF run sound pre P_reaches child_cost_bounds source_factor
        source_progress])
qed

theorem direct_insert_costed_nonbase_step_closes_amortized_bound_from_child_bound_with_invariants:
  assumes loop:
    "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U_loop c_loop child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and P_k_cap: "k * card P \<le> cap"
    and P_anti: "tree_antichain P"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child;
          k * card S_child \<le> cap;
          tree_antichain S_child\<rbrakk>
        \<Longrightarrow> c_child \<le>
          bmssp_amortized_cost_bound A R h t q L B_child U_child"
    and M_cap: "M_of l \<le> cap"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
    and U_def: "U = U_loop \<union> W"
    and finite_U: "finite U"
    and scan_insert: "c_scan_insert \<le> A * card U"
    and c_def: "c = c_scan_insert + c_loop"
  shows "c \<le>
    bmssp_amortized_cost_bound A R h t (Suc q) (Suc (Suc L)) B U"
proof -
  have loop_bound:
    "c_loop \<le>
      bmssp_amortized_cost_bound A R h t (Suc q) (Suc L) B U_loop"
    by (rule direct_insert_costed_partition_loop_state_closes_amortized_bound_from_child_bound_with_invariants
      [OF loop sound pre P_reaches P_k_cap P_anti child_bound M_cap
        source_factor k_pos])
  have U_loop_subset: "U_loop \<subseteq> U"
    using U_def by blast
  have card_loop_le: "card U_loop \<le> card U"
    by (rule card_mono[OF finite_U U_loop_subset])
  have outgoing_subset: "outgoing_edges U_loop \<subseteq> outgoing_edges U"
    by (rule outgoing_edges_mono[OF U_loop_subset])
  have finite_out_U: "finite (outgoing_edges U)"
    by simp
  have card_out_le: "card (outgoing_edges U_loop) \<le> card (outgoing_edges U)"
    by (rule card_mono[OF finite_out_U outgoing_subset])
  have range_subset:
    "outgoing_edges_range U_loop 0 B \<subseteq> outgoing_edges_range U 0 B"
    by (rule outgoing_edges_range_mono_sources[OF U_loop_subset])
  have card_range_le:
    "card (outgoing_edges_range U_loop 0 B) \<le>
      card (outgoing_edges_range U 0 B)"
    by (rule card_mono[OF finite_outgoing_edges_range range_subset])
  have loop_to_U:
    "c_loop \<le>
      A * Suc L * card U +
      (R + Suc q * h) * card (outgoing_edges U) +
      t * card (outgoing_edges_range U 0 B)"
  proof -
    have vterm:
      "A * Suc L * card U_loop \<le> A * Suc L * card U"
      using card_loop_le by simp
    have eterm:
      "(R + Suc q * h) * card (outgoing_edges U_loop) \<le>
       (R + Suc q * h) * card (outgoing_edges U)"
      using card_out_le by simp
    have rterm:
      "t * card (outgoing_edges_range U_loop 0 B) \<le>
       t * card (outgoing_edges_range U 0 B)"
      using card_range_le by simp
    show ?thesis
      using loop_bound vterm eterm rterm
      unfolding bmssp_amortized_cost_bound_def by linarith
  qed
  have "c \<le>
      A * card U +
      (A * Suc L * card U +
       (R + Suc q * h) * card (outgoing_edges U) +
       t * card (outgoing_edges_range U 0 B))"
    using scan_insert loop_to_U c_def by linarith
  also have "\<dots> =
      A * Suc (Suc L) * card U +
      (R + Suc q * h) * card (outgoing_edges U) +
      t * card (outgoing_edges_range U 0 B)"
    by (simp add: algebra_simps)
  finally show ?thesis
    unfolding bmssp_amortized_cost_bound_def .
qed

theorem direct_insert_costed_bmssp_amortized_bound_from_local_budgets_with_invariants:
  assumes base_budget: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
    and M_cap: "\<And>i. i \<le> l \<Longrightarrow> M_of i \<le> cap"
    and step_budget:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
          Us U_loop c_loop child_costs \<Longrightarrow>
        complete_on d'
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        U = U_loop \<union>
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B) \<Longrightarrow>
        k * card S \<le> cap \<Longrightarrow>
        tree_antichain S \<Longrightarrow>
        fp_iter_capped_scan_cost k cap d S S B + c_insert \<le> A * card U"
    and run:
      "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and S_k_cap: "k * card S \<le> cap"
    and S_anti: "tree_antichain S"
  shows "c \<le> bmssp_amortized_cost_bound A R h t l (2 * l + 1) B U"
  using run sound pre S_reaches below S_k_cap S_anti M_cap
proof (induction l arbitrary: d S B d' B' U c rule: less_induct)
  case (less l)
  show ?case
  proof (cases l)
    case 0
    have run0:
      "direct_insert_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
      using less.prems(1) 0 by simp
    show ?thesis
      using run0
    proof cases
      case (Direct_Insert_Costed_Base x)
      have scan:
        "base_case_scan_cost \<Delta> k x B \<le>
          R * card (outgoing_edges (base_case_vertices k x B))"
        using R_pos unfolding base_case_scan_cost_def by simp
      show ?thesis
        using Direct_Insert_Costed_Base 0 scan
        by (simp add: bmssp_amortized_cost_bound_def; linarith)
    qed
  next
    case (Suc l0)
    have run_suc:
      "direct_insert_costed_bmssp \<Delta> M_of t h k cap (Suc l0) d S B d' B' U c"
      using less.prems(1) Suc by simp
    show ?thesis
    proof (cases rule: direct_insert_costed_bmssp_SucE[OF run_suc])
      case (1 c_insert a betas bs Us U_loop c_loop child_costs_loop)
      let ?d_fp = "find_pivots_label_capped k cap d S B"
      let ?P = "find_pivots_pivots_capped k cap d S B"
      let ?W = "{v \<in> bound_tree S B'. ?d_fp v = dist s v}"
      have sound_fp: "sound_label ?d_fp"
        unfolding find_pivots_label_capped_def
        by (rule fp_iter_capped_label_sound[OF less.prems(2) less.prems(4)])
      have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
        using find_pivots_capped_establishes_pivot_pre_concrete
          [OF less.prems(2) less.prems(3) less.prems(4)] .
      have S_subset: "S \<subseteq> V"
        using less.prems(3) unfolding bmssp_pre_full_def by blast
      have P_subset_S: "?P \<subseteq> S"
        unfolding find_pivots_pivots_capped_def by (auto split: if_splits)
      have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
        using P_subset_S less.prems(4) by blast
      have P_k_cap: "k * card ?P \<le> cap"
        by (rule find_pivots_pivots_capped_scaled_card_le
          [OF S_subset less.prems(6)])
      have P_anti: "tree_antichain ?P"
        by (rule find_pivots_pivots_capped_tree_antichain[OF less.prems(7)])
      have child_bound:
        "\<And>c_child U_child S_child B_child d_child B_child'.
          \<lbrakk>direct_insert_costed_bmssp \<Delta> M_of t h k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child;
            bmssp_pre_full ?d_fp S_child B_child;
            \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
            card S_child \<le> M_of l0;
            \<And>x. x \<in> S_child \<Longrightarrow> below_bound (?d_fp x) B_child;
            k * card S_child \<le> cap;
            tree_antichain S_child\<rbrakk>
          \<Longrightarrow> c_child \<le>
            bmssp_amortized_cost_bound A R h t l0 (2 * l0 + 1)
              B_child U_child"
      proof -
        fix c_child U_child S_child B_child d_child B_child'
        assume child:
            "direct_insert_costed_bmssp \<Delta> M_of t h k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child"
          and child_pre: "bmssp_pre_full ?d_fp S_child B_child"
          and child_reaches: "\<And>x. x \<in> S_child \<Longrightarrow> reachable s x"
          and child_below:
            "\<And>x. x \<in> S_child \<Longrightarrow> below_bound (?d_fp x) B_child"
          and child_k_cap: "k * card S_child \<le> cap"
          and child_anti: "tree_antichain S_child"
        have M_cap_child: "\<And>i. i \<le> l0 \<Longrightarrow> M_of i \<le> cap"
          using less.prems(8) Suc by simp
        show "c_child \<le>
            bmssp_amortized_cost_bound A R h t l0 (2 * l0 + 1)
              B_child U_child"
          by (rule less.IH[of l0 ?d_fp S_child B_child d_child B_child'
                U_child c_child, OF _ child sound_fp child_pre child_reaches
                child_below child_k_cap child_anti M_cap_child])
            (simp add: Suc)
      qed
      have scan_insert:
        "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
          A * card U"
        by (rule step_budget[OF refl 1(3) 1(4) 1(5) 1(1)
            less.prems(2) less.prems(3) less.prems(4) less.prems(5)
            less.prems(6) less.prems(7)])
      have trace:
        "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
        by (rule direct_insert_costed_partition_loop_state_trace
          [OF 1(4) sound_fp pivot_pre P_reaches])
      have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
        by (rule concrete_partition_loop_trace_post[OF trace])
      have finite_U_loop: "finite U_loop"
        using loop_post unfolding bmssp_post_full_def by simp
      have finite_W: "finite ?W"
        by simp
      have finite_U: "finite U"
        using 1(1) finite_U_loop finite_W by simp
      have M_cap_l0: "M_of l0 \<le> cap"
        using less.prems(8) Suc by simp
      have step:
        "c \<le>
          bmssp_amortized_cost_bound A R h t (Suc l0)
            (Suc (Suc (2 * l0 + 1))) B U"
        by (rule direct_insert_costed_nonbase_step_closes_amortized_bound_from_child_bound_with_invariants
          [OF 1(4) sound_fp pivot_pre P_reaches P_k_cap P_anti child_bound
            M_cap_l0 source_factor k_pos 1(1) finite_U scan_insert 1(2)])
      show ?thesis
        using step Suc by simp
    qed
  qed
qed

theorem direct_insert_costed_partition_loop_state_closes_level_bound_from_child_bound_with_invariants_and_edge_budget:
  assumes run:
    "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and P_k_cap: "k * card P \<le> cap"
    and P_anti: "tree_antichain P"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child;
          k * card S_child \<le> cap;
          tree_antichain S_child\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and M_cap: "M_of l \<le> cap"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
    and edge_budget:
      "t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
       h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs))
       \<le> H * card (outgoing_edges U)"
  shows "c \<le> A * Suc L * card U + (R + H) * card (outgoing_edges U)"
proof -
  have loop:
    "c \<le>
      A * Suc L * card U + R * card (outgoing_edges U) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs))"
    by (rule direct_insert_costed_partition_loop_state_closes_level_bound_from_child_bound_with_invariants_and_edge_ranges
      [OF run sound pre P_reaches P_k_cap P_anti child_bound M_cap
        source_factor k_pos])
  have "c \<le> A * Suc L * card U + R * card (outgoing_edges U) +
      H * card (outgoing_edges U)"
    using loop edge_budget by linarith
  also have "\<dots> = A * Suc L * card U + (R + H) * card (outgoing_edges U)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem direct_insert_costed_nonbase_step_closes_level_bound_from_child_bound_with_invariants_and_edge_budget:
  assumes loop:
    "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U_loop c_loop child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and P_k_cap: "k * card P \<le> cap"
    and P_anti: "tree_antichain P"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child;
          k * card S_child \<le> cap;
          tree_antichain S_child\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and M_cap: "M_of l \<le> cap"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
    and edge_budget:
      "t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
       h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs))
       \<le> H * card (outgoing_edges U_loop)"
    and U_def: "U = U_loop \<union> W"
    and finite_U: "finite U"
    and scan_insert: "c_scan_insert \<le> A * card U"
    and c_def: "c = c_scan_insert + c_loop"
  shows "c \<le> A * Suc (Suc L) * card U +
    (R + H) * card (outgoing_edges U)"
proof -
  have loop_bound:
    "c_loop \<le> A * Suc L * card U_loop +
      (R + H) * card (outgoing_edges U_loop)"
    by (rule direct_insert_costed_partition_loop_state_closes_level_bound_from_child_bound_with_invariants_and_edge_budget
      [OF loop sound pre P_reaches P_k_cap P_anti child_bound M_cap
        source_factor k_pos edge_budget])
  have U_loop_subset: "U_loop \<subseteq> U"
    using U_def by blast
  have card_loop_le: "card U_loop \<le> card U"
    by (rule card_mono[OF finite_U U_loop_subset])
  have outgoing_subset: "outgoing_edges U_loop \<subseteq> outgoing_edges U"
    by (rule outgoing_edges_mono[OF U_loop_subset])
  have finite_out_U: "finite (outgoing_edges U)"
    by simp
  have card_out_le:
    "card (outgoing_edges U_loop) \<le> card (outgoing_edges U)"
    by (rule card_mono[OF finite_out_U outgoing_subset])
  have "c \<le>
      A * card U +
      (A * Suc L * card U + (R + H) * card (outgoing_edges U))"
  proof -
    have loop_to_U:
      "c_loop \<le> A * Suc L * card U +
        (R + H) * card (outgoing_edges U)"
    proof -
      have "A * Suc L * card U_loop \<le> A * Suc L * card U"
        using card_loop_le by simp
      moreover have "(R + H) * card (outgoing_edges U_loop) \<le>
          (R + H) * card (outgoing_edges U)"
        using card_out_le by simp
      ultimately show ?thesis
        using loop_bound by linarith
    qed
    show ?thesis
      using scan_insert loop_to_U c_def by linarith
  qed
  also have "\<dots> =
      A * Suc (Suc L) * card U + (R + H) * card (outgoing_edges U)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem direct_insert_costed_bmssp_level_bound_from_local_budgets_with_invariants_and_edge_budget:
  assumes base_budget: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
    and M_cap: "\<And>i. i \<le> l \<Longrightarrow> M_of i \<le> cap"
    and edge_budget:
      "\<And>l d P B d' D a betas bs B' Us U c child_costs.
        direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
          betas bs B' Us U c child_costs \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d P B \<Longrightarrow>
        (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
        t * sum_list
          (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
        h * sum_list
          (map card (range_tree_child_edge_range_list P a betas bs))
          \<le> H * card (outgoing_edges U)"
    and step_budget:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
          Us U_loop c_loop child_costs \<Longrightarrow>
        complete_on d'
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        U = U_loop \<union>
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B) \<Longrightarrow>
        k * card S \<le> cap \<Longrightarrow>
        tree_antichain S \<Longrightarrow>
        fp_iter_capped_scan_cost k cap d S S B + c_insert \<le> A * card U"
    and run:
      "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and S_k_cap: "k * card S \<le> cap"
    and S_anti: "tree_antichain S"
  shows "c \<le> level_range_cost_bound A (R + l * H) (2 * l + 1) U"
  using run sound pre S_reaches below S_k_cap S_anti M_cap
proof (induction l arbitrary: d S B d' B' U c rule: less_induct)
  case (less l)
  show ?case
  proof (cases l)
    case 0
    have run0:
      "direct_insert_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
      using less.prems(1) 0 by simp
    show ?thesis
      using run0 R_pos 0
      by (cases rule: direct_insert_costed_bmssp.cases)
        (simp_all add: split_range_costed_base_level_bound)
  next
    case (Suc l0)
    have run_suc:
      "direct_insert_costed_bmssp \<Delta> M_of t h k cap (Suc l0) d S B d' B' U c"
      using less.prems(1) Suc by simp
    show ?thesis
    proof (cases rule: direct_insert_costed_bmssp_SucE[OF run_suc])
      case (1 c_insert a betas bs Us U_loop c_loop child_costs_loop)
      let ?d_fp = "find_pivots_label_capped k cap d S B"
      let ?P = "find_pivots_pivots_capped k cap d S B"
      let ?W = "{v \<in> bound_tree S B'. ?d_fp v = dist s v}"
      have sound_fp: "sound_label ?d_fp"
        unfolding find_pivots_label_capped_def
        by (rule fp_iter_capped_label_sound[OF less.prems(2) less.prems(4)])
      have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
        using find_pivots_capped_establishes_pivot_pre_concrete
          [OF less.prems(2) less.prems(3) less.prems(4)] .
      have S_subset: "S \<subseteq> V"
        using less.prems(3) unfolding bmssp_pre_full_def by blast
      have P_subset_S: "?P \<subseteq> S"
        unfolding find_pivots_pivots_capped_def by (auto split: if_splits)
      have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
        using P_subset_S less.prems(4) by blast
      have P_k_cap: "k * card ?P \<le> cap"
        by (rule find_pivots_pivots_capped_scaled_card_le
          [OF S_subset less.prems(6)])
      have P_anti: "tree_antichain ?P"
        by (rule find_pivots_pivots_capped_tree_antichain[OF less.prems(7)])
      have child_bound:
        "\<And>c_child U_child S_child B_child d_child B_child'.
          \<lbrakk>direct_insert_costed_bmssp \<Delta> M_of t h k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child;
            bmssp_pre_full ?d_fp S_child B_child;
            \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
            card S_child \<le> M_of l0;
            \<And>x. x \<in> S_child \<Longrightarrow> below_bound (?d_fp x) B_child;
            k * card S_child \<le> cap;
            tree_antichain S_child\<rbrakk>
          \<Longrightarrow> c_child \<le> level_range_cost_bound A (R + l0 * H)
            (2 * l0 + 1) U_child"
      proof -
        fix c_child U_child S_child B_child d_child B_child'
        assume child:
            "direct_insert_costed_bmssp \<Delta> M_of t h k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child"
          and child_pre: "bmssp_pre_full ?d_fp S_child B_child"
          and child_reaches: "\<And>x. x \<in> S_child \<Longrightarrow> reachable s x"
          and child_below:
            "\<And>x. x \<in> S_child \<Longrightarrow> below_bound (?d_fp x) B_child"
          and child_k_cap: "k * card S_child \<le> cap"
          and child_anti: "tree_antichain S_child"
        have M_cap_child: "\<And>i. i \<le> l0 \<Longrightarrow> M_of i \<le> cap"
          using less.prems(8) Suc by simp
        show "c_child \<le> level_range_cost_bound A (R + l0 * H)
            (2 * l0 + 1) U_child"
          by (rule less.IH[of l0 ?d_fp S_child B_child d_child B_child'
                U_child c_child, OF _ child sound_fp child_pre child_reaches
                child_below child_k_cap child_anti M_cap_child])
            (simp add: Suc)
      qed
      have loop_edge_budget:
        "t * sum_list
          (map card (range_tree_child_direct_edge_range_list ?P B a betas bs)) +
         h * sum_list
          (map card (range_tree_child_edge_range_list ?P a betas bs))
          \<le> H * card (outgoing_edges U_loop)"
        by (rule edge_budget[OF 1(4) sound_fp pivot_pre P_reaches])
      have scan_insert:
        "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
          A * card U"
        by (rule step_budget[OF refl 1(3) 1(4) 1(5) 1(1)
            less.prems(2) less.prems(3) less.prems(4) less.prems(5)
            less.prems(6) less.prems(7)])
      have trace:
        "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
        by (rule direct_insert_costed_partition_loop_state_trace
          [OF 1(4) sound_fp pivot_pre P_reaches])
      have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
        by (rule concrete_partition_loop_trace_post[OF trace])
      have finite_U_loop: "finite U_loop"
        using loop_post unfolding bmssp_post_full_def by simp
      have finite_W: "finite ?W"
        by simp
      have finite_U: "finite U"
        using 1(1) finite_U_loop finite_W by simp
      have M_cap_l0: "M_of l0 \<le> cap"
        using less.prems(8) Suc by simp
      have step:
        "c \<le> A * Suc (Suc (2 * l0 + 1)) * card U +
          (R + l0 * H + H) * card (outgoing_edges U)"
        by (rule direct_insert_costed_nonbase_step_closes_level_bound_from_child_bound_with_invariants_and_edge_budget
          [OF 1(4) sound_fp pivot_pre P_reaches P_k_cap P_anti child_bound
            M_cap_l0 source_factor k_pos loop_edge_budget 1(1) finite_U
            scan_insert 1(2)])
      show ?thesis
        using step Suc unfolding level_range_cost_bound_def
        by (simp add: algebra_simps)
    qed
  qed
qed

theorem finite_initial_label_direct_insert_costed_top_level_correct_and_closed_refined_graph_bound_level_cap_from_local_budgets:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and edge_budget:
      "\<And>l' d P B d' D a betas bs B' Us U_loop c_loop child_costs.
        direct_insert_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
          (bmssp_level_cap k t l) l' d P B d' D a betas bs B'
          Us U_loop c_loop child_costs \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d P B \<Longrightarrow>
        (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
        t * sum_list
          (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
        h * sum_list
          (map card (range_tree_child_edge_range_list P a betas bs))
          \<le> H * card (outgoing_edges U_loop)"
    and step_budget:
      "\<And>l' d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) \<Longrightarrow>
        direct_insert_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
          (bmssp_level_cap k t l) l'
          (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) B d' D
          a betas bs B' Us U_loop c_loop child_costs \<Longrightarrow>
        complete_on d'
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
              dist s v} \<Longrightarrow>
        U = U_loop \<union>
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
              dist s v} \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B) \<Longrightarrow>
        k * card S \<le> bmssp_level_cap k t l \<Longrightarrow>
        tree_antichain S \<Longrightarrow>
        fp_iter_capped_scan_cost k (bmssp_level_cap k t l) d S S B +
          c_insert \<le> 2 * A * card U"
    and run:
      "direct_insert_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * H) * edge_count"
proof
  show "sssp_correct d'"
    by (rule finite_initial_label_direct_insert_costed_top_level_correct
      [OF all_reachable run])
next
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  have below: "\<And>x. x \<in> {s} \<Longrightarrow>
      below_bound (finite_initial_label x) Infinity"
    by simp
  have top_cap: "k * card {s} \<le> bmssp_level_cap k t l"
  proof -
    have one_le: "1 \<le> bmssp_level_width t l"
      unfolding bmssp_level_width_def by simp
    have "k * 1 \<le> k * bmssp_level_width t l"
      by (rule mult_left_mono[OF one_le]) simp
    then show ?thesis
      unfolding bmssp_level_cap_def by simp
  qed
  have top_anti: "tree_antichain {s}"
    by simp
  have range_bound:
    "c \<le> level_range_cost_bound (2 * A) (R + l * H) (2 * l + 1) U"
  proof (rule direct_insert_costed_bmssp_level_bound_from_local_budgets_with_invariants_and_edge_budget
      [where A = "2 * A" and R = R and H = H,
        OF _ R_pos source_factor k_pos _ _ _ run sound pre S_reaches below
          top_cap top_anti])
    show "\<Delta> \<le> 2 * A"
      using degree_factor by simp
  next
    fix i
    assume "i \<le> l"
    then show "bmssp_level_cap k t i \<le> bmssp_level_cap k t l"
      by (rule bmssp_level_cap_mono)
  next
    fix l' d P B d' D a betas bs B' Us U_loop c_loop child_costs
    assume loop:
        "direct_insert_costed_partition_loop_state \<Delta>
          (bmssp_level_cap k t) t h k (bmssp_level_cap k t l) l'
          d P B d' D a betas bs B' Us U_loop c_loop child_costs"
      and sound_l: "sound_label d"
      and pre_l: "bmssp_pre_full d P B"
      and reaches_l: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    show "t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list (map card (range_tree_child_edge_range_list P a betas bs))
        \<le> H * card (outgoing_edges U_loop)"
      by (rule edge_budget[OF loop sound_l pre_l reaches_l])
  next
    fix l' d S B D c_insert d' a betas bs B' Us U_loop c_loop child_costs U
    assume D_def:
        "D = label_partition_view
          (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B)"
      and insert:
        "partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B)"
      and loop:
        "direct_insert_costed_partition_loop_state \<Delta>
          (bmssp_level_cap k t) t h k (bmssp_level_cap k t l) l'
          (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) B d' D
          a betas bs B' Us U_loop c_loop child_costs"
      and complete:
        "complete_on d'
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
              dist s v}"
      and U_def:
        "U = U_loop \<union>
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
              dist s v}"
      and sound_s: "sound_label d"
      and pre_s: "bmssp_pre_full d S B"
      and reaches_s: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
      and below_s: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
      and S_k_cap: "k * card S \<le> bmssp_level_cap k t l"
      and anti: "tree_antichain S"
    show "fp_iter_capped_scan_cost k (bmssp_level_cap k t l) d S S B +
        c_insert \<le> 2 * A * card U"
      by (rule step_budget[OF D_def insert loop complete U_def sound_s pre_s
          reaches_s below_s S_k_cap anti])
  qed
  have post_full:
    "bmssp_post_full finite_initial_label {s} Infinity d' Infinity U"
    by (rule direct_insert_costed_bmssp_correct[OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  have U_V: "U = V"
    using post bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  have graph_bound:
    "level_range_cost_bound (2 * A) (R + l * H) (2 * l + 1) U
      \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * H) * edge_count"
  proof -
    have U_card: "card U = vertex_count"
      unfolding U_V vertex_count_def by simp
    have out_le: "card (outgoing_edges U) \<le> edge_count"
      by (rule edge_count_outgoing_bound)
    have out_term:
      "(R + l * H) * card (outgoing_edges U) \<le> (R + l * H) * edge_count"
      using out_le by simp
    show ?thesis
      unfolding level_range_cost_bound_def
      using U_card out_term by (simp add: algebra_simps)
  qed
  show "c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * H) * edge_count"
    using range_bound graph_bound by linarith
qed

corollary finite_initial_label_direct_insert_costed_top_level_correct_and_closed_bmssp_refined_graph_time_bound_level_cap_from_local_budgets:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and edge_budget:
      "\<And>l' d P B d' D a betas bs B' Us U_loop c_loop child_costs.
        direct_insert_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
          (bmssp_level_cap k t l) l' d P B d' D a betas bs B'
          Us U_loop c_loop child_costs \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d P B \<Longrightarrow>
        (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
        t * sum_list
          (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
        h * sum_list
          (map card (range_tree_child_edge_range_list P a betas bs))
          \<le> H * card (outgoing_edges U_loop)"
    and step_budget:
      "\<And>l' d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) \<Longrightarrow>
        direct_insert_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
          (bmssp_level_cap k t l) l'
          (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) B d' D
          a betas bs B' Us U_loop c_loop child_costs \<Longrightarrow>
        complete_on d'
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
              dist s v} \<Longrightarrow>
        U = U_loop \<union>
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
              dist s v} \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B) \<Longrightarrow>
        k * card S \<le> bmssp_level_cap k t l \<Longrightarrow>
        tree_antichain S \<Longrightarrow>
        fp_iter_capped_scan_cost k (bmssp_level_cap k t l) d S S B +
          c_insert \<le> 2 * A * card U"
    and run:
      "direct_insert_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. H)
      (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
proof -
  have graph:
    "sssp_correct d' \<and>
      c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * H) * edge_count"
    by (rule finite_initial_label_direct_insert_costed_top_level_correct_and_closed_refined_graph_bound_level_cap_from_local_budgets
      [OF all_reachable degree_factor R_pos source_factor k_pos edge_budget
        step_budget run])
  have bound:
    "2 * A * (2 * l + 1) * vertex_count + (R + l * H) * edge_count
      \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. H)
        (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
    unfolding bmssp_refined_graph_time_bound_def by simp
  show ?thesis
    using graph bound by linarith
qed

theorem finite_initial_label_direct_insert_costed_top_level_correct_and_closed_refined_graph_bound_level_cap:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and edge_budget:
      "\<And>l' d P B d' D a betas bs B' Us U_loop c_loop child_costs.
        direct_insert_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
          (bmssp_level_cap k t l) l' d P B d' D a betas bs B'
          Us U_loop c_loop child_costs \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d P B \<Longrightarrow>
        (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
        t * sum_list
          (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
        h * sum_list
          (map card (range_tree_child_edge_range_list P a betas bs))
          \<le> H * card (outgoing_edges U_loop)"
    and run:
      "direct_insert_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * H) * edge_count"
proof (rule finite_initial_label_direct_insert_costed_top_level_correct_and_closed_refined_graph_bound_level_cap_from_local_budgets
    [OF all_reachable degree_factor R_pos source_factor k_pos edge_budget _ run])
  fix l' d S B D c_insert d' a betas bs B' Us U_loop c_loop
    child_costs U
  assume D_def:
      "D = label_partition_view
        (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
        (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B)"
    and insert:
      "partition_initial_insert_cost_bound c_insert t
        (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B)"
    and loop:
      "direct_insert_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l'
        (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
        (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) B d' D
        a betas bs B' Us U_loop c_loop child_costs"
    and complete:
      "complete_on d'
        {v \<in> bound_tree S B'.
          find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
            dist s v}"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'.
          find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
            dist s v}"
    and sound_s: "sound_label d"
    and pre_s: "bmssp_pre_full d S B"
    and reaches_s: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below_s: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and S_k_cap: "k * card S \<le> bmssp_level_cap k t l"
    and anti: "tree_antichain S"
  have seen_success:
    "B' = B \<Longrightarrow>
      card (find_pivots_seen_capped k (bmssp_level_cap k t l) d S B)
      \<le> card U"
    by (rule direct_insert_costed_step_seen_success
      [OF loop U_def sound_s pre_s reaches_s below_s])
  show "fp_iter_capped_scan_cost k (bmssp_level_cap k t l) d S S B +
      c_insert \<le> 2 * A * card U"
    by (rule direct_insert_costed_capped_step_scan_insert_budget_from_scaled_seen_or_threshold
      [OF degree degree_factor insert_factor insert_scaled_factor
        seen_scaled_factor insert loop U_def sound_s pre_s reaches_s
        S_k_cap anti k_pos seen_success])
qed

corollary finite_initial_label_direct_insert_costed_top_level_correct_and_closed_bmssp_refined_graph_time_bound_level_cap:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and edge_budget:
      "\<And>l' d P B d' D a betas bs B' Us U_loop c_loop child_costs.
        direct_insert_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
          (bmssp_level_cap k t l) l' d P B d' D a betas bs B'
          Us U_loop c_loop child_costs \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d P B \<Longrightarrow>
        (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
        t * sum_list
          (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
        h * sum_list
          (map card (range_tree_child_edge_range_list P a betas bs))
          \<le> H * card (outgoing_edges U_loop)"
    and run:
      "direct_insert_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. H)
      (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
proof -
  have graph:
    "sssp_correct d' \<and>
      c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * H) * edge_count"
    by (rule finite_initial_label_direct_insert_costed_top_level_correct_and_closed_refined_graph_bound_level_cap
      [OF all_reachable degree degree_factor R_pos insert_factor insert_scaled_factor
        seen_scaled_factor source_factor k_pos edge_budget run])
  have bound:
    "2 * A * (2 * l + 1) * vertex_count + (R + l * H) * edge_count
      \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. H)
        (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
    unfolding bmssp_refined_graph_time_bound_def by simp
  show ?thesis
    using graph bound by linarith
qed

lemma direct_insert_costed_partition_loop_state_trivial_edge_budget:
  assumes run:
    "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
  shows "t * sum_list
      (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
    h * sum_list (map card (range_tree_child_edge_range_list P a betas bs))
    \<le> (t + h) * card (outgoing_edges U)"
proof -
  have mono: "nondecreasing_from a bs"
    by (rule direct_insert_costed_partition_loop_state_mono[OF run])
  have trace: "concrete_partition_loop_trace P B a bs d' B' Us U"
    by (rule direct_insert_costed_partition_loop_state_trace
      [OF run sound pre P_reaches])
  have children:
    "list_all2 (\<lambda>U X. U = X \<and> complete_on d' U) Us
      (range_tree_chain_list P a bs B')"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have U_def: "U = bound_tree P (Fin a) \<union> \<Union>(set Us)"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have Union_eq:
    "\<Union>(set Us) = \<Union>(set (range_tree_chain_list P a bs B'))"
    using children by (induction rule: list_all2_induct) auto
  have U_eq_chain:
    "U = bound_tree P (Fin a) \<union> range_tree_chain P a bs B'"
    using U_def Union_eq Union_range_tree_chain_list[of P a bs B'] by simp
  have chain_subset: "range_tree_chain P a bs B' \<subseteq> U"
    using U_eq_chain by blast
  have outgoing_subset:
    "outgoing_edges (range_tree_chain P a bs B') \<subseteq> outgoing_edges U"
    by (rule outgoing_edges_mono[OF chain_subset])
  have card_out_le:
    "card (outgoing_edges (range_tree_chain P a bs B')) \<le>
      card (outgoing_edges U)"
    by (rule card_mono) (simp_all add: outgoing_subset)
  have sum_le_chain:
    "h * sum_list (map card (range_tree_child_edge_range_list P a betas bs)) +
     t * sum_list
       (map card (range_tree_child_direct_edge_range_list P B a betas bs))
     \<le> (h + t) * card (outgoing_edges (range_tree_chain P a bs B'))"
    by (rule weighted_sum_child_lower_direct_edge_ranges_le_outgoing_edges_chain
      [OF mono])
  have chain_to_U:
    "(h + t) * card (outgoing_edges (range_tree_chain P a bs B')) \<le>
      (h + t) * card (outgoing_edges U)"
    using card_out_le by simp
  show ?thesis
    using sum_le_chain chain_to_U by (simp add: algebra_simps)
qed

corollary finite_initial_label_direct_insert_costed_top_level_correct_and_closed_bmssp_refined_graph_time_bound_level_cap_trivial_edge_budget:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and run:
      "direct_insert_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. t + h)
      (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
proof (rule finite_initial_label_direct_insert_costed_top_level_correct_and_closed_bmssp_refined_graph_time_bound_level_cap
    [OF all_reachable degree degree_factor R_pos insert_factor insert_scaled_factor
      seen_scaled_factor source_factor k_pos _ run])
  fix l' d P B d' D a betas bs B' Us U_loop c_loop child_costs
  assume loop:
      "direct_insert_costed_partition_loop_state \<Delta>
        (bmssp_level_cap k t) t h k (bmssp_level_cap k t l) l'
        d P B d' D a betas bs B' Us U_loop c_loop child_costs"
    and sound_l: "sound_label d"
    and pre_l: "bmssp_pre_full d P B"
    and reaches_l: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
  show "t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list (map card (range_tree_child_edge_range_list P a betas bs))
      \<le> (t + h) * card (outgoing_edges U_loop)"
    by (rule direct_insert_costed_partition_loop_state_trivial_edge_budget
      [OF loop sound_l pre_l reaches_l])
qed

theorem finite_initial_label_direct_insert_costed_top_level_correct_and_closed_bmssp_refined_graph_time_bound_level_cap_amortized:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and run:
      "direct_insert_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. h)
      (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
proof
  show "sssp_correct d'"
    by (rule finite_initial_label_direct_insert_costed_top_level_correct
      [OF all_reachable run])
next
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  have below: "\<And>x. x \<in> {s} \<Longrightarrow>
      below_bound (finite_initial_label x) Infinity"
    by simp
  have top_cap: "k * card {s} \<le> bmssp_level_cap k t l"
  proof -
    have one_le: "1 \<le> bmssp_level_width t l"
      unfolding bmssp_level_width_def by simp
    have "k * 1 \<le> k * bmssp_level_width t l"
      by (rule mult_left_mono[OF one_le]) simp
    then show ?thesis
      unfolding bmssp_level_cap_def by simp
  qed
  have top_anti: "tree_antichain {s}"
    by simp
  have amortized:
    "c \<le> bmssp_amortized_cost_bound (2 * A) R h t l (2 * l + 1)
      Infinity U"
  proof (rule direct_insert_costed_bmssp_amortized_bound_from_local_budgets_with_invariants
      [where A = "2 * A" and R = R,
        OF _ R_pos source_factor k_pos _ _ run sound pre S_reaches below
          top_cap top_anti])
    show "\<Delta> \<le> 2 * A"
      using degree_factor by simp
  next
    fix i
    assume "i \<le> l"
    then show "bmssp_level_cap k t i \<le> bmssp_level_cap k t l"
      by (rule bmssp_level_cap_mono)
  next
    fix l' d S B D c_insert d' a betas bs B' Us U_loop c_loop
      child_costs U
    assume D_def:
        "D = label_partition_view
          (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B)"
      and insert:
        "partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B)"
      and loop:
        "direct_insert_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
          (bmssp_level_cap k t l) l'
          (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) B d' D
          a betas bs B' Us U_loop c_loop child_costs"
      and complete:
        "complete_on d'
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
              dist s v}"
      and U_def:
        "U = U_loop \<union>
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
              dist s v}"
      and sound_s: "sound_label d"
      and pre_s: "bmssp_pre_full d S B"
      and reaches_s: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
      and below_s: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
      and S_k_cap: "k * card S \<le> bmssp_level_cap k t l"
      and anti: "tree_antichain S"
    have seen_success:
      "B' = B \<Longrightarrow>
        card (find_pivots_seen_capped k (bmssp_level_cap k t l) d S B)
        \<le> card U"
      by (rule direct_insert_costed_step_seen_success
        [OF loop U_def sound_s pre_s reaches_s below_s])
    show "fp_iter_capped_scan_cost k (bmssp_level_cap k t l) d S S B +
        c_insert \<le> 2 * A * card U"
      by (rule direct_insert_costed_capped_step_scan_insert_budget_from_scaled_seen_or_threshold
        [OF degree degree_factor insert_factor insert_scaled_factor
          seen_scaled_factor insert loop U_def sound_s pre_s reaches_s
          S_k_cap anti k_pos seen_success])
  qed
  have post_full:
    "bmssp_post_full finite_initial_label {s} Infinity d' Infinity U"
    by (rule direct_insert_costed_bmssp_correct[OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  have U_V: "U = V"
    using post bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  have graph_bound:
    "bmssp_amortized_cost_bound (2 * A) R h t l (2 * l + 1) Infinity U
      \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. h)
        (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
  proof -
    have U_card: "card U = vertex_count"
      unfolding U_V vertex_count_def by simp
    have out_le: "card (outgoing_edges U) \<le> edge_count"
      by (rule edge_count_outgoing_bound)
    have range_le: "card (outgoing_edges_range U 0 Infinity) \<le> edge_count"
      by (rule card_outgoing_edges_range_le_edge_count)
    have out_term:
      "(R + l * h) * card (outgoing_edges U) \<le>
       (R + l * h) * edge_count"
      using out_le by simp
    have range_term:
      "t * card (outgoing_edges_range U 0 Infinity) \<le> t * edge_count"
      using range_le by simp
    show ?thesis
      unfolding bmssp_amortized_cost_bound_def bmssp_refined_graph_time_bound_def
      using U_card out_term range_term by (simp add: algebra_simps; linarith)
  qed
  show "c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. h)
      (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
    using amortized graph_bound by linarith
qed

text \<open>
  The remaining exact split-range results repeat the same source-progress
  closure without the direct-insert edge split.  They are kept because some
  clients of the development may want the simpler range-costed interface, while
  the bucketed headline uses the more refined direct-insert and amortised path.
  The proof shape is the same: extract child calls, use strict progress to
  dominate child sources by child outputs, and close the level recurrence.

  Having both interfaces documented makes the proof stack easier to audit.  The
  exact split-range family is the clean mathematical recurrence, and the
  direct-insert family is the implementation-aware recurrence that exposes the
  bucketed partition's local costs.
\<close>

theorem exact_split_range_costed_partition_loop_state_closes_level_bound_from_child_costs:
  assumes run:
    "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child U_child.
        c_child \<le> level_range_cost_bound A R L U_child)
        child_costs (range_tree_child_list P a bs)"
    and M_cap: "M_of l \<le> cap"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
  shows "c \<le> A * Suc L * card U + (R + t) * card (outgoing_edges U)"
proof -
  have split_run:
    "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    using exact_split_range_costed_refines_split_range_costed(1)[OF run] .
  have trace: "concrete_partition_loop_trace P B a bs d' B' Us U"
    by (rule split_range_costed_partition_loop_state_trace
      [OF split_run sound pre P_reaches])
  have children:
    "list_all2 (\<lambda>U X. U = X \<and> complete_on d' U) Us
      (range_tree_chain_list P a bs B')"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have U_def: "U = bound_tree P (Fin a) \<union> \<Union>(set Us)"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have Union_eq:
    "\<Union>(set Us) = \<Union>(set (range_tree_chain_list P a bs B'))"
    using children by (induction rule: list_all2_induct) auto
  have U_eq_chain:
    "U = bound_tree P (Fin a) \<union> range_tree_chain P a bs B'"
    using U_def Union_eq Union_range_tree_chain_list[of P a bs B'] by simp
  have finite_U: "finite U"
    using U_eq_chain by simp
  have chain_subset: "range_tree_chain P a bs B' \<subseteq> U"
    using U_eq_chain by blast
  have card_chain_le: "card (range_tree_chain P a bs B') \<le> card U"
    by (rule card_mono[OF finite_U chain_subset])
  have outgoing_subset:
    "outgoing_edges (range_tree_chain P a bs B') \<subseteq> outgoing_edges U"
    by (rule outgoing_edges_mono[OF chain_subset])
  have finite_out_U: "finite (outgoing_edges U)"
    by simp
  have card_out_le:
    "card (outgoing_edges (range_tree_chain P a bs B')) \<le>
      card (outgoing_edges U)"
    by (rule card_mono[OF finite_out_U outgoing_subset])
  have loop:
    "c \<le>
      A * L * card (range_tree_chain P a bs B') +
      (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
      Suc h * card (range_tree_chain P a bs B')"
  proof (rule exact_split_range_costed_partition_loop_state_cost_from_child_and_source_bounds
      [OF run child_cost_bounds])
    fix S_child B_child d_child B_child' U_child c_child
    assume child:
        "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child"
      and child_pre: "bmssp_pre_full d S_child B_child"
      and child_reaches: "\<And>x. x \<in> S_child \<Longrightarrow> reachable s x"
      and child_card: "card S_child \<le> M_of l"
      and child_below: "\<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child"
    have child_cap: "card S_child \<le> cap"
      using child_card M_cap by linarith
    show "card S_child \<le> card U_child"
      by (rule exact_split_range_costed_bmssp_source_card_le_from_label_below_all_levels
        [OF child sound child_pre child_reaches child_below child_cap k_pos])
  qed
  have "c \<le>
      A * L * card U + (R + t) * card (outgoing_edges U) + A * card U"
  proof -
    have vterm:
      "A * L * card (range_tree_chain P a bs B') \<le> A * L * card U"
      using card_chain_le by simp
    have eterm:
      "(R + t) * card (outgoing_edges (range_tree_chain P a bs B')) \<le>
       (R + t) * card (outgoing_edges U)"
      using card_out_le by simp
    have source_term:
      "Suc h * card (range_tree_chain P a bs B') \<le> A * card U"
    proof -
      have "Suc h * card (range_tree_chain P a bs B') \<le>
          A * card (range_tree_chain P a bs B')"
        by (rule mult_right_mono[OF source_factor]) simp
      also have "\<dots> \<le> A * card U"
        using card_chain_le by simp
      finally show ?thesis .
    qed
    show ?thesis
      using loop vterm eterm source_term by linarith
  qed
  also have "\<dots> =
      A * Suc L * card U + (R + t) * card (outgoing_edges U)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem exact_split_range_costed_partition_loop_state_closes_level_bound_from_child_costs_and_edge_ranges:
  assumes run:
    "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child U_child.
        c_child \<le> level_range_cost_bound A R L U_child)
        child_costs (range_tree_child_list P a bs)"
    and M_cap: "M_of l \<le> cap"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
  shows "c \<le>
    A * Suc L * card U + R * card (outgoing_edges U) +
    t * sum_list (map card (range_tree_child_edge_range_list P a betas bs))"
proof -
  have split_run:
    "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    using exact_split_range_costed_refines_split_range_costed(1)[OF run] .
  have trace: "concrete_partition_loop_trace P B a bs d' B' Us U"
    by (rule split_range_costed_partition_loop_state_trace
      [OF split_run sound pre P_reaches])
  have children:
    "list_all2 (\<lambda>U X. U = X \<and> complete_on d' U) Us
      (range_tree_chain_list P a bs B')"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have U_def: "U = bound_tree P (Fin a) \<union> \<Union>(set Us)"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have Union_eq:
    "\<Union>(set Us) = \<Union>(set (range_tree_chain_list P a bs B'))"
    using children by (induction rule: list_all2_induct) auto
  have U_eq_chain:
    "U = bound_tree P (Fin a) \<union> range_tree_chain P a bs B'"
    using U_def Union_eq Union_range_tree_chain_list[of P a bs B'] by simp
  have finite_U: "finite U"
    using U_eq_chain by simp
  have chain_subset: "range_tree_chain P a bs B' \<subseteq> U"
    using U_eq_chain by blast
  have card_chain_le: "card (range_tree_chain P a bs B') \<le> card U"
    by (rule card_mono[OF finite_U chain_subset])
  have outgoing_subset:
    "outgoing_edges (range_tree_chain P a bs B') \<subseteq> outgoing_edges U"
    by (rule outgoing_edges_mono[OF chain_subset])
  have finite_out_U: "finite (outgoing_edges U)"
    by simp
  have card_out_le:
    "card (outgoing_edges (range_tree_chain P a bs B')) \<le>
      card (outgoing_edges U)"
    by (rule card_mono[OF finite_out_U outgoing_subset])
  have loop:
    "c \<le>
      A * L * card (range_tree_chain P a bs B') +
      R * card (outgoing_edges (range_tree_chain P a bs B')) +
      t * sum_list (map card (range_tree_child_edge_range_list P a betas bs)) +
      Suc h * card (range_tree_chain P a bs B')"
  proof (rule exact_split_range_costed_partition_loop_state_cost_from_child_source_and_edge_range_bounds
      [OF run sound child_cost_bounds])
    fix S_child B_child d_child B_child' U_child c_child
    assume child:
        "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child"
      and child_pre: "bmssp_pre_full d S_child B_child"
      and child_reaches: "\<And>x. x \<in> S_child \<Longrightarrow> reachable s x"
      and child_card: "card S_child \<le> M_of l"
      and child_below: "\<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child"
    have child_cap: "card S_child \<le> cap"
      using child_card M_cap by linarith
    show "card S_child \<le> card U_child"
      by (rule exact_split_range_costed_bmssp_source_card_le_from_label_below_all_levels
        [OF child sound child_pre child_reaches child_below child_cap k_pos])
  qed
  have "c \<le>
      A * L * card U + R * card (outgoing_edges U) +
      t * sum_list (map card (range_tree_child_edge_range_list P a betas bs)) +
      A * card U"
  proof -
    have vterm:
      "A * L * card (range_tree_chain P a bs B') \<le> A * L * card U"
      using card_chain_le by simp
    have eterm:
      "R * card (outgoing_edges (range_tree_chain P a bs B')) \<le>
       R * card (outgoing_edges U)"
      using card_out_le by simp
    have source_term:
      "Suc h * card (range_tree_chain P a bs B') \<le> A * card U"
    proof -
      have "Suc h * card (range_tree_chain P a bs B') \<le>
          A * card (range_tree_chain P a bs B')"
        by (rule mult_right_mono[OF source_factor]) simp
      also have "\<dots> \<le> A * card U"
        using card_chain_le by simp
      finally show ?thesis .
    qed
    show ?thesis
      using loop vterm eterm source_term by linarith
  qed
  also have "\<dots> =
      A * Suc L * card U + R * card (outgoing_edges U) +
      t * sum_list (map card (range_tree_child_edge_range_list P a betas bs))"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem exact_split_range_costed_partition_loop_state_closes_level_bound_from_child_bound:
  assumes run:
    "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and M_cap: "M_of l \<le> cap"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
  shows "c \<le> A * Suc L * card U + (R + t) * card (outgoing_edges U)"
proof -
  have child_cost_bounds:
    "list_all2 (\<lambda>c_child U_child.
      c_child \<le> level_range_cost_bound A R L U_child)
      child_costs (range_tree_child_list P a bs)"
    by (rule exact_split_range_costed_partition_loop_state_child_cost_bounds
      [OF run child_bound])
  show ?thesis
    by (rule exact_split_range_costed_partition_loop_state_closes_level_bound_from_child_costs
      [OF run sound pre P_reaches child_cost_bounds M_cap source_factor k_pos])
qed

theorem exact_split_range_costed_partition_loop_state_closes_level_bound_from_child_bound_and_edge_ranges:
  assumes run:
    "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and M_cap: "M_of l \<le> cap"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
  shows "c \<le>
    A * Suc L * card U + R * card (outgoing_edges U) +
    t * sum_list (map card (range_tree_child_edge_range_list P a betas bs))"
proof -
  have child_cost_bounds:
    "list_all2 (\<lambda>c_child U_child.
      c_child \<le> level_range_cost_bound A R L U_child)
      child_costs (range_tree_child_list P a bs)"
    by (rule exact_split_range_costed_partition_loop_state_child_cost_bounds
      [OF run child_bound])
  show ?thesis
    by (rule exact_split_range_costed_partition_loop_state_closes_level_bound_from_child_costs_and_edge_ranges
      [OF run sound pre P_reaches child_cost_bounds M_cap source_factor k_pos])
qed

theorem exact_split_range_costed_partition_loop_state_closes_level_bound_from_child_bound_with_invariants:
  assumes run:
    "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and P_k_cap: "k * card P \<le> cap"
    and P_anti: "tree_antichain P"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child;
          k * card S_child \<le> cap;
          tree_antichain S_child\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and M_cap: "M_of l \<le> cap"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
  shows "c \<le> A * Suc L * card U + (R + t) * card (outgoing_edges U)"
proof -
  have P_subset: "P \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have child_cost_bounds:
    "list_all2 (\<lambda>c_child U_child.
      c_child \<le> level_range_cost_bound A R L U_child)
      child_costs (range_tree_child_list P a bs)"
    by (rule exact_split_range_costed_partition_loop_state_child_cost_bounds_with_invariants
      [OF run P_subset P_k_cap P_anti child_bound])
  show ?thesis
    by (rule exact_split_range_costed_partition_loop_state_closes_level_bound_from_child_costs
      [OF run sound pre P_reaches child_cost_bounds M_cap source_factor k_pos])
qed

theorem exact_split_range_costed_nonbase_step_closes_level_bound_from_child_bound:
  assumes loop:
    "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U_loop c_loop child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and M_cap: "M_of l \<le> cap"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
    and U_def: "U = U_loop \<union> W"
    and finite_U: "finite U"
    and scan_insert: "c_scan_insert \<le> A * card U"
    and c_def: "c = c_scan_insert + c_loop"
  shows "c \<le> A * Suc (Suc L) * card U +
    (R + t) * card (outgoing_edges U)"
proof -
  have loop_bound:
    "c_loop \<le> A * Suc L * card U_loop +
      (R + t) * card (outgoing_edges U_loop)"
    by (rule exact_split_range_costed_partition_loop_state_closes_level_bound_from_child_bound
      [OF loop sound pre P_reaches child_bound M_cap source_factor k_pos])
  have U_loop_subset: "U_loop \<subseteq> U"
    using U_def by blast
  have card_loop_le: "card U_loop \<le> card U"
    by (rule card_mono[OF finite_U U_loop_subset])
  have outgoing_subset: "outgoing_edges U_loop \<subseteq> outgoing_edges U"
    by (rule outgoing_edges_mono[OF U_loop_subset])
  have finite_out_U: "finite (outgoing_edges U)"
    by simp
  have card_out_le: "card (outgoing_edges U_loop) \<le> card (outgoing_edges U)"
    by (rule card_mono[OF finite_out_U outgoing_subset])
  have "c \<le>
      A * card U +
      (A * Suc L * card U + (R + t) * card (outgoing_edges U))"
  proof -
    have loop_to_U:
      "c_loop \<le> A * Suc L * card U +
        (R + t) * card (outgoing_edges U)"
    proof -
      have "A * Suc L * card U_loop \<le> A * Suc L * card U"
        using card_loop_le by simp
      moreover have "(R + t) * card (outgoing_edges U_loop) \<le>
          (R + t) * card (outgoing_edges U)"
        using card_out_le by simp
      ultimately show ?thesis
        using loop_bound by linarith
    qed
    show ?thesis
      using scan_insert loop_to_U c_def by linarith
  qed
  also have "\<dots> =
      A * Suc (Suc L) * card U + (R + t) * card (outgoing_edges U)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem exact_split_range_costed_nonbase_step_closes_level_bound_from_child_bound_and_edge_ranges:
  assumes loop:
    "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U_loop c_loop child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and M_cap: "M_of l \<le> cap"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
    and U_def: "U = U_loop \<union> W"
    and finite_U: "finite U"
    and scan_insert: "c_scan_insert \<le> A * card U"
    and c_def: "c = c_scan_insert + c_loop"
  shows "c \<le> A * Suc (Suc L) * card U +
    R * card (outgoing_edges U) +
    t * sum_list (map card (range_tree_child_edge_range_list P a betas bs))"
proof -
  have loop_bound:
    "c_loop \<le>
      A * Suc L * card U_loop + R * card (outgoing_edges U_loop) +
      t * sum_list (map card (range_tree_child_edge_range_list P a betas bs))"
    by (rule exact_split_range_costed_partition_loop_state_closes_level_bound_from_child_bound_and_edge_ranges
      [OF loop sound pre P_reaches child_bound M_cap source_factor k_pos])
  have U_loop_subset: "U_loop \<subseteq> U"
    using U_def by blast
  have card_loop_le: "card U_loop \<le> card U"
    by (rule card_mono[OF finite_U U_loop_subset])
  have outgoing_subset: "outgoing_edges U_loop \<subseteq> outgoing_edges U"
    by (rule outgoing_edges_mono[OF U_loop_subset])
  have finite_out_U: "finite (outgoing_edges U)"
    by simp
  have card_out_le: "card (outgoing_edges U_loop) \<le> card (outgoing_edges U)"
    by (rule card_mono[OF finite_out_U outgoing_subset])
  have "c \<le>
      A * card U +
      (A * Suc L * card U + R * card (outgoing_edges U) +
        t * sum_list (map card (range_tree_child_edge_range_list P a betas bs)))"
  proof -
    have loop_to_U:
      "c_loop \<le>
        A * Suc L * card U + R * card (outgoing_edges U) +
        t * sum_list (map card (range_tree_child_edge_range_list P a betas bs))"
    proof -
      have "A * Suc L * card U_loop \<le> A * Suc L * card U"
        using card_loop_le by simp
      moreover have "R * card (outgoing_edges U_loop) \<le>
          R * card (outgoing_edges U)"
        using card_out_le by simp
      ultimately show ?thesis
        using loop_bound by linarith
    qed
    show ?thesis
      using scan_insert loop_to_U c_def by linarith
  qed
  also have "\<dots> =
      A * Suc (Suc L) * card U + R * card (outgoing_edges U) +
      t * sum_list (map card (range_tree_child_edge_range_list P a betas bs))"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem exact_split_range_costed_nonbase_step_closes_level_bound_from_child_bound_with_invariants:
  assumes loop:
    "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U_loop c_loop child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and P_k_cap: "k * card P \<le> cap"
    and P_anti: "tree_antichain P"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child;
          k * card S_child \<le> cap;
          tree_antichain S_child\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and M_cap: "M_of l \<le> cap"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
    and U_def: "U = U_loop \<union> W"
    and finite_U: "finite U"
    and scan_insert: "c_scan_insert \<le> A * card U"
    and c_def: "c = c_scan_insert + c_loop"
  shows "c \<le> A * Suc (Suc L) * card U +
    (R + t) * card (outgoing_edges U)"
proof -
  have loop_bound:
    "c_loop \<le> A * Suc L * card U_loop +
      (R + t) * card (outgoing_edges U_loop)"
    by (rule exact_split_range_costed_partition_loop_state_closes_level_bound_from_child_bound_with_invariants
      [OF loop sound pre P_reaches P_k_cap P_anti child_bound M_cap
        source_factor k_pos])
  have U_loop_subset: "U_loop \<subseteq> U"
    using U_def by blast
  have card_loop_le: "card U_loop \<le> card U"
    by (rule card_mono[OF finite_U U_loop_subset])
  have outgoing_subset: "outgoing_edges U_loop \<subseteq> outgoing_edges U"
    by (rule outgoing_edges_mono[OF U_loop_subset])
  have finite_out_U: "finite (outgoing_edges U)"
    by simp
  have card_out_le: "card (outgoing_edges U_loop) \<le> card (outgoing_edges U)"
    by (rule card_mono[OF finite_out_U outgoing_subset])
  have "c \<le>
      A * card U +
      (A * Suc L * card U + (R + t) * card (outgoing_edges U))"
  proof -
    have loop_to_U:
      "c_loop \<le> A * Suc L * card U +
        (R + t) * card (outgoing_edges U)"
    proof -
      have "A * Suc L * card U_loop \<le> A * Suc L * card U"
        using card_loop_le by simp
      moreover have "(R + t) * card (outgoing_edges U_loop) \<le>
          (R + t) * card (outgoing_edges U)"
        using card_out_le by simp
      ultimately show ?thesis
        using loop_bound by linarith
    qed
    show ?thesis
      using scan_insert loop_to_U c_def by linarith
  qed
  also have "\<dots> =
      A * Suc (Suc L) * card U + (R + t) * card (outgoing_edges U)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem exact_split_range_costed_bmssp_level_bound_from_local_budgets:
  assumes base_budget: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
    and M_cap: "\<And>i. i \<le> l \<Longrightarrow> M_of i \<le> cap"
    and step_budget:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
          Us U_loop c_loop child_costs \<Longrightarrow>
        complete_on d'
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        U = U_loop \<union>
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B) \<Longrightarrow>
        fp_iter_capped_scan_cost k cap d S S B + c_insert \<le> A * card U"
    and run:
      "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
  shows "c \<le> level_range_cost_bound A (R + l * t) (2 * l + 1) U"
  using run sound pre S_reaches below M_cap
proof (induction l arbitrary: d S B d' B' U c rule: less_induct)
  case (less l)
  show ?case
  proof (cases l)
    case 0
    have run0:
      "exact_split_range_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
      using less.prems(1) 0 by simp
    have split_run0:
      "split_range_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
      using exact_split_range_costed_refines_split_range_costed(2)[OF run0] .
    show ?thesis
      using split_run0 R_pos 0
      by (cases rule: split_range_costed_bmssp.cases)
        (simp_all add: split_range_costed_base_level_bound)
  next
    case (Suc l0)
    have run_suc:
      "exact_split_range_costed_bmssp \<Delta> M_of t h k cap (Suc l0) d S B d' B' U c"
      using less.prems(1) Suc by simp
    show ?thesis
    proof (cases rule: exact_split_range_costed_bmssp_SucE[OF run_suc])
      case (1 c_insert a betas bs Us U_loop c_loop child_costs_loop)
      let ?d_fp = "find_pivots_label_capped k cap d S B"
      let ?P = "find_pivots_pivots_capped k cap d S B"
      let ?W = "{v \<in> bound_tree S B'. ?d_fp v = dist s v}"
      have sound_fp: "sound_label ?d_fp"
        unfolding find_pivots_label_capped_def
        by (rule fp_iter_capped_label_sound[OF less.prems(2) less.prems(4)])
      have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
        using find_pivots_capped_establishes_pivot_pre_concrete
          [OF less.prems(2) less.prems(3) less.prems(4)] .
      have P_subset_S: "?P \<subseteq> S"
        unfolding find_pivots_pivots_capped_def by (auto split: if_splits)
      have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
        using P_subset_S less.prems(4) by blast
      have child_bound:
        "\<And>c_child U_child S_child B_child d_child B_child'.
          \<lbrakk>exact_split_range_costed_bmssp \<Delta> M_of t h k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child;
            bmssp_pre_full ?d_fp S_child B_child;
            \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
            card S_child \<le> M_of l0;
            \<And>x. x \<in> S_child \<Longrightarrow> below_bound (?d_fp x) B_child\<rbrakk>
          \<Longrightarrow> c_child \<le> level_range_cost_bound A (R + l0 * t)
            (2 * l0 + 1) U_child"
      proof -
        fix c_child U_child S_child B_child d_child B_child'
        assume child:
            "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child"
          and child_pre: "bmssp_pre_full ?d_fp S_child B_child"
          and child_reaches: "\<And>x. x \<in> S_child \<Longrightarrow> reachable s x"
          and child_below: "\<And>x. x \<in> S_child \<Longrightarrow> below_bound (?d_fp x) B_child"
        have M_cap_child: "\<And>i. i \<le> l0 \<Longrightarrow> M_of i \<le> cap"
          using less.prems(6) Suc by simp
        show "c_child \<le> level_range_cost_bound A (R + l0 * t)
            (2 * l0 + 1) U_child"
          by (rule less.IH[of l0 ?d_fp S_child B_child d_child B_child'
                U_child c_child, OF _ child sound_fp child_pre child_reaches
                child_below M_cap_child])
            (simp add: Suc)
      qed
      have scan_insert:
        "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
          A * card U"
        by (rule step_budget[OF refl 1(3) 1(4) 1(5) 1(1)
            less.prems(2) less.prems(3) less.prems(4) less.prems(5)])
      have trace:
        "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
      proof -
        have split_loop:
          "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l0
            ?d_fp ?P B d'
            (label_partition_view ?d_fp ?P) a betas bs B' Us U_loop c_loop
            child_costs_loop"
          using exact_split_range_costed_refines_split_range_costed(1)[OF 1(4)]
            by simp
        show ?thesis
          by (rule split_range_costed_partition_loop_state_trace
            [OF split_loop sound_fp pivot_pre P_reaches])
      qed
      have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
        by (rule concrete_partition_loop_trace_post[OF trace])
      have finite_U_loop: "finite U_loop"
        using loop_post unfolding bmssp_post_full_def by simp
      have finite_W: "finite ?W"
        by simp
      have finite_U: "finite U"
        using 1(1) finite_U_loop finite_W by simp
      have M_cap_l0: "M_of l0 \<le> cap"
        using less.prems(6) Suc by simp
      have step:
        "c \<le> A * Suc (Suc (2 * l0 + 1)) * card U +
          (R + l0 * t + t) * card (outgoing_edges U)"
        by (rule exact_split_range_costed_nonbase_step_closes_level_bound_from_child_bound
          [OF 1(4) sound_fp pivot_pre P_reaches child_bound M_cap_l0
            source_factor k_pos 1(1) finite_U scan_insert 1(2)])
      show ?thesis
        using step Suc unfolding level_range_cost_bound_def
        by (simp add: algebra_simps)
    qed
  qed
qed

theorem exact_split_range_costed_bmssp_level_bound_from_local_budgets_with_invariants:
  assumes base_budget: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
    and M_cap: "\<And>i. i \<le> l \<Longrightarrow> M_of i \<le> cap"
    and step_budget:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
          Us U_loop c_loop child_costs \<Longrightarrow>
        complete_on d'
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        U = U_loop \<union>
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B) \<Longrightarrow>
        k * card S \<le> cap \<Longrightarrow>
        tree_antichain S \<Longrightarrow>
        fp_iter_capped_scan_cost k cap d S S B + c_insert \<le> A * card U"
    and run:
      "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and S_k_cap: "k * card S \<le> cap"
    and S_anti: "tree_antichain S"
  shows "c \<le> level_range_cost_bound A (R + l * t) (2 * l + 1) U"
  using run sound pre S_reaches below S_k_cap S_anti M_cap
proof (induction l arbitrary: d S B d' B' U c rule: less_induct)
  case (less l)
  show ?case
  proof (cases l)
    case 0
    have run0:
      "exact_split_range_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
      using less.prems(1) 0 by simp
    have split_run0:
      "split_range_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
      using exact_split_range_costed_refines_split_range_costed(2)[OF run0] .
    show ?thesis
      using split_run0 R_pos 0
      by (cases rule: split_range_costed_bmssp.cases)
        (simp_all add: split_range_costed_base_level_bound)
  next
    case (Suc l0)
    have run_suc:
      "exact_split_range_costed_bmssp \<Delta> M_of t h k cap (Suc l0) d S B d' B' U c"
      using less.prems(1) Suc by simp
    show ?thesis
    proof (cases rule: exact_split_range_costed_bmssp_SucE[OF run_suc])
      case (1 c_insert a betas bs Us U_loop c_loop child_costs_loop)
      let ?d_fp = "find_pivots_label_capped k cap d S B"
      let ?P = "find_pivots_pivots_capped k cap d S B"
      let ?W = "{v \<in> bound_tree S B'. ?d_fp v = dist s v}"
      have sound_fp: "sound_label ?d_fp"
        unfolding find_pivots_label_capped_def
        by (rule fp_iter_capped_label_sound[OF less.prems(2) less.prems(4)])
      have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
        using find_pivots_capped_establishes_pivot_pre_concrete
          [OF less.prems(2) less.prems(3) less.prems(4)] .
      have S_subset: "S \<subseteq> V"
        using less.prems(3) unfolding bmssp_pre_full_def by blast
      have P_subset_S: "?P \<subseteq> S"
        unfolding find_pivots_pivots_capped_def by (auto split: if_splits)
      have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
        using P_subset_S less.prems(4) by blast
      have P_k_cap: "k * card ?P \<le> cap"
        by (rule find_pivots_pivots_capped_scaled_card_le
          [OF S_subset less.prems(6)])
      have P_anti: "tree_antichain ?P"
        by (rule find_pivots_pivots_capped_tree_antichain[OF less.prems(7)])
      have child_bound:
        "\<And>c_child U_child S_child B_child d_child B_child'.
          \<lbrakk>exact_split_range_costed_bmssp \<Delta> M_of t h k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child;
            bmssp_pre_full ?d_fp S_child B_child;
            \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
            card S_child \<le> M_of l0;
            \<And>x. x \<in> S_child \<Longrightarrow> below_bound (?d_fp x) B_child;
            k * card S_child \<le> cap;
            tree_antichain S_child\<rbrakk>
          \<Longrightarrow> c_child \<le> level_range_cost_bound A (R + l0 * t)
            (2 * l0 + 1) U_child"
      proof -
        fix c_child U_child S_child B_child d_child B_child'
        assume child:
            "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child"
          and child_pre: "bmssp_pre_full ?d_fp S_child B_child"
          and child_reaches: "\<And>x. x \<in> S_child \<Longrightarrow> reachable s x"
          and child_below:
            "\<And>x. x \<in> S_child \<Longrightarrow> below_bound (?d_fp x) B_child"
          and child_k_cap: "k * card S_child \<le> cap"
          and child_anti: "tree_antichain S_child"
        have M_cap_child: "\<And>i. i \<le> l0 \<Longrightarrow> M_of i \<le> cap"
          using less.prems(8) Suc by simp
        show "c_child \<le> level_range_cost_bound A (R + l0 * t)
            (2 * l0 + 1) U_child"
          by (rule less.IH[of l0 ?d_fp S_child B_child d_child B_child'
                U_child c_child, OF _ child sound_fp child_pre child_reaches
                child_below child_k_cap child_anti M_cap_child])
            (simp add: Suc)
      qed
      have scan_insert:
        "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
          A * card U"
        by (rule step_budget[OF refl 1(3) 1(4) 1(5) 1(1)
            less.prems(2) less.prems(3) less.prems(4) less.prems(5)
            less.prems(6) less.prems(7)])
      have trace:
        "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
      proof -
        have split_loop:
          "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l0
            ?d_fp ?P B d'
            (label_partition_view ?d_fp ?P) a betas bs B' Us U_loop c_loop
            child_costs_loop"
          using exact_split_range_costed_refines_split_range_costed(1)[OF 1(4)]
            by simp
        show ?thesis
          by (rule split_range_costed_partition_loop_state_trace
            [OF split_loop sound_fp pivot_pre P_reaches])
      qed
      have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
        by (rule concrete_partition_loop_trace_post[OF trace])
      have finite_U_loop: "finite U_loop"
        using loop_post unfolding bmssp_post_full_def by simp
      have finite_W: "finite ?W"
        by simp
      have finite_U: "finite U"
        using 1(1) finite_U_loop finite_W by simp
      have M_cap_l0: "M_of l0 \<le> cap"
        using less.prems(8) Suc by simp
      have step:
        "c \<le> A * Suc (Suc (2 * l0 + 1)) * card U +
          (R + l0 * t + t) * card (outgoing_edges U)"
        by (rule exact_split_range_costed_nonbase_step_closes_level_bound_from_child_bound_with_invariants
          [OF 1(4) sound_fp pivot_pre P_reaches P_k_cap P_anti child_bound
            M_cap_l0 source_factor k_pos 1(1) finite_U scan_insert 1(2)])
      show ?thesis
        using step Suc unfolding level_range_cost_bound_def
        by (simp add: algebra_simps)
    qed
  qed
qed

theorem finite_initial_label_exact_split_range_costed_top_level_correct_and_local_budget_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and base_budget: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
    and M_cap: "\<And>i. i \<le> l \<Longrightarrow> M_of i \<le> cap"
    and step_budget:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
          Us U_loop c_loop child_costs \<Longrightarrow>
        complete_on d'
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        U = U_loop \<union>
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B) \<Longrightarrow>
        fp_iter_capped_scan_cost k cap d S S B + c_insert \<le> A * card U"
    and run:
      "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> level_range_cost_bound A (R + l * t) (2 * l + 1) U"
proof
  show "sssp_correct d'"
    by (rule finite_initial_label_exact_split_range_costed_top_level_correct
      [OF all_reachable run])
next
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  have below: "\<And>x. x \<in> {s} \<Longrightarrow> below_bound (finite_initial_label x) Infinity"
    by simp
  show "c \<le> level_range_cost_bound A (R + l * t) (2 * l + 1) U"
    by (rule exact_split_range_costed_bmssp_level_bound_from_local_budgets
      [OF base_budget R_pos source_factor k_pos M_cap step_budget run sound pre
        S_reaches below])
qed

theorem finite_initial_label_exact_split_range_costed_top_level_correct_and_local_budget_graph_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and base_budget: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
    and M_cap: "\<And>i. i \<le> l \<Longrightarrow> M_of i \<le> cap"
    and step_budget:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
          Us U_loop c_loop child_costs \<Longrightarrow>
        complete_on d'
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        U = U_loop \<union>
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B) \<Longrightarrow>
        fp_iter_capped_scan_cost k cap d S S B + c_insert \<le> A * card U"
    and run:
      "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> A * (2 * l + 1) * vertex_count + (R + l * t) * edge_count"
proof -
  have combined:
    "sssp_correct d' \<and>
      c \<le> level_range_cost_bound A (R + l * t) (2 * l + 1) U"
    by (rule finite_initial_label_exact_split_range_costed_top_level_correct_and_local_budget_bound
      [OF all_reachable base_budget R_pos source_factor k_pos M_cap step_budget run])
  then have correct: "sssp_correct d'"
    by blast
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  have post_full:
    "bmssp_post_full finite_initial_label {s} Infinity d' Infinity U"
    by (rule exact_split_range_costed_bmssp_correct[OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  have U_V: "U = V"
    using post bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  have cost_U:
      "c \<le> level_range_cost_bound A (R + l * t) (2 * l + 1) U"
    using combined by blast
  have graph_bound:
    "level_range_cost_bound A (R + l * t) (2 * l + 1) U
      \<le> A * (2 * l + 1) * vertex_count + (R + l * t) * edge_count"
  proof -
    have U_card: "card U = vertex_count"
      unfolding U_V vertex_count_def by simp
    have out_le: "card (outgoing_edges U) \<le> edge_count"
      by (rule edge_count_outgoing_bound)
    have out_term:
      "(R + l * t) * card (outgoing_edges U) \<le> (R + l * t) * edge_count"
      using out_le by simp
    show ?thesis
      unfolding level_range_cost_bound_def
      using U_card out_term by (simp add: algebra_simps)
  qed
  show ?thesis
    using correct cost_U graph_bound by linarith
qed

theorem finite_initial_label_exact_split_range_costed_top_level_correct_and_scaled_seen_progress_graph_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and M_cap: "\<And>i. i \<le> l \<Longrightarrow> M_of i \<le> cap"
    and step_scaled_seen_progress:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
          Us U_loop c_loop child_costs \<Longrightarrow>
        complete_on d'
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        U = U_loop \<union>
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B) \<Longrightarrow>
        k * card S \<le> cap \<and> tree_antichain S \<and>
        (B' = B \<longrightarrow>
          card (find_pivots_seen_capped k cap d S B) \<le> card U)"
    and run:
      "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * t) * edge_count"
proof (rule finite_initial_label_exact_split_range_costed_top_level_correct_and_local_budget_graph_bound
    [where A = "2 * A" and R = R,
      OF all_reachable _ R_pos source_factor k_pos M_cap _ run])
  show "\<Delta> \<le> 2 * A"
    using degree_factor by simp
next
  fix l d S B D c_insert d' a betas bs B' Us U_loop c_loop child_costs U
  assume D_def:
      "D = label_partition_view
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B)"
    and insert:
      "partition_initial_insert_cost_bound c_insert t
        (find_pivots_pivots_capped k cap d S B)"
    and loop:
      "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
        Us U_loop c_loop child_costs"
    and complete:
      "complete_on d'
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v}"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v}"
    and sound_s: "sound_label d"
    and pre_s: "bmssp_pre_full d S B"
    and reaches_s: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below_s: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
  have progress:
      "k * card S \<le> cap \<and> tree_antichain S \<and>
        (B' = B \<longrightarrow>
          card (find_pivots_seen_capped k cap d S B) \<le> card U)"
    by (rule step_scaled_seen_progress
      [OF D_def insert loop complete U_def sound_s pre_s reaches_s below_s])
  then have S_k_cap: "k * card S \<le> cap"
    by blast
  from progress have anti: "tree_antichain S"
    by blast
  from progress have seen_success:
      "B' = B \<Longrightarrow>
        card (find_pivots_seen_capped k cap d S B) \<le> card U"
    by blast
  have split_loop:
    "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
      (find_pivots_label_capped k cap d S B)
      (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
      Us U_loop c_loop child_costs"
    by (rule exact_split_range_costed_refines_split_range_costed(1)[OF loop])
  show "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
      2 * A * card U"
    by (rule split_range_costed_capped_step_scan_insert_budget_from_scaled_seen_or_threshold
      [OF degree degree_factor insert_factor insert_scaled_factor
        seen_scaled_factor insert split_loop U_def sound_s pre_s reaches_s
        S_k_cap anti k_pos seen_success])
qed

theorem finite_initial_label_exact_split_range_costed_top_level_correct_and_scaled_seen_progress_graph_bound_level_cap:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and step_scaled_seen_progress:
      "\<And>l' d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) \<Longrightarrow>
        exact_split_range_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
          (bmssp_level_cap k t l) l'
          (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) B d' D
          a betas bs B' Us U_loop c_loop child_costs \<Longrightarrow>
        complete_on d'
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
              dist s v} \<Longrightarrow>
        U = U_loop \<union>
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
              dist s v} \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B) \<Longrightarrow>
        k * card S \<le> bmssp_level_cap k t l \<and> tree_antichain S \<and>
        (B' = B \<longrightarrow>
          card (find_pivots_seen_capped k (bmssp_level_cap k t l) d S B) \<le>
            card U)"
    and run:
      "exact_split_range_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * t) * edge_count"
proof (rule finite_initial_label_exact_split_range_costed_top_level_correct_and_scaled_seen_progress_graph_bound
    [OF all_reachable degree degree_factor R_pos insert_factor insert_scaled_factor
      seen_scaled_factor source_factor k_pos _ _ run])
  fix i
  assume "i \<le> l"
  then show "bmssp_level_cap k t i \<le> bmssp_level_cap k t l"
    by (rule bmssp_level_cap_mono)
next
  fix l' d S B D c_insert d' a betas bs B' Us U_loop c_loop child_costs U
  assume D_def:
      "D = label_partition_view
        (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
        (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B)"
    and insert:
      "partition_initial_insert_cost_bound c_insert t
        (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B)"
    and loop:
      "exact_split_range_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l'
        (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
        (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) B d' D
        a betas bs B' Us U_loop c_loop child_costs"
    and complete:
      "complete_on d'
        {v \<in> bound_tree S B'.
          find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
            dist s v}"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'.
          find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
            dist s v}"
    and sound_s: "sound_label d"
    and pre_s: "bmssp_pre_full d S B"
    and reaches_s: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below_s: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
  show "k * card S \<le> bmssp_level_cap k t l \<and> tree_antichain S \<and>
      (B' = B \<longrightarrow>
        card (find_pivots_seen_capped k (bmssp_level_cap k t l) d S B)
        \<le> card U)"
    by (rule step_scaled_seen_progress
      [OF D_def insert loop complete U_def sound_s pre_s reaches_s below_s])
qed

theorem finite_initial_label_exact_split_range_costed_top_level_correct_and_scaled_seen_success_graph_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and top_cap: "k \<le> cap"
    and M_cap: "\<And>i. i \<le> l \<Longrightarrow> M_of i \<le> cap"
    and seen_success:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
          Us U_loop c_loop child_costs \<Longrightarrow>
        complete_on d'
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        U = U_loop \<union>
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B) \<Longrightarrow>
        k * card S \<le> cap \<Longrightarrow>
        tree_antichain S \<Longrightarrow>
        B' = B \<Longrightarrow>
        card (find_pivots_seen_capped k cap d S B) \<le> card U"
    and run:
      "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * t) * edge_count"
proof -
  have correct: "sssp_correct d'"
    by (rule finite_initial_label_exact_split_range_costed_top_level_correct
      [OF all_reachable run])
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  have below: "\<And>x. x \<in> {s} \<Longrightarrow>
      below_bound (finite_initial_label x) Infinity"
    by simp
  have S_k_cap: "k * card {s} \<le> cap"
    using top_cap by simp
  have S_anti: "tree_antichain {s}"
    by simp
  have range_bound:
    "c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
  proof (rule exact_split_range_costed_bmssp_level_bound_from_local_budgets_with_invariants
      [where A = "2 * A" and R = R,
        OF _ R_pos source_factor k_pos M_cap _ run sound pre S_reaches below
          S_k_cap S_anti])
    show "\<Delta> \<le> 2 * A"
      using degree_factor by simp
  next
    fix l d S B D c_insert d' a betas bs B' Us U_loop c_loop child_costs U
    assume D_def:
        "D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B)"
      and insert:
        "partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B)"
      and loop:
        "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
          Us U_loop c_loop child_costs"
      and complete:
        "complete_on d'
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v =
            dist s v}"
      and U_def:
        "U = U_loop \<union>
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v =
            dist s v}"
      and sound_s: "sound_label d"
      and pre_s: "bmssp_pre_full d S B"
      and reaches_s: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
      and below_s: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
      and S_k_cap: "k * card S \<le> cap"
      and anti: "tree_antichain S"
    have split_loop:
      "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
        Us U_loop c_loop child_costs"
      by (rule exact_split_range_costed_refines_split_range_costed(1)[OF loop])
    have seen_success_step:
      "B' = B \<Longrightarrow>
        card (find_pivots_seen_capped k cap d S B) \<le> card U"
      by (rule seen_success
        [OF D_def insert loop complete U_def sound_s pre_s reaches_s below_s
          S_k_cap anti])
    show "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
        2 * A * card U"
      by (rule split_range_costed_capped_step_scan_insert_budget_from_scaled_seen_or_threshold
        [OF degree degree_factor insert_factor insert_scaled_factor
          seen_scaled_factor insert split_loop U_def sound_s pre_s reaches_s
          S_k_cap anti k_pos seen_success_step])
  qed
  have post_full:
    "bmssp_post_full finite_initial_label {s} Infinity d' Infinity U"
    by (rule exact_split_range_costed_bmssp_correct[OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  have U_V: "U = V"
    using post bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  have graph_bound:
    "level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U
      \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * t) * edge_count"
  proof -
    have U_card: "card U = vertex_count"
      unfolding U_V vertex_count_def by simp
    have out_le: "card (outgoing_edges U) \<le> edge_count"
      by (rule edge_count_outgoing_bound)
    have out_term:
      "(R + l * t) * card (outgoing_edges U) \<le> (R + l * t) * edge_count"
      using out_le by simp
    show ?thesis
      unfolding level_range_cost_bound_def
      using U_card out_term by (simp add: algebra_simps)
  qed
  show ?thesis
    using correct range_bound graph_bound by linarith
qed

theorem finite_initial_label_exact_split_range_costed_top_level_correct_and_scaled_seen_success_graph_bound_level_cap:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and seen_success:
      "\<And>l' d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) \<Longrightarrow>
        exact_split_range_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
          (bmssp_level_cap k t l) l'
          (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) B d' D
          a betas bs B' Us U_loop c_loop child_costs \<Longrightarrow>
        complete_on d'
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
              dist s v} \<Longrightarrow>
        U = U_loop \<union>
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
              dist s v} \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B) \<Longrightarrow>
        k * card S \<le> bmssp_level_cap k t l \<Longrightarrow>
        tree_antichain S \<Longrightarrow>
        B' = B \<Longrightarrow>
        card (find_pivots_seen_capped k (bmssp_level_cap k t l) d S B) \<le>
          card U"
    and run:
      "exact_split_range_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * t) * edge_count"
proof (rule finite_initial_label_exact_split_range_costed_top_level_correct_and_scaled_seen_success_graph_bound
    [OF all_reachable degree degree_factor R_pos insert_factor insert_scaled_factor
      seen_scaled_factor source_factor k_pos _ _ _ run])
  show "k \<le> bmssp_level_cap k t l"
  proof -
    have one_le: "1 \<le> bmssp_level_width t l"
      unfolding bmssp_level_width_def by simp
    have "k * 1 \<le> k * bmssp_level_width t l"
      by (rule mult_left_mono[OF one_le]) simp
    then show ?thesis
      unfolding bmssp_level_cap_def by simp
  qed
next
  fix i
  assume "i \<le> l"
  then show "bmssp_level_cap k t i \<le> bmssp_level_cap k t l"
    by (rule bmssp_level_cap_mono)
next
  fix l' d S B D c_insert d' a betas bs B' Us U_loop c_loop child_costs U
  assume D_def:
      "D = label_partition_view
        (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
        (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B)"
    and insert:
      "partition_initial_insert_cost_bound c_insert t
        (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B)"
    and loop:
      "exact_split_range_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l'
        (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
        (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) B d' D
        a betas bs B' Us U_loop c_loop child_costs"
    and complete:
      "complete_on d'
        {v \<in> bound_tree S B'.
          find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
            dist s v}"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'.
          find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
            dist s v}"
    and sound_s: "sound_label d"
    and pre_s: "bmssp_pre_full d S B"
    and reaches_s: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below_s: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and S_k_cap: "k * card S \<le> bmssp_level_cap k t l"
    and anti: "tree_antichain S"
  show "B' = B \<Longrightarrow>
      card (find_pivots_seen_capped k (bmssp_level_cap k t l) d S B)
      \<le> card U"
    by (rule seen_success
      [OF D_def insert loop complete U_def sound_s pre_s reaches_s below_s
        S_k_cap anti])
qed

theorem finite_initial_label_exact_split_range_costed_top_level_correct_and_closed_scaled_graph_bound_level_cap:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and run:
      "exact_split_range_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * t) * edge_count"
proof (rule finite_initial_label_exact_split_range_costed_top_level_correct_and_scaled_seen_success_graph_bound_level_cap
    [OF all_reachable degree degree_factor R_pos insert_factor insert_scaled_factor
      seen_scaled_factor source_factor k_pos _ run])
  fix l' d S B D c_insert d' a betas bs B' Us U_loop c_loop child_costs U
  assume loop:
      "exact_split_range_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l'
        (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
        (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) B d' D
        a betas bs B' Us U_loop c_loop child_costs"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'.
          find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
            dist s v}"
    and sound_s: "sound_label d"
    and pre_s: "bmssp_pre_full d S B"
    and reaches_s: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below_s: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and success: "B' = B"
  show "card (find_pivots_seen_capped k (bmssp_level_cap k t l) d S B)
      \<le> card U"
    by (rule exact_split_range_costed_step_seen_success
      [OF loop U_def sound_s pre_s reaches_s below_s success])
qed

corollary finite_initial_label_exact_split_range_costed_top_level_correct_and_closed_bmssp_graph_time_bound_level_cap:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and run:
      "exact_split_range_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> bmssp_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. l) (\<lambda>_. t)
      (\<lambda>_. edge_count) vertex_count"
proof -
  have graph:
    "sssp_correct d' \<and>
      c \<le> 2 * A * (2 * l + 1) * vertex_count +
        (R + l * t) * edge_count"
    by (rule finite_initial_label_exact_split_range_costed_top_level_correct_and_closed_scaled_graph_bound_level_cap
      [OF all_reachable degree degree_factor R_pos insert_factor insert_scaled_factor
        seen_scaled_factor source_factor k_pos run])
  then show ?thesis
    unfolding bmssp_graph_time_bound_def by simp
qed

lemma exact_split_range_costed_partition_loop_state_trivial_edge_budget:
  assumes run:
    "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
  shows "t * sum_list (map card (range_tree_child_edge_range_list P a betas bs))
    \<le> t * card (outgoing_edges U)"
proof -
  have split_run:
    "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    using exact_split_range_costed_refines_split_range_costed(1)[OF run] .
  have mono: "nondecreasing_from a bs"
    by (rule split_range_costed_partition_loop_state_mono[OF split_run])
  have trace: "concrete_partition_loop_trace P B a bs d' B' Us U"
    by (rule split_range_costed_partition_loop_state_trace
      [OF split_run sound pre P_reaches])
  have children:
    "list_all2 (\<lambda>U X. U = X \<and> complete_on d' U) Us
      (range_tree_chain_list P a bs B')"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have U_def: "U = bound_tree P (Fin a) \<union> \<Union>(set Us)"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have Union_eq:
    "\<Union>(set Us) = \<Union>(set (range_tree_chain_list P a bs B'))"
    using children by (induction rule: list_all2_induct) auto
  have U_eq_chain:
    "U = bound_tree P (Fin a) \<union> range_tree_chain P a bs B'"
    using U_def Union_eq Union_range_tree_chain_list[of P a bs B'] by simp
  have chain_subset: "range_tree_chain P a bs B' \<subseteq> U"
    using U_eq_chain by blast
  have outgoing_subset:
    "outgoing_edges (range_tree_chain P a bs B') \<subseteq> outgoing_edges U"
    by (rule outgoing_edges_mono[OF chain_subset])
  have card_out_le:
    "card (outgoing_edges (range_tree_chain P a bs B')) \<le>
      card (outgoing_edges U)"
    by (rule card_mono) (simp_all add: outgoing_subset)
  have sum_le_chain:
    "sum_list (map card (range_tree_child_edge_range_list P a betas bs))
      \<le> card (outgoing_edges (range_tree_chain P a bs B'))"
    by (rule sum_card_range_tree_child_edge_range_list_le_outgoing_edges_chain
      [OF mono])
  have sum_le_U:
    "sum_list (map card (range_tree_child_edge_range_list P a betas bs))
      \<le> card (outgoing_edges U)"
    using sum_le_chain card_out_le by linarith
  then show ?thesis
    by simp
qed

theorem exact_split_range_costed_partition_loop_state_closes_level_bound_from_child_bound_with_invariants_and_edge_budget:
  assumes run:
    "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and P_k_cap: "k * card P \<le> cap"
    and P_anti: "tree_antichain P"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child;
          k * card S_child \<le> cap;
          tree_antichain S_child\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and M_cap: "M_of l \<le> cap"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
    and edge_budget:
      "t * sum_list (map card (range_tree_child_edge_range_list P a betas bs)) \<le>
        H * card (outgoing_edges U)"
  shows "c \<le> A * Suc L * card U + (R + H) * card (outgoing_edges U)"
proof -
  have P_subset: "P \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have child_cost_bounds:
    "list_all2 (\<lambda>c_child U_child.
      c_child \<le> level_range_cost_bound A R L U_child)
      child_costs (range_tree_child_list P a bs)"
    by (rule exact_split_range_costed_partition_loop_state_child_cost_bounds_with_invariants
      [OF run P_subset P_k_cap P_anti child_bound])
  have loop:
    "c \<le>
      A * Suc L * card U + R * card (outgoing_edges U) +
      t * sum_list (map card (range_tree_child_edge_range_list P a betas bs))"
    by (rule exact_split_range_costed_partition_loop_state_closes_level_bound_from_child_costs_and_edge_ranges
      [OF run sound pre P_reaches child_cost_bounds M_cap source_factor k_pos])
  have "c \<le> A * Suc L * card U + R * card (outgoing_edges U) +
      H * card (outgoing_edges U)"
    using loop edge_budget by linarith
  also have "\<dots> = A * Suc L * card U + (R + H) * card (outgoing_edges U)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem exact_split_range_costed_nonbase_step_closes_level_bound_from_child_bound_with_invariants_and_edge_budget:
  assumes loop:
    "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U_loop c_loop child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and P_k_cap: "k * card P \<le> cap"
    and P_anti: "tree_antichain P"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child;
          k * card S_child \<le> cap;
          tree_antichain S_child\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and M_cap: "M_of l \<le> cap"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
    and edge_budget:
      "t * sum_list (map card (range_tree_child_edge_range_list P a betas bs)) \<le>
        H * card (outgoing_edges U_loop)"
    and U_def: "U = U_loop \<union> W"
    and finite_U: "finite U"
    and scan_insert: "c_scan_insert \<le> A * card U"
    and c_def: "c = c_scan_insert + c_loop"
  shows "c \<le> A * Suc (Suc L) * card U + (R + H) * card (outgoing_edges U)"
proof -
  have loop_bound:
    "c_loop \<le> A * Suc L * card U_loop +
      (R + H) * card (outgoing_edges U_loop)"
    by (rule exact_split_range_costed_partition_loop_state_closes_level_bound_from_child_bound_with_invariants_and_edge_budget
      [OF loop sound pre P_reaches P_k_cap P_anti child_bound M_cap
        source_factor k_pos edge_budget])
  have U_loop_subset: "U_loop \<subseteq> U"
    using U_def by blast
  have card_loop_le: "card U_loop \<le> card U"
    by (rule card_mono[OF finite_U U_loop_subset])
  have outgoing_subset: "outgoing_edges U_loop \<subseteq> outgoing_edges U"
    by (rule outgoing_edges_mono[OF U_loop_subset])
  have finite_out_U: "finite (outgoing_edges U)"
    by simp
  have card_out_le:
    "card (outgoing_edges U_loop) \<le> card (outgoing_edges U)"
    by (rule card_mono[OF finite_out_U outgoing_subset])
  have "c \<le>
      A * card U +
      (A * Suc L * card U + (R + H) * card (outgoing_edges U))"
  proof -
    have loop_to_U:
      "c_loop \<le> A * Suc L * card U +
        (R + H) * card (outgoing_edges U)"
    proof -
      have "A * Suc L * card U_loop \<le> A * Suc L * card U"
        using card_loop_le by simp
      moreover have "(R + H) * card (outgoing_edges U_loop) \<le>
          (R + H) * card (outgoing_edges U)"
        using card_out_le by simp
      ultimately show ?thesis
        using loop_bound by linarith
    qed
    show ?thesis
      using scan_insert loop_to_U c_def by linarith
  qed
  also have "\<dots> =
      A * Suc (Suc L) * card U + (R + H) * card (outgoing_edges U)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem exact_split_range_costed_bmssp_level_bound_from_local_budgets_with_invariants_and_edge_budget:
  assumes base_budget: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
    and M_cap: "\<And>i. i \<le> l \<Longrightarrow> M_of i \<le> cap"
    and edge_budget:
      "\<And>l d P B d' D a betas bs B' Us U c child_costs.
        exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
          betas bs B' Us U c child_costs \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d P B \<Longrightarrow>
        (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
        t * sum_list (map card (range_tree_child_edge_range_list P a betas bs))
          \<le> H * card (outgoing_edges U)"
    and step_budget:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
          Us U_loop c_loop child_costs \<Longrightarrow>
        complete_on d'
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        U = U_loop \<union>
          {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B) \<Longrightarrow>
        k * card S \<le> cap \<Longrightarrow>
        tree_antichain S \<Longrightarrow>
        fp_iter_capped_scan_cost k cap d S S B + c_insert \<le> A * card U"
    and run:
      "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and S_k_cap: "k * card S \<le> cap"
    and S_anti: "tree_antichain S"
  shows "c \<le> level_range_cost_bound A (R + l * H) (2 * l + 1) U"
  using run sound pre S_reaches below S_k_cap S_anti M_cap
proof (induction l arbitrary: d S B d' B' U c rule: less_induct)
  case (less l)
  show ?case
  proof (cases l)
    case 0
    have run0:
      "exact_split_range_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
      using less.prems(1) 0 by simp
    have split_run0:
      "split_range_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
      using exact_split_range_costed_refines_split_range_costed(2)[OF run0] .
    show ?thesis
      using split_run0 R_pos 0
      by (cases rule: split_range_costed_bmssp.cases)
        (simp_all add: split_range_costed_base_level_bound)
  next
    case (Suc l0)
    have run_suc:
      "exact_split_range_costed_bmssp \<Delta> M_of t h k cap (Suc l0) d S B d' B' U c"
      using less.prems(1) Suc by simp
    show ?thesis
    proof (cases rule: exact_split_range_costed_bmssp_SucE[OF run_suc])
      case (1 c_insert a betas bs Us U_loop c_loop child_costs_loop)
      let ?d_fp = "find_pivots_label_capped k cap d S B"
      let ?P = "find_pivots_pivots_capped k cap d S B"
      let ?W = "{v \<in> bound_tree S B'. ?d_fp v = dist s v}"
      have sound_fp: "sound_label ?d_fp"
        unfolding find_pivots_label_capped_def
        by (rule fp_iter_capped_label_sound[OF less.prems(2) less.prems(4)])
      have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
        using find_pivots_capped_establishes_pivot_pre_concrete
          [OF less.prems(2) less.prems(3) less.prems(4)] .
      have S_subset: "S \<subseteq> V"
        using less.prems(3) unfolding bmssp_pre_full_def by blast
      have P_subset_S: "?P \<subseteq> S"
        unfolding find_pivots_pivots_capped_def by (auto split: if_splits)
      have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
        using P_subset_S less.prems(4) by blast
      have P_k_cap: "k * card ?P \<le> cap"
        by (rule find_pivots_pivots_capped_scaled_card_le
          [OF S_subset less.prems(6)])
      have P_anti: "tree_antichain ?P"
        by (rule find_pivots_pivots_capped_tree_antichain[OF less.prems(7)])
      have child_bound:
        "\<And>c_child U_child S_child B_child d_child B_child'.
          \<lbrakk>exact_split_range_costed_bmssp \<Delta> M_of t h k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child;
            bmssp_pre_full ?d_fp S_child B_child;
            \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
            card S_child \<le> M_of l0;
            \<And>x. x \<in> S_child \<Longrightarrow> below_bound (?d_fp x) B_child;
            k * card S_child \<le> cap;
            tree_antichain S_child\<rbrakk>
          \<Longrightarrow> c_child \<le> level_range_cost_bound A (R + l0 * H)
            (2 * l0 + 1) U_child"
      proof -
        fix c_child U_child S_child B_child d_child B_child'
        assume child:
            "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child"
          and child_pre: "bmssp_pre_full ?d_fp S_child B_child"
          and child_reaches: "\<And>x. x \<in> S_child \<Longrightarrow> reachable s x"
          and child_below:
            "\<And>x. x \<in> S_child \<Longrightarrow> below_bound (?d_fp x) B_child"
          and child_k_cap: "k * card S_child \<le> cap"
          and child_anti: "tree_antichain S_child"
        have M_cap_child: "\<And>i. i \<le> l0 \<Longrightarrow> M_of i \<le> cap"
          using less.prems(8) Suc by simp
        show "c_child \<le> level_range_cost_bound A (R + l0 * H)
            (2 * l0 + 1) U_child"
          by (rule less.IH[of l0 ?d_fp S_child B_child d_child B_child'
                U_child c_child, OF _ child sound_fp child_pre child_reaches
                child_below child_k_cap child_anti M_cap_child])
            (simp add: Suc)
      qed
      have loop_edge_budget:
        "t * sum_list (map card (range_tree_child_edge_range_list ?P a betas bs))
          \<le> H * card (outgoing_edges U_loop)"
        by (rule edge_budget[OF 1(4) sound_fp pivot_pre P_reaches])
      have scan_insert:
        "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
          A * card U"
        by (rule step_budget[OF refl 1(3) 1(4) 1(5) 1(1)
            less.prems(2) less.prems(3) less.prems(4) less.prems(5)
            less.prems(6) less.prems(7)])
      have trace:
        "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
      proof -
        have split_loop:
          "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l0
            ?d_fp ?P B d'
            (label_partition_view ?d_fp ?P) a betas bs B' Us U_loop c_loop
            child_costs_loop"
          using exact_split_range_costed_refines_split_range_costed(1)[OF 1(4)]
            by simp
        show ?thesis
          by (rule split_range_costed_partition_loop_state_trace
            [OF split_loop sound_fp pivot_pre P_reaches])
      qed
      have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
        by (rule concrete_partition_loop_trace_post[OF trace])
      have finite_U_loop: "finite U_loop"
        using loop_post unfolding bmssp_post_full_def by simp
      have finite_W: "finite ?W"
        by simp
      have finite_U: "finite U"
        using 1(1) finite_U_loop finite_W by simp
      have M_cap_l0: "M_of l0 \<le> cap"
        using less.prems(8) Suc by simp
      have step:
        "c \<le> A * Suc (Suc (2 * l0 + 1)) * card U +
          (R + l0 * H + H) * card (outgoing_edges U)"
        by (rule exact_split_range_costed_nonbase_step_closes_level_bound_from_child_bound_with_invariants_and_edge_budget
          [OF 1(4) sound_fp pivot_pre P_reaches P_k_cap P_anti child_bound
            M_cap_l0 source_factor k_pos loop_edge_budget 1(1) finite_U
            scan_insert 1(2)])
      show ?thesis
        using step Suc unfolding level_range_cost_bound_def
        by (simp add: algebra_simps)
    qed
  qed
qed

theorem finite_initial_label_exact_split_range_costed_top_level_correct_and_closed_refined_graph_bound_level_cap:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and edge_budget:
      "\<And>l' d P B d' D a betas bs B' Us U_loop c_loop child_costs.
        exact_split_range_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
          (bmssp_level_cap k t l) l' d P B d' D a betas bs B'
          Us U_loop c_loop child_costs \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d P B \<Longrightarrow>
        (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
        t * sum_list (map card (range_tree_child_edge_range_list P a betas bs))
          \<le> H * card (outgoing_edges U_loop)"
    and run:
      "exact_split_range_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * H) * edge_count"
proof
  show "sssp_correct d'"
    by (rule finite_initial_label_exact_split_range_costed_top_level_correct
      [OF all_reachable run])
next
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  have below: "\<And>x. x \<in> {s} \<Longrightarrow>
      below_bound (finite_initial_label x) Infinity"
    by simp
  have top_cap: "k * card {s} \<le> bmssp_level_cap k t l"
  proof -
    have one_le: "1 \<le> bmssp_level_width t l"
      unfolding bmssp_level_width_def by simp
    have "k * 1 \<le> k * bmssp_level_width t l"
      by (rule mult_left_mono[OF one_le]) simp
    then show ?thesis
      unfolding bmssp_level_cap_def by simp
  qed
  have top_anti: "tree_antichain {s}"
    by simp
  have range_bound:
    "c \<le> level_range_cost_bound (2 * A) (R + l * H) (2 * l + 1) U"
  proof (rule exact_split_range_costed_bmssp_level_bound_from_local_budgets_with_invariants_and_edge_budget
      [where A = "2 * A" and R = R and H = H,
        OF _ R_pos source_factor k_pos _ _ _ run sound pre S_reaches below
          top_cap top_anti])
    show "\<Delta> \<le> 2 * A"
      using degree_factor by simp
  next
    fix i
    assume "i \<le> l"
    then show "bmssp_level_cap k t i \<le> bmssp_level_cap k t l"
      by (rule bmssp_level_cap_mono)
  next
    fix l' d P B d' D a betas bs B' Us U_loop c_loop child_costs
    assume loop:
        "exact_split_range_costed_partition_loop_state \<Delta>
          (bmssp_level_cap k t) t h k (bmssp_level_cap k t l) l'
          d P B d' D a betas bs B' Us U_loop c_loop child_costs"
      and sound_l: "sound_label d"
      and pre_l: "bmssp_pre_full d P B"
      and reaches_l: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    show "t * sum_list (map card (range_tree_child_edge_range_list P a betas bs))
        \<le> H * card (outgoing_edges U_loop)"
      by (rule edge_budget[OF loop sound_l pre_l reaches_l])
  next
    fix l' d S B D c_insert d' a betas bs B' Us U_loop c_loop child_costs U
    assume D_def:
        "D = label_partition_view
          (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B)"
      and insert:
        "partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B)"
      and loop:
        "exact_split_range_costed_partition_loop_state \<Delta>
          (bmssp_level_cap k t) t h k (bmssp_level_cap k t l) l'
          (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) B d' D
          a betas bs B' Us U_loop c_loop child_costs"
      and complete:
        "complete_on d'
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
              dist s v}"
      and U_def:
        "U = U_loop \<union>
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
              dist s v}"
      and sound_s: "sound_label d"
      and pre_s: "bmssp_pre_full d S B"
      and reaches_s: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
      and below_s: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
      and S_k_cap: "k * card S \<le> bmssp_level_cap k t l"
      and anti: "tree_antichain S"
    have split_loop:
      "split_range_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l'
        (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
        (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) B d' D
        a betas bs B' Us U_loop c_loop child_costs"
      by (rule exact_split_range_costed_refines_split_range_costed(1)[OF loop])
    have seen_success:
      "B' = B \<Longrightarrow>
        card (find_pivots_seen_capped k (bmssp_level_cap k t l) d S B)
        \<le> card U"
      by (rule exact_split_range_costed_step_seen_success
        [OF loop U_def sound_s pre_s reaches_s below_s])
    show "fp_iter_capped_scan_cost k (bmssp_level_cap k t l) d S S B +
        c_insert \<le> 2 * A * card U"
      by (rule split_range_costed_capped_step_scan_insert_budget_from_scaled_seen_or_threshold
        [OF degree degree_factor insert_factor insert_scaled_factor
          seen_scaled_factor insert split_loop U_def sound_s pre_s reaches_s
          S_k_cap anti k_pos seen_success])
  qed
  have post_full:
    "bmssp_post_full finite_initial_label {s} Infinity d' Infinity U"
    by (rule exact_split_range_costed_bmssp_correct[OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  have U_V: "U = V"
    using post bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  have graph_bound:
    "level_range_cost_bound (2 * A) (R + l * H) (2 * l + 1) U
      \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * H) * edge_count"
  proof -
    have U_card: "card U = vertex_count"
      unfolding U_V vertex_count_def by simp
    have out_le: "card (outgoing_edges U) \<le> edge_count"
      by (rule edge_count_outgoing_bound)
    have out_term:
      "(R + l * H) * card (outgoing_edges U) \<le> (R + l * H) * edge_count"
      using out_le by simp
    show ?thesis
      unfolding level_range_cost_bound_def
      using U_card out_term by (simp add: algebra_simps)
  qed
  show "c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * H) * edge_count"
    using range_bound graph_bound by linarith
qed

corollary finite_initial_label_exact_split_range_costed_top_level_correct_and_closed_bmssp_refined_graph_time_bound_level_cap:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and edge_budget:
      "\<And>l' d P B d' D a betas bs B' Us U_loop c_loop child_costs.
        exact_split_range_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
          (bmssp_level_cap k t l) l' d P B d' D a betas bs B'
          Us U_loop c_loop child_costs \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d P B \<Longrightarrow>
        (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
        t * sum_list (map card (range_tree_child_edge_range_list P a betas bs))
          \<le> H * card (outgoing_edges U_loop)"
    and run:
      "exact_split_range_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. H)
      (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
proof -
  have graph:
    "sssp_correct d' \<and>
      c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * H) * edge_count"
    by (rule finite_initial_label_exact_split_range_costed_top_level_correct_and_closed_refined_graph_bound_level_cap
      [OF all_reachable degree degree_factor R_pos insert_factor insert_scaled_factor
        seen_scaled_factor source_factor k_pos edge_budget run])
  have bound:
    "2 * A * (2 * l + 1) * vertex_count + (R + l * H) * edge_count
      \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. H)
        (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
    unfolding bmssp_refined_graph_time_bound_def by simp
  show ?thesis
    using graph bound by linarith
qed

corollary finite_initial_label_exact_split_range_costed_top_level_correct_and_closed_bmssp_refined_graph_time_bound_level_cap_trivial_edge_budget:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and run:
      "exact_split_range_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. t)
      (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
proof (rule finite_initial_label_exact_split_range_costed_top_level_correct_and_closed_bmssp_refined_graph_time_bound_level_cap
    [OF all_reachable degree degree_factor R_pos insert_factor insert_scaled_factor
      seen_scaled_factor source_factor k_pos _ run])
  fix l' d P B d' D a betas bs B' Us U_loop c_loop child_costs
  assume loop:
      "exact_split_range_costed_partition_loop_state \<Delta>
        (bmssp_level_cap k t) t h k (bmssp_level_cap k t l) l'
        d P B d' D a betas bs B' Us U_loop c_loop child_costs"
    and sound_l: "sound_label d"
    and pre_l: "bmssp_pre_full d P B"
    and reaches_l: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
  show "t * sum_list (map card (range_tree_child_edge_range_list P a betas bs))
      \<le> t * card (outgoing_edges U_loop)"
    by (rule exact_split_range_costed_partition_loop_state_trivial_edge_budget
      [OF loop sound_l pre_l reaches_l])
qed

end

end
