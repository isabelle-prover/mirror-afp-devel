theory BMSSP_Operational_Pull
  imports BMSSP_Partition_Pull_Bridge BMSSP_Recursive
begin

section \<open>Operational Pull Step\<close>

text \<open>
  This theory is the bridge from the abstract recursive BMSSP specification to
  an operational loop that explicitly pulls a bounded prefix out of a partition,
  recurses on that prefix, and then pushes newly discovered labels into the
  remaining partition.  Earlier theories prove the abstract correctness theorem
  for \<open>concrete_bmssp\<close>; here we expose the loop shape that the later cost
  relations charge.

  The paper's partition loop is not merely a list traversal.  Each iteration
  selects a child source set below a temporary bound, runs BMSSP recursively on
  that child problem, and then refreshes the parent partition with two kinds of
  labels: edge relaxations out of the completed child tree and old source labels
  that now fall into the open range just processed.  The predicate
  \<open>pull_separates\<close> is the abstract statement that the pull operation has
  found exactly such a prefix and retained an ordered residual partition.

  The main proof obligation is a lifting argument.  If a child recursive call
  satisfies \<open>bmssp_post_full\<close> for the split prefix, and if the parent
  already satisfied \<open>bmssp_pre_full\<close> up to the larger bound, then the
  child result can be viewed as progress for the parent.  The connective tissue
  is the lower split \<open>split_below\<close>: it identifies the prefix chosen by
  the data structure with the mathematical set of vertices whose current labels
  are below the recursive child bound.

  Later in the file the same idea is rephrased as inductive operational traces.
  The traces remember the sequence of child output bounds, the range trees
  \<open>range_tree\<close> that those bounds cut out, and the final tree assembled
  from all slices.  This is the form needed by the range-synchronised cost
  theories, where every loop iteration must be charged to the slice it actually
  completed.
\<close>

context unique_shortest_digraph
begin

theorem sorted_pull_recursive_child_lifts:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S (Fin Bmax)"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and upper: "\<And>u. u \<in> S \<Longrightarrow> d u < Bmax"
    and S'_def: "S' = sorted_pull_set M (label_partition_view d S)"
    and beta_def: "beta = sorted_pull_bound M Bmax (label_partition_view d S)"
    and run: "concrete_bmssp k cap l d S' (Fin beta) d' B' U"
  shows "bmssp_post_full d S (Fin Bmax) d' B' U"
proof -
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have finite_S: "finite S"
    using finite_subset[OF S_subset finite_V] .
  let ?D = "label_partition_view d S"
  let ?xs = "partition_key_order ?D"
  have set_xs: "set ?xs = S"
    using partition_key_order_properties(1)[of ?D] finite_S by simp
  have child_pre: "bmssp_pre_full d S' (Fin beta)"
    by (rule sorted_pull_establishes_lower_pre
      [OF pre upper refl S'_def beta_def])
  have S'_split: "S' = split_below d S beta"
    using sorted_pull_set_eq_split_below[OF finite_S upper refl beta_def]
    unfolding S'_def .
  have S'_reaches: "\<And>x. x \<in> S' \<Longrightarrow> reachable s x"
    using S_reaches S'_split unfolding split_below_def by blast
  have child_post: "bmssp_post_full d S' (Fin beta) d' B' U"
    by (rule concrete_bmssp_correct[OF sound child_pre S'_reaches run])
  have beta_le: "beta \<le> Bmax"
  proof (cases "length ?xs \<le> M")
    case True
    then show ?thesis
      unfolding beta_def sorted_pull_bound_def by (simp add: Let_def)
  next
    case False
    then have M_lt: "M < length ?xs"
      by simp
    have beta_eq: "beta = d (?xs ! M)"
      using False unfolding beta_def sorted_pull_bound_def by (simp add: Let_def)
    have "?xs ! M \<in> S"
      using set_xs M_lt nth_mem by metis
    then have "beta < Bmax"
      using upper beta_eq by simp
    then show ?thesis
      by simp
  qed
  have pre_beta: "bmssp_pre_full d S (Fin beta)"
    using bmssp_pre_full_bound_mono[OF pre, of "Fin beta"] beta_le by simp
  have cover_beta: "complete_tree_cover d S (Fin beta)"
    using bmssp_pre_full_complete_tree_cover[OF pre_beta] .
  have child_post_split:
    "bmssp_post_full d (split_below d S beta) (Fin beta) d' B' U"
    using child_post unfolding S'_split .
  have U_tree: "U = bound_tree S B'"
    using pull_recursive_post_lifts_bound_tree[OF cover_beta child_post_split] .
  have le_child: "bound_le B' (Fin beta)"
    using child_post unfolding bmssp_post_full_def by blast
  have le_parent: "bound_le B' (Fin Bmax)"
    using le_child beta_le by (cases B') auto
  have complete: "complete_on d' U"
    using child_post unfolding bmssp_post_full_def by blast
  show ?thesis
    using le_parent U_tree complete unfolding bmssp_post_full_def by blast
qed

theorem pull_separates_recursive_child_lifts:
  fixes Bmax :: real
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S (Fin Bmax)"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and upper: "\<And>u. u \<in> S \<Longrightarrow> d u < Bmax"
    and pull: "pull_separates (label_partition_view d S) M Bmax S' beta D'"
    and run: "concrete_bmssp k cap l d S' (Fin beta) d' B' U"
  shows "bmssp_post_full d S (Fin Bmax) d' B' U"
proof -
  have S'_split: "S' = split_below d S beta"
    using pull_separates_label_set_eq_split_below[OF pull upper] .
  have S'_subset: "S' \<subseteq> S"
    using pull_separates_subset[OF pull] by simp
  have beta_le: "beta \<le> Bmax"
  proof (cases "keys_of D' = {}")
    case True
    then show ?thesis
      using pull_separates_empty_bound[OF pull True] by simp
  next
    case False
    then obtain v where vD': "v \<in> keys_of D'"
      by blast
    have D'_keys: "keys_of D' = S - S'"
      using pull unfolding pull_separates_def by simp
    then have vS: "v \<in> S"
      using vD' by blast
    have "beta \<le> value_of D' v"
      by (rule pull_separates_nonempty_bound[OF pull False vD'])
    also have "\<dots> = d v"
      using pull unfolding pull_separates_def by simp
    also have "\<dots> < Bmax"
      using upper[OF vS] .
    finally show ?thesis
      by simp
  qed
  have child_pre: "bmssp_pre_full d S' (Fin beta)"
  proof (cases "beta = Bmax")
    case True
    have split_all: "split_below d S beta = S"
      unfolding split_below_def True using upper by blast
    show ?thesis
      using pre S'_split split_all True by simp
  next
    case False
    then have beta_lt: "beta < Bmax"
      using beta_le by simp
    have "bmssp_pre_full d (split_below d S beta) (Fin beta)"
      by (rule pull_minimum_pre_for_lower_split[OF pre]) (simp add: beta_lt)
    then show ?thesis
      using S'_split by simp
  qed
  have S'_reaches: "\<And>x. x \<in> S' \<Longrightarrow> reachable s x"
    using S'_subset S_reaches by blast
  have child_post: "bmssp_post_full d S' (Fin beta) d' B' U"
    by (rule concrete_bmssp_correct[OF sound child_pre S'_reaches run])
  have pre_beta: "bmssp_pre_full d S (Fin beta)"
  proof -
    have "bound_le (Fin beta) (Fin Bmax)"
      using beta_le by simp
    then show ?thesis
      by (rule bmssp_pre_full_bound_mono[OF pre])
  qed
  have cover_beta: "complete_tree_cover d S (Fin beta)"
    using bmssp_pre_full_complete_tree_cover[OF pre_beta] .
  have child_post_split:
    "bmssp_post_full d (split_below d S beta) (Fin beta) d' B' U"
    using child_post S'_split by simp
  have U_tree: "U = bound_tree S B'"
    using pull_recursive_post_lifts_bound_tree[OF cover_beta child_post_split] .
  have le_child: "bound_le B' (Fin beta)"
    using child_post unfolding bmssp_post_full_def by blast
  have le_parent: "bound_le B' (Fin Bmax)"
    using le_child beta_le by (cases B') auto
  have complete: "complete_on d' U"
    using child_post unfolding bmssp_post_full_def by blast
  show ?thesis
    using le_parent U_tree complete unfolding bmssp_post_full_def by blast
qed

text \<open>
  The first two lifting lemmas isolate the correctness content of a pull.  The
  theorem @{thm sorted_pull_recursive_child_lifts} is phrased for the executable
  sorted-list partition view: the child set and child bound are computed by
  sorting labels and taking the first \<open>M\<close> positions.  The theorem
  @{thm pull_separates_recursive_child_lifts} is the abstract version used by
  the bucketed partition and by the costed loop relations.

  Both statements follow the same pattern.  The pulled set is shown to equal
  the mathematical split below the child bound, the child precondition is
  inherited from the parent precondition, and the child postcondition is lifted
  through the parent's complete tree cover.  The conclusion deliberately
  reuses @{const bmssp_post_full}; nothing about the later operational or costed
  presentation changes the semantic contract of BMSSP.
\<close>

definition complete_preserved where
  "complete_preserved d d' U \<longleftrightarrow> (complete_on d U \<longrightarrow> complete_on d' U)"

lemma relax_edges_complete_preserved:
  assumes sound: "sound_label d"
    and edges: "\<And>u v. (u, v) \<in> set es \<Longrightarrow> (u, v) \<in> E"
    and reaches: "\<And>u v. (u, v) \<in> set es \<Longrightarrow> reachable s u"
  shows "complete_preserved d (relax_edges d es) U"
proof -
  have preserve: "\<And>x. d x = dist s x \<Longrightarrow> relax_edges d es x = dist s x"
  proof -
    fix x
    assume complete_x: "d x = dist s x"
    show "relax_edges d es x = dist s x"
      by (rule relax_edges_preserves_complete_sound
        [OF sound complete_x edges reaches])
  qed
  show ?thesis
    unfolding complete_preserved_def complete_on_def using preserve by blast
qed

lemma relax_frontier_complete_preserved:
  assumes sound: "sound_label d"
    and reaches: "\<And>u. u \<in> F \<Longrightarrow> reachable s u"
  shows "complete_preserved d (relax_frontier d F) U"
proof -
  have preserve: "\<And>x. d x = dist s x \<Longrightarrow> relax_frontier d F x = dist s x"
  proof -
    fix x
    assume complete_x: "d x = dist s x"
    show "relax_frontier d F x = dist s x"
      by (rule relax_frontier_preserves_complete_sound
        [OF sound complete_x reaches])
  qed
  show ?thesis
    unfolding complete_preserved_def complete_on_def using preserve by blast
qed

text \<open>
  After a child call returns, the parent loop relaxes edges out of the completed
  child tree and may also reinsert source labels from the pulled set.  The small
  predicate @{const complete_preserved} packages the only semantic requirement
  imposed on that refresh: labels already complete on the child slice stay
  complete after the refresh.

  The lemmas @{thm relax_edges_complete_preserved} and
  @{thm relax_frontier_complete_preserved} are deliberately local and modest.
  They do not prove a new shortest-path theorem; they just record that ordinary
  sound relaxation cannot destroy a vertex whose label has already reached its
  true distance.  This lets the loop proofs compose recursive completion with
  parent-side batch updates without reopening the relaxation algebra every time.
\<close>

definition edge_relaxation_pairs_between where
  "edge_relaxation_pairs_between d U L H =
    map (\<lambda>(u, v). (v, d u + w u v))
      (filter (\<lambda>(u, v). L \<le> d u + w u v \<and> d u + w u v < H)
        (edge_list_of (outgoing_edges U)))"

definition label_pairs_between where
  "label_pairs_between d S L H =
    map (\<lambda>x. (x, d x))
      (filter (\<lambda>x. L \<le> d x \<and> d x < H)
        (partition_key_order (label_partition_view d S)))"

lemma edge_relaxation_pairs_between_value_le_high:
  assumes "(x, b) \<in> set (edge_relaxation_pairs_between d U L H)"
  shows "b \<le> H"
  using assms unfolding edge_relaxation_pairs_between_def
  by (auto split: prod.splits)

lemma edge_relaxation_pairs_between_value_ge_low:
  assumes "(x, b) \<in> set (edge_relaxation_pairs_between d U L H)"
  shows "L \<le> b"
  using assms unfolding edge_relaxation_pairs_between_def
  by (auto split: prod.splits)

lemma label_pairs_between_value_le_high:
  assumes "(x, b) \<in> set (label_pairs_between d S L H)"
  shows "b \<le> H"
  using assms unfolding label_pairs_between_def by auto

lemma label_pairs_between_value_ge_low:
  assumes "(x, b) \<in> set (label_pairs_between d S L H)"
  shows "L \<le> b"
  using assms unfolding label_pairs_between_def by auto

lemma edge_relaxation_pairs_between_length_le_outgoing:
  "length (edge_relaxation_pairs_between d U L H) \<le>
    card (outgoing_edges U)"
proof -
  let ?es = "edge_list_of (outgoing_edges U)"
  have distinct_es: "distinct ?es"
    using edge_list_of_properties(2)[OF finite_outgoing_edges] .
  have length_es: "length ?es = card (outgoing_edges U)"
    using edge_list_of_properties(1)[OF finite_outgoing_edges] distinct_es
    by (metis distinct_card)
  have "length (edge_relaxation_pairs_between d U L H) \<le> length ?es"
    unfolding edge_relaxation_pairs_between_def by simp
  then show ?thesis
    using length_es by simp
qed

lemma label_pairs_between_length_le_card:
  assumes finite_S: "finite S"
  shows "length (label_pairs_between d S L H) \<le> card S"
proof -
  let ?xs = "partition_key_order (label_partition_view d S)"
  have set_xs: "set ?xs = S"
    using partition_key_order_properties(1)[of "label_partition_view d S"]
      finite_S by simp
  have distinct_xs: "distinct ?xs"
    using partition_key_order_properties(2)[of "label_partition_view d S"]
      finite_S by simp
  have length_xs: "length ?xs = card S"
    using set_xs distinct_xs by (metis distinct_card)
  have "length (label_pairs_between d S L H) \<le> length ?xs"
    unfolding label_pairs_between_def by simp
  then show ?thesis
    using length_xs by simp
qed

theorem pull_separates_batch_prepend_for_relaxation_pairs:
  assumes pull: "pull_separates D M B S_pull beta D'"
  shows "batch_prepend_admissible D'
    (edge_relaxation_pairs_between d U L beta @ label_pairs_between d S L beta)"
proof (rule pull_separates_batch_prepend_admissible[OF pull])
  fix x b
  assume "(x, b) \<in> set
    (edge_relaxation_pairs_between d U L beta @ label_pairs_between d S L beta)"
  then show "b \<le> beta"
    using edge_relaxation_pairs_between_value_le_high
      label_pairs_between_value_le_high by auto
qed

text \<open>
  The two batch constructors separate the sources of new partition entries.
  @{const edge_relaxation_pairs_between} enumerates outgoing child-tree edges
  whose relaxed values lie in the current open range, while
  @{const label_pairs_between} keeps old source labels that also lie in that
  range.  The length lemmas above connect these lists to the quantities charged
  later: outgoing edges for the first list and source cardinality for the
  second.

  The admissibility theorem
  @{thm pull_separates_batch_prepend_for_relaxation_pairs} is the key local
  invariant for pushing the batch into the residual partition.  It says
  that every generated value is still below the bound exposed by the pull, so
  the residual ordered partition can accept the batch without invalidating the
  next pull.
\<close>

lemma range_tree_same_empty [simp]:
  "range_tree S a (Fin a) = {}"
  unfolding range_tree_def by auto

text \<open>
  The relation below is the first operational presentation of the parent loop.
  It abstracts away the concrete partition representation, but it records the
  same sequence of events as the algorithm: stop when the lower bound has
  already produced enough completed vertices, otherwise recurse on the split
  prefix, preserve completion through the parent refresh, and continue from the
  child output bound.

  The lists \<open>betas\<close>, \<open>bs\<close>, and \<open>Us\<close> are not auxiliary clutter.  They are
  the trace that later cost proofs consume.  The child output bounds \<open>bs\<close>
  determine adjacent range slices, and each stored set in \<open>Us\<close> is identified
  with the corresponding @{const range_tree}.  Proving this trace property once
  keeps the later runtime arguments independent of the details of the recursive
  correctness proof.
\<close>

inductive operational_partition_loop where
  Done:
    "bound_le (Fin a) B \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     operational_partition_loop k cap l d P B d' a [] [] (Fin a)
       [range_tree P a (Fin a)]
       (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a (Fin a)]))"
| Step:
    "below_bound beta B \<Longrightarrow>
     a \<le> b \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     concrete_bmssp k cap l d (split_below d P beta) (Fin beta)
       d_child (Fin b) U_child \<Longrightarrow>
     complete_preserved d_child d' U_child \<Longrightarrow>
     operational_partition_loop k cap l d P B d' b betas bs B' Us_tail U_tail \<Longrightarrow>
     operational_partition_loop k cap l d P B d' a (beta # betas) (b # bs) B'
       (range_tree P a (Fin b) # Us_tail)
       (bound_tree P (Fin a) \<union> \<Union>(set (range_tree P a (Fin b) # Us_tail)))"

theorem operational_partition_loop_trace:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and loop: "operational_partition_loop k cap l d P B d' a betas bs B' Us U"
  shows "concrete_partition_loop_trace P B a bs d' B' Us U"
  using loop sound pre P_reaches
proof (induction)
  case (Done a B d' P k cap l d)
  then show ?case
    unfolding concrete_partition_loop_trace_def complete_on_def by simp
next
  case (Step beta B a b d' P k cap l d d_child U_child betas bs B' Us_tail U_tail)
  have beta_le: "bound_le (Fin beta) B"
    using Step.hyps(1) by (cases B) auto
  have pre_beta: "bmssp_pre_full d P (Fin beta)"
    using bmssp_pre_full_bound_mono[OF Step.prems(2) beta_le] .
  have child_pre: "bmssp_pre_full d (split_below d P beta) (Fin beta)"
    using pull_minimum_pre_for_lower_split[OF Step.prems(2) Step.hyps(1)] .
  have child_reaches:
    "\<And>x. x \<in> split_below d P beta \<Longrightarrow> reachable s x"
    using Step.prems(3) unfolding split_below_def by blast
  have child_post:
    "bmssp_post_full d (split_below d P beta) (Fin beta)
      d_child (Fin b) U_child"
    by (rule concrete_bmssp_correct[OF Step.prems(1) child_pre child_reaches Step.hyps(4)])
  have cover_beta: "complete_tree_cover d P (Fin beta)"
    using bmssp_pre_full_complete_tree_cover[OF pre_beta] .
  have U_child_tree: "U_child = bound_tree P (Fin b)"
    using pull_recursive_post_lifts_bound_tree[OF cover_beta child_post] .
  have child_complete: "complete_on d_child U_child"
    using child_post unfolding bmssp_post_full_def by blast
  have child_complete_final: "complete_on d' U_child"
    using Step.hyps(5) child_complete unfolding complete_preserved_def by blast
  have head_complete: "complete_on d' (range_tree P a (Fin b))"
  proof -
    have "range_tree P a (Fin b) \<subseteq> U_child"
      using U_child_tree range_tree_subset_bound_tree[of P a "Fin b"] by simp
    then show ?thesis
      using complete_on_subset[OF child_complete_final] by blast
  qed
  have tail_trace:
    "concrete_partition_loop_trace P B b bs d' B' Us_tail U_tail"
    using Step.IH[OF Step.prems(1) Step.prems(2) Step.prems(3)] .
  have tail_le: "bound_le B' B"
    and tail_mono: "nondecreasing_from b bs"
    and tail_bounds: "bounds_le B' (b # bs)"
    and tail_children:
      "list_all2 (\<lambda>U X. U = X \<and> complete_on d' U) Us_tail
        (range_tree_chain_list P b bs B')"
    using tail_trace unfolding concrete_partition_loop_trace_def by blast+
  have a_bound: "bound_le (Fin a) B'"
  proof -
    have "bound_le (Fin b) B'"
      using tail_bounds by simp
    then show ?thesis
      using Step.hyps(2) by (cases B') auto
  qed
  show ?case
    unfolding concrete_partition_loop_trace_def
    using tail_le Step.hyps(2) tail_mono tail_bounds a_bound
      Step.hyps(3) head_complete tail_children
    by auto
qed

definition operational_capped_bmssp_step where
  "operational_capped_bmssp_step k cap l d S B a betas bs d' B' Us U \<longleftrightarrow>
     (let d_fp = find_pivots_label_capped k cap d S B;
          P = find_pivots_pivots_capped k cap d S B;
          W = {v \<in> bound_tree S B'. d_fp v = dist s v}
      in \<exists>U_loop.
           operational_partition_loop k cap l d_fp P B d' a betas bs B' Us U_loop \<and>
           complete_on d' W \<and>
           U = U_loop \<union> W)"

theorem operational_capped_bmssp_step_correct:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and step: "operational_capped_bmssp_step k cap l d S B a betas bs d' B' Us U"
  shows "bmssp_post_full d S B d' B' U"
proof -
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  let ?W = "{v \<in> bound_tree S B'. ?d_fp v = dist s v}"
  obtain U_loop where
    loop: "operational_partition_loop k cap l ?d_fp ?P B d' a betas bs B' Us U_loop"
    and compW: "complete_on d' ?W"
    and U: "U = U_loop \<union> ?W"
    using step unfolding operational_capped_bmssp_step_def by (auto simp: Let_def)
  have sound_fp: "sound_label ?d_fp"
    unfolding find_pivots_label_capped_def
    by (rule fp_iter_capped_label_sound[OF sound S_reaches])
  have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
    using find_pivots_capped_establishes_pivot_pre_concrete[OF sound pre S_reaches] .
  have P_subset_S: "?P \<subseteq> S"
    unfolding find_pivots_pivots_capped_def by auto
  have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
    using P_subset_S S_reaches by blast
  have trace: "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
    by (rule operational_partition_loop_trace[OF sound_fp pivot_pre P_reaches loop])
  have concrete_step:
    "concrete_capped_bmssp_step k cap d S B a bs d' B' Us U"
    unfolding concrete_capped_bmssp_step_def
    using trace compW U by (auto simp: Let_def)
  show ?thesis
    by (rule concrete_capped_bmssp_step_correct
      [OF sound pre S_reaches concrete_step])
qed

inductive operational_bmssp where
  Base:
    "S = {x} \<Longrightarrow>
     operational_bmssp k cap 0 d S B
       (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
       (base_case_bound k x B)
       (base_case_vertices k x B)"
| Step:
    "operational_capped_bmssp_step k cap l d S B a betas bs d' B' Us U \<Longrightarrow>
     operational_bmssp k cap (Suc l) d S B d' B' U"

theorem operational_bmssp_correct:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and run: "operational_bmssp k cap l d S B d' B' U"
  shows "bmssp_post_full d S B d' B' U"
  using run sound pre S_reaches
proof (induction arbitrary: rule: operational_bmssp.induct)
  case (Base S x k cap d B)
  have post:
    "bmssp_post d S B
      (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
      (base_case_bound k x B)
      (base_case_vertices k x B)"
    using base_case_result_bmssp_post[OF Base.hyps, where k = k and B = B and d = d]
    unfolding base_case_result_def by simp
  then show ?case
    by (rule bmssp_post_imp_post_full)
next
  case (Step k cap l d S B a betas bs d' B' Us U)
  show ?case
    by (rule operational_capped_bmssp_step_correct
      [OF Step.prems(1) Step.prems(2) Step.prems(3) Step.hyps])
qed

theorem finite_initial_label_operational_top_level_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and run: "operational_bmssp k cap l finite_initial_label {s} Infinity d' Infinity U"
  shows "sssp_correct d'"
proof -
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  have post_full:
    "bmssp_post_full finite_initial_label {s} Infinity d' Infinity U"
    by (rule operational_bmssp_correct[OF sound pre S_reaches run])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  then have U_V: "U = V"
    using bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  have complete: "complete_on d' U"
    using post unfolding bmssp_post_def by auto
  then show ?thesis
    using U_V unfolding complete_on_def sssp_correct_def by auto
qed

text \<open>
  The plain operational relation still calls @{const concrete_bmssp} in each
  loop step.  The full relation below unfolds that recursive call as another
  inductive branch.  This mutual presentation is more verbose, but it gives the
  cost layer a single derivation tree whose nodes are either BMSSP calls or
  partition-loop iterations.

  The theorem @{thm finite_initial_label_operational_top_level_correct} remains
  the semantic endpoint for this layer: starting from the finite initial label
  at the source and an infinite top-level bound, any operational run computes a
  full single-source shortest-path labelling.  The later relations refine this
  one by adding costs and range synchronisation; they do not change this
  correctness statement.
\<close>

inductive full_operational_partition_loop and full_operational_bmssp where
  Full_Loop_Done:
    "bound_le (Fin a) B \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     full_operational_partition_loop k cap l d P B d' a [] [] (Fin a)
       [range_tree P a (Fin a)]
       (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a (Fin a)]))"
| Full_Loop_Step:
    "below_bound beta B \<Longrightarrow>
     a \<le> b \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     full_operational_bmssp k cap l d (split_below d P beta) (Fin beta)
       d_child (Fin b) U_child \<Longrightarrow>
     complete_preserved d_child d' U_child \<Longrightarrow>
     full_operational_partition_loop k cap l d P B d' b betas bs B' Us_tail U_tail \<Longrightarrow>
     full_operational_partition_loop k cap l d P B d' a (beta # betas) (b # bs) B'
       (range_tree P a (Fin b) # Us_tail)
       (bound_tree P (Fin a) \<union> \<Union>(set (range_tree P a (Fin b) # Us_tail)))"
| Full_Loop_Step_Pre:
    "bound_le (Fin beta) B \<Longrightarrow>
     bmssp_pre_full d (split_below d P beta) (Fin beta) \<Longrightarrow>
     a \<le> b \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     full_operational_bmssp k cap l d (split_below d P beta) (Fin beta)
       d_child (Fin b) U_child \<Longrightarrow>
     complete_preserved d_child d' U_child \<Longrightarrow>
     full_operational_partition_loop k cap l d P B d' b betas bs B' Us_tail U_tail \<Longrightarrow>
     full_operational_partition_loop k cap l d P B d' a (beta # betas) (b # bs) B'
       (range_tree P a (Fin b) # Us_tail)
       (bound_tree P (Fin a) \<union> \<Union>(set (range_tree P a (Fin b) # Us_tail)))"
| Full_Base:
    "S = {x} \<Longrightarrow>
     full_operational_bmssp k cap 0 d S B
       (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
       (base_case_bound k x B)
       (base_case_vertices k x B)"
| Full_Step:
    "full_operational_partition_loop k cap l
       (find_pivots_label_capped k cap d S B)
       (find_pivots_pivots_capped k cap d S B) B d' a betas bs B' Us U_loop \<Longrightarrow>
     complete_on d'
       {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
     U = U_loop \<union>
       {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
     full_operational_bmssp k cap (Suc l) d S B d' B' U"

theorem full_operational_partition_loop_trace:
  "full_operational_partition_loop k cap l d P B d' a betas bs B' Us U \<Longrightarrow>
   sound_label d \<Longrightarrow>
   bmssp_pre_full d P B \<Longrightarrow>
   (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
   concrete_partition_loop_trace P B a bs d' B' Us U"
and full_operational_bmssp_correct:
  "full_operational_bmssp k cap l d S B d' B' U \<Longrightarrow>
   sound_label d \<Longrightarrow>
   bmssp_pre_full d S B \<Longrightarrow>
   (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
   bmssp_post_full d S B d' B' U"
proof (induction rule: full_operational_partition_loop_full_operational_bmssp.inducts)
  case (Full_Loop_Done a B d' P k cap l d)
  then show ?case
    unfolding concrete_partition_loop_trace_def complete_on_def by simp
next
  case (Full_Loop_Step beta B a b d' P k cap l d d_child U_child betas bs B' Us_tail U_tail)
  have beta_le: "bound_le (Fin beta) B"
    using Full_Loop_Step(1) by (cases B) auto
  have pre_beta: "bmssp_pre_full d P (Fin beta)"
    using bmssp_pre_full_bound_mono[OF Full_Loop_Step.prems(2) beta_le] .
  have child_pre: "bmssp_pre_full d (split_below d P beta) (Fin beta)"
    using pull_minimum_pre_for_lower_split
      [OF Full_Loop_Step.prems(2) Full_Loop_Step(1)] .
  have child_reaches:
    "\<And>x. x \<in> split_below d P beta \<Longrightarrow> reachable s x"
    using Full_Loop_Step.prems(3) unfolding split_below_def by blast
  have child_post:
    "bmssp_post_full d (split_below d P beta) (Fin beta)
      d_child (Fin b) U_child"
    using Full_Loop_Step.IH Full_Loop_Step.prems(1) child_pre child_reaches
    by blast
  have cover_beta: "complete_tree_cover d P (Fin beta)"
    using bmssp_pre_full_complete_tree_cover[OF pre_beta] .
  have U_child_tree: "U_child = bound_tree P (Fin b)"
    using pull_recursive_post_lifts_bound_tree[OF cover_beta child_post] .
  have child_complete: "complete_on d_child U_child"
    using child_post unfolding bmssp_post_full_def by blast
  have child_complete_final: "complete_on d' U_child"
    using Full_Loop_Step child_complete
    unfolding complete_preserved_def by blast
  have head_complete: "complete_on d' (range_tree P a (Fin b))"
  proof -
    have "range_tree P a (Fin b) \<subseteq> U_child"
      using U_child_tree range_tree_subset_bound_tree[of P a "Fin b"] by simp
    then show ?thesis
      using complete_on_subset[OF child_complete_final] by blast
  qed
  have tail_trace:
    "concrete_partition_loop_trace P B b bs d' B' Us_tail U_tail"
    using Full_Loop_Step.IH Full_Loop_Step.prems by blast
  have tail_le: "bound_le B' B"
    and tail_mono: "nondecreasing_from b bs"
    and tail_bounds: "bounds_le B' (b # bs)"
    and tail_children:
      "list_all2 (\<lambda>U X. U = X \<and> complete_on d' U) Us_tail
        (range_tree_chain_list P b bs B')"
    using tail_trace unfolding concrete_partition_loop_trace_def by blast+
  have a_bound: "bound_le (Fin a) B'"
  proof -
    have "bound_le (Fin b) B'"
      using tail_bounds by simp
    then show ?thesis
      using Full_Loop_Step(2) by (cases B') auto
  qed
  show ?case
    unfolding concrete_partition_loop_trace_def
    using tail_le Full_Loop_Step(2) tail_mono tail_bounds a_bound
      Full_Loop_Step(3) head_complete tail_children
    by auto
next
  case (Full_Loop_Step_Pre beta B d P a b d' k cap l d_child U_child betas bs B' Us_tail U_tail)
  have beta_le: "bound_le (Fin beta) B"
    using Full_Loop_Step_Pre by blast
  have a_le_b: "a \<le> b"
    using Full_Loop_Step_Pre by blast
  have lower_complete: "complete_on d' (bound_tree P (Fin a))"
    using Full_Loop_Step_Pre by blast
  have pre_beta: "bmssp_pre_full d P (Fin beta)"
    using bmssp_pre_full_bound_mono
      [OF Full_Loop_Step_Pre.prems(2) beta_le] .
  have child_pre: "bmssp_pre_full d (split_below d P beta) (Fin beta)"
    using Full_Loop_Step_Pre by blast
  have child_reaches:
    "\<And>x. x \<in> split_below d P beta \<Longrightarrow> reachable s x"
    using Full_Loop_Step_Pre.prems(3) unfolding split_below_def by blast
  have child_post:
    "bmssp_post_full d (split_below d P beta) (Fin beta)
      d_child (Fin b) U_child"
    using Full_Loop_Step_Pre.IH Full_Loop_Step_Pre.prems(1) child_pre child_reaches
    by blast
  have cover_beta: "complete_tree_cover d P (Fin beta)"
    using bmssp_pre_full_complete_tree_cover[OF pre_beta] .
  have U_child_tree: "U_child = bound_tree P (Fin b)"
    using pull_recursive_post_lifts_bound_tree[OF cover_beta child_post] .
  have child_complete: "complete_on d_child U_child"
    using child_post unfolding bmssp_post_full_def by blast
  have child_complete_final: "complete_on d' U_child"
    using Full_Loop_Step_Pre child_complete
    unfolding complete_preserved_def by blast
  have head_complete: "complete_on d' (range_tree P a (Fin b))"
  proof -
    have "range_tree P a (Fin b) \<subseteq> U_child"
      using U_child_tree range_tree_subset_bound_tree[of P a "Fin b"] by simp
    then show ?thesis
      using complete_on_subset[OF child_complete_final] by blast
  qed
  have tail_trace:
    "concrete_partition_loop_trace P B b bs d' B' Us_tail U_tail"
    using Full_Loop_Step_Pre.IH Full_Loop_Step_Pre.prems by blast
  have tail_le: "bound_le B' B"
    and tail_mono: "nondecreasing_from b bs"
    and tail_bounds: "bounds_le B' (b # bs)"
    and tail_children:
      "list_all2 (\<lambda>U X. U = X \<and> complete_on d' U) Us_tail
        (range_tree_chain_list P b bs B')"
    using tail_trace unfolding concrete_partition_loop_trace_def by blast+
  have a_bound: "bound_le (Fin a) B'"
  proof -
    have "bound_le (Fin b) B'"
      using tail_bounds by simp
    then show ?thesis
      using a_le_b by (cases B') auto
  qed
  show ?case
    unfolding concrete_partition_loop_trace_def
    using tail_le a_le_b tail_mono tail_bounds a_bound
      lower_complete head_complete tail_children
    by auto
next
  case (Full_Base S x k cap d B)
  have post:
    "bmssp_post d S B
      (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
      (base_case_bound k x B)
      (base_case_vertices k x B)"
    using base_case_result_bmssp_post[OF Full_Base.hyps, where k = k and B = B and d = d]
    unfolding base_case_result_def by simp
  then show ?case
    by (rule bmssp_post_imp_post_full)
next
  case (Full_Step k cap l d S B d' a betas bs B' Us U_loop U)
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  let ?W = "{v \<in> bound_tree S B'. ?d_fp v = dist s v}"
  have sound_fp: "sound_label ?d_fp"
    unfolding find_pivots_label_capped_def
    by (rule fp_iter_capped_label_sound[OF Full_Step.prems(1) Full_Step.prems(3)])
  have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
    using find_pivots_capped_establishes_pivot_pre_concrete
      [OF Full_Step.prems(1) Full_Step.prems(2) Full_Step.prems(3)] .
  have P_subset_S: "?P \<subseteq> S"
    unfolding find_pivots_pivots_capped_def by auto
  have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
    using P_subset_S Full_Step.prems(3) by blast
  have trace: "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
    using Full_Step.IH sound_fp pivot_pre P_reaches by blast
  have concrete_step:
    "concrete_capped_bmssp_step k cap d S B a bs d' B' Us U"
    unfolding concrete_capped_bmssp_step_def
    using trace Full_Step by (auto simp: Let_def)
  show ?case
    by (rule concrete_capped_bmssp_step_correct
      [OF Full_Step.prems(1) Full_Step.prems(2) Full_Step.prems(3) concrete_step])
qed

theorem finite_initial_label_full_operational_top_level_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and run: "full_operational_bmssp k cap l finite_initial_label {s} Infinity d' Infinity U"
  shows "sssp_correct d'"
proof -
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  have post_full:
    "bmssp_post_full finite_initial_label {s} Infinity d' Infinity U"
    by (rule full_operational_bmssp_correct[OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  then have U_V: "U = V"
    using bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  have complete: "complete_on d' U"
    using post unfolding bmssp_post_def by auto
  then show ?thesis
    using U_V unfolding complete_on_def sssp_correct_def by auto
qed

inductive full_operational_partition_loop_state where
  State_Done:
    "keys_of D = {} \<Longrightarrow>
     bound_le (Fin a) B \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     full_operational_partition_loop_state M t k cap l d P B d' D a [] [] (Fin a)
       [range_tree P a (Fin a)]
       (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a (Fin a)])) 0"
| State_Step:
    "pull_separates D M Bmax S_pull beta D_pull \<Longrightarrow>
     bound_le (Fin beta) B \<Longrightarrow>
     bmssp_pre_full d (split_below d P beta) (Fin beta) \<Longrightarrow>
     S_pull = split_below d P beta \<Longrightarrow>
     a \<le> b \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     full_operational_bmssp k cap l d S_pull (Fin beta) d_child (Fin b) U_child \<Longrightarrow>
     complete_preserved d_child d' U_child \<Longrightarrow>
     batch =
       edge_relaxation_pairs_between d_child U_child b beta @
       label_pairs_between d S_pull b beta \<Longrightarrow>
     D_next = batch_min_update D_pull batch \<Longrightarrow>
     partition_pull_cost_bound c_pull S_pull \<Longrightarrow>
     partition_batch_cost_bound c_batch t batch \<Longrightarrow>
     full_operational_partition_loop_state M t k cap l d P B d' D_next b betas bs B'
       Us_tail U_tail c_tail \<Longrightarrow>
     c = c_pull + c_batch + c_child + c_tail \<Longrightarrow>
     full_operational_partition_loop_state M t k cap l d P B d' D a (beta # betas) (b # bs) B'
       (range_tree P a (Fin b) # Us_tail)
       (bound_tree P (Fin a) \<union> \<Union>(set (range_tree P a (Fin b) # Us_tail))) c"

lemma full_operational_partition_loop_state_lengths:
  assumes run:
    "full_operational_partition_loop_state M t k cap l d P B d' D a
      betas bs B' Us U c"
  shows "length betas = length bs"
    and "length Us = Suc (length bs)"
proof -
  have both: "length betas = length bs \<and> length Us = Suc (length bs)"
    using run
  proof (induction)
    case State_Done
    then show ?case by simp
  next
    case (State_Step D M Bmax S_pull beta D_pull B d P a b d' k cap l
        d_child U_child batch D_next c_pull c_batch t betas bs B'
        Us_tail U_tail c_tail c_child c)
    then show ?case by simp
  qed
  show "length betas = length bs"
    using both by blast
  show "length Us = Suc (length bs)"
    using both by blast
qed

theorem full_operational_partition_loop_state_refines:
  assumes run:
    "full_operational_partition_loop_state M t k cap l d P B d' D a betas bs B' Us U c"
  shows "full_operational_partition_loop k cap l d P B d' a betas bs B' Us U"
  using run
proof (induction)
  case (State_Done D a B d' P M t k cap l d)
  show ?case
    by (rule Full_Loop_Done[OF State_Done.hyps(2,3)])
next
  case (State_Step D M Bmax S_pull beta D_pull B d P a b d' k cap l d_child U_child batch D_next c_pull c_batch t betas bs B' Us_tail U_tail c_tail c_step c_total)
  have child_run:
    "full_operational_bmssp k cap l d (split_below d P beta) (Fin beta)
      d_child (Fin b) U_child"
    using State_Step by blast
  show ?case
    by (rule Full_Loop_Step_Pre)
      (use State_Step child_run in auto)
qed

theorem full_operational_partition_loop_state_cost_bound:
  assumes run:
    "full_operational_partition_loop_state M t k cap l d P B d' D a betas bs B' Us U c"
  shows "\<exists>child_costs pulls batches.
    c \<le> sum_list child_costs + sum_list (map (\<lambda>S. card (S :: 'a set)) pulls) +
      t * sum_list (map (\<lambda>batch. length (batch :: ('a \<times> real) list)) batches)"
  using run
proof (induction)
  case (State_Done D a B d' P M t k cap l d)
  show ?case
    by (intro exI[of _ "[]"] exI[of _ "[]"] exI[of _ "[]"]) simp
next
  case (State_Step D M Bmax S_pull beta D_pull B d P a b d' k cap l d_child U_child batch D_next c_pull c_batch t betas bs B' Us_tail U_tail c_tail c_step c_total)
  have tail_ex: "\<exists>child_costs pulls batches.
    c_tail \<le> sum_list child_costs + sum_list (map (\<lambda>S. card (S :: 'a set)) pulls) +
      t * sum_list (map (\<lambda>batch. length (batch :: ('a \<times> real) list)) batches)"
    using State_Step.IH by assumption
  obtain child_costs :: "nat list" and pulls :: "'a set list"
    and batches :: "('a \<times> real) list list" where tail:
    "c_tail \<le> sum_list child_costs + sum_list (map card pulls) +
      t * sum_list (map length batches)"
    using tail_ex by blast
  have pull_bound: "c_pull \<le> card S_pull"
    using State_Step unfolding partition_pull_cost_bound_def by blast
  have batch_bound: "c_batch \<le> t * length batch"
    using State_Step unfolding partition_batch_cost_bound_def by blast
  have c_eq: "c_step = c_pull + c_batch + c_total + c_tail"
    using State_Step by blast
  let ?child_costs = "c_total # child_costs"
  let ?pulls = "S_pull # pulls"
  let ?batches = "batch # batches"
  have "c_step \<le> sum_list ?child_costs + sum_list (map card ?pulls) +
      t * sum_list (map length ?batches)"
  proof -
    have "c_pull + c_batch + c_total + c_tail \<le>
        card S_pull + t * length batch + c_total +
        (sum_list child_costs + sum_list (map card pulls) +
          t * sum_list (map length batches))"
      using pull_bound batch_bound tail by simp
    also have "\<dots> =
        sum_list ?child_costs + sum_list (map card ?pulls) +
        t * sum_list (map length ?batches)"
      by (simp add: algebra_simps)
    finally show ?thesis
      using c_eq by simp
  qed
  then show ?case
    by blast
qed

theorem full_operational_partition_loop_state_trace_and_cost:
  assumes run:
    "full_operational_partition_loop_state M t k cap l d P B d' D a betas bs B' Us U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
  obtains child_costs pulls batches where
    "concrete_partition_loop_trace P B a bs d' B' Us U"
    "c \<le> sum_list child_costs + sum_list (map (\<lambda>S. card (S :: 'a set)) pulls) +
      t * sum_list (map (\<lambda>batch. length (batch :: ('a \<times> real) list)) batches)"
proof -
  have full_loop:
    "full_operational_partition_loop k cap l d P B d' a betas bs B' Us U"
    by (rule full_operational_partition_loop_state_refines[OF run])
  have trace: "concrete_partition_loop_trace P B a bs d' B' Us U"
    by (rule full_operational_partition_loop_trace
      [OF full_loop sound pre P_reaches])
  obtain child_costs pulls batches where cost:
    "c \<le> sum_list child_costs + sum_list (map (\<lambda>S. card (S :: 'a set)) pulls) +
      t * sum_list (map (\<lambda>batch. length (batch :: ('a \<times> real) list)) batches)"
    using full_operational_partition_loop_state_cost_bound[OF run] by blast
  then show thesis
    using that trace by blast
qed

theorem full_operational_partition_loop_state_cost_bound_by_child_edges:
  assumes run:
    "full_operational_partition_loop_state M t k cap l d P B d' D a betas bs B' Us U c"
    and P_subset: "P \<subseteq> V"
  shows "\<exists>child_costs child_sets.
    length child_costs = length child_sets \<and>
    c \<le> sum_list child_costs + M * length child_costs +
      t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
        M * length child_costs)"
  using run P_subset
proof (induction)
  case (State_Done D a B d' P M t k cap l d)
  show ?case
    by (intro exI[of _ "[]"] exI[of _ "[]"]) simp
next
  case (State_Step D M Bmax S_pull beta D_pull B d P a b d' k cap l
      d_child U_child batch D_next c_pull c_batch t betas bs B'
      Us_tail U_tail c_tail c_step c_total)
  have tail_ex: "\<exists>child_costs child_sets.
      length child_costs = length child_sets \<and>
      c_tail \<le> sum_list child_costs + M * length child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
          M * length child_costs)"
    using State_Step.IH State_Step.prems by blast
  obtain child_costs child_sets where len_tail:
      "length child_costs = length child_sets"
    and tail:
      "c_tail \<le> sum_list child_costs + M * length child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
          M * length child_costs)"
    using tail_ex by blast
  have finite_P: "finite P"
    using finite_subset[OF State_Step.prems(1) finite_V] .
  have S_pull_subset: "S_pull \<subseteq> P"
    using State_Step.hyps(4) unfolding split_below_def by blast
  have finite_S_pull: "finite S_pull"
    using finite_subset[OF S_pull_subset finite_P] .
  have card_pull: "card S_pull \<le> M"
    using pull_separates_card[OF State_Step.hyps(1)] .
  have pull_cost: "c_pull \<le> M"
    using State_Step.hyps(11) card_pull
    unfolding partition_pull_cost_bound_def by linarith
  have edge_len:
    "length (edge_relaxation_pairs_between d_child U_child b beta) \<le>
      card (outgoing_edges U_child)"
    by (rule edge_relaxation_pairs_between_length_le_outgoing)
  have label_len:
    "length (label_pairs_between d S_pull b beta) \<le> card S_pull"
    by (rule label_pairs_between_length_le_card[OF finite_S_pull])
  have batch_len:
    "length batch \<le> card (outgoing_edges U_child) + M"
    using State_Step.hyps(9) edge_len label_len card_pull by simp
  have batch_cost:
    "c_batch \<le> t * (card (outgoing_edges U_child) + M)"
  proof -
    have "c_batch \<le> t * length batch"
      using State_Step.hyps(12)
      unfolding partition_batch_cost_bound_def by simp
    also have "\<dots> \<le> t * (card (outgoing_edges U_child) + M)"
      using batch_len by simp
    finally show ?thesis .
  qed
  let ?child_costs = "c_total # child_costs"
  let ?child_sets = "U_child # child_sets"
  have len: "length ?child_costs = length ?child_sets"
    using len_tail by simp
  have cost:
    "c_step \<le> sum_list ?child_costs + M * length ?child_costs +
      t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) ?child_sets) +
        M * length ?child_costs)"
  proof -
    have c_eq: "c_step = c_pull + c_batch + c_total + c_tail"
      using State_Step.hyps(14) .
    have "c_pull + c_batch + c_total + c_tail \<le>
        M + t * (card (outgoing_edges U_child) + M) + c_total +
        (sum_list child_costs + M * length child_costs +
          t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
            M * length child_costs))"
      using pull_cost batch_cost tail by simp
    also have "\<dots> =
        sum_list ?child_costs + M * length ?child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) ?child_sets) +
          M * length ?child_costs)"
      by (simp add: algebra_simps)
    finally show ?thesis
      using c_eq by simp
  qed
  show ?case
    using len cost by blast
qed

theorem full_operational_partition_loop_state_trace_and_edge_cost:
  assumes run:
    "full_operational_partition_loop_state M t k cap l d P B d' D a betas bs B' Us U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
  obtains child_costs child_sets where
    "concrete_partition_loop_trace P B a bs d' B' Us U"
    "length child_costs = length child_sets"
    "c \<le> sum_list child_costs + M * length child_costs +
      t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
        M * length child_costs)"
proof -
  have P_subset: "P \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have full_loop:
    "full_operational_partition_loop k cap l d P B d' a betas bs B' Us U"
    by (rule full_operational_partition_loop_state_refines[OF run])
  have trace: "concrete_partition_loop_trace P B a bs d' B' Us U"
    by (rule full_operational_partition_loop_trace
      [OF full_loop sound pre P_reaches])
  obtain child_costs child_sets where len:
      "length child_costs = length child_sets"
    and cost:
      "c \<le> sum_list child_costs + M * length child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
          M * length child_costs)"
    using full_operational_partition_loop_state_cost_bound_by_child_edges
      [OF run P_subset] by blast
  then show thesis
    using that trace by blast
qed

theorem full_operational_partition_loop_state_cost_bound_by_child_edges_complete:
  assumes run:
    "full_operational_partition_loop_state M t k cap l d P B d' D a betas bs B' Us U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
  shows "\<exists>child_costs child_sets.
    length child_costs = length child_sets \<and>
    (\<forall>X\<in>set child_sets. X \<subseteq> V) \<and>
    c \<le> sum_list child_costs + M * length child_costs +
      t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
        M * length child_costs)"
  using run sound pre P_reaches
proof (induction)
  case (State_Done D a B d' P M t k cap l d)
  show ?case
    by (intro exI[of _ "[]"] exI[of _ "[]"]) simp
next
  case (State_Step D M Bmax S_pull beta D_pull B d P a b d' k cap l
      d_child U_child batch D_next c_pull c_batch t betas bs B'
      Us_tail U_tail c_tail c_step c_total)
  have tail_ex: "\<exists>child_costs child_sets.
      length child_costs = length child_sets \<and>
      (\<forall>X\<in>set child_sets. X \<subseteq> V) \<and>
      c_tail \<le> sum_list child_costs + M * length child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
          M * length child_costs)"
    using State_Step.IH State_Step.prems by blast
  obtain child_costs child_sets where len_tail:
      "length child_costs = length child_sets"
    and sets_tail: "\<forall>X\<in>set child_sets. X \<subseteq> V"
    and tail:
      "c_tail \<le> sum_list child_costs + M * length child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
          M * length child_costs)"
    using tail_ex by blast
  have child_reaches:
    "\<And>x. x \<in> S_pull \<Longrightarrow> reachable s x"
    using State_Step.prems(3) State_Step.hyps(4)
    unfolding split_below_def by blast
  have child_pre: "bmssp_pre_full d S_pull (Fin beta)"
    using State_Step.hyps(3,4) by simp
  have child_post:
    "bmssp_post_full d S_pull (Fin beta) d_child (Fin b) U_child"
    using full_operational_bmssp_correct
      [OF State_Step.hyps(7) State_Step.prems(1) child_pre child_reaches] .
  have child_set: "U_child \<subseteq> V"
    using child_post unfolding bmssp_post_full_def bound_tree_def by blast
  have P_subset: "P \<subseteq> V"
    using State_Step.prems(2) unfolding bmssp_pre_full_def by blast
  have finite_P: "finite P"
    using finite_subset[OF P_subset finite_V] .
  have S_pull_subset: "S_pull \<subseteq> P"
    using State_Step.hyps(4) unfolding split_below_def by blast
  have finite_S_pull: "finite S_pull"
    using finite_subset[OF S_pull_subset finite_P] .
  have card_pull: "card S_pull \<le> M"
    using pull_separates_card[OF State_Step.hyps(1)] .
  have pull_cost: "c_pull \<le> M"
    using State_Step.hyps(11) card_pull
    unfolding partition_pull_cost_bound_def by linarith
  have edge_len:
    "length (edge_relaxation_pairs_between d_child U_child b beta) \<le>
      card (outgoing_edges U_child)"
    by (rule edge_relaxation_pairs_between_length_le_outgoing)
  have label_len:
    "length (label_pairs_between d S_pull b beta) \<le> card S_pull"
    by (rule label_pairs_between_length_le_card[OF finite_S_pull])
  have batch_len:
    "length batch \<le> card (outgoing_edges U_child) + M"
    using State_Step.hyps(9) edge_len label_len card_pull by simp
  have batch_cost:
    "c_batch \<le> t * (card (outgoing_edges U_child) + M)"
  proof -
    have "c_batch \<le> t * length batch"
      using State_Step.hyps(12)
      unfolding partition_batch_cost_bound_def by simp
    also have "\<dots> \<le> t * (card (outgoing_edges U_child) + M)"
      using batch_len by simp
    finally show ?thesis .
  qed
  let ?child_costs = "c_total # child_costs"
  let ?child_sets = "U_child # child_sets"
  have len: "length ?child_costs = length ?child_sets"
    using len_tail by simp
  have sets: "\<forall>X\<in>set ?child_sets. X \<subseteq> V"
    using child_set sets_tail by simp
  have cost:
    "c_step \<le> sum_list ?child_costs + M * length ?child_costs +
      t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) ?child_sets) +
        M * length ?child_costs)"
  proof -
    have c_eq: "c_step = c_pull + c_batch + c_total + c_tail"
      using State_Step.hyps(14) .
    have "c_pull + c_batch + c_total + c_tail \<le>
        M + t * (card (outgoing_edges U_child) + M) + c_total +
        (sum_list child_costs + M * length child_costs +
          t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
            M * length child_costs))"
      using pull_cost batch_cost tail by simp
    also have "\<dots> =
        sum_list ?child_costs + M * length ?child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) ?child_sets) +
          M * length ?child_costs)"
      by (simp add: algebra_simps)
    finally show ?thesis
      using c_eq by simp
  qed
  show ?case
    using len sets cost by blast
qed

theorem full_operational_partition_loop_state_trace_and_complete_edge_cost:
  assumes run:
    "full_operational_partition_loop_state M t k cap l d P B d' D a betas bs B' Us U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
  obtains child_costs child_sets where
    "concrete_partition_loop_trace P B a bs d' B' Us U"
    "length child_costs = length child_sets"
    "\<And>X. X \<in> set child_sets \<Longrightarrow> X \<subseteq> V"
    "c \<le> sum_list child_costs + M * length child_costs +
      t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
        M * length child_costs)"
proof -
  have full_loop:
    "full_operational_partition_loop k cap l d P B d' a betas bs B' Us U"
    by (rule full_operational_partition_loop_state_refines[OF run])
  have trace: "concrete_partition_loop_trace P B a bs d' B' Us U"
    by (rule full_operational_partition_loop_trace
      [OF full_loop sound pre P_reaches])
  obtain child_costs child_sets where len:
      "length child_costs = length child_sets"
    and sets: "\<forall>X\<in>set child_sets. X \<subseteq> V"
    and cost:
      "c \<le> sum_list child_costs + M * length child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
          M * length child_costs)"
    using full_operational_partition_loop_state_cost_bound_by_child_edges_complete
      [OF run sound pre P_reaches] by blast
  then show thesis
    using that trace by blast
qed

end

end
