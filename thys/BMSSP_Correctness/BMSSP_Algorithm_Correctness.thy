theory BMSSP_Algorithm_Correctness
  imports BMSSP_Correctness
begin

section \<open>Abstract BMSSP Correctness\<close>

text \<open>
  This theory is the correctness skeleton of the BMSSP development.  The
  previous entry-point theory defines distances, bounds, and the basic
  bounded multi-source postcondition.  Here we refine that interface just far
  enough to express the recursive algorithm described in the paper, while
  still abstracting from running time and from the concrete partition data
  structure.

  The key strengthening is that sources used by a recursive call are required
  to be complete sources: their current labels already equal their true
  shortest-path distances.  This matters because BMSSP does not merely carry a
  set of vertices; it carries a set of vertices whose shortest-path trees may
  certify the rest of the current bounded range.  A vertex that is not solved
  yet must either be solved directly by the current round or lie on a shortest
  path through one of those complete sources.

  At this level the algorithm is decomposed into three abstract obligations:

    \<^item> \<open>FindPivots\<close> must either complete a bounded vertex or delegate it to
      a complete pivot.
    \<^item> The partition loop driven by \<open>Pull\<close>, recursive BMSSP calls, edge
      relaxation, and \<open>BatchPrepend\<close> must solve the bounded problem induced by
      the pivot set.
    \<^item> The final assembly of recursive-loop vertices with the completed
      \<open>FindPivots\<close> vertices is then proved correct.

  The main theorem of the file, \<open>abstract_bmssp_correct\<close>, says that any
  implementation satisfying those obligations establishes the full BMSSP
  postcondition.  Later theories instantiate the obligations with a concrete
  recursive loop, then the bucketed partition structure, and finally the
  executable example.  None of the runtime arguments appear here; this file is
  the semantic hinge that lets the later cost proofs remain separate from the
  shortest-path correctness proof.

  Two abstractions matter for navigating the rest of the development.  First,
  this layer abstracts from the partition data structure entirely: any
  implementation satisfying the three obligations above is acceptable, so the
  later sorted-list and bucketed-partition refinements both plug in here
  without disturbing the correctness proof.  Second, this layer abstracts from
  running time entirely: the cost predicates and amortized budgets live one
  layer further down, in \<^file>\<open>BMSSP_Top_Level_Bounds.thy\<close> and
  \<^file>\<open>BMSSP_Bucketed_Partition.thy\<close>, so that a reader interested only
  in correctness can stop here.
\<close>

context finite_weighted_digraph
begin

definition complete_vertices :: "('v \<Rightarrow> real) \<Rightarrow> 'v set" where
  "complete_vertices d = {v \<in> V. reachable s v \<and> d v = dist s v}"

definition through_complete :: "('v \<Rightarrow> real) \<Rightarrow> 'v set \<Rightarrow> 'v \<Rightarrow> bool" where
  "through_complete d S v \<longleftrightarrow> through (S \<inter> complete_vertices d) v"

definition bmssp_pre_full :: "('v \<Rightarrow> real) \<Rightarrow> 'v set \<Rightarrow> bound \<Rightarrow> bool" where
  "bmssp_pre_full d S B \<longleftrightarrow>
     S \<subseteq> V \<and>
     (\<forall>v\<in>V. reachable s v \<longrightarrow> below_bound (dist s v) B \<longrightarrow>
       d v \<noteq> dist s v \<longrightarrow> through_complete d S v)"

definition bmssp_post_full ::
  "('v \<Rightarrow> real) \<Rightarrow> 'v set \<Rightarrow> bound \<Rightarrow> ('v \<Rightarrow> real) \<Rightarrow> bound \<Rightarrow> 'v set \<Rightarrow> bool" where
  "bmssp_post_full d S B d' B' U \<longleftrightarrow>
     bound_le B' B \<and> U = bound_tree S B' \<and> complete_on d' U"

definition find_pivots_post ::
  "('v \<Rightarrow> real) \<Rightarrow> 'v set \<Rightarrow> bound \<Rightarrow> ('v \<Rightarrow> real) \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> bool" where
  "find_pivots_post d S B d' P W \<longleftrightarrow>
     S \<subseteq> V \<and>
     P \<subseteq> S \<and>
     W \<subseteq> bound_tree S B \<and>
     complete_on d' W \<and>
     (\<forall>v\<in>V. reachable s v \<longrightarrow> below_bound (dist s v) B \<longrightarrow>
       d v = dist s v \<longrightarrow> d' v = dist s v) \<and>
     (\<forall>v\<in>bound_tree S B. v \<in> W \<or> through_complete d' P v)"

definition partition_loop_post ::
  "('v \<Rightarrow> real) \<Rightarrow> 'v set \<Rightarrow> bound \<Rightarrow> ('v \<Rightarrow> real) \<Rightarrow> bound \<Rightarrow> 'v set \<Rightarrow> bool" where
  "partition_loop_post d P B d' B' U \<longleftrightarrow> bmssp_post_full d P B d' B' U"

definition final_bmssp_assembly ::
  "'v set \<Rightarrow> bound \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> bool" where
  "final_bmssp_assembly S B' W U_loop U \<longleftrightarrow>
     U = U_loop \<union> {v \<in> W. below_bound (dist s v) B'}"

definition abstract_bmssp_step ::
  "('v \<Rightarrow> real) \<Rightarrow> 'v set \<Rightarrow> bound \<Rightarrow> ('v \<Rightarrow> real) \<Rightarrow> bound \<Rightarrow> 'v set \<Rightarrow> bool" where
  "abstract_bmssp_step d S B d' B' U \<longleftrightarrow>
     (\<exists>d_fp P W U_loop.
       find_pivots_post d S B d_fp P W \<and>
       partition_loop_post d_fp P B d' B' U_loop \<and>
       complete_on d' W \<and>
       final_bmssp_assembly S B' W U_loop U)"

text \<open>
  The definitions above separate the proof into named contracts.  The set
  @{const complete_vertices} records exactly the vertices solved by a label
  function, and @{const through_complete} refines the earlier
  \<open>through\<close>-predicate by requiring the intermediary source to be solved.
  The strengthened precondition @{const bmssp_pre_full} is therefore the
  recursive invariant: every unresolved bounded vertex is certified by a
  shortest path through a complete source.

  The predicate @{const find_pivots_post} is intentionally asymmetric.  It
  returns a new label function, a pivot subset, and a set of vertices completed
  directly by the pivot search.  Vertices in the current bounded tree are then
  either in that completed set or are delegated to the pivot subset via
  @{const through_complete}.  The partition loop contract
  @{const partition_loop_post} is just the full BMSSP postcondition specialized
  to those pivots.  Finally, @{const final_bmssp_assembly} describes the set
  union that reconstructs the caller's solved range from the recursive-loop
  output and the vertices completed by FindPivots.

  This decomposition is useful because each later theory can prove one small
  interface.  The algorithmic theory proves an instance of
  @{const abstract_bmssp_step}; the data-structure theories prove that the
  partition operations realize the abstract loop assumptions; the top-level
  theory only needs the postcondition produced here.
\<close>

lemma bmssp_post_full_imp_post:
  assumes "bmssp_post_full d S B d' B' U"
  shows "bmssp_post d S B d' B' U"
  using assms unfolding bmssp_post_full_def bmssp_post_def by blast

lemma top_bmssp_pre_full:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and source_complete: "d s = dist s s"
  shows "bmssp_pre_full d {s} Infinity"
proof -
  have "s \<in> complete_vertices d"
    using source_in_V source_complete reachable_refl
    unfolding complete_vertices_def by blast
  then have "\<And>v. reachable s v \<Longrightarrow> through_complete d {s} v"
    using reachable_source_through unfolding through_complete_def by auto
  then show ?thesis
    using all_reachable source_in_V unfolding bmssp_pre_full_def by auto
qed

lemma top_bmssp_pre_full_reachable:
  assumes source_complete: "d s = dist s s"
  shows "bmssp_pre_full d {s} Infinity"
proof -
  have "s \<in> complete_vertices d"
    using source_in_V source_complete reachable_refl
    unfolding complete_vertices_def by blast
  then have "\<And>v. reachable s v \<Longrightarrow> through_complete d {s} v"
    using reachable_source_through unfolding through_complete_def by auto
  then show ?thesis
    using source_in_V unfolding bmssp_pre_full_def by auto
qed

lemma through_complete_imp_through:
  assumes "through_complete d S v"
  shows "through S v"
  using assms unfolding through_complete_def through_def by blast

lemma bound_tree_mono:
  assumes "S \<subseteq> T"
  shows "bound_tree S B \<subseteq> bound_tree T B"
  using assms unfolding bound_tree_def through_def by blast

lemma bound_tree_bound_mono:
  assumes "bound_le B' B"
  shows "bound_tree S B' \<subseteq> bound_tree S B"
  using assms unfolding bound_tree_def
  by (cases B'; cases B) auto

lemma complete_on_subset:
  assumes "complete_on d T" "S \<subseteq> T"
  shows "complete_on d S"
  using assms unfolding complete_on_def by blast

lemma source_in_own_bound_tree:
  assumes xS: "x \<in> S"
    and reach_x: "reachable s x"
    and below_x: "below_bound (dist s x) B"
  shows "x \<in> bound_tree S B"
proof -
  obtain p where p: "shortest_walk s p x"
    using reach_x by (rule shortest_walk_exists)
  have x_in_p: "x \<in> set p"
    using shortest_walk_hd(1,3)[OF p] by (metis last_in_set)
  then have "through S x"
    using xS p unfolding through_def by blast
  moreover have "x \<in> V"
  proof -
    have "walk p"
      using p unfolding shortest_walk_def simple_walk_betw_def
        walk_betw_def by blast
    then have "set p \<subseteq> V"
      by (rule walk_set_subset)
    then show ?thesis
      using x_in_p by blast
  qed
  ultimately show ?thesis
    using reach_x below_x unfolding bound_tree_def by blast
qed

lemma sources_subset_bound_tree:
  assumes reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (dist s x) B"
  shows "S \<subseteq> bound_tree S B"
  using source_in_own_bound_tree[OF _ reaches below] by blast

lemma sources_subset_bound_tree_if_label_below:
  assumes complete: "complete_on d S"
    and reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
  shows "S \<subseteq> bound_tree S B"
proof (rule sources_subset_bound_tree)
  fix x
  assume xS: "x \<in> S"
  then show "reachable s x"
    by (rule reaches)
  have "d x = dist s x"
    using complete reaches[OF xS] xS unfolding complete_on_def by blast
  then show "below_bound (dist s x) B"
    using below[OF xS] by simp
qed

lemma bmssp_post_full_source_card_le_if_label_below_output:
  assumes post: "bmssp_post_full d S B d' B' U"
    and complete: "complete_on d S"
    and reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B'"
  shows "card S \<le> card U"
proof -
  have U_eq: "U = bound_tree S B'"
    using post unfolding bmssp_post_full_def by blast
  have S_subset_U: "S \<subseteq> U"
    using sources_subset_bound_tree_if_label_below[OF complete reaches below]
    unfolding U_eq .
  have finite_U: "finite U"
    unfolding U_eq bound_tree_def using finite_V by auto
  show ?thesis
    by (rule card_mono[OF finite_U S_subset_U])
qed

text \<open>
  The first group of lemmas is structural.  It relates the strengthened
  complete-source invariant to the base BMSSP vocabulary and proves the
  monotonicity facts needed when the recursive call returns a smaller bound.
  The source-subset lemmas are small but important: they show that a complete
  source whose label is below the returned bound belongs to the returned
  @{const bound_tree}.  That is the formal reason the recursive call cannot
  discard the pivots it was asked to solve.
\<close>

lemma find_pivots_establishes_pivot_pre:
  assumes pre: "bmssp_pre_full d S B"
    and fp: "find_pivots_post d S B d' P W"
  shows "bmssp_pre_full d' P B"
proof -
  have "P \<subseteq> V"
    using fp unfolding find_pivots_post_def bound_tree_def by auto
  moreover have "\<And>v. \<lbrakk>v \<in> V; reachable s v; below_bound (dist s v) B; d' v \<noteq> dist s v\<rbrakk>
      \<Longrightarrow> through_complete d' P v"
  proof -
    fix v
    assume v: "v \<in> V" "reachable s v" "below_bound (dist s v) B" "d' v \<noteq> dist s v"
    show "through_complete d' P v"
    proof (cases "through S v")
      case True
      then have "v \<in> bound_tree S B"
        using v unfolding bound_tree_def by blast
      then have "v \<in> W \<or> through_complete d' P v"
        using fp unfolding find_pivots_post_def by blast
      then show ?thesis
      proof
        assume "v \<in> W"
        then have "d' v = dist s v"
          using fp v unfolding find_pivots_post_def complete_on_def by blast
        with v show ?thesis by blast
      qed blast
    next
      case False
      have "d v = dist s v"
      proof (rule ccontr)
        assume "d v \<noteq> dist s v"
        then have "through_complete d S v"
          using pre v unfolding bmssp_pre_full_def by blast
        then have "through S v"
          by (rule through_complete_imp_through)
        with False show False by blast
      qed
      then have "d' v = dist s v"
        using fp v unfolding find_pivots_post_def by blast
      with v show ?thesis by blast
    qed
  qed
  ultimately show ?thesis
    unfolding bmssp_pre_full_def by blast
qed

lemma conservative_find_pivots_post:
  assumes pre: "bmssp_pre_full d S B"
  defines "W \<equiv> {v \<in> bound_tree S B. d v = dist s v}"
  shows "find_pivots_post d S B d S W"
proof -
  have S: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have W_subset: "W \<subseteq> bound_tree S B"
    unfolding W_def by blast
  have compW: "complete_on d W"
    unfolding W_def complete_on_def by blast
  have preserve: "\<forall>v\<in>V. reachable s v \<longrightarrow> below_bound (dist s v) B \<longrightarrow>
      d v = dist s v \<longrightarrow> d v = dist s v"
    by blast
  have cover: "\<forall>v\<in>bound_tree S B. v \<in> W \<or> through_complete d S v"
  proof
    fix v
    assume v: "v \<in> bound_tree S B"
    show "v \<in> W \<or> through_complete d S v"
    proof (cases "d v = dist s v")
      case True
      then show ?thesis
        using v unfolding W_def by blast
    next
      case False
      then show ?thesis
        using pre v unfolding bmssp_pre_full_def bound_tree_def by blast
    qed
  qed
  show ?thesis
    using S W_subset compW preserve cover
    unfolding find_pivots_post_def by blast
qed

text \<open>
  The next two lemmas explain the handoff from FindPivots to recursion.  The
  theorem @{thm find_pivots_establishes_pivot_pre} is the crucial invariant
  transfer: after FindPivots, the pivot set satisfies @{const bmssp_pre_full}
  under the updated labels.  If a vertex was already outside the old source
  tree, the preservation clause of @{const find_pivots_post} keeps its label
  correct; if it was inside the tree and not directly completed, the cover
  clause delegates it through a complete pivot.

  The conservative postcondition is a sanity instance of the same interface.
  It says the abstract FindPivots contract is not empty: keeping the same
  sources and naming the already-complete part of the tree is sufficient.  The
  executable development uses stronger concrete pivot selection, but this
  lemma is helpful for understanding the shape of the contract independently of
  any particular implementation.
\<close>

lemma final_assembly_bound_tree:
  assumes fp: "find_pivots_post d S B d_fp P W"
    and loop: "partition_loop_post d_fp P B d' B' U_loop"
    and asm: "final_bmssp_assembly S B' W U_loop U"
  shows "U = bound_tree S B'"
proof -
  have loop_post: "bmssp_post_full d_fp P B d' B' U_loop"
    using loop unfolding partition_loop_post_def .
  then have le: "bound_le B' B" and Uloop: "U_loop = bound_tree P B'"
    unfolding bmssp_post_full_def by auto
  have P_subset: "P \<subseteq> S"
    using fp unfolding find_pivots_post_def by blast
  have W_subset: "W \<subseteq> bound_tree S B"
    using fp unfolding find_pivots_post_def by blast

  show ?thesis
  proof
    show "U \<subseteq> bound_tree S B'"
    proof
      fix v
      assume "v \<in> U"
      then consider "v \<in> U_loop" | "v \<in> W" "below_bound (dist s v) B'"
        using asm unfolding final_bmssp_assembly_def by blast
      then show "v \<in> bound_tree S B'"
      proof cases
        case 1
        then have "v \<in> bound_tree P B'"
          using Uloop by simp
        then show ?thesis
          using bound_tree_mono[OF P_subset, of B'] by blast
      next
        case 2
        then show ?thesis
          using W_subset unfolding bound_tree_def by blast
      qed
    qed
  next
    show "bound_tree S B' \<subseteq> U"
    proof
      fix v
      assume v: "v \<in> bound_tree S B'"
      then have "v \<in> bound_tree S B"
        using bound_tree_bound_mono[OF le, of S] by blast
      then have cover: "v \<in> W \<or> through_complete d_fp P v"
        using fp unfolding find_pivots_post_def by blast
      then show "v \<in> U"
      proof
        assume "v \<in> W"
        moreover have "below_bound (dist s v) B'"
          using v unfolding bound_tree_def by blast
        ultimately show ?thesis
          using asm unfolding final_bmssp_assembly_def by blast
      next
        assume "through_complete d_fp P v"
        then have "through P v"
          by (rule through_complete_imp_through)
        then have "v \<in> bound_tree P B'"
          using v unfolding bound_tree_def by blast
        then have "v \<in> U_loop"
          using Uloop by simp
        then show ?thesis
          using asm unfolding final_bmssp_assembly_def by blast
      qed
    qed
  qed
qed

lemma final_assembly_complete:
  assumes fp: "find_pivots_post d S B d_fp P W"
    and loop: "partition_loop_post d_fp P B d' B' U_loop"
    and compW: "complete_on d' W"
    and asm: "final_bmssp_assembly S B' W U_loop U"
  shows "complete_on d' U"
proof -
  have "complete_on d' U_loop"
    using loop unfolding partition_loop_post_def bmssp_post_full_def by blast
  moreover have "{v \<in> W. below_bound (dist s v) B'} \<subseteq> W"
    by blast
  then have "complete_on d' {v \<in> W. below_bound (dist s v) B'}"
    using complete_on_subset[OF compW] by blast
  ultimately show ?thesis
    using asm unfolding final_bmssp_assembly_def complete_on_def by blast
qed

text \<open>
  Final assembly is where the two solved regions are reconciled.  The loop has
  solved @{const bound_tree} for the pivot set below the returned bound.  The
  FindPivots phase may also have solved vertices in the caller's original
  tree; only those below the returned bound are retained in the caller's output
  set.  Lemma @{thm final_assembly_bound_tree} proves that this union is not
  merely contained in the desired set but exactly equals the caller's
  @{const bound_tree}.  Lemma @{thm final_assembly_complete} then proves that
  labels are complete on that exact set.
\<close>

theorem abstract_bmssp_correct:
  assumes step: "abstract_bmssp_step d S B d' B' U"
  shows "bmssp_post_full d S B d' B' U"
proof -
  obtain d_fp P W U_loop where
    fp: "find_pivots_post d S B d_fp P W" and
    loop: "partition_loop_post d_fp P B d' B' U_loop" and
    compW: "complete_on d' W" and
    asm: "final_bmssp_assembly S B' W U_loop U"
    using step unfolding abstract_bmssp_step_def by blast
  have le: "bound_le B' B"
    using loop unfolding partition_loop_post_def bmssp_post_full_def by blast
  have U: "U = bound_tree S B'"
    using final_assembly_bound_tree[OF fp loop asm] .
  have comp: "complete_on d' U"
    using final_assembly_complete[OF fp loop compW asm] .
  show ?thesis
    using le U comp unfolding bmssp_post_full_def by blast
qed

theorem abstract_bmssp_correct_with_pre:
  assumes pre: "bmssp_pre_full d S B"
    and step: "abstract_bmssp_step d S B d' B' U"
  shows "bmssp_post_full d S B d' B' U"
  using abstract_bmssp_correct[OF step] .

lemma abstract_bmssp_step_exposes_pivot_pre:
  assumes pre: "bmssp_pre_full d S B"
    and step: "abstract_bmssp_step d S B d' B' U"
  obtains d_fp P W U_loop where
    "find_pivots_post d S B d_fp P W"
    "bmssp_pre_full d_fp P B"
    "partition_loop_post d_fp P B d' B' U_loop"
    "complete_on d' W"
    "final_bmssp_assembly S B' W U_loop U"
proof -
  obtain d_fp P W U_loop where
    fp: "find_pivots_post d S B d_fp P W" and
    loop: "partition_loop_post d_fp P B d' B' U_loop" and
    compW: "complete_on d' W" and
    asm: "final_bmssp_assembly S B' W U_loop U"
    using step unfolding abstract_bmssp_step_def by blast
  have "bmssp_pre_full d_fp P B"
    using find_pivots_establishes_pivot_pre[OF pre fp] .
  then show thesis
    using that fp loop compW asm by blast
qed

corollary abstract_bmssp_correct_weak:
  assumes "abstract_bmssp_step d S B d' B' U"
  shows "bmssp_post d S B d' B' U"
  using bmssp_post_full_imp_post abstract_bmssp_correct assms by blast

text \<open>
  The theorem @{thm abstract_bmssp_correct} is the file's main assembly result:
  from an @{const abstract_bmssp_step} witness it extracts the FindPivots
  contract, the recursive partition-loop contract, and the final set assembly,
  then rebuilds @{const bmssp_post_full}.  The variant
  @{thm abstract_bmssp_correct_with_pre} keeps the precondition in its
  statement for clients whose proof scripts naturally carry it, while
  @{thm abstract_bmssp_step_exposes_pivot_pre} exposes the pivot precondition
  needed by the recursive implementation.

  The final top-level theorems connect this abstract step to ordinary
  single-source shortest paths.  Once the root call uses source set \<open>{s}\<close> and
  bound @{term Infinity}, the root correctness lemmas from the entry-point
  theory turn the BMSSP postcondition into @{const sssp_correct}.
\<close>

theorem abstract_top_level_sssp_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and step: "abstract_bmssp_step d {s} Infinity d' Infinity U"
  shows "sssp_correct d'"
proof -
  have "bmssp_post d {s} Infinity d' Infinity U"
    using abstract_bmssp_correct_weak[OF step] .
  then show ?thesis
    using successful_root_bmssp_correct[OF all_reachable] by blast
qed

theorem abstract_top_level_reachable_sssp_correct:
  assumes step: "abstract_bmssp_step d {s} Infinity d' Infinity U"
  shows "sssp_correct d'"
proof -
  have "bmssp_post d {s} Infinity d' Infinity U"
    using abstract_bmssp_correct_weak[OF step] .
  then show ?thesis
    by (rule successful_root_bmssp_sssp_correct)
qed

theorem initialized_abstract_top_level_sssp_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and source_complete: "d s = dist s s"
    and step: "abstract_bmssp_step d {s} Infinity d' Infinity U"
  shows "sssp_correct d'"
  using abstract_top_level_sssp_correct[OF all_reachable step] .

theorem initialized_abstract_top_level_reachable_sssp_correct:
  assumes source_complete: "d s = dist s s"
    and step: "abstract_bmssp_step d {s} Infinity d' Infinity U"
  shows "sssp_correct d'"
  using abstract_top_level_reachable_sssp_correct[OF step] .

end

end
