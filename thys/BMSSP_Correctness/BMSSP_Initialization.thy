theory BMSSP_Initialization
  imports BMSSP_Shortest_Path_Lemmas
begin

section \<open>Initial Labels\<close>

text \<open>
  BMSSP starts from the usual shortest-path initialization: the source is
  complete and all other labels are conservative upper bounds.  In an
  imperative implementation one would normally write this as distance zero for
  the source and infinity for every other vertex.  The abstract correctness
  layer in this entry uses real-valued labels rather than an extended-real
  datatype, so this theory gives a finite replacement for infinity.

  The replacement is the maximum true source distance over the finite vertex
  set.  This is not intended as an executable way to discover shortest paths;
  it is a semantic initial label used in the proof stack.  Because the graph
  locale is finite, the maximum exists.  Because every reachable vertex has
  distance at most that maximum, the label function is sound.  The source
  remains exact because the distance from any vertex to itself is zero under
  non-negative edge weights.

  The lemmas below isolate precisely the facts needed by later top-level
  theorems: the source label is complete, the whole label function is sound,
  and the root call with source set \<open>{s}\<close> and bound \<open>Infinity\<close> satisfies
  the BMSSP precondition.
\<close>

context finite_weighted_digraph
begin

definition finite_initial_label where
  "finite_initial_label v = (if v = s then 0 else Max (dist s ` V))"

text \<open>
  The definition @{const finite_initial_label} is intentionally semantic.  Its
  non-source value mentions @{const dist}, so it is not the data structure used
  by the exported example.  Its role is to let the correctness proof start
  from a finite real-valued label function while preserving the same logical
  shape as Dijkstra's standard initialization.
\<close>

lemma dist_refl_zero:
  assumes "v \<in> V"
  shows "dist v v = 0"
proof -
  have simple: "simple_walk_betw v [v] v"
    using assms unfolding simple_walk_betw_def walk_betw_def by simp
  have "dist v v \<le> 0"
    using dist_le_simple_walk_weight[OF simple] by simp
  moreover have "0 \<le> dist v v"
  proof -
    have "reachable v v"
      using reachable_refl[OF assms] .
    then have "dist v v \<in> simple_walk_weights v v"
      using dist_is_simple_walk_weight by blast
    then obtain p where p: "simple_walk_betw v p v" "walk_weight p = dist v v"
      unfolding simple_walk_weights_def by auto
    then have "walk p"
      unfolding simple_walk_betw_def walk_betw_def by auto
    then have "0 \<le> walk_weight p"
      by (rule walk_weight_nonneg)
    then show ?thesis
      using p by simp
  qed
  ultimately show ?thesis
    by simp
qed

lemma finite_initial_label_source_complete:
  "finite_initial_label s = dist s s"
  using dist_refl_zero[OF source_in_V] unfolding finite_initial_label_def by simp

text \<open>
  The proof of @{thm dist_refl_zero} uses the one-vertex simple walk for the
  upper bound and non-negativity of walk weights for the lower bound.  From it,
  @{thm finite_initial_label_source_complete} gives the exact source label
  required by root BMSSP initialization.  The two soundness lemmas below differ
  only in whether reachability of every vertex is supplied explicitly or left
  as the local reachable premise of @{const sound_label}.
\<close>

lemma finite_initial_label_sound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
  shows "sound_label finite_initial_label"
proof -
  have nonempty: "dist s ` V \<noteq> {}"
    using source_in_V by blast
  show ?thesis
    unfolding sound_label_def finite_initial_label_def
  proof clarify
    fix v
    assume vV: "v \<in> V" and reach_v: "reachable s v"
    show "dist s v \<le> (if v = s then 0 else Max (dist s ` V))"
    proof (cases "v = s")
      case True
      then show ?thesis
        using dist_refl_zero[OF source_in_V] by simp
    next
      case False
      have "dist s v \<in> dist s ` V"
        using vV by blast
      then have "dist s v \<le> Max (dist s ` V)"
        using finite_V by simp
      then show ?thesis
        using False by simp
    qed
  qed
qed

lemma finite_initial_label_sound_reachable:
  shows "sound_label finite_initial_label"
proof -
  have nonempty: "dist s ` V \<noteq> {}"
    using source_in_V by blast
  show ?thesis
    unfolding sound_label_def finite_initial_label_def
  proof clarify
    fix v
    assume vV: "v \<in> V" and reach_v: "reachable s v"
    show "dist s v \<le> (if v = s then 0 else Max (dist s ` V))"
    proof (cases "v = s")
      case True
      then show ?thesis
        using dist_refl_zero[OF source_in_V] by simp
    next
      case False
      have "dist s v \<in> dist s ` V"
        using vV by blast
      then have "dist s v \<le> Max (dist s ` V)"
        using finite_V nonempty by simp
      then show ?thesis
        using False by simp
    qed
  qed
qed

lemma initialized_root_pre_full:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
  shows "bmssp_pre finite_initial_label {s} Infinity"
  using top_bmssp_pre[OF all_reachable, of finite_initial_label] .

text \<open>
  Finally, @{thm initialized_root_pre_full} packages the initialized labels for
  the root abstract BMSSP call.  The source set is the singleton \<open>{s}\<close>, the
  bound is @{term Infinity}, and every reachable vertex lies on a shortest path
  through the source.  Later theories strengthen this precondition to the
  complete-source form and then discharge the full algorithmic step relation.
\<close>

end

end
