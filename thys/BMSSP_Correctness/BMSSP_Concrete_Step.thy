theory BMSSP_Concrete_Step
  imports BMSSP_Pull_Minimum
begin

section \<open>Concrete One-Step BMSSP Assembly\<close>

text \<open>
  This theory packages the concrete part of a non-base BMSSP call.  The
  abstract correctness skeleton states its recursive middle phase with the
  predicate \<open>partition_loop_post\<close>: after FindPivots has chosen a pivot
  set, the loop must solve the bounded tree induced by those pivots.  That
  statement is intentionally compact, but it hides the range structure that the
  implementation actually follows.

  The concrete step exposed here replaces that abstract loop contract by an
  explicit monotone trace of child ranges.  A trace contains the first lower
  boundary, the list of subsequent boundaries, the label function after the
  loop, and the collection of vertex sets solved by the child calls.  The trace
  proof checks that the boundaries are nondecreasing, remain below the returned
  BMSSP bound, and cover exactly the chain of bounded shortest-path trees that
  the partition loop is supposed to assemble.

  The final step definitions then restore FindPivots.  The uncapped version
  uses the conceptual FindPivots operation, while the capped version uses the
  executable bounded search from the paper.  Both definitions have the same
  shape: perform FindPivots, solve the pivot loop, keep the vertices completed
  directly by FindPivots, and return their union.  The two correctness theorems
  below show that this concrete assembly is still a valid
  \<open>bmssp_post_full\<close> result.
\<close>

context unique_shortest_digraph
begin

definition concrete_partition_loop_trace where
  "concrete_partition_loop_trace P B a bs d' B' Us U \<longleftrightarrow>
     bound_le B' B \<and>
     nondecreasing_from a bs \<and>
     bounds_le B' (a # bs) \<and>
     complete_on d' (bound_tree P (Fin a)) \<and>
     list_all2 (\<lambda>U X. U = X \<and> complete_on d' U) Us
       (range_tree_chain_list P a bs B') \<and>
     U = bound_tree P (Fin a) \<union> \<Union>(set Us)"

theorem concrete_partition_loop_trace_post:
  assumes trace: "concrete_partition_loop_trace P B a bs d' B' Us U"
  shows "bmssp_post_full d P B d' B' U"
proof -
  have le: "bound_le B' B"
    and mono: "nondecreasing_from a bs"
    and bounds: "bounds_le B' (a # bs)"
    and lower: "complete_on d' (bound_tree P (Fin a))"
    and children: "list_all2 (\<lambda>U X. U = X \<and> complete_on d' U) Us
       (range_tree_chain_list P a bs B')"
    and U: "U = bound_tree P (Fin a) \<union> \<Union>(set Us)"
    using trace unfolding concrete_partition_loop_trace_def by blast+
  show ?thesis
    by (rule partition_loop_trace_assembly_post
      [OF le mono bounds lower children U])
qed

definition concrete_bmssp_step where
  "concrete_bmssp_step k d S B a bs d' B' Us U \<longleftrightarrow>
     (let d_fp = find_pivots_label k d S B;
          P = find_pivots_pivots k d S B;
          W = {v \<in> bound_tree S B'. d_fp v = dist s v}
      in \<exists>U_loop.
          concrete_partition_loop_trace P B a bs d' B' Us U_loop \<and>
          complete_on d' W \<and>
          U = U_loop \<union> W)"

definition concrete_capped_bmssp_step where
  "concrete_capped_bmssp_step k cap d S B a bs d' B' Us U \<longleftrightarrow>
     (let d_fp = find_pivots_label_capped k cap d S B;
          P = find_pivots_pivots_capped k cap d S B;
          W = {v \<in> bound_tree S B'. d_fp v = dist s v}
      in \<exists>U_loop.
          concrete_partition_loop_trace P B a bs d' B' Us U_loop \<and>
          complete_on d' W \<and>
          U = U_loop \<union> W)"

text \<open>
  The definition @{const concrete_partition_loop_trace} is the local certificate
  for the recursive partition loop.  It does not say how pulls are generated;
  it says what must be true of the resulting range sequence.  The theorem
  @{thm concrete_partition_loop_trace_post} then converts such a trace into
  @{const bmssp_post_full} for the pivot set.  The step predicates
  @{const concrete_bmssp_step} and @{const concrete_capped_bmssp_step} wrap the
  trace with FindPivots and the final union of loop-completed and
  FindPivots-completed vertices.
\<close>

theorem concrete_bmssp_step_correct:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and step: "concrete_bmssp_step k d S B a bs d' B' Us U"
  shows "bmssp_post_full d S B d' B' U"
proof -
  let ?d_fp = "find_pivots_label k d S B"
  let ?P = "find_pivots_pivots k d S B"
  let ?W = "{v \<in> bound_tree S B'. ?d_fp v = dist s v}"
  obtain U_loop where
    trace: "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
    and compW: "complete_on d' ?W"
    and U: "U = U_loop \<union> ?W"
    using step unfolding concrete_bmssp_step_def by (auto simp: Let_def)
  have loop: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
    using concrete_partition_loop_trace_post[OF trace] .
  have le: "bound_le B' B"
    using loop unfolding bmssp_post_full_def by blast
  have U_tree: "U_loop \<union> ?W = bound_tree S B'"
    using concrete_find_pivots_final_tree_assembly[OF sound pre S_reaches loop] .
  have loop_complete: "complete_on d' U_loop"
    using loop unfolding bmssp_post_full_def by blast
  have complete: "complete_on d' (U_loop \<union> ?W)"
    using complete_on_Un[OF loop_complete compW] .
  have "bmssp_post_full d S B d' B' (U_loop \<union> ?W)"
    using le U_tree complete unfolding bmssp_post_full_def by blast
  then show ?thesis
    using U by simp
qed

theorem concrete_capped_bmssp_step_correct:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and step: "concrete_capped_bmssp_step k cap d S B a bs d' B' Us U"
  shows "bmssp_post_full d S B d' B' U"
proof -
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  let ?W = "{v \<in> bound_tree S B'. ?d_fp v = dist s v}"
  obtain U_loop where
    trace: "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
    and compW: "complete_on d' ?W"
    and U: "U = U_loop \<union> ?W"
    using step unfolding concrete_capped_bmssp_step_def by (auto simp: Let_def)
  have loop: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
    using concrete_partition_loop_trace_post[OF trace] .
  have le: "bound_le B' B"
    using loop unfolding bmssp_post_full_def by blast
  have U_tree: "U_loop \<union> ?W = bound_tree S B'"
    using concrete_capped_find_pivots_final_tree_assembly[OF sound pre S_reaches loop] .
  have loop_complete: "complete_on d' U_loop"
    using loop unfolding bmssp_post_full_def by blast
  have complete: "complete_on d' (U_loop \<union> ?W)"
    using complete_on_Un[OF loop_complete compW] .
  have "bmssp_post_full d S B d' B' (U_loop \<union> ?W)"
    using le U_tree complete unfolding bmssp_post_full_def by blast
  then show ?thesis
    using U by simp
qed

end

end
