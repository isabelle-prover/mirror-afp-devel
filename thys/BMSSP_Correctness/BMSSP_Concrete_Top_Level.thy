theory BMSSP_Concrete_Top_Level
  imports BMSSP_Initialization BMSSP_Concrete_Step
begin

section \<open>Concrete Top-Level Correctness\<close>

text \<open>
  These theorems connect the finite initial labels to the concrete one-step
  BMSSP assembly relation.  They avoid the abstract \<open>abstract_bmssp_step\<close>
  contract used by the abstract interface.

  The top-level SSSP call is a BMSSP call with singleton source set \<open>{s}\<close>
  and infinite bound.  The finite initial label gives distance \<open>0\<close> at the
  source and an effectively infinite value elsewhere.  Once a concrete BMSSP
  step proves the full BMSSP postcondition for this root problem, the
  infinite-bound tree is the whole vertex set, so completeness of the returned
  label function is exactly SSSP correctness.

  Two entry points are provided because the development has both an uncapped
  concrete step and the capped step used by the paper's parameter schedule.
  They share the same proof: establish the root precondition, invoke the
  corresponding concrete-step correctness theorem, then collapse the root
  BMSSP postcondition to \<open>sssp_correct\<close>.
\<close>

context unique_shortest_digraph
begin

theorem finite_initial_label_concrete_top_level_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and step: "concrete_bmssp_step k finite_initial_label {s} Infinity a bs
      d' Infinity Us U"
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
    by (rule concrete_bmssp_step_correct[OF sound pre S_reaches step])
  have "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  then have U_V: "U = V"
    using bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  have complete: "complete_on d' U"
    using \<open>bmssp_post finite_initial_label {s} Infinity d' Infinity U\<close>
    unfolding bmssp_post_def by auto
  then show ?thesis
    using U_V unfolding complete_on_def sssp_correct_def by auto
qed

theorem finite_initial_label_concrete_capped_top_level_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and step: "concrete_capped_bmssp_step k cap finite_initial_label {s} Infinity a bs
      d' Infinity Us U"
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
    by (rule concrete_capped_bmssp_step_correct[OF sound pre S_reaches step])
  have "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  then have U_V: "U = V"
    using bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  have complete: "complete_on d' U"
    using \<open>bmssp_post finite_initial_label {s} Infinity d' Infinity U\<close>
    unfolding bmssp_post_def by auto
  then show ?thesis
    using U_V unfolding complete_on_def sssp_correct_def by auto
qed

end

end
