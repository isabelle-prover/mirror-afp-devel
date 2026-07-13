theory BMSSP_Recursive
  imports BMSSP_Base_Case BMSSP_Concrete_Top_Level
begin

section \<open>Level-Indexed BMSSP Relation\<close>

text \<open>
  This theory introduces the first level-indexed BMSSP relation.  Earlier
  theories prove a base case and a concrete non-base step in isolation.  The
  inductive relation below is the small bridge that turns those one-step facts
  into a recursive BMSSP run indexed by a natural recursion level.

  The relation is deliberately simple.  At level zero it uses the checked base
  case for a singleton source set.  At a successor level it accepts any
  concrete capped BMSSP step assembled from FindPivots and a monotone partition
  trace.  This file does not yet model the operational generation of every
  pull and child call; that more detailed relation is proved separately in
  \<open>BMSSP_Operational_Pull\<close>.  Here the purpose is to show that the base/step
  decomposition is already enough for semantic correctness.

  The main theorem \<open>concrete_bmssp_correct\<close> below is an induction over the
  level-indexed relation.  The base rule delegates to the base-case
  postcondition, and the step rule delegates to the concrete capped step
  theorem.  The final theorem specializes the relation to the root source and
  infinite bound, obtaining ordinary single-source shortest-path correctness
  for the finite initial label.
\<close>

context unique_shortest_digraph
begin

inductive concrete_bmssp where
  Base:
    "S = {x} \<Longrightarrow>
     concrete_bmssp k cap 0 d S B
       (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
       (base_case_bound k x B)
       (base_case_vertices k x B)"
| Step:
    "concrete_capped_bmssp_step k cap d S B a bs d' B' Us U \<Longrightarrow>
     concrete_bmssp k cap (Suc l) d S B d' B' U"

text \<open>
  The two rules of @{const concrete_bmssp} mirror the recursive structure of
  the paper.  The base rule solves the bounded region reachable from one source
  by the base-case routine.  The successor rule abstracts over the child runs
  already summarized by @{const concrete_capped_bmssp_step}.  This keeps the
  induction proof short and makes clear which theorem is responsible for each
  layer of the algorithm.
\<close>

lemma bmssp_post_imp_post_full:
  assumes "bmssp_post d S B d' B' U"
  shows "bmssp_post_full d S B d' B' U"
  using assms unfolding bmssp_post_def bmssp_post_full_def by blast

theorem concrete_bmssp_correct:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and run: "concrete_bmssp k cap l d S B d' B' U"
  shows "bmssp_post_full d S B d' B' U"
  using run sound pre S_reaches
proof (induction arbitrary: rule: concrete_bmssp.induct)
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
  case (Step k cap d S B a bs d' B' Us U l)
  show ?case
    by (rule concrete_capped_bmssp_step_correct
      [OF Step.prems(1) Step.prems(2) Step.prems(3) Step.hyps])
qed

text \<open>
  The proof of @{thm concrete_bmssp_correct} is intentionally direct.  All
  shortest-path reasoning has already been packaged in the base-case and
  concrete-step theories, so the induction only selects the appropriate
  correctness theorem for each rule.  The remaining top-level theorem then
  supplies the standard root precondition, soundness of the initial label, and
  reachability of the singleton source set.
\<close>

theorem finite_initial_label_recursive_top_level_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and run: "concrete_bmssp k cap l finite_initial_label {s} Infinity d' Infinity U"
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
    by (rule concrete_bmssp_correct[OF sound pre S_reaches run])
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

end

end
