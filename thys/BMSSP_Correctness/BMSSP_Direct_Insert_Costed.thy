theory BMSSP_Direct_Insert_Costed
  imports BMSSP_Exact_Range_Costed
begin

section \<open>Direct-Insert Costed Runs\<close>

text \<open>
  This theory refines the range-costed BMSSP run with the final accounting
  distinction needed by the bucketed partition implementation.  The earlier
  split-range relation separates edge-generated batch entries from source-label
  batch entries.  Here the edge-generated entries are split again.  Some relaxed
  edge values belong directly in the current parent range and are paid for by
  the ordinary insert cost parameter \<open>t\<close>.  Other relaxed values fall below the
  next child bound and are prepended into the lower block; those are paid for by
  the batch parameter \<open>h\<close>.

  The distinction mirrors the bucketed data structure.  A direct insert is the
  operation that searches for a bucket position and may trigger the logarithmic
  bucket-splitting work.  A lower-range prepend is cheaper in the abstract
  accounting because it is grouped with other items destined for the next pull.
  Recording the two lists separately lets the later amortised theorem keep the
  direct-insert term visible instead of hiding it inside one combined batch
  budget.

  The semantic content is intentionally unchanged.  The inductive run still
  produces the same completed range slices as the exact range-costed relation,
  and the same BMSSP postcondition is recovered by forgetting the extra
  accounting fields.  What changes is the cost expression: each loop step now
  exposes a direct-edge batch, a lower-edge batch, a source batch, the child
  recursive cost, and the tail-loop cost.

  This is the last local-cost layer before the global recurrence is instantiated.
  The closing theorems near the end of the file package the separated charges
  into two forms: an amortised bound that keeps direct range inserts explicit,
  and a level bound that can feed the headline top-level analysis.
\<close>

context unique_shortest_digraph
begin

inductive direct_insert_costed_partition_loop_state
  and direct_insert_costed_bmssp where
  Direct_Insert_Costed_State_Done:
    "keys_of D = {} \<Longrightarrow>
     bound_le (Fin a) B \<Longrightarrow>
     complete_on d' (bound_tree P B) \<Longrightarrow>
     direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
       [] [] B [range_tree P a B]
       (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a B])) 0 []"
| Direct_Insert_Costed_State_Stop:
    "bound_le (Fin a) B \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     k * cap \<le> card (bound_tree P (Fin a)) \<Longrightarrow>
     direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
       [] [] (Fin a) [range_tree P a (Fin a)]
       (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a (Fin a)])) 0 []"
| Direct_Insert_Costed_State_Step:
    "pull_separates D (M_of l) Bmax S_pull beta D_pull \<Longrightarrow>
     bound_le (Fin beta) B \<Longrightarrow>
     bmssp_pre_full d S_pull (Fin beta) \<Longrightarrow>
     S_pull = split_below d P beta \<Longrightarrow>
     (\<forall>x\<in>S_pull. reachable s x) \<Longrightarrow>
     a \<le> b \<Longrightarrow>
     bound_le (Fin a) B' \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     card (bound_tree P (Fin a)) < k * cap \<Longrightarrow>
     direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
       d_child (Fin b) U_child c_child \<Longrightarrow>
     U_child = range_tree P a (Fin b) \<Longrightarrow>
     complete_preserved d_child d' U_child \<Longrightarrow>
     direct_edge_batch = edge_relaxation_pairs_in_bound d_child U_child beta B \<Longrightarrow>
     lower_edge_batch = edge_relaxation_pairs_between d_child U_child b beta \<Longrightarrow>
     source_batch = label_pairs_between d S_pull b beta \<Longrightarrow>
     batch = direct_edge_batch @ lower_edge_batch @ source_batch \<Longrightarrow>
     D_next = batch_min_update D_pull batch \<Longrightarrow>
     partition_pull_cost_bound c_pull S_pull \<Longrightarrow>
     partition_batch_cost_bound c_direct t direct_edge_batch \<Longrightarrow>
     partition_batch_cost_bound c_lower h lower_edge_batch \<Longrightarrow>
     partition_batch_cost_bound c_sources h source_batch \<Longrightarrow>
     direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d'
       D_next b betas bs B' Us_tail U_tail c_tail child_costs_tail \<Longrightarrow>
     c = c_pull + c_direct + c_lower + c_sources + c_child + c_tail \<Longrightarrow>
     direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
       (beta # betas) (b # bs) B'
       (range_tree P a (Fin b) # Us_tail)
       (bound_tree P (Fin a) \<union>
        \<Union>(set (range_tree P a (Fin b) # Us_tail))) c
       (c_child # child_costs_tail)"
| Direct_Insert_Costed_Base:
    "S = {x} \<Longrightarrow>
     direct_insert_costed_bmssp \<Delta> M_of t h k cap 0 d S B
       (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
       (base_case_bound k x B)
       (base_case_vertices k x B)
       (base_case_scan_cost \<Delta> k x B)"
| Direct_Insert_Costed_Step:
    "D = label_partition_view
       (find_pivots_label_capped k cap d S B)
       (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
     partition_initial_insert_cost_bound c_insert t
       (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
     direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l
       (find_pivots_label_capped k cap d S B)
       (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
       Us U_loop c_loop child_costs_loop \<Longrightarrow>
     complete_on d'
       {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
     U = U_loop \<union>
      {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
      c = fp_iter_capped_scan_cost k cap d S S B + c_insert + c_loop \<Longrightarrow>
      direct_insert_costed_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"

text \<open>
  The constructors are the same operational skeleton as before, but the step
  constructor now names three batches.  @{const edge_relaxation_pairs_in_bound}
  extracts direct edge relaxations in the parent range, @{const
  edge_relaxation_pairs_between} extracts lower edge relaxations between the
  child output bound and the pull bound, and @{const label_pairs_between}
  extracts old source labels in the same lower interval.

  Keeping these lists in the derivation tree is useful because each has a
  different combinatorial owner.  Direct edge entries are counted by the direct
  range lists; lower edge entries are counted by child edge-range lists; source
  entries are counted through child source sets and then by the progress
  lemma.  The proof scripts that follow mostly say that this extra bookkeeping
  is conservative: it refines the earlier correctness trace without changing
  which vertices are completed.
\<close>

inductive_cases direct_insert_costed_bmssp_zeroE:
  "direct_insert_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"

inductive_cases direct_insert_costed_bmssp_SucE:
  "direct_insert_costed_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"

lemma direct_insert_costed_partition_loop_state_mono:
  assumes run:
    "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
  shows "nondecreasing_from a bs"
  using run by (induction) auto

lemma direct_insert_costed_partition_loop_state_beta_bounds:
  assumes run:
    "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
  shows "bounds_le B betas"
  using run by (induction) auto

theorem direct_insert_costed_partition_loop_state_trace:
  "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
     betas bs B' Us U c child_costs \<Longrightarrow>
   sound_label d \<Longrightarrow>
   bmssp_pre_full d P B \<Longrightarrow>
   (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
   concrete_partition_loop_trace P B a bs d' B' Us U"
and direct_insert_costed_bmssp_correct:
  "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
   sound_label d \<Longrightarrow>
   bmssp_pre_full d S B \<Longrightarrow>
   (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
   bmssp_post_full d S B d' B' U"
proof (induction rule:
    direct_insert_costed_partition_loop_state_direct_insert_costed_bmssp.inducts)
  case (Direct_Insert_Costed_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  have a_le: "bound_le (Fin a) B"
    using Direct_Insert_Costed_State_Done by blast
  have complete_B: "complete_on d' (bound_tree P B)"
    using Direct_Insert_Costed_State_Done by blast
  have lower: "complete_on d' (bound_tree P (Fin a))"
    by (rule complete_on_subset[OF complete_B])
      (rule bound_tree_bound_mono[OF a_le])
  have range_complete: "complete_on d' (range_tree P a B)"
    by (rule complete_on_subset[OF complete_B])
      (rule range_tree_subset_bound_tree)
  have B_le: "bound_le B B"
    by (cases B) simp_all
  show ?case
    unfolding concrete_partition_loop_trace_def
    using B_le a_le lower range_complete by simp
next
  case (Direct_Insert_Costed_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  then show ?case
    unfolding concrete_partition_loop_trace_def complete_on_def by simp
next
  case Direct_Insert_Costed_State_Step
  then show ?case
    unfolding concrete_partition_loop_trace_def bmssp_post_full_def
      complete_preserved_def
    by (auto split: bound.splits)
next
  case (Direct_Insert_Costed_Base S x \<Delta> M_of t h k cap d B)
  have post:
    "bmssp_post d S B
      (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
      (base_case_bound k x B)
      (base_case_vertices k x B)"
    using base_case_result_bmssp_post[OF Direct_Insert_Costed_Base.hyps,
        where k = k and B = B and d = d]
    unfolding base_case_result_def by simp
  then show ?case
    by (rule bmssp_post_imp_post_full)
next
  case (Direct_Insert_Costed_Step D k cap d S B c_insert t \<Delta> M_of h l d' a
      betas bs B' Us U_loop c_loop child_costs_loop U c)
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  let ?W = "{v \<in> bound_tree S B'. ?d_fp v = dist s v}"
  have sound_fp: "sound_label ?d_fp"
    unfolding find_pivots_label_capped_def
    by (rule fp_iter_capped_label_sound[OF Direct_Insert_Costed_Step.prems(1)
      Direct_Insert_Costed_Step.prems(3)])
  have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
    using find_pivots_capped_establishes_pivot_pre_concrete
      [OF Direct_Insert_Costed_Step.prems(1) Direct_Insert_Costed_Step.prems(2)
        Direct_Insert_Costed_Step.prems(3)] .
  have P_subset_S: "?P \<subseteq> S"
    unfolding find_pivots_pivots_capped_def by auto
  have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
    using P_subset_S Direct_Insert_Costed_Step.prems(3) by blast
  have trace:
    "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
    using Direct_Insert_Costed_Step.IH sound_fp pivot_pre P_reaches by blast
  have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
    by (rule concrete_partition_loop_trace_post[OF trace])
  have le: "bound_le B' B"
    using loop_post unfolding bmssp_post_full_def by blast
  have U_tree: "U = bound_tree S B'"
  proof -
    have "U_loop \<union> ?W = bound_tree S B'"
      by (rule concrete_capped_find_pivots_final_tree_assembly
        [OF Direct_Insert_Costed_Step.prems(1) Direct_Insert_Costed_Step.prems(2)
          Direct_Insert_Costed_Step.prems(3) loop_post])
    then show ?thesis
      using Direct_Insert_Costed_Step(6) by simp
  qed
  have loop_complete: "complete_on d' U_loop"
    using loop_post unfolding bmssp_post_full_def by blast
  have U_complete: "complete_on d' U"
    using complete_on_Un[OF loop_complete Direct_Insert_Costed_Step(5)]
      Direct_Insert_Costed_Step(6) by simp
  show ?case
    using le U_tree U_complete unfolding bmssp_post_full_def by blast
qed

theorem finite_initial_label_direct_insert_costed_top_level_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and run:
      "direct_insert_costed_bmssp \<Delta> M_of t h k cap l
        finite_initial_label {s} Infinity d' Infinity U c"
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
    by (rule direct_insert_costed_bmssp_correct[OF run sound pre S_reaches])
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

theorem finite_initial_label_direct_insert_costed_top_level_reachable_correct:
  assumes run:
      "direct_insert_costed_bmssp \<Delta> M_of t h k cap l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d'"
proof -
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using finite_initial_label_source_complete
    by (rule top_bmssp_pre_full_reachable)
  have sound: "sound_label finite_initial_label"
    by (rule finite_initial_label_sound_reachable)
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using reachable_refl[OF source_in_V] by blast
  have post_full:
    "bmssp_post_full finite_initial_label {s} Infinity d' Infinity U"
    by (rule direct_insert_costed_bmssp_correct[OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  then show ?thesis
    by (rule successful_root_bmssp_sssp_correct)
qed

text \<open>
  The correctness theorem @{thm direct_insert_costed_bmssp_correct} is the
  semantic projection of the direct-insert relation.  Once projected, the
  top-level corollaries are the familiar root BMSSP statements: from the finite
  initial label at the source and the infinite output bound, the returned label
  function is a complete SSSP solution.

  The next group of lemmas supplies the progress side conditions used by the
  cost recurrence.  They show that successful BMSSP calls either return the
  original bound or have accumulated enough completed vertices to meet the
  threshold, and that a source set whose labels are below the output bound is
  dominated by the output tree.  These facts turn source-batch costs into
  vertex-count terms.
\<close>

theorem direct_insert_costed_bmssp_source_card_le_if_label_below_output:
  assumes run:
      "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and complete: "complete_on d S"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B'"
  shows "card S \<le> card U"
proof -
  have post: "bmssp_post_full d S B d' B' U"
    by (rule direct_insert_costed_bmssp_correct[OF run sound pre S_reaches])
  show ?thesis
    by (rule bmssp_post_full_source_card_le_if_label_below_output
      [OF post complete S_reaches below])
qed

theorem direct_insert_costed_bmssp_source_card_le_if_sound_label_below_output:
  assumes run:
      "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B'"
  shows "card S \<le> card U"
proof -
  have post: "bmssp_post_full d S B d' B' U"
    by (rule direct_insert_costed_bmssp_correct[OF run sound pre S_reaches])
  have U_eq: "U = bound_tree S B'"
    using post unfolding bmssp_post_full_def by blast
  have S_subset_U: "S \<subseteq> U"
  proof
    fix x
    assume xS: "x \<in> S"
    have S_subset: "S \<subseteq> V"
      using pre unfolding bmssp_pre_full_def by blast
    have xV: "x \<in> V"
      using S_subset xS by blast
    have reach_x: "reachable s x"
      by (rule S_reaches[OF xS])
    have dist_le: "dist s x \<le> d x"
      using sound xV reach_x unfolding sound_label_def by blast
    have below_dist: "below_bound (dist s x) B'"
      using below_bound_le_trans[OF dist_le below[OF xS]] .
    show "x \<in> U"
      unfolding U_eq
      by (rule source_in_own_bound_tree[OF xS reach_x below_dist])
  qed
  have finite_U: "finite U"
    unfolding U_eq bound_tree_def using finite_V by auto
  show ?thesis
    by (rule card_mono[OF finite_U S_subset_U])
qed

theorem direct_insert_costed_partition_loop_state_success_or_threshold:
  "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs \<Longrightarrow>
   sound_label d \<Longrightarrow>
   bmssp_pre_full d P B \<Longrightarrow>
   (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
   B' = B \<or> k * cap \<le> card U"
and direct_insert_costed_bmssp_success_or_threshold_trivial:
  "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule:
    direct_insert_costed_partition_loop_state_direct_insert_costed_bmssp.inducts)
  case (Direct_Insert_Costed_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  then show ?case
    by simp
next
  case (Direct_Insert_Costed_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  then show ?case
    by simp
next
  case (Direct_Insert_Costed_State_Step D M_of l Bmax S_pull beta D_pull B d
      P a b B_out d_out k cap \<Delta> t h d_child U_child c_child
      direct_edge_batch lower_edge_batch source_batch batch D_next c_pull
      c_direct c_lower c_sources betas bs Us_tail U_tail c_tail
      child_costs_tail c)
  have tail:
    "B_out = B \<or> k * cap \<le> card U_tail"
    using Direct_Insert_Costed_State_Step.IH Direct_Insert_Costed_State_Step.prems by blast
  then show ?case
  proof
    assume "B_out = B"
    then show ?thesis
      by blast
  next
    assume threshold_tail: "k * cap \<le> card U_tail"
    have tail_trace:
      "concrete_partition_loop_trace P B b bs d_out B_out Us_tail U_tail"
      by (rule direct_insert_costed_partition_loop_state_trace)
        (use Direct_Insert_Costed_State_Step in blast)+
    have U_tail_def:
      "U_tail = bound_tree P (Fin b) \<union> \<Union>(set Us_tail)"
      using tail_trace unfolding concrete_partition_loop_trace_def by blast
    have split_b:
      "bound_tree P (Fin b) =
        bound_tree P (Fin a) \<union> range_tree P a (Fin b)"
      using bound_tree_split_at[of a "Fin b" P] Direct_Insert_Costed_State_Step
      by simp
    have U_eq_tail:
      "bound_tree P (Fin a) \<union>
          \<Union>(set (range_tree P a (Fin b) # Us_tail)) =
        U_tail"
      using U_tail_def split_b by auto
    show ?thesis
      using threshold_tail U_eq_tail by simp
  qed
next
  case (Direct_Insert_Costed_Base S x \<Delta> M_of t h k cap d B)
  then show ?case
    by simp
next
  case (Direct_Insert_Costed_Step D k cap d S B c_insert t \<Delta> M_of h l d' a
      betas bs B' Us U_loop c_loop child_costs_loop U c)
  then show ?case
    by simp
qed

theorem direct_insert_costed_bmssp_Suc_success_or_threshold:
  assumes run:
      "direct_insert_costed_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "B' = B \<or> k * cap \<le> card U"
  using run
proof cases
  case (Direct_Insert_Costed_Step D c_insert a betas bs Us U_loop c_loop child_costs_loop)
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  let ?W = "{v \<in> bound_tree S B'. ?d_fp v = dist s v}"
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
      [OF Direct_Insert_Costed_Step(3) sound_fp pivot_pre P_reaches])
  have loop_trace:
    "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
    by (rule direct_insert_costed_partition_loop_state_trace
      [OF Direct_Insert_Costed_Step(3) sound_fp pivot_pre P_reaches])
  have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
    by (rule concrete_partition_loop_trace_post[OF loop_trace])
  have finite_U_loop: "finite U_loop"
    using loop_post unfolding bmssp_post_full_def by simp
  show ?thesis
    using loop_class
  proof
    assume "B' = B"
    then show ?thesis
      by blast
  next
    assume threshold_loop: "k * cap \<le> card U_loop"
    have U_eq: "U = U_loop \<union> ?W"
      using Direct_Insert_Costed_Step(5) by simp
    have finite_U: "finite U"
      unfolding U_eq using finite_U_loop by simp
    have U_loop_subset: "U_loop \<subseteq> U"
      unfolding U_eq by blast
    have "card U_loop \<le> card U"
      by (rule card_mono[OF finite_U U_loop_subset])
    then show ?thesis
      using threshold_loop by linarith
  qed
qed

theorem direct_insert_costed_bmssp_Suc_source_card_le_from_label_below:
  assumes run:
      "direct_insert_costed_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and S_cap: "card S \<le> cap"
    and k_pos: "0 < k"
  shows "card S \<le> card U"
proof -
  have call_class: "B' = B \<or> k * cap \<le> card U"
    by (rule direct_insert_costed_bmssp_Suc_success_or_threshold
      [OF run sound pre S_reaches])
  then show ?thesis
  proof
    assume B'_eq: "B' = B"
    show ?thesis
    proof (rule direct_insert_costed_bmssp_source_card_le_if_sound_label_below_output
        [OF run sound pre S_reaches])
      fix x
      assume "x \<in> S"
      then show "below_bound (d x) B'"
        using below B'_eq by simp
    qed
  next
    assume threshold: "k * cap \<le> card U"
    have "cap \<le> k * cap"
      using k_pos by (cases k) simp_all
    then show ?thesis
      using S_cap threshold by linarith
  qed
qed

text \<open>
  The child-cost lemmas extract the recursive calls hidden inside a partition
  loop.  Each child call is paired with the range slice it completed, together
  with the exact source set pulled for that child and the proof obligations
  needed to apply the induction hypothesis.  The additional
  \<open>below_bound (d x) B_child\<close> invariant is what makes source progress
  available without re-deriving the pull/split equality at every later use.
\<close>

theorem direct_insert_costed_partition_loop_state_child_cost_calls_below:
  "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs \<Longrightarrow>
   length child_costs = length bs \<and>
   list_all2
      (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
        direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_costs (range_tree_child_list P a bs)"
and direct_insert_costed_bmssp_child_cost_calls_below_trivial:
  "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule:
    direct_insert_costed_partition_loop_state_direct_insert_costed_bmssp.inducts)
  case (Direct_Insert_Costed_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  show ?case
    by simp
next
  case (Direct_Insert_Costed_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  show ?case
    by simp
next
  case (Direct_Insert_Costed_State_Step D M_of l Bmax S_pull beta D_pull B d
      P a b B' d' k cap \<Delta> t h d_child U_child c_child
      direct_edge_batch lower_edge_batch source_batch batch D_next c_pull
      c_direct c_lower c_sources betas bs Us_tail U_tail c_tail
      child_costs_tail c)
  have tail:
    "length child_costs_tail = length bs \<and>
     list_all2
      (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
        direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_costs_tail (range_tree_child_list P b bs)"
    using Direct_Insert_Costed_State_Step.IH by blast
  have card_pull: "card S_pull \<le> M_of l"
    using Direct_Insert_Costed_State_Step
    unfolding pull_separates_def by blast
  have below_pull: "\<forall>x\<in>S_pull. below_bound (d x) (Fin beta)"
  proof
    fix x
    assume xS: "x \<in> S_pull"
    have "S_pull = split_below d P beta"
      using Direct_Insert_Costed_State_Step by blast
    then show "below_bound (d x) (Fin beta)"
      using xS unfolding split_below_def by auto
  qed
  have head:
    "\<exists>S_child B_child d_child' B_child'.
      direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
        d_child' B_child' U_child c_child \<and>
      bmssp_pre_full d S_child B_child \<and>
      (\<forall>x\<in>S_child. reachable s x) \<and>
      card S_child \<le> M_of l \<and>
      (\<forall>x\<in>S_child. below_bound (d x) B_child)"
    using Direct_Insert_Costed_State_Step card_pull below_pull by blast
  show ?case
    using tail head Direct_Insert_Costed_State_Step by simp
next
  case (Direct_Insert_Costed_Base S x \<Delta> M_of t h k cap d B)
  show ?case
    by simp
next
  case (Direct_Insert_Costed_Step D k cap d S B c_insert t \<Delta> M_of h l
      d' a betas bs B' Us U_loop c_loop child_costs_loop U c)
  show ?case
    by simp
qed

theorem direct_insert_costed_partition_loop_state_child_cost_calls_below_with_bounds:
  "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs \<Longrightarrow>
   list_all2
      (\<lambda>c_child UB. case UB of (U_child, B_child) \<Rightarrow>
        \<exists>S_child d_child B_child'.
          direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l \<and>
          (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_costs (range_tree_child_bound_pair_list P a betas bs)"
and direct_insert_costed_bmssp_child_cost_calls_below_with_bounds_trivial:
  "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule:
    direct_insert_costed_partition_loop_state_direct_insert_costed_bmssp.inducts)
  case (Direct_Insert_Costed_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  show ?case
    by simp
next
  case (Direct_Insert_Costed_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  show ?case
    by simp
next
  case (Direct_Insert_Costed_State_Step D M_of l Bmax S_pull beta D_pull B d
      P a b B' d' k cap \<Delta> t h d_child U_child c_child
      direct_edge_batch lower_edge_batch source_batch batch D_next c_pull
      c_direct c_lower c_sources betas bs Us_tail U_tail c_tail
      child_costs_tail c)
  have tail:
    "list_all2
      (\<lambda>c_child UB. case UB of (U_child, B_child) \<Rightarrow>
        \<exists>S_child d_child B_child'.
          direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l \<and>
          (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_costs_tail (range_tree_child_bound_pair_list P b betas bs)"
    using Direct_Insert_Costed_State_Step.IH by blast
  have card_pull: "card S_pull \<le> M_of l"
    using Direct_Insert_Costed_State_Step
    unfolding pull_separates_def by blast
  have below_pull: "\<forall>x\<in>S_pull. below_bound (d x) (Fin beta)"
  proof
    fix x
    assume xS: "x \<in> S_pull"
    have "S_pull = split_below d P beta"
      using Direct_Insert_Costed_State_Step by blast
    then show "below_bound (d x) (Fin beta)"
      using xS unfolding split_below_def by auto
  qed
  have head:
    "\<exists>S_child d_child' B_child'.
      direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child (Fin beta)
        d_child' B_child' U_child c_child \<and>
      bmssp_pre_full d S_child (Fin beta) \<and>
      (\<forall>x\<in>S_child. reachable s x) \<and>
      card S_child \<le> M_of l \<and>
      (\<forall>x\<in>S_child. below_bound (d x) (Fin beta))"
    using Direct_Insert_Costed_State_Step card_pull below_pull by blast
  show ?case
    using tail head Direct_Insert_Costed_State_Step by simp
next
  case (Direct_Insert_Costed_Base S x \<Delta> M_of t h k cap d B)
  show ?case
    by simp
next
  case (Direct_Insert_Costed_Step D k cap d S B c_insert t \<Delta> M_of h l
      d' a betas bs B' Us U_loop c_loop child_costs_loop U c)
  show ?case
    by simp
qed

theorem direct_insert_costed_partition_loop_state_child_cost_bounds:
  assumes run:
    "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
  shows "list_all2 (\<lambda>c_child U_child.
      c_child \<le> level_range_cost_bound A R L U_child)
    child_costs (range_tree_child_list P a bs)"
proof -
  have calls:
    "list_all2
      (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
        direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_costs (range_tree_child_list P a bs)"
    using direct_insert_costed_partition_loop_state_child_cost_calls_below
      [OF run] by blast
  then show ?thesis
  proof (induction rule: list_all2_induct)
    case Nil
    then show ?case by simp
  next
    case (Cons c_child child_costs U_child child_ranges)
    obtain S_child B_child d_child B_child' where child:
        "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child"
      and child_pre: "bmssp_pre_full d S_child B_child"
      and child_reaches: "\<forall>x\<in>S_child. reachable s x"
      and child_card: "card S_child \<le> M_of l"
      and child_below: "\<forall>x\<in>S_child. below_bound (d x) B_child"
      using Cons.hyps by blast
    have head:
      "c_child \<le> level_range_cost_bound A R L U_child"
      by (rule child_bound[OF child child_pre _ child_card])
        (use child_reaches child_below in blast)+
    show ?case
      using head Cons.IH Cons.hyps by simp
  qed
qed

theorem direct_insert_costed_partition_loop_state_child_cost_bounds_with_invariants:
  "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs \<Longrightarrow>
    P \<subseteq> V \<Longrightarrow>
    k * card P \<le> cap \<Longrightarrow>
    tree_antichain P \<Longrightarrow>
    (\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child;
          k * card S_child \<le> cap;
          tree_antichain S_child\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child) \<Longrightarrow>
    list_all2 (\<lambda>c_child U_child.
      c_child \<le> level_range_cost_bound A R L U_child)
    child_costs (range_tree_child_list P a bs)"
and direct_insert_costed_bmssp_child_cost_bounds_with_invariants_trivial:
  "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule:
    direct_insert_costed_partition_loop_state_direct_insert_costed_bmssp.inducts)
  case (Direct_Insert_Costed_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  then show ?case
    by simp
next
  case (Direct_Insert_Costed_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  then show ?case
    by simp
next
  case (Direct_Insert_Costed_State_Step D M_of l Bmax S_pull beta D_pull B d
      P a b B' d' k cap \<Delta> t h d_child U_child c_child
      direct_edge_batch lower_edge_batch source_batch batch D_next c_pull
      c_direct c_lower c_sources betas bs Us_tail U_tail c_tail
      child_costs_tail c)
  have tail:
    "list_all2 (\<lambda>c_child U_child.
      c_child \<le> level_range_cost_bound A R L U_child)
      child_costs_tail (range_tree_child_list P b bs)"
    using Direct_Insert_Costed_State_Step.IH Direct_Insert_Costed_State_Step.prems
    by blast
  have card_pull: "card S_pull \<le> M_of l"
    using Direct_Insert_Costed_State_Step
    unfolding pull_separates_def by blast
  have below_pull: "\<And>x. x \<in> S_pull \<Longrightarrow> below_bound (d x) (Fin beta)"
  proof -
    fix x
    assume xS: "x \<in> S_pull"
    have "S_pull = split_below d P beta"
      using Direct_Insert_Costed_State_Step by blast
    then show "below_bound (d x) (Fin beta)"
      using xS unfolding split_below_def by auto
  qed
  have pull_k_cap: "k * card S_pull \<le> cap"
  proof -
    have "S_pull = split_below d P beta"
      using Direct_Insert_Costed_State_Step by blast
    then show ?thesis
      using split_below_scaled_card_le
        [OF Direct_Insert_Costed_State_Step.prems(1)
          Direct_Insert_Costed_State_Step.prems(2), of d beta]
      by simp
  qed
  have pull_anti: "tree_antichain S_pull"
  proof -
    have "S_pull = split_below d P beta"
      using Direct_Insert_Costed_State_Step by blast
    then show ?thesis
      using split_below_tree_antichain
        [OF Direct_Insert_Costed_State_Step.prems(3), of d beta]
      by simp
  qed
  have child_run:
    "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
      d_child (Fin b) U_child c_child"
    using Direct_Insert_Costed_State_Step by blast
  have pre_pull: "bmssp_pre_full d S_pull (Fin beta)"
    using Direct_Insert_Costed_State_Step by blast
  have reaches_pull: "\<And>x. x \<in> S_pull \<Longrightarrow> reachable s x"
    using Direct_Insert_Costed_State_Step by blast
  have head:
    "c_child \<le> level_range_cost_bound A R L U_child"
    by (rule Direct_Insert_Costed_State_Step.prems(4)
      [OF child_run pre_pull reaches_pull card_pull below_pull
        pull_k_cap pull_anti])
  show ?case
    using head tail Direct_Insert_Costed_State_Step by simp
next
  case (Direct_Insert_Costed_Base S x \<Delta> M_of t h k cap d B)
  then show ?case
    by simp
next
  case (Direct_Insert_Costed_Step D k cap d S B c_insert t \<Delta> M_of h l
      d' a betas bs B' Us U_loop c_loop child_costs_loop U c)
  then show ?case
    by simp
qed

theorem direct_insert_costed_partition_loop_state_child_amortized_cost_bounds_with_invariants:
  "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs \<Longrightarrow>
    P \<subseteq> V \<Longrightarrow>
    k * card P \<le> cap \<Longrightarrow>
    tree_antichain P \<Longrightarrow>
    (\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child;
          k * card S_child \<le> cap;
          tree_antichain S_child\<rbrakk>
        \<Longrightarrow> c_child \<le>
          bmssp_amortized_cost_bound A R h t q L B_child U_child) \<Longrightarrow>
    list_all2 (\<lambda>c_child UB. case UB of (U_child, B_child) \<Rightarrow>
      c_child \<le> bmssp_amortized_cost_bound A R h t q L B_child U_child)
    child_costs (range_tree_child_bound_pair_list P a betas bs)"
and direct_insert_costed_bmssp_child_amortized_cost_bounds_with_invariants_trivial:
  "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule:
    direct_insert_costed_partition_loop_state_direct_insert_costed_bmssp.inducts)
  case (Direct_Insert_Costed_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  then show ?case
    by simp
next
  case (Direct_Insert_Costed_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  then show ?case
    by simp
next
  case (Direct_Insert_Costed_State_Step D M_of l Bmax S_pull beta D_pull B d
      P a b B' d' k cap \<Delta> t h d_child U_child c_child
      direct_edge_batch lower_edge_batch source_batch batch D_next c_pull
      c_direct c_lower c_sources betas bs Us_tail U_tail c_tail
      child_costs_tail c)
  have tail:
    "list_all2 (\<lambda>c_child UB. case UB of (U_child, B_child) \<Rightarrow>
      c_child \<le> bmssp_amortized_cost_bound A R h t q L B_child U_child)
      child_costs_tail (range_tree_child_bound_pair_list P b betas bs)"
    using Direct_Insert_Costed_State_Step.IH Direct_Insert_Costed_State_Step.prems
    by blast
  have card_pull: "card S_pull \<le> M_of l"
    using Direct_Insert_Costed_State_Step
    unfolding pull_separates_def by blast
  have below_pull: "\<And>x. x \<in> S_pull \<Longrightarrow> below_bound (d x) (Fin beta)"
  proof -
    fix x
    assume xS: "x \<in> S_pull"
    have "S_pull = split_below d P beta"
      using Direct_Insert_Costed_State_Step by blast
    then show "below_bound (d x) (Fin beta)"
      using xS unfolding split_below_def by auto
  qed
  have pull_k_cap: "k * card S_pull \<le> cap"
  proof -
    have "S_pull = split_below d P beta"
      using Direct_Insert_Costed_State_Step by blast
    then show ?thesis
      using split_below_scaled_card_le
        [OF Direct_Insert_Costed_State_Step.prems(1)
          Direct_Insert_Costed_State_Step.prems(2), of d beta]
      by simp
  qed
  have pull_anti: "tree_antichain S_pull"
  proof -
    have "S_pull = split_below d P beta"
      using Direct_Insert_Costed_State_Step by blast
    then show ?thesis
      using split_below_tree_antichain
        [OF Direct_Insert_Costed_State_Step.prems(3), of d beta]
      by simp
  qed
  have child_run:
    "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
      d_child (Fin b) U_child c_child"
    using Direct_Insert_Costed_State_Step by blast
  have pre_pull: "bmssp_pre_full d S_pull (Fin beta)"
    using Direct_Insert_Costed_State_Step by blast
  have reaches_pull: "\<And>x. x \<in> S_pull \<Longrightarrow> reachable s x"
    using Direct_Insert_Costed_State_Step by blast
  have head:
    "c_child \<le>
      bmssp_amortized_cost_bound A R h t q L (Fin beta) U_child"
    by (rule Direct_Insert_Costed_State_Step.prems(4)
      [OF child_run pre_pull reaches_pull card_pull below_pull
        pull_k_cap pull_anti])
  show ?case
    using head tail Direct_Insert_Costed_State_Step by simp
next
  case (Direct_Insert_Costed_Base S x \<Delta> M_of t h k cap d B)
  then show ?case
    by simp
next
  case (Direct_Insert_Costed_Step D k cap d S B c_insert t \<Delta> M_of h l
      d' a betas bs B' Us U_loop c_loop child_costs_loop U c)
  then show ?case
    by simp
qed

text \<open>
  The central loop cost bound separates the four local charges that survive
  after recursive child costs have been bounded: pulled child sources, direct
  edge-range inserts, lower edge-range batches, and source batches.  The list
  functions over @{const range_tree_child_list} and its edge-range variants are
  the combinatorial map from one loop trace to disjoint graph regions.  Their
  disjointness lemmas are what prevent the loop from paying for the same edge
  range repeatedly.
\<close>

theorem direct_insert_costed_partition_loop_state_cost_bound_by_child_sources_and_edge_ranges:
  "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs \<Longrightarrow>
   sound_label d \<Longrightarrow>
   \<exists>child_sources.
    length child_sources = length bs \<and>
    list_all2
      (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
        direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_sources (range_tree_child_list P a bs) \<and>
    c \<le> sum_list child_costs + sum_list (map card child_sources) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs)) +
      h * sum_list (map card child_sources)"
and direct_insert_costed_bmssp_cost_child_sources_and_edge_ranges_trivial:
  "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule:
    direct_insert_costed_partition_loop_state_direct_insert_costed_bmssp.inducts)
  case (Direct_Insert_Costed_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  show ?case
    by (intro exI[of _ "[]"]) simp
next
  case (Direct_Insert_Costed_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  show ?case
    by (intro exI[of _ "[]"]) simp
next
  case (Direct_Insert_Costed_State_Step D M_of l Bmax S_pull beta D_pull B d
      P a b B' d' k cap \<Delta> t h d_child U_child c_child
      direct_edge_batch lower_edge_batch source_batch batch D_next c_pull
      c_direct c_lower c_sources betas bs Us_tail U_tail c_tail
      child_costs_tail c)
  obtain child_sources_tail where len_tail:
      "length child_sources_tail = length bs"
    and sources_tail:
      "list_all2
        (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
          direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l \<and>
          (\<forall>x\<in>S_child. below_bound (d x) B_child))
        child_sources_tail (range_tree_child_list P b bs)"
    and tail_cost:
      "c_tail \<le>
        sum_list child_costs_tail + sum_list (map card child_sources_tail) +
        t * sum_list
          (map card (range_tree_child_direct_edge_range_list P B b betas bs)) +
        h * sum_list
          (map card (range_tree_child_edge_range_list P b betas bs)) +
        h * sum_list (map card child_sources_tail)"
    using Direct_Insert_Costed_State_Step.IH Direct_Insert_Costed_State_Step.prems by blast
  have card_pull: "card S_pull \<le> M_of l"
    using Direct_Insert_Costed_State_Step
    unfolding pull_separates_def by blast
  have below_pull: "\<forall>x\<in>S_pull. below_bound (d x) (Fin beta)"
  proof
    fix x
    assume xS: "x \<in> S_pull"
    have "S_pull = split_below d P beta"
      using Direct_Insert_Costed_State_Step by blast
    then show "below_bound (d x) (Fin beta)"
      using xS unfolding split_below_def by auto
  qed
  have pull_cost: "c_pull \<le> card S_pull"
    using Direct_Insert_Costed_State_Step
    unfolding partition_pull_cost_bound_def by blast
  have child_run:
    "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
      d_child (Fin b) U_child c_child"
    using Direct_Insert_Costed_State_Step by blast
  have child_pre: "bmssp_pre_full d S_pull (Fin beta)"
    using Direct_Insert_Costed_State_Step by blast
  have child_reaches: "\<And>x. x \<in> S_pull \<Longrightarrow> reachable s x"
    using Direct_Insert_Costed_State_Step by blast
  have child_post:
    "bmssp_post_full d S_pull (Fin beta) d_child (Fin b) U_child"
    by (rule direct_insert_costed_bmssp_correct
      [OF child_run Direct_Insert_Costed_State_Step.prems child_pre child_reaches])
  have child_complete: "complete_on d_child U_child"
    using child_post unfolding bmssp_post_full_def by blast
  have U_child_eq: "U_child = range_tree P a (Fin b)"
    using Direct_Insert_Costed_State_Step by blast
  have U_child_reaches: "\<And>u. u \<in> U_child \<Longrightarrow> reachable s u"
    unfolding U_child_eq range_tree_def tree_set_def tree_path_def by blast
  have direct_cost:
    "c_direct \<le> t * card (outgoing_edges_range U_child beta B)"
    by (rule partition_batch_cost_bound_edge_relaxation_pairs_in_bound
      [where d = d_child])
      (use Direct_Insert_Costed_State_Step child_complete U_child_reaches in auto)
  have lower_source_cost:
    "c_lower + c_sources \<le>
      h * card (outgoing_edges_range U_child b (Fin beta)) +
      h * card S_pull"
    by (rule range_costed_split_batch_cost_le_range_card[
        where d = d and S = S_pull and d_child = d_child and b = b
          and beta = beta])
      (use Direct_Insert_Costed_State_Step child_complete U_child_reaches in auto)
  let ?child_sources = "S_pull # child_sources_tail"
  have len: "length ?child_sources = length (b # bs)"
    using len_tail by simp
  have head_source:
    "\<exists>c_child' B_child d_child' B_child'.
      direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_pull B_child
        d_child' B_child' U_child c_child' \<and>
      bmssp_pre_full d S_pull B_child \<and>
      (\<forall>x\<in>S_pull. reachable s x) \<and>
      card S_pull \<le> M_of l \<and>
      (\<forall>x\<in>S_pull. below_bound (d x) B_child)"
    using Direct_Insert_Costed_State_Step card_pull below_pull by blast
  have sources:
    "list_all2
      (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
        direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      ?child_sources (range_tree_child_list P a (b # bs))"
    using head_source sources_tail Direct_Insert_Costed_State_Step by simp
  have cost:
    "c \<le> sum_list (c_child # child_costs_tail) +
      sum_list (map card ?child_sources) +
      t * sum_list
        (map card
          (range_tree_child_direct_edge_range_list P B a (beta # betas) (b # bs))) +
      h * sum_list
        (map card
          (range_tree_child_edge_range_list P a (beta # betas) (b # bs))) +
      h * sum_list (map card ?child_sources)"
  proof -
    have c_eq:
      "c = c_pull + c_direct + c_lower + c_sources + c_child + c_tail"
      using Direct_Insert_Costed_State_Step by blast
    have "c_pull + c_direct + c_lower + c_sources + c_child + c_tail \<le>
        card S_pull +
        t * card (outgoing_edges_range U_child beta B) +
        (h * card (outgoing_edges_range U_child b (Fin beta)) +
          h * card S_pull) +
        c_child +
        (sum_list child_costs_tail + sum_list (map card child_sources_tail) +
          t * sum_list
            (map card (range_tree_child_direct_edge_range_list P B b betas bs)) +
          h * sum_list
            (map card (range_tree_child_edge_range_list P b betas bs)) +
          h * sum_list (map card child_sources_tail))"
      using pull_cost direct_cost lower_source_cost tail_cost by linarith
    also have "\<dots> =
        sum_list (c_child # child_costs_tail) +
        sum_list (map card ?child_sources) +
        t * (card (outgoing_edges_range U_child beta B) +
          sum_list
            (map card (range_tree_child_direct_edge_range_list P B b betas bs))) +
        h * (card (outgoing_edges_range U_child b (Fin beta)) +
          sum_list
            (map card (range_tree_child_edge_range_list P b betas bs))) +
        h * sum_list (map card ?child_sources)"
      by (simp add: algebra_simps)
    also have "\<dots> =
        sum_list (c_child # child_costs_tail) +
        sum_list (map card ?child_sources) +
        t * sum_list
          (map card
            (range_tree_child_direct_edge_range_list P B a (beta # betas) (b # bs))) +
        h * sum_list
          (map card
            (range_tree_child_edge_range_list P a (beta # betas) (b # bs))) +
        h * sum_list (map card ?child_sources)"
      using U_child_eq by simp
    finally show ?thesis
      using c_eq by simp
  qed
  show ?case
    by (intro exI[of _ ?child_sources] conjI)
      (use len sources cost in simp_all)
next
  case (Direct_Insert_Costed_Base S x \<Delta> M_of t h k cap d B)
  show ?case
    by simp
next
  case (Direct_Insert_Costed_Step D k cap d S B c_insert t \<Delta> M_of h l
      d' a betas bs B' Us U_loop c_loop child_costs_loop U c)
  show ?case
    by simp
qed

theorem direct_insert_costed_partition_loop_state_cost_from_child_source_and_edge_range_bounds:
  assumes run:
    "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child U_child.
        c_child \<le> level_range_cost_bound A R L U_child)
        child_costs (range_tree_child_list P a bs)"
    and source_progress:
      "\<And>S_child B_child d_child B_child' U_child c_child.
        \<lbrakk>direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child\<rbrakk>
        \<Longrightarrow> card S_child \<le> card U_child"
  shows "c \<le>
    A * L * card (range_tree_chain P a bs B') +
    R * card (outgoing_edges (range_tree_chain P a bs B')) +
    t * sum_list
      (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
    h * sum_list
      (map card (range_tree_child_edge_range_list P a betas bs)) +
    (Suc h) * card (range_tree_chain P a bs B')"
proof -
  obtain child_sources where sources:
      "list_all2
        (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
          direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l \<and>
          (\<forall>x\<in>S_child. below_bound (d x) B_child))
        child_sources (range_tree_child_list P a bs)"
    and cost:
      "c \<le> sum_list child_costs + sum_list (map card child_sources) +
        t * sum_list
          (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
        h * sum_list
          (map card (range_tree_child_edge_range_list P a betas bs)) +
        h * sum_list (map card child_sources)"
    using direct_insert_costed_partition_loop_state_cost_bound_by_child_sources_and_edge_ranges
      [OF run sound] by blast
  have mono: "nondecreasing_from a bs"
    by (rule direct_insert_costed_partition_loop_state_mono[OF run])
  have source_dom:
    "list_all2 (\<lambda>S_child U_child. card S_child \<le> card U_child)
      child_sources (range_tree_child_list P a bs)"
    using sources
  proof (induction rule: list_all2_induct)
    case Nil
    then show ?case by simp
  next
    case (Cons S_child child_sources U_child child_sets)
    obtain c_child B_child d_child B_child' where child:
        "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child"
      and child_pre: "bmssp_pre_full d S_child B_child"
      and child_reaches: "\<forall>x\<in>S_child. reachable s x"
      and child_card: "card S_child \<le> M_of l"
      and child_below: "\<forall>x\<in>S_child. below_bound (d x) B_child"
      using Cons.hyps by blast
    have head: "card S_child \<le> card U_child"
      by (rule source_progress[OF child child_pre _ child_card])
        (use child_reaches child_below in blast)+
    show ?case
      using head Cons.IH Cons.hyps by simp
  qed
  have source_sum:
    "sum_list (map card child_sources) \<le>
      card (range_tree_chain P a bs B')"
    by (rule sum_card_dominated_by_range_tree_child_list_le_chain
      [OF mono source_dom])
  have child_sum:
    "sum_list child_costs \<le>
      A * L * card (range_tree_chain P a bs B') +
      R * card (outgoing_edges (range_tree_chain P a bs B'))"
    by (rule child_costs_le_level_range_child_list_bound
      [OF mono child_cost_bounds])
  have "c \<le>
      A * L * card (range_tree_chain P a bs B') +
      R * card (outgoing_edges (range_tree_chain P a bs B')) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs)) +
      sum_list (map card child_sources) +
      h * sum_list (map card child_sources)"
    using cost child_sum by linarith
  also have "\<dots> \<le>
      A * L * card (range_tree_chain P a bs B') +
      R * card (outgoing_edges (range_tree_chain P a bs B')) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs)) +
      (Suc h) * card (range_tree_chain P a bs B')"
  proof -
    have source_part:
      "sum_list (map card child_sources) +
        h * sum_list (map card child_sources) \<le>
       Suc h * card (range_tree_chain P a bs B')"
    proof -
      have h_part:
        "h * sum_list (map card child_sources) \<le>
          h * card (range_tree_chain P a bs B')"
        using source_sum by simp
      have "sum_list (map card child_sources) +
          h * sum_list (map card child_sources) \<le>
        card (range_tree_chain P a bs B') +
          h * card (range_tree_chain P a bs B')"
        using source_sum h_part by linarith
      then show ?thesis
        by (simp add: algebra_simps)
    qed
    show ?thesis
      using source_part by linarith
  qed
  finally show ?thesis .
qed

theorem direct_insert_costed_partition_loop_state_cost_from_child_source_and_amortized_bounds:
  assumes run:
    "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child UB. case UB of (U_child, B_child) \<Rightarrow>
        c_child \<le> bmssp_amortized_cost_bound A R h t q L B_child U_child)
        child_costs (range_tree_child_bound_pair_list P a betas bs)"
    and source_progress:
      "\<And>S_child B_child d_child B_child' U_child c_child.
        \<lbrakk>direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child\<rbrakk>
        \<Longrightarrow> card S_child \<le> card U_child"
  shows "c \<le>
    A * L * card (range_tree_chain P a bs B') +
    (R + q * h) * card (outgoing_edges (range_tree_chain P a bs B')) +
    t * sum_list
      (map card (range_tree_child_zero_edge_range_list P a betas bs)) +
    t * sum_list
      (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
    h * sum_list
      (map card (range_tree_child_edge_range_list P a betas bs)) +
    (Suc h) * card (range_tree_chain P a bs B')"
proof -
  obtain child_sources where sources:
      "list_all2
        (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
          direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l \<and>
          (\<forall>x\<in>S_child. below_bound (d x) B_child))
        child_sources (range_tree_child_list P a bs)"
    and cost:
      "c \<le> sum_list child_costs + sum_list (map card child_sources) +
        t * sum_list
          (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
        h * sum_list
          (map card (range_tree_child_edge_range_list P a betas bs)) +
        h * sum_list (map card child_sources)"
    using direct_insert_costed_partition_loop_state_cost_bound_by_child_sources_and_edge_ranges
      [OF run sound] by blast
  have mono: "nondecreasing_from a bs"
    by (rule direct_insert_costed_partition_loop_state_mono[OF run])
  have source_dom:
    "list_all2 (\<lambda>S_child U_child. card S_child \<le> card U_child)
      child_sources (range_tree_child_list P a bs)"
    using sources
  proof (induction rule: list_all2_induct)
    case Nil
    then show ?case by simp
  next
    case (Cons S_child child_sources U_child child_sets)
    obtain c_child B_child d_child B_child' where child:
        "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child"
      and child_pre: "bmssp_pre_full d S_child B_child"
      and child_reaches: "\<forall>x\<in>S_child. reachable s x"
      and child_card: "card S_child \<le> M_of l"
      and child_below: "\<forall>x\<in>S_child. below_bound (d x) B_child"
      using Cons.hyps by blast
    have head: "card S_child \<le> card U_child"
      by (rule source_progress[OF child child_pre _ child_card])
        (use child_reaches child_below in blast)+
    show ?case
      using head Cons.IH Cons.hyps by simp
  qed
  have source_sum:
    "sum_list (map card child_sources) \<le>
      card (range_tree_chain P a bs B')"
    by (rule sum_card_dominated_by_range_tree_child_list_le_chain
      [OF mono source_dom])
  have child_sum_raw:
    "sum_list child_costs \<le>
      A * L * sum_list (map card (range_tree_child_list P a bs)) +
      (R + q * h) *
        sum_list (map (\<lambda>U. card (outgoing_edges U))
          (range_tree_child_list P a bs)) +
      t * sum_list
        (map card (range_tree_child_zero_edge_range_list P a betas bs))"
    by (rule sum_bmssp_amortized_child_bounds_le[OF child_cost_bounds])
  have child_card_sum:
    "sum_list (map card (range_tree_child_list P a bs)) \<le>
      card (range_tree_chain P a bs B')"
    by (rule card_range_tree_child_list_le_chain[OF mono])
  have child_out_sum:
    "sum_list (map (\<lambda>U. card (outgoing_edges U))
        (range_tree_child_list P a bs)) \<le>
      card (outgoing_edges (range_tree_chain P a bs B'))"
    by (rule card_outgoing_edges_range_tree_child_list_le_chain[OF mono])
  have child_sum:
    "sum_list child_costs \<le>
      A * L * card (range_tree_chain P a bs B') +
      (R + q * h) * card (outgoing_edges (range_tree_chain P a bs B')) +
      t * sum_list
        (map card (range_tree_child_zero_edge_range_list P a betas bs))"
  proof -
    have vterm:
      "A * L * sum_list (map card (range_tree_child_list P a bs)) \<le>
       A * L * card (range_tree_chain P a bs B')"
      using child_card_sum by simp
    have eterm:
      "(R + q * h) *
        sum_list (map (\<lambda>U. card (outgoing_edges U))
          (range_tree_child_list P a bs)) \<le>
       (R + q * h) * card (outgoing_edges (range_tree_chain P a bs B'))"
      using child_out_sum by simp
    show ?thesis
      using child_sum_raw vterm eterm by linarith
  qed
  have "c \<le>
      A * L * card (range_tree_chain P a bs B') +
      (R + q * h) * card (outgoing_edges (range_tree_chain P a bs B')) +
      t * sum_list
        (map card (range_tree_child_zero_edge_range_list P a betas bs)) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs)) +
      sum_list (map card child_sources) +
      h * sum_list (map card child_sources)"
    using cost child_sum by linarith
  also have "\<dots> \<le>
      A * L * card (range_tree_chain P a bs B') +
      (R + q * h) * card (outgoing_edges (range_tree_chain P a bs B')) +
      t * sum_list
        (map card (range_tree_child_zero_edge_range_list P a betas bs)) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs)) +
      (Suc h) * card (range_tree_chain P a bs B')"
  proof -
    have source_part:
      "sum_list (map card child_sources) +
        h * sum_list (map card child_sources) \<le>
       Suc h * card (range_tree_chain P a bs B')"
    proof -
      have h_part:
        "h * sum_list (map card child_sources) \<le>
          h * card (range_tree_chain P a bs B')"
        using source_sum by simp
      have "sum_list (map card child_sources) +
          h * sum_list (map card child_sources) \<le>
        card (range_tree_chain P a bs B') +
          h * card (range_tree_chain P a bs B')"
        using source_sum h_part by linarith
      then show ?thesis
        by (simp add: algebra_simps)
    qed
    show ?thesis
      using source_part by linarith
  qed
  finally show ?thesis .
qed

text \<open>
  The amortised closing theorem below keeps the direct-insert range term visible
  because the bucketed implementation has a sharper accounting story for it.
  The child calls contribute a lower-level amortised bound, the source-progress
  hypothesis absorbs the pulled source sets into completed child ranges, and the
  edge-range disjointness lemmas collapse the direct and lower edge lists into
  the outgoing-edge terms of the parent output.
\<close>

theorem direct_insert_costed_partition_loop_state_closes_amortized_bound_from_child_costs:
  assumes run:
    "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child UB. case UB of (U_child, B_child) \<Rightarrow>
        c_child \<le> bmssp_amortized_cost_bound A R h t q L B_child U_child)
        child_costs (range_tree_child_bound_pair_list P a betas bs)"
    and source_factor: "Suc h \<le> A"
    and source_progress:
      "\<And>S_child B_child d_child B_child' U_child c_child.
        \<lbrakk>direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child\<rbrakk>
        \<Longrightarrow> card S_child \<le> card U_child"
  shows "c \<le> bmssp_amortized_cost_bound A R h t (Suc q) (Suc L) B U"
proof -
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
  have range_subset:
    "outgoing_edges_range (range_tree_chain P a bs B') 0 B \<subseteq>
      outgoing_edges_range U 0 B"
    by (rule outgoing_edges_range_mono_sources[OF chain_subset])
  have card_range_le:
    "card (outgoing_edges_range (range_tree_chain P a bs B') 0 B) \<le>
      card (outgoing_edges_range U 0 B)"
    by (rule card_mono[OF finite_outgoing_edges_range range_subset])
  have mono: "nondecreasing_from a bs"
    by (rule direct_insert_costed_partition_loop_state_mono[OF run])
  have beta_bounds: "bounds_le B betas"
    by (rule direct_insert_costed_partition_loop_state_beta_bounds[OF run])
  have cost:
    "c \<le>
      A * L * card (range_tree_chain P a bs B') +
      (R + q * h) * card (outgoing_edges (range_tree_chain P a bs B')) +
      t * sum_list
        (map card (range_tree_child_zero_edge_range_list P a betas bs)) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs)) +
      (Suc h) * card (range_tree_chain P a bs B')"
    by (rule direct_insert_costed_partition_loop_state_cost_from_child_source_and_amortized_bounds
      [OF run sound child_cost_bounds source_progress])
  have lower_sum:
    "sum_list (map card (range_tree_child_edge_range_list P a betas bs))
      \<le> card (outgoing_edges (range_tree_chain P a bs B'))"
    by (rule sum_card_range_tree_child_edge_range_list_le_outgoing_edges_chain
      [OF mono])
  have direct_sum:
    "sum_list
        (map card (range_tree_child_zero_edge_range_list P a betas bs)) +
     sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs))
     \<le> card (outgoing_edges_range (range_tree_chain P a bs B') 0 B)"
    by (rule sum_card_range_tree_child_zero_direct_edge_ranges_le_outgoing_edges_range_chain
      [OF mono beta_bounds])
  have vertex_part:
    "A * L * card (range_tree_chain P a bs B') +
      Suc h * card (range_tree_chain P a bs B') \<le>
     A * Suc L * card U"
  proof -
    have source_term:
      "Suc h * card (range_tree_chain P a bs B') \<le>
       A * card U"
    proof -
      have "Suc h * card (range_tree_chain P a bs B') \<le>
          A * card (range_tree_chain P a bs B')"
        by (rule mult_right_mono[OF source_factor]) simp
      also have "\<dots> \<le> A * card U"
        using card_chain_le by simp
      finally show ?thesis .
    qed
    have child_term:
      "A * L * card (range_tree_chain P a bs B') \<le>
       A * L * card U"
      using card_chain_le by simp
    have "A * L * card U + A * card U = A * Suc L * card U"
      by (simp add: algebra_simps)
    then show ?thesis
      using child_term source_term by linarith
  qed
  have edge_part:
    "(R + q * h) * card (outgoing_edges (range_tree_chain P a bs B')) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs))
     \<le> (R + Suc q * h) * card (outgoing_edges U)"
  proof -
    have lower_term:
      "h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs))
       \<le> h * card (outgoing_edges (range_tree_chain P a bs B'))"
      using lower_sum by simp
    have chain_term:
      "(R + q * h) * card (outgoing_edges (range_tree_chain P a bs B')) +
        h * card (outgoing_edges (range_tree_chain P a bs B')) =
       (R + Suc q * h) *
        card (outgoing_edges (range_tree_chain P a bs B'))"
      by (simp add: algebra_simps)
    have to_chain:
      "(R + q * h) * card (outgoing_edges (range_tree_chain P a bs B')) +
        h * sum_list
          (map card (range_tree_child_edge_range_list P a betas bs))
       \<le> (R + Suc q * h) *
        card (outgoing_edges (range_tree_chain P a bs B'))"
      using lower_term chain_term by linarith
    have to_U:
      "(R + Suc q * h) *
        card (outgoing_edges (range_tree_chain P a bs B')) \<le>
       (R + Suc q * h) * card (outgoing_edges U)"
      using card_out_le by simp
    show ?thesis
      using to_chain to_U by linarith
  qed
  have direct_part:
    "t * sum_list
        (map card (range_tree_child_zero_edge_range_list P a betas bs)) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs))
     \<le> t * card (outgoing_edges_range U 0 B)"
  proof -
    have "t * (sum_list
        (map card (range_tree_child_zero_edge_range_list P a betas bs)) +
      sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)))
      \<le> t * card (outgoing_edges_range (range_tree_chain P a bs B') 0 B)"
      using direct_sum by simp
    also have "\<dots> \<le> t * card (outgoing_edges_range U 0 B)"
      using card_range_le by simp
    finally show ?thesis
      by (simp add: algebra_simps)
  qed
  have "c \<le>
      A * Suc L * card U +
      (R + Suc q * h) * card (outgoing_edges U) +
      t * card (outgoing_edges_range U 0 B)"
    using cost vertex_part edge_part direct_part by linarith
  then show ?thesis
    unfolding bmssp_amortized_cost_bound_def .
qed

text \<open>
  The final level-bound theorem is the non-amortised companion used by the
  abstract headline recurrence.  It closes the same loop skeleton, but leaves
  the direct and lower edge-range sums explicit rather than folding them into
  @{const bmssp_amortized_cost_bound}.  This gives later theories the freedom
  to plug in either an abstract partition budget or the bucketed amortised
  budget without changing the semantic development.
\<close>

theorem direct_insert_costed_partition_loop_state_closes_level_bound_from_child_costs_and_edge_ranges:
  assumes run:
    "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child U_child.
        c_child \<le> level_range_cost_bound A R L U_child)
        child_costs (range_tree_child_list P a bs)"
    and source_factor: "Suc h \<le> A"
    and source_progress:
      "\<And>S_child B_child d_child B_child' U_child c_child.
        \<lbrakk>direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child\<rbrakk>
        \<Longrightarrow> card S_child \<le> card U_child"
  shows "c \<le>
    A * Suc L * card U + R * card (outgoing_edges U) +
    t * sum_list
      (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
    h * sum_list
      (map card (range_tree_child_edge_range_list P a betas bs))"
proof -
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
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs)) +
      Suc h * card (range_tree_chain P a bs B')"
    by (rule direct_insert_costed_partition_loop_state_cost_from_child_source_and_edge_range_bounds
      [OF run sound child_cost_bounds source_progress])
  have "c \<le>
      A * L * card U + R * card (outgoing_edges U) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs)) +
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
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs))"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

end

end
