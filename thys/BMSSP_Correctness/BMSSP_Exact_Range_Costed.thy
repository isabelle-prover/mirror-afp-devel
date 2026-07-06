theory BMSSP_Exact_Range_Costed
  imports BMSSP_Range_Costed
begin

section \<open>Exact Split Range-Costed Runs\<close>

text \<open>
  The range-costed relation records the algorithm's range accounting, but leaves
  the pulled child source abstract.  The exact variant below keeps the same
  cost and range information while additionally recording that each pull source
  is exactly the lower label split used by the operational algorithm.  It
  refines the existing range-costed relation, so the established correctness
  and cost lemmas remain reusable.

  This extra equality is small syntactically and important analytically.  A
  pull operation returns a child source set and a child bound.  For correctness
  it is enough to know that the child call satisfies the BMSSP precondition.
  For progress and runtime, however, the source set must be identified with the
  mathematical split of the parent sources below the child bound.  Only then can
  the proof inherit the antichain and scaled-cardinality facts that were proved
  for lower splits.

  The theory therefore sits between range synchronisation and direct insertion.
  It keeps the range slices, child-cost list, and edge/source batch split from
  the preceding layer, while adding enough exactness to discharge the source
  progress side conditions needed by the recurrence.  Later theories refine
  this one by splitting edge batches further; they rely on the exact source
  information introduced here rather than reproving it.

  No new algorithm is introduced.  Each theorem either forgets the exactness to
  recover the split-range relation, or uses exactness to derive stronger cost
  premises for the same loop trace.
\<close>

context unique_shortest_digraph
begin

inductive exact_split_range_costed_partition_loop_state
  and exact_split_range_costed_bmssp where
  Exact_Split_Range_State_Done:
    "keys_of D = {} \<Longrightarrow>
     bound_le (Fin a) B \<Longrightarrow>
     complete_on d' (bound_tree P B) \<Longrightarrow>
     exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
       [] [] B [range_tree P a B]
       (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a B])) 0 []"
| Exact_Split_Range_State_Stop:
    "bound_le (Fin a) B \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     k * cap \<le> card (bound_tree P (Fin a)) \<Longrightarrow>
     exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
       [] [] (Fin a) [range_tree P a (Fin a)]
       (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a (Fin a)])) 0 []"
| Exact_Split_Range_State_Step:
    "pull_separates D (M_of l) Bmax S_pull beta D_pull \<Longrightarrow>
     bound_le (Fin beta) B \<Longrightarrow>
     bmssp_pre_full d S_pull (Fin beta) \<Longrightarrow>
     S_pull = split_below d P beta \<Longrightarrow>
     (\<forall>x\<in>S_pull. reachable s x) \<Longrightarrow>
     a \<le> b \<Longrightarrow>
     bound_le (Fin a) B' \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     card (bound_tree P (Fin a)) < k * cap \<Longrightarrow>
     exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
       d_child (Fin b) U_child c_child \<Longrightarrow>
     U_child = range_tree P a (Fin b) \<Longrightarrow>
     complete_preserved d_child d' U_child \<Longrightarrow>
     edge_batch = edge_relaxation_pairs_between d_child U_child b beta \<Longrightarrow>
     source_batch = label_pairs_between d S_pull b beta \<Longrightarrow>
     batch = edge_batch @ source_batch \<Longrightarrow>
     D_next = batch_min_update D_pull batch \<Longrightarrow>
     partition_pull_cost_bound c_pull S_pull \<Longrightarrow>
     partition_batch_cost_bound c_edges t edge_batch \<Longrightarrow>
     partition_batch_cost_bound c_sources h source_batch \<Longrightarrow>
     exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d'
       D_next b betas bs B' Us_tail U_tail c_tail child_costs_tail \<Longrightarrow>
     c = c_pull + c_edges + c_sources + c_child + c_tail \<Longrightarrow>
     exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
       (beta # betas) (b # bs) B'
       (range_tree P a (Fin b) # Us_tail)
       (bound_tree P (Fin a) \<union>
        \<Union>(set (range_tree P a (Fin b) # Us_tail))) c
       (c_child # child_costs_tail)"
| Exact_Split_Range_Cost_Base:
    "S = {x} \<Longrightarrow>
     exact_split_range_costed_bmssp \<Delta> M_of t h k cap 0 d S B
       (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
       (base_case_bound k x B)
       (base_case_vertices k x B)
       (base_case_scan_cost \<Delta> k x B)"
| Exact_Split_Range_Cost_Step:
    "D = label_partition_view
       (find_pivots_label_capped k cap d S B)
       (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
     partition_initial_insert_cost_bound c_insert t
       (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
     exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
       (find_pivots_label_capped k cap d S B)
       (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
       Us U_loop c_loop child_costs_loop \<Longrightarrow>
     complete_on d'
       {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
     U = U_loop \<union>
      {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
      c = fp_iter_capped_scan_cost k cap d S S B + c_insert + c_loop \<Longrightarrow>
      exact_split_range_costed_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"

text \<open>
  The defining difference from the split-range relation is the premise
  \<open>S_pull = split_below d P beta\<close> in the loop step.  This says that the
  implementation-level pull has not merely produced an admissible child set; it
  has produced exactly the semantic lower split of the parent problem.  The rest
  of the constructor mirrors the earlier relation: edge and source batches are
  charged separately, the child output is the next @{const range_tree}, and the
  total cost is the sum of local and recursive costs.

  The equality to @{const split_below} is deliberately stored at the point where
  the pull happens.  Downstream proofs then extract it from the derivation tree
  rather than reconstructing it from the partition invariant.  This keeps the
  cost proofs focused on summing costs and ranges.
\<close>

inductive_cases exact_split_range_costed_bmssp_zeroE:
  "exact_split_range_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"

inductive_cases exact_split_range_costed_bmssp_SucE:
  "exact_split_range_costed_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"

theorem exact_split_range_costed_refines_split_range_costed:
  shows
    "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
       betas bs B' Us U c child_costs \<Longrightarrow>
     split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
       betas bs B' Us U c child_costs"
  and
    "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
     split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
proof (induction rule:
    exact_split_range_costed_partition_loop_state_exact_split_range_costed_bmssp.inducts)
  case (Exact_Split_Range_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  show ?case
    by (rule Split_Range_State_Done)
      (use Exact_Split_Range_State_Done in auto)
next
  case (Exact_Split_Range_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  show ?case
    by (rule Split_Range_State_Stop)
      (use Exact_Split_Range_State_Stop in auto)
next
  case (Exact_Split_Range_State_Step D M_of l Bmax S_pull beta D_pull B d
      P a b B' d' k cap \<Delta> t h d_child U_child c_child edge_batch
      source_batch batch D_next c_pull c_edges c_sources betas bs Us_tail
      U_tail c_tail child_costs_tail c)
  show ?case
    by (rule Split_Range_State_Step)
      (use Exact_Split_Range_State_Step in auto)
next
  case (Exact_Split_Range_Cost_Base S x \<Delta> M_of t h k cap d B)
  show ?case
    by (rule Split_Range_Cost_Base)
      (use Exact_Split_Range_Cost_Base in auto)
next
  case (Exact_Split_Range_Cost_Step D k cap d S B c_insert t \<Delta> M_of h l
      d' a betas bs B' Us U_loop c_loop child_costs_loop U c)
  show ?case
    by (rule Split_Range_Cost_Step)
      (use Exact_Split_Range_Cost_Step in auto)
qed

theorem exact_split_range_costed_bmssp_correct:
  assumes run:
    "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "bmssp_post_full d S B d' B' U"
  by (rule split_range_costed_bmssp_correct
    [OF exact_split_range_costed_refines_split_range_costed(2)[OF run]
      sound pre S_reaches])

theorem finite_initial_label_exact_split_range_costed_top_level_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and run:
      "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d'"
  by (rule finite_initial_label_split_range_costed_top_level_correct
    [OF all_reachable exact_split_range_costed_refines_split_range_costed(2)
      [OF run]])

text \<open>
  The refinement theorem
  @{thm exact_split_range_costed_refines_split_range_costed(1)} is the
  compatibility layer: forgetting the exact source equality gives a valid
  split-range run.  Correctness and top-level SSSP correctness are then inherited
  immediately from the previous theory.

  The remaining results use the exact source equality in the other direction.
  They expose the child calls together with the lower-split facts needed for the
  induction hypothesis: bounded cardinality, reachability, and labels below the
  child bound.  Those facts are the source-progress side of the runtime proof.
\<close>

theorem exact_split_range_costed_partition_loop_state_child_cost_calls_below:
  "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs \<Longrightarrow>
   length child_costs = length bs \<and>
   list_all2
      (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
        exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_costs (range_tree_child_list P a bs)"
and exact_split_range_costed_bmssp_child_cost_calls_below_trivial:
  "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule:
    exact_split_range_costed_partition_loop_state_exact_split_range_costed_bmssp.inducts)
  case (Exact_Split_Range_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  show ?case
    by simp
next
  case (Exact_Split_Range_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  show ?case
    by simp
next
  case (Exact_Split_Range_State_Step D M_of l Bmax S_pull beta D_pull B d
      P a b B' d' k cap \<Delta> t h d_child U_child c_child edge_batch
      source_batch batch D_next c_pull c_edges c_sources betas bs Us_tail
      U_tail c_tail child_costs_tail c)
  have tail:
    "length child_costs_tail = length bs \<and>
     list_all2
      (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
        exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_costs_tail (range_tree_child_list P b bs)"
    using Exact_Split_Range_State_Step.IH by blast
  have card_pull: "card S_pull \<le> M_of l"
    using Exact_Split_Range_State_Step
    unfolding pull_separates_def by blast
  have below_pull: "\<forall>x\<in>S_pull. below_bound (d x) (Fin beta)"
  proof
    fix x
    assume xS: "x \<in> S_pull"
    have "S_pull = split_below d P beta"
      using Exact_Split_Range_State_Step by blast
    then show "below_bound (d x) (Fin beta)"
      using xS unfolding split_below_def by auto
  qed
  have head:
    "\<exists>S_child B_child d_child' B_child'.
      exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
        d_child' B_child' U_child c_child \<and>
      bmssp_pre_full d S_child B_child \<and>
      (\<forall>x\<in>S_child. reachable s x) \<and>
      card S_child \<le> M_of l \<and>
      (\<forall>x\<in>S_child. below_bound (d x) B_child)"
    using Exact_Split_Range_State_Step card_pull below_pull by blast
  show ?case
    using tail head Exact_Split_Range_State_Step by simp
next
  case (Exact_Split_Range_Cost_Base S x \<Delta> M_of t h k cap d B)
  show ?case
    by simp
next
  case (Exact_Split_Range_Cost_Step D k cap d S B c_insert t \<Delta> M_of h l
      d' a betas bs B' Us U_loop c_loop child_costs_loop U c)
  show ?case
    by simp
qed

theorem exact_split_range_costed_partition_loop_state_child_cost_bounds:
  assumes run:
    "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
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
        exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_costs (range_tree_child_list P a bs)"
    using exact_split_range_costed_partition_loop_state_child_cost_calls_below
      [OF run] by blast
  then show ?thesis
  proof (induction rule: list_all2_induct)
    case Nil
    then show ?case by simp
  next
    case (Cons c_child child_costs U_child child_ranges)
    obtain S_child B_child d_child B_child' where child:
        "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
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

theorem exact_split_range_costed_partition_loop_state_child_cost_bounds_with_invariants:
  "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs \<Longrightarrow>
    P \<subseteq> V \<Longrightarrow>
    k * card P \<le> cap \<Longrightarrow>
    tree_antichain P \<Longrightarrow>
    (\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
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
and exact_split_range_costed_bmssp_child_cost_bounds_with_invariants_trivial:
  "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule:
    exact_split_range_costed_partition_loop_state_exact_split_range_costed_bmssp.inducts)
  case (Exact_Split_Range_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  then show ?case
    by simp
next
  case (Exact_Split_Range_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  then show ?case
    by simp
next
  case (Exact_Split_Range_State_Step D M_of l Bmax S_pull beta D_pull B d
      P a b B' d' k cap \<Delta> t h d_child U_child c_child edge_batch
      source_batch batch D_next c_pull c_edges c_sources betas bs Us_tail
      U_tail c_tail child_costs_tail c)
  have tail:
    "list_all2 (\<lambda>c_child U_child.
      c_child \<le> level_range_cost_bound A R L U_child)
      child_costs_tail (range_tree_child_list P b bs)"
    using Exact_Split_Range_State_Step.IH Exact_Split_Range_State_Step.prems
    by blast
  have card_pull: "card S_pull \<le> M_of l"
    using Exact_Split_Range_State_Step
    unfolding pull_separates_def by blast
  have below_pull: "\<And>x. x \<in> S_pull \<Longrightarrow> below_bound (d x) (Fin beta)"
  proof -
    fix x
    assume xS: "x \<in> S_pull"
    have "S_pull = split_below d P beta"
      using Exact_Split_Range_State_Step by blast
    then show "below_bound (d x) (Fin beta)"
      using xS unfolding split_below_def by auto
  qed
  have pull_k_cap: "k * card S_pull \<le> cap"
  proof -
    have "S_pull = split_below d P beta"
      using Exact_Split_Range_State_Step by blast
    then show ?thesis
      using split_below_scaled_card_le
        [OF Exact_Split_Range_State_Step.prems(1)
          Exact_Split_Range_State_Step.prems(2), of d beta]
      by simp
  qed
  have pull_anti: "tree_antichain S_pull"
  proof -
    have "S_pull = split_below d P beta"
      using Exact_Split_Range_State_Step by blast
    then show ?thesis
      using split_below_tree_antichain
        [OF Exact_Split_Range_State_Step.prems(3), of d beta]
      by simp
  qed
  have child_run:
    "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
      d_child (Fin b) U_child c_child"
    using Exact_Split_Range_State_Step by blast
  have pre_pull: "bmssp_pre_full d S_pull (Fin beta)"
    using Exact_Split_Range_State_Step by blast
  have reaches_pull: "\<And>x. x \<in> S_pull \<Longrightarrow> reachable s x"
    using Exact_Split_Range_State_Step by blast
  have head:
    "c_child \<le> level_range_cost_bound A R L U_child"
    by (rule Exact_Split_Range_State_Step.prems(4)
      [OF child_run pre_pull reaches_pull card_pull below_pull
        pull_k_cap pull_anti])
  show ?case
    using head tail Exact_Split_Range_State_Step by simp
next
  case (Exact_Split_Range_Cost_Base S x \<Delta> M_of t h k cap d B)
  then show ?case
    by simp
next
  case (Exact_Split_Range_Cost_Step D k cap d S B c_insert t \<Delta> M_of h l
      d' a betas bs B' Us U_loop c_loop child_costs_loop U c)
  then show ?case
    by simp
qed

text \<open>
  The child-source extraction theorem packages one loop trace as a list of
  source sets aligned with @{const range_tree_child_list}.  Alignment matters:
  each source set is charged against the same range slice as its recursive child
  call.  Once this list exists, subsequent cost theorems can use ordinary
  list-wise reasoning instead of induction over the full operational relation.
\<close>

theorem exact_split_range_costed_partition_loop_state_child_sources_below:
  "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs \<Longrightarrow>
   \<exists>child_sources.
    length child_sources = length bs \<and>
    list_all2
      (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
        exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_sources (range_tree_child_list P a bs)"
and exact_split_range_costed_bmssp_child_sources_below_trivial:
  "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule:
    exact_split_range_costed_partition_loop_state_exact_split_range_costed_bmssp.inducts)
  case (Exact_Split_Range_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  show ?case
    by (intro exI[of _ "[]"]) simp
next
  case (Exact_Split_Range_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  show ?case
    by (intro exI[of _ "[]"]) simp
next
  case (Exact_Split_Range_State_Step D M_of l Bmax S_pull beta D_pull B d
      P a b B' d' k cap \<Delta> t h d_child U_child c_child edge_batch
      source_batch batch D_next c_pull c_edges c_sources betas bs Us_tail
      U_tail c_tail child_costs_tail c)
  obtain child_sources_tail where len_tail:
      "length child_sources_tail = length bs"
    and tail:
      "list_all2
        (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
          exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l \<and>
          (\<forall>x\<in>S_child. below_bound (d x) B_child))
        child_sources_tail (range_tree_child_list P b bs)"
    using Exact_Split_Range_State_Step.IH by blast
  have card_pull: "card S_pull \<le> M_of l"
    using Exact_Split_Range_State_Step
    unfolding pull_separates_def by blast
  have below_pull: "\<forall>x\<in>S_pull. below_bound (d x) (Fin beta)"
  proof
    fix x
    assume xS: "x \<in> S_pull"
    have "S_pull = split_below d P beta"
      using Exact_Split_Range_State_Step by blast
    then show "below_bound (d x) (Fin beta)"
      using xS unfolding split_below_def by auto
  qed
  let ?child_sources = "S_pull # child_sources_tail"
  have head:
    "\<exists>c_child' B_child d_child' B_child'.
      exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_pull B_child
        d_child' B_child' U_child c_child' \<and>
      bmssp_pre_full d S_pull B_child \<and>
      (\<forall>x\<in>S_pull. reachable s x) \<and>
      card S_pull \<le> M_of l \<and>
      (\<forall>x\<in>S_pull. below_bound (d x) B_child)"
    using Exact_Split_Range_State_Step card_pull below_pull
    by blast
  show ?case
    by (intro exI[of _ ?child_sources] conjI)
      (use len_tail head tail Exact_Split_Range_State_Step in simp_all)
next
  case (Exact_Split_Range_Cost_Base S x \<Delta> M_of t h k cap d B)
  show ?case
    by simp
next
  case (Exact_Split_Range_Cost_Step D k cap d S B c_insert t \<Delta> M_of h l
      d' a betas bs B' Us U_loop c_loop child_costs_loop U c)
  show ?case
    by simp
qed

text \<open>
  The next cost bounds combine the extracted child sources with the explicit
  edge and source batch costs stored in the relation.  First the local loop cost
  is bounded by the sum of child costs, source cardinalities, and outgoing-edge
  charges over the child ranges.  Then the range-chain lemmas replace those
  list sums by the corresponding counts for the parent loop output.
\<close>

theorem exact_split_range_costed_partition_loop_state_cost_bound_by_child_sources_below:
  "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs \<Longrightarrow>
   \<exists>child_sources.
    length child_sources = length bs \<and>
    list_all2
      (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
        exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_sources (range_tree_child_list P a bs) \<and>
    c \<le> sum_list child_costs + sum_list (map card child_sources) +
      t * sum_list
        (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs)) +
      h * sum_list (map card child_sources)"
and exact_split_range_costed_bmssp_cost_child_sources_below_trivial:
  "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule:
    exact_split_range_costed_partition_loop_state_exact_split_range_costed_bmssp.inducts)
  case (Exact_Split_Range_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  show ?case
    by (intro exI[of _ "[]"]) simp
next
  case (Exact_Split_Range_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  show ?case
    by (intro exI[of _ "[]"]) simp
next
  case (Exact_Split_Range_State_Step D M_of l Bmax S_pull beta D_pull B d
      P a b B' d' k cap \<Delta> t h d_child U_child c_child edge_batch
      source_batch batch D_next c_pull c_edges c_sources betas bs Us_tail
      U_tail c_tail child_costs_tail c)
  obtain child_sources_tail where len_tail:
      "length child_sources_tail = length bs"
    and sources_tail:
      "list_all2
        (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
          exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
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
          (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P b bs)) +
        h * sum_list (map card child_sources_tail)"
    using Exact_Split_Range_State_Step.IH by blast
  have card_pull: "card S_pull \<le> M_of l"
    using Exact_Split_Range_State_Step
    unfolding pull_separates_def by blast
  have below_pull: "\<forall>x\<in>S_pull. below_bound (d x) (Fin beta)"
  proof
    fix x
    assume xS: "x \<in> S_pull"
    have "S_pull = split_below d P beta"
      using Exact_Split_Range_State_Step by blast
    then show "below_bound (d x) (Fin beta)"
      using xS unfolding split_below_def by auto
  qed
  have pull_cost: "c_pull \<le> card S_pull"
    using Exact_Split_Range_State_Step
    unfolding partition_pull_cost_bound_def by blast
  have batch_cost:
    "c_edges + c_sources \<le>
      t * card (outgoing_edges U_child) + h * card S_pull"
    by (rule range_costed_split_batch_cost_le_card[
        where d = d and S = S_pull and d_child = d_child and b = b
          and beta = beta])
      (use Exact_Split_Range_State_Step in auto)
  let ?child_sources = "S_pull # child_sources_tail"
  have len: "length ?child_sources = length (b # bs)"
    using len_tail by simp
  have head_source:
    "\<exists>c_child' B_child d_child' B_child'.
      exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_pull B_child
        d_child' B_child' U_child c_child' \<and>
      bmssp_pre_full d S_pull B_child \<and>
      (\<forall>x\<in>S_pull. reachable s x) \<and>
      card S_pull \<le> M_of l \<and>
      (\<forall>x\<in>S_pull. below_bound (d x) B_child)"
    using Exact_Split_Range_State_Step card_pull below_pull by blast
  have sources:
    "list_all2
      (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
        exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      ?child_sources (range_tree_child_list P a (b # bs))"
    using head_source sources_tail Exact_Split_Range_State_Step by simp
  have cost:
    "c \<le> sum_list (c_child # child_costs_tail) +
      sum_list (map card ?child_sources) +
      t * sum_list
        (map (\<lambda>X. card (outgoing_edges X))
          (range_tree_child_list P a (b # bs))) +
      h * sum_list (map card ?child_sources)"
  proof -
    have c_eq: "c = c_pull + c_edges + c_sources + c_child + c_tail"
      using Exact_Split_Range_State_Step by blast
    have "c_pull + c_edges + c_sources + c_child + c_tail \<le>
        card S_pull +
        (t * card (outgoing_edges U_child) + h * card S_pull) +
        c_child +
        (sum_list child_costs_tail + sum_list (map card child_sources_tail) +
          t * sum_list
            (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P b bs)) +
          h * sum_list (map card child_sources_tail))"
      using pull_cost batch_cost tail_cost by linarith
    also have "\<dots> =
        sum_list (c_child # child_costs_tail) +
        sum_list (map card ?child_sources) +
        t * (card (outgoing_edges U_child) +
          sum_list
            (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P b bs))) +
        h * sum_list (map card ?child_sources)"
      by (simp add: algebra_simps)
    also have "\<dots> =
        sum_list (c_child # child_costs_tail) +
        sum_list (map card ?child_sources) +
        t * sum_list
          (map (\<lambda>X. card (outgoing_edges X))
            (range_tree_child_list P a (b # bs))) +
        h * sum_list (map card ?child_sources)"
      using Exact_Split_Range_State_Step by simp
    finally show ?thesis
      using c_eq by simp
  qed
  show ?case
    by (intro exI[of _ ?child_sources] conjI)
      (use len sources cost in simp_all)
next
  case (Exact_Split_Range_Cost_Base S x \<Delta> M_of t h k cap d B)
  show ?case
    by simp
next
  case (Exact_Split_Range_Cost_Step D k cap d S B c_insert t \<Delta> M_of h l
      d' a betas bs B' Us U_loop c_loop child_costs_loop U c)
  show ?case
    by simp
qed

theorem exact_split_range_costed_partition_loop_state_cost_bound_by_child_sources_and_edge_ranges:
  "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs \<Longrightarrow>
   sound_label d \<Longrightarrow>
   \<exists>child_sources.
    length child_sources = length bs \<and>
    list_all2
      (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
        exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_sources (range_tree_child_list P a bs) \<and>
    c \<le> sum_list child_costs + sum_list (map card child_sources) +
      t * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs)) +
      h * sum_list (map card child_sources)"
and exact_split_range_costed_bmssp_cost_child_sources_and_edge_ranges_trivial:
  "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule:
    exact_split_range_costed_partition_loop_state_exact_split_range_costed_bmssp.inducts)
  case (Exact_Split_Range_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  show ?case
    by (intro exI[of _ "[]"]) simp
next
  case (Exact_Split_Range_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  show ?case
    by (intro exI[of _ "[]"]) simp
next
  case (Exact_Split_Range_State_Step D M_of l Bmax S_pull beta D_pull B d
      P a b B' d' k cap \<Delta> t h d_child U_child c_child edge_batch
      source_batch batch D_next c_pull c_edges c_sources betas bs Us_tail
      U_tail c_tail child_costs_tail c)
  obtain child_sources_tail where len_tail:
      "length child_sources_tail = length bs"
    and sources_tail:
      "list_all2
        (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
          exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
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
          (map card (range_tree_child_edge_range_list P b betas bs)) +
        h * sum_list (map card child_sources_tail)"
    using Exact_Split_Range_State_Step.IH
      Exact_Split_Range_State_Step.prems by blast
  have card_pull: "card S_pull \<le> M_of l"
    using Exact_Split_Range_State_Step
    unfolding pull_separates_def by blast
  have below_pull: "\<forall>x\<in>S_pull. below_bound (d x) (Fin beta)"
  proof
    fix x
    assume xS: "x \<in> S_pull"
    have "S_pull = split_below d P beta"
      using Exact_Split_Range_State_Step by blast
    then show "below_bound (d x) (Fin beta)"
      using xS unfolding split_below_def by auto
  qed
  have pull_cost: "c_pull \<le> card S_pull"
    using Exact_Split_Range_State_Step
    unfolding partition_pull_cost_bound_def by blast
  have child_run:
    "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
      d_child (Fin b) U_child c_child"
    using Exact_Split_Range_State_Step by blast
  have child_pre: "bmssp_pre_full d S_pull (Fin beta)"
    using Exact_Split_Range_State_Step by blast
  have child_reaches: "\<And>x. x \<in> S_pull \<Longrightarrow> reachable s x"
    using Exact_Split_Range_State_Step by blast
  have child_post:
    "bmssp_post_full d S_pull (Fin beta) d_child (Fin b) U_child"
    by (rule exact_split_range_costed_bmssp_correct
      [OF child_run Exact_Split_Range_State_Step.prems child_pre child_reaches])
  have child_complete: "complete_on d_child U_child"
    using child_post unfolding bmssp_post_full_def by blast
  have U_child_eq: "U_child = range_tree P a (Fin b)"
    using Exact_Split_Range_State_Step by blast
  have U_child_reaches: "\<And>u. u \<in> U_child \<Longrightarrow> reachable s u"
    unfolding U_child_eq range_tree_def tree_set_def tree_path_def by blast
  have batch_cost:
    "c_edges + c_sources \<le>
      t * card (outgoing_edges_range U_child b (Fin beta)) +
      h * card S_pull"
    by (rule range_costed_split_batch_cost_le_range_card[
        where d = d and S = S_pull and d_child = d_child and b = b
          and beta = beta])
      (use Exact_Split_Range_State_Step child_complete U_child_reaches in auto)
  let ?child_sources = "S_pull # child_sources_tail"
  have len: "length ?child_sources = length (b # bs)"
    using len_tail by simp
  have head_source:
    "\<exists>c_child' B_child d_child' B_child'.
      exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_pull B_child
        d_child' B_child' U_child c_child' \<and>
      bmssp_pre_full d S_pull B_child \<and>
      (\<forall>x\<in>S_pull. reachable s x) \<and>
      card S_pull \<le> M_of l \<and>
      (\<forall>x\<in>S_pull. below_bound (d x) B_child)"
    using Exact_Split_Range_State_Step card_pull below_pull by blast
  have sources:
    "list_all2
      (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
        exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      ?child_sources (range_tree_child_list P a (b # bs))"
    using head_source sources_tail Exact_Split_Range_State_Step by simp
  have cost:
    "c \<le> sum_list (c_child # child_costs_tail) +
      sum_list (map card ?child_sources) +
      t * sum_list
        (map card (range_tree_child_edge_range_list P a (beta # betas) (b # bs))) +
      h * sum_list (map card ?child_sources)"
  proof -
    have c_eq: "c = c_pull + c_edges + c_sources + c_child + c_tail"
      using Exact_Split_Range_State_Step by blast
    have "c_pull + c_edges + c_sources + c_child + c_tail \<le>
        card S_pull +
        (t * card (outgoing_edges_range U_child b (Fin beta)) +
          h * card S_pull) +
        c_child +
        (sum_list child_costs_tail + sum_list (map card child_sources_tail) +
          t * sum_list
            (map card (range_tree_child_edge_range_list P b betas bs)) +
          h * sum_list (map card child_sources_tail))"
      using pull_cost batch_cost tail_cost by linarith
    also have "\<dots> =
        sum_list (c_child # child_costs_tail) +
        sum_list (map card ?child_sources) +
        t * (card (outgoing_edges_range U_child b (Fin beta)) +
          sum_list
            (map card (range_tree_child_edge_range_list P b betas bs))) +
        h * sum_list (map card ?child_sources)"
      by (simp add: algebra_simps)
    also have "\<dots> =
        sum_list (c_child # child_costs_tail) +
        sum_list (map card ?child_sources) +
        t * sum_list
          (map card (range_tree_child_edge_range_list P a (beta # betas) (b # bs))) +
        h * sum_list (map card ?child_sources)"
      using U_child_eq by simp
    finally show ?thesis
      using c_eq by simp
  qed
  show ?case
    by (intro exI[of _ ?child_sources] conjI)
      (use len sources cost in simp_all)
next
  case (Exact_Split_Range_Cost_Base S x \<Delta> M_of t h k cap d B)
  show ?case
    by simp
next
  case (Exact_Split_Range_Cost_Step D k cap d S B c_insert t \<Delta> M_of h l
      d' a betas bs B' Us U_loop c_loop child_costs_loop U c)
  show ?case
    by simp
qed

theorem exact_split_range_costed_partition_loop_state_cost_from_child_source_and_edge_range_bounds:
  assumes run:
    "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child U_child.
        c_child \<le> level_range_cost_bound A R L U_child)
        child_costs (range_tree_child_list P a bs)"
    and source_progress:
      "\<And>S_child B_child d_child B_child' U_child c_child.
        \<lbrakk>exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
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
      (map card (range_tree_child_edge_range_list P a betas bs)) +
    (Suc h) * card (range_tree_chain P a bs B')"
proof -
  obtain child_sources where len_sources:
      "length child_sources = length bs"
    and sources:
      "list_all2
        (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
          exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l \<and>
          (\<forall>x\<in>S_child. below_bound (d x) B_child))
        child_sources (range_tree_child_list P a bs)"
    and cost:
      "c \<le> sum_list child_costs + sum_list (map card child_sources) +
        t * sum_list
          (map card (range_tree_child_edge_range_list P a betas bs)) +
        h * sum_list (map card child_sources)"
    using exact_split_range_costed_partition_loop_state_cost_bound_by_child_sources_and_edge_ranges
      [OF run sound] by blast
  have mono: "nondecreasing_from a bs"
  proof -
    have split_run:
      "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
        betas bs B' Us U c child_costs"
      using exact_split_range_costed_refines_split_range_costed(1)[OF run] .
    then show ?thesis
      by (rule split_range_costed_partition_loop_state_mono)
  qed
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
        "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
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
        (map card (range_tree_child_edge_range_list P a betas bs)) +
      sum_list (map card child_sources) +
      h * sum_list (map card child_sources)"
    using cost child_sum by linarith
  also have "\<dots> \<le>
      A * L * card (range_tree_chain P a bs B') +
      R * card (outgoing_edges (range_tree_chain P a bs B')) +
      t * sum_list
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

corollary exact_split_range_costed_partition_loop_state_cost_from_child_source_and_edge_range_graph_bound:
  assumes run:
    "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child U_child.
        c_child \<le> level_range_cost_bound A R L U_child)
        child_costs (range_tree_child_list P a bs)"
    and source_progress:
      "\<And>S_child B_child d_child B_child' U_child c_child.
        \<lbrakk>exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child\<rbrakk>
        \<Longrightarrow> card S_child \<le> card U_child"
  shows "c \<le>
    A * L * card (range_tree_chain P a bs B') +
    R * card (outgoing_edges (range_tree_chain P a bs B')) +
    t * edge_count +
    (Suc h) * card (range_tree_chain P a bs B')"
proof -
  have split_run:
    "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    using exact_split_range_costed_refines_split_range_costed(1)[OF run] .
  have mono: "nondecreasing_from a bs"
    by (rule split_range_costed_partition_loop_state_mono[OF split_run])
  have direct_edges:
    "sum_list (map card (range_tree_child_edge_range_list P a betas bs))
      \<le> edge_count"
    by (rule sum_card_range_tree_child_edge_range_list_le_edge_count[OF mono])
  have separated:
    "c \<le>
      A * L * card (range_tree_chain P a bs B') +
      R * card (outgoing_edges (range_tree_chain P a bs B')) +
      t * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs)) +
      (Suc h) * card (range_tree_chain P a bs B')"
    by (rule exact_split_range_costed_partition_loop_state_cost_from_child_source_and_edge_range_bounds
      [OF run sound child_cost_bounds source_progress])
  have "t * sum_list (map card (range_tree_child_edge_range_list P a betas bs))
      \<le> t * edge_count"
    using direct_edges by simp
  then show ?thesis
    using separated by linarith
qed

text \<open>
  The final theorem in this theory is the reusable recurrence step for exact
  split ranges.  Given child costs already bounded by
  @{const level_range_cost_bound} and a source-progress hypothesis, it proves
  the parent-loop bound with one additional level of vertex cost and one
  additional batch coefficient on outgoing edges.  This is the shape consumed by
  the direct-insert and bucketed refinements.
\<close>

theorem exact_split_range_costed_partition_loop_state_cost_from_child_and_source_bounds:
  assumes run:
    "exact_split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child U_child.
        c_child \<le> level_range_cost_bound A R L U_child)
        child_costs (range_tree_child_list P a bs)"
    and source_progress:
      "\<And>S_child B_child d_child B_child' U_child c_child.
        \<lbrakk>exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child\<rbrakk>
        \<Longrightarrow> card S_child \<le> card U_child"
  shows "c \<le>
    A * L * card (range_tree_chain P a bs B') +
    (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
    (Suc h) * card (range_tree_chain P a bs B')"
proof -
  obtain child_sources where len_sources:
      "length child_sources = length bs"
    and sources:
      "list_all2
        (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
          exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l \<and>
          (\<forall>x\<in>S_child. below_bound (d x) B_child))
        child_sources (range_tree_child_list P a bs)"
    and cost:
      "c \<le> sum_list child_costs + sum_list (map card child_sources) +
        t * sum_list
          (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs)) +
        h * sum_list (map card child_sources)"
    using exact_split_range_costed_partition_loop_state_cost_bound_by_child_sources_below
      [OF run] by blast
  have mono: "nondecreasing_from a bs"
  proof -
    have split_run:
      "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
        betas bs B' Us U c child_costs"
      using exact_split_range_costed_refines_split_range_costed(1)[OF run] .
    then show ?thesis
      by (rule split_range_costed_partition_loop_state_mono)
  qed
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
        "exact_split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
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
  have edge_sum:
    "sum_list
      (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs)) \<le>
     card (outgoing_edges (range_tree_chain P a bs B'))"
    by (rule card_outgoing_edges_range_tree_child_list_le_chain[OF mono])
  have "c \<le>
      A * L * card (range_tree_chain P a bs B') +
      R * card (outgoing_edges (range_tree_chain P a bs B')) +
      sum_list (map card child_sources) +
      t * card (outgoing_edges (range_tree_chain P a bs B')) +
      h * sum_list (map card child_sources)"
  proof -
    have edge_part:
      "t * sum_list
          (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs))
       \<le> t * card (outgoing_edges (range_tree_chain P a bs B'))"
      using edge_sum by simp
    have "sum_list child_costs + sum_list (map card child_sources) +
        t * sum_list
          (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs)) +
        h * sum_list (map card child_sources) \<le>
        A * L * card (range_tree_chain P a bs B') +
        R * card (outgoing_edges (range_tree_chain P a bs B')) +
        sum_list (map card child_sources) +
        t * card (outgoing_edges (range_tree_chain P a bs B')) +
        h * sum_list (map card child_sources)"
      using child_sum edge_part by linarith
    then show ?thesis
      using cost by linarith
  qed
  also have "\<dots> \<le>
      A * L * card (range_tree_chain P a bs B') +
      R * card (outgoing_edges (range_tree_chain P a bs B')) +
      t * card (outgoing_edges (range_tree_chain P a bs B')) +
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
  also have "\<dots> =
      A * L * card (range_tree_chain P a bs B') +
      (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
      (Suc h) * card (range_tree_chain P a bs B')"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

end

end
