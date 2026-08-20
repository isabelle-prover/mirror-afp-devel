theory BMSSP_Range_Costed
  imports BMSSP_Complexity
begin

section \<open>Range-Synchronised Costed Runs\<close>

text \<open>
  The algorithm's time proof charges the recursive calls in one BMSSP loop to
  the disjoint distance ranges cut out by the successive returned bounds.  The
  earlier costed relation keeps enough information for correctness and local
  data-structure costs, but its child-call cost is attached to the raw child
  output.  This theory strengthens the operational run with the range invariant:
  every child output is exactly the next range slice.

  That strengthening is the point at which the informal amortised analysis in
  the paper becomes a reusable Isabelle recurrence.  A child call is not charged
  against the whole parent tree.  It is charged against a slice
  \<open>range_tree\<close> between the previous loop bound and the child output
  bound.  The list version \<open>range_tree_child_list\<close> records all such
  slices for one parent loop.  Since those slices are disjoint and lie inside
  the final loop output, their vertex and outgoing-edge sums can be bounded by
  the final output itself.

  The exported cost shape is \<open>level_range_cost_bound\<close>.  Its first term
  counts completed vertices multiplied by a level factor; its second term counts
  outgoing edges with the range cost coefficient.  The main technical work below
  is to show that the local costs of pulling, batching, and recursive child
  calls close under this shape when moving from level \<open>l\<close> to \<open>Suc l\<close>.

  There are two related relations.  The first one uses a single batch cost
  parameter for the concatenation of edge relaxations and reinserted source
  labels.  The split relation refines it by charging edge batches and source
  batches separately.  That split form is useful for later progress arguments:
  edge batches are paid for by outgoing edges of the completed ranges, while
  source batches are paid for by the number of child sources exposed by the
  partition pulls.
\<close>

context unique_shortest_digraph
begin

lemma child_costs_le_level_range_child_list_bound:
  assumes mono: "nondecreasing_from a bs"
    and costs: "list_all2 (\<lambda>c X. c \<le> level_range_cost_bound A R l X) costs
      (range_tree_child_list S a bs)"
  shows "sum_list costs \<le>
    A * l * card (range_tree_chain S a bs B) +
    R * card (outgoing_edges (range_tree_chain S a bs B))"
proof -
  define Xs where "Xs = range_tree_child_list S a bs"
  have cost_sum:
    "sum_list costs \<le> sum_list (map (level_range_cost_bound A R l) Xs)"
    using costs unfolding Xs_def
  proof (induction rule: list_all2_induct)
    case Nil
    then show ?case by simp
  next
    case (Cons c X costs Xs)
    then show ?case
      unfolding level_range_cost_bound_def by simp
  qed
  have split_sum:
    "sum_list (map (level_range_cost_bound A R l) Xs) =
      A * l * sum_list (map card Xs) +
      R * sum_list (map (\<lambda>X. card (outgoing_edges X)) Xs)"
  proof (induction Xs)
    case Nil
    then show ?case
      unfolding level_range_cost_bound_def by simp
  next
    case (Cons X Xs)
    then show ?case
      unfolding level_range_cost_bound_def by (simp add: algebra_simps)
  qed
  have card_sum:
    "sum_list (map card Xs) \<le> card (range_tree_chain S a bs B)"
    unfolding Xs_def
    by (rule card_range_tree_child_list_le_chain[OF mono])
  have edge_sum:
    "sum_list (map (\<lambda>X. card (outgoing_edges X)) Xs) \<le>
      card (outgoing_edges (range_tree_chain S a bs B))"
    unfolding Xs_def
    by (rule card_outgoing_edges_range_tree_child_list_le_chain[OF mono])
  have "sum_list (map (level_range_cost_bound A R l) Xs) \<le>
      A * l * card (range_tree_chain S a bs B) +
      R * card (outgoing_edges (range_tree_chain S a bs B))"
  proof -
    have left:
      "A * l * sum_list (map card Xs) \<le>
        A * l * card (range_tree_chain S a bs B)"
      using card_sum by simp
    have right:
      "R * sum_list (map (\<lambda>X. card (outgoing_edges X)) Xs) \<le>
        R * card (outgoing_edges (range_tree_chain S a bs B))"
      using edge_sum by simp
    show ?thesis
      using left right split_sum by linarith
  qed
  then show ?thesis
    using cost_sum by linarith
qed

inductive range_costed_partition_loop_state
  and range_costed_bmssp where
  Range_State_Done:
    "keys_of D = {} \<Longrightarrow>
     bound_le (Fin a) B \<Longrightarrow>
     complete_on d' (bound_tree P B) \<Longrightarrow>
     range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
       [] [] B [range_tree P a B]
       (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a B])) 0 []"
| Range_State_Stop:
    "bound_le (Fin a) B \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     k * cap \<le> card (bound_tree P (Fin a)) \<Longrightarrow>
     range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
       [] [] (Fin a) [range_tree P a (Fin a)]
       (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a (Fin a)])) 0 []"
| Range_State_Step:
    "pull_separates D (M_of l) Bmax S_pull beta D_pull \<Longrightarrow>
     bound_le (Fin beta) B \<Longrightarrow>
     bmssp_pre_full d S_pull (Fin beta) \<Longrightarrow>
     (\<forall>x\<in>S_pull. reachable s x) \<Longrightarrow>
     a \<le> b \<Longrightarrow>
     bound_le (Fin a) B' \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     card (bound_tree P (Fin a)) < k * cap \<Longrightarrow>
     range_costed_bmssp \<Delta> M_of t k cap l d S_pull (Fin beta)
       d_child (Fin b) U_child c_child \<Longrightarrow>
     U_child = range_tree P a (Fin b) \<Longrightarrow>
     complete_preserved d_child d' U_child \<Longrightarrow>
     batch =
       edge_relaxation_pairs_between d_child U_child b beta @
       label_pairs_between d S_pull b beta \<Longrightarrow>
     D_next = batch_min_update D_pull batch \<Longrightarrow>
     partition_pull_cost_bound c_pull S_pull \<Longrightarrow>
     partition_batch_cost_bound c_batch t batch \<Longrightarrow>
     range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d'
       D_next b betas bs B' Us_tail U_tail c_tail child_costs_tail \<Longrightarrow>
     c = c_pull + c_batch + c_child + c_tail \<Longrightarrow>
     range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
       (beta # betas) (b # bs) B'
       (range_tree P a (Fin b) # Us_tail)
       (bound_tree P (Fin a) \<union>
        \<Union>(set (range_tree P a (Fin b) # Us_tail))) c
       (c_child # child_costs_tail)"
| Range_Cost_Base:
    "S = {x} \<Longrightarrow>
     range_costed_bmssp \<Delta> M_of t k cap 0 d S B
       (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
       (base_case_bound k x B)
       (base_case_vertices k x B)
       (base_case_scan_cost \<Delta> k x B)"
| Range_Cost_Step:
    "D = label_partition_view
       (find_pivots_label_capped k cap d S B)
       (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
     partition_initial_insert_cost_bound c_insert t
      (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
     range_costed_partition_loop_state \<Delta> M_of t k cap l
       (find_pivots_label_capped k cap d S B)
       (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
       Us U_loop c_loop child_costs_loop \<Longrightarrow>
     complete_on d'
       {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
     U = U_loop \<union>
       {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
     c = fp_iter_capped_scan_cost k cap d S S B + c_insert + c_loop \<Longrightarrow>
     range_costed_bmssp \<Delta> M_of t k cap (Suc l) d S B d' B' U c"

text \<open>
  The mutually inductive relation above adds the accounting data that the
  operational theory intentionally omitted.  A loop derivation carries the pull
  bounds \<open>betas\<close>, the child output bounds \<open>bs\<close>, the concrete range slices
  \<open>Us\<close>, a total cost \<open>c\<close>, and the list of recursive child costs.  The step
  constructor synchronises these fields by requiring the returned child set to
  be exactly @{const range_tree} for the current interval.

  The BMSSP branch keeps the usual split between the base case and the recursive
  step.  In the recursive step, FindPivots pays the scan and initial insertion
  cost, then the range-synchronised loop pays all pulls, batches, and child
  calls.  The correctness argument later forgets the costs and reuses the
  operational trace theorem; the runtime argument keeps the cost and child-cost
  lists.
\<close>

inductive_cases range_costed_bmssp_zeroE:
  "range_costed_bmssp \<Delta> M_of t k cap 0 d S B d' B' U c"

inductive_cases range_costed_bmssp_SucE:
  "range_costed_bmssp \<Delta> M_of t k cap (Suc l) d S B d' B' U c"

lemma range_costed_partition_loop_state_mono:
  assumes run:
    "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c child_costs"
  shows "nondecreasing_from a bs"
  using run by (induction) auto

theorem range_costed_partition_loop_state_child_call_ranges:
  assumes run:
    "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c child_costs"
  shows "length child_costs = length bs"
    and "list_all2
      (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
        range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l)
      child_costs (range_tree_child_list P a bs)"
  using run
  by (induction) (auto simp: pull_separates_def)

lemma range_costed_pull_cost_le_M:
  assumes pull: "pull_separates D M Bmax S beta D_pull"
    and cost: "partition_pull_cost_bound c S"
  shows "c \<le> M"
proof -
  have "card S \<le> M"
    using pull unfolding pull_separates_def by blast
  then show ?thesis
    using cost unfolding partition_pull_cost_bound_def by linarith
qed

lemma range_costed_batch_cost_le:
  assumes pre: "bmssp_pre_full d S (Fin beta)"
    and batch:
      "batch =
        edge_relaxation_pairs_between d_child U b beta @
        label_pairs_between d S b beta"
    and cost: "partition_batch_cost_bound c t batch"
    and card_S: "card S \<le> M"
  shows "c \<le> t * (card (outgoing_edges U) + M)"
proof -
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have finite_S: "finite S"
    using finite_subset[OF S_subset finite_V] .
  have edge_len:
    "length (edge_relaxation_pairs_between d_child U b beta) \<le>
      card (outgoing_edges U)"
    by (rule edge_relaxation_pairs_between_length_le_outgoing)
  have label_len:
    "length (label_pairs_between d S b beta) \<le> card S"
    by (rule label_pairs_between_length_le_card[OF finite_S])
  have batch_len: "length batch \<le> card (outgoing_edges U) + M"
    using batch edge_len label_len card_S by simp
  have "c \<le> t * length batch"
    using cost unfolding partition_batch_cost_bound_def by simp
  also have "\<dots> \<le> t * (card (outgoing_edges U) + M)"
    using batch_len by simp
  finally show ?thesis .
qed

lemma range_costed_split_batch_cost_le:
  assumes pre: "bmssp_pre_full d S (Fin beta)"
    and edge_cost:
      "partition_batch_cost_bound c_edges t
        (edge_relaxation_pairs_between d_child U b beta)"
    and source_cost:
      "partition_batch_cost_bound c_sources h
        (label_pairs_between d S b beta)"
    and c_def: "c = c_edges + c_sources"
    and card_S: "card S \<le> M"
  shows "c \<le> t * card (outgoing_edges U) + h * M"
proof -
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have finite_S: "finite S"
    using finite_subset[OF S_subset finite_V] .
  have edge_len:
    "length (edge_relaxation_pairs_between d_child U b beta) \<le>
      card (outgoing_edges U)"
    by (rule edge_relaxation_pairs_between_length_le_outgoing)
  have label_len:
    "length (label_pairs_between d S b beta) \<le> card S"
    by (rule label_pairs_between_length_le_card[OF finite_S])
  have edge_part: "c_edges \<le> t * card (outgoing_edges U)"
  proof -
    have "c_edges \<le> t * length (edge_relaxation_pairs_between d_child U b beta)"
      using edge_cost unfolding partition_batch_cost_bound_def by simp
    also have "\<dots> \<le> t * card (outgoing_edges U)"
      using edge_len by simp
    finally show ?thesis .
  qed
  have source_part: "c_sources \<le> h * M"
  proof -
    have "c_sources \<le> h * length (label_pairs_between d S b beta)"
      using source_cost unfolding partition_batch_cost_bound_def by simp
    also have "\<dots> \<le> h * card S"
      using label_len by simp
    also have "\<dots> \<le> h * M"
      using card_S by simp
    finally show ?thesis .
  qed
  show ?thesis
    using edge_part source_part c_def by linarith
qed

lemma range_costed_split_batch_cost_le_card:
  assumes pre: "bmssp_pre_full d S (Fin beta)"
    and edge_cost:
      "partition_batch_cost_bound c_edges t
        (edge_relaxation_pairs_between d_child U b beta)"
    and source_cost:
      "partition_batch_cost_bound c_sources h
        (label_pairs_between d S b beta)"
    and c_def: "c = c_edges + c_sources"
  shows "c \<le> t * card (outgoing_edges U) + h * card S"
proof -
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have finite_S: "finite S"
    using finite_subset[OF S_subset finite_V] .
  have edge_len:
    "length (edge_relaxation_pairs_between d_child U b beta) \<le>
      card (outgoing_edges U)"
    by (rule edge_relaxation_pairs_between_length_le_outgoing)
  have label_len:
    "length (label_pairs_between d S b beta) \<le> card S"
    by (rule label_pairs_between_length_le_card[OF finite_S])
  have edge_part: "c_edges \<le> t * card (outgoing_edges U)"
  proof -
    have "c_edges \<le> t * length (edge_relaxation_pairs_between d_child U b beta)"
      using edge_cost unfolding partition_batch_cost_bound_def by simp
    also have "\<dots> \<le> t * card (outgoing_edges U)"
      using edge_len by simp
    finally show ?thesis .
  qed
  have source_part: "c_sources \<le> h * card S"
  proof -
    have "c_sources \<le> h * length (label_pairs_between d S b beta)"
      using source_cost unfolding partition_batch_cost_bound_def by simp
    also have "\<dots> \<le> h * card S"
      using label_len by simp
    finally show ?thesis .
  qed
  show ?thesis
    using edge_part source_part c_def by linarith
qed

lemma range_costed_split_batch_cost_le_range_card:
  assumes pre: "bmssp_pre_full d S (Fin beta)"
    and edge_cost:
      "partition_batch_cost_bound c_edges t
        (edge_relaxation_pairs_between d_child U b beta)"
    and source_cost:
      "partition_batch_cost_bound c_sources h
        (label_pairs_between d S b beta)"
    and complete: "complete_on d_child U"
    and reaches: "\<And>u. u \<in> U \<Longrightarrow> reachable s u"
    and c_def: "c = c_edges + c_sources"
  shows "c \<le> t * card (outgoing_edges_range U b (Fin beta)) + h * card S"
proof -
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have finite_S: "finite S"
    using finite_subset[OF S_subset finite_V] .
  have edge_len:
    "length (edge_relaxation_pairs_between d_child U b beta) \<le>
      card (outgoing_edges_range U b (Fin beta))"
    by (rule edge_relaxation_pairs_between_length_le_outgoing_edges_range
      [OF complete reaches])
  have label_len:
    "length (label_pairs_between d S b beta) \<le> card S"
    by (rule label_pairs_between_length_le_card[OF finite_S])
  have edge_part:
    "c_edges \<le> t * card (outgoing_edges_range U b (Fin beta))"
  proof -
    have "c_edges \<le> t * length (edge_relaxation_pairs_between d_child U b beta)"
      using edge_cost unfolding partition_batch_cost_bound_def by simp
    also have "\<dots> \<le> t * card (outgoing_edges_range U b (Fin beta))"
      using edge_len by simp
    finally show ?thesis .
  qed
  have source_part: "c_sources \<le> h * card S"
  proof -
    have "c_sources \<le> h * length (label_pairs_between d S b beta)"
      using source_cost unfolding partition_batch_cost_bound_def by simp
    also have "\<dots> \<le> h * card S"
      using label_len by simp
    finally show ?thesis .
  qed
  show ?thesis
    using edge_part source_part c_def by linarith
qed

text \<open>
  The single-batch relation is convenient, but the sharper progress lemmas need
  to distinguish where a batch entry came from.  Edge entries are generated by
  @{const edge_relaxation_pairs_between} and are charged to outgoing edges of
  the just-completed range.  Source entries are generated by
  @{const label_pairs_between} and are charged to the number of pulled child
  sources.  The split relation below records both costs explicitly.

  This is a refinement, not a different algorithm.  Its proof to the
  single-batch relation uses the append rule for @{const partition_batch_cost_bound}
  and the elementary fact that a source-batch coefficient bounded by the edge
  coefficient can be absorbed into the combined batch budget.
\<close>

inductive split_range_costed_partition_loop_state
  and split_range_costed_bmssp where
  Split_Range_State_Done:
    "keys_of D = {} \<Longrightarrow>
     bound_le (Fin a) B \<Longrightarrow>
     complete_on d' (bound_tree P B) \<Longrightarrow>
     split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
       [] [] B [range_tree P a B]
       (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a B])) 0 []"
| Split_Range_State_Stop:
    "bound_le (Fin a) B \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     k * cap \<le> card (bound_tree P (Fin a)) \<Longrightarrow>
     split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
       [] [] (Fin a) [range_tree P a (Fin a)]
       (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a (Fin a)])) 0 []"
| Split_Range_State_Step:
    "pull_separates D (M_of l) Bmax S_pull beta D_pull \<Longrightarrow>
     bound_le (Fin beta) B \<Longrightarrow>
     bmssp_pre_full d S_pull (Fin beta) \<Longrightarrow>
     (\<forall>x\<in>S_pull. reachable s x) \<Longrightarrow>
     a \<le> b \<Longrightarrow>
     bound_le (Fin a) B' \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     card (bound_tree P (Fin a)) < k * cap \<Longrightarrow>
     split_range_costed_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
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
     split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d'
       D_next b betas bs B' Us_tail U_tail c_tail child_costs_tail \<Longrightarrow>
     c = c_pull + c_edges + c_sources + c_child + c_tail \<Longrightarrow>
     split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
       (beta # betas) (b # bs) B'
       (range_tree P a (Fin b) # Us_tail)
       (bound_tree P (Fin a) \<union>
        \<Union>(set (range_tree P a (Fin b) # Us_tail))) c
       (c_child # child_costs_tail)"
| Split_Range_Cost_Base:
    "S = {x} \<Longrightarrow>
     split_range_costed_bmssp \<Delta> M_of t h k cap 0 d S B
       (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
       (base_case_bound k x B)
       (base_case_vertices k x B)
       (base_case_scan_cost \<Delta> k x B)"
| Split_Range_Cost_Step:
    "D = label_partition_view
       (find_pivots_label_capped k cap d S B)
       (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
     partition_initial_insert_cost_bound c_insert t
       (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
     split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
       (find_pivots_label_capped k cap d S B)
       (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
       Us U_loop c_loop child_costs_loop \<Longrightarrow>
     complete_on d'
       {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
     U = U_loop \<union>
       {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
      c = fp_iter_capped_scan_cost k cap d S S B + c_insert + c_loop \<Longrightarrow>
      split_range_costed_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"

inductive_cases split_range_costed_bmssp_zeroE:
  "split_range_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"

inductive_cases split_range_costed_bmssp_SucE:
  "split_range_costed_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"

theorem split_range_costed_partition_loop_state_refines:
  shows
    "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
       betas bs B' Us U c child_costs \<Longrightarrow>
     h \<le> t \<Longrightarrow>
     range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
       betas bs B' Us U c child_costs"
  and
    "split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
     h \<le> t \<Longrightarrow>
     range_costed_bmssp \<Delta> M_of t k cap l d S B d' B' U c"
proof (induction rule:
    split_range_costed_partition_loop_state_split_range_costed_bmssp.inducts)
  case (Split_Range_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  show ?case
    using Split_Range_State_Done by (meson Range_State_Done)
next
  case (Split_Range_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  show ?case
    using Split_Range_State_Stop by (meson Range_State_Stop)
next
  case (Split_Range_State_Step D M_of l Bmax S_pull beta D_pull B d a b B'
      d' P k cap \<Delta> t h d_child U_child c_child edge_batch source_batch
      batch D_next c_pull c_edges c_sources betas bs Us_tail U_tail c_tail
      child_costs_tail c)
  have h_le_t: "h \<le> t"
    using Split_Range_State_Step.prems by simp
  have edge_cost':
    "partition_batch_cost_bound c_edges t
      (edge_relaxation_pairs_between d_child U_child b beta)"
    using Split_Range_State_Step by simp
  have source_cost':
    "partition_batch_cost_bound c_sources h
      (label_pairs_between d S_pull b beta)"
    using Split_Range_State_Step by simp
  have batch_cost:
    "partition_batch_cost_bound
      (c_edges + c_sources) t
      (edge_relaxation_pairs_between d_child U_child b beta @
       label_pairs_between d S_pull b beta)"
    by (rule partition_batch_cost_bound_append[OF edge_cost' source_cost' h_le_t])
  have c_eq:
    "c = c_pull + (c_edges + c_sources) + c_child + c_tail"
    using Split_Range_State_Step by simp
  show ?case
    by (rule Range_State_Step[
        where batch =
          "edge_relaxation_pairs_between d_child U_child b beta @
           label_pairs_between d S_pull b beta"
        and c_batch = "c_edges + c_sources"])
      (use Split_Range_State_Step h_le_t batch_cost c_eq in auto)
next
  case (Split_Range_Cost_Base S x \<Delta> M_of t h k cap d B)
  show ?case
    by (rule Range_Cost_Base[OF Split_Range_Cost_Base.hyps])
next
  case Split_Range_Cost_Step
  show ?case
    by (rule Range_Cost_Step)
      (use Split_Range_Cost_Step in auto)
qed

text \<open>
  The refinement theorem @{thm split_range_costed_partition_loop_state_refines}
  is the formal connection between the two presentations.  Once it is proved,
  any semantic theorem established for the single-batch relation can be reused
  for the split relation.  The remaining split-specific lemmas therefore focus
  on costs: extracting child sources, bounding edge and source batches
  separately, and then recombining those bounds into the level recurrence.
\<close>

lemma split_range_costed_partition_loop_state_mono:
  assumes run:
    "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
  shows "nondecreasing_from a bs"
  using run by (induction) auto

theorem split_range_costed_partition_loop_state_child_call_ranges:
  assumes run:
    "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
  shows "length child_costs = length bs"
    and "list_all2
      (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
        split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l)
      child_costs (range_tree_child_list P a bs)"
  using run
  by (induction) (auto simp: pull_separates_def)

theorem split_range_costed_partition_loop_state_cost_bound_by_child_sources:
  "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs \<Longrightarrow>
   \<exists>child_sources.
    length child_sources = length bs \<and>
    list_all2
      (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
        split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l)
      child_sources (range_tree_child_list P a bs) \<and>
    c \<le> sum_list child_costs + sum_list (map card child_sources) +
      t * sum_list
        (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs)) +
      h * sum_list (map card child_sources)"
and split_range_costed_bmssp_child_sources_trivial:
  "split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule:
    split_range_costed_partition_loop_state_split_range_costed_bmssp.inducts)
  case (Split_Range_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  show ?case
    by (intro exI[of _ "[]"]) simp
next
  case (Split_Range_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  show ?case
    by (intro exI[of _ "[]"]) simp
next
  case (Split_Range_State_Step D M_of l Bmax S_pull beta D_pull B d a b B'
      d' P k cap \<Delta> t h d_child U_child c_child edge_batch source_batch
      batch D_next c_pull c_edges c_sources betas bs Us_tail U_tail c_tail
      child_costs_tail c)
  obtain child_sources_tail where len_tail:
      "length child_sources_tail = length bs"
    and sources_tail:
      "list_all2
        (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
          split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l)
        child_sources_tail (range_tree_child_list P b bs)"
    and tail_cost:
      "c_tail \<le>
        sum_list child_costs_tail + sum_list (map card child_sources_tail) +
        t * sum_list
          (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P b bs)) +
        h * sum_list (map card child_sources_tail)"
    using Split_Range_State_Step.IH by blast
  have card_pull: "card S_pull \<le> M_of l"
    using Split_Range_State_Step unfolding pull_separates_def by blast
  have pull_cost: "c_pull \<le> card S_pull"
    using Split_Range_State_Step
    unfolding partition_pull_cost_bound_def by blast
  have batch_cost:
    "c_edges + c_sources \<le>
      t * card (outgoing_edges U_child) + h * card S_pull"
    by (rule range_costed_split_batch_cost_le_card[
        where d = d and S = S_pull and d_child = d_child and b = b
          and beta = beta])
      (use Split_Range_State_Step in auto)
  let ?child_sources = "S_pull # child_sources_tail"
  have len: "length ?child_sources = length (b # bs)"
    using len_tail by simp
  have head_source:
    "\<exists>c_child' B_child d_child' B_child'.
      split_range_costed_bmssp \<Delta> M_of t h k cap l d S_pull B_child
        d_child' B_child' U_child c_child' \<and>
      bmssp_pre_full d S_pull B_child \<and>
      (\<forall>x\<in>S_pull. reachable s x) \<and>
      card S_pull \<le> M_of l"
    using Split_Range_State_Step card_pull by blast
  have sources:
    "list_all2
      (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
        split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l)
      ?child_sources (range_tree_child_list P a (b # bs))"
    using head_source sources_tail Split_Range_State_Step by simp
  have cost:
    "c \<le> sum_list (c_child # child_costs_tail) +
      sum_list (map card ?child_sources) +
      t * sum_list
        (map (\<lambda>X. card (outgoing_edges X))
          (range_tree_child_list P a (b # bs))) +
      h * sum_list (map card ?child_sources)"
  proof -
    have c_eq: "c = c_pull + c_edges + c_sources + c_child + c_tail"
      using Split_Range_State_Step by blast
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
      using Split_Range_State_Step by simp
    finally show ?thesis
      using c_eq by simp
  qed
  show ?case
    by (intro exI[of _ ?child_sources] conjI)
      (use len sources cost in simp_all)
next
  case (Split_Range_Cost_Base S x \<Delta> M_of t h k cap d B)
  show ?case
    by simp
next
  case (Split_Range_Cost_Step D k cap d S B c_insert t \<Delta> M_of h l d' a
      betas bs B' Us U_loop c_loop child_costs_loop U c)
  show ?case
    by simp
qed

theorem split_range_costed_partition_loop_state_cost_from_child_and_source_bounds:
  assumes run:
    "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child U_child.
        c_child \<le> level_range_cost_bound A R L U_child)
        child_costs (range_tree_child_list P a bs)"
    and source_progress:
      "\<And>S_child B_child d_child B_child' U_child c_child.
        \<lbrakk>split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> card S_child \<le> card U_child"
  shows "c \<le>
    A * L * card (range_tree_chain P a bs B') +
    (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
    Suc h * card (range_tree_chain P a bs B')"
proof -
  obtain child_sources where len_sources:
      "length child_sources = length bs"
    and sources:
      "list_all2
        (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
          split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l)
        child_sources (range_tree_child_list P a bs)"
    and cost:
      "c \<le> sum_list child_costs + sum_list (map card child_sources) +
        t * sum_list
          (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs)) +
        h * sum_list (map card child_sources)"
    using split_range_costed_partition_loop_state_cost_bound_by_child_sources[OF run]
    by blast
  have mono: "nondecreasing_from a bs"
    by (rule split_range_costed_partition_loop_state_mono[OF run])
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
        "split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child"
      and child_pre: "bmssp_pre_full d S_child B_child"
      and child_reaches: "\<forall>x\<in>S_child. reachable s x"
      and child_card: "card S_child \<le> M_of l"
      using Cons.hyps by blast
    have head: "card S_child \<le> card U_child"
      by (rule source_progress[OF child child_pre _ child_card])
        (use child_reaches in blast)
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
          (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs)) \<le>
       t * card (outgoing_edges (range_tree_chain P a bs B'))"
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
      (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
      Suc h * card (range_tree_chain P a bs B')"
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
      using source_part by (simp add: algebra_simps)
  qed
  finally show ?thesis .
qed

theorem split_range_costed_partition_loop_state_child_cost_bounds:
  assumes run:
    "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
  shows "list_all2 (\<lambda>c_child U_child.
      c_child \<le> level_range_cost_bound A R L U_child)
    child_costs (range_tree_child_list P a bs)"
proof -
  have calls:
    "list_all2
      (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
        split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l)
      child_costs (range_tree_child_list P a bs)"
    by (rule split_range_costed_partition_loop_state_child_call_ranges(2)[OF run])
  show ?thesis
    using calls
  proof (induction rule: list_all2_induct)
    case Nil
    then show ?case by simp
  next
    case (Cons c_child child_costs U_child child_sets)
    obtain S_child B_child d_child B_child' where child:
        "split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child"
      and child_pre: "bmssp_pre_full d S_child B_child"
      and child_reaches: "\<forall>x\<in>S_child. reachable s x"
      and child_card: "card S_child \<le> M_of l"
      using Cons.hyps by blast
    have head:
      "c_child \<le> level_range_cost_bound A R L U_child"
      by (rule child_bound[OF child child_pre _ child_card])
        (use child_reaches in blast)
    show ?case
      using head Cons.IH Cons.hyps by simp
  qed
qed

theorem split_range_costed_partition_loop_state_cost_from_child_bound:
  assumes run:
    "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and source_progress:
      "\<And>S_child B_child d_child B_child' U_child c_child.
        \<lbrakk>split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> card S_child \<le> card U_child"
  shows "c \<le>
    A * L * card (range_tree_chain P a bs B') +
    (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
    Suc h * card (range_tree_chain P a bs B')"
proof -
  have child_cost_bounds:
    "list_all2 (\<lambda>c_child U_child.
      c_child \<le> level_range_cost_bound A R L U_child)
      child_costs (range_tree_child_list P a bs)"
    by (rule split_range_costed_partition_loop_state_child_cost_bounds
      [OF run child_bound])
  show ?thesis
    by (rule split_range_costed_partition_loop_state_cost_from_child_and_source_bounds
      [OF run child_cost_bounds source_progress])
qed

theorem split_range_costed_partition_loop_state_trace:
  "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
     betas bs B' Us U c child_costs \<Longrightarrow>
   sound_label d \<Longrightarrow>
   bmssp_pre_full d P B \<Longrightarrow>
   (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
   concrete_partition_loop_trace P B a bs d' B' Us U"
and split_range_costed_bmssp_correct:
  "split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
   sound_label d \<Longrightarrow>
   bmssp_pre_full d S B \<Longrightarrow>
   (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
   bmssp_post_full d S B d' B' U"
proof (induction rule:
    split_range_costed_partition_loop_state_split_range_costed_bmssp.inducts)
  case (Split_Range_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  have a_le: "bound_le (Fin a) B"
    using Split_Range_State_Done by blast
  have complete_B: "complete_on d' (bound_tree P B)"
    using Split_Range_State_Done by blast
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
  case (Split_Range_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  then show ?case
    unfolding concrete_partition_loop_trace_def complete_on_def by simp
next
  case Split_Range_State_Step
  then show ?case
    unfolding concrete_partition_loop_trace_def bmssp_post_full_def
      complete_preserved_def
    by (auto split: bound.splits)
next
  case (Split_Range_Cost_Base S x \<Delta> M_of t h k cap d B)
  have post:
    "bmssp_post d S B
      (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
      (base_case_bound k x B)
      (base_case_vertices k x B)"
    using base_case_result_bmssp_post[OF Split_Range_Cost_Base.hyps,
        where k = k and B = B and d = d]
    unfolding base_case_result_def by simp
  then show ?case
    by (rule bmssp_post_imp_post_full)
next
  case (Split_Range_Cost_Step D k cap d S B c_insert t \<Delta> M_of h l d' a
      betas bs B' Us U_loop c_loop child_costs_loop U c)
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  let ?W = "{v \<in> bound_tree S B'. ?d_fp v = dist s v}"
  have sound_fp: "sound_label ?d_fp"
    unfolding find_pivots_label_capped_def
    by (rule fp_iter_capped_label_sound[OF Split_Range_Cost_Step.prems(1)
      Split_Range_Cost_Step.prems(3)])
  have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
    using find_pivots_capped_establishes_pivot_pre_concrete
      [OF Split_Range_Cost_Step.prems(1) Split_Range_Cost_Step.prems(2)
        Split_Range_Cost_Step.prems(3)] .
  have P_subset_S: "?P \<subseteq> S"
    unfolding find_pivots_pivots_capped_def by auto
  have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
    using P_subset_S Split_Range_Cost_Step.prems(3) by blast
  have trace:
    "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
    using Split_Range_Cost_Step.IH sound_fp pivot_pre P_reaches by blast
  have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
    by (rule concrete_partition_loop_trace_post[OF trace])
  have le: "bound_le B' B"
    using loop_post unfolding bmssp_post_full_def by blast
  have U_tree: "U = bound_tree S B'"
  proof -
    have "U_loop \<union> ?W = bound_tree S B'"
      by (rule concrete_capped_find_pivots_final_tree_assembly
        [OF Split_Range_Cost_Step.prems(1) Split_Range_Cost_Step.prems(2)
          Split_Range_Cost_Step.prems(3) loop_post])
    then show ?thesis
      using Split_Range_Cost_Step(6) by simp
  qed
  have loop_complete: "complete_on d' U_loop"
    using loop_post unfolding bmssp_post_full_def by blast
  have U_complete: "complete_on d' U"
    using complete_on_Un[OF loop_complete Split_Range_Cost_Step(5)]
      Split_Range_Cost_Step(6) by simp
  show ?case
    using le U_tree U_complete unfolding bmssp_post_full_def by blast
qed

text \<open>
  The next block closes the level recurrence for the split relation.  The input
  hypotheses have the same shape as the informal induction in the paper: each
  child call already satisfies a level-\<open>L\<close> bound on its own output slice, and
  every pulled child source set makes enough progress to be charged to that
  slice.  The trace theorem supplies the geometric fact needed to sum these
  charges: the range slices form a chain inside the parent output.

  Once the slice sums are bounded by the parent output and its outgoing edges,
  the arithmetic is straightforward.  The child level factor contributes
  \<open>A * L\<close>, the source-progress term contributes one more \<open>A\<close>, and the edge
  batch cost contributes the extra \<open>t\<close> in the range coefficient.  This is why
  the target has level \<open>Suc L\<close> and coefficient \<open>R + t\<close>.
\<close>

theorem split_range_costed_partition_loop_state_closes_level_bound_from_child_cost_bounds_general:
  assumes run:
    "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child U_child.
        c_child \<le> level_range_cost_bound A R L U_child)
        child_costs (range_tree_child_list P a bs)"
    and source_progress:
      "\<And>S_child B_child d_child B_child' U_child c_child.
        \<lbrakk>split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> card S_child \<le> card U_child"
    and source_factor: "Suc h \<le> A"
  shows "c \<le> A * Suc L * card U + (R + t) * card (outgoing_edges U)"
proof -
  have trace: "concrete_partition_loop_trace P B a bs d' B' Us U"
    by (rule split_range_costed_partition_loop_state_trace
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
      (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
      Suc h * card (range_tree_chain P a bs B')"
    by (rule split_range_costed_partition_loop_state_cost_from_child_and_source_bounds
      [OF run child_cost_bounds source_progress])
  have source_term:
    "Suc h * card (range_tree_chain P a bs B') \<le> A * card U"
  proof -
    have "Suc h * card (range_tree_chain P a bs B') \<le>
        A * card (range_tree_chain P a bs B')"
      using source_factor by (rule mult_right_mono) simp
    also have "\<dots> \<le> A * card U"
      using card_chain_le by simp
    finally show ?thesis .
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
    have "A * L * card (range_tree_chain P a bs B') +
        (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
        Suc h * card (range_tree_chain P a bs B') \<le>
        A * L * card U + (R + t) * card (outgoing_edges U) + A * card U"
      using vterm eterm source_term by linarith
    then show ?thesis
      using loop by linarith
  qed
  also have "\<dots> =
      A * Suc L * card U + (R + t) * card (outgoing_edges U)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem split_range_costed_partition_loop_state_closes_level_bound_from_source_progress_general:
  assumes run:
    "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and source_progress:
      "\<And>S_child B_child d_child B_child' U_child c_child.
        \<lbrakk>split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> card S_child \<le> card U_child"
    and source_factor: "Suc h \<le> A"
  shows "c \<le> A * Suc L * card U + (R + t) * card (outgoing_edges U)"
proof -
  have child_cost_bounds:
    "list_all2 (\<lambda>c_child U_child.
      c_child \<le> level_range_cost_bound A R L U_child)
      child_costs (range_tree_child_list P a bs)"
    by (rule split_range_costed_partition_loop_state_child_cost_bounds
      [OF run child_bound])
  show ?thesis
    by (rule
      split_range_costed_partition_loop_state_closes_level_bound_from_child_cost_bounds_general
      [OF run sound pre P_reaches child_cost_bounds source_progress
        source_factor])
qed

theorem split_range_costed_nonbase_step_closes_level_bound_from_source_progress_general:
  assumes loop:
    "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U_loop c_loop child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and source_progress:
      "\<And>S_child B_child d_child B_child' U_child c_child.
        \<lbrakk>split_range_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> card S_child \<le> card U_child"
    and source_factor: "Suc h \<le> A"
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
    by (rule split_range_costed_partition_loop_state_closes_level_bound_from_source_progress_general
      [OF loop sound pre P_reaches child_bound source_progress source_factor])
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

lemma split_range_costed_base_level_bound:
  assumes R_pos: "0 < R"
  shows "base_case_scan_cost \<Delta> k x B \<le>
    level_range_cost_bound A R (Suc 0) (base_case_vertices k x B)"
proof -
  have "base_case_scan_cost \<Delta> k x B \<le>
      R * card (outgoing_edges (base_case_vertices k x B))"
    using R_pos unfolding base_case_scan_cost_def by simp
  then show ?thesis
    unfolding level_range_cost_bound_def by linarith
qed

theorem split_range_costed_bmssp_level_bound_from_source_progress_and_local_budgets:
  assumes base_budget: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and source_factor: "Suc h \<le> A"
    and source_progress:
      "\<And>l d S B d' B' U c.
        split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        card S \<le> M_of l \<Longrightarrow>
        card S \<le> card U"
    and step_budget:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
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
        fp_iter_capped_scan_cost k cap d S S B + c_insert \<le> A * card U"
    and run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "c \<le> level_range_cost_bound A (R + l * t) (2 * l + 1) U"
  using run sound pre S_reaches
proof (induction l arbitrary: d S B d' B' U c rule: less_induct)
  case (less l)
  show ?case
  proof (cases l)
    case 0
    have run0:
      "split_range_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
      using less.prems(1) 0 by simp
    show ?thesis
      using run0 R_pos 0
      by (cases rule: split_range_costed_bmssp.cases)
        (simp_all add: split_range_costed_base_level_bound)
  next
    case (Suc l0)
    have run_suc:
      "split_range_costed_bmssp \<Delta> M_of t h k cap (Suc l0) d S B d' B' U c"
      using less.prems(1) Suc by simp
    show ?thesis
    proof (cases rule: split_range_costed_bmssp_SucE[OF run_suc])
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
        unfolding find_pivots_pivots_capped_def by auto
      have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
        using P_subset_S less.prems(4) by blast
      have child_bound:
        "\<And>c_child U_child S_child B_child d_child B_child'.
          \<lbrakk>split_range_costed_bmssp \<Delta> M_of t h k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child;
            bmssp_pre_full ?d_fp S_child B_child;
            \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
            card S_child \<le> M_of l0\<rbrakk>
          \<Longrightarrow> c_child \<le> level_range_cost_bound A (R + l0 * t)
            (2 * l0 + 1) U_child"
      proof -
        fix c_child U_child S_child B_child d_child B_child'
        assume child:
            "split_range_costed_bmssp \<Delta> M_of t h k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child"
          and child_pre: "bmssp_pre_full ?d_fp S_child B_child"
          and child_reaches: "\<And>x. x \<in> S_child \<Longrightarrow> reachable s x"
        show "c_child \<le> level_range_cost_bound A (R + l0 * t)
            (2 * l0 + 1) U_child"
          by (rule less.IH[of l0 ?d_fp S_child B_child d_child B_child'
                U_child c_child, OF _ child sound_fp child_pre child_reaches])
            (simp add: Suc)
      qed
      have source_progress_loop:
        "\<And>S_child B_child d_child B_child' U_child c_child.
          \<lbrakk>split_range_costed_bmssp \<Delta> M_of t h k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child;
            bmssp_pre_full ?d_fp S_child B_child;
            \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
            card S_child \<le> M_of l0\<rbrakk>
          \<Longrightarrow> card S_child \<le> card U_child"
        by (rule source_progress)
      have scan_insert:
        "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
          A * card U"
        by (rule step_budget[OF refl 1(3) 1(4) 1(5) 1(1)
            less.prems(2) less.prems(3) less.prems(4)])
      have trace:
        "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
        by (rule split_range_costed_partition_loop_state_trace
          [OF 1(4) sound_fp pivot_pre P_reaches])
      have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
        by (rule concrete_partition_loop_trace_post[OF trace])
      have finite_U_loop: "finite U_loop"
        using loop_post unfolding bmssp_post_full_def by simp
      have finite_W: "finite ?W"
        by simp
      have finite_U: "finite U"
        using 1(1) finite_U_loop finite_W by simp
      have step:
        "c \<le> A * Suc (Suc (2 * l0 + 1)) * card U +
          (R + l0 * t + t) * card (outgoing_edges U)"
        by (rule split_range_costed_nonbase_step_closes_level_bound_from_source_progress_general
          [OF 1(4) sound_fp pivot_pre P_reaches child_bound
            source_progress_loop source_factor 1(1) finite_U scan_insert 1(2)])
      show ?thesis
        using step Suc unfolding level_range_cost_bound_def
        by (simp add: algebra_simps)
    qed
  qed
qed

theorem split_range_costed_bmssp_level_bound_from_source_progress_budgets:
  assumes degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and source_factor: "Suc h \<le> 2 * A"
    and source_progress:
      "\<And>l d S B d' B' U c.
        split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        card S \<le> M_of l \<Longrightarrow>
        card S \<le> card U"
    and step_progress:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
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
        card S \<le> cap \<and> k * cap \<le> card U"
    and run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
proof (rule split_range_costed_bmssp_level_bound_from_source_progress_and_local_budgets
    [where A = "2 * A" and R = R,
      OF _ R_pos source_factor source_progress _ run sound pre S_reaches])
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
      "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
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
  have S_subset: "S \<subseteq> V"
    using pre_s unfolding bmssp_pre_full_def by blast
  have progress:
      "card S \<le> cap \<and> k * cap \<le> card U"
    by (rule step_progress[OF D_def insert loop complete U_def sound_s pre_s reaches_s])
  then have S_cap: "card S \<le> cap"
    by blast
  from progress have U_progress: "k * cap \<le> card U"
    by blast
  show "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
      2 * A * card U"
    by (rule find_pivots_scan_and_initial_insert_budget_from_progress
      [OF S_subset degree S_cap insert degree_factor insert_factor U_progress])
qed

theorem finite_initial_label_split_range_costed_top_level_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap l finite_initial_label {s}
        Infinity d' Infinity U c"
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
    by (rule split_range_costed_bmssp_correct[OF run sound pre S_reaches])
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

theorem finite_initial_label_split_range_costed_top_level_correct_and_local_budget_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and base_budget: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and source_factor: "Suc h \<le> A"
    and source_progress:
      "\<And>l d S B d' B' U c.
        split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        card S \<le> M_of l \<Longrightarrow>
        card S \<le> card U"
    and step_budget:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
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
        fp_iter_capped_scan_cost k cap d S S B + c_insert \<le> A * card U"
    and run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap l finite_initial_label {s}
        Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> level_range_cost_bound A (R + l * t) (2 * l + 1) U"
proof
  show "sssp_correct d'"
    by (rule finite_initial_label_split_range_costed_top_level_correct
      [OF all_reachable run])
next
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  show "c \<le> level_range_cost_bound A (R + l * t) (2 * l + 1) U"
    by (rule split_range_costed_bmssp_level_bound_from_source_progress_and_local_budgets
      [OF base_budget R_pos source_factor source_progress step_budget run sound pre
        S_reaches])
qed

theorem finite_initial_label_split_range_costed_top_level_correct_and_local_budget_graph_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and base_budget: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and source_factor: "Suc h \<le> A"
    and source_progress:
      "\<And>l d S B d' B' U c.
        split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        card S \<le> M_of l \<Longrightarrow>
        card S \<le> card U"
    and step_budget:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
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
        fp_iter_capped_scan_cost k cap d S S B + c_insert \<le> A * card U"
    and run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap l finite_initial_label {s}
        Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> A * (2 * l + 1) * vertex_count + (R + l * t) * edge_count"
proof -
  have combined:
    "sssp_correct d' \<and>
      c \<le> level_range_cost_bound A (R + l * t) (2 * l + 1) U"
    by (rule finite_initial_label_split_range_costed_top_level_correct_and_local_budget_bound
      [OF all_reachable base_budget R_pos source_factor source_progress step_budget run])
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
    by (rule split_range_costed_bmssp_correct[OF run sound pre S_reaches])
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

theorem finite_initial_label_split_range_costed_top_level_correct_and_source_progress_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and source_factor: "Suc h \<le> 2 * A"
    and source_progress:
      "\<And>l d S B d' B' U c.
        split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        card S \<le> M_of l \<Longrightarrow>
        card S \<le> card U"
    and step_progress:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
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
        card S \<le> cap \<and> k * cap \<le> card U"
    and run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap l finite_initial_label {s}
        Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
proof
  show "sssp_correct d'"
    by (rule finite_initial_label_split_range_costed_top_level_correct
      [OF all_reachable run])
next
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  show "c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
    by (rule split_range_costed_bmssp_level_bound_from_source_progress_budgets
      [OF degree degree_factor R_pos insert_factor source_factor source_progress
        step_progress run sound pre S_reaches])
qed

theorem finite_initial_label_split_range_costed_top_level_correct_and_graph_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and source_factor: "Suc h \<le> 2 * A"
    and source_progress:
      "\<And>l d S B d' B' U c.
        split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        card S \<le> M_of l \<Longrightarrow>
        card S \<le> card U"
    and step_progress:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
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
        card S \<le> cap \<and> k * cap \<le> card U"
    and run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap l finite_initial_label {s}
        Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * t) * edge_count"
proof -
  have combined:
    "sssp_correct d' \<and>
      c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
    by (rule finite_initial_label_split_range_costed_top_level_correct_and_source_progress_bound
      [OF all_reachable degree degree_factor R_pos insert_factor source_factor
        source_progress step_progress run])
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
    by (rule split_range_costed_bmssp_correct[OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  have U_V: "U = V"
    using post bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  have cost_U:
      "c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
    using combined by blast
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
    using correct cost_U graph_bound by linarith
qed

theorem split_range_costed_bmssp_source_card_le_if_sound_label_below_output:
  assumes run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B'"
  shows "card S \<le> card U"
proof -
  have post: "bmssp_post_full d S B d' B' U"
    by (rule split_range_costed_bmssp_correct[OF run sound pre S_reaches])
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

theorem split_range_costed_partition_loop_state_success_or_threshold:
  "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' Us U c child_costs \<Longrightarrow>
   sound_label d \<Longrightarrow>
   bmssp_pre_full d P B \<Longrightarrow>
   (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
   B' = B \<or> k * cap \<le> card U"
and split_range_costed_bmssp_success_or_threshold_trivial:
  "split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule: split_range_costed_partition_loop_state_split_range_costed_bmssp.inducts)
  case (Split_Range_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  then show ?case
    by simp
next
  case (Split_Range_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  then show ?case
    by simp
next
  case (Split_Range_State_Step D M_of l Bmax S_pull beta D_pull B d a b B_out
      d_out P k cap Delta t h d_child U_child c_child edge_batch source_batch
      batch D_next c_pull c_edges c_sources betas bs Us_tail U_tail c_tail
      child_costs_tail c)
  have tail:
    "B_out = B \<or> k * cap \<le> card U_tail"
    using Split_Range_State_Step.IH Split_Range_State_Step.prems by blast
  then show ?case
  proof
    assume "B_out = B"
    then show ?thesis
      by blast
  next
    assume threshold_tail: "k * cap \<le> card U_tail"
    have tail_trace:
      "concrete_partition_loop_trace P B b bs d_out B_out Us_tail U_tail"
      by (rule split_range_costed_partition_loop_state_trace)
        (use Split_Range_State_Step in blast)+
    have U_tail_def:
      "U_tail = bound_tree P (Fin b) \<union> \<Union>(set Us_tail)"
      using tail_trace unfolding concrete_partition_loop_trace_def by blast
    have split_b:
      "bound_tree P (Fin b) =
        bound_tree P (Fin a) \<union> range_tree P a (Fin b)"
      using bound_tree_split_at[of a "Fin b" P] Split_Range_State_Step
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
  case (Split_Range_Cost_Base S x \<Delta> M_of t h k cap d B)
  then show ?case
    by simp
next
  case (Split_Range_Cost_Step D k cap d S B c_insert t \<Delta> M_of h l d' a
      betas bs B' Us U_loop c_loop child_costs_loop U c)
  then show ?case
    by simp
qed

theorem split_range_costed_bmssp_Suc_success_or_threshold:
  assumes run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "B' = B \<or> k * cap \<le> card U"
  using run
proof cases
  case (Split_Range_Cost_Step D c_insert a betas bs Us U_loop c_loop child_costs_loop)
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
    by (rule split_range_costed_partition_loop_state_success_or_threshold
      [OF Split_Range_Cost_Step(3) sound_fp pivot_pre P_reaches])
  have loop_trace:
    "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
    by (rule split_range_costed_partition_loop_state_trace
      [OF Split_Range_Cost_Step(3) sound_fp pivot_pre P_reaches])
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
      using Split_Range_Cost_Step(5) by simp
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

theorem split_range_costed_bmssp_Suc_source_card_le_from_label_below:
  assumes run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and S_cap: "card S \<le> cap"
    and k_pos: "0 < k"
  shows "card S \<le> card U"
proof -
  have call_class: "B' = B \<or> k * cap \<le> card U"
    by (rule split_range_costed_bmssp_Suc_success_or_threshold
      [OF run sound pre S_reaches])
  then show ?thesis
  proof
    assume B'_eq: "B' = B"
    show ?thesis
    proof (rule split_range_costed_bmssp_source_card_le_if_sound_label_below_output
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

theorem split_range_costed_capped_step_threshold_if_not_success:
  assumes loop:
      "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
        Us U_loop c_loop child_costs"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v}"
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
    by (rule split_range_costed_partition_loop_state_success_or_threshold
      [OF loop sound_fp pivot_pre P_reaches])
  have threshold_loop: "k * cap \<le> card U_loop"
    using loop_class not_success by blast
  have trace: "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
    by (rule split_range_costed_partition_loop_state_trace
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

theorem split_range_costed_capped_step_scan_insert_budget_if_not_success:
  assumes degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and insert_factor: "t \<le> A * k"
    and insert:
      "partition_initial_insert_cost_bound c_insert t
        (find_pivots_pivots_capped k cap d S B)"
    and loop:
      "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
        Us U_loop c_loop child_costs"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v}"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and S_cap: "card S \<le> cap"
    and not_success: "B' \<noteq> B"
  shows "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
    2 * A * card U"
proof -
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have progress: "k * cap \<le> card U"
    by (rule split_range_costed_capped_step_threshold_if_not_success
      [OF loop U_def sound pre S_reaches not_success])
  show ?thesis
    by (rule find_pivots_scan_and_initial_insert_budget_from_progress
      [OF S_subset degree S_cap insert degree_factor insert_factor progress])
qed

theorem split_range_costed_capped_step_scan_insert_budget_from_seen_or_threshold:
  assumes degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and insert_factor: "t \<le> A * k"
    and seen_factor: "k * \<Delta> + t \<le> 2 * A"
    and insert:
      "partition_initial_insert_cost_bound c_insert t
        (find_pivots_pivots_capped k cap d S B)"
    and loop:
      "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
        Us U_loop c_loop child_costs"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v}"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and S_cap: "card S \<le> cap"
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
    by (rule find_pivots_scan_and_initial_insert_budget_from_seen_total
      [OF S_subset degree S_cap anti k_pos insert seen_factor
        seen_success[OF True]])
next
  case False
  show ?thesis
    by (rule split_range_costed_capped_step_scan_insert_budget_if_not_success
      [OF degree degree_factor insert_factor insert loop U_def sound pre
        S_reaches S_cap False])
qed

theorem split_range_costed_capped_step_scan_insert_budget_from_scaled_seen_or_threshold:
  assumes degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and insert:
      "partition_initial_insert_cost_bound c_insert t
        (find_pivots_pivots_capped k cap d S B)"
    and loop:
      "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
        Us U_loop c_loop child_costs"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v}"
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
  have S_cap: "card S \<le> cap"
  proof -
    have "card S \<le> k * card S"
      using k_pos by (cases k) simp_all
    then show ?thesis
      using S_k_cap by linarith
  qed
  show ?thesis
    by (rule split_range_costed_capped_step_scan_insert_budget_if_not_success
      [OF degree degree_factor insert_factor insert loop U_def sound pre
        S_reaches S_cap False])
qed

theorem split_range_costed_bmssp_level_bound_from_seen_progress_budgets:
  assumes degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and seen_factor: "k * \<Delta> + t \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and source_progress:
      "\<And>l d S B d' B' U c.
        split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        card S \<le> M_of l \<Longrightarrow>
        card S \<le> card U"
    and step_seen_progress:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
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
        card S \<le> cap \<and> tree_antichain S \<and>
        (B' = B \<longrightarrow>
          card (find_pivots_seen_capped k cap d S B) \<le> card U)"
    and run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
proof (rule split_range_costed_bmssp_level_bound_from_source_progress_and_local_budgets
    [where A = "2 * A" and R = R,
      OF _ R_pos source_factor source_progress _ run sound pre S_reaches])
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
      "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
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
  have progress:
      "card S \<le> cap \<and> tree_antichain S \<and>
        (B' = B \<longrightarrow>
          card (find_pivots_seen_capped k cap d S B) \<le> card U)"
    by (rule step_seen_progress
      [OF D_def insert loop complete U_def sound_s pre_s reaches_s])
  then have S_cap: "card S \<le> cap"
    by blast
  from progress have anti: "tree_antichain S"
    by blast
  from progress have seen_success:
      "B' = B \<Longrightarrow>
        card (find_pivots_seen_capped k cap d S B) \<le> card U"
    by blast
  show "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
      2 * A * card U"
    by (rule split_range_costed_capped_step_scan_insert_budget_from_seen_or_threshold
      [OF degree degree_factor insert_factor seen_factor insert loop U_def sound_s
        pre_s reaches_s S_cap anti k_pos seen_success])
qed

theorem split_range_costed_bmssp_level_bound_from_scaled_seen_progress_budgets:
  assumes degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and source_progress:
      "\<And>l d S B d' B' U c.
        split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        card S \<le> M_of l \<Longrightarrow>
        card S \<le> card U"
    and step_scaled_seen_progress:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
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
        k * card S \<le> cap \<and> tree_antichain S \<and>
        (B' = B \<longrightarrow>
          card (find_pivots_seen_capped k cap d S B) \<le> card U)"
    and run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
proof (rule split_range_costed_bmssp_level_bound_from_source_progress_and_local_budgets
    [where A = "2 * A" and R = R,
      OF _ R_pos source_factor source_progress _ run sound pre S_reaches])
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
      "split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
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
  have progress:
      "k * card S \<le> cap \<and> tree_antichain S \<and>
        (B' = B \<longrightarrow>
          card (find_pivots_seen_capped k cap d S B) \<le> card U)"
    by (rule step_scaled_seen_progress
      [OF D_def insert loop complete U_def sound_s pre_s reaches_s])
  then have S_k_cap: "k * card S \<le> cap"
    by blast
  from progress have anti: "tree_antichain S"
    by blast
  from progress have seen_success:
      "B' = B \<Longrightarrow>
        card (find_pivots_seen_capped k cap d S B) \<le> card U"
    by blast
  show "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
      2 * A * card U"
    by (rule split_range_costed_capped_step_scan_insert_budget_from_scaled_seen_or_threshold
      [OF degree degree_factor insert_factor insert_scaled_factor
        seen_scaled_factor insert loop U_def sound_s pre_s reaches_s
        S_k_cap anti k_pos seen_success])
qed

theorem finite_initial_label_split_range_costed_top_level_correct_and_seen_progress_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and seen_factor: "k * \<Delta> + t \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and source_progress:
      "\<And>l d S B d' B' U c.
        split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        card S \<le> M_of l \<Longrightarrow>
        card S \<le> card U"
    and step_seen_progress:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
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
        card S \<le> cap \<and> tree_antichain S \<and>
        (B' = B \<longrightarrow>
          card (find_pivots_seen_capped k cap d S B) \<le> card U)"
    and run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap l finite_initial_label {s}
        Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
proof
  show "sssp_correct d'"
    by (rule finite_initial_label_split_range_costed_top_level_correct
      [OF all_reachable run])
next
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  show "c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
    by (rule split_range_costed_bmssp_level_bound_from_seen_progress_budgets
      [OF degree degree_factor R_pos insert_factor seen_factor source_factor k_pos
        source_progress step_seen_progress run sound pre S_reaches])
qed

theorem finite_initial_label_split_range_costed_top_level_correct_and_scaled_seen_progress_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and source_progress:
      "\<And>l d S B d' B' U c.
        split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        card S \<le> M_of l \<Longrightarrow>
        card S \<le> card U"
    and step_scaled_seen_progress:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
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
        k * card S \<le> cap \<and> tree_antichain S \<and>
        (B' = B \<longrightarrow>
          card (find_pivots_seen_capped k cap d S B) \<le> card U)"
    and run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap l finite_initial_label {s}
        Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
proof
  show "sssp_correct d'"
    by (rule finite_initial_label_split_range_costed_top_level_correct
      [OF all_reachable run])
next
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  show "c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
    by (rule split_range_costed_bmssp_level_bound_from_scaled_seen_progress_budgets
      [OF degree degree_factor R_pos insert_factor insert_scaled_factor
        seen_scaled_factor source_factor k_pos source_progress
        step_scaled_seen_progress run sound pre S_reaches])
qed

theorem finite_initial_label_split_range_costed_top_level_correct_and_seen_progress_graph_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and seen_factor: "k * \<Delta> + t \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and source_progress:
      "\<And>l d S B d' B' U c.
        split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        card S \<le> M_of l \<Longrightarrow>
        card S \<le> card U"
    and step_seen_progress:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
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
        card S \<le> cap \<and> tree_antichain S \<and>
        (B' = B \<longrightarrow>
          card (find_pivots_seen_capped k cap d S B) \<le> card U)"
    and run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap l finite_initial_label {s}
        Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * t) * edge_count"
proof -
  have combined:
    "sssp_correct d' \<and>
      c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
    by (rule finite_initial_label_split_range_costed_top_level_correct_and_seen_progress_bound
      [OF all_reachable degree degree_factor R_pos insert_factor seen_factor
        source_factor k_pos source_progress step_seen_progress run])
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
    by (rule split_range_costed_bmssp_correct[OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  have U_V: "U = V"
    using post bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  have cost_U:
      "c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
    using combined by blast
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
    using correct cost_U graph_bound by linarith
qed

theorem finite_initial_label_split_range_costed_top_level_correct_and_scaled_seen_progress_graph_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and source_progress:
      "\<And>l d S B d' B' U c.
        split_range_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        card S \<le> M_of l \<Longrightarrow>
        card S \<le> card U"
    and step_scaled_seen_progress:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        split_range_costed_partition_loop_state \<Delta> M_of t h k cap l
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
        k * card S \<le> cap \<and> tree_antichain S \<and>
        (B' = B \<longrightarrow>
          card (find_pivots_seen_capped k cap d S B) \<le> card U)"
    and run:
      "split_range_costed_bmssp \<Delta> M_of t h k cap l finite_initial_label {s}
        Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * t) * edge_count"
proof -
  have combined:
    "sssp_correct d' \<and>
      c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
    by (rule finite_initial_label_split_range_costed_top_level_correct_and_scaled_seen_progress_bound
      [OF all_reachable degree degree_factor R_pos insert_factor insert_scaled_factor
        seen_scaled_factor source_factor k_pos source_progress
        step_scaled_seen_progress run])
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
    by (rule split_range_costed_bmssp_correct[OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  have U_V: "U = V"
    using post bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  have cost_U:
      "c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
    using combined by blast
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
    using correct cost_U graph_bound by linarith
qed

theorem range_costed_partition_loop_state_cost_bound:
  assumes run:
    "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c child_costs"
  shows "c \<le> sum_list child_costs + (M_of l) * length child_costs +
    t * (sum_list
      (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs)) +
      (M_of l) * length child_costs)"
  using run
  by (induction)
    (auto simp: pull_separates_def partition_pull_cost_bound_def
      partition_batch_cost_bound_def algebra_simps
      dest: range_costed_pull_cost_le_M range_costed_batch_cost_le)

theorem range_costed_partition_loop_state_cost_bound_by_child_sources:
  "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c child_costs \<Longrightarrow>
   \<exists>child_sources.
    length child_sources = length bs \<and>
    list_all2
      (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
        range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l)
      child_sources (range_tree_child_list P a bs) \<and>
    c \<le> sum_list child_costs + sum_list (map card child_sources) +
      t * (sum_list
        (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs)) +
        sum_list (map card child_sources))"
and range_costed_bmssp_child_sources_trivial:
  "range_costed_bmssp \<Delta> M_of t k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule:
    range_costed_partition_loop_state_range_costed_bmssp.inducts)
  case (Range_State_Done D a B d' P \<Delta> M_of t k cap l d)
  show ?case
    by (intro exI[of _ "[]"]) simp
next
  case (Range_State_Stop a B d' P k cap \<Delta> M_of t l d D)
  show ?case
    by (intro exI[of _ "[]"]) simp
next
  case (Range_State_Step D M_of l Bmax S_pull beta D_pull B d a b B'
      d' P k cap \<Delta> t d_child U_child c_child batch D_next c_pull
      c_batch betas bs Us_tail U_tail c_tail child_costs_tail c)
  obtain child_sources_tail where len_tail:
      "length child_sources_tail = length bs"
    and sources_tail:
      "list_all2
        (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
          range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l)
        child_sources_tail (range_tree_child_list P b bs)"
    and tail_cost:
      "c_tail \<le>
        sum_list child_costs_tail + sum_list (map card child_sources_tail) +
        t * (sum_list
          (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P b bs)) +
          sum_list (map card child_sources_tail))"
    using Range_State_Step.IH(11) by blast
  have card_pull: "card S_pull \<le> M_of l"
    using Range_State_Step unfolding pull_separates_def by blast
  have pull_cost: "c_pull \<le> card S_pull"
    using Range_State_Step
    unfolding partition_pull_cost_bound_def by blast
  have batch_cost:
    "c_batch \<le> t * (card (outgoing_edges U_child) + card S_pull)"
    by (rule range_costed_batch_cost_le
      [where d = d and S = S_pull and d_child = d_child and b = b
        and beta = beta and batch = batch and M = "card S_pull"])
      (use Range_State_Step in auto)
  let ?child_sources = "S_pull # child_sources_tail"
  have len: "length ?child_sources = length (b # bs)"
    using len_tail by simp
  have head_source:
    "\<exists>c_child' B_child d_child' B_child'.
      range_costed_bmssp \<Delta> M_of t k cap l d S_pull B_child
        d_child' B_child' U_child c_child' \<and>
      bmssp_pre_full d S_pull B_child \<and>
      (\<forall>x\<in>S_pull. reachable s x) \<and>
      card S_pull \<le> M_of l"
    using Range_State_Step card_pull by blast
  have sources:
    "list_all2
      (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
        range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l)
      ?child_sources (range_tree_child_list P a (b # bs))"
    using head_source sources_tail Range_State_Step by simp
  have cost:
    "c \<le> sum_list (c_child # child_costs_tail) +
      sum_list (map card ?child_sources) +
      t * (sum_list
        (map (\<lambda>X. card (outgoing_edges X))
          (range_tree_child_list P a (b # bs))) +
        sum_list (map card ?child_sources))"
  proof -
    have c_eq: "c = c_pull + c_batch + c_child + c_tail"
      using Range_State_Step by blast
    have "c_pull + c_batch + c_child + c_tail \<le>
        card S_pull + t * (card (outgoing_edges U_child) + card S_pull) +
        c_child +
        (sum_list child_costs_tail + sum_list (map card child_sources_tail) +
          t * (sum_list
            (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P b bs)) +
            sum_list (map card child_sources_tail)))"
      using pull_cost batch_cost tail_cost by simp
    also have "\<dots> =
        sum_list (c_child # child_costs_tail) +
        sum_list (map card ?child_sources) +
        t * (card (outgoing_edges U_child) +
          sum_list
            (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P b bs)) +
          sum_list (map card ?child_sources))"
      by (simp add: algebra_simps)
    also have "\<dots> =
        sum_list (c_child # child_costs_tail) +
        sum_list (map card ?child_sources) +
        t * (sum_list
          (map (\<lambda>X. card (outgoing_edges X))
            (range_tree_child_list P a (b # bs))) +
          sum_list (map card ?child_sources))"
      using Range_State_Step by simp
    finally show ?thesis
      using c_eq by simp
  qed
  show ?case
    by (intro exI[of _ ?child_sources] conjI)
      (use len sources cost in simp_all)
next
  case (Range_Cost_Base S x \<Delta> M_of t k cap d B)
  show ?case
    by simp
next
  case (Range_Cost_Step D k cap d S B c_insert t \<Delta> M_of l d' a betas bs B'
      Us U_loop c_loop child_costs_loop U c)
  show ?case
    by simp
qed

theorem range_costed_partition_loop_state_cost_from_child_and_source_bounds:
  assumes run:
    "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child U_child.
        c_child \<le> level_range_cost_bound A R L U_child)
        child_costs (range_tree_child_list P a bs)"
    and source_progress:
      "\<And>S_child B_child d_child B_child' U_child c_child.
        \<lbrakk>range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> card S_child \<le> card U_child"
  shows "c \<le>
    A * L * card (range_tree_chain P a bs B') +
    (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
    Suc t * card (range_tree_chain P a bs B')"
proof -
  obtain child_sources where len_sources:
      "length child_sources = length bs"
    and sources:
      "list_all2
        (\<lambda>S_child U_child. \<exists>c_child B_child d_child B_child'.
          range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l)
        child_sources (range_tree_child_list P a bs)"
    and cost:
      "c \<le> sum_list child_costs + sum_list (map card child_sources) +
        t * (sum_list
          (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs)) +
          sum_list (map card child_sources))"
    using range_costed_partition_loop_state_cost_bound_by_child_sources[OF run]
    by blast
  have mono: "nondecreasing_from a bs"
    by (rule range_costed_partition_loop_state_mono[OF run])
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
        "range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
          d_child B_child' U_child c_child"
      and child_pre: "bmssp_pre_full d S_child B_child"
      and child_reaches: "\<forall>x\<in>S_child. reachable s x"
      and child_card: "card S_child \<le> M_of l"
      using Cons.hyps by blast
    have head: "card S_child \<le> card U_child"
      by (rule source_progress[OF child child_pre _ child_card])
        (use child_reaches in blast)
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
      t * (card (outgoing_edges (range_tree_chain P a bs B')) +
        sum_list (map card child_sources))"
  proof -
    have tail:
      "t * (sum_list
          (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs)) +
          sum_list (map card child_sources)) \<le>
       t * (card (outgoing_edges (range_tree_chain P a bs B')) +
          sum_list (map card child_sources))"
      using edge_sum by simp
    have "sum_list child_costs + sum_list (map card child_sources) +
        t * (sum_list
          (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs)) +
          sum_list (map card child_sources)) \<le>
        A * L * card (range_tree_chain P a bs B') +
        R * card (outgoing_edges (range_tree_chain P a bs B')) +
        sum_list (map card child_sources) +
        t * (card (outgoing_edges (range_tree_chain P a bs B')) +
          sum_list (map card child_sources))"
      using child_sum tail by linarith
    then show ?thesis
      using cost by linarith
  qed
  also have "\<dots> \<le>
      A * L * card (range_tree_chain P a bs B') +
      (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
      Suc t * card (range_tree_chain P a bs B')"
  proof -
    have source_part:
      "sum_list (map card child_sources) +
        t * sum_list (map card child_sources) \<le>
       Suc t * card (range_tree_chain P a bs B')"
    proof -
      have t_part:
        "t * sum_list (map card child_sources) \<le>
          t * card (range_tree_chain P a bs B')"
        using source_sum by simp
      have "sum_list (map card child_sources) +
          t * sum_list (map card child_sources) \<le>
        card (range_tree_chain P a bs B') +
          t * card (range_tree_chain P a bs B')"
        using source_sum t_part by linarith
      then show ?thesis
        by (simp add: algebra_simps)
    qed
    show ?thesis
      using source_part by (simp add: algebra_simps)
  qed
  finally show ?thesis .
qed

theorem range_costed_partition_loop_state_cost_from_child_cost_bounds:
  assumes run:
    "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child U_child.
        c_child \<le> level_range_cost_bound A R L U_child)
        child_costs (range_tree_child_list P a bs)"
  shows "c \<le>
    A * L * card (range_tree_chain P a bs B') +
    (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
    (Suc t) * (M_of l) * length bs"
proof -
  have child_len: "length child_costs = length bs"
    by (rule range_costed_partition_loop_state_child_call_ranges(1)[OF run])
  have cost:
    "c \<le> sum_list child_costs + (M_of l) * length child_costs +
      t * (sum_list
        (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs)) +
        (M_of l) * length child_costs)"
    by (rule range_costed_partition_loop_state_cost_bound[OF run])
  have mono: "nondecreasing_from a bs"
    by (rule range_costed_partition_loop_state_mono[OF run])
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
      (M_of l) * length bs +
      t * (card (outgoing_edges (range_tree_chain P a bs B')) +
        (M_of l) * length bs)"
  proof -
    have middle:
      "(M_of l) * length child_costs = (M_of l) * length bs"
      using child_len by simp
    have tail:
      "t * (sum_list
          (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs)) +
          (M_of l) * length child_costs) \<le>
       t * (card (outgoing_edges (range_tree_chain P a bs B')) +
          (M_of l) * length bs)"
    proof -
      have "sum_list
          (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs)) +
          (M_of l) * length child_costs \<le>
        card (outgoing_edges (range_tree_chain P a bs B')) +
          (M_of l) * length bs"
        using edge_sum middle by linarith
      then show ?thesis
        by simp
    qed
    have "sum_list child_costs + (M_of l) * length child_costs +
        t * (sum_list
          (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list P a bs)) +
          (M_of l) * length child_costs) \<le>
        A * L * card (range_tree_chain P a bs B') +
        R * card (outgoing_edges (range_tree_chain P a bs B')) +
        (M_of l) * length bs +
        t * (card (outgoing_edges (range_tree_chain P a bs B')) +
          (M_of l) * length bs)"
      using child_sum middle tail by linarith
    then show ?thesis
      using cost by linarith
  qed
  also have "\<dots> =
      A * L * card (range_tree_chain P a bs B') +
      (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
      (Suc t) * (M_of l) * length bs"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem range_costed_partition_loop_state_child_cost_bounds:
  assumes run:
    "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
  shows "list_all2 (\<lambda>c_child U_child.
      c_child \<le> level_range_cost_bound A R L U_child)
    child_costs (range_tree_child_list P a bs)"
proof -
  have calls:
    "list_all2
      (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
        range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l)
      child_costs (range_tree_child_list P a bs)"
    by (rule range_costed_partition_loop_state_child_call_ranges(2)[OF run])
  show ?thesis
    using calls
  proof (induction rule: list_all2_induct)
    case Nil
    then show ?case by simp
  next
    case (Cons c_child child_costs U_child child_sets)
    obtain S_child B_child d_child B_child' where child:
        "range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
          d_child B_child' U_child c_child"
      and child_pre: "bmssp_pre_full d S_child B_child"
      and child_reaches: "\<forall>x\<in>S_child. reachable s x"
      and child_card: "card S_child \<le> M_of l"
      using Cons.hyps by blast
    have head:
      "c_child \<le> level_range_cost_bound A R L U_child"
      by (rule child_bound[OF child child_pre _ child_card])
        (use child_reaches in blast)
    show ?case
      using head Cons.IH Cons.hyps by simp
  qed
qed

theorem range_costed_partition_loop_state_cost_from_child_bound:
  assumes run:
    "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
  shows "c \<le>
    A * L * card (range_tree_chain P a bs B') +
    (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
    (Suc t) * (M_of l) * length bs"
proof -
  have child_cost_bounds:
    "list_all2 (\<lambda>c_child U_child.
      c_child \<le> level_range_cost_bound A R L U_child)
      child_costs (range_tree_child_list P a bs)"
    by (rule range_costed_partition_loop_state_child_cost_bounds
      [OF run child_bound])
  show ?thesis
    by (rule range_costed_partition_loop_state_cost_from_child_cost_bounds
      [OF run child_cost_bounds])
qed

theorem range_costed_partition_loop_state_trace:
  "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
     betas bs B' Us U c child_costs \<Longrightarrow>
   sound_label d \<Longrightarrow>
   bmssp_pre_full d P B \<Longrightarrow>
   (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
   concrete_partition_loop_trace P B a bs d' B' Us U"
and range_costed_bmssp_correct:
  "range_costed_bmssp \<Delta> M_of t k cap l d S B d' B' U c \<Longrightarrow>
   sound_label d \<Longrightarrow>
   bmssp_pre_full d S B \<Longrightarrow>
   (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
   bmssp_post_full d S B d' B' U"
proof (induction rule:
    range_costed_partition_loop_state_range_costed_bmssp.inducts)
  case (Range_State_Done D a B d' P \<Delta> M_of t k cap l d)
  have a_le: "bound_le (Fin a) B"
    using Range_State_Done by blast
  have complete_B: "complete_on d' (bound_tree P B)"
    using Range_State_Done by blast
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
  case (Range_State_Stop a B d' P k cap \<Delta> M_of t l d D)
  then show ?case
    unfolding concrete_partition_loop_trace_def complete_on_def by simp
next
  case Range_State_Step
  then show ?case
    unfolding concrete_partition_loop_trace_def bmssp_post_full_def
      complete_preserved_def
    by (auto split: bound.splits)
next
  case (Range_Cost_Base S x \<Delta> M_of t k cap d B)
  have post:
    "bmssp_post d S B
      (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
      (base_case_bound k x B)
      (base_case_vertices k x B)"
    using base_case_result_bmssp_post[OF Range_Cost_Base.hyps,
        where k = k and B = B and d = d]
    unfolding base_case_result_def by simp
  then show ?case
    by (rule bmssp_post_imp_post_full)
next
  case (Range_Cost_Step D k cap d S B c_insert t \<Delta> M_of l d' a
      betas bs B' Us U_loop c_loop child_costs_loop U c)
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  let ?W = "{v \<in> bound_tree S B'. ?d_fp v = dist s v}"
  have sound_fp: "sound_label ?d_fp"
    unfolding find_pivots_label_capped_def
    by (rule fp_iter_capped_label_sound[OF Range_Cost_Step.prems(1)
      Range_Cost_Step.prems(3)])
  have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
    using find_pivots_capped_establishes_pivot_pre_concrete
      [OF Range_Cost_Step.prems(1) Range_Cost_Step.prems(2)
        Range_Cost_Step.prems(3)] .
  have P_subset_S: "?P \<subseteq> S"
    unfolding find_pivots_pivots_capped_def by auto
  have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
    using P_subset_S Range_Cost_Step.prems(3) by blast
  have trace:
    "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
    using Range_Cost_Step.IH sound_fp pivot_pre P_reaches by blast
  have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
    by (rule concrete_partition_loop_trace_post[OF trace])
  have le: "bound_le B' B"
    using loop_post unfolding bmssp_post_full_def by blast
  have U_tree: "U = bound_tree S B'"
  proof -
    have "U_loop \<union> ?W = bound_tree S B'"
      by (rule concrete_capped_find_pivots_final_tree_assembly
        [OF Range_Cost_Step.prems(1) Range_Cost_Step.prems(2)
          Range_Cost_Step.prems(3) loop_post])
    then show ?thesis
      using Range_Cost_Step(6) by simp
  qed
  have loop_complete: "complete_on d' U_loop"
    using loop_post unfolding bmssp_post_full_def by blast
  have U_complete: "complete_on d' U"
    using complete_on_Un[OF loop_complete Range_Cost_Step(5)]
      Range_Cost_Step(6) by simp
  show ?case
    using le U_tree U_complete unfolding bmssp_post_full_def by blast
qed

theorem range_costed_bmssp_source_card_le_if_label_below_output:
  assumes run:
      "range_costed_bmssp \<Delta> M_of t k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and complete: "complete_on d S"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B'"
  shows "card S \<le> card U"
proof -
  have post: "bmssp_post_full d S B d' B' U"
    by (rule range_costed_bmssp_correct[OF run sound pre S_reaches])
  show ?thesis
    by (rule bmssp_post_full_source_card_le_if_label_below_output
      [OF post complete S_reaches below])
qed

theorem range_costed_bmssp_source_card_le_if_sound_label_below_output:
  assumes run:
      "range_costed_bmssp \<Delta> M_of t k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B'"
  shows "card S \<le> card U"
proof -
  have post: "bmssp_post_full d S B d' B' U"
    by (rule range_costed_bmssp_correct[OF run sound pre S_reaches])
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

theorem range_costed_partition_loop_state_success_or_threshold:
  "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c child_costs \<Longrightarrow>
   sound_label d \<Longrightarrow>
   bmssp_pre_full d P B \<Longrightarrow>
   (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
   B' = B \<or> k * cap \<le> card U"
and range_costed_bmssp_success_or_threshold_trivial:
  "range_costed_bmssp \<Delta> M_of t k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule: range_costed_partition_loop_state_range_costed_bmssp.inducts)
  case (Range_State_Done D a B d' P \<Delta> M_of t k cap l d)
  then show ?case
    by simp
next
  case (Range_State_Stop a B d' P k cap \<Delta> M_of t l d D)
  then show ?case
    by simp
next
  case (Range_State_Step D M_of l Bmax S_pull beta D_pull B d a b B_out
      d_out P k cap Delta t d_child U_child c_child batch D_next c_pull
      c_batch betas bs Us_tail U_tail c_tail child_costs_tail c)
  have tail:
    "B_out = B \<or> k * cap \<le> card U_tail"
    using Range_State_Step.IH Range_State_Step.prems by blast
  then show ?case
  proof
    assume "B_out = B"
    then show ?thesis
      by blast
  next
    assume threshold_tail: "k * cap \<le> card U_tail"
    have tail_trace:
      "concrete_partition_loop_trace P B b bs d_out B_out Us_tail U_tail"
      by (rule range_costed_partition_loop_state_trace)
        (use Range_State_Step in blast)+
    have U_tail_def:
      "U_tail = bound_tree P (Fin b) \<union> \<Union>(set Us_tail)"
      using tail_trace unfolding concrete_partition_loop_trace_def by blast
    have split_b:
      "bound_tree P (Fin b) =
        bound_tree P (Fin a) \<union> range_tree P a (Fin b)"
      using bound_tree_split_at[of a "Fin b" P] Range_State_Step
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
  case (Range_Cost_Base S x \<Delta> M_of t k cap d B)
  then show ?case
    by simp
next
  case (Range_Cost_Step D k cap d S B c_insert t \<Delta> M_of l d' a betas bs B'
      Us U_loop c_loop child_costs_loop U c)
  then show ?case
    by simp
qed

theorem range_costed_bmssp_Suc_success_or_threshold:
  assumes run:
      "range_costed_bmssp \<Delta> M_of t k cap (Suc l) d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "B' = B \<or> k * cap \<le> card U"
  using run
proof cases
  case (Range_Cost_Step D c_insert a betas bs Us U_loop c_loop child_costs_loop)
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
    by (rule range_costed_partition_loop_state_success_or_threshold
      [OF Range_Cost_Step(3) sound_fp pivot_pre P_reaches])
  have loop_trace:
    "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
    by (rule range_costed_partition_loop_state_trace
      [OF Range_Cost_Step(3) sound_fp pivot_pre P_reaches])
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
      using Range_Cost_Step(5) by simp
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

theorem range_costed_bmssp_Suc_source_card_le_from_complete_sources:
  assumes run:
      "range_costed_bmssp \<Delta> M_of t k cap (Suc l) d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and complete: "complete_on d S"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and S_cap: "card S \<le> cap"
    and k_pos: "0 < k"
  shows "card S \<le> card U"
proof -
  have call_class: "B' = B \<or> k * cap \<le> card U"
    by (rule range_costed_bmssp_Suc_success_or_threshold
      [OF run sound pre S_reaches])
  then show ?thesis
  proof
    assume B'_eq: "B' = B"
    show ?thesis
    proof (rule range_costed_bmssp_source_card_le_if_label_below_output
        [OF run sound pre S_reaches complete])
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

theorem range_costed_bmssp_Suc_source_card_le_from_label_below:
  assumes run:
      "range_costed_bmssp \<Delta> M_of t k cap (Suc l) d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and S_cap: "card S \<le> cap"
    and k_pos: "0 < k"
  shows "card S \<le> card U"
proof -
  have call_class: "B' = B \<or> k * cap \<le> card U"
    by (rule range_costed_bmssp_Suc_success_or_threshold
      [OF run sound pre S_reaches])
  then show ?thesis
  proof
    assume B'_eq: "B' = B"
    show ?thesis
    proof (rule range_costed_bmssp_source_card_le_if_sound_label_below_output
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

theorem range_costed_capped_step_threshold_if_not_success:
  assumes loop:
      "range_costed_partition_loop_state \<Delta> M_of t k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
        Us U_loop c_loop child_costs"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v}"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and not_success: "B' \<noteq> B"
  shows "k * cap \<le> card U"
proof -
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
    by (rule range_costed_partition_loop_state_success_or_threshold
      [OF loop sound_fp pivot_pre P_reaches])
  have threshold_loop: "k * cap \<le> card U_loop"
    using loop_class not_success by blast
  have trace: "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
    by (rule range_costed_partition_loop_state_trace
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

theorem range_costed_capped_step_scan_insert_budget_if_not_success:
  assumes degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and insert_factor: "t \<le> A * k"
    and insert:
      "partition_initial_insert_cost_bound c_insert t
        (find_pivots_pivots_capped k cap d S B)"
    and loop:
      "range_costed_partition_loop_state \<Delta> M_of t k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
        Us U_loop c_loop child_costs"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v}"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and S_cap: "card S \<le> cap"
    and not_success: "B' \<noteq> B"
  shows "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
    2 * A * card U"
proof -
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have progress: "k * cap \<le> card U"
    by (rule range_costed_capped_step_threshold_if_not_success
      [OF loop U_def sound pre S_reaches not_success])
  show ?thesis
    by (rule find_pivots_scan_and_initial_insert_budget_from_progress
      [OF S_subset degree S_cap insert degree_factor insert_factor progress])
qed

theorem range_costed_partition_loop_state_closes_level_bound_general:
  assumes run:
    "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and overhead: "(Suc t) * (M_of l) * length bs \<le> A * card U"
  shows "c \<le> A * Suc L * card U + (R + t) * card (outgoing_edges U)"
proof -
  have trace: "concrete_partition_loop_trace P B a bs d' B' Us U"
    by (rule range_costed_partition_loop_state_trace
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
      (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
      (Suc t) * (M_of l) * length bs"
    by (rule range_costed_partition_loop_state_cost_from_child_bound
      [OF run child_bound])
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
    have "A * L * card (range_tree_chain P a bs B') +
        (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
        (Suc t) * (M_of l) * length bs \<le>
        A * L * card U + (R + t) * card (outgoing_edges U) + A * card U"
      using vterm eterm overhead by linarith
    then show ?thesis
      using loop by linarith
  qed
  also have "\<dots> =
      A * Suc L * card U + (R + t) * card (outgoing_edges U)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem range_costed_partition_loop_state_closes_level_bound_from_source_progress_general:
  assumes run:
    "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and source_progress:
      "\<And>S_child B_child d_child B_child' U_child c_child.
        \<lbrakk>range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> card S_child \<le> card U_child"
    and source_factor: "Suc t \<le> A"
  shows "c \<le> A * Suc L * card U + (R + t) * card (outgoing_edges U)"
proof -
  have trace: "concrete_partition_loop_trace P B a bs d' B' Us U"
    by (rule range_costed_partition_loop_state_trace
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
  have child_cost_bounds:
    "list_all2 (\<lambda>c_child U_child.
      c_child \<le> level_range_cost_bound A R L U_child)
      child_costs (range_tree_child_list P a bs)"
    by (rule range_costed_partition_loop_state_child_cost_bounds
      [OF run child_bound])
  have loop:
    "c \<le>
      A * L * card (range_tree_chain P a bs B') +
      (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
      Suc t * card (range_tree_chain P a bs B')"
    by (rule range_costed_partition_loop_state_cost_from_child_and_source_bounds
      [OF run child_cost_bounds source_progress])
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
      "Suc t * card (range_tree_chain P a bs B') \<le> A * card U"
    proof -
      have "Suc t * card (range_tree_chain P a bs B') \<le>
          A * card (range_tree_chain P a bs B')"
        by (rule mult_right_mono[OF source_factor]) simp
      also have "\<dots> \<le> A * card U"
        using card_chain_le by simp
      finally show ?thesis .
    qed
    have "A * L * card (range_tree_chain P a bs B') +
        (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
        Suc t * card (range_tree_chain P a bs B') \<le>
        A * L * card U + (R + t) * card (outgoing_edges U) + A * card U"
      using vterm eterm source_term by linarith
    then show ?thesis
      using loop by linarith
  qed
  also have "\<dots> =
      A * Suc L * card U + (R + t) * card (outgoing_edges U)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem range_costed_partition_loop_state_closes_level_bound_from_child_cost_bounds_general:
  assumes run:
    "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child U_child.
        c_child \<le> level_range_cost_bound A R L U_child)
        child_costs (range_tree_child_list P a bs)"
    and overhead: "(Suc t) * (M_of l) * length bs \<le> A * card U"
  shows "c \<le> A * Suc L * card U + (R + t) * card (outgoing_edges U)"
proof -
  have trace: "concrete_partition_loop_trace P B a bs d' B' Us U"
    by (rule range_costed_partition_loop_state_trace
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
      (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
      (Suc t) * (M_of l) * length bs"
    by (rule range_costed_partition_loop_state_cost_from_child_cost_bounds
      [OF run child_cost_bounds])
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
    have "A * L * card (range_tree_chain P a bs B') +
        (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
        (Suc t) * (M_of l) * length bs \<le>
        A * L * card U + (R + t) * card (outgoing_edges U) + A * card U"
      using vterm eterm overhead by linarith
    then show ?thesis
      using loop by linarith
  qed
  also have "\<dots> =
      A * Suc L * card U + (R + t) * card (outgoing_edges U)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem range_costed_partition_loop_state_closes_level_bound:
  assumes run:
    "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R l U_child"
    and overhead: "(Suc t) * (M_of l) * length bs \<le> A * card U"
  shows "c \<le> A * Suc l * card U + (R + t) * card (outgoing_edges U)"
proof -
  have trace: "concrete_partition_loop_trace P B a bs d' B' Us U"
    by (rule range_costed_partition_loop_state_trace
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
      A * l * card (range_tree_chain P a bs B') +
      (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
      (Suc t) * (M_of l) * length bs"
    by (rule range_costed_partition_loop_state_cost_from_child_bound
      [OF run child_bound])
  have "c \<le>
      A * l * card U + (R + t) * card (outgoing_edges U) + A * card U"
  proof -
    have vterm:
      "A * l * card (range_tree_chain P a bs B') \<le> A * l * card U"
      using card_chain_le by simp
    have eterm:
      "(R + t) * card (outgoing_edges (range_tree_chain P a bs B')) \<le>
       (R + t) * card (outgoing_edges U)"
      using card_out_le by simp
    have "A * l * card (range_tree_chain P a bs B') +
        (R + t) * card (outgoing_edges (range_tree_chain P a bs B')) +
        (Suc t) * (M_of l) * length bs \<le>
        A * l * card U + (R + t) * card (outgoing_edges U) + A * card U"
      using vterm eterm overhead by linarith
    then show ?thesis
      using loop by linarith
  qed
  also have "\<dots> =
      A * Suc l * card U + (R + t) * card (outgoing_edges U)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem range_costed_nonbase_step_closes_level_bound_general:
  assumes loop:
    "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U_loop c_loop child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and overhead: "(Suc t) * (M_of l) * length bs \<le> A * card U_loop"
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
    by (rule range_costed_partition_loop_state_closes_level_bound_general
      [OF loop sound pre P_reaches child_bound overhead])
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

theorem range_costed_nonbase_step_closes_level_bound_from_source_progress_general:
  assumes loop:
    "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U_loop c_loop child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L U_child"
    and source_progress:
      "\<And>S_child B_child d_child B_child' U_child c_child.
        \<lbrakk>range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> card S_child \<le> card U_child"
    and source_factor: "Suc t \<le> A"
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
    by (rule range_costed_partition_loop_state_closes_level_bound_from_source_progress_general
      [OF loop sound pre P_reaches child_bound source_progress source_factor])
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

theorem range_costed_nonbase_step_closes_level_bound_from_child_cost_bounds_general:
  assumes loop:
    "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U_loop c_loop child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child U_child.
        c_child \<le> level_range_cost_bound A R L U_child)
        child_costs (range_tree_child_list P a bs)"
    and overhead: "(Suc t) * (M_of l) * length bs \<le> A * card U_loop"
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
    by (rule
      range_costed_partition_loop_state_closes_level_bound_from_child_cost_bounds_general
      [OF loop sound pre P_reaches child_cost_bounds overhead])
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

theorem range_costed_nonbase_step_closes_level_bound:
  assumes loop:
    "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U_loop c_loop child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>range_costed_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R l U_child"
    and overhead: "(Suc t) * (M_of l) * length bs \<le> A * card U_loop"
    and U_def: "U = U_loop \<union> W"
    and finite_U: "finite U"
    and scan_insert: "c_scan_insert \<le> A * card U"
    and c_def: "c = c_scan_insert + c_loop"
  shows "c \<le> A * Suc (Suc l) * card U +
    (R + t) * card (outgoing_edges U)"
proof -
  have loop_bound:
    "c_loop \<le> A * Suc l * card U_loop +
      (R + t) * card (outgoing_edges U_loop)"
    by (rule range_costed_partition_loop_state_closes_level_bound
      [OF loop sound pre P_reaches child_bound overhead])
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
      (A * Suc l * card U + (R + t) * card (outgoing_edges U))"
  proof -
    have loop_to_U:
      "c_loop \<le> A * Suc l * card U +
        (R + t) * card (outgoing_edges U)"
    proof -
      have "A * Suc l * card U_loop \<le> A * Suc l * card U"
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
      A * Suc (Suc l) * card U + (R + t) * card (outgoing_edges U)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem range_costed_base_level_bound:
  assumes R_pos: "0 < R"
  shows "base_case_scan_cost \<Delta> k x B \<le>
    level_range_cost_bound A R (Suc 0) (base_case_vertices k x B)"
proof -
  have "base_case_scan_cost \<Delta> k x B \<le>
      R * card (outgoing_edges (base_case_vertices k x B))"
    using R_pos unfolding base_case_scan_cost_def by simp
  then show ?thesis
    unfolding level_range_cost_bound_def by linarith
qed

text \<open>
  The unsplit relation repeats the same recurrence in a form that is closer to
  the abstract cost interface.  The base theorem
  @{thm range_costed_base_level_bound} pays for the bounded base scan with the
  outgoing-edge component of @{const level_range_cost_bound}.  The main theorem
  below then performs induction on the recursion level: the induction
  hypothesis bounds each child call, while the supplied local-budget hypotheses
  pay for loop overhead and FindPivots overhead at the current level.

  This theorem is intentionally parameterised by the constants \<open>A\<close>, \<open>R\<close>,
  \<open>t\<close>, and \<open>M_of\<close>.  Later theories instantiate those parameters with the
  BMSSP schedule and with the bucketed partition costs, but the recurrence
  itself does not depend on how the partition primitive is implemented.
\<close>

theorem range_costed_bmssp_level_bound_from_local_budgets:
  assumes base_budget: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and loop_budget:
      "\<And>l d P B d' D a betas bs B' Us U c child_costs.
        range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
          betas bs B' Us U c child_costs \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d P B \<Longrightarrow>
        (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
        (Suc t) * (M_of l) * length bs \<le> A * card U"
    and step_budget:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        range_costed_partition_loop_state \<Delta> M_of t k cap l
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
        fp_iter_capped_scan_cost k cap d S S B + c_insert \<le> A * card U"
    and run:
      "range_costed_bmssp \<Delta> M_of t k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "c \<le> level_range_cost_bound A (R + l * t) (2 * l + 1) U"
  using run sound pre S_reaches
proof (induction l arbitrary: d S B d' B' U c rule: less_induct)
  case (less l)
  show ?case
  proof (cases l)
    case 0
    have run0:
      "range_costed_bmssp \<Delta> M_of t k cap 0 d S B d' B' U c"
      using less.prems(1) 0 by simp
    show ?thesis
      using run0 R_pos 0
      by (cases rule: range_costed_bmssp.cases)
        (simp_all add: range_costed_base_level_bound)
  next
    case (Suc l0)
    have run_suc:
      "range_costed_bmssp \<Delta> M_of t k cap (Suc l0) d S B d' B' U c"
      using less.prems(1) Suc by simp
    show ?thesis
    proof (cases rule: range_costed_bmssp_SucE[OF run_suc])
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
        unfolding find_pivots_pivots_capped_def by auto
      have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
        using P_subset_S less.prems(4) by blast
      have child_bound:
        "\<And>c_child U_child S_child B_child d_child B_child'.
          \<lbrakk>range_costed_bmssp \<Delta> M_of t k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child;
            bmssp_pre_full ?d_fp S_child B_child;
            \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
            card S_child \<le> M_of l0\<rbrakk>
          \<Longrightarrow> c_child \<le> level_range_cost_bound A (R + l0 * t)
            (2 * l0 + 1) U_child"
      proof -
        fix c_child U_child S_child B_child d_child B_child'
        assume child:
            "range_costed_bmssp \<Delta> M_of t k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child"
          and child_pre: "bmssp_pre_full ?d_fp S_child B_child"
          and child_reaches: "\<And>x. x \<in> S_child \<Longrightarrow> reachable s x"
        show "c_child \<le> level_range_cost_bound A (R + l0 * t)
            (2 * l0 + 1) U_child"
          by (rule less.IH[of l0 ?d_fp S_child B_child d_child B_child'
                U_child c_child, OF _ child sound_fp child_pre child_reaches])
            (simp add: Suc)
      qed
      have overhead:
        "(Suc t) * (M_of l0) * length bs \<le> A * card U_loop"
        by (rule loop_budget[OF 1(4) sound_fp pivot_pre P_reaches])
      have scan_insert:
        "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
          A * card U"
        by (rule step_budget[OF refl 1(3) 1(4) 1(5) 1(1)
            less.prems(2) less.prems(3) less.prems(4)])
      have trace:
        "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
        by (rule range_costed_partition_loop_state_trace
          [OF 1(4) sound_fp pivot_pre P_reaches])
      have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
        by (rule concrete_partition_loop_trace_post[OF trace])
      have finite_U_loop: "finite U_loop"
        using loop_post unfolding bmssp_post_full_def by simp
      have finite_W: "finite ?W"
        by simp
      have finite_U: "finite U"
        using 1(1) finite_U_loop finite_W by simp
      have step:
        "c \<le> A * Suc (Suc (2 * l0 + 1)) * card U +
          (R + l0 * t + t) * card (outgoing_edges U)"
        by (rule range_costed_nonbase_step_closes_level_bound_general
          [OF 1(4) sound_fp pivot_pre P_reaches child_bound overhead
            1(1) finite_U scan_insert 1(2)])
      show ?thesis
        using step Suc unfolding level_range_cost_bound_def
        by (simp add: algebra_simps)
    qed
  qed
qed

theorem range_costed_bmssp_level_bound_from_source_progress_and_local_budgets:
  assumes base_budget: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and source_factor: "Suc t \<le> A"
    and source_progress:
      "\<And>l d S B d' B' U c.
        range_costed_bmssp \<Delta> M_of t k cap l d S B d' B' U c \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        card S \<le> M_of l \<Longrightarrow>
        card S \<le> card U"
    and step_budget:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        range_costed_partition_loop_state \<Delta> M_of t k cap l
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
        fp_iter_capped_scan_cost k cap d S S B + c_insert \<le> A * card U"
    and run:
      "range_costed_bmssp \<Delta> M_of t k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "c \<le> level_range_cost_bound A (R + l * t) (2 * l + 1) U"
  using run sound pre S_reaches
proof (induction l arbitrary: d S B d' B' U c rule: less_induct)
  case (less l)
  show ?case
  proof (cases l)
    case 0
    have run0:
      "range_costed_bmssp \<Delta> M_of t k cap 0 d S B d' B' U c"
      using less.prems(1) 0 by simp
    show ?thesis
      using run0 R_pos 0
      by (cases rule: range_costed_bmssp.cases)
        (simp_all add: range_costed_base_level_bound)
  next
    case (Suc l0)
    have run_suc:
      "range_costed_bmssp \<Delta> M_of t k cap (Suc l0) d S B d' B' U c"
      using less.prems(1) Suc by simp
    show ?thesis
    proof (cases rule: range_costed_bmssp_SucE[OF run_suc])
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
        unfolding find_pivots_pivots_capped_def by auto
      have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
        using P_subset_S less.prems(4) by blast
      have child_bound:
        "\<And>c_child U_child S_child B_child d_child B_child'.
          \<lbrakk>range_costed_bmssp \<Delta> M_of t k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child;
            bmssp_pre_full ?d_fp S_child B_child;
            \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
            card S_child \<le> M_of l0\<rbrakk>
          \<Longrightarrow> c_child \<le> level_range_cost_bound A (R + l0 * t)
            (2 * l0 + 1) U_child"
      proof -
        fix c_child U_child S_child B_child d_child B_child'
        assume child:
            "range_costed_bmssp \<Delta> M_of t k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child"
          and child_pre: "bmssp_pre_full ?d_fp S_child B_child"
          and child_reaches: "\<And>x. x \<in> S_child \<Longrightarrow> reachable s x"
        show "c_child \<le> level_range_cost_bound A (R + l0 * t)
            (2 * l0 + 1) U_child"
          by (rule less.IH[of l0 ?d_fp S_child B_child d_child B_child'
                U_child c_child, OF _ child sound_fp child_pre child_reaches])
            (simp add: Suc)
      qed
      have source_progress_loop:
        "\<And>S_child B_child d_child B_child' U_child c_child.
          \<lbrakk>range_costed_bmssp \<Delta> M_of t k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child;
            bmssp_pre_full ?d_fp S_child B_child;
            \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
            card S_child \<le> M_of l0\<rbrakk>
          \<Longrightarrow> card S_child \<le> card U_child"
        by (rule source_progress)
      have scan_insert:
        "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
          A * card U"
        by (rule step_budget[OF refl 1(3) 1(4) 1(5) 1(1)
            less.prems(2) less.prems(3) less.prems(4)])
      have trace:
        "concrete_partition_loop_trace ?P B a bs d' B' Us U_loop"
        by (rule range_costed_partition_loop_state_trace
          [OF 1(4) sound_fp pivot_pre P_reaches])
      have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
        by (rule concrete_partition_loop_trace_post[OF trace])
      have finite_U_loop: "finite U_loop"
        using loop_post unfolding bmssp_post_full_def by simp
      have finite_W: "finite ?W"
        by simp
      have finite_U: "finite U"
        using 1(1) finite_U_loop finite_W by simp
      have step:
        "c \<le> A * Suc (Suc (2 * l0 + 1)) * card U +
          (R + l0 * t + t) * card (outgoing_edges U)"
        by (rule range_costed_nonbase_step_closes_level_bound_from_source_progress_general
          [OF 1(4) sound_fp pivot_pre P_reaches child_bound
            source_progress_loop source_factor 1(1) finite_U scan_insert 1(2)])
      show ?thesis
        using step Suc unfolding level_range_cost_bound_def
        by (simp add: algebra_simps)
    qed
  qed
qed

theorem range_costed_bmssp_level_bound_from_source_progress_budgets:
  assumes degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and source_factor: "Suc t \<le> 2 * A"
    and source_progress:
      "\<And>l d S B d' B' U c.
        range_costed_bmssp \<Delta> M_of t k cap l d S B d' B' U c \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        card S \<le> M_of l \<Longrightarrow>
        card S \<le> card U"
    and step_progress:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        range_costed_partition_loop_state \<Delta> M_of t k cap l
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
        card S \<le> cap \<and> k * cap \<le> card U"
    and run:
      "range_costed_bmssp \<Delta> M_of t k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
proof (rule range_costed_bmssp_level_bound_from_source_progress_and_local_budgets
    [where A = "2 * A" and R = R,
      OF _ R_pos source_factor _ _ run sound pre S_reaches])
  show "\<Delta> \<le> 2 * A"
    using degree_factor by simp
next
  fix l d S B d' B' U c
  assume child:
      "range_costed_bmssp \<Delta> M_of t k cap l d S B d' B' U c"
    and child_pre: "bmssp_pre_full d S B"
    and child_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and child_card: "card S \<le> M_of l"
  show "card S \<le> card U"
    by (rule source_progress[OF child child_pre child_reaches child_card])
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
      "range_costed_partition_loop_state \<Delta> M_of t k cap l
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
  have S_subset: "S \<subseteq> V"
    using pre_s unfolding bmssp_pre_full_def by blast
  have progress:
      "card S \<le> cap \<and> k * cap \<le> card U"
    by (rule step_progress[OF D_def insert loop complete U_def sound_s pre_s reaches_s])
  then have S_cap: "card S \<le> cap"
    by blast
  from progress have U_progress: "k * cap \<le> card U"
    by blast
  show "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
      2 * A * card U"
    by (rule find_pivots_scan_and_initial_insert_budget_from_progress
      [OF S_subset degree S_cap insert degree_factor insert_factor U_progress])
qed

theorem range_costed_bmssp_level_bound_from_progress_budgets:
  assumes degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and loop_factor: "Suc t \<le> 2 * A"
    and loop_progress:
      "\<And>l d P B d' D a betas bs B' Us U c child_costs.
        range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
          betas bs B' Us U c child_costs \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d P B \<Longrightarrow>
        (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
        (M_of l) * length bs \<le> card U"
    and step_progress:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        range_costed_partition_loop_state \<Delta> M_of t k cap l
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
        card S \<le> cap \<and> k * cap \<le> card U"
    and run:
      "range_costed_bmssp \<Delta> M_of t k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
proof (rule range_costed_bmssp_level_bound_from_local_budgets
    [where A = "2 * A" and R = R,
      OF _ R_pos _ _ run sound pre S_reaches])
  show "\<Delta> \<le> 2 * A"
    using degree_factor by simp
next
  fix l d P B d' D a betas bs B' Us U c child_costs
  assume loop:
      "range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
        betas bs B' Us U c child_costs"
    and sound_l: "sound_label d"
    and pre_l: "bmssp_pre_full d P B"
    and reaches_l: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
  have progress: "(M_of l) * length bs \<le> card U"
    by (rule loop_progress[OF loop sound_l pre_l reaches_l])
  show "(Suc t) * (M_of l) * length bs \<le> 2 * A * card U"
    by (rule loop_overhead_budget_from_progress[OF loop_factor progress])
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
      "range_costed_partition_loop_state \<Delta> M_of t k cap l
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
  have S_subset: "S \<subseteq> V"
    using pre_s unfolding bmssp_pre_full_def by blast
  have progress:
      "card S \<le> cap \<and> k * cap \<le> card U"
    by (rule step_progress[OF D_def insert loop complete U_def sound_s pre_s reaches_s])
  then have S_cap: "card S \<le> cap"
    by blast
  from progress have U_progress: "k * cap \<le> card U"
    by blast
  show "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
      2 * A * card U"
    by (rule find_pivots_scan_and_initial_insert_budget_from_progress
      [OF S_subset degree S_cap insert degree_factor insert_factor U_progress])
qed

theorem finite_initial_label_range_costed_top_level_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and run:
      "range_costed_bmssp \<Delta> M_of t k cap l finite_initial_label {s}
        Infinity d' Infinity U c"
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
    by (rule range_costed_bmssp_correct[OF run sound pre S_reaches])
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

theorem finite_initial_label_range_costed_top_level_correct_and_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and loop_factor: "Suc t \<le> 2 * A"
    and loop_progress:
      "\<And>l d P B d' D a betas bs B' Us U c child_costs.
        range_costed_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
          betas bs B' Us U c child_costs \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d P B \<Longrightarrow>
        (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
        (M_of l) * length bs \<le> card U"
    and step_progress:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        range_costed_partition_loop_state \<Delta> M_of t k cap l
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
        card S \<le> cap \<and> k * cap \<le> card U"
    and run:
      "range_costed_bmssp \<Delta> M_of t k cap l finite_initial_label {s}
        Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
proof
  show "sssp_correct d'"
    by (rule finite_initial_label_range_costed_top_level_correct
      [OF all_reachable run])
next
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  show "c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
    by (rule range_costed_bmssp_level_bound_from_progress_budgets
      [OF degree degree_factor R_pos insert_factor loop_factor loop_progress
        step_progress run sound pre S_reaches])
qed

theorem finite_initial_label_range_costed_top_level_correct_and_source_progress_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and source_factor: "Suc t \<le> 2 * A"
    and source_progress:
      "\<And>l d S B d' B' U c.
        range_costed_bmssp \<Delta> M_of t k cap l d S B d' B' U c \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        card S \<le> M_of l \<Longrightarrow>
        card S \<le> card U"
    and step_progress:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        range_costed_partition_loop_state \<Delta> M_of t k cap l
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
        card S \<le> cap \<and> k * cap \<le> card U"
    and run:
      "range_costed_bmssp \<Delta> M_of t k cap l finite_initial_label {s}
        Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
proof
  show "sssp_correct d'"
    by (rule finite_initial_label_range_costed_top_level_correct
      [OF all_reachable run])
next
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  show "c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
    by (rule range_costed_bmssp_level_bound_from_source_progress_budgets
      [OF degree degree_factor R_pos insert_factor source_factor source_progress
        step_progress run sound pre S_reaches])
qed

theorem finite_initial_label_range_costed_top_level_correct_and_graph_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and source_factor: "Suc t \<le> 2 * A"
    and source_progress:
      "\<And>l d S B d' B' U c.
        range_costed_bmssp \<Delta> M_of t k cap l d S B d' B' U c \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        card S \<le> M_of l \<Longrightarrow>
        card S \<le> card U"
    and step_progress:
      "\<And>l d S B D c_insert d' a betas bs B' Us U_loop c_loop
          child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        range_costed_partition_loop_state \<Delta> M_of t k cap l
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
        card S \<le> cap \<and> k * cap \<le> card U"
    and run:
      "range_costed_bmssp \<Delta> M_of t k cap l finite_initial_label {s}
        Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> 2 * A * (2 * l + 1) * vertex_count + (R + l * t) * edge_count"
proof -
  have combined:
    "sssp_correct d' \<and>
      c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
    by (rule finite_initial_label_range_costed_top_level_correct_and_source_progress_bound
      [OF all_reachable degree degree_factor R_pos insert_factor source_factor
        source_progress step_progress run])
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
    by (rule range_costed_bmssp_correct[OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  have U_V: "U = V"
    using post bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  have cost_U:
      "c \<le> level_range_cost_bound (2 * A) (R + l * t) (2 * l + 1) U"
    using combined by blast
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
    using correct cost_U graph_bound by linarith
qed

end

end
