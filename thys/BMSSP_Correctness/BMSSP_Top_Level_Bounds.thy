theory BMSSP_Top_Level_Bounds
  imports BMSSP_Strict_Tie_Breaking BMSSP_Exact_Concrete_Cost
begin

section \<open>Top-Level BMSSP Theorems\<close>

text \<open>
  This theory is the entry point for the checked correctness result for the
  top-level BMSSP algorithm modelled in this development.  Everything before
  this point proves local correctness and local cost statements: FindPivots
  preserves the complete-source invariant, the partition loop realizes the
  recursive BMSSP step, and the concrete partition operations account for
  Insert, BatchPrepend, and Pull.  This file is where those ingredients are
  closed over a root call and converted into the single-source shortest-path
  headline.

  The algorithmic run relations used here are the strongest ones in the
  project.  They record the capped FindPivots step, the exact pulled child
  source, the range-synchronised recursive calls, and the separated edge and
  source batch costs.  The early theorems therefore look a little verbose:
  their purpose is to expose a precise bridge from the executable recurrence to
  the abstract correctness theorem while retaining enough cost structure for
  the asymptotic proof.

  The locale assumption is the paper's tie-breaking consequence: shortest paths
  form a strict tree order.  Under that assumption, the proof instantiates the
  BMSSP parameters with @{const sssp_log_one_third_param} and
  @{const sssp_log_two_thirds_param}.  These correspond to the paper's
  \<open>log^{1/3} n\<close> and \<open>log^{2/3} n\<close> scales.  The level capacity is computed by
  @{const bmssp_level_cap}; the point of the schedule is that the recursive
  tree depth, pivot growth, and bucketed partition cost telescope into the
  target \<open>O(m * log^{2/3} n)\<close> envelope.

  The file proceeds in four stages.  First, it proves root-level correctness
  for operational and costed runs.  Second, it specializes the refined graph
  bound to the logarithmic parameter schedule.  Third, it packages the least
  top-level execution cost as a function and proves Big-O bounds for it.
  Finally, it exposes locale-level headline theorems that downstream theories
  can cite without reopening the cost recurrence.
\<close>

context strict_tie_breaking_digraph
begin

theorem operational_range_split_algorithm_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and run:
      "full_operational_bmssp k cap l
        finite_initial_label {s} Infinity d' Infinity U"
  shows "U = V \<and> sssp_correct d'"
proof
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
  show "U = V"
    using post bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  show "sssp_correct d'"
    using finite_initial_label_full_operational_top_level_correct
      [OF all_reachable run] .
qed

theorem operational_range_split_algorithm_reachable_correct:
  assumes run:
      "full_operational_bmssp k cap l
        finite_initial_label {s} Infinity d' Infinity U"
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
    by (rule full_operational_bmssp_correct[OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  then show ?thesis
    by (rule successful_root_bmssp_sssp_correct)
qed

theorem range_split_algorithm_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and run:
      "exact_split_range_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "U = V \<and> sssp_correct d'"
proof
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  have post_full:
    "bmssp_post_full finite_initial_label {s} Infinity d' Infinity U"
    by (rule exact_split_range_costed_bmssp_correct
      [OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  show "U = V"
    using post bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  show "sssp_correct d'"
    by (rule finite_initial_label_exact_split_range_costed_top_level_correct
      [OF all_reachable run])
qed

theorem range_split_algorithm_reachable_correct:
  assumes run:
      "exact_split_range_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
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
    by (rule exact_split_range_costed_bmssp_correct
      [OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  then show ?thesis
    by (rule successful_root_bmssp_sssp_correct)
qed

theorem direct_insert_algorithm_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and run:
      "direct_insert_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "U = V \<and> sssp_correct d'"
proof
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
  show "U = V"
    using post bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  show "sssp_correct d'"
    by (rule finite_initial_label_direct_insert_costed_top_level_correct
      [OF all_reachable run])
qed

theorem direct_insert_algorithm_reachable_correct:
  assumes run:
      "direct_insert_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d'"
  by (rule finite_initial_label_direct_insert_costed_top_level_reachable_correct[OF run])

theorem direct_insert_algorithm_correct_and_refined_graph_bound_under_edge_budget:
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
  shows "U = V \<and> sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. H)
      (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
proof -
  have UV_correct: "U = V \<and> sssp_correct d'"
    by (rule direct_insert_algorithm_correct[OF all_reachable run])
  have cost:
    "sssp_correct d' \<and>
      c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. H)
        (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
    by (rule finite_initial_label_direct_insert_costed_top_level_correct_and_closed_bmssp_refined_graph_time_bound_level_cap
      [OF all_reachable degree degree_factor R_pos insert_factor insert_scaled_factor
        seen_scaled_factor source_factor k_pos edge_budget run])
  show ?thesis
    using UV_correct cost by blast
qed

theorem direct_insert_algorithm_correct_and_refined_graph_bound_trivial_edge_budget:
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
  shows "U = V \<and> sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. t + h)
      (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
proof -
  have UV_correct: "U = V \<and> sssp_correct d'"
    by (rule direct_insert_algorithm_correct[OF all_reachable run])
  have cost:
    "sssp_correct d' \<and>
      c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. t + h)
        (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
    by (rule finite_initial_label_direct_insert_costed_top_level_correct_and_closed_bmssp_refined_graph_time_bound_level_cap_trivial_edge_budget
      [OF all_reachable degree degree_factor R_pos insert_factor insert_scaled_factor
        seen_scaled_factor source_factor k_pos run])
  show ?thesis
    using UV_correct cost by blast
qed

theorem direct_insert_algorithm_correct_and_refined_graph_bound_amortized:
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
  shows "U = V \<and> sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. h)
      (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
proof -
  have UV_correct: "U = V \<and> sssp_correct d'"
    by (rule direct_insert_algorithm_correct[OF all_reachable run])
  have cost:
    "sssp_correct d' \<and>
      c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. h)
        (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
    by (rule finite_initial_label_direct_insert_costed_top_level_correct_and_closed_bmssp_refined_graph_time_bound_level_cap_amortized
      [OF all_reachable degree degree_factor R_pos insert_factor insert_scaled_factor
        seen_scaled_factor source_factor k_pos run])
  show ?thesis
    using UV_correct cost by blast
qed

text \<open>
  The preceding theorems keep the parameters abstract.  They are useful because
  they show exactly which inequalities are required of a costed BMSSP run:
  outdegree must be bounded, Insert must be charged at the chosen parameter
  scale, and the source and seen-set terms must fit into the refined graph
  bound @{const bmssp_refined_graph_time_bound}.  The amortized variant is the
  one that matches the bucketed partition analysis: the split work is not
  charged to each operation eagerly, but through the aggregate accounting used
  by the partition interface.

  The next group substitutes the logarithmic schedule.  The one-third
  parameter controls the number of levels and source growth, while the
  two-thirds parameter controls the Insert scale supplied to the partition
  layer.  The simple arithmetic lemmas in @{const sssp_log_one_third_param} and
  @{const sssp_log_two_thirds_param} prove that these choices satisfy the
  abstract side conditions.
\<close>

theorem direct_insert_algorithm_correct_and_refined_graph_bound_log_params_bounded_degree:
  fixes N p q :: nat
  defines p_def: "p \<equiv> sssp_log_one_third_param N"
    and q_def: "q \<equiv> sssp_log_two_thirds_param N"
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and run:
      "direct_insert_costed_bmssp \<Delta> (bmssp_level_cap p q) q p p
        (bmssp_level_cap p q p) p
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "U = V \<and> sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc \<Delta> * p) (\<lambda>_. q) (\<lambda>_. p)
      (\<lambda>_. p) (\<lambda>_. q) (\<lambda>_. edge_count) vertex_count"
proof -
  have p_pos: "0 < p"
    unfolding p_def by simp
  have q_pos: "0 < q"
    unfolding q_def by simp
  have q_le_square: "q \<le> p * p"
    unfolding p_def q_def
    by (rule sssp_log_two_thirds_param_le_one_third_square)
  have degree_factor: "\<Delta> \<le> Suc \<Delta> * p"
    using p_pos by (cases p) simp_all
  have insert_factor: "q \<le> (Suc \<Delta> * p) * p"
  proof -
    have "p * p \<le> (Suc \<Delta> * p) * p"
      by simp
    then show ?thesis
      using q_le_square by linarith
  qed
  have insert_scaled_factor: "q \<le> p * p"
    using q_le_square .
  have seen_scaled_factor: "p * \<Delta> + p \<le> 2 * (Suc \<Delta> * p)"
  proof -
    have "p * \<Delta> + p = Suc \<Delta> * p"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> 2 * (Suc \<Delta> * p)"
      by simp
    finally show ?thesis .
  qed
  have source_factor: "Suc p \<le> 2 * (Suc \<Delta> * p)"
  proof -
    have "Suc p \<le> 2 * p"
      using p_pos by simp
    also have "\<dots> \<le> 2 * (Suc \<Delta> * p)"
      by simp
    finally show ?thesis .
  qed
  show ?thesis
    by (rule direct_insert_algorithm_correct_and_refined_graph_bound_amortized
      [OF all_reachable degree degree_factor q_pos insert_factor
        insert_scaled_factor seen_scaled_factor source_factor p_pos run])
qed

theorem direct_insert_algorithm_correct_and_refined_graph_bound_log_params_fixed_degree:
  fixes N D p q :: nat
  defines p_def: "p \<equiv> sssp_log_one_third_param N"
    and q_def: "q \<equiv> sssp_log_two_thirds_param N"
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and run:
      "direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p
        (bmssp_level_cap p q p) p
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "U = V \<and> sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * p) (\<lambda>_. q) (\<lambda>_. p)
      (\<lambda>_. p) (\<lambda>_. q) (\<lambda>_. edge_count) vertex_count"
proof -
  have run':
    "direct_insert_costed_bmssp D
      (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N))
      (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)
      (sssp_log_one_third_param N)
      (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N)
        (sssp_log_one_third_param N))
      (sssp_log_one_third_param N)
      finite_initial_label {s} Infinity d' Infinity U c"
    using run unfolding p_def q_def by simp
  show ?thesis
    unfolding p_def q_def
    by (rule direct_insert_algorithm_correct_and_refined_graph_bound_log_params_bounded_degree
      [OF all_reachable degree run'])
qed

theorem exact_concrete_algorithm_correct_and_refined_graph_bound_log_params_fixed_degree:
  fixes N D p q :: nat
  defines p_def: "p \<equiv> sssp_log_one_third_param N"
    and q_def: "q \<equiv> sssp_log_two_thirds_param N"
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and run:
      "exact_concrete_bmssp D (bmssp_level_cap p q) q p p
        (bmssp_level_cap p q p) p
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "U = V \<and> sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * p) (\<lambda>_. q) (\<lambda>_. p)
      (\<lambda>_. p) (\<lambda>_. q) (\<lambda>_. edge_count) vertex_count"
proof -
  have direct_run:
    "direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p
      (bmssp_level_cap p q p) p
      finite_initial_label {s} Infinity d' Infinity U c"
    by (rule exact_concrete_bmssp_refines_direct_insert[OF run])
  have direct_run':
    "direct_insert_costed_bmssp D
      (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N))
      (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)
      (sssp_log_one_third_param N)
      (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N)
        (sssp_log_one_third_param N))
      (sssp_log_one_third_param N)
      finite_initial_label {s} Infinity d' Infinity U c"
    using direct_run unfolding p_def q_def by simp
  show ?thesis
    unfolding p_def q_def
    by (rule direct_insert_algorithm_correct_and_refined_graph_bound_log_params_fixed_degree
      [OF all_reachable degree direct_run'])
qed

text \<open>
  The definitions below package the root execution as an ordinary total cost
  predicate.  \<open>exact_concrete_top_level_run\<close> fixes the root source set to
  @{term "{s}"} and the input bound to @{term Infinity}; the auxiliary
  \<open>exact_concrete_root_run\<close> keeps the returned bound visible for existence
  proofs that reason about threshold cases.  The least-cost wrapper
  \<open>exact_concrete_top_level_time\<close> is not an algorithm in its own right; it is
  a mathematical way to speak about the cost of any concrete run satisfying the
  checked run relation.
\<close>

definition exact_concrete_top_level_run ::
  "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> bool" where
  "exact_concrete_top_level_run D N d' U c \<longleftrightarrow>
     (let p = sssp_log_one_third_param N;
          q = sssp_log_two_thirds_param N
      in exact_concrete_bmssp D (bmssp_level_cap p q) q p p
        (bmssp_level_cap p q p) p
        finite_initial_label {s} Infinity d' Infinity U c)"

definition exact_concrete_root_run ::
  "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bound \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> bool" where
  "exact_concrete_root_run D N d' B' U c \<longleftrightarrow>
     (let p = sssp_log_one_third_param N;
          q = sssp_log_two_thirds_param N
      in exact_concrete_bmssp D (bmssp_level_cap p q) q p p
        (bmssp_level_cap p q p) p
        finite_initial_label {s} Infinity d' B' U c)"

lemma exact_concrete_top_level_run_root_run_iff:
  "exact_concrete_top_level_run D N d' U c \<longleftrightarrow>
    exact_concrete_root_run D N d' Infinity U c"
  unfolding exact_concrete_top_level_run_def exact_concrete_root_run_def
  by (simp add: Let_def)

definition exact_concrete_top_level_cost :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "exact_concrete_top_level_cost D N c \<longleftrightarrow>
     (\<exists>d' U. exact_concrete_top_level_run D N d' U c)"

definition exact_concrete_top_level_time :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "exact_concrete_top_level_time D N =
     (LEAST c. exact_concrete_top_level_cost D N c)"

lemma exact_concrete_top_level_cost_exists_if_top_pivots_empty:
  assumes pivots_empty:
    "find_pivots_pivots_capped (sssp_log_one_third_param N)
      (bmssp_level_cap (sssp_log_one_third_param N)
        (sssp_log_two_thirds_param N) (sssp_log_one_third_param N))
      finite_initial_label {s} Infinity = {}"
  shows "\<exists>c. exact_concrete_top_level_cost D N c"
proof -
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  have p_eq: "?p = Suc (?p - 1)"
    using sssp_log_one_third_param_pos[of N] by simp
  have source_subset: "{s} \<subseteq> V"
    using source_in_V by simp
  have run:
    "\<exists>d' U c.
      exact_concrete_bmssp D (bmssp_level_cap ?p ?q) ?q ?p ?p
        (bmssp_level_cap ?p ?q ?p) (Suc (?p - 1))
        finite_initial_label {s} Infinity d' Infinity U c"
    by (rule exact_concrete_bmssp_Suc_exists_if_pivots_empty_same_bound
      [OF source_subset _ pivots_empty]) simp
  then obtain d' U c where
    "exact_concrete_bmssp D (bmssp_level_cap ?p ?q) ?q ?p ?p
      (bmssp_level_cap ?p ?q ?p) (Suc (?p - 1))
      finite_initial_label {s} Infinity d' Infinity U c"
    by blast
  then have root_run:
    "exact_concrete_bmssp D (bmssp_level_cap ?p ?q) ?q ?p ?p
      (bmssp_level_cap ?p ?q ?p) ?p
      finite_initial_label {s} Infinity d' Infinity U c"
    using p_eq by simp
  have "exact_concrete_top_level_run D N d' U c"
    unfolding exact_concrete_top_level_run_def
    using root_run by (simp add: Let_def)
  then have "exact_concrete_top_level_cost D N c"
    unfolding exact_concrete_top_level_cost_def by blast
  then show ?thesis
    by blast
qed

lemma exact_concrete_top_level_cost_exists_from_initial_loop:
  fixes D N p q cap l :: nat
    and d_fp :: "'a \<Rightarrow> real"
    and P :: "'a set"
  defines p_def: "p \<equiv> sssp_log_one_third_param N"
    and q_def: "q \<equiv> sssp_log_two_thirds_param N"
    and cap_def: "cap \<equiv> bmssp_level_cap p q p"
    and l_def: "l \<equiv> p - 1"
    and d_fp_def:
      "d_fp \<equiv> find_pivots_label_capped p cap finite_initial_label {s}
        Infinity"
    and P_def:
      "P \<equiv> find_pivots_pivots_capped p cap finite_initial_label {s}
        Infinity"
  assumes loop:
      "\<And>D_part. exact_partition_initial_state q d_fp P D_part
        (q * card P) \<Longrightarrow>
        \<exists>d' a betas bs Us U_loop c_loop child_costs_loop.
          exact_concrete_partition_loop_state D (bmssp_level_cap p q)
            q p p cap l d_fp P Infinity d' D_part a betas bs Infinity
            Us U_loop c_loop child_costs_loop \<and>
          complete_on d'
            {v \<in> bound_tree {s} Infinity. d_fp v = dist s v}"
  shows "\<exists>c. exact_concrete_top_level_cost D N c"
proof -
  have p_eq: "p = Suc l"
    using sssp_log_one_third_param_pos[of N]
    unfolding p_def l_def by simp
  have source_subset: "{s} \<subseteq> V"
    using source_in_V by simp
  obtain D_part where init:
    "exact_partition_initial_state q d_fp P D_part (q * card P)"
    using exact_partition_initial_state_exists_for_capped_pivots_with_cost
      [OF source_subset]
    unfolding d_fp_def P_def by blast
  obtain d' a betas bs Us U_loop c_loop child_costs_loop where
    loop_run:
      "exact_concrete_partition_loop_state D (bmssp_level_cap p q)
        q p p cap l d_fp P Infinity d' D_part a betas bs Infinity
        Us U_loop c_loop child_costs_loop"
    and complete:
      "complete_on d'
        {v \<in> bound_tree {s} Infinity. d_fp v = dist s v}"
    using loop[OF init] by blast
  have init_actual:
    "exact_partition_initial_state q
      (find_pivots_label_capped p cap finite_initial_label {s} Infinity)
      (find_pivots_pivots_capped p cap finite_initial_label {s} Infinity)
      D_part
      (q * card
        (find_pivots_pivots_capped p cap finite_initial_label {s}
          Infinity))"
    using init unfolding d_fp_def P_def .
  have loop_actual:
    "exact_concrete_partition_loop_state D (bmssp_level_cap p q)
      q p p cap l
      (find_pivots_label_capped p cap finite_initial_label {s} Infinity)
      (find_pivots_pivots_capped p cap finite_initial_label {s} Infinity)
      Infinity d' D_part a betas bs Infinity Us U_loop c_loop
      child_costs_loop"
    using loop_run unfolding d_fp_def P_def .
  have complete_actual:
    "complete_on d'
      {v \<in> bound_tree {s} Infinity.
        find_pivots_label_capped p cap finite_initial_label {s}
          Infinity v = dist s v}"
    using complete unfolding d_fp_def .
  let ?U =
    "U_loop \<union>
      {v \<in> bound_tree {s} Infinity.
        find_pivots_label_capped p cap finite_initial_label {s}
          Infinity v = dist s v}"
  have run_root_suc:
    "exact_concrete_bmssp D (bmssp_level_cap p q) q p p cap (Suc l)
      finite_initial_label {s} Infinity d' Infinity ?U
      (fp_iter_capped_scan_cost p cap finite_initial_label {s} {s} Infinity +
        q * card
          (find_pivots_pivots_capped p cap finite_initial_label {s}
            Infinity) + c_loop)"
    by (rule exact_concrete_bmssp_step_with_exact_insert_cost
      [OF init_actual loop_actual complete_actual refl])
  let ?c =
    "fp_iter_capped_scan_cost p cap finite_initial_label {s} {s} Infinity +
      q * card
        (find_pivots_pivots_capped p cap finite_initial_label {s}
          Infinity) + c_loop"
  have run_root:
    "exact_concrete_bmssp D (bmssp_level_cap p q) q p p cap p
      finite_initial_label {s} Infinity d' Infinity ?U ?c"
    using run_root_suc p_eq by simp
  have "exact_concrete_top_level_run D N d' ?U ?c"
    unfolding exact_concrete_top_level_run_def
    using run_root
    by (simp add: Let_def p_def q_def cap_def)
  then have "exact_concrete_top_level_cost D N ?c"
    unfolding exact_concrete_top_level_cost_def by blast
  then show ?thesis
    by blast
qed

lemma exact_concrete_top_level_cost_exists_from_root_run_below_threshold:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and below_threshold:
      "vertex_count <
        sssp_log_one_third_param N *
        bmssp_level_cap (sssp_log_one_third_param N)
          (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)"
    and run: "exact_concrete_root_run D N d' B' U c"
  shows "\<exists>c. exact_concrete_top_level_cost D N c"
proof -
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  let ?cap = "bmssp_level_cap ?p ?q ?p"
  have p_pos: "0 < ?p"
    by simp
  have run_bmssp:
    "exact_concrete_bmssp D (bmssp_level_cap ?p ?q) ?q ?p ?p ?cap ?p
      finite_initial_label {s} Infinity d' B' U c"
    using run unfolding exact_concrete_root_run_def by (simp add: Let_def)
  have run_suc:
    "exact_concrete_bmssp D (bmssp_level_cap ?p ?q) ?q ?p ?p ?cap
      (Suc (?p - 1)) finite_initial_label {s} Infinity d' B' U c"
    using run_bmssp p_pos by simp
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have source_reaches:
    "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  have success_or_threshold: "B' = Infinity \<or> ?p * ?cap \<le> card U"
    by (rule exact_concrete_bmssp_Suc_success_or_threshold
      [OF run_suc sound pre source_reaches])
  have post: "bmssp_post_full finite_initial_label {s} Infinity d' B' U"
    by (rule exact_concrete_bmssp_correct
      [OF run_bmssp sound pre source_reaches])
  have U_subset: "U \<subseteq> V"
    using post unfolding bmssp_post_full_def bound_tree_def by blast
  have card_U_le: "card U \<le> vertex_count"
    by (rule card_subset_vertex_count[OF U_subset])
  have not_threshold: "\<not> ?p * ?cap \<le> card U"
    using below_threshold card_U_le by linarith
  have B'_eq: "B' = Infinity"
    using success_or_threshold not_threshold by blast
  have top_run: "exact_concrete_top_level_run D N d' U c"
    using run B'_eq
    unfolding exact_concrete_top_level_run_root_run_iff
      exact_concrete_root_run_def
    by simp
  then have "exact_concrete_top_level_cost D N c"
    unfolding exact_concrete_top_level_cost_def by blast
  then show ?thesis
    by blast
qed

lemma eventually_exact_concrete_top_level_cost_if_root_runs_exist_below_threshold:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and below_threshold:
      "eventually
        (\<lambda>N. vertex_count <
          sssp_log_one_third_param N *
          bmssp_level_cap (sssp_log_one_third_param N)
            (sssp_log_two_thirds_param N) (sssp_log_one_third_param N))
        at_top"
    and root_runs:
      "eventually
        (\<lambda>N. \<exists>d' B' U c. exact_concrete_root_run D N d' B' U c)
        at_top"
  shows "eventually (\<lambda>N. \<exists>c. exact_concrete_top_level_cost D N c) at_top"
  using below_threshold root_runs
proof eventually_elim
  case (elim N)
  then obtain d' B' U c where run:
    "exact_concrete_root_run D N d' B' U c"
    by blast
  show ?case
    by (rule exact_concrete_top_level_cost_exists_from_root_run_below_threshold
      [OF all_reachable elim(1) run])
qed

lemma eventually_exact_concrete_top_level_cost_from_empty_top_pivots:
  "eventually (\<lambda>N. \<exists>c. exact_concrete_top_level_cost D N c) at_top"
  using eventually_top_level_pivots_empty
    [of finite_initial_label Infinity]
proof eventually_elim
  case (elim N)
  show ?case
    by (rule exact_concrete_top_level_cost_exists_if_top_pivots_empty
      [OF elim])
qed

lemma exact_concrete_top_level_time_witness:
  assumes "exact_concrete_top_level_cost D N c"
  shows "exact_concrete_top_level_cost D N
    (exact_concrete_top_level_time D N)"
  unfolding exact_concrete_top_level_time_def
  by (rule LeastI_ex) (use assms in blast)

lemma exact_concrete_top_level_time_le:
  assumes "exact_concrete_top_level_cost D N c"
  shows "exact_concrete_top_level_time D N \<le> c"
  unfolding exact_concrete_top_level_time_def
  by (rule Least_le) (rule assms)

lemma eventually_exact_concrete_top_level_cost_if_all:
  assumes "\<And>N. \<exists>c. exact_concrete_top_level_cost D N c"
  shows "eventually (\<lambda>N. \<exists>c. exact_concrete_top_level_cost D N c) at_top"
  by (rule eventuallyI) (rule assms)

lemma eventually_exact_concrete_top_level_cost_square_if_all:
  assumes "\<And>N. \<exists>c. exact_concrete_top_level_cost D N c"
  shows "eventually
    (\<lambda>N. \<exists>c. exact_concrete_top_level_cost D (N * N) c) at_top"
  by (rule eventuallyI) (rule assms)

theorem exact_concrete_top_level_run_correct_and_refined_bound_log_params_fixed_degree:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and run: "exact_concrete_top_level_run D N d' U c"
  shows "U = V \<and> sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. edge_count) vertex_count"
proof -
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  have run':
    "exact_concrete_bmssp D (bmssp_level_cap ?p ?q) ?q ?p ?p
      (bmssp_level_cap ?p ?q ?p) ?p
      finite_initial_label {s} Infinity d' Infinity U c"
    using run unfolding exact_concrete_top_level_run_def by (simp add: Let_def)
  show ?thesis
    by (rule exact_concrete_algorithm_correct_and_refined_graph_bound_log_params_fixed_degree
      [OF all_reachable degree run'])
qed

theorem exact_concrete_top_level_cost_refined_bound_log_params_fixed_degree:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and cost: "exact_concrete_top_level_cost D N c"
  shows "c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. edge_count) vertex_count"
proof -
  obtain d' U where run: "exact_concrete_top_level_run D N d' U c"
    using cost unfolding exact_concrete_top_level_cost_def by blast
  show ?thesis
    using exact_concrete_top_level_run_correct_and_refined_bound_log_params_fixed_degree
      [OF all_reachable degree run]
    by blast
qed

theorem exact_concrete_top_level_time_refined_bound_log_params_fixed_degree:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and run_exists: "exact_concrete_top_level_cost D N c"
  shows "exact_concrete_top_level_time D N \<le>
    bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. edge_count) vertex_count"
proof -
  have cost:
    "exact_concrete_top_level_cost D N (exact_concrete_top_level_time D N)"
    by (rule exact_concrete_top_level_time_witness[OF run_exists])
  show ?thesis
    by (rule exact_concrete_top_level_cost_refined_bound_log_params_fixed_degree
      [OF all_reachable degree cost])
qed

text \<open>
  From this point onward, the file is purely asymptotic.  The function
  \<open>T_bmssp\<close> abbreviates the least top-level concrete cost, and the
  following theorems compare it with increasingly convenient targets.  The
  central comparison target is @{const sssp_time_target}, which expands to an
  edge-count term multiplied by the two-thirds logarithmic factor.  The proofs
  reuse the complexity lemmas for @{const bmssp_refined_graph_time_bound}; no
  algorithmic invariant is reproved in this section.
\<close>

definition T_bmssp :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "T_bmssp D N = exact_concrete_top_level_time D N"

theorem T_bmssp_refined_bound_log_params_fixed_degree:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and run_exists: "exact_concrete_top_level_cost D N c"
  shows "T_bmssp D N \<le>
    bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. edge_count) vertex_count"
  unfolding T_bmssp_def
  by (rule exact_concrete_top_level_time_refined_bound_log_params_fixed_degree
    [OF all_reachable degree run_exists])

theorem T_bmssp_bigo_sssp_time_target_log_params_fixed_degree_if_exact_runs_exist:
  fixes m :: "nat \<Rightarrow> nat"
    and Cn Cm :: real
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and Cn_pos: "0 < Cn"
    and Cm_pos: "0 < Cm"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real vertex_count \<le> Cn * real (m n)) at_top"
    and edge_count_dominated:
      "eventually (\<lambda>n. real edge_count \<le> Cm * real (m n)) at_top"
    and exact_runs:
      "eventually (\<lambda>n. \<exists>c. exact_concrete_top_level_cost D n c) at_top"
  shows "(\<lambda>n. real (T_bmssp D n)) \<in> O(\<lambda>n. sssp_time_target m n)"
proof (rule bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree_slack
    [where D = D and Cn = Cn and Cm = Cm
      and v = "\<lambda>_. vertex_count" and m' = "\<lambda>_. edge_count"])
  show "0 < Cn"
    by (rule Cn_pos)
  show "0 < Cm"
    by (rule Cm_pos)
  show "eventually (\<lambda>n. real ((\<lambda>_. vertex_count) n) \<le>
      Cn * real (m n)) at_top"
    using vertex_count_dominated by simp
  show "eventually (\<lambda>n. real ((\<lambda>_. edge_count) n) \<le>
      Cm * real (m n)) at_top"
    using edge_count_dominated by simp
  show "eventually
      (\<lambda>n. T_bmssp D n \<le>
        bmssp_refined_graph_time_bound
          (\<lambda>_. Suc D * sssp_log_one_third_param n)
          (\<lambda>_. sssp_log_two_thirds_param n)
          (\<lambda>_. sssp_log_one_third_param n)
          (\<lambda>_. sssp_log_one_third_param n)
          (\<lambda>_. sssp_log_two_thirds_param n)
          (\<lambda>_. (\<lambda>_. edge_count) n) ((\<lambda>_. vertex_count) n)) at_top"
    using exact_runs
  proof eventually_elim
    case (elim n)
    then obtain c where cost: "exact_concrete_top_level_cost D n c"
      by blast
    show ?case
      by (rule T_bmssp_refined_bound_log_params_fixed_degree
        [OF all_reachable degree cost])
  qed
qed

theorem T_bmssp_bigo_sssp_time_target_square_size_params_fixed_degree_if_exact_runs_exist:
  fixes m :: "nat \<Rightarrow> nat"
    and Cn Cm :: real
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and Cn_pos: "0 < Cn"
    and Cm_pos: "0 < Cm"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real vertex_count \<le> Cn * real (m n)) at_top"
    and edge_count_dominated:
      "eventually (\<lambda>n. real edge_count \<le> Cm * real (m n)) at_top"
    and exact_runs:
      "eventually (\<lambda>n. \<exists>c. exact_concrete_top_level_cost D (n * n) c) at_top"
  shows "(\<lambda>n. real (T_bmssp D (n * n))) \<in>
    O(\<lambda>n. sssp_time_target m n)"
proof (rule bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree_square_arg_slack
    [where D = D and Cn = Cn and Cm = Cm
      and v = "\<lambda>_. vertex_count" and m' = "\<lambda>_. edge_count"])
  show "0 < Cn"
    by (rule Cn_pos)
  show "0 < Cm"
    by (rule Cm_pos)
  show "eventually (\<lambda>n. real ((\<lambda>_. vertex_count) n) \<le>
      Cn * real (m n)) at_top"
    using vertex_count_dominated by simp
  show "eventually (\<lambda>n. real ((\<lambda>_. edge_count) n) \<le>
      Cm * real (m n)) at_top"
    using edge_count_dominated by simp
  show "eventually
      (\<lambda>n. T_bmssp D (n * n) \<le>
        bmssp_refined_graph_time_bound
          (\<lambda>_. Suc D * sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. (\<lambda>_. edge_count) n) ((\<lambda>_. vertex_count) n)) at_top"
    using exact_runs
  proof eventually_elim
    case (elim n)
    then obtain c where cost: "exact_concrete_top_level_cost D (n * n) c"
      by blast
    show ?case
      by (rule T_bmssp_refined_bound_log_params_fixed_degree
        [OF all_reachable degree cost])
  qed
qed

theorem T_bmssp_bigo_edge_count_target_log_params_fixed_degree_if_exact_runs_exist:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and edge_count_pos: "0 < edge_count"
    and exact_runs:
      "eventually (\<lambda>n. \<exists>c. exact_concrete_top_level_cost D n c) at_top"
  shows "(\<lambda>n. real (T_bmssp D n)) \<in>
    O(\<lambda>n. sssp_time_target (\<lambda>_. edge_count) n)"
proof (rule T_bmssp_bigo_sssp_time_target_log_params_fixed_degree_if_exact_runs_exist
    [OF all_reachable degree, where Cn = 2 and Cm = 1])
  show "0 < (2::real)"
    by simp
  show "0 < (1::real)"
    by simp
  have vertex_le: "vertex_count \<le> 2 * edge_count"
    by (rule vertex_count_le_twice_edge_count_if_all_reachable
      [OF all_reachable edge_count_pos])
  show "eventually
      (\<lambda>n. real vertex_count \<le> 2 * real ((\<lambda>_. edge_count) n)) at_top"
    using vertex_le by simp
  show "eventually
      (\<lambda>n. real edge_count \<le> 1 * real ((\<lambda>_. edge_count) n)) at_top"
    by simp
  show "eventually (\<lambda>n. \<exists>c. exact_concrete_top_level_cost D n c) at_top"
    by (rule exact_runs)
qed

theorem T_bmssp_bigo_edge_count_target_log_params_fixed_degree:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and edge_count_pos: "0 < edge_count"
  shows "(\<lambda>n. real (T_bmssp D n)) \<in>
    O(\<lambda>n. sssp_time_target (\<lambda>_. edge_count) n)"
  by (rule T_bmssp_bigo_edge_count_target_log_params_fixed_degree_if_exact_runs_exist
    [OF all_reachable degree edge_count_pos
      eventually_exact_concrete_top_level_cost_from_empty_top_pivots])

theorem T_bmssp_bigo_size_target_log_params_fixed_degree:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
  shows "(\<lambda>n. real (T_bmssp D n)) \<in>
    O(\<lambda>n. sssp_time_target (\<lambda>_. Suc edge_count) n)"
proof (rule T_bmssp_bigo_sssp_time_target_log_params_fixed_degree_if_exact_runs_exist
    [OF all_reachable degree, where Cn = 1 and Cm = 1])
  show "0 < (1::real)"
    by simp
  show "0 < (1::real)"
    by simp
  have vertex_le: "vertex_count \<le> Suc edge_count"
    by (rule vertex_count_le_Suc_edge_count_if_all_reachable[OF all_reachable])
  show "eventually
      (\<lambda>n. real vertex_count \<le> 1 * real ((\<lambda>_. Suc edge_count) n)) at_top"
    using vertex_le by simp
  show "eventually
      (\<lambda>n. real edge_count \<le> 1 * real ((\<lambda>_. Suc edge_count) n)) at_top"
    by simp
  show "eventually (\<lambda>n. \<exists>c. exact_concrete_top_level_cost D n c) at_top"
    by (rule eventually_exact_concrete_top_level_cost_from_empty_top_pivots)
qed

theorem T_bmssp_bigo_target_log_params_fixed_degree_if_exact_runs_exist:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and edge_count_pos: "0 < edge_count"
    and exact_runs:
      "eventually (\<lambda>n. \<exists>c. exact_concrete_top_level_cost D n c) at_top"
  shows "(\<lambda>n. real (T_bmssp D n)) \<in>
    O(\<lambda>n. real edge_count * (ln (real n + 2)) powr (2 / 3))"
  using T_bmssp_bigo_edge_count_target_log_params_fixed_degree_if_exact_runs_exist
    [OF all_reachable degree edge_count_pos exact_runs]
  unfolding sssp_time_target_def sssp_log_factor_def by simp

theorem T_bmssp_bigo_target_log_params_fixed_degree_if_root_runs_exist_below_threshold:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and edge_count_pos: "0 < edge_count"
    and below_threshold:
      "eventually
        (\<lambda>N. vertex_count <
          sssp_log_one_third_param N *
          bmssp_level_cap (sssp_log_one_third_param N)
            (sssp_log_two_thirds_param N) (sssp_log_one_third_param N))
        at_top"
    and root_runs:
      "eventually
        (\<lambda>N. \<exists>d' B' U c. exact_concrete_root_run D N d' B' U c)
        at_top"
  shows "(\<lambda>n. real (T_bmssp D n)) \<in>
    O(\<lambda>n. real edge_count * (ln (real n + 2)) powr (2 / 3))"
proof (rule T_bmssp_bigo_target_log_params_fixed_degree_if_exact_runs_exist
    [OF all_reachable degree edge_count_pos])
  show "eventually (\<lambda>N. \<exists>c. exact_concrete_top_level_cost D N c) at_top"
    by (rule eventually_exact_concrete_top_level_cost_if_root_runs_exist_below_threshold
      [OF all_reachable below_threshold root_runs])
qed

theorem T_bmssp_bigo_target_log_params_fixed_degree_if_root_runs_exist:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and edge_count_pos: "0 < edge_count"
    and root_runs:
      "eventually
        (\<lambda>N. \<exists>d' B' U c. exact_concrete_root_run D N d' B' U c)
        at_top"
  shows "(\<lambda>n. real (T_bmssp D n)) \<in>
    O(\<lambda>n. real edge_count * (ln (real n + 2)) powr (2 / 3))"
proof (rule T_bmssp_bigo_target_log_params_fixed_degree_if_root_runs_exist_below_threshold
    [OF all_reachable degree edge_count_pos _ root_runs])
  show "eventually
      (\<lambda>N. vertex_count <
        sssp_log_one_third_param N *
        bmssp_level_cap (sssp_log_one_third_param N)
          (sssp_log_two_thirds_param N) (sssp_log_one_third_param N))
      at_top"
    by (rule eventually_top_level_threshold_exceeds_vertex_count)
qed

theorem T_bmssp_bigo_target_log_params_fixed_degree:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and edge_count_pos: "0 < edge_count"
  shows "(\<lambda>n. real (T_bmssp D n)) \<in>
    O(\<lambda>n. real edge_count * (ln (real n + 2)) powr (2 / 3))"
  using T_bmssp_bigo_edge_count_target_log_params_fixed_degree
    [OF all_reachable degree edge_count_pos]
  unfolding sssp_time_target_def sssp_log_factor_def by simp

theorem bmssp_runtime_bigo_target:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and edge_count_pos: "0 < edge_count"
  shows "(\<lambda>n. real (T_bmssp D n)) \<in>
    O(\<lambda>n. real edge_count * (ln (real n + 2)) powr (2 / 3))"
  by (rule T_bmssp_bigo_target_log_params_fixed_degree
    [OF all_reachable degree edge_count_pos])

theorem T_bmssp_bigo_target_log_params_fixed_degree_if_total:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and edge_count_pos: "0 < edge_count"
    and total: "\<And>N. \<exists>c. exact_concrete_top_level_cost D N c"
  shows "(\<lambda>n. real (T_bmssp D n)) \<in>
    O(\<lambda>n. real edge_count * (ln (real n + 2)) powr (2 / 3))"
  by (rule T_bmssp_bigo_target_log_params_fixed_degree_if_exact_runs_exist
    [OF all_reachable degree edge_count_pos
      eventually_exact_concrete_top_level_cost_if_all[OF total]])

theorem T_bmssp_bigo_edge_count_target_square_size_params_fixed_degree_if_exact_runs_exist:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and edge_count_pos: "0 < edge_count"
    and exact_runs:
      "eventually (\<lambda>n. \<exists>c. exact_concrete_top_level_cost D (n * n) c) at_top"
  shows "(\<lambda>n. real (T_bmssp D (n * n))) \<in>
    O(\<lambda>n. sssp_time_target (\<lambda>_. edge_count) n)"
proof (rule T_bmssp_bigo_sssp_time_target_square_size_params_fixed_degree_if_exact_runs_exist
    [OF all_reachable degree, where Cn = 2 and Cm = 1])
  show "0 < (2::real)"
    by simp
  show "0 < (1::real)"
    by simp
  have vertex_le: "vertex_count \<le> 2 * edge_count"
    by (rule vertex_count_le_twice_edge_count_if_all_reachable
      [OF all_reachable edge_count_pos])
  show "eventually
      (\<lambda>n. real vertex_count \<le> 2 * real ((\<lambda>_. edge_count) n)) at_top"
    using vertex_le by simp
  show "eventually
      (\<lambda>n. real edge_count \<le> 1 * real ((\<lambda>_. edge_count) n)) at_top"
    by simp
  show "eventually
      (\<lambda>n. \<exists>c. exact_concrete_top_level_cost D (n * n) c) at_top"
    by (rule exact_runs)
qed

theorem T_bmssp_bigo_target_square_size_params_fixed_degree_if_exact_runs_exist:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and edge_count_pos: "0 < edge_count"
    and exact_runs:
      "eventually (\<lambda>n. \<exists>c. exact_concrete_top_level_cost D (n * n) c) at_top"
  shows "(\<lambda>n. real (T_bmssp D (n * n))) \<in>
    O(\<lambda>n. real edge_count * (ln (real n + 2)) powr (2 / 3))"
  using T_bmssp_bigo_edge_count_target_square_size_params_fixed_degree_if_exact_runs_exist
    [OF all_reachable degree edge_count_pos exact_runs]
  unfolding sssp_time_target_def sssp_log_factor_def by simp

theorem T_bmssp_bigo_target_square_size_params_fixed_degree_if_total:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and edge_count_pos: "0 < edge_count"
    and total: "\<And>N. \<exists>c. exact_concrete_top_level_cost D N c"
  shows "(\<lambda>n. real (T_bmssp D (n * n))) \<in>
    O(\<lambda>n. real edge_count * (ln (real n + 2)) powr (2 / 3))"
  by (rule T_bmssp_bigo_target_square_size_params_fixed_degree_if_exact_runs_exist
    [OF all_reachable degree edge_count_pos
      eventually_exact_concrete_top_level_cost_square_if_all[OF total]])

theorem range_split_algorithm_correct_and_closed_graph_bound:
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
  shows "U = V \<and> sssp_correct d' \<and>
    c \<le> bmssp_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. l) (\<lambda>_. t)
      (\<lambda>_. edge_count) vertex_count"
proof -
  have UV_correct: "U = V \<and> sssp_correct d'"
    by (rule range_split_algorithm_correct[OF all_reachable run])
  have cost:
    "sssp_correct d' \<and>
      c \<le> bmssp_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. l) (\<lambda>_. t)
        (\<lambda>_. edge_count) vertex_count"
    by (rule finite_initial_label_exact_split_range_costed_top_level_correct_and_closed_bmssp_graph_time_bound_level_cap
      [OF all_reachable degree degree_factor R_pos insert_factor insert_scaled_factor
        seen_scaled_factor source_factor k_pos run])
  show ?thesis
    using UV_correct cost by blast
qed

theorem range_split_algorithm_correct_and_refined_graph_bound_under_edge_budget:
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
  shows "U = V \<and> sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. H)
      (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
proof -
  have UV_correct: "U = V \<and> sssp_correct d'"
    by (rule range_split_algorithm_correct[OF all_reachable run])
  have cost:
    "sssp_correct d' \<and>
      c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. H)
        (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
    by (rule finite_initial_label_exact_split_range_costed_top_level_correct_and_closed_bmssp_refined_graph_time_bound_level_cap
      [OF all_reachable degree degree_factor R_pos insert_factor insert_scaled_factor
        seen_scaled_factor source_factor k_pos edge_budget run])
  show ?thesis
    using UV_correct cost by blast
qed

theorem range_split_algorithm_correct_and_refined_graph_bound_trivial_edge_budget:
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
  shows "U = V \<and> sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. t)
      (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
proof -
  have UV_correct: "U = V \<and> sssp_correct d'"
    by (rule range_split_algorithm_correct[OF all_reachable run])
  have cost:
    "sssp_correct d' \<and>
      c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. t)
        (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
    by (rule finite_initial_label_exact_split_range_costed_top_level_correct_and_closed_bmssp_refined_graph_time_bound_level_cap_trivial_edge_budget
      [OF all_reachable degree degree_factor R_pos insert_factor insert_scaled_factor
        seen_scaled_factor source_factor k_pos run])
  show ?thesis
    using UV_correct cost by blast
qed

end

context positive_unique_shortest_digraph
begin

theorem positive_weight_direct_insert_algorithm_correct_and_refined_graph_bound_log_params_fixed_degree:
  fixes N D p q :: nat
  defines p_def: "p \<equiv> sssp_log_one_third_param N"
    and q_def: "q \<equiv> sssp_log_two_thirds_param N"
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and run:
      "direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p
        (bmssp_level_cap p q p) p
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "U = V \<and> sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * p) (\<lambda>_. q) (\<lambda>_. p)
      (\<lambda>_. p) (\<lambda>_. q) (\<lambda>_. edge_count) vertex_count"
proof -
  have run':
    "direct_insert_costed_bmssp D
      (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N))
      (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)
      (sssp_log_one_third_param N)
      (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N)
        (sssp_log_one_third_param N))
      (sssp_log_one_third_param N)
      finite_initial_label {s} Infinity d' Infinity U c"
    using run unfolding p_def q_def by simp
  show ?thesis
    unfolding p_def q_def
    by (rule direct_insert_algorithm_correct_and_refined_graph_bound_log_params_fixed_degree
      [OF all_reachable degree run'])
qed

theorem positive_weight_exact_concrete_algorithm_correct_and_refined_graph_bound_log_params_fixed_degree:
  fixes N D p q :: nat
  defines p_def: "p \<equiv> sssp_log_one_third_param N"
    and q_def: "q \<equiv> sssp_log_two_thirds_param N"
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and run:
      "exact_concrete_bmssp D (bmssp_level_cap p q) q p p
        (bmssp_level_cap p q p) p
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "U = V \<and> sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * p) (\<lambda>_. q) (\<lambda>_. p)
      (\<lambda>_. p) (\<lambda>_. q) (\<lambda>_. edge_count) vertex_count"
proof -
  have direct_run:
    "direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p
      (bmssp_level_cap p q p) p
      finite_initial_label {s} Infinity d' Infinity U c"
    by (rule exact_concrete_bmssp_refines_direct_insert[OF run])
  have direct_run':
    "direct_insert_costed_bmssp D
      (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N))
      (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)
      (sssp_log_one_third_param N)
      (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N)
        (sssp_log_one_third_param N))
      (sssp_log_one_third_param N)
      finite_initial_label {s} Infinity d' Infinity U c"
    using direct_run unfolding p_def q_def by simp
  show ?thesis
    unfolding p_def q_def
    by (rule positive_weight_direct_insert_algorithm_correct_and_refined_graph_bound_log_params_fixed_degree
      [OF all_reachable degree direct_run'])
qed

end

locale bounded_reduced_positive_instance = positive_unique_shortest_digraph +
  fixes D :: nat
  assumes all_vertices_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and bounded_edge_outdegree: "edge_outdegree_le D"
begin

theorem bounded_reduced_direct_insert_algorithm_correct_and_refined_graph_bound_log_params:
  fixes N p q :: nat
  defines p_def: "p \<equiv> sssp_log_one_third_param N"
    and q_def: "q \<equiv> sssp_log_two_thirds_param N"
  assumes run:
      "direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p
        (bmssp_level_cap p q p) p
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "U = V \<and> sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * p) (\<lambda>_. q) (\<lambda>_. p)
      (\<lambda>_. p) (\<lambda>_. q) (\<lambda>_. edge_count) vertex_count"
proof -
  have run':
    "direct_insert_costed_bmssp D
      (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N))
      (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)
      (sssp_log_one_third_param N)
      (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N)
        (sssp_log_one_third_param N))
      (sssp_log_one_third_param N)
      finite_initial_label {s} Infinity d' Infinity U c"
    using run unfolding p_def q_def by simp
  show ?thesis
    unfolding p_def q_def
    by (rule positive_weight_direct_insert_algorithm_correct_and_refined_graph_bound_log_params_fixed_degree
      [OF all_vertices_reachable bounded_edge_outdegree run'])
qed

theorem bounded_reduced_exact_concrete_algorithm_correct_and_refined_graph_bound_log_params:
  fixes N p q :: nat
  defines p_def: "p \<equiv> sssp_log_one_third_param N"
    and q_def: "q \<equiv> sssp_log_two_thirds_param N"
  assumes run:
      "exact_concrete_bmssp D (bmssp_level_cap p q) q p p
        (bmssp_level_cap p q p) p
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "U = V \<and> sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * p) (\<lambda>_. q) (\<lambda>_. p)
      (\<lambda>_. p) (\<lambda>_. q) (\<lambda>_. edge_count) vertex_count"
proof -
  have direct_run:
    "direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p
      (bmssp_level_cap p q p) p
      finite_initial_label {s} Infinity d' Infinity U c"
    by (rule exact_concrete_bmssp_refines_direct_insert[OF run])
  have direct_run':
    "direct_insert_costed_bmssp D
      (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N))
      (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)
      (sssp_log_one_third_param N)
      (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N)
        (sssp_log_one_third_param N))
      (sssp_log_one_third_param N)
      finite_initial_label {s} Infinity d' Infinity U c"
    using direct_run unfolding p_def q_def by simp
  show ?thesis
    unfolding p_def q_def
    by (rule bounded_reduced_direct_insert_algorithm_correct_and_refined_graph_bound_log_params
      [OF direct_run'])
qed

theorem bounded_reduced_bmssp_runtime_bigo_target:
  assumes edge_count_pos: "0 < edge_count"
  shows "(\<lambda>n. real (T_bmssp D n)) \<in>
    O(\<lambda>n. real edge_count * (ln (real n + 2)) powr (2 / 3))"
  by (rule T_bmssp_bigo_target_log_params_fixed_degree
    [OF all_vertices_reachable bounded_edge_outdegree edge_count_pos])

end

locale bmssp_runtime_headline_instance =
  bounded: bounded_reduced_positive_instance V E w s D
  for V :: "'v set"
    and E :: "('v \<times> 'v) set"
    and w :: "'v \<Rightarrow> 'v \<Rightarrow> real"
    and s :: "'v"
    and D :: nat
begin

text \<open>
  This locale is the public asymptotic headline for the top-level theory.  It
  hides the reduced positive instance, the fixed outdegree bound, and the
  least-cost definition behind two simple functions, \<open>T_bmssp\<close> for the
  checked BMSSP running time and \<open>m\<close> for the edge-count scale.  The
  theorem below is deliberately assumption-free inside the locale: all graph
  hypotheses are already part of the locale interpretation.
\<close>

definition T_bmssp :: "nat \<Rightarrow> nat" where
  "T_bmssp N = bounded.T_bmssp D N"

definition m :: "nat \<Rightarrow> nat" where
  "m N = Suc bounded.edge_count"

theorem bmssp_runtime_bigo_target:
  shows "(\<lambda>n. real (T_bmssp n)) \<in>
    O(\<lambda>n. real (m n) * (ln (real n + 2)) powr (2 / 3))"
  using bounded.T_bmssp_bigo_size_target_log_params_fixed_degree
    [OF bounded.all_vertices_reachable bounded.bounded_edge_outdegree]
  unfolding T_bmssp_def m_def sssp_time_target_def sssp_log_factor_def by simp

text \<open>
  The theorem @{thm bmssp_runtime_bigo_target} is the headline statement used
  by the rest of the AFP entry.  Its right-hand side is the deterministic
  BMSSP target: graph-size work times \<open>log^{2/3}\<close>.  The proof is short here
  because the recurrence has already been solved in the preceding fixed-degree
  theorem and the locale definitions only rename the time and size functions.
\<close>

end

sublocale bounded_reduced_positive_instance <
  runtime_headline: bmssp_runtime_headline_instance V E w s D
  by unfold_locales

context bounded_reduced_positive_instance
begin

theorem bounded_reduced_runtime_headline_bmssp_runtime_bigo_target:
  shows "(\<lambda>n. real (runtime_headline.T_bmssp n)) \<in>
    O(\<lambda>n. real (runtime_headline.m n) * (ln (real n + 2)) powr (2 / 3))"
  by (rule runtime_headline.bmssp_runtime_bigo_target)

end

locale reduction_correctness_contract =
  original: finite_weighted_digraph V E w s +
  reduced: bounded_reduced_positive_instance V' E' w' s' D
  for V :: "'v set"
    and E :: "('v \<times> 'v) set"
    and w :: "'v \<Rightarrow> 'v \<Rightarrow> real"
    and s :: "'v"
    and V' :: "'r set"
    and E' :: "('r \<times> 'r) set"
    and w' :: "'r \<Rightarrow> 'r \<Rightarrow> real"
    and s' :: "'r"
    and D :: nat +
  fixes decode_label :: "('r \<Rightarrow> real) \<Rightarrow> 'v \<Rightarrow> real"
  assumes transfer_sssp_correct:
    "reduced.sssp_correct d' \<Longrightarrow> original.sssp_correct (decode_label d')"
begin

theorem reduced_direct_insert_run_transfers_correctness_and_refined_bound:
  fixes N p q :: nat
  defines p_def: "p \<equiv> sssp_log_one_third_param N"
    and q_def: "q \<equiv> sssp_log_two_thirds_param N"
  assumes run:
      "reduced.direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p
        (bmssp_level_cap p q p) p
        reduced.finite_initial_label {s'} Infinity d' Infinity U c"
  shows "original.sssp_correct (decode_label d') \<and>
    c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * p) (\<lambda>_. q) (\<lambda>_. p)
      (\<lambda>_. p) (\<lambda>_. q) (\<lambda>_. reduced.edge_count)
      reduced.vertex_count"
proof -
  have run':
    "reduced.direct_insert_costed_bmssp D
      (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N))
      (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)
      (sssp_log_one_third_param N)
      (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N)
        (sssp_log_one_third_param N))
      (sssp_log_one_third_param N)
      reduced.finite_initial_label {s'} Infinity d' Infinity U c"
    using run unfolding p_def q_def by simp
  have reduced_result:
    "U = V' \<and> reduced.sssp_correct d' \<and>
      c \<le> bmssp_refined_graph_time_bound
        (\<lambda>_. Suc D * sssp_log_one_third_param N)
        (\<lambda>_. sssp_log_two_thirds_param N)
        (\<lambda>_. sssp_log_one_third_param N)
        (\<lambda>_. sssp_log_one_third_param N)
        (\<lambda>_. sssp_log_two_thirds_param N)
        (\<lambda>_. reduced.edge_count) reduced.vertex_count"
    by (rule reduced.bounded_reduced_direct_insert_algorithm_correct_and_refined_graph_bound_log_params
      [OF run'])
  then show ?thesis
    unfolding p_def q_def
    using transfer_sssp_correct by blast
qed

theorem reduced_exact_concrete_run_transfers_correctness_and_refined_bound:
  fixes N p q :: nat
  defines p_def: "p \<equiv> sssp_log_one_third_param N"
    and q_def: "q \<equiv> sssp_log_two_thirds_param N"
  assumes run:
      "reduced.exact_concrete_bmssp D (bmssp_level_cap p q) q p p
        (bmssp_level_cap p q p) p
        reduced.finite_initial_label {s'} Infinity d' Infinity U c"
  shows "original.sssp_correct (decode_label d') \<and>
    c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * p) (\<lambda>_. q) (\<lambda>_. p)
      (\<lambda>_. p) (\<lambda>_. q) (\<lambda>_. reduced.edge_count)
      reduced.vertex_count"
proof -
  have direct_run:
    "reduced.direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p
      (bmssp_level_cap p q p) p
      reduced.finite_initial_label {s'} Infinity d' Infinity U c"
    by (rule reduced.exact_concrete_bmssp_refines_direct_insert[OF run])
  have direct_run':
    "reduced.direct_insert_costed_bmssp D
      (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N))
      (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)
      (sssp_log_one_third_param N)
      (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N)
        (sssp_log_one_third_param N))
      (sssp_log_one_third_param N)
      reduced.finite_initial_label {s'} Infinity d' Infinity U c"
    using direct_run unfolding p_def q_def by simp
  show ?thesis
    unfolding p_def q_def
    by (rule reduced_direct_insert_run_transfers_correctness_and_refined_bound
      [OF direct_run'])
qed

theorem reduced_exact_concrete_top_level_time_transfers_correctness_and_refined_bound:
  assumes run_exists: "reduced.exact_concrete_top_level_cost D N c"
  shows "\<exists>d' U. reduced.exact_concrete_top_level_run D N d' U
      (reduced.exact_concrete_top_level_time D N) \<and>
    original.sssp_correct (decode_label d') \<and>
    reduced.exact_concrete_top_level_time D N \<le>
      bmssp_refined_graph_time_bound
        (\<lambda>_. Suc D * sssp_log_one_third_param N)
        (\<lambda>_. sssp_log_two_thirds_param N)
        (\<lambda>_. sssp_log_one_third_param N)
        (\<lambda>_. sssp_log_one_third_param N)
        (\<lambda>_. sssp_log_two_thirds_param N)
        (\<lambda>_. reduced.edge_count) reduced.vertex_count"
proof -
  have cost:
    "reduced.exact_concrete_top_level_cost D N
      (reduced.exact_concrete_top_level_time D N)"
    by (rule reduced.exact_concrete_top_level_time_witness[OF run_exists])
  obtain d' U where run:
    "reduced.exact_concrete_top_level_run D N d' U
      (reduced.exact_concrete_top_level_time D N)"
    using cost unfolding reduced.exact_concrete_top_level_cost_def by blast
  have reduced_result:
    "U = V' \<and> reduced.sssp_correct d' \<and>
      reduced.exact_concrete_top_level_time D N \<le>
        bmssp_refined_graph_time_bound
          (\<lambda>_. Suc D * sssp_log_one_third_param N)
          (\<lambda>_. sssp_log_two_thirds_param N)
          (\<lambda>_. sssp_log_one_third_param N)
          (\<lambda>_. sssp_log_one_third_param N)
          (\<lambda>_. sssp_log_two_thirds_param N)
          (\<lambda>_. reduced.edge_count) reduced.vertex_count"
    by (rule reduced.exact_concrete_top_level_run_correct_and_refined_bound_log_params_fixed_degree
      [OF reduced.all_vertices_reachable reduced.bounded_edge_outdegree run])
  have original_correct: "original.sssp_correct (decode_label d')"
    by (rule transfer_sssp_correct) (use reduced_result in blast)
  show ?thesis
    using run reduced_result original_correct by blast
qed

theorem reduced_runtime_headline_bmssp_runtime_bigo_target:
  shows "(\<lambda>n. real (reduced.runtime_headline.T_bmssp n)) \<in>
    O(\<lambda>n. real (reduced.runtime_headline.m n) *
      (ln (real n + 2)) powr (2 / 3))"
  by (rule reduced.runtime_headline.bmssp_runtime_bigo_target)

end

section \<open>Reduction Contract for the Asymptotic Bound\<close>

text \<open>
  The theorem below is the checked asymptotic contract needed from the graph
  reduction layer.  Once a family of reduced instances supplies a fixed
  outdegree bound \<open>D\<close>, a linear edge-count domination for the vertex term, and
  the per-instance cost bound produced by the locale theorem above, the final
  SSSP target bound follows.
\<close>

theorem reduction_contract_bigo_sssp_time_target:
  fixes D :: nat
  assumes Cn_pos: "0 < Cn"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    and reduced_instance_cost_bound:
      "eventually
        (\<lambda>n. T n \<le>
          bmssp_refined_graph_time_bound
            (\<lambda>n. Suc D * sssp_log_one_third_param n)
            sssp_log_two_thirds_param sssp_log_one_third_param
            sssp_log_one_third_param sssp_log_two_thirds_param m n) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
  by (rule bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree
      [OF Cn_pos vertex_count_dominated reduced_instance_cost_bound])

theorem reduction_contract_bigo_sssp_time_target_with_constant_slack:
  fixes D :: nat
  assumes Cn_pos: "0 < Cn"
    and Ccost_pos: "0 < Ccost"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    and reduced_instance_cost_bound:
      "eventually
        (\<lambda>n. real (T n) \<le> Ccost *
          real (bmssp_refined_graph_time_bound
            (\<lambda>n. Suc D * sssp_log_one_third_param n)
            sssp_log_two_thirds_param sssp_log_one_third_param
            sssp_log_one_third_param sssp_log_two_thirds_param m n)) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
  by (rule bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree_real_slack
      [OF Cn_pos Ccost_pos vertex_count_dominated reduced_instance_cost_bound])

theorem reduction_contract_bigo_sssp_time_target_square_size_params:
  fixes D :: nat
  assumes Cn_pos: "0 < Cn"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    and reduced_instance_cost_bound:
      "eventually
        (\<lambda>n. T n \<le>
          bmssp_refined_graph_time_bound
            (\<lambda>n. Suc D * sssp_log_one_third_param (n * n))
            (\<lambda>n. sssp_log_two_thirds_param (n * n))
            (\<lambda>n. sssp_log_one_third_param (n * n))
            (\<lambda>n. sssp_log_one_third_param (n * n))
            (\<lambda>n. sssp_log_two_thirds_param (n * n)) m n) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
  by (rule bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree_square_arg
      [OF Cn_pos vertex_count_dominated reduced_instance_cost_bound])

theorem reduction_contract_bigo_sssp_time_target_square_size_params_with_constant_slack:
  fixes D :: nat
  assumes Cn_pos: "0 < Cn"
    and Ccost_pos: "0 < Ccost"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    and reduced_instance_cost_bound:
      "eventually
        (\<lambda>n. real (T n) \<le> Ccost *
          real (bmssp_refined_graph_time_bound
            (\<lambda>n. Suc D * sssp_log_one_third_param (n * n))
            (\<lambda>n. sssp_log_two_thirds_param (n * n))
            (\<lambda>n. sssp_log_one_third_param (n * n))
            (\<lambda>n. sssp_log_one_third_param (n * n))
            (\<lambda>n. sssp_log_two_thirds_param (n * n)) m n)) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
  by (rule bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree_square_arg_real_slack
      [OF Cn_pos Ccost_pos vertex_count_dominated reduced_instance_cost_bound])

end
