theory BMSSP_Bucketed_Runtime
  imports BMSSP_Top_Level_Bounds BMSSP_Bucketed_Cost_Bridge
begin

section \<open>Non-Conditional Bucketed Running-Time Bound\<close>

text \<open>
  The capstone of \<^file>\<open>BMSSP_Bucketed_Cost_Bridge.thy\<close> is conditional: it
  assumes a cost function already bounded by the refined graph-time expression
  with the bucketed costs in the Insert and BatchPrepend slots.  This theory
  discharges that assumption against an actual costed BMSSP run, producing a
  hypothesis-free \<open>O(m * log\<^sup>2\<^sup>/\<^sup>3 n)\<close> bound that carries the bucketed
  operation costs.

  The key structural fact making this possible is that the local-budget
  amortised theorem
  \<open>direct_insert_costed_bmssp_amortized_bound_from_local_budgets_with_invariants\<close>
  is parametric in the level geometry \<open>M_of\<close>/\<open>cap\<close> and in the per-operation
  costs \<open>t\<close>/\<open>h\<close> \emph{independently}.  We therefore keep the level geometry at
  the paper's schedule exponents \<open>p = log\<^sup>1\<^sup>/\<^sup>3\<close>, \<open>q = log\<^sup>2\<^sup>/\<^sup>3\<close> (so the
  recursion tree, pivot growth, and pull blocks are unchanged), while charging
  Insert at the bucketed budget \<open>9 + q\<close> and BatchPrepend at \<open>2 + p\<close>.  Because
  the FindPivots pivot set \<open>find_pivots_pivots_capped\<close> depends only on the
  geometry, not on the costs, the same emptiness argument that makes the existing
  headline total applies here verbatim, so the bound is total in \<open>N\<close>.

  Throughout, \<open>D\<close> is a fixed outdegree bound and the running graph is the locale
  graph of @{locale strict_tie_breaking_digraph}.
\<close>

subsection \<open>A One-Third-Scale Envelope for the BatchPrepend Cost\<close>

text \<open>
  The BatchPrepend cost \<open>2 + p\<close> here grows like \<open>p = log\<^sup>1\<^sup>/\<^sup>3\<close> (the schedule
  parameter), not a constant.  This envelope, the one-third analogue of the
  two-thirds envelope in the cost bridge, shows it stays within a constant
  multiple of \<open>log\<^sup>1\<^sup>/\<^sup>3\<close> --- exactly the \<open>H_bound\<close> the recurrence solver needs.
\<close>

lemma const_plus_one_third_param_le_one_third_factor:
  "eventually
    (\<lambda>n. real (c + sssp_log_one_third_param n) \<le>
      real (c + 2) * sssp_log_factor_one_third n) at_top"
  using eventually_one_le_sssp_log_factor_one_third
proof eventually_elim
  case (elim n)
  have one_le: "1 \<le> sssp_log_factor_one_third n"
    using elim .
  have param_le:
    "real (sssp_log_one_third_param n) \<le> sssp_log_factor_one_third n + 1"
  proof -
    have nonneg: "0 \<le> sssp_log_factor_one_third n"
      using one_le by linarith
    have "real (nat \<lceil>sssp_log_factor_one_third n\<rceil>) =
        of_int \<lceil>sssp_log_factor_one_third n\<rceil>"
      using of_nat_int_ceiling[OF nonneg] .
    moreover have "of_int \<lceil>sssp_log_factor_one_third n\<rceil> \<le>
        sssp_log_factor_one_third n + 1"
      using ceiling_correct[of "sssp_log_factor_one_third n"] by linarith
    ultimately show ?thesis
      unfolding sssp_log_one_third_param_def by simp
  qed
  have c_le: "real c \<le> real c * sssp_log_factor_one_third n"
  proof -
    have "real c * 1 \<le> real c * sssp_log_factor_one_third n"
      by (rule mult_left_mono[OF one_le]) simp
    then show ?thesis by simp
  qed
  have "real (c + sssp_log_one_third_param n) =
      real c + real (sssp_log_one_third_param n)"
    by simp
  also have "\<dots> \<le> real c + (sssp_log_factor_one_third n + 1)"
    using param_le by linarith
  also have "\<dots> \<le> real c * sssp_log_factor_one_third n +
      2 * sssp_log_factor_one_third n"
    using c_le one_le by linarith
  also have "\<dots> = real (c + 2) * sssp_log_factor_one_third n"
    by (simp add: algebra_simps)
  finally show ?case .
qed

text \<open>
  An affine version used for the vertex factor \<open>A = a * p + b\<close>: it is dominated
  by \<open>(2 a + b)\<close> times the one-third log factor, hence \<open>O(log\<^sup>1\<^sup>/\<^sup>3)\<close>.
\<close>

lemma affine_one_third_param_le_one_third_factor:
  "eventually
    (\<lambda>n. real (a * sssp_log_one_third_param n + b) \<le>
      real (2 * a + b) * sssp_log_factor_one_third n) at_top"
  using eventually_one_le_sssp_log_factor_one_third
proof eventually_elim
  case (elim n)
  have one_le: "1 \<le> sssp_log_factor_one_third n"
    using elim .
  have nonneg: "0 \<le> sssp_log_factor_one_third n"
    using one_le by linarith
  let ?L = "sssp_log_factor_one_third n"
  have param_le:
    "real (sssp_log_one_third_param n) \<le> ?L + 1"
  proof -
    have "real (nat \<lceil>?L\<rceil>) = of_int \<lceil>?L\<rceil>"
      using of_nat_int_ceiling[OF nonneg] .
    moreover have "of_int \<lceil>?L\<rceil> \<le> ?L + 1"
      using ceiling_correct[of ?L] by linarith
    ultimately show ?thesis
      unfolding sssp_log_one_third_param_def by simp
  qed
  have "real (a * sssp_log_one_third_param n + b) =
      real a * real (sssp_log_one_third_param n) + real b"
    by simp
  also have "\<dots> \<le> real a * (?L + 1) + real b"
    using param_le by (intro add_mono mult_left_mono) simp_all
  also have "\<dots> = real a * ?L + (real a + real b)"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> real a * ?L + (real a + real b) * ?L"
  proof -
    have "(real a + real b) * 1 \<le> (real a + real b) * ?L"
      by (rule mult_left_mono[OF one_le]) simp
    then show ?thesis by simp
  qed
  also have "\<dots> = real (2 * a + b) * ?L"
    by (simp add: algebra_simps)
  finally show ?case .
qed

context strict_tie_breaking_digraph
begin

subsection \<open>A Decoupled Amortised Bound: Geometry Exponent vs.\ Operation Cost\<close>

text \<open>
  This is the existing level-cap amortised theorem with one generalisation: the
  level geometry uses an exponent \<open>tg\<close> that is decoupled from the per-Insert
  cost \<open>t\<close>.  In the original theorem the two coincide (\<open>M_of = bmssp_level_cap k
  t\<close>); here \<open>M_of = bmssp_level_cap k tg\<close>, while \<open>t\<close> remains the cost charged at
  each direct insert.  The proof is the original one: the local-budget amortised
  lemma is parametric in \<open>M_of\<close>, \<open>cap\<close>, \<open>t\<close>, \<open>h\<close>, \<open>A\<close>, \<open>R\<close>, \<open>k\<close>, so the only
  coupling needed is @{prop "M_of i \<le> cap"} for \<open>i \<le> l\<close>, which still holds by
  monotonicity of @{const bmssp_level_cap} in the level.
\<close>

theorem finite_initial_label_decoupled_amortized:
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
      "direct_insert_costed_bmssp \<Delta> (bmssp_level_cap k tg) t h k
        (bmssp_level_cap k tg l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. h)
      (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
proof
  show "sssp_correct d'"
    by (rule finite_initial_label_direct_insert_costed_top_level_correct
      [OF all_reachable run])
next
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  have below: "\<And>x. x \<in> {s} \<Longrightarrow>
      below_bound (finite_initial_label x) Infinity"
    by simp
  have top_cap: "k * card {s} \<le> bmssp_level_cap k tg l"
  proof -
    have one_le: "1 \<le> bmssp_level_width tg l"
      unfolding bmssp_level_width_def by simp
    have "k * 1 \<le> k * bmssp_level_width tg l"
      by (rule mult_left_mono[OF one_le]) simp
    then show ?thesis
      unfolding bmssp_level_cap_def by simp
  qed
  have top_anti: "tree_antichain {s}"
    by simp
  have amortized:
    "c \<le> bmssp_amortized_cost_bound (2 * A) R h t l (2 * l + 1)
      Infinity U"
  proof (rule direct_insert_costed_bmssp_amortized_bound_from_local_budgets_with_invariants
      [where A = "2 * A" and R = R,
        OF _ R_pos source_factor k_pos _ _ run sound pre S_reaches below
          top_cap top_anti])
    show "\<Delta> \<le> 2 * A"
      using degree_factor by simp
  next
    fix i
    assume "i \<le> l"
    then show "bmssp_level_cap k tg i \<le> bmssp_level_cap k tg l"
      by (rule bmssp_level_cap_mono)
  next
    fix l' d S B D c_insert d' a betas bs B' Us U_loop c_loop
      child_costs U
    assume D_def:
        "D = label_partition_view
          (find_pivots_label_capped k (bmssp_level_cap k tg l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k tg l) d S B)"
      and insert:
        "partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k (bmssp_level_cap k tg l) d S B)"
      and loop:
        "direct_insert_costed_partition_loop_state \<Delta> (bmssp_level_cap k tg) t h k
          (bmssp_level_cap k tg l) l'
          (find_pivots_label_capped k (bmssp_level_cap k tg l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k tg l) d S B) B d' D
          a betas bs B' Us U_loop c_loop child_costs"
      and complete:
        "complete_on d'
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k tg l) d S B v =
              dist s v}"
      and U_def:
        "U = U_loop \<union>
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k tg l) d S B v =
              dist s v}"
      and sound_s: "sound_label d"
      and pre_s: "bmssp_pre_full d S B"
      and reaches_s: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
      and below_s: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
      and S_k_cap: "k * card S \<le> bmssp_level_cap k tg l"
      and anti: "tree_antichain S"
    have seen_success:
      "B' = B \<Longrightarrow>
        card (find_pivots_seen_capped k (bmssp_level_cap k tg l) d S B)
        \<le> card U"
      by (rule direct_insert_costed_step_seen_success
        [OF loop U_def sound_s pre_s reaches_s below_s])
    show "fp_iter_capped_scan_cost k (bmssp_level_cap k tg l) d S S B +
        c_insert \<le> 2 * A * card U"
      by (rule direct_insert_costed_capped_step_scan_insert_budget_from_scaled_seen_or_threshold
        [OF degree degree_factor insert_factor insert_scaled_factor
          seen_scaled_factor insert loop U_def sound_s pre_s reaches_s
          S_k_cap anti k_pos seen_success])
  qed
  have post_full:
    "bmssp_post_full finite_initial_label {s} Infinity d' Infinity U"
    by (rule direct_insert_costed_bmssp_correct[OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  have U_V: "U = V"
    using post bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  have graph_bound:
    "bmssp_amortized_cost_bound (2 * A) R h t l (2 * l + 1) Infinity U
      \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. h)
        (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
  proof -
    have U_card: "card U = vertex_count"
      unfolding U_V vertex_count_def by simp
    have out_le: "card (outgoing_edges U) \<le> edge_count"
      by (rule edge_count_outgoing_bound)
    have range_le: "card (outgoing_edges_range U 0 Infinity) \<le> edge_count"
      by (rule card_outgoing_edges_range_le_edge_count)
    have out_term:
      "(R + l * h) * card (outgoing_edges U) \<le>
       (R + l * h) * edge_count"
      using out_le by simp
    have range_term:
      "t * card (outgoing_edges_range U 0 Infinity) \<le> t * edge_count"
      using range_le by simp
    show ?thesis
      unfolding bmssp_amortized_cost_bound_def bmssp_refined_graph_time_bound_def
      using U_card out_term range_term by (simp add: algebra_simps; linarith)
  qed
  show "c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. h)
      (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
    using amortized graph_bound by linarith
qed

subsection \<open>A Costed Run With Decoupled Geometry and Bucketed Costs\<close>

text \<open>
  \<open>bmssp_bucketed_run D N\<close> is a top-level costed run whose level geometry uses
  the schedule exponents \<open>p, q\<close> but whose Insert cost is the bucketed budget
  \<open>9 + q\<close> and whose BatchPrepend cost is \<open>2 + p\<close>.
\<close>

definition bmssp_bucketed_run ::
  "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> bool" where
  "bmssp_bucketed_run D N d' U c \<longleftrightarrow>
     (let p = sssp_log_one_third_param N;
          q = sssp_log_two_thirds_param N
      in exact_concrete_bmssp D (bmssp_level_cap p q) (9 + q) (2 + p) p
        (bmssp_level_cap p q p) p
        finite_initial_label {s} Infinity d' Infinity U c)"

definition bmssp_bucketed_cost :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "bmssp_bucketed_cost D N c \<longleftrightarrow> (\<exists>d' U. bmssp_bucketed_run D N d' U c)"

definition bmssp_bucketed_time :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bmssp_bucketed_time D N = (LEAST c. bmssp_bucketed_cost D N c)"

subsection \<open>Totality of the Bucketed Cost\<close>

text \<open>
  The same FindPivots-emptiness argument as the existing headline, with the
  bucketed costs in the cost slots.  Since
  \<open>exact_concrete_bmssp_Suc_exists_if_pivots_empty_same_bound\<close> is
  parametric in the costs, the substitution is immediate.
\<close>

lemma bmssp_bucketed_cost_exists_if_top_pivots_empty:
  assumes pivots_empty:
    "find_pivots_pivots_capped (sssp_log_one_third_param N)
      (bmssp_level_cap (sssp_log_one_third_param N)
        (sssp_log_two_thirds_param N) (sssp_log_one_third_param N))
      finite_initial_label {s} Infinity = {}"
  shows "\<exists>c. bmssp_bucketed_cost D N c"
proof -
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  have p_eq: "?p = Suc (?p - 1)"
    using sssp_log_one_third_param_pos[of N] by simp
  have source_subset: "{s} \<subseteq> V"
    using source_in_V by simp
  have run:
    "\<exists>d' U c.
      exact_concrete_bmssp D (bmssp_level_cap ?p ?q) (9 + ?q) (2 + ?p) ?p
        (bmssp_level_cap ?p ?q ?p) (Suc (?p - 1))
        finite_initial_label {s} Infinity d' Infinity U c"
    by (rule exact_concrete_bmssp_Suc_exists_if_pivots_empty_same_bound
      [OF source_subset _ pivots_empty]) simp
  then obtain d' U c where
    "exact_concrete_bmssp D (bmssp_level_cap ?p ?q) (9 + ?q) (2 + ?p) ?p
      (bmssp_level_cap ?p ?q ?p) (Suc (?p - 1))
      finite_initial_label {s} Infinity d' Infinity U c"
    by blast
  then have root_run:
    "exact_concrete_bmssp D (bmssp_level_cap ?p ?q) (9 + ?q) (2 + ?p) ?p
      (bmssp_level_cap ?p ?q ?p) ?p
      finite_initial_label {s} Infinity d' Infinity U c"
    using p_eq by simp
  have "bmssp_bucketed_run D N d' U c"
    unfolding bmssp_bucketed_run_def
    using root_run by (simp add: Let_def)
  then have "bmssp_bucketed_cost D N c"
    unfolding bmssp_bucketed_cost_def by blast
  then show ?thesis
    by blast
qed

lemma eventually_bmssp_bucketed_cost:
  "eventually (\<lambda>N. \<exists>c. bmssp_bucketed_cost D N c) at_top"
  using eventually_top_level_pivots_empty[of finite_initial_label Infinity]
proof eventually_elim
  case (elim N)
  show ?case
    by (rule bmssp_bucketed_cost_exists_if_top_pivots_empty[OF elim])
qed

lemma bmssp_bucketed_time_witness:
  assumes "bmssp_bucketed_cost D N c"
  shows "bmssp_bucketed_cost D N (bmssp_bucketed_time D N)"
  unfolding bmssp_bucketed_time_def
  by (rule LeastI_ex) (use assms in blast)

subsection \<open>Cost Bound for a Bucketed Run\<close>

text \<open>
  A bucketed run refines a direct-insert run with the same (decoupled) geometry
  and costs, to which the decoupled amortised theorem applies.  Choosing
  \<open>A = Suc D * p + 9\<close> makes the local-budget side conditions hold for \emph{all}
  \<open>N\<close> (the binding constraint \<open>9 + q \<le> A * p\<close> follows from \<open>q \<le> p\<^sup>2\<close> and
  \<open>9 \<le> 9 * p\<close>), and \<open>A\<close> still grows only like \<open>log\<^sup>1\<^sup>/\<^sup>3\<close>.
\<close>

lemma bmssp_bucketed_run_refined_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and run: "bmssp_bucketed_run D N d' U c"
  shows "c \<le> bmssp_refined_graph_time_bound
    (\<lambda>_. Suc D * sssp_log_one_third_param N + 9)
    (\<lambda>_. sssp_log_two_thirds_param N)
    (\<lambda>_. 2 + sssp_log_one_third_param N)
    (\<lambda>_. sssp_log_one_third_param N)
    (\<lambda>_. 9 + sssp_log_two_thirds_param N)
    (\<lambda>_. edge_count) vertex_count"
proof -
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  let ?A = "Suc D * ?p + 9"
  have direct:
    "direct_insert_costed_bmssp D (bmssp_level_cap ?p ?q) (9 + ?q) (2 + ?p) ?p
      (bmssp_level_cap ?p ?q ?p) ?p
      finite_initial_label {s} Infinity d' Infinity U c"
    by (rule exact_concrete_bmssp_refines_direct_insert
      [OF run[unfolded bmssp_bucketed_run_def Let_def]])
  have p_pos: "0 < ?p" by simp
  have p_ge1: "1 \<le> ?p" using p_pos by linarith
  have q_le_sq: "?q \<le> ?p * ?p"
    by (rule sssp_log_two_thirds_param_le_one_third_square)
  have degree_factor: "D \<le> ?A"
  proof -
    have "D \<le> Suc D * ?p"
      using p_pos by (cases ?p) simp_all
    then show ?thesis by simp
  qed
  have insert_factor: "9 + ?q \<le> ?A * ?p"
  proof -
    have "9 + ?q \<le> 9 * ?p + ?p * ?p"
      using q_le_sq p_ge1 by (simp add: algebra_simps; linarith)
    also have "\<dots> \<le> 9 * ?p + Suc D * ?p * ?p"
      by simp
    also have "\<dots> = ?A * ?p"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have insert_scaled_factor: "9 + ?q \<le> ?A * ?p"
    by (rule insert_factor)
  have seen_scaled_factor: "?p * D + ?A \<le> 2 * ?A"
  proof -
    have "?p * D \<le> Suc D * ?p"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> ?A"
      by simp
    finally have "?p * D \<le> ?A" .
    then show ?thesis by simp
  qed
  have source_factor: "Suc (2 + ?p) \<le> 2 * ?A"
  proof -
    have "2 * ?A = 2 * Suc D * ?p + 18"
      by (simp add: algebra_simps)
    moreover have "2 * ?p \<le> 2 * Suc D * ?p"
      by (simp add: algebra_simps)
    ultimately have "2 * ?p + 18 \<le> 2 * ?A"
      by linarith
    moreover have "Suc (2 + ?p) \<le> 2 * ?p + 18"
      by simp
    ultimately show ?thesis by linarith
  qed
  have R_pos: "0 < ?q"
    by (rule sssp_log_two_thirds_param_pos)
  have "sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. ?A) (\<lambda>_. ?q) (\<lambda>_. 2 + ?p)
      (\<lambda>_. ?p) (\<lambda>_. 9 + ?q) (\<lambda>_. edge_count) vertex_count"
    by (rule finite_initial_label_decoupled_amortized
      [OF all_reachable degree degree_factor R_pos insert_factor
        insert_scaled_factor seen_scaled_factor source_factor p_pos direct])
  then show ?thesis
    by blast
qed

subsection \<open>The Non-Conditional Bucketed Running-Time Bound\<close>

text \<open>
  Assembling the pieces.  Totality of the bucketed cost (via the
  FindPivots-emptiness argument) discharges the existence premise; the cost
  bound discharges the recurrence premise; and the schedule envelopes for the
  five cost parameters discharge the component bounds.  Nothing is left
  conditional: the bucketed BMSSP running time is \<open>O(m * log\<^sup>2\<^sup>/\<^sup>3 n)\<close>.
\<close>

theorem bmssp_bucketed_time_bigo_sssp_time_target:
  fixes m :: "nat \<Rightarrow> nat"
    and Cn Cm :: real
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and Cn_pos: "0 < Cn"
    and Cm_pos: "0 < Cm"
    and vc_dom: "eventually (\<lambda>n. real vertex_count \<le> Cn * real (m n)) at_top"
    and ec_dom: "eventually (\<lambda>n. real edge_count \<le> Cm * real (m n)) at_top"
  shows "(\<lambda>n. real (bmssp_bucketed_time D n)) \<in> O(\<lambda>n. sssp_time_target m n)"
proof (rule bmssp_refined_cost_bound_bigo_sssp_time_target_from_component_bounds_slack)
  show "0 < Cn" by (rule Cn_pos)
  show "0 < Cm" by (rule Cm_pos)
  show "eventually (\<lambda>n. real ((\<lambda>_. vertex_count) n) \<le> Cn * real (m n)) at_top"
    using vc_dom by simp
  show "eventually (\<lambda>n. real ((\<lambda>_. edge_count) n) \<le> Cm * real (m n)) at_top"
    using ec_dom by simp
  show "eventually
      (\<lambda>n. real (Suc D * sssp_log_one_third_param n + 9) \<le>
        real (2 * Suc D + 9) * sssp_log_factor_one_third n) at_top"
    using affine_one_third_param_le_one_third_factor[of "Suc D" 9] by simp
  show "eventually
      (\<lambda>n. real (sssp_log_one_third_param n) \<le> 2 * sssp_log_factor_one_third n)
      at_top"
    using const_plus_one_third_param_le_one_third_factor[of 0] by simp
  show "eventually
      (\<lambda>n. real (sssp_log_two_thirds_param n) \<le> 2 * sssp_log_factor n) at_top"
    using const_plus_two_thirds_param_le_two_thirds_factor[of 0] by simp
  show "eventually
      (\<lambda>n. real (9 + sssp_log_two_thirds_param n) \<le> 11 * sssp_log_factor n)
      at_top"
    using const_plus_two_thirds_param_le_two_thirds_factor[of 9] by simp
  show "eventually
      (\<lambda>n. real (2 + sssp_log_one_third_param n) \<le>
        4 * sssp_log_factor_one_third n) at_top"
    using const_plus_one_third_param_le_one_third_factor[of 2] by simp
  have cost_ev: "eventually
      (\<lambda>n. bmssp_bucketed_time D n \<le>
        bmssp_refined_graph_time_bound
          (\<lambda>_. Suc D * sssp_log_one_third_param n + 9)
          (\<lambda>_. sssp_log_two_thirds_param n)
          (\<lambda>_. 2 + sssp_log_one_third_param n)
          (\<lambda>_. sssp_log_one_third_param n)
          (\<lambda>_. 9 + sssp_log_two_thirds_param n)
          (\<lambda>_. edge_count) vertex_count) at_top"
  proof (rule eventually_mono[OF eventually_bmssp_bucketed_cost])
    fix n :: nat
    assume "\<exists>c. bmssp_bucketed_cost D n c"
    then obtain c where c: "bmssp_bucketed_cost D n c"
      by blast
    have cost: "bmssp_bucketed_cost D n (bmssp_bucketed_time D n)"
      by (rule bmssp_bucketed_time_witness[OF c])
    then obtain d' U where run:
      "bmssp_bucketed_run D n d' U (bmssp_bucketed_time D n)"
      unfolding bmssp_bucketed_cost_def by blast
    show "bmssp_bucketed_time D n \<le>
        bmssp_refined_graph_time_bound
          (\<lambda>_. Suc D * sssp_log_one_third_param n + 9)
          (\<lambda>_. sssp_log_two_thirds_param n)
          (\<lambda>_. 2 + sssp_log_one_third_param n)
          (\<lambda>_. sssp_log_one_third_param n)
          (\<lambda>_. 9 + sssp_log_two_thirds_param n)
          (\<lambda>_. edge_count) vertex_count"
      by (rule bmssp_bucketed_run_refined_bound[OF all_reachable degree run])
  qed
  show "eventually
      (\<lambda>n. bmssp_bucketed_time D n \<le>
        bmssp_refined_graph_time_bound
          (\<lambda>_. Suc D * sssp_log_one_third_param n + 9)
          (\<lambda>_. sssp_log_two_thirds_param n)
          (\<lambda>_. 2 + sssp_log_one_third_param n)
          (\<lambda>_. sssp_log_one_third_param n)
          (\<lambda>_. 9 + sssp_log_two_thirds_param n)
          (\<lambda>_. (\<lambda>_. edge_count) n) ((\<lambda>_. vertex_count) n)) at_top"
    using cost_ev by simp
qed auto

text \<open>
  The sparse-graph specialisation, fully closed: for the bounded-outdegree
  locale graph with at least one edge, the bucketed BMSSP running time is
  \<open>O(m * (ln n) powr (2/3))\<close>, where the Insert and BatchPrepend costs charged
  inside the recurrence are the actual bucketed budgets, not free parameters.
\<close>

theorem bmssp_bucketed_runtime_bigo_target:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and edge_count_pos: "0 < edge_count"
  shows "(\<lambda>n. real (bmssp_bucketed_time D n)) \<in>
    O(\<lambda>n. real edge_count * (ln (real n + 2)) powr (2 / 3))"
proof -
  have vertex_le: "vertex_count \<le> 2 * edge_count"
    by (rule vertex_count_le_twice_edge_count_if_all_reachable
      [OF all_reachable edge_count_pos])
  have "(\<lambda>n. real (bmssp_bucketed_time D n)) \<in>
    O(\<lambda>n. sssp_time_target (\<lambda>_. edge_count) n)"
  proof (rule bmssp_bucketed_time_bigo_sssp_time_target [OF all_reachable degree])
    show "0 < (2::real)" by simp
    show "0 < (1::real)" by simp
    show "eventually (\<lambda>n. real vertex_count \<le> 2 * real edge_count) at_top"
      using vertex_le by simp
    show "eventually (\<lambda>n. real edge_count \<le> 1 * real edge_count) at_top"
      by simp
  qed
  then show ?thesis
    unfolding sssp_time_target_def sssp_log_factor_def by simp
qed

end

end
