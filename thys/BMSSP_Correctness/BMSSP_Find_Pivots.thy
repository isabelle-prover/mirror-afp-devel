theory BMSSP_Find_Pivots
  imports BMSSP_Find_Pivots_Core BMSSP_Algorithm_Correctness
begin

section \<open>Concrete FindPivots Rounds\<close>

text \<open>
  FindPivots is the first nontrivial subroutine in a BMSSP recursive step.
  Conceptually, it starts from a current source frontier, performs a bounded
  number of relaxation rounds, records the vertices reached by those rounds,
  and chooses a smaller set of pivots whose shortest-path trees are large
  enough to justify the next recursive partitioning phase.

  This theory gives the concrete round-by-round model used by the later
  correctness and cost proofs.  The round state consists of a label function,
  a frontier, and a seen set.  One round relaxes edges out of the frontier,
  selects the next frontier under the current upper bound, and extends the
  seen set.  The capped variant stops early once the seen set exceeds a
  cardinality cap.  That cap is the formal hook for the paper's parameter
  schedule: if the local search grows too quickly, the original source set is
  already large enough to serve as the next pivot set.

  The proof obligations in this file fall into three groups.  First, the
  frontier and seen sets stay inside the finite vertex set and have the
  expected cardinality bounds under an outdegree assumption.  Second,
  relaxation preserves the BMSSP source precondition and label soundness.
  Third, if the capped search does not overflow, every short tight path
  starting from a complete source is completed, and long tight trees expose a
  pivot.  These facts are assembled into the concrete FindPivots postcondition
  consumed by the abstract algorithm-correctness theory.
\<close>

context unique_shortest_digraph
begin

definition fp_next where
  "fp_next d F B =
    {v \<in> V. \<exists>u\<in>F. (u, v) \<in> E \<and> d u + w u v \<le> d v \<and>
      below_bound (d u + w u v) B}"

fun fp_iter where
  "fp_iter 0 d F W B = (d, F, W)"
| "fp_iter (Suc n) d F W B =
    (let d' = relax_frontier d F;
         F' = fp_next d F B;
         W' = W \<union> F'
     in fp_iter n d' F' W' B)"

fun fp_iter_capped where
  "fp_iter_capped 0 cap d F W B = (d, F, W)"
| "fp_iter_capped (Suc n) cap d F W B =
    (let d' = relax_frontier d F;
         F' = fp_next d F B;
         W' = W \<union> F'
     in if card W' > cap then (d', F', W')
        else fp_iter_capped n cap d' F' W' B)"

fun fp_iter_capped_scan_cost where
  "fp_iter_capped_scan_cost 0 cap d F W B = 0"
| "fp_iter_capped_scan_cost (Suc n) cap d F W B =
    (let d' = relax_frontier d F;
         F' = fp_next d F B;
         W' = W \<union> F';
         round = card (outgoing_edges F)
     in round + (if card W' > cap then 0
        else fp_iter_capped_scan_cost n cap d' F' W' B))"

definition fp_label where
  "fp_label st = fst st"

definition fp_frontier where
  "fp_frontier st = fst (snd st)"

definition fp_seen where
  "fp_seen st = snd (snd st)"

definition find_pivots_label where
  "find_pivots_label k d S B = fp_label (fp_iter k d S S B)"

definition find_pivots_seen where
  "find_pivots_seen k d S B = fp_seen (fp_iter k d S S B)"

definition find_pivots_seen_capped where
  "find_pivots_seen_capped k cap d S B = fp_seen (fp_iter_capped k cap d S S B)"

definition find_pivots_label_capped where
  "find_pivots_label_capped k cap d S B = fp_label (fp_iter_capped k cap d S S B)"

definition find_pivots_pivots_capped where
  "find_pivots_pivots_capped k cap d S B =
    (if card (find_pivots_seen_capped k cap d S B) > cap then S
     else {u \<in> S. k \<le> card (tree_of u \<inter> find_pivots_seen_capped k cap d S B)})"

definition find_pivots_pivots where
  "find_pivots_pivots k d S B =
    {u \<in> S. k \<le> card (tree_of u \<inter> find_pivots_seen k d S B)}"

definition short_tight_witness where
  "short_tight_witness k d S B x \<longleftrightarrow>
    (\<exists>p. p \<noteq> [] \<and> hd p \<in> S \<and> last p = x \<and>
      d (hd p) = dist s (hd p) \<and> successively tight_edge_step p \<and>
      (\<forall>y\<in>set p. below_bound (dist s y) B) \<and>
      length (path_edges p) \<le> k)"

definition find_pivots_short_vertices where
  "find_pivots_short_vertices k d S B =
    {x \<in> V. short_tight_witness k d S B x}"

definition out_neighbors where
  "out_neighbors F = {v \<in> V. \<exists>u\<in>F. (u, v) \<in> E}"

definition outdegree_le where
  "outdegree_le \<Delta> \<longleftrightarrow> (\<forall>u\<in>V. card (out_neighbors {u}) \<le> \<Delta>)"

definition edge_outdegree_le where
  "edge_outdegree_le \<Delta> \<longleftrightarrow> (\<forall>u\<in>V. card (outgoing_edges {u}) \<le> \<Delta>)"

text \<open>
  The definitions above mirror the paper's informal description.  The set
  @{const fp_next} is the next bounded frontier: it contains vertices reached
  by a currently tight relaxation whose value remains below the call bound.
  The iterator @{const fp_iter} performs exactly \<open>k\<close> such rounds, while
  @{const fp_iter_capped} returns early when the accumulated seen set exceeds
  the cap.  The projections @{const find_pivots_label_capped},
  @{const find_pivots_seen_capped}, and @{const find_pivots_pivots_capped}
  are the concrete objects used by later BMSSP steps.

  Two degree predicates are kept separate.  @{const outdegree_le} bounds the
  number of distinct out-neighbours and is convenient for bounding the size of
  the seen set.  @{const edge_outdegree_le} bounds outgoing edge records and is
  used for scan-cost accounting.  The distinction matters in multigraph-style
  encodings where several edges may point to the same neighbour.
\<close>

lemma finite_tree_of [simp]:
  "finite (tree_of u)"
  unfolding tree_of_def using finite_V by auto

lemma fp_next_reaches:
  assumes reaches: "\<And>u. u \<in> F \<Longrightarrow> reachable s u"
    and v: "v \<in> fp_next d F B"
  shows "reachable s v"
proof -
  obtain u where "u \<in> F" "(u, v) \<in> E"
    using v unfolding fp_next_def by blast
  then show ?thesis
    using reaches dist_triangle_edge by blast
qed

lemma fp_next_subset_V:
  "fp_next d F B \<subseteq> V"
  unfolding fp_next_def by blast

lemma fp_next_subset_out_neighbors:
  "fp_next d F B \<subseteq> out_neighbors F"
  unfolding fp_next_def out_neighbors_def by blast

lemma out_neighbors_subset_V:
  "out_neighbors F \<subseteq> V"
  unfolding out_neighbors_def by blast

lemma finite_out_neighbors [simp]:
  "finite (out_neighbors F)"
  using finite_subset[OF out_neighbors_subset_V finite_V] .

lemma out_neighbors_UN_singleton:
  "out_neighbors F = (\<Union>u\<in>F. out_neighbors {u})"
  unfolding out_neighbors_def by auto

lemma outgoing_edges_UN_singleton:
  "outgoing_edges F = (\<Union>u\<in>F. outgoing_edges {u})"
  unfolding outgoing_edges_def by auto

lemma card_out_neighbors_le:
  assumes F_subset: "F \<subseteq> V"
    and degree: "outdegree_le \<Delta>"
  shows "card (out_neighbors F) \<le> \<Delta> * card F"
proof -
  have finite_F: "finite F"
    using finite_subset[OF F_subset finite_V] .
  have card_union: "card (out_neighbors F) \<le> (\<Sum>u\<in>F. card (out_neighbors {u}))"
  proof -
    have "card (out_neighbors F) = card (\<Union>u\<in>F. out_neighbors {u})"
      using out_neighbors_UN_singleton[of F] by simp
    also have "\<dots> \<le> (\<Sum>u\<in>F. card (out_neighbors {u}))"
      using card_UN_le[OF finite_F, of "\<lambda>u. out_neighbors {u}"] .
    finally show ?thesis .
  qed
  have sum_bound: "(\<Sum>u\<in>F. card (out_neighbors {u})) \<le> (\<Sum>u\<in>F. \<Delta>)"
  proof (rule sum_mono)
    fix u
    assume "u \<in> F"
    then have "u \<in> V"
      using F_subset by blast
    then show "card (out_neighbors {u}) \<le> \<Delta>"
      using degree unfolding outdegree_le_def by blast
  qed
  also have "\<dots> = \<Delta> * card F"
    by (simp add: mult.commute)
  finally have "(\<Sum>u\<in>F. card (out_neighbors {u})) \<le> \<Delta> * card F" .
  then show ?thesis
    using card_union by linarith
qed

lemma card_fp_next_le:
  assumes F_subset: "F \<subseteq> V"
    and degree: "outdegree_le \<Delta>"
  shows "card (fp_next d F B) \<le> \<Delta> * card F"
proof -
  have "card (fp_next d F B) \<le> card (out_neighbors F)"
    by (rule card_mono) (simp_all add: fp_next_subset_out_neighbors)
  also have "\<dots> \<le> \<Delta> * card F"
    using card_out_neighbors_le[OF F_subset degree] .
  finally show ?thesis .
qed

lemma card_outgoing_edges_le:
  assumes F_subset: "F \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
  shows "card (outgoing_edges F) \<le> \<Delta> * card F"
proof -
  have finite_F: "finite F"
    using finite_subset[OF F_subset finite_V] .
  have card_union: "card (outgoing_edges F) \<le>
      (\<Sum>u\<in>F. card (outgoing_edges {u}))"
  proof -
    have "card (outgoing_edges F) = card (\<Union>u\<in>F. outgoing_edges {u})"
      using outgoing_edges_UN_singleton[of F] by simp
    also have "\<dots> \<le> (\<Sum>u\<in>F. card (outgoing_edges {u}))"
      using card_UN_le[OF finite_F, of "\<lambda>u. outgoing_edges {u}"] .
    finally show ?thesis .
  qed
  have sum_bound: "(\<Sum>u\<in>F. card (outgoing_edges {u})) \<le> (\<Sum>u\<in>F. \<Delta>)"
  proof (rule sum_mono)
    fix u
    assume "u \<in> F"
    then have "u \<in> V"
      using F_subset by blast
    then show "card (outgoing_edges {u}) \<le> \<Delta>"
      using degree unfolding edge_outdegree_le_def by blast
  qed
  also have "\<dots> = \<Delta> * card F"
    by (simp add: mult.commute)
  finally have "(\<Sum>u\<in>F. card (outgoing_edges {u})) \<le> \<Delta> * card F" .
  then show ?thesis
    using card_union by linarith
qed

lemma card_seen_after_fp_step_le:
  assumes W_subset: "W \<subseteq> V"
    and F_subset: "F \<subseteq> V"
    and degree: "outdegree_le \<Delta>"
  shows "card (W \<union> fp_next d F B) \<le> card W + \<Delta> * card F"
proof -
  have "card (W \<union> fp_next d F B) \<le> card W + card (fp_next d F B)"
    by (rule card_Un_le)
  also have "\<dots> \<le> card W + \<Delta> * card F"
    using card_fp_next_le[OF F_subset degree] by simp
  finally show ?thesis .
qed

lemma card_seen_after_fp_step_cap_le:
  assumes F_subset_W: "F \<subseteq> W"
    and W_subset: "W \<subseteq> V"
    and degree: "outdegree_le \<Delta>"
    and W_cap: "card W \<le> cap"
  shows "card (W \<union> fp_next d F B) \<le> Suc \<Delta> * cap"
proof -
  have F_subset: "F \<subseteq> V"
    using F_subset_W W_subset by blast
  have finite_W: "finite W"
    using finite_subset[OF W_subset finite_V] .
  have card_F_le_W: "card F \<le> card W"
    using card_mono[OF finite_W F_subset_W] .
  have card_F_le_cap: "card F \<le> cap"
    using card_F_le_W W_cap by linarith
  have "card (W \<union> fp_next d F B) \<le> card W + \<Delta> * card F"
    using card_seen_after_fp_step_le[OF W_subset F_subset degree] .
  also have "\<dots> \<le> cap + \<Delta> * cap"
    using W_cap card_F_le_cap by (intro add_mono mult_left_mono) simp_all
  also have "\<dots> = Suc \<Delta> * cap"
    by simp
  finally show ?thesis .
qed

lemma fp_iter_capped_seen_subset_V:
  assumes F_subset: "F \<subseteq> V"
    and W_subset: "W \<subseteq> V"
  shows "fp_seen (fp_iter_capped n cap d F W B) \<subseteq> V"
  using assms
proof (induction n arbitrary: d F W)
  case 0
  then show ?case
    unfolding fp_seen_def by simp
next
  case (Suc n)
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  have F'_subset: "?F' \<subseteq> V"
    using fp_next_subset_V .
  have W'_subset: "?W' \<subseteq> V"
    using Suc.prems F'_subset by blast
  show ?case
  proof (cases "card ?W' > cap")
    case True
    then show ?thesis
      using W'_subset by (simp add: fp_seen_def Let_def)
  next
    case False
    have "fp_seen (fp_iter_capped n cap (relax_frontier d F) ?F' ?W' B) \<subseteq> V"
      using Suc.IH[OF F'_subset W'_subset] .
    then show ?thesis
      using False by (simp add: fp_seen_def Let_def)
  qed
qed

lemma fp_iter_capped_frontier_subset_seen:
  assumes "F \<subseteq> W"
  shows "fp_frontier (fp_iter_capped n cap d F W B) \<subseteq>
    fp_seen (fp_iter_capped n cap d F W B)"
  using assms
proof (induction n arbitrary: d F W)
  case 0
  then show ?case
    unfolding fp_frontier_def fp_seen_def by simp
next
  case (Suc n)
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  have F'_W': "?F' \<subseteq> ?W'"
    by blast
  show ?case
  proof (cases "card ?W' > cap")
    case True
    then show ?thesis
      using F'_W' by (simp add: fp_frontier_def fp_seen_def Let_def)
  next
    case False
    show ?thesis
      using Suc.IH[OF F'_W'] False by (simp add: fp_frontier_def fp_seen_def Let_def)
  qed
qed

lemma fp_iter_capped_seen_initial_subset:
  "W \<subseteq> fp_seen (fp_iter_capped n cap d F W B)"
proof (induction n arbitrary: d F W)
  case 0
  then show ?case
    unfolding fp_seen_def by simp
next
  case (Suc n)
  let ?d' = "relax_frontier d F"
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  show ?case
  proof (cases "card ?W' > cap")
    case True
    then show ?thesis
      unfolding fp_seen_def by (simp add: Let_def)
  next
    case False
    have "W \<subseteq> ?W'"
      by blast
    also have "\<dots> \<subseteq> fp_seen (fp_iter_capped n cap ?d' ?F' ?W' B)"
      by (rule Suc.IH)
    finally show ?thesis
      using False unfolding fp_seen_def by (simp add: Let_def)
  qed
qed

lemma fp_iter_capped_seen_reaches:
  assumes F_reaches: "\<And>u. u \<in> F \<Longrightarrow> reachable s u"
    and W_reaches: "\<And>u. u \<in> W \<Longrightarrow> reachable s u"
  shows "\<forall>u\<in>fp_seen (fp_iter_capped n cap d F W B). reachable s u"
  using assms
proof (induction n arbitrary: d F W)
  case 0
  then show ?case
    unfolding fp_seen_def by simp
next
  case (Suc n)
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  have F'_reaches: "\<And>u. u \<in> ?F' \<Longrightarrow> reachable s u"
  proof -
    fix u
    assume uF': "u \<in> ?F'"
    then obtain x where xF: "x \<in> F" and edge: "(x, u) \<in> E"
      unfolding fp_next_def by blast
    have "reachable s x"
      by (rule Suc.prems(1)[OF xF])
    then show "reachable s u"
      using dist_triangle_edge[OF edge] by blast
  qed
  have W'_reaches: "\<And>u. u \<in> ?W' \<Longrightarrow> reachable s u"
    using Suc.prems(2) F'_reaches by blast
  show ?case
  proof (cases "card ?W' > cap")
    case True
    then show ?thesis
      using W'_reaches by (simp add: fp_seen_def Let_def)
  next
    case False
    have tail:
      "\<forall>u\<in>fp_seen (fp_iter_capped n cap (relax_frontier d F) ?F' ?W' B).
        reachable s u"
      by (rule Suc.IH
        [where d = "relax_frontier d F" and F = ?F' and W = ?W',
          OF F'_reaches W'_reaches])
    show ?thesis
      using tail False by (simp add: fp_seen_def Let_def)
  qed
qed

lemma find_pivots_seen_capped_reaches:
  assumes S_reaches: "\<And>u. u \<in> S \<Longrightarrow> reachable s u"
    and u: "u \<in> find_pivots_seen_capped k cap d S B"
  shows "reachable s u"
  using fp_iter_capped_seen_reaches
    [where F = S and W = S and n = k and cap = cap and d = d and B = B,
      OF S_reaches S_reaches]
    u
  unfolding find_pivots_seen_capped_def by blast

theorem fp_iter_capped_seen_card_le:
  assumes F_subset_W: "F \<subseteq> W"
    and W_subset: "W \<subseteq> V"
    and degree: "outdegree_le \<Delta>"
    and W_cap: "card W \<le> cap"
  shows "card (fp_seen (fp_iter_capped n cap d F W B)) \<le> Suc \<Delta> * cap"
  using assms
proof (induction n arbitrary: d F W)
  case 0
  have "card W \<le> Suc \<Delta> * cap"
    using "0.prems"(4) by simp
  then show ?case
    unfolding fp_seen_def by simp
next
  case (Suc n)
  let ?d' = "relax_frontier d F"
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  have F_subset: "F \<subseteq> V"
    using Suc.prems(1,2) by blast
  have F'_subset: "?F' \<subseteq> V"
    using fp_next_subset_V .
  have W'_subset: "?W' \<subseteq> V"
    using Suc.prems(2) F'_subset by blast
  have F'_W': "?F' \<subseteq> ?W'"
    by blast
  have step_cap: "card ?W' \<le> Suc \<Delta> * cap"
    using card_seen_after_fp_step_cap_le
      [OF Suc.prems(1,2,3,4), of d B] .
  show ?case
  proof (cases "card ?W' > cap")
    case True
    then show ?thesis
      using step_cap by (simp add: fp_seen_def Let_def)
  next
    case False
    have W'_cap: "card ?W' \<le> cap"
      using False by simp
    show ?thesis
      using Suc.IH[OF F'_W' W'_subset Suc.prems(3) W'_cap] False
      by (simp add: fp_seen_def Let_def)
  qed
qed

theorem find_pivots_seen_capped_card_le:
  assumes S_subset: "S \<subseteq> V"
    and degree: "outdegree_le \<Delta>"
    and S_cap: "card S \<le> cap"
  shows "card (find_pivots_seen_capped k cap d S B) \<le> Suc \<Delta> * cap"
  unfolding find_pivots_seen_capped_def
  by (rule fp_iter_capped_seen_card_le[OF subset_refl S_subset degree S_cap])

theorem fp_iter_capped_scan_cost_le:
  assumes F_subset_W: "F \<subseteq> W"
    and W_subset: "W \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
    and W_cap: "card W \<le> cap"
  shows "fp_iter_capped_scan_cost n cap d F W B \<le> n * \<Delta> * cap"
  using assms
proof (induction n arbitrary: d F W)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  let ?d' = "relax_frontier d F"
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  have F_subset: "F \<subseteq> V"
    using Suc.prems(1,2) by blast
  have finite_W: "finite W"
    using finite_subset[OF Suc.prems(2) finite_V] .
  have card_F_le_W: "card F \<le> card W"
    using card_mono[OF finite_W Suc.prems(1)] .
  have card_F_le_cap: "card F \<le> cap"
    using card_F_le_W Suc.prems(4) by linarith
  have round_le: "card (outgoing_edges F) \<le> \<Delta> * cap"
  proof -
    have "card (outgoing_edges F) \<le> \<Delta> * card F"
      using card_outgoing_edges_le[OF F_subset Suc.prems(3)] .
    also have "\<dots> \<le> \<Delta> * cap"
      using card_F_le_cap by simp
    finally show ?thesis .
  qed
  show ?case
  proof (cases "card ?W' > cap")
    case True
    have "card (outgoing_edges F) \<le> Suc n * \<Delta> * cap"
    proof -
      have "\<Delta> * cap \<le> Suc n * (\<Delta> * cap)"
        by simp
      also have "\<dots> = Suc n * \<Delta> * cap"
        by (simp add: algebra_simps)
      finally show ?thesis
        using round_le by linarith
    qed
    then show ?thesis
      using True by (simp add: Let_def)
  next
    case False
    have F'_W': "?F' \<subseteq> ?W'"
      by blast
    have F'_subset: "?F' \<subseteq> V"
      using fp_next_subset_V .
    have W'_subset: "?W' \<subseteq> V"
      using Suc.prems(2) F'_subset by blast
    have W'_cap: "card ?W' \<le> cap"
      using False by simp
    have tail_le:
      "fp_iter_capped_scan_cost n cap ?d' ?F' ?W' B \<le> n * \<Delta> * cap"
      using Suc.IH[OF F'_W' W'_subset Suc.prems(3) W'_cap] .
    have "card (outgoing_edges F) +
        fp_iter_capped_scan_cost n cap ?d' ?F' ?W' B
        \<le> \<Delta> * cap + n * \<Delta> * cap"
      using round_le tail_le by simp
    also have "\<dots> = Suc n * \<Delta> * cap"
      by (simp add: algebra_simps)
    finally show ?thesis
      using False by (simp add: Let_def)
  qed
qed

theorem find_pivots_capped_scan_cost_le:
  assumes S_subset: "S \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
    and S_cap: "card S \<le> cap"
  shows "fp_iter_capped_scan_cost k cap d S S B \<le> k * \<Delta> * cap"
  by (rule fp_iter_capped_scan_cost_le[OF subset_refl S_subset degree S_cap])

theorem fp_iter_capped_scan_cost_le_seen:
  assumes F_subset_W: "F \<subseteq> W"
    and W_subset: "W \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
  shows "fp_iter_capped_scan_cost n cap d F W B \<le>
    n * \<Delta> * card (fp_seen (fp_iter_capped n cap d F W B))"
  using F_subset_W W_subset
proof (induction n arbitrary: d F W)
  case 0
  then show ?case
    unfolding fp_iter_capped_scan_cost.simps by simp
next
  case (Suc n)
  let ?d' = "relax_frontier d F"
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  let ?final = "fp_seen (fp_iter_capped (Suc n) cap d F W B)"
  have F_subset_V: "F \<subseteq> V"
    using Suc.prems by blast
  have finite_final: "finite ?final"
    using fp_iter_capped_seen_subset_V[OF F_subset_V Suc.prems(2)] finite_V
    by (rule finite_subset)
  have W_final: "W \<subseteq> ?final"
    by (rule fp_iter_capped_seen_initial_subset)
  have F_final: "F \<subseteq> ?final"
    using Suc.prems(1) W_final by blast
  have card_F_le_final: "card F \<le> card ?final"
    by (rule card_mono[OF finite_final F_final])
  have round_le:
    "card (outgoing_edges F) \<le> \<Delta> * card ?final"
  proof -
    have "card (outgoing_edges F) \<le> \<Delta> * card F"
      by (rule card_outgoing_edges_le[OF F_subset_V degree])
    also have "\<dots> \<le> \<Delta> * card ?final"
      using card_F_le_final by simp
    finally show ?thesis .
  qed
  show ?case
  proof (cases "card ?W' > cap")
    case True
    have "card (outgoing_edges F) \<le> Suc n * \<Delta> * card ?final"
    proof -
      have "\<Delta> * card ?final \<le> Suc n * (\<Delta> * card ?final)"
        by simp
      then show ?thesis
        using round_le by linarith
    qed
    then show ?thesis
      using True by (simp add: Let_def)
  next
    case False
    have F'_subset_W': "?F' \<subseteq> ?W'"
      by blast
    have W'_subset: "?W' \<subseteq> V"
      using Suc.prems fp_next_subset_V by blast
    have tail:
      "fp_iter_capped_scan_cost n cap ?d' ?F' ?W' B \<le>
        n * \<Delta> * card (fp_seen (fp_iter_capped n cap ?d' ?F' ?W' B))"
      by (rule Suc.IH[OF F'_subset_W' W'_subset])
    have final_eq:
      "?final = fp_seen (fp_iter_capped n cap ?d' ?F' ?W' B)"
      using False by (simp add: fp_seen_def Let_def)
    have "card (outgoing_edges F) +
        fp_iter_capped_scan_cost n cap ?d' ?F' ?W' B \<le>
        \<Delta> * card ?final + n * \<Delta> * card ?final"
      using round_le tail final_eq by simp
    also have "\<dots> = Suc n * \<Delta> * card ?final"
      by (simp add: algebra_simps)
    finally show ?thesis
      using False by (simp add: Let_def)
  qed
qed

theorem find_pivots_capped_scan_cost_le_seen:
  assumes S_subset: "S \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
  shows "fp_iter_capped_scan_cost k cap d S S B \<le>
    k * \<Delta> * card (find_pivots_seen_capped k cap d S B)"
  unfolding find_pivots_seen_capped_def
  by (rule fp_iter_capped_scan_cost_le_seen[OF subset_refl S_subset degree])

theorem fp_iter_capped_scan_cost_le_outgoing_seen:
  assumes F_subset_W: "F \<subseteq> W"
  shows "fp_iter_capped_scan_cost n cap d F W B \<le>
    n * card (outgoing_edges (fp_seen (fp_iter_capped n cap d F W B)))"
  using F_subset_W
proof (induction n arbitrary: d F W)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  let ?d' = "relax_frontier d F"
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  let ?final = "fp_seen (fp_iter_capped (Suc n) cap d F W B)"
  have W_final: "W \<subseteq> ?final"
    by (rule fp_iter_capped_seen_initial_subset)
  have F_final: "F \<subseteq> ?final"
    using Suc.prems W_final by blast
  have outgoing_subset: "outgoing_edges F \<subseteq> outgoing_edges ?final"
    using F_final unfolding outgoing_edges_def by blast
  have round_le:
    "card (outgoing_edges F) \<le> card (outgoing_edges ?final)"
    by (rule card_mono[OF finite_outgoing_edges outgoing_subset])
  show ?case
  proof (cases "card ?W' > cap")
    case True
    have "card (outgoing_edges F) \<le>
        Suc n * card (outgoing_edges ?final)"
    proof -
      have "card (outgoing_edges ?final) \<le>
          Suc n * card (outgoing_edges ?final)"
        by simp
      then show ?thesis
        using round_le by linarith
    qed
    then show ?thesis
      using True by (simp add: Let_def)
  next
    case False
    have tail:
      "fp_iter_capped_scan_cost n cap ?d' ?F' ?W' B \<le>
        n * card (outgoing_edges (fp_seen (fp_iter_capped n cap ?d' ?F' ?W' B)))"
      by (rule Suc.IH) blast
    have final_eq:
      "?final = fp_seen (fp_iter_capped n cap ?d' ?F' ?W' B)"
      using False by (simp add: fp_seen_def Let_def)
    have "card (outgoing_edges F) +
        fp_iter_capped_scan_cost n cap ?d' ?F' ?W' B \<le>
        card (outgoing_edges ?final) +
        n * card (outgoing_edges ?final)"
      using round_le tail final_eq by simp
    also have "\<dots> = Suc n * card (outgoing_edges ?final)"
      by (simp add: algebra_simps)
    finally show ?thesis
      using False by (simp add: Let_def)
  qed
qed

theorem find_pivots_capped_scan_cost_le_outgoing_seen:
  shows "fp_iter_capped_scan_cost k cap d S S B \<le>
    k * card (outgoing_edges (find_pivots_seen_capped k cap d S B))"
  unfolding find_pivots_seen_capped_def
  by (rule fp_iter_capped_scan_cost_le_outgoing_seen[OF subset_refl])

text \<open>
  The capped search scans only edges leaving frontiers that have already been
  absorbed into the final seen set.  The theorem
  @{thm find_pivots_capped_scan_cost_le_outgoing_seen} is the compact cost
  statement used later: @{const fp_iter_capped_scan_cost} is bounded by the
  number of rounds times the outgoing-edge volume of
  @{const find_pivots_seen_capped}.  This is deliberately stated in terms of
  the final seen set rather than a sum over intermediate frontiers, because the
  top-level analysis controls the size of that set through the cap.
\<close>

lemma fp_iter_capped_eq_fp_iter_if_final_within_cap:
  assumes final_cap: "card (fp_seen (fp_iter_capped n cap d F W B)) \<le> cap"
  shows "fp_iter_capped n cap d F W B = fp_iter n d F W B"
  using final_cap
proof (induction n arbitrary: d F W)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  let ?d' = "relax_frontier d F"
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  show ?case
  proof (cases "card ?W' > cap")
    case True
    then have "fp_seen (fp_iter_capped (Suc n) cap d F W B) = ?W'"
      by (simp add: fp_seen_def Let_def)
    then have False
      using Suc.prems True by simp
    then show ?thesis
      by blast
  next
    case False
    have tail_cap:
      "card (fp_seen (fp_iter_capped n cap ?d' ?F' ?W' B)) \<le> cap"
      using Suc.prems False by (simp add: fp_seen_def Let_def)
    have "fp_iter_capped n cap ?d' ?F' ?W' B = fp_iter n ?d' ?F' ?W' B"
      using Suc.IH[OF tail_cap] .
    then show ?thesis
      using False by (simp add: Let_def)
  qed
qed

lemma fp_iter_seen_subset_V:
  assumes F_subset: "F \<subseteq> V"
    and W_subset: "W \<subseteq> V"
  shows "fp_seen (fp_iter n d F W B) \<subseteq> V"
  using assms
proof (induction n arbitrary: d F W)
  case 0
  then show ?case
    unfolding fp_seen_def by simp
next
  case (Suc n)
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  have "?F' \<subseteq> V"
    using fp_next_subset_V .
  then have "?W' \<subseteq> V"
    using Suc.prems by blast
  then have "fp_seen (fp_iter n (relax_frontier d F) ?F' ?W' B) \<subseteq> V"
    using Suc.IH[OF \<open>?F' \<subseteq> V\<close>] by blast
  then show ?case
    by (simp add: fp_seen_def Let_def)
qed

lemma find_pivots_seen_subset_V:
  assumes "S \<subseteq> V"
  shows "find_pivots_seen k d S B \<subseteq> V"
  unfolding find_pivots_seen_def
  using fp_iter_seen_subset_V[OF assms assms] .

lemma finite_find_pivots_seen [simp]:
  assumes "S \<subseteq> V"
  shows "finite (find_pivots_seen k d S B)"
  using finite_subset[OF find_pivots_seen_subset_V[OF assms] finite_V] .

lemma fp_next_tight_successor:
  assumes sound: "sound_label d"
    and uF: "u \<in> F"
    and complete_u: "d u = dist s u"
    and tight: "tight_edge_step u v"
    and below_v: "below_bound (dist s v) B"
  shows "v \<in> fp_next d F B"
proof -
  have edge: "(u, v) \<in> E" and reach_u: "reachable s u"
    and dist_v: "dist s v = dist s u + w u v"
    using tight unfolding tight_edge_step_def by auto
  have vV: "v \<in> V"
    using edge edge_in_V by blast
  have reach_v: "reachable s v"
    using dist_triangle_edge[OF edge reach_u] by blast
  have "dist s v \<le> d v"
    using sound vV reach_v unfolding sound_label_def by blast
  then have "d u + w u v \<le> d v"
    using complete_u dist_v by simp
  moreover have "below_bound (d u + w u v) B"
    using complete_u dist_v below_v by simp
  ultimately show ?thesis
    using uF edge vV unfolding fp_next_def by blast
qed

lemma fp_step_tight_successor_complete:
  assumes sound: "sound_label d"
    and uF: "u \<in> F"
    and frontier_reaches: "\<And>x. x \<in> F \<Longrightarrow> reachable s x"
    and complete_u: "d u = dist s u"
    and tight: "tight_edge_step u v"
    and below_v: "below_bound (dist s v) B"
  shows "sound_label (relax_frontier d F)"
    and "relax_frontier d F v = dist s v"
    and "v \<in> fp_next d F B"
proof -
  show "sound_label (relax_frontier d F)"
    using relax_frontier_tight_successor_complete(1)
      [OF sound uF frontier_reaches complete_u tight] .
  show "relax_frontier d F v = dist s v"
    using relax_frontier_tight_successor_complete(2)
      [OF sound uF frontier_reaches complete_u tight] .
  show "v \<in> fp_next d F B"
    using fp_next_tight_successor[OF sound uF complete_u tight below_v] .
qed

lemma fp_iter_seen_mono:
  assumes "x \<in> W"
  shows "x \<in> fp_seen (fp_iter n d F W B)"
  using assms
proof (induction n arbitrary: d F W)
  case 0
  then show ?case
    unfolding fp_seen_def by simp
next
  case (Suc n)
  let ?d' = "relax_frontier d F"
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  have "x \<in> ?W'"
    using Suc.prems by blast
  then have "x \<in> fp_seen (fp_iter n ?d' ?F' ?W' B)"
    using Suc.IH by blast
  then show ?case
    by (simp add: fp_seen_def Let_def)
qed

lemma relax_frontier_preserves_complete_sound:
  assumes sound: "sound_label d"
    and complete_x: "d x = dist s x"
    and reaches: "\<And>u. u \<in> F \<Longrightarrow> reachable s u"
  shows "relax_frontier d F x = dist s x"
proof -
  let ?es = "edge_list_of (outgoing_edges F)"
  have set_es: "set ?es = outgoing_edges F"
    using edge_list_of_properties(1)[OF finite_outgoing_edges] .
  have edges: "\<And>u v. (u, v) \<in> set ?es \<Longrightarrow> (u, v) \<in> E"
    using set_es unfolding outgoing_edges_def by blast
  have reaches_es: "\<And>u v. (u, v) \<in> set ?es \<Longrightarrow> reachable s u"
    using set_es reaches unfolding outgoing_edges_def by blast
  show ?thesis
  unfolding relax_frontier_def
  using relax_edges_preserves_complete_sound[OF sound complete_x edges reaches_es] .
qed

lemma relax_frontier_preserves_bmssp_pre_full:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and reaches: "\<And>u. u \<in> F \<Longrightarrow> reachable s u"
  shows "bmssp_pre_full (relax_frontier d F) S B"
proof -
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have cover:
    "\<And>v. \<lbrakk>v \<in> V; reachable s v; below_bound (dist s v) B;
       relax_frontier d F v \<noteq> dist s v\<rbrakk>
      \<Longrightarrow> through_complete (relax_frontier d F) S v"
  proof -
    fix v
    assume vV: "v \<in> V" and reach_v: "reachable s v"
      and below_v: "below_bound (dist s v) B"
      and incomplete_v: "relax_frontier d F v \<noteq> dist s v"
    have d_incomplete: "d v \<noteq> dist s v"
    proof
      assume complete_v: "d v = dist s v"
      have "relax_frontier d F v = dist s v"
        by (rule relax_frontier_preserves_complete_sound
          [OF sound complete_v reaches])
      then show False
        using incomplete_v by simp
    qed
    have through_d: "through_complete d S v"
      using pre vV reach_v below_v d_incomplete
      unfolding bmssp_pre_full_def by blast
    then obtain u p where uS: "u \<in> S"
      and u_complete: "u \<in> complete_vertices d"
      and sp: "shortest_walk s p v"
      and up: "u \<in> set p"
      unfolding through_complete_def through_def by blast
    have uV: "u \<in> V" and reach_u: "reachable s u"
      and du: "d u = dist s u"
      using u_complete unfolding complete_vertices_def by auto
    have relax_u: "relax_frontier d F u = dist s u"
      by (rule relax_frontier_preserves_complete_sound[OF sound du reaches])
    have "u \<in> complete_vertices (relax_frontier d F)"
      using uV reach_u relax_u unfolding complete_vertices_def by blast
    then have "through (S \<inter> complete_vertices (relax_frontier d F)) v"
      using uS sp up unfolding through_def by blast
    then show "through_complete (relax_frontier d F) S v"
      unfolding through_complete_def .
  qed
  show ?thesis
    using S_subset cover unfolding bmssp_pre_full_def by blast
qed

lemma fp_iter_capped_preserves_bmssp_pre_full:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B0"
    and reaches: "\<And>u. u \<in> F \<Longrightarrow> reachable s u"
  shows "bmssp_pre_full (fp_label (fp_iter_capped n cap d F W B)) S B0"
  using assms
proof (induction n arbitrary: d F W)
  case 0
  then show ?case
    unfolding fp_label_def by simp
next
  case (Suc n)
  let ?d' = "relax_frontier d F"
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  have sound': "sound_label ?d'"
    using relax_frontier_sound[OF Suc.prems(1,3)] .
  have pre': "bmssp_pre_full ?d' S B0"
    by (rule relax_frontier_preserves_bmssp_pre_full
      [OF Suc.prems(1,2,3)])
  have reaches': "\<And>u. u \<in> ?F' \<Longrightarrow> reachable s u"
    using fp_next_reaches[OF Suc.prems(3)] by blast
  show ?case
  proof (cases "card ?W' > cap")
    case True
    then show ?thesis
      using pre' by (simp add: fp_label_def Let_def)
  next
    case False
    show ?thesis
      using Suc.IH[OF sound' pre' reaches'] False
      by (simp add: fp_label_def Let_def)
  qed
qed

lemma find_pivots_label_capped_preserves_source_pre:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>u. u \<in> S \<Longrightarrow> reachable s u"
  shows "bmssp_pre_full (find_pivots_label_capped k cap d S B) S B"
  unfolding find_pivots_label_capped_def
  by (rule fp_iter_capped_preserves_bmssp_pre_full
    [OF sound pre S_reaches])

lemma fp_iter_capped_label_le:
  "fp_label (fp_iter_capped n cap d F W B) x \<le> d x"
proof (induction n arbitrary: d F W)
  case 0
  then show ?case
    unfolding fp_label_def by simp
next
  case (Suc n)
  let ?d' = "relax_frontier d F"
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  show ?case
  proof (cases "card ?W' > cap")
    case True
    then show ?thesis
      using relax_frontier_le[of d F x]
      by (simp add: fp_label_def Let_def)
  next
    case False
    have tail: "fp_label (fp_iter_capped n cap ?d' ?F' ?W' B) x \<le> ?d' x"
      by (rule Suc.IH)
    also have "\<dots> \<le> d x"
      by (rule relax_frontier_le)
    finally show ?thesis
      using False by (simp add: fp_label_def Let_def)
  qed
qed

lemma find_pivots_label_capped_le:
  "find_pivots_label_capped k cap d S B x \<le> d x"
  unfolding find_pivots_label_capped_def
  by (rule fp_iter_capped_label_le)

lemma fp_iter_capped_label_sound:
  assumes sound: "sound_label d"
    and reaches: "\<And>u. u \<in> F \<Longrightarrow> reachable s u"
  shows "sound_label (fp_label (fp_iter_capped n cap d F W B))"
  using assms
proof (induction n arbitrary: d F W)
  case 0
  then show ?case
    unfolding fp_label_def by simp
next
  case (Suc n)
  let ?d' = "relax_frontier d F"
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  have sound': "sound_label ?d'"
    using relax_frontier_sound[OF Suc.prems] .
  have reaches': "\<And>u. u \<in> ?F' \<Longrightarrow> reachable s u"
    using fp_next_reaches[OF Suc.prems(2)] by blast
  show ?case
  proof (cases "card ?W' > cap")
    case True
    then show ?thesis
      using sound' by (simp add: fp_label_def Let_def)
  next
    case False
    show ?thesis
      using Suc.IH[OF sound' reaches'] False by (simp add: fp_label_def Let_def)
  qed
qed

lemma fp_iter_capped_preserves_complete_sound:
  assumes sound: "sound_label d"
    and complete_x: "d x = dist s x"
    and reaches: "\<And>u. u \<in> F \<Longrightarrow> reachable s u"
  shows "fp_label (fp_iter_capped n cap d F W B) x = dist s x"
  using assms
proof (induction n arbitrary: d F W)
  case 0
  then show ?case
    unfolding fp_label_def by simp
next
  case (Suc n)
  let ?d' = "relax_frontier d F"
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  have sound': "sound_label ?d'"
    using relax_frontier_sound[OF Suc.prems(1,3)] .
  have complete': "?d' x = dist s x"
    using relax_frontier_preserves_complete_sound[OF Suc.prems] .
  have reaches': "\<And>u. u \<in> ?F' \<Longrightarrow> reachable s u"
    using fp_next_reaches[OF Suc.prems(3)] by blast
  show ?case
  proof (cases "card ?W' > cap")
    case True
    then show ?thesis
      using complete' by (simp add: fp_label_def Let_def)
  next
    case False
    show ?thesis
      using Suc.IH[OF sound' complete' reaches'] False
      by (simp add: fp_label_def Let_def)
  qed
qed

theorem find_pivots_capped_overflow_establishes_pre:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and overflow: "card (find_pivots_seen_capped k cap d S B) > cap"
  shows "bmssp_pre_full
    (find_pivots_label_capped k cap d S B)
    (find_pivots_pivots_capped k cap d S B) B"
proof -
  let ?d' = "find_pivots_label_capped k cap d S B"
  have pivots_eq: "find_pivots_pivots_capped k cap d S B = S"
    using overflow unfolding find_pivots_pivots_capped_def by simp
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have preserve_complete:
    "\<And>x. d x = dist s x \<Longrightarrow> ?d' x = dist s x"
    unfolding find_pivots_label_capped_def
    by (rule fp_iter_capped_preserves_complete_sound[OF sound _ S_reaches])
  have cover:
    "\<And>v. \<lbrakk>v \<in> V; reachable s v; below_bound (dist s v) B;
       ?d' v \<noteq> dist s v\<rbrakk> \<Longrightarrow> through_complete ?d' S v"
  proof -
    fix v
    assume vV: "v \<in> V"
      and reach_v: "reachable s v"
      and below_v: "below_bound (dist s v) B"
      and d'_incomplete: "?d' v \<noteq> dist s v"
    have d_incomplete: "d v \<noteq> dist s v"
    proof
      assume "d v = dist s v"
      then have "?d' v = dist s v"
        by (rule preserve_complete)
      with d'_incomplete show False
        by simp
    qed
    have "through_complete d S v"
      using pre vV reach_v below_v d_incomplete unfolding bmssp_pre_full_def by blast
    then obtain u p where uS: "u \<in> S" and ucomp: "u \<in> complete_vertices d"
      and sp: "shortest_walk s p v" and u_path: "u \<in> set p"
      unfolding through_complete_def through_def by blast
    have uV: "u \<in> V" and reach_u: "reachable s u" and complete_u: "d u = dist s u"
      using ucomp unfolding complete_vertices_def by auto
    have complete_u': "?d' u = dist s u"
      using preserve_complete[OF complete_u] .
    have "u \<in> complete_vertices ?d'"
      using uV reach_u complete_u' unfolding complete_vertices_def by blast
    then have "through (S \<inter> complete_vertices ?d') v"
      using uS sp u_path unfolding through_def by blast
    then show "through_complete ?d' S v"
      unfolding through_complete_def .
  qed
  show ?thesis
    unfolding bmssp_pre_full_def
  proof
    show "find_pivots_pivots_capped k cap d S B \<subseteq> V"
      using pivots_eq S_subset by simp
  next
    show "\<forall>v\<in>V. reachable s v \<longrightarrow> below_bound (dist s v) B \<longrightarrow>
      ?d' v \<noteq> dist s v \<longrightarrow>
      through_complete ?d' (find_pivots_pivots_capped k cap d S B) v"
    proof (intro ballI impI)
      fix v
      assume vV: "v \<in> V"
        and reach_v: "reachable s v"
        and below_v: "below_bound (dist s v) B"
        and incomplete_v: "?d' v \<noteq> dist s v"
      have "through_complete ?d' S v"
        using cover[OF vV reach_v below_v incomplete_v] .
      then show "through_complete ?d' (find_pivots_pivots_capped k cap d S B) v"
        using pivots_eq by simp
    qed
  qed
qed

lemma fp_iter_preserves_complete_sound:
  assumes sound: "sound_label d"
    and complete_x: "d x = dist s x"
    and reaches: "\<And>u. u \<in> F \<Longrightarrow> reachable s u"
  shows "fp_label (fp_iter n d F W B) x = dist s x"
  using sound complete_x reaches
proof (induction n arbitrary: d F W)
  case 0
  then show ?case
    unfolding fp_label_def by simp
next
  case (Suc n)
  let ?d' = "relax_frontier d F"
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  have sound': "sound_label ?d'"
    using relax_frontier_sound[OF Suc.prems(1,3)] .
  have complete': "?d' x = dist s x"
    using relax_frontier_preserves_complete_sound[OF Suc.prems] .
  have reaches': "\<And>u. u \<in> ?F' \<Longrightarrow> reachable s u"
    using fp_next_reaches[OF Suc.prems(3)] by blast
  show ?case
    using Suc.IH[OF sound' complete' reaches'] by (simp add: fp_label_def Let_def)
qed

lemma fp_iter_one_tight_step_completion:
  assumes sound: "sound_label d"
    and uF: "u \<in> F"
    and frontier_reaches: "\<And>x. x \<in> F \<Longrightarrow> reachable s x"
    and complete_u: "d u = dist s u"
    and tight: "tight_edge_step u v"
    and below_v: "below_bound (dist s v) B"
  shows "fp_label (fp_iter (Suc n) d F W B) v = dist s v"
    and "v \<in> fp_seen (fp_iter (Suc n) d F W B)"
proof -
  let ?d' = "relax_frontier d F"
  let ?F' = "fp_next d F B"
  let ?W' = "W \<union> ?F'"
  have sound': "sound_label ?d'"
    using fp_step_tight_successor_complete(1)
      [OF sound uF frontier_reaches complete_u tight below_v] .
  have complete_v: "?d' v = dist s v"
    using fp_step_tight_successor_complete(2)
      [OF sound uF frontier_reaches complete_u tight below_v] .
  have vF': "v \<in> ?F'"
    using fp_step_tight_successor_complete(3)
      [OF sound uF frontier_reaches complete_u tight below_v] .
  have reaches': "\<And>x. x \<in> ?F' \<Longrightarrow> reachable s x"
    using fp_next_reaches[OF frontier_reaches] by blast
  have tail_complete:
    "fp_label (fp_iter n ?d' ?F' ?W' B) v = dist s v"
    by (rule fp_iter_preserves_complete_sound[OF sound' complete_v reaches'])
  show "fp_label (fp_iter (Suc n) d F W B) v = dist s v"
    using tail_complete by (simp add: fp_label_def Let_def)
  have "v \<in> ?W'"
    using vF' by blast
  then have tail_seen: "v \<in> fp_seen (fp_iter n ?d' ?F' ?W' B)"
    using fp_iter_seen_mono[of v ?W' n ?d' ?F' B] by blast
  then show "v \<in> fp_seen (fp_iter (Suc n) d F W B)"
    using tail_seen by (simp add: fp_seen_def Let_def)
qed

lemma fp_iter_tight_path_completion:
  assumes sound: "sound_label d"
    and frontier_reaches: "\<And>x. x \<in> F \<Longrightarrow> reachable s x"
    and F_seen: "F \<subseteq> W"
    and nonempty: "p \<noteq> []"
    and start: "hd p \<in> F"
    and complete_start: "d (hd p) = dist s (hd p)"
    and tight: "successively tight_edge_step p"
    and below: "\<And>x. x \<in> set p \<Longrightarrow> below_bound (dist s x) B"
    and len: "length (path_edges p) \<le> n"
  shows "fp_label (fp_iter n d F W B) (last p) = dist s (last p) \<and>
    last p \<in> fp_seen (fp_iter n d F W B)"
  using assms
proof (induction p arbitrary: n d F W rule: path_edges.induct)
  case 1
  then show ?case
    by simp
next
  case (2 x)
  have sound0: "sound_label d"
    using "2.prems" by blast
  have reaches0: "\<And>z. z \<in> F \<Longrightarrow> reachable s z"
    using "2.prems" by blast
  have complete0: "d x = dist s x"
    using "2.prems" by simp
  have complete_x: "fp_label (fp_iter n d F W B) x = dist s x"
    using fp_iter_preserves_complete_sound[OF sound0 complete0 reaches0] .
  have seen_x: "x \<in> fp_seen (fp_iter n d F W B)"
  proof -
    have "x \<in> W"
      using "2.prems" by auto
    then show ?thesis
      using fp_iter_seen_mono by blast
  qed
  show ?case
    using complete_x seen_x by simp
next
  case (3 x y xs)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis
      using "3.prems"(9) by simp
  next
    case (Suc m)
    let ?d' = "relax_frontier d F"
    let ?F' = "fp_next d F B"
    let ?W' = "W \<union> ?F'"
    have sound0: "sound_label d"
      using "3.prems" by blast
    have reaches0: "\<And>z. z \<in> F \<Longrightarrow> reachable s z"
      using "3.prems" by blast
    have xF: "x \<in> F"
      using "3.prems" by simp
    have complete_x: "d x = dist s x"
      using "3.prems" by simp
    have step: "tight_edge_step x y"
      using "3.prems" by (simp add: successively_Cons)
    have below_y: "below_bound (dist s y) B"
      using "3.prems" by simp
    have sound': "sound_label ?d'"
      using fp_step_tight_successor_complete(1)
        [OF sound0 xF reaches0 complete_x step below_y] .
    have complete_y: "?d' y = dist s y"
      using fp_step_tight_successor_complete(2)
        [OF sound0 xF reaches0 complete_x step below_y] .
    have yF': "y \<in> ?F'"
      using fp_step_tight_successor_complete(3)
        [OF sound0 xF reaches0 complete_x step below_y] .
    have reaches': "\<And>z. z \<in> ?F' \<Longrightarrow> reachable s z"
      using fp_next_reaches[OF reaches0] by blast
    have F_seen': "?F' \<subseteq> ?W'"
      by blast
    have tail_nonempty: "y # xs \<noteq> []"
      by simp
    have tail_start: "hd (y # xs) \<in> ?F'"
      using yF' by simp
    have tail_complete_start: "?d' (hd (y # xs)) = dist s (hd (y # xs))"
      using complete_y by simp
    have tail_tight: "successively tight_edge_step (y # xs)"
      using "3.prems" by (simp add: successively_Cons)
    have tail_below: "\<And>z. z \<in> set (y # xs) \<Longrightarrow> below_bound (dist s z) B"
      using "3.prems" by simp
    have tail_len: "length (path_edges (y # xs)) \<le> m"
      using "3.prems" Suc by simp
    have tail:
      "fp_label (fp_iter m ?d' ?F' ?W' B) (last (y # xs)) =
        dist s (last (y # xs)) \<and>
       last (y # xs) \<in> fp_seen (fp_iter m ?d' ?F' ?W' B)"
      using "3.IH"[of ?d' ?F' ?W' m,
          OF sound' reaches' F_seen' tail_nonempty tail_start tail_complete_start
          tail_tight tail_below tail_len]
      by simp
    then show ?thesis
      using Suc by (simp add: fp_label_def fp_seen_def Let_def)
  qed
qed

corollary find_pivots_short_tight_path_complete:
  assumes sound: "sound_label d"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and nonempty: "p \<noteq> []"
    and start: "hd p \<in> S"
    and complete_start: "d (hd p) = dist s (hd p)"
    and tight: "successively tight_edge_step p"
    and below: "\<And>x. x \<in> set p \<Longrightarrow> below_bound (dist s x) B"
    and len: "length (path_edges p) \<le> k"
  shows "find_pivots_label k d S B (last p) = dist s (last p)"
    and "last p \<in> find_pivots_seen k d S B"
proof -
  have combined:
    "fp_label (fp_iter k d S S B) (last p) = dist s (last p) \<and>
      last p \<in> fp_seen (fp_iter k d S S B)"
    using fp_iter_tight_path_completion
      [OF sound S_reaches subset_refl nonempty start complete_start tight below len] .
  show "find_pivots_label k d S B (last p) = dist s (last p)"
    using combined unfolding find_pivots_label_def by blast
  show "last p \<in> find_pivots_seen k d S B"
    using combined unfolding find_pivots_seen_def by blast
qed

lemma find_pivots_short_paths_complete_on:
  assumes sound: "sound_label d"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and witnesses:
      "\<And>x. x \<in> X \<Longrightarrow> \<exists>p. p \<noteq> [] \<and> hd p \<in> S \<and> last p = x \<and>
        d (hd p) = dist s (hd p) \<and> successively tight_edge_step p \<and>
        (\<forall>y\<in>set p. below_bound (dist s y) B) \<and> length (path_edges p) \<le> k"
  shows "complete_on (find_pivots_label k d S B) X \<and>
    X \<subseteq> find_pivots_seen k d S B"
proof -
  have complete: "complete_on (find_pivots_label k d S B) X"
  proof (unfold complete_on_def, intro ballI impI)
    fix x
    assume xX: "x \<in> X"
    obtain p where p:
      "p \<noteq> []" "hd p \<in> S" "last p = x"
      "d (hd p) = dist s (hd p)"
      "successively tight_edge_step p"
      "\<forall>y\<in>set p. below_bound (dist s y) B"
      "length (path_edges p) \<le> k"
      using witnesses[OF xX] by blast
    have "find_pivots_label k d S B (last p) = dist s (last p)"
      using find_pivots_short_tight_path_complete(1)
        [OF sound S_reaches p(1,2,4,5) _ p(7)]
        p(6) by blast
    then show "reachable s x \<Longrightarrow> find_pivots_label k d S B x = dist s x"
      using p(3) by simp
  qed
  have seen: "X \<subseteq> find_pivots_seen k d S B"
  proof
    fix x
    assume xX: "x \<in> X"
    obtain p where p:
      "p \<noteq> []" "hd p \<in> S" "last p = x"
      "d (hd p) = dist s (hd p)"
      "successively tight_edge_step p"
      "\<forall>y\<in>set p. below_bound (dist s y) B"
      "length (path_edges p) \<le> k"
      using witnesses[OF xX] by blast
    have "last p \<in> find_pivots_seen k d S B"
      using find_pivots_short_tight_path_complete(2)
        [OF sound S_reaches p(1,2,4,5) _ p(7)]
        p(6) by blast
    then show "x \<in> find_pivots_seen k d S B"
      using p(3) by simp
  qed
  show ?thesis
    using complete seen by blast
qed

text \<open>
  The path-completion lemmas are the semantic core of FindPivots.  A short
  tight witness is a shortest-path prefix, already correct at its start, whose
  edges remain below the current bound.  The round induction proves that such a
  witness is followed by the relaxation process: @{thm find_pivots_short_tight_path_complete}
  records both the resulting label equality and membership in the seen set.
  The set-level lemma above packages the same fact for any family of witnesses.
  The next theorem instantiates that package with
  @{const find_pivots_short_vertices}, the set defined exactly by
  @{const short_tight_witness}, yielding completeness via @{const complete_on}.
\<close>

theorem find_pivots_completes_short_vertices:
  assumes sound: "sound_label d"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "complete_on (find_pivots_label k d S B)
      (find_pivots_short_vertices k d S B) \<and>
    find_pivots_short_vertices k d S B \<subseteq> find_pivots_seen k d S B"
proof (rule find_pivots_short_paths_complete_on[OF sound S_reaches])
  fix x
  assume "x \<in> find_pivots_short_vertices k d S B"
  then show "\<exists>p. p \<noteq> [] \<and> hd p \<in> S \<and> last p = x \<and>
      d (hd p) = dist s (hd p) \<and> successively tight_edge_step p \<and>
      (\<forall>y\<in>set p. below_bound (dist s y) B) \<and> length (path_edges p) \<le> k"
    unfolding find_pivots_short_vertices_def short_tight_witness_def by blast
qed

lemma card_set_take_distinct:
  assumes "distinct xs" "k \<le> length xs"
  shows "card (set (take k xs)) = k"
  using assms by (simp add: distinct_card)

lemma successively_take:
  assumes "successively R xs"
  shows "successively R (take n xs)"
  unfolding successively_conv_nth
proof clarify
  fix i
  assume i_take: "Suc i < length (take n xs)"
  have i_xs: "Suc i < length xs"
    using i_take by simp
  have si_n: "Suc i < n"
    using i_take by simp
  have step: "R (xs ! i) (xs ! Suc i)"
    using assms i_xs unfolding successively_conv_nth by blast
  have "take n xs ! i = xs ! i"
    using si_n by simp
  moreover have "take n xs ! Suc i = xs ! Suc i"
    using si_n by simp
  ultimately show "R (take n xs ! i) (take n xs ! Suc i)"
    using step by simp
qed

lemma successively_drop:
  assumes "successively R xs"
  shows "successively R (drop n xs)"
  unfolding successively_conv_nth
proof clarify
  fix i
  assume i_drop: "Suc i < length (drop n xs)"
  have i_xs: "Suc (n + i) < length xs"
    using i_drop by simp
  have step: "R (xs ! (n + i)) (xs ! Suc (n + i))"
    using assms i_xs unfolding successively_conv_nth by blast
  have "drop n xs ! i = xs ! (n + i)"
    using i_drop by simp
  moreover have "drop n xs ! Suc i = xs ! Suc (n + i)"
    using i_drop by simp
  ultimately show "R (drop n xs ! i) (drop n xs ! Suc i)"
    using step by simp
qed

lemma below_bound_le_trans:
  assumes "a \<le> b" "below_bound b B"
  shows "below_bound a B"
  using assms by (cases B) auto

lemma find_pivots_pivots_capped_label_below:
  assumes below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and xP: "x \<in> find_pivots_pivots_capped k cap d S B"
  shows "below_bound (find_pivots_label_capped k cap d S B x) B"
proof -
  have xS: "x \<in> S"
    using xP unfolding find_pivots_pivots_capped_def
    by (auto split: if_splits)
  have le: "find_pivots_label_capped k cap d S B x \<le> d x"
    by (rule find_pivots_label_capped_le)
  show ?thesis
    by (rule below_bound_le_trans[OF le below[OF xS]])
qed

lemma find_pivots_completes_short_tree_suffix:
  assumes sound: "sound_label d"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and reach_v: "reachable s v"
    and below_v: "below_bound (dist s v) B"
    and i: "i < length (shortest_path_to v)"
    and source_in_S: "shortest_path_to v ! i \<in> S"
    and source_complete: "d (shortest_path_to v ! i) = dist s (shortest_path_to v ! i)"
    and suffix_len: "length (path_edges (drop i (shortest_path_to v))) \<le> k"
  shows "find_pivots_label k d S B v = dist s v"
    and "v \<in> find_pivots_seen k d S B"
proof -
  let ?p = "shortest_path_to v"
  let ?q = "drop i ?p"
  have sp: "shortest_walk s ?p v"
    using shortest_path_to_shortest[OF reach_v] .
  have tight_p: "successively tight_edge_step ?p"
    using shortest_path_to_successively_tight[OF reach_v] .
  have q_nonempty: "?q \<noteq> []"
    using i by auto
  have hd_q: "hd ?q = ?p ! i"
    using i by (simp add: hd_drop_conv_nth)
  have last_q: "last ?q = v"
    using sp i unfolding shortest_walk_def simple_walk_betw_def walk_betw_def
    by (simp add: last_drop)
  have tight_q: "successively tight_edge_step ?q"
    using successively_drop[OF tight_p, of i] .
  have below_q: "\<And>x. x \<in> set ?q \<Longrightarrow> below_bound (dist s x) B"
  proof -
    fix x
    assume xq: "x \<in> set ?q"
    have "x \<in> set ?p"
      using in_set_dropD[OF xq] .
    then have "tree_path x v"
      using reach_v unfolding tree_path_def by blast
    then have "dist s x \<le> dist s v"
      by (rule tree_path_dist_le)
    then show "below_bound (dist s x) B"
      using below_bound_le_trans[OF _ below_v] by blast
  qed
  have hd_q_S: "hd ?q \<in> S"
    using hd_q source_in_S by simp
  have hd_q_complete: "d (hd ?q) = dist s (hd ?q)"
    using hd_q source_complete by simp
  have label_last: "find_pivots_label k d S B (last ?q) = dist s (last ?q)"
    using find_pivots_short_tight_path_complete(1)
      [OF sound S_reaches q_nonempty hd_q_S hd_q_complete tight_q below_q suffix_len] .
  have seen_last: "last ?q \<in> find_pivots_seen k d S B"
    using find_pivots_short_tight_path_complete(2)
      [OF sound S_reaches q_nonempty hd_q_S hd_q_complete tight_q below_q suffix_len] .
  show "find_pivots_label k d S B v = dist s v"
    using label_last last_q by simp
  show "v \<in> find_pivots_seen k d S B"
    using seen_last last_q by simp
qed

lemma find_pivots_pivot_if_k_seen_tree_vertices:
  assumes uS: "u \<in> S"
    and distinct: "distinct xs"
    and len: "k \<le> length xs"
    and in_tree: "set (take k xs) \<subseteq> tree_of u"
    and seen: "set (take k xs) \<subseteq> find_pivots_seen k d S B"
  shows "u \<in> find_pivots_pivots k d S B"
proof -
  let ?A = "set (take k xs)"
  have card_A: "card ?A = k"
    using card_set_take_distinct[OF distinct len] .
  have A_subset: "?A \<subseteq> tree_of u \<inter> find_pivots_seen k d S B"
    using in_tree seen by blast
  have "card ?A \<le> card (tree_of u \<inter> find_pivots_seen k d S B)"
    using A_subset by (intro card_mono) simp_all
  then show ?thesis
    using uS card_A unfolding find_pivots_pivots_def by simp
qed

lemma finite_find_pivots_pivots [simp]:
  assumes "S \<subseteq> V"
  shows "finite (find_pivots_pivots k d S B)"
proof -
  have "find_pivots_pivots k d S B \<subseteq> V"
    using assms unfolding find_pivots_pivots_def by blast
  then show ?thesis
    using finite_subset[OF _ finite_V] by blast
qed

lemma find_pivots_pivots_subset:
  "find_pivots_pivots k d S B \<subseteq> S"
  unfolding find_pivots_pivots_def by blast

theorem find_pivots_pivots_card_times_le_seen:
  assumes S_subset: "S \<subseteq> V"
    and anti: "tree_antichain S"
  shows "k * card (find_pivots_pivots k d S B) \<le>
    card (find_pivots_seen k d S B)"
proof -
  let ?P = "find_pivots_pivots k d S B"
  let ?W = "find_pivots_seen k d S B"
  let ?A = "\<lambda>u. tree_of u \<inter> ?W"
  have finite_P: "finite ?P"
    using finite_find_pivots_pivots[OF S_subset] .
  have finite_W: "finite ?W"
    using finite_find_pivots_seen[OF S_subset] .
  have finite_A: "\<And>u. u \<in> ?P \<Longrightarrow> finite (?A u)"
    using finite_W by blast
  have disjoint_A:
    "\<And>u v. \<lbrakk>u \<in> ?P; v \<in> ?P; u \<noteq> v\<rbrakk> \<Longrightarrow> ?A u \<inter> ?A v = {}"
  proof -
    fix u v
    assume uP: "u \<in> ?P" and vP: "v \<in> ?P" and neq: "u \<noteq> v"
    have uS: "u \<in> S" and vS: "v \<in> S"
      using uP vP unfolding find_pivots_pivots_def by auto
    have "tree_of u \<inter> tree_of v = {}"
      using tree_of_disjoint_if_antichain[OF anti uS vS neq] .
    then show "?A u \<inter> ?A v = {}"
      by blast
  qed
  have finite_A_all: "\<forall>u\<in>?P. finite (?A u)"
    using finite_A by blast
  have disjoint_A_all: "\<forall>u\<in>?P. \<forall>v\<in>?P. u \<noteq> v \<longrightarrow> ?A u \<inter> ?A v = {}"
    using disjoint_A by blast
  have card_union_image:
    "card (\<Union>(?A ` ?P)) = (\<Sum>u\<in>?P. card (?A u))"
    by (rule card_UN_disjoint[OF finite_P finite_A_all disjoint_A_all])
  have union_eq: "(\<Union>u\<in>?P. ?A u) = \<Union>(?A ` ?P)"
    by blast
  have card_union:
    "card (\<Union>u\<in>?P. ?A u) = (\<Sum>u\<in>?P. card (?A u))"
    using card_union_image union_eq by simp
  have lower: "(\<Sum>u\<in>?P. k) \<le> (\<Sum>u\<in>?P. card (?A u))"
  proof (rule sum_mono)
    fix u
    assume "u \<in> ?P"
    then show "k \<le> card (?A u)"
      unfolding find_pivots_pivots_def by simp
  qed
  have const_sum: "(\<Sum>u\<in>?P. k) = k * card ?P"
    by (simp add: mult.commute)
  have "k * card ?P \<le> card (\<Union>u\<in>?P. ?A u)"
  proof -
    have "k * card ?P \<le> (\<Sum>u\<in>?P. card (?A u))"
      using lower const_sum by (simp add: mult.commute)
    also have "\<dots> = card (\<Union>u\<in>?P. ?A u)"
      using card_union by simp
    finally show ?thesis .
  qed
  also have "\<dots> \<le> card ?W"
  proof (rule card_mono[OF finite_W])
    show "(\<Union>u\<in>?P. ?A u) \<subseteq> ?W"
      by blast
  qed
  finally show ?thesis .
qed

theorem find_pivots_pivots_capped_card_times_le_seen_or_overflow:
  assumes S_subset: "S \<subseteq> V"
    and anti: "tree_antichain S"
  shows "k * card (find_pivots_pivots_capped k cap d S B) \<le>
      card (find_pivots_seen_capped k cap d S B) \<or>
    (find_pivots_pivots_capped k cap d S B = S \<and>
      card (find_pivots_seen_capped k cap d S B) > cap)"
proof (cases "card (find_pivots_seen_capped k cap d S B) > cap")
  case True
  then show ?thesis
    unfolding find_pivots_pivots_capped_def by simp
next
  case False
  have cap_le: "card (find_pivots_seen_capped k cap d S B) \<le> cap"
    using False by simp
  have iter_eq: "fp_iter_capped k cap d S S B = fp_iter k d S S B"
    using fp_iter_capped_eq_fp_iter_if_final_within_cap[of k cap d S S B]
      cap_le unfolding find_pivots_seen_capped_def by simp
  have seen_eq: "find_pivots_seen_capped k cap d S B = find_pivots_seen k d S B"
    using iter_eq unfolding find_pivots_seen_capped_def find_pivots_seen_def by simp
  have pivots_eq:
    "find_pivots_pivots_capped k cap d S B = find_pivots_pivots k d S B"
    using False seen_eq
    unfolding find_pivots_pivots_capped_def find_pivots_pivots_def by simp
  have "k * card (find_pivots_pivots k d S B) \<le>
      card (find_pivots_seen k d S B)"
    by (rule find_pivots_pivots_card_times_le_seen[OF S_subset anti])
  then show ?thesis
    unfolding seen_eq pivots_eq by blast
qed

lemma find_pivots_long_tight_path_root_pivot:
  assumes sound: "sound_label d"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and uS: "u \<in> S"
    and complete_u: "d u = dist s u"
    and p_nonempty: "p \<noteq> []"
    and hd_p: "hd p = u"
    and distinct_p: "distinct p"
    and len: "k \<le> length p"
    and tight: "successively tight_edge_step p"
    and below_prefix:
      "\<And>z. z \<in> set (take k p) \<Longrightarrow> below_bound (dist s z) B"
    and tree_prefix: "set (take k p) \<subseteq> tree_of u"
  shows "u \<in> find_pivots_pivots k d S B"
proof (rule find_pivots_pivot_if_k_seen_tree_vertices[OF uS distinct_p len tree_prefix])
  show "set (take k p) \<subseteq> find_pivots_seen k d S B"
  proof
    fix z
    assume z_take: "z \<in> set (take k p)"
    obtain i where i: "i < length (take k p)" "take k p ! i = z"
      using z_take by (auto simp: in_set_conv_nth)
    have len_take: "length (take k p) = k"
      using len by simp
    have i_k: "i < k"
      using i(1) len_take by simp
    have i_p: "i < length p"
      using i_k len by linarith
    have p_i: "p ! i = z"
      using i i_k by simp
    let ?q = "take (Suc i) p"
    have q_nonempty: "?q \<noteq> []"
      using i_p by (cases p) auto
    have hd_q: "hd ?q = u"
      using hd_p p_nonempty by (cases p) auto
    have hd_q_S: "hd ?q \<in> S"
      using hd_q uS by simp
    have complete_hd_q: "d (hd ?q) = dist s (hd ?q)"
      using hd_q complete_u by simp
    have last_q: "last ?q = z"
    proof -
      have len_q: "length ?q = Suc i"
        using i_p by simp
      have "last ?q = ?q ! i"
        using len_q last_conv_nth[OF q_nonempty] by simp
      also have "\<dots> = z"
        using p_i i_p by simp
      finally show ?thesis .
    qed
    have tight_q: "successively tight_edge_step ?q"
      using successively_take[OF tight, of "Suc i"] .
    have below_q: "\<And>y. y \<in> set ?q \<Longrightarrow> below_bound (dist s y) B"
    proof -
      fix y
      assume yq: "y \<in> set ?q"
      have "set ?q \<subseteq> set (take k p)"
        using i_k set_take_subset_set_take[of "Suc i" k p] by auto
      then show "below_bound (dist s y) B"
        using below_prefix yq by blast
    qed
    have len_q: "length (path_edges ?q) \<le> k"
    proof -
      have "length (path_edges ?q) = length ?q - 1"
        by (rule path_edges_length)
      also have "\<dots> = i"
        using i_p by simp
      also have "\<dots> \<le> k"
        using i_k by simp
      finally show ?thesis .
    qed
    have "last ?q \<in> find_pivots_seen k d S B"
      using find_pivots_short_tight_path_complete(2)
        [OF sound S_reaches q_nonempty hd_q_S complete_hd_q tight_q below_q len_q] .
    then show "z \<in> find_pivots_seen k d S B"
      using last_q by simp
  qed
qed

lemma find_pivots_long_tree_suffix_root_pivot:
  assumes sound: "sound_label d"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and reach_v: "reachable s v"
    and below_v: "below_bound (dist s v) B"
    and i: "i < length (shortest_path_to v)"
    and source_in_S: "shortest_path_to v ! i \<in> S"
    and source_complete: "d (shortest_path_to v ! i) = dist s (shortest_path_to v ! i)"
    and long: "k \<le> length (drop i (shortest_path_to v))"
    and tree_prefix:
      "set (take k (drop i (shortest_path_to v))) \<subseteq>
        tree_of (shortest_path_to v ! i)"
  shows "shortest_path_to v ! i \<in> find_pivots_pivots k d S B"
proof -
  let ?p = "shortest_path_to v"
  let ?q = "drop i ?p"
  let ?u = "?p ! i"
  have sp: "shortest_walk s ?p v"
    using shortest_path_to_shortest[OF reach_v] .
  have simple_p: "simple_walk_betw s ?p v"
    using sp unfolding shortest_walk_def by blast
  have distinct_p: "distinct ?p"
    using simple_p unfolding simple_walk_betw_def by blast
  have distinct_q: "distinct ?q"
    using distinct_p by simp
  have q_nonempty: "?q \<noteq> []"
    using i by auto
  have hd_q: "hd ?q = ?u"
    using i by (simp add: hd_drop_conv_nth)
  have tight_q: "successively tight_edge_step ?q"
    using successively_drop[OF shortest_path_to_successively_tight[OF reach_v], of i] .
  have below_prefix: "\<And>x. x \<in> set (take k ?q) \<Longrightarrow> below_bound (dist s x) B"
  proof -
    fix x
    assume x_take: "x \<in> set (take k ?q)"
    have xq: "x \<in> set ?q"
      using x_take by (meson in_set_takeD)
    have "x \<in> set ?p"
      using in_set_dropD[OF xq] .
    then have "tree_path x v"
      using reach_v unfolding tree_path_def by blast
    then have "dist s x \<le> dist s v"
      by (rule tree_path_dist_le)
    then show "below_bound (dist s x) B"
      using below_bound_le_trans[OF _ below_v] by blast
  qed
  show ?thesis
    using find_pivots_long_tight_path_root_pivot
      [OF sound S_reaches source_in_S source_complete q_nonempty hd_q
        distinct_q long tight_q below_prefix tree_prefix] .
qed

corollary find_pivots_one_tight_step_complete:
  assumes sound: "sound_label d"
    and uS: "u \<in> S"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and complete_u: "d u = dist s u"
    and tight: "tight_edge_step u v"
    and below_v: "below_bound (dist s v) B"
  shows "find_pivots_label (Suc n) d S B v = dist s v"
    and "v \<in> find_pivots_seen (Suc n) d S B"
  using fp_iter_one_tight_step_completion
    [OF sound uS S_reaches complete_u tight below_v, of n S]
  unfolding find_pivots_label_def find_pivots_seen_def by auto

theorem find_pivots_covers_bound_tree_complete_sources:
  assumes sound: "sound_label d"
    and S_complete: "complete_on d S"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and v_bound: "v \<in> bound_tree S B"
  shows
    "(find_pivots_label k d S B v = dist s v \<and>
      v \<in> find_pivots_seen k d S B) \<or>
     through_complete (find_pivots_label k d S B)
       (find_pivots_pivots k d S B) v"
proof -
  let ?p = "shortest_path_to v"
  let ?d' = "find_pivots_label k d S B"
  let ?P = "find_pivots_pivots k d S B"
  have reach_v: "reachable s v"
    and through_S: "through S v"
    and below_v: "below_bound (dist s v) B"
    using v_bound unfolding bound_tree_def by auto
  obtain u where uS: "u \<in> S" and tree_uv: "tree_path u v"
    using through_iff_tree_path[OF reach_v, of S] through_S by blast
  then have u_in_path: "u \<in> set ?p"
    by (auto dest: tree_pathD)
  have sp_v: "shortest_walk s ?p v"
    using shortest_path_to_shortest[OF reach_v] .
  have uV: "u \<in> V"
  proof -
    have "walk ?p"
      using sp_v unfolding shortest_walk_def simple_walk_betw_def walk_betw_def by blast
    then show ?thesis
      using u_in_path walk_set_subset by blast
  qed
  obtain i where i: "i < length ?p" "?p ! i = u"
    using u_in_path by (auto simp: in_set_conv_nth)
  have complete_u: "d u = dist s u"
    using S_complete S_reaches[OF uS] uS unfolding complete_on_def by blast
  have source_in: "?p ! i \<in> S"
    using i(2) uS by simp
  have source_complete: "d (?p ! i) = dist s (?p ! i)"
    using i(2) complete_u by simp

  show ?thesis
  proof (cases "length (path_edges (drop i ?p)) \<le> k")
    case True
    have complete_v: "?d' v = dist s v"
      by (rule find_pivots_completes_short_tree_suffix(1)
          [OF sound S_reaches reach_v below_v i(1) source_in source_complete True])
    have seen_v: "v \<in> find_pivots_seen k d S B"
      by (rule find_pivots_completes_short_tree_suffix(2)
          [OF sound S_reaches reach_v below_v i(1) source_in source_complete True])
    then show ?thesis
      using complete_v by blast
  next
    case False
    let ?q = "drop i ?p"
    have q_nonempty: "?q \<noteq> []"
      using i(1) by auto
    have long: "k \<le> length ?q"
    proof -
      have "k < length (path_edges ?q)"
        using False by simp
      also have "\<dots> = length ?q - 1"
        by (rule path_edges_length)
      finally show ?thesis
        by linarith
    qed
    have source_tree_prefix:
      "set (take k ?q) \<subseteq> tree_of (?p ! i)"
      using tree_prefix_of_shortest_path_suffix[OF reach_v i(1), of k] .
    have source_pivot: "?p ! i \<in> ?P"
      by (rule find_pivots_long_tree_suffix_root_pivot
          [OF sound S_reaches reach_v below_v i(1) source_in source_complete long
            source_tree_prefix])
    have u_pivot: "u \<in> ?P"
      using source_pivot i(2) by simp
    have complete_u_after: "?d' u = dist s u"
      unfolding find_pivots_label_def
      by (rule fp_iter_preserves_complete_sound[OF sound complete_u S_reaches])
    have u_complete_vertex: "u \<in> complete_vertices ?d'"
      using uV S_reaches[OF uS] complete_u_after
      unfolding complete_vertices_def by blast
    have "through (?P \<inter> complete_vertices ?d') v"
      using u_pivot u_complete_vertex sp_v u_in_path unfolding through_def by blast
    then show ?thesis
      unfolding through_complete_def by blast
  qed
qed

theorem find_pivots_post_complete_sources:
  assumes sound: "sound_label d"
    and S_subset: "S \<subseteq> V"
    and S_complete: "complete_on d S"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "find_pivots_post d S B
    (find_pivots_label k d S B)
    (find_pivots_pivots k d S B)
    {v \<in> bound_tree S B. find_pivots_label k d S B v = dist s v}"
proof -
  let ?d' = "find_pivots_label k d S B"
  let ?P = "find_pivots_pivots k d S B"
  let ?W = "{v \<in> bound_tree S B. ?d' v = dist s v}"
  have P_subset: "?P \<subseteq> S"
    unfolding find_pivots_pivots_def by blast
  have W_subset: "?W \<subseteq> bound_tree S B"
    by blast
  have complete_W: "complete_on ?d' ?W"
    unfolding complete_on_def by blast
  have preserve:
    "\<forall>v\<in>V. reachable s v \<longrightarrow> below_bound (dist s v) B \<longrightarrow>
      d v = dist s v \<longrightarrow> ?d' v = dist s v"
  proof clarify
    fix v
    assume v_complete: "d v = dist s v"
    show "?d' v = dist s v"
      unfolding find_pivots_label_def
      by (rule fp_iter_preserves_complete_sound[OF sound v_complete S_reaches])
  qed
  have cover: "\<forall>v\<in>bound_tree S B. v \<in> ?W \<or> through_complete ?d' ?P v"
  proof
    fix v
    assume v: "v \<in> bound_tree S B"
    have cov:
      "(?d' v = dist s v \<and> v \<in> find_pivots_seen k d S B) \<or>
       through_complete ?d' ?P v"
      using find_pivots_covers_bound_tree_complete_sources
        [OF sound S_complete S_reaches v]
      .
    then show "v \<in> ?W \<or> through_complete ?d' ?P v"
      using v by blast
  qed
  show ?thesis
    using S_subset P_subset W_subset complete_W preserve cover
    unfolding find_pivots_post_def by blast
qed

theorem find_pivots_establishes_pivot_pre_concrete:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "bmssp_pre_full
    (find_pivots_label k d S B)
    (find_pivots_pivots k d S B) B"
proof -
  let ?d' = "find_pivots_label k d S B"
  let ?P = "find_pivots_pivots k d S B"
  have P_subset_S: "?P \<subseteq> S"
    unfolding find_pivots_pivots_def by blast
  have P_subset_V: "?P \<subseteq> V"
    using P_subset_S pre unfolding bmssp_pre_full_def by blast
  have preserve_complete: "\<And>x. d x = dist s x \<Longrightarrow> ?d' x = dist s x"
    unfolding find_pivots_label_def
    by (rule fp_iter_preserves_complete_sound[OF sound _ S_reaches])
  have cover:
    "\<And>v. \<lbrakk>v \<in> V; reachable s v; below_bound (dist s v) B;
       ?d' v \<noteq> dist s v\<rbrakk> \<Longrightarrow> through_complete ?d' ?P v"
  proof -
    fix v
    assume vV: "v \<in> V"
      and reach_v: "reachable s v"
      and below_v: "below_bound (dist s v) B"
      and d'_incomplete: "?d' v \<noteq> dist s v"
    have d_incomplete: "d v \<noteq> dist s v"
    proof
      assume "d v = dist s v"
      then have "?d' v = dist s v"
        by (rule preserve_complete)
      with d'_incomplete show False
        by simp
    qed
    have through_comp: "through_complete d S v"
      using pre vV reach_v below_v d_incomplete
      unfolding bmssp_pre_full_def by blast
    obtain u p where uS: "u \<in> S" and ucomp: "u \<in> complete_vertices d"
      and sp: "shortest_walk s p v" and u_in_p: "u \<in> set p"
      using through_comp unfolding through_complete_def through_def by blast
    let ?p = "shortest_path_to v"
    have sp_canon: "shortest_walk s ?p v"
      using shortest_path_to_shortest[OF reach_v] .
    have p_eq: "p = ?p"
      using unique_shortest_walk[OF sp sp_canon] .
    have u_in_path: "u \<in> set ?p"
      using u_in_p p_eq by simp
    obtain i where i: "i < length ?p" "?p ! i = u"
      using u_in_path by (auto simp: in_set_conv_nth)
    have complete_u: "d u = dist s u"
      using ucomp unfolding complete_vertices_def by blast
    have source_in: "?p ! i \<in> S"
      using i(2) uS by simp
    have source_complete: "d (?p ! i) = dist s (?p ! i)"
      using i(2) complete_u by simp

    show "through_complete ?d' ?P v"
    proof (cases "length (path_edges (drop i ?p)) \<le> k")
      case True
      have "?d' v = dist s v"
        by (rule find_pivots_completes_short_tree_suffix(1)
            [OF sound S_reaches reach_v below_v i(1) source_in source_complete True])
      with d'_incomplete have False
        by simp
      then show ?thesis
        by blast
    next
      case False
      let ?q = "drop i ?p"
      have long: "k \<le> length ?q"
      proof -
        have "k < length (path_edges ?q)"
          using False by simp
        also have "\<dots> = length ?q - 1"
          by (rule path_edges_length)
        finally show ?thesis
          by linarith
      qed
      have source_tree_prefix:
        "set (take k ?q) \<subseteq> tree_of (?p ! i)"
        using tree_prefix_of_shortest_path_suffix[OF reach_v i(1), of k] .
      have source_pivot: "?p ! i \<in> ?P"
        by (rule find_pivots_long_tree_suffix_root_pivot
            [OF sound S_reaches reach_v below_v i(1) source_in source_complete long
              source_tree_prefix])
      have u_pivot: "u \<in> ?P"
        using source_pivot i(2) by simp
      have uV: "u \<in> V" and reach_u: "reachable s u"
        using ucomp unfolding complete_vertices_def by auto
      have complete_u_after: "?d' u = dist s u"
        by (rule preserve_complete[OF complete_u])
      have u_complete_after: "u \<in> complete_vertices ?d'"
        using uV reach_u complete_u_after unfolding complete_vertices_def by blast
      have "through (?P \<inter> complete_vertices ?d') v"
        using u_pivot u_complete_after sp_canon u_in_path unfolding through_def by blast
      then show ?thesis
        unfolding through_complete_def .
    qed
  qed
  show ?thesis
    using P_subset_V cover unfolding bmssp_pre_full_def by blast
qed

theorem find_pivots_post_from_pre_concrete:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "find_pivots_post d S B
    (find_pivots_label k d S B)
    (find_pivots_pivots k d S B)
    {v \<in> bound_tree S B. find_pivots_label k d S B v = dist s v}"
proof -
  let ?d' = "find_pivots_label k d S B"
  let ?P = "find_pivots_pivots k d S B"
  let ?W = "{v \<in> bound_tree S B. ?d' v = dist s v}"
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have P_subset: "?P \<subseteq> S"
    unfolding find_pivots_pivots_def by blast
  have W_subset: "?W \<subseteq> bound_tree S B"
    by blast
  have complete_W: "complete_on ?d' ?W"
    unfolding complete_on_def by blast
  have preserve:
    "\<forall>v\<in>V. reachable s v \<longrightarrow> below_bound (dist s v) B \<longrightarrow>
      d v = dist s v \<longrightarrow> ?d' v = dist s v"
  proof clarify
    fix v
    assume complete_v: "d v = dist s v"
    show "?d' v = dist s v"
      unfolding find_pivots_label_def
      by (rule fp_iter_preserves_complete_sound[OF sound complete_v S_reaches])
  qed
  have pivot_pre: "bmssp_pre_full ?d' ?P B"
    by (rule find_pivots_establishes_pivot_pre_concrete
      [OF sound pre S_reaches])
  have cover: "\<forall>v\<in>bound_tree S B. v \<in> ?W \<or> through_complete ?d' ?P v"
  proof
    fix v
    assume v_bound: "v \<in> bound_tree S B"
    show "v \<in> ?W \<or> through_complete ?d' ?P v"
    proof (cases "?d' v = dist s v")
      case True
      then show ?thesis
        using v_bound by blast
    next
      case False
      have vV: "v \<in> V" and reach_v: "reachable s v"
        and below_v: "below_bound (dist s v) B"
        using v_bound unfolding bound_tree_def by auto
      have "through_complete ?d' ?P v"
        using pivot_pre vV reach_v below_v False
        unfolding bmssp_pre_full_def by blast
      then show ?thesis
        by blast
    qed
  qed
  show ?thesis
    using S_subset P_subset W_subset complete_W preserve cover
    unfolding find_pivots_post_def by blast
qed

theorem find_pivots_capped_no_overflow_establishes_pre:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and no_overflow: "\<not> card (find_pivots_seen_capped k cap d S B) > cap"
  shows "bmssp_pre_full
    (find_pivots_label_capped k cap d S B)
    (find_pivots_pivots_capped k cap d S B) B"
proof -
  have cap_le: "card (find_pivots_seen_capped k cap d S B) \<le> cap"
    using no_overflow by simp
  have iter_eq: "fp_iter_capped k cap d S S B = fp_iter k d S S B"
    using fp_iter_capped_eq_fp_iter_if_final_within_cap[of k cap d S S B]
      cap_le unfolding find_pivots_seen_capped_def by simp
  have label_eq: "find_pivots_label_capped k cap d S B = find_pivots_label k d S B"
    using iter_eq unfolding find_pivots_label_capped_def find_pivots_label_def by simp
  have seen_eq: "find_pivots_seen_capped k cap d S B = find_pivots_seen k d S B"
    using iter_eq unfolding find_pivots_seen_capped_def find_pivots_seen_def by simp
  have pivots_eq:
    "find_pivots_pivots_capped k cap d S B = find_pivots_pivots k d S B"
    using no_overflow seen_eq
    unfolding find_pivots_pivots_capped_def find_pivots_pivots_def by simp
  show ?thesis
    using find_pivots_establishes_pivot_pre_concrete[OF sound pre S_reaches]
    unfolding label_eq pivots_eq .
qed

theorem find_pivots_capped_establishes_pivot_pre_concrete:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "bmssp_pre_full
    (find_pivots_label_capped k cap d S B)
    (find_pivots_pivots_capped k cap d S B) B"
proof (cases "card (find_pivots_seen_capped k cap d S B) > cap")
  case True
  show ?thesis
    by (rule find_pivots_capped_overflow_establishes_pre[OF sound pre S_reaches True])
next
  case False
  show ?thesis
    by (rule find_pivots_capped_no_overflow_establishes_pre[OF sound pre S_reaches False])
qed

text \<open>
  The capped variant has two proof branches but one external contract.  If the
  cap overflows, the paper keeps the original source set as the pivot set; the
  existing BMSSP precondition is therefore preserved.  If it does not overflow,
  @{thm fp_iter_capped_eq_fp_iter_if_final_within_cap} identifies the capped
  execution with the uncapped one, so the pivot-precondition proof can reuse
  the short-path completeness argument.  The theorem above hides that case
  split and exposes a single @{const bmssp_pre_full} fact for the capped
  labels and @{const find_pivots_pivots_capped}.
\<close>

theorem find_pivots_capped_post_from_pre_concrete:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "find_pivots_post d S B
    (find_pivots_label_capped k cap d S B)
    (find_pivots_pivots_capped k cap d S B)
    {v \<in> bound_tree S B.
      find_pivots_label_capped k cap d S B v = dist s v}"
proof -
  let ?d' = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  let ?W = "{v \<in> bound_tree S B. ?d' v = dist s v}"
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have P_subset: "?P \<subseteq> S"
    unfolding find_pivots_pivots_capped_def by auto
  have W_subset: "?W \<subseteq> bound_tree S B"
    by blast
  have complete_W: "complete_on ?d' ?W"
    unfolding complete_on_def by blast
  have preserve:
    "\<forall>v\<in>V. reachable s v \<longrightarrow> below_bound (dist s v) B \<longrightarrow>
      d v = dist s v \<longrightarrow> ?d' v = dist s v"
  proof clarify
    fix v
    assume complete_v: "d v = dist s v"
    show "?d' v = dist s v"
      unfolding find_pivots_label_capped_def
      by (rule fp_iter_capped_preserves_complete_sound
        [OF sound complete_v S_reaches])
  qed
  have pivot_pre: "bmssp_pre_full ?d' ?P B"
    by (rule find_pivots_capped_establishes_pivot_pre_concrete
      [OF sound pre S_reaches])
  have cover: "\<forall>v\<in>bound_tree S B. v \<in> ?W \<or> through_complete ?d' ?P v"
  proof
    fix v
    assume v_bound: "v \<in> bound_tree S B"
    show "v \<in> ?W \<or> through_complete ?d' ?P v"
    proof (cases "?d' v = dist s v")
      case True
      then show ?thesis
        using v_bound by blast
    next
      case False
      have vV: "v \<in> V" and reach_v: "reachable s v"
        and below_v: "below_bound (dist s v) B"
        using v_bound unfolding bound_tree_def by auto
      have "through_complete ?d' ?P v"
        using pivot_pre vV reach_v below_v False
        unfolding bmssp_pre_full_def by blast
      then show ?thesis
        by blast
    qed
  qed
  show ?thesis
    using S_subset P_subset W_subset complete_W preserve cover
    unfolding find_pivots_post_def by blast
qed

end

end
