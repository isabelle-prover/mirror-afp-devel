theory BMSSP_Code_Export
  imports BMSSP_Bucketed_Partition
begin

section \<open>Executable Bucketed BMSSP Smoke Test\<close>

text \<open>
  This theory gives the development an executable surface.  All preceding
  imported theory proves the paper-faithful bucketed operation costs and the
  concrete partition API.  Those facts are essential, but they do not by
  themselves show a human reader that the formalized program can be run on an
  ordinary graph.  The purpose of this file is to close that gap with a small
  concrete instantiation and a proof by evaluation.

  The executable graph representation is deliberately plain: vertices are
  natural numbers, edges are triples of natural numbers, and distances are
  association lists sorted by vertex at the end of the run.  The work-list is
  the paper-style bucketed partition structure imported from the bucketed
  theory, not the baseline sorted-list partition model.  The loop below uses
  Pull to obtain the next bucket of unsettled vertices, relaxes outgoing edges
  from that batch, and feeds discovered or improved labels through
  BatchPrepend for an empty partition and Insert otherwise.  This shape is
  chosen to exercise all three bucketed operations in the worked example.

  The fuel argument is an executable guard, not part of the mathematical
  correctness theorem.  For the small smoke graph it is chosen large enough to
  allow all relaxations needed by the hand calculation.  The checked statement
  at the bottom is the important artifact: \<open>example_bmssp_correct\<close> is proved
  by Isabelle's evaluator, so the bundled Poly/ML runtime executes the exported
  equations during the build and compares the result with the literal expected
  distance map.
\<close>

type_synonym nat_edge = "nat \<times> nat \<times> nat"
type_synonym nat_graph = "nat_edge list"
type_synonym nat_dist = "(nat \<times> nat) list"

definition bmssp_block_size :: nat where
  "bmssp_block_size = 1"

definition bmssp_infinity :: nat where
  "bmssp_infinity = 1000000"

definition bmssp_bound :: real where
  "bmssp_bound = real bmssp_infinity"

fun bmssp_edge_vertices :: "nat_edge \<Rightarrow> nat list" where
  "bmssp_edge_vertices (u, v, w) = [u, v]"

definition bmssp_vertices :: "nat_graph \<Rightarrow> nat \<Rightarrow> nat list" where
  "bmssp_vertices G s = sort (remdups (s # concat (map bmssp_edge_vertices G)))"

fun bmssp_lookup_dist :: "nat_dist \<Rightarrow> nat \<Rightarrow> nat option" where
  "bmssp_lookup_dist [] x = None"
| "bmssp_lookup_dist ((y, d) # ds) x =
     (if x = y then Some d else bmssp_lookup_dist ds x)"

fun bmssp_set_dist :: "nat \<Rightarrow> nat \<Rightarrow> nat_dist \<Rightarrow> nat_dist" where
  "bmssp_set_dist x d [] = [(x, d)]"
| "bmssp_set_dist x d ((y, e) # ds) =
     (if x = y then (x, d) # ds else (y, e) # bmssp_set_dist x d ds)"

definition bmssp_normalize_dist :: "nat_dist \<Rightarrow> nat_dist" where
  "bmssp_normalize_dist ds = sort_key fst ds"

definition bmssp_partition_key :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "bmssp_partition_key x d = real d + real x / real (Suc x)"

lemma bmssp_partition_key_fraction_nonneg:
  "0 \<le> real x / real (Suc x)"
  by simp

lemma bmssp_partition_key_fraction_lt_one:
  "real x / real (Suc x) < 1"
proof -
  have "real x < real (Suc x)"
    by simp
  then show ?thesis
    by (simp add: divide_less_eq)
qed

lemma bmssp_partition_key_ge_distance:
  "real d \<le> bmssp_partition_key x d"
  unfolding bmssp_partition_key_def by simp

lemma bmssp_partition_key_lt_suc_distance:
  "bmssp_partition_key x d < real (Suc d)"
proof -
  have frac_lt: "real x / real (Suc x) < 1"
    by (rule bmssp_partition_key_fraction_lt_one)
  have "bmssp_partition_key x d < real d + 1"
    unfolding bmssp_partition_key_def using frac_lt by linarith
  then show ?thesis
    by simp
qed

lemma bmssp_partition_key_floor:
  "nat (floor (bmssp_partition_key x d)) = d"
proof (rule floor_eq4)
  show "real d \<le> bmssp_partition_key x d"
    by (rule bmssp_partition_key_ge_distance)
  show "bmssp_partition_key x d < real (Suc d)"
    by (rule bmssp_partition_key_lt_suc_distance)
qed

lemma bmssp_partition_key_strict_mono_distance:
  assumes "d < e"
  shows "bmssp_partition_key x d < bmssp_partition_key y e"
proof -
  have "bmssp_partition_key x d < real (Suc d)"
    by (rule bmssp_partition_key_lt_suc_distance)
  also have "\<dots> \<le> real e"
    using assms by simp
  also have "\<dots> \<le> bmssp_partition_key y e"
    by (rule bmssp_partition_key_ge_distance)
  finally show ?thesis .
qed

fun bmssp_insert_updates ::
  "(nat \<times> real) list \<Rightarrow> nat bucketed_partition \<Rightarrow>
    nat bucketed_partition" where
  "bmssp_insert_updates [] P = P"
| "bmssp_insert_updates ((x, b) # xs) P =
     bmssp_insert_updates xs
       (bp_result_of (c_bp_regularized_local_insert x b P))"

lemma bmssp_insert_updates_regular_invariant:
  assumes "bp_regular_invariant P"
  shows "bp_regular_invariant (bmssp_insert_updates xs P)"
  using assms
proof (induction xs arbitrary: P)
  case Nil
  then show ?case by simp
next
  case (Cons p xs)
  then obtain x b where p: "p = (x, b)"
    by force
  have step:
    "bp_regular_invariant
      (bp_result_of (c_bp_regularized_local_insert x b P))"
    by (rule c_bp_regularized_local_insert_regular_invariant[OF Cons.prems])
  show ?case
    unfolding p bmssp_insert_updates.simps
    by (rule Cons.IH[OF step])
qed

lemma bmssp_insert_updates_ordered_invariant:
  assumes "bp_regular_invariant P"
  shows "bp_ordered_invariant (bmssp_insert_updates xs P)"
  using bp_regular_invariant_ordered_invariant
    [OF bmssp_insert_updates_regular_invariant[OF assms]]
  .

lemma bmssp_insert_updates_refines_batch_min_update:
  assumes reg: "bp_regular_invariant P"
  shows "bp_view (bmssp_insert_updates xs P) =
    batch_min_update (bp_view P) xs"
  using reg
proof (induction xs arbitrary: P)
  case Nil
  then show ?case
    unfolding batch_min_update_def by simp
next
  case (Cons p xs)
  then obtain x b where p: "p = (x, b)"
    by force
  let ?P1 = "bp_result_of (c_bp_regularized_local_insert x b P)"
  have step_reg: "bp_regular_invariant ?P1"
    by (rule c_bp_regularized_local_insert_regular_invariant[OF Cons.prems])
  have step_view: "bp_view ?P1 = min_update (bp_view P) x b"
    by (rule c_bp_regularized_local_insert_refines_min_update[OF Cons.prems])
  have tail:
    "bp_view (bmssp_insert_updates xs ?P1) =
      batch_min_update (bp_view ?P1) xs"
    by (rule Cons.IH[OF step_reg])
  have head:
    "batch_min_update (bp_view P) ((x, b) # xs) =
      batch_min_update (min_update (bp_view P) x b) xs"
    unfolding batch_min_update_def by simp
  show ?case
    unfolding p bmssp_insert_updates.simps
    using tail step_view head by simp
qed

lemma bmssp_insert_updates_ordered_invariant_from_ordered:
  assumes ord: "bp_ordered_invariant P"
  shows "bp_ordered_invariant (bmssp_insert_updates xs P)"
proof (cases xs)
  case Nil
  then show ?thesis
    using ord by simp
next
  case (Cons p ys)
  then obtain x b where p: "p = (x, b)"
    by force
  let ?P1 = "bp_result_of (c_bp_regularized_local_insert x b P)"
  have step_reg: "bp_regular_invariant ?P1"
    unfolding c_bp_regularized_local_insert_result
    by (rule bp_regularized_local_insert_regular_invariant[OF ord])
  have tail_ord: "bp_ordered_invariant (bmssp_insert_updates ys ?P1)"
    by (rule bmssp_insert_updates_ordered_invariant[OF step_reg])
  show ?thesis
    unfolding Cons p bmssp_insert_updates.simps
    by (rule tail_ord)
qed

lemma bmssp_insert_updates_refines_batch_min_update_from_ordered:
  assumes ord: "bp_ordered_invariant P"
  shows "bp_view (bmssp_insert_updates xs P) =
    batch_min_update (bp_view P) xs"
proof (cases xs)
  case Nil
  then show ?thesis
    unfolding batch_min_update_def by simp
next
  case (Cons p ys)
  then obtain x b where p: "p = (x, b)"
    by force
  let ?P1 = "bp_result_of (c_bp_regularized_local_insert x b P)"
  have step_reg: "bp_regular_invariant ?P1"
    unfolding c_bp_regularized_local_insert_result
    by (rule bp_regularized_local_insert_regular_invariant[OF ord])
  have step_view: "bp_view ?P1 = min_update (bp_view P) x b"
    unfolding c_bp_regularized_local_insert_result
    by (rule bp_regularized_local_insert_refines_min_update[OF ord])
  have tail:
    "bp_view (bmssp_insert_updates ys ?P1) =
      batch_min_update (bp_view ?P1) ys"
    by (rule bmssp_insert_updates_refines_batch_min_update[OF step_reg])
  have head:
    "batch_min_update (bp_view P) ((x, b) # ys) =
      batch_min_update (min_update (bp_view P) x b) ys"
    unfolding batch_min_update_def by simp
  show ?thesis
    unfolding Cons p bmssp_insert_updates.simps
    using tail step_view head by simp
qed

definition bmssp_trim_empty_prefix ::
  "nat bucketed_partition \<Rightarrow> nat bucketed_partition" where
  "bmssp_trim_empty_prefix P =
     P\<lparr>bp_buckets := bp_drop_empty_prefix (bp_buckets P)\<rparr>"

lemma bp_bucket_entries_flat_drop_empty_prefix [simp]:
  "bp_bucket_entries_flat (bp_drop_empty_prefix bs) =
    bp_bucket_entries_flat bs"
  by (induction bs) (simp_all add: bp_bucket_entries_flat_def)

lemma bp_drop_empty_prefix_set_subset:
  "set (bp_drop_empty_prefix bs) \<subseteq> set bs"
  by (induction bs) auto

lemma bp_drop_empty_prefix_length_le [simp]:
  "length (bp_drop_empty_prefix bs) \<le> length bs"
proof (induction bs)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  show ?case
  proof (cases "bp_bucket_entries b = []")
    case True
    have "length (bp_drop_empty_prefix bs) \<le> Suc (length bs)"
      using Cons.IH by linarith
    then show ?thesis
      using True by simp
  next
    case False
    then show ?thesis by simp
  qed
qed

lemma bp_drop_empty_prefix_sorted_wrt:
  assumes "sorted_wrt R bs"
  shows "sorted_wrt R (bp_drop_empty_prefix bs)"
  using assms
  by (induction bs) auto

lemma bp_bucket_boundaries_ok_drop_empty_prefix:
  assumes "bp_bucket_boundaries_ok bs"
  shows "bp_bucket_boundaries_ok (bp_drop_empty_prefix bs)"
  using assms
proof (induction bs)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  show ?case
  proof (cases "bp_bucket_entries b = []")
    case True
    have "bp_bucket_boundaries_ok bs"
      using Cons.prems by (cases bs) auto
    then show ?thesis
      using True Cons.IH by simp
  next
    case False
    then show ?thesis
      using Cons.prems by simp
  qed
qed

lemma bmssp_trim_empty_prefix_entries [simp]:
  "bp_entries (bmssp_trim_empty_prefix P) = bp_entries P"
  unfolding bmssp_trim_empty_prefix_def bp_entries_def by simp

lemma bmssp_trim_empty_prefix_view [simp]:
  "bp_view (bmssp_trim_empty_prefix P) = bp_view P"
  unfolding bmssp_trim_empty_prefix_def bp_view_def bp_entries_def by simp

lemma bmssp_trim_empty_prefix_ordered_invariant:
  assumes "bp_ordered_invariant P"
  shows "bp_ordered_invariant (bmssp_trim_empty_prefix P)"
proof -
  have inv: "bp_invariant P"
    using assms unfolding bp_ordered_invariant_def by blast
  have boundaries: "bp_bucket_boundaries_state_ok P"
    using assms unfolding bp_ordered_invariant_def by blast
  have set_subset:
    "set (bp_buckets (bmssp_trim_empty_prefix P)) \<subseteq> set (bp_buckets P)"
    unfolding bmssp_trim_empty_prefix_def
    by (simp add: bp_drop_empty_prefix_set_subset)
  have "bp_invariant (bmssp_trim_empty_prefix P)"
  proof -
    have "0 < bp_block_size (bmssp_trim_empty_prefix P)"
      using inv unfolding bmssp_trim_empty_prefix_def bp_invariant_def by simp
    moreover have "bp_distinct_keys (bmssp_trim_empty_prefix P)"
      using inv unfolding bp_invariant_def bp_distinct_keys_def by simp
    moreover have "bp_bucket_sizes_ok (bmssp_trim_empty_prefix P)"
    proof (unfold bp_bucket_sizes_ok_def, intro ballI)
      fix b
      assume b: "b \<in> set (bp_buckets (bmssp_trim_empty_prefix P))"
      then have "b \<in> set (bp_buckets P)"
        using set_subset by blast
      then have "length (bp_bucket_entries b) \<le> bp_block_size P"
        using inv unfolding bp_invariant_def bp_bucket_sizes_ok_def by blast
      then show "length (bp_bucket_entries b) \<le>
        bp_block_size (bmssp_trim_empty_prefix P)"
        unfolding bmssp_trim_empty_prefix_def by simp
    qed
    moreover have "bp_bucket_markers_sorted (bmssp_trim_empty_prefix P)"
      using inv
      unfolding bmssp_trim_empty_prefix_def bp_invariant_def
        bp_bucket_markers_sorted_def
      by (simp add: bp_drop_empty_prefix_sorted_wrt)
    moreover have "bp_bucket_markers_lower_bound (bmssp_trim_empty_prefix P)"
      using inv set_subset
      unfolding bp_invariant_def bp_bucket_markers_lower_bound_def by auto
    moreover have "bp_values_consistent (bmssp_trim_empty_prefix P)"
      using inv
      unfolding bmssp_trim_empty_prefix_def bp_invariant_def
        bp_values_consistent_def bp_entries_def
      by simp
    ultimately show ?thesis
      unfolding bp_invariant_def by blast
  qed
  moreover have "bp_bucket_boundaries_state_ok (bmssp_trim_empty_prefix P)"
    using boundaries
    unfolding bmssp_trim_empty_prefix_def bp_bucket_boundaries_state_ok_def
    by (simp add: bp_bucket_boundaries_ok_drop_empty_prefix)
  ultimately show ?thesis
    unfolding bp_ordered_invariant_def by blast
qed

lemma bmssp_trim_empty_prefix_regular_invariant:
  assumes "bp_regular_invariant P"
  shows "bp_regular_invariant (bmssp_trim_empty_prefix P)"
proof -
  have ordered: "bp_ordered_invariant P"
    by (rule bp_regular_invariant_ordered_invariant[OF assms])
  have ratio: "bp_bucket_count_ratio_ok P"
    by (rule bp_regular_invariant_ratio_ok[OF assms])
  have "bp_bucket_count_ratio_ok (bmssp_trim_empty_prefix P)"
  proof -
    have len_le:
      "length (bp_drop_empty_prefix (bp_buckets P)) \<le> length (bp_buckets P)"
      by (rule bp_drop_empty_prefix_length_le)
    have block_pos: "0 < bp_block_size P"
      using ratio unfolding bp_bucket_count_ratio_ok_def by blast
    have orig_len:
      "length (bp_buckets P) \<le>
        Suc (length (bp_entries P) div bp_block_size P)"
      using ratio unfolding bp_bucket_count_ratio_ok_def by blast
    have drop_len:
      "length (bp_drop_empty_prefix (bp_buckets P)) \<le>
        Suc (length (bp_entries P) div bp_block_size P)"
      using len_le orig_len by (rule order_trans)
    show ?thesis
      using block_pos drop_len
      unfolding bmssp_trim_empty_prefix_def bp_bucket_count_ratio_ok_def
        bp_entries_def
      by simp
  qed
  then show ?thesis
    using bmssp_trim_empty_prefix_ordered_invariant[OF ordered]
    unfolding bp_regular_invariant_def by blast
qed

definition bmssp_apply_updates ::
  "(nat \<times> real) list \<Rightarrow> nat bucketed_partition \<Rightarrow>
    nat bucketed_partition" where
  "bmssp_apply_updates xs P =
     (let P0 = bmssp_trim_empty_prefix P in
      if bp_entries P0 = []
      then bp_result_of (c_bp_paper_batch_prepend xs P0)
      else bmssp_insert_updates xs P0)"

lemma bmssp_apply_updates_refines_batch_min_update:
  assumes reg: "bp_regular_invariant P"
    and distinct: "distinct (map fst xs)"
  shows "bp_view (bmssp_apply_updates xs P) =
    batch_min_update (bp_view P) xs"
proof -
  let ?P0 = "bmssp_trim_empty_prefix P"
  have reg0: "bp_regular_invariant ?P0"
    by (rule bmssp_trim_empty_prefix_regular_invariant[OF reg])
  have ord0: "bp_ordered_invariant ?P0"
    by (rule bp_regular_invariant_ordered_invariant[OF reg0])
  show ?thesis
  proof (cases "bp_entries ?P0 = []")
    case True
    have disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view ?P0) = {}"
      using True unfolding bp_view_def bp_entry_keys_def by simp
    have "bp_view (bp_result_of (c_bp_paper_batch_prepend xs ?P0)) =
      batch_min_update (bp_view ?P0) xs"
      by (rule c_bp_paper_batch_prepend_refines_batch_min_update
          [OF ord0 distinct disjoint])
    then show ?thesis
      using True unfolding bmssp_apply_updates_def by simp
  next
    case False
    have "bp_view (bmssp_insert_updates xs ?P0) =
      batch_min_update (bp_view ?P0) xs"
      by (rule bmssp_insert_updates_refines_batch_min_update[OF reg0])
    then show ?thesis
      using False unfolding bmssp_apply_updates_def by simp
  qed
qed

lemma bmssp_apply_updates_ordered_invariant:
  assumes reg: "bp_regular_invariant P"
    and distinct: "distinct (map fst xs)"
    and admissible:
      "batch_prepend_admissible (bp_view (bmssp_trim_empty_prefix P)) xs"
  shows "bp_ordered_invariant (bmssp_apply_updates xs P)"
proof -
  let ?P0 = "bmssp_trim_empty_prefix P"
  have reg0: "bp_regular_invariant ?P0"
    by (rule bmssp_trim_empty_prefix_regular_invariant[OF reg])
  have ord0: "bp_ordered_invariant ?P0"
    by (rule bp_regular_invariant_ordered_invariant[OF reg0])
  show ?thesis
  proof (cases "bp_entries ?P0 = []")
    case True
    have disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view ?P0) = {}"
      using True unfolding bp_view_def bp_entry_keys_def by simp
    have "bp_ordered_invariant
      (bp_result_of (c_bp_paper_batch_prepend xs ?P0))"
      by (rule c_bp_paper_batch_prepend_ordered_invariant
          [OF ord0 distinct disjoint admissible])
    then show ?thesis
      using True unfolding bmssp_apply_updates_def by simp
  next
    case False
    have "bp_ordered_invariant (bmssp_insert_updates xs ?P0)"
      by (rule bmssp_insert_updates_ordered_invariant[OF reg0])
    then show ?thesis
      using False unfolding bmssp_apply_updates_def by simp
  qed
qed

lemma bmssp_apply_updates_refines_batch_min_update_from_ordered:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
  shows "bp_view (bmssp_apply_updates xs P) =
    batch_min_update (bp_view P) xs"
proof -
  let ?P0 = "bmssp_trim_empty_prefix P"
  have ord0: "bp_ordered_invariant ?P0"
    by (rule bmssp_trim_empty_prefix_ordered_invariant[OF ord])
  show ?thesis
  proof (cases "bp_entries ?P0 = []")
    case True
    have disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view ?P0) = {}"
      using True unfolding bp_view_def bp_entry_keys_def by simp
    have "bp_view (bp_result_of (c_bp_paper_batch_prepend xs ?P0)) =
      batch_min_update (bp_view ?P0) xs"
      by (rule c_bp_paper_batch_prepend_refines_batch_min_update
          [OF ord0 distinct disjoint])
    then show ?thesis
      using True unfolding bmssp_apply_updates_def by simp
  next
    case False
    have "bp_view (bmssp_insert_updates xs ?P0) =
      batch_min_update (bp_view ?P0) xs"
      by (rule bmssp_insert_updates_refines_batch_min_update_from_ordered
          [OF ord0])
    then show ?thesis
      using False unfolding bmssp_apply_updates_def by simp
  qed
qed

lemma bmssp_apply_updates_ordered_invariant_from_ordered:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
  shows "bp_ordered_invariant (bmssp_apply_updates xs P)"
proof -
  let ?P0 = "bmssp_trim_empty_prefix P"
  have ord0: "bp_ordered_invariant ?P0"
    by (rule bmssp_trim_empty_prefix_ordered_invariant[OF ord])
  show ?thesis
  proof (cases "bp_entries ?P0 = []")
    case True
    have disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view ?P0) = {}"
      using True unfolding bp_view_def bp_entry_keys_def by simp
    have admissible: "batch_prepend_admissible (bp_view ?P0) xs"
      using True
      unfolding batch_prepend_admissible_def bp_view_def bp_entry_keys_def
      by simp
    have "bp_ordered_invariant
      (bp_result_of (c_bp_paper_batch_prepend xs ?P0))"
      by (rule c_bp_paper_batch_prepend_ordered_invariant
          [OF ord0 distinct disjoint admissible])
    then show ?thesis
      using True unfolding bmssp_apply_updates_def by simp
  next
    case False
    have "bp_ordered_invariant (bmssp_insert_updates xs ?P0)"
      by (rule bmssp_insert_updates_ordered_invariant_from_ordered[OF ord0])
    then show ?thesis
      using False unfolding bmssp_apply_updates_def by simp
  qed
qed

lemma bmssp_apply_updates_preserves_upper_bound:
  assumes reg: "bp_regular_invariant P"
    and upper: "partition_upper_bound (bp_view P) B"
    and distinct: "distinct (map fst xs)"
    and values_lt: "\<And>x b. (x, b) \<in> set xs \<Longrightarrow> b < B"
  shows "partition_upper_bound (bp_view (bmssp_apply_updates xs P)) B"
  unfolding bmssp_apply_updates_refines_batch_min_update[OF reg distinct]
  by (rule batch_min_update_preserves_upper_bound[OF upper values_lt])

lemma bmssp_apply_updates_preserves_upper_bound_from_ordered:
  assumes ord: "bp_ordered_invariant P"
    and upper: "partition_upper_bound (bp_view P) B"
    and distinct: "distinct (map fst xs)"
    and values_lt: "\<And>x b. (x, b) \<in> set xs \<Longrightarrow> b < B"
  shows "partition_upper_bound (bp_view (bmssp_apply_updates xs P)) B"
  unfolding bmssp_apply_updates_refines_batch_min_update_from_ordered
    [OF ord distinct]
  by (rule batch_min_update_preserves_upper_bound[OF upper values_lt])

lemma bmssp_pull_refines_pull_separates:
  assumes ord: "bp_ordered_invariant P"
    and upper: "partition_upper_bound (bp_view P) B"
    and pull: "bp_pull M B P = (S, beta, P')"
  shows "pull_separates (bp_view P) M B S beta (bp_view P')"
proof (rule bp_pull_refines_pull_separates[OF _ _ pull])
  show "bp_invariant P"
    by (rule bp_ordered_invariant_invariant[OF ord])
next
  fix u
  assume "u \<in> keys_of (bp_view P)"
  then show "value_of (bp_view P) u < B"
    using upper unfolding partition_upper_bound_def by blast
qed

lemma bmssp_pull_ordered_invariant:
  assumes ord: "bp_ordered_invariant P"
    and pull: "bp_pull M B P = (S, beta, P')"
  shows "bp_ordered_invariant P'"
  by (rule bp_pull_ordered_invariant[OF ord pull])

lemma bmssp_pull_preserves_upper_bound:
  assumes ord: "bp_ordered_invariant P"
    and upper: "partition_upper_bound (bp_view P) B"
    and pull: "bp_pull M B P = (S, beta, P')"
  shows "partition_upper_bound (bp_view P') B"
proof -
  have inv: "bp_invariant P"
    by (rule bp_ordered_invariant_invariant[OF ord])
  show ?thesis
    by (rule bp_pull_preserves_upper_bound[OF inv upper upper pull])
qed

lemma bmssp_pull_step_bridge:
  assumes ord: "bp_ordered_invariant P"
    and upper: "partition_upper_bound (bp_view P) B"
    and pull: "bp_pull M B P = (S, beta, P')"
  shows "pull_separates (bp_view P) M B S beta (bp_view P')"
    and "bp_ordered_invariant P'"
    and "partition_upper_bound (bp_view P') B"
  using bmssp_pull_refines_pull_separates[OF assms]
    bmssp_pull_ordered_invariant[OF ord pull]
    bmssp_pull_preserves_upper_bound[OF assms]
  by blast+

lemma bmssp_vertices_distinct [simp]:
  "distinct (bmssp_vertices G s)"
  unfolding bmssp_vertices_def by simp

lemma finite_keys_of_bp_view [simp]:
  "finite (keys_of (bp_view P))"
  unfolding bp_view_def bp_entry_keys_def by simp

lemma bmssp_pulled_length_le_block_size:
  assumes distinct_vertices: "distinct vertices"
    and pull: "pull_separates (bp_view P) bmssp_block_size B S beta D'"
  shows "length (filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices)
    \<le> bmssp_block_size"
proof -
  let ?pulled = "filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices"
  have S_subset: "S \<subseteq> keys_of (bp_view P)"
    by (rule pull_separates_subset[OF pull])
  then have finite_S: "finite S"
    by (rule finite_subset) simp
  have set_pulled: "set ?pulled \<subseteq> S"
    by auto
  have distinct_pulled: "distinct ?pulled"
    using distinct_vertices by simp
  have "length ?pulled = card (set ?pulled)"
    using distinct_card[OF distinct_pulled] by simp
  also have "\<dots> \<le> card S"
    by (rule card_mono[OF finite_S set_pulled])
  also have "\<dots> \<le> bmssp_block_size"
    by (rule pull_separates_card[OF pull])
  finally show ?thesis .
qed

lemma bmssp_pulled_length_le_one:
  assumes distinct_vertices: "distinct vertices"
    and pull: "pull_separates (bp_view P) bmssp_block_size B S beta D'"
  shows "length (filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices)
    \<le> 1"
  using bmssp_pulled_length_le_block_size[OF distinct_vertices pull]
  unfolding bmssp_block_size_def .

fun bmssp_relax_edges ::
  "nat_graph \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat_dist \<Rightarrow>
    (nat \<times> real) list \<times> nat_dist" where
  "bmssp_relax_edges [] settled u du ds = ([], ds)"
| "bmssp_relax_edges ((a, b, w) # es) settled u du ds =
     (case bmssp_relax_edges es settled u du ds of
        (updates, ds1) \<Rightarrow>
          (if a = u \<and> b \<notin> set settled
           then
             (let nd = du + w in
              case bmssp_lookup_dist ds1 b of
                None \<Rightarrow>
                  ((b, bmssp_partition_key b nd) # updates,
                   bmssp_set_dist b nd ds1)
              | Some old \<Rightarrow>
                  (if nd < old
                   then ((b, bmssp_partition_key b nd) # updates,
                         bmssp_set_dist b nd ds1)
                   else (updates, ds1)))
           else (updates, ds1)))"

fun bmssp_relax_vertices ::
  "nat_graph \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat_dist \<Rightarrow>
    (nat \<times> real) list \<times> nat_dist" where
  "bmssp_relax_vertices G settled [] ds = ([], ds)"
| "bmssp_relax_vertices G settled (u # us) ds =
     (case bmssp_lookup_dist ds u of
        None \<Rightarrow> bmssp_relax_vertices G settled us ds
      | Some du \<Rightarrow>
          (case bmssp_relax_edges G settled u du ds of
             (updates_u, ds1) \<Rightarrow>
               (case bmssp_relax_vertices G settled us ds1 of
                  (updates_us, ds2) \<Rightarrow> (updates_u @ updates_us, ds2))))"

fun bmssp_loop ::
  "nat \<Rightarrow> nat_graph \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat_dist \<Rightarrow> nat bucketed_partition \<Rightarrow> nat_dist" where
  "bmssp_loop 0 G vertices settled ds P = bmssp_normalize_dist ds"
| "bmssp_loop (Suc fuel) G vertices settled ds P =
     (case bp_pull bmssp_block_size bmssp_bound P of
        (S, beta, P1) \<Rightarrow>
          (let pulled = filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices in
           if pulled = []
           then bmssp_normalize_dist ds
           else
             (let settled' = pulled @ settled;
                  relaxed = bmssp_relax_vertices G settled' pulled ds;
                  updates = fst relaxed;
                  ds' = snd relaxed;
                  P2 = bmssp_apply_updates updates P1
              in bmssp_loop fuel G vertices settled' ds' P2)))"

definition bmssp_distances :: "nat_graph \<Rightarrow> nat \<Rightarrow> nat_dist" where
  "bmssp_distances G s =
     (let vertices = bmssp_vertices G s;
          P0 = bp_empty bmssp_block_size bmssp_bound;
          P1 = bp_result_of
            (c_bp_regularized_local_insert s (bmssp_partition_key s 0) P0);
          fuel = Suc (length vertices * Suc (length G))
      in bmssp_loop fuel G vertices [] [(s, 0)] P1)"

text \<open>
  The entry point @{const bmssp_distances} initializes the bucketed partition
  with the source at distance zero and then iterates @{const bmssp_loop}.  The
  helper @{const bmssp_apply_updates} makes the example exercise both bulk and
  singleton update paths: an empty work-list receives a batch prepend, while a
  non-empty work-list receives local inserts.  The bucketed Pull operation is
  invoked in every loop iteration through @{const bp_pull}.
\<close>

definition example_graph :: nat_graph where
  "example_graph =
     [(0, 1, 3), (0, 4, 6), (0, 2, 10),
      (1, 2, 2), (1, 4, 4), (1, 3, 9),
      (2, 3, 3), (2, 4, 1), (4, 3, 5)]"

text \<open>
  From source 0:
    d(0) = 0
    d(1) = 3   via 0 -> 1
    d(2) = 5   via 0 -> 1 -> 2
    d(3) = 8   via 0 -> 1 -> 2 -> 3
    d(4) = 6   via 0 -> 4, tied by 0 -> 1 -> 2 -> 4
\<close>
definition example_expected_dist :: nat_dist where
  "example_expected_dist = [(0, 0), (1, 3), (2, 5), (3, 8), (4, 6)]"

text \<open>
  The graph is small enough to audit by hand but nontrivial enough to check the
  executable plumbing.  Vertex 0 starts the run.  Vertex 1 is reached directly
  with cost 3; vertex 2 improves from the direct edge of cost 10 to cost 5 via
  1; vertex 3 is then reached at cost 8 via 2; and vertex 4 has final cost 6,
  tied between the direct edge and the path through 1 and 2.  The constant
  @{const example_expected_dist} records that hand calculation as a literal
  sorted association list.
\<close>

lemma example_bmssp_correct:
  "bmssp_distances example_graph 0 = example_expected_dist"
  by eval

lemma bmssp_counterexample_fixed:
  "bmssp_distances [(0::nat, 1::nat, 1::nat), (0, 2, 1), (1, 3, 2)] 0
     = [(0, 0), (1, 1), (2, 1), (3, 3)]"
  by eval

lemma bmssp_line_graph_fixed:
  "bmssp_distances [(0::nat, 1::nat, 1::nat), (1, 2, 1), (2, 3, 1)] 0
     = [(0, 0), (1, 1), (2, 2), (3, 3)]"
  by eval

lemma bmssp_empty_prefix_progress_fixed:
  "bmssp_distances
     [(0::nat, 1::nat, 1::nat), (0, 2, 2), (0, 3, 3), (2, 4, 1)] 0
     = [(0, 0), (1, 1), (2, 2), (3, 3), (4, 3)]"
  by eval

text \<open>
  The theorem @{thm example_bmssp_correct} is the end-to-end smoke test.  The
  regression lemmas above cover equal-distance frontier updates, a multi-hop
  line graph, and progress after a pull leaves an empty bucket in front of
  pending vertices.  The proof method \<open>eval\<close> runs the generated equations
  inside Isabelle and proves that the result equals the expected literal
  distance map.  The following @{command value} command is intentionally kept in
  the theory so the build log prints the computed list for human inspection,
  and the final @{command export_code} declaration emits the same executable
  entry point as SML in the generated directory.
\<close>

value "bmssp_distances example_graph 0"

export_code bmssp_distances example_graph example_expected_dist
  in SML module_name BMSSP file_prefix "generated/BMSSP"

end
