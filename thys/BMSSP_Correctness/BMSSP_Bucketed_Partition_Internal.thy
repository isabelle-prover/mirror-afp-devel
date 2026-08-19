theory BMSSP_Bucketed_Partition_Internal
  imports BMSSP_Partition_Interface
    "HOL-Library.Discrete_Functions"
    "HOL-Library.Landau_Symbols"
begin

section \<open>Bucketed Partition Data Structure\<close>

text \<open>
  This is the main data-structure theory for the paper-faithful partition
  layer.  The BMSSP paper uses a bucketed structure whose operation bounds are
  expressed in terms of the ratio between the number of inserted elements and
  the block size.  That ratio is the essential distinction from a sorted-list
  model: Insert must pay for a search over buckets, not for a search over all
  stored elements.

  The formal model is functional.  A partition state contains a block size, an
  upper bound, a list of buckets, and a value memory.  Each bucket has a marker
  and an unsorted list of key/value entries.  The marker is a lower bound for
  the values in the bucket, and adjacent markers delimit the value ranges used
  by Pull.  The list-level operations below first establish a simple exact
  model, then a lazy model that permits buckets to grow up to the split
  threshold before they are rebuilt.

  The theory has three layers.  The first layer defines the functional state,
  invariants, Insert, BatchPrepend, and Pull, and proves that their views refine
  the abstract partition interface.  The second layer adds primitive step
  counters and a potential function for lazy splitting.  The third layer names
  the paper-facing operations and proves the three exported cost bounds:
  Insert at the ratio-log budget, BatchPrepend at the matching batched budget,
  and Pull at an amortized linear-in-\<open>M\<close> budget.  The baseline sorted-list
  partition state used by the recurrence proofs is not used here.

  The amortized analysis uses a scaled credit potential
  \<open>\<Phi>(P) = 4 \<cdot> \<Sum>\<^sub>b max 0 (length (bp_bucket_entries b) - bp_block_size P)\<close>,
  summed over the buckets of \<open>P\<close>.  The factor of four is the constant that
  absorbs the per-Insert charge: each Insert raises \<open>\<Phi>\<close> by at most four credits,
  which is exactly the budget that pays for the \<open>O(M)\<close> rebucket work performed
  during a Pull when a bucket has overflowed past the lazy split threshold.  This
  bookkeeping is what makes the bound paper-tight rather than merely
  amortized-but-loose: an Insert that does not split the bucket pays only for
  the bucket walk \<open>O(log (N / M))\<close>, an Insert that triggers a rebucket pays
  the same physical cost plus a refund of credits to \<open>\<Phi>\<close>, and Pull discharges
  the credits accumulated by its bucket's prior Inserts to fund the rebucket
  step.  Without the factor four the per-Insert charge would not cover the
  rebucket, and the resulting Insert bound would degrade to \<open>O(N / M)\<close>; with
  the factor four it stays at the paper rate.
\<close>

record 'k bp_bucket =
  bp_marker :: real
  bp_bucket_entries :: "('k \<times> real) list"

record 'k bucketed_partition =
  bp_block_size :: nat
  bp_upper_bound :: real
  bp_buckets :: "'k bp_bucket list"
  bp_values :: "'k \<Rightarrow> real"

definition bp_bucket_entries_flat :: "'k bp_bucket list \<Rightarrow> ('k \<times> real) list" where
  "bp_bucket_entries_flat bs = concat (map bp_bucket_entries bs)"

definition bp_entries :: "'k bucketed_partition \<Rightarrow> ('k \<times> real) list" where
  "bp_entries P = bp_bucket_entries_flat (bp_buckets P)"

definition bp_entry_keys :: "('k \<times> real) list \<Rightarrow> 'k set" where
  "bp_entry_keys xs = fst ` set xs"

definition bp_bucket_keys :: "'k bp_bucket \<Rightarrow> 'k set" where
  "bp_bucket_keys b = bp_entry_keys (bp_bucket_entries b)"

definition bp_view :: "'k bucketed_partition \<Rightarrow> 'k partition_view" where
  "bp_view P =
     \<lparr> keys_of = bp_entry_keys (bp_entries P),
       value_of = bp_values P \<rparr>"

definition bp_bucket_sizes_ok :: "'k bucketed_partition \<Rightarrow> bool" where
  "bp_bucket_sizes_ok P \<longleftrightarrow>
     (\<forall>b\<in>set (bp_buckets P).
       length (bp_bucket_entries b) \<le> bp_block_size P)"

definition bp_lazy_bucket_sizes_ok :: "'k bucketed_partition \<Rightarrow> bool" where
  "bp_lazy_bucket_sizes_ok P \<longleftrightarrow>
     (\<forall>b\<in>set (bp_buckets P).
       length (bp_bucket_entries b) \<le> 2 * bp_block_size P)"

definition bp_bucket_markers_sorted :: "'k bucketed_partition \<Rightarrow> bool" where
  "bp_bucket_markers_sorted P \<longleftrightarrow>
     sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) (bp_buckets P)"

definition bp_bucket_markers_lower_bound :: "'k bucketed_partition \<Rightarrow> bool" where
  "bp_bucket_markers_lower_bound P \<longleftrightarrow>
     (\<forall>b\<in>set (bp_buckets P).
       \<forall>p\<in>set (bp_bucket_entries b). bp_marker b \<le> snd p)"

definition bp_values_consistent :: "'k bucketed_partition \<Rightarrow> bool" where
  "bp_values_consistent P \<longleftrightarrow>
     (\<forall>p\<in>set (bp_entries P). bp_values P (fst p) = snd p)"

definition bp_distinct_keys :: "'k bucketed_partition \<Rightarrow> bool" where
  "bp_distinct_keys P \<longleftrightarrow> distinct (map fst (bp_entries P))"

fun bp_bucket_boundaries_ok :: "'k bp_bucket list \<Rightarrow> bool" where
  "bp_bucket_boundaries_ok [] \<longleftrightarrow> True"
| "bp_bucket_boundaries_ok [b] \<longleftrightarrow> True"
| "bp_bucket_boundaries_ok (b # c # bs) \<longleftrightarrow>
     (\<forall>p\<in>set (bp_bucket_entries b). snd p \<le> bp_marker c) \<and>
     bp_bucket_boundaries_ok (c # bs)"

definition bp_bucket_boundaries_state_ok ::
  "'k bucketed_partition \<Rightarrow> bool" where
  "bp_bucket_boundaries_state_ok P \<longleftrightarrow>
     bp_bucket_boundaries_ok (bp_buckets P)"

definition bp_invariant :: "'k bucketed_partition \<Rightarrow> bool" where
  "bp_invariant P \<longleftrightarrow>
     0 < bp_block_size P \<and>
     bp_distinct_keys P \<and>
     bp_bucket_sizes_ok P \<and>
     bp_bucket_markers_sorted P \<and>
     bp_bucket_markers_lower_bound P \<and>
     bp_values_consistent P"

definition bp_ordered_invariant :: "'k bucketed_partition \<Rightarrow> bool" where
  "bp_ordered_invariant P \<longleftrightarrow>
     bp_invariant P \<and> bp_bucket_boundaries_state_ok P"

definition bp_lazy_invariant :: "'k bucketed_partition \<Rightarrow> bool" where
  "bp_lazy_invariant P \<longleftrightarrow>
     0 < bp_block_size P \<and>
     bp_distinct_keys P \<and>
     bp_lazy_bucket_sizes_ok P \<and>
     bp_bucket_markers_sorted P \<and>
     bp_bucket_markers_lower_bound P \<and>
     bp_values_consistent P"

definition bp_lazy_ordered_invariant :: "'k bucketed_partition \<Rightarrow> bool" where
  "bp_lazy_ordered_invariant P \<longleftrightarrow>
     bp_lazy_invariant P \<and> bp_bucket_boundaries_state_ok P"

text \<open>
  The invariant vocabulary separates three concerns.  The basic view of a
  state is @{const bp_view}: it exposes only the key set and the value memory
  required by the abstract partition interface.  The structural invariant
  @{const bp_invariant} says that the block size is positive, keys are unique,
  strict bucket sizes are at most @{const bp_block_size}, markers are sorted,
  markers are lower bounds for their entries, and the stored value memory
  agrees with the bucket entries.  The ordered invariant
  @{const bp_ordered_invariant} adds the boundary condition between adjacent
  buckets, which is what makes a first-bucket Pull sound.

  The lazy variants are used for the amortized Insert proof.  In
  @{const bp_lazy_invariant}, buckets may temporarily contain up to twice the
  block size.  This slack is exactly what lets Insert avoid rebuilding on every
  operation.  Once a bucket crosses the lazy threshold, the state is rebuilt
  into strict buckets and the potential drops enough to pay for the split.
\<close>

definition bp_empty :: "nat \<Rightarrow> real \<Rightarrow> 'k bucketed_partition" where
  "bp_empty M B =
     \<lparr> bp_block_size = M,
       bp_upper_bound = B,
       bp_buckets = [],
       bp_values = (\<lambda>_. B) \<rparr>"

definition bp_singleton_bucket :: "'k \<times> real \<Rightarrow> 'k bp_bucket" where
  "bp_singleton_bucket p =
     \<lparr> bp_marker = snd p, bp_bucket_entries = [p] \<rparr>"

lemma bp_singleton_bucket_simps [simp]:
  "bp_marker (bp_singleton_bucket p) = snd p"
  "bp_bucket_entries (bp_singleton_bucket p) = [p]"
  unfolding bp_singleton_bucket_def by simp_all

definition bp_make_bucket :: "('k \<times> real) list \<Rightarrow> 'k bp_bucket" where
  "bp_make_bucket xs =
     \<lparr> bp_marker = snd (hd xs), bp_bucket_entries = xs \<rparr>"

fun bp_bucketize_sorted_entries_aux ::
  "nat \<Rightarrow> nat \<Rightarrow> ('k \<times> real) list \<Rightarrow> 'k bp_bucket list" where
  "bp_bucketize_sorted_entries_aux 0 M xs = []"
| "bp_bucketize_sorted_entries_aux (Suc fuel) M xs =
     (if M = 0 \<or> xs = []
      then []
      else bp_make_bucket (take M xs) #
        bp_bucketize_sorted_entries_aux fuel M (drop M xs))"

definition bp_bucketize_sorted_entries ::
  "nat \<Rightarrow> ('k \<times> real) list \<Rightarrow> 'k bp_bucket list" where
  "bp_bucketize_sorted_entries M xs =
     bp_bucketize_sorted_entries_aux (length xs) M xs"

definition bp_bucketize_entries ::
  "nat \<Rightarrow> ('k \<times> real) list \<Rightarrow> 'k bp_bucket list" where
  "bp_bucketize_entries M xs = bp_bucketize_sorted_entries M (sort_key snd xs)"

lemma bp_bucketize_sorted_entries_aux_empty [simp]:
  "bp_bucketize_sorted_entries_aux fuel M [] = []"
  by (cases fuel) simp_all

definition bp_rebucket :: "'k bucketed_partition \<Rightarrow> 'k bucketed_partition" where
  "bp_rebucket P =
     P\<lparr>bp_buckets := bp_bucketize_entries (bp_block_size P) (bp_entries P)\<rparr>"

fun bp_local_insert_bucket ::
  "nat \<Rightarrow> 'k \<times> real \<Rightarrow> 'k bp_bucket list \<Rightarrow> 'k bp_bucket list" where
  "bp_local_insert_bucket M p [] = bp_bucketize_entries M [p]"
| "bp_local_insert_bucket M p [b] =
     (if snd p < bp_marker b
      then bp_bucketize_entries M [p] @ [b]
      else bp_bucketize_entries M (p # bp_bucket_entries b))"
| "bp_local_insert_bucket M p (b # c # bs) =
     (if snd p < bp_marker b
      then bp_bucketize_entries M [p] @ b # c # bs
      else if snd p < bp_marker c
        then bp_bucketize_entries M (p # bp_bucket_entries b) @ c # bs
        else b # bp_local_insert_bucket M p (c # bs))"

definition bp_lazy_bucket_insert_entries ::
  "nat \<Rightarrow> 'k \<times> real \<Rightarrow> 'k bp_bucket \<Rightarrow> 'k bp_bucket list" where
  "bp_lazy_bucket_insert_entries M p b =
     (if length (bp_bucket_entries b) < 2 * M
      then [b\<lparr>bp_bucket_entries := p # bp_bucket_entries b\<rparr>]
      else bp_bucketize_entries M (p # bp_bucket_entries b))"

fun bp_lazy_insert_bucket ::
  "nat \<Rightarrow> 'k \<times> real \<Rightarrow> 'k bp_bucket list \<Rightarrow> 'k bp_bucket list" where
  "bp_lazy_insert_bucket M p [] = bp_bucketize_entries M [p]"
| "bp_lazy_insert_bucket M p [b] =
     (if snd p < bp_marker b
      then bp_bucketize_entries M [p] @ [b]
      else bp_lazy_bucket_insert_entries M p b)"
| "bp_lazy_insert_bucket M p (b # c # bs) =
     (if snd p < bp_marker b
      then bp_bucketize_entries M [p] @ b # c # bs
      else if snd p < bp_marker c
        then bp_lazy_bucket_insert_entries M p b @ c # bs
        else b # bp_lazy_insert_bucket M p (c # bs))"

fun bp_insert_bucket :: "'k \<times> real \<Rightarrow> 'k bp_bucket list \<Rightarrow> 'k bp_bucket list" where
  "bp_insert_bucket p [] = [bp_singleton_bucket p]"
| "bp_insert_bucket p (b # bs) =
     (if snd p \<le> bp_marker b
      then bp_singleton_bucket p # b # bs
      else b # bp_insert_bucket p bs)"

definition bp_delete_key_from_bucket :: "'k \<Rightarrow> 'k bp_bucket \<Rightarrow> 'k bp_bucket" where
  "bp_delete_key_from_bucket x b =
     b\<lparr>bp_bucket_entries := filter (\<lambda>p. fst p \<noteq> x) (bp_bucket_entries b)\<rparr>"

definition bp_delete_key :: "'k \<Rightarrow> 'k bucketed_partition \<Rightarrow> 'k bucketed_partition" where
  "bp_delete_key x P =
     P\<lparr>bp_buckets := map (bp_delete_key_from_bucket x) (bp_buckets P)\<rparr>"

definition bp_insert ::
  "'k \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow> 'k bucketed_partition" where
  "bp_insert x b P =
     (let b' = (if x \<in> bp_entry_keys (bp_entries P)
          then min (bp_values P x) b else b);
        P0 = bp_delete_key x P
      in P0\<lparr>bp_buckets := bp_insert_bucket (x, b') (bp_buckets P0),
             bp_values := (bp_values P)(x := b')\<rparr>)"

definition bp_local_insert_state ::
  "'k \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow> 'k bucketed_partition" where
  "bp_local_insert_state x b P =
     (let b' = (if x \<in> bp_entry_keys (bp_entries P)
          then min (bp_values P x) b else b);
        P0 = bp_delete_key x P
      in P0\<lparr>bp_buckets :=
             bp_local_insert_bucket (bp_block_size P0) (x, b') (bp_buckets P0),
             bp_values := (bp_values P)(x := b')\<rparr>)"

definition bp_lazy_insert_state ::
  "'k \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow> 'k bucketed_partition" where
  "bp_lazy_insert_state x b P =
     (let b' = (if x \<in> bp_entry_keys (bp_entries P)
          then min (bp_values P x) b else b);
        P0 = bp_delete_key x P
      in P0\<lparr>bp_buckets :=
             bp_lazy_insert_bucket (bp_block_size P0) (x, b') (bp_buckets P0),
             bp_values := (bp_values P)(x := b')\<rparr>)"

definition bp_batch_prepend ::
  "('k \<times> real) list \<Rightarrow> 'k bucketed_partition \<Rightarrow> 'k bucketed_partition" where
  "bp_batch_prepend xs P =
     fold (\<lambda>(x, b) P'. bp_insert x b P') xs P"

fun bp_batch_value_update ::
  "('k \<times> real) list \<Rightarrow> ('k \<Rightarrow> real) \<Rightarrow> 'k \<Rightarrow> real" where
  "bp_batch_value_update [] f = f"
| "bp_batch_value_update ((x, b) # xs) f =
     bp_batch_value_update xs (f(x := b))"

fun bp_batch_max_value :: "real \<Rightarrow> ('k \<times> real) list \<Rightarrow> real" where
  "bp_batch_max_value beta [] = beta"
| "bp_batch_max_value beta ((x, b) # xs) =
     bp_batch_max_value (max beta b) xs"

fun bp_rebase_first_bucket_marker ::
  "real \<Rightarrow> 'k bp_bucket list \<Rightarrow> 'k bp_bucket list" where
  "bp_rebase_first_bucket_marker beta [] = []"
| "bp_rebase_first_bucket_marker beta (b # bs) =
     b\<lparr>bp_marker := beta\<rparr> # bs"

fun bp_drop_empty_prefix :: "'k bp_bucket list \<Rightarrow> 'k bp_bucket list" where
  "bp_drop_empty_prefix [] = []"
| "bp_drop_empty_prefix (b # bs) =
     (if bp_bucket_entries b = [] then bp_drop_empty_prefix bs else b # bs)"

definition bp_bucketed_batch_prepend_state ::
  "('k \<times> real) list \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k bucketed_partition" where
  "bp_bucketed_batch_prepend_state xs P =
     (case xs of
        [] \<Rightarrow> P
      | p # ps \<Rightarrow>
          (let beta = bp_batch_max_value (snd p) ps;
             new = bp_bucketize_entries (bp_block_size P) xs;
             old = bp_rebase_first_bucket_marker beta
               (bp_drop_empty_prefix (bp_buckets P))
           in P\<lparr>bp_buckets := new @ old,
                bp_values := bp_batch_value_update xs (bp_values P)\<rparr>))"

definition bp_delete_keys_from_bucket :: "'k set \<Rightarrow> 'k bp_bucket \<Rightarrow> 'k bp_bucket" where
  "bp_delete_keys_from_bucket S b =
     b\<lparr>bp_bucket_entries := filter (\<lambda>p. fst p \<notin> S) (bp_bucket_entries b)\<rparr>"

definition bp_delete_keys :: "'k set \<Rightarrow> 'k bucketed_partition \<Rightarrow> 'k bucketed_partition" where
  "bp_delete_keys S P =
     P\<lparr>bp_buckets := map (bp_delete_keys_from_bucket S) (bp_buckets P)\<rparr>"

fun bp_min_value :: "real \<Rightarrow> ('k \<times> real) list \<Rightarrow> real" where
  "bp_min_value B [] = B"
| "bp_min_value B ((x, b) # xs) = min b (bp_min_value B xs)"

definition bp_bucket_below_bound :: "'k bp_bucket \<Rightarrow> real \<Rightarrow> bool" where
  "bp_bucket_below_bound b beta \<longleftrightarrow>
     (\<forall>p\<in>set (bp_bucket_entries b). snd p < beta)"

definition bp_first_bucket_pull ::
  "nat \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k set \<times> real \<times> 'k bucketed_partition" where
  "bp_first_bucket_pull M B P =
     (case bp_buckets P of
        b # c # bs \<Rightarrow>
          (let S = bp_bucket_keys b
           in (S, bp_marker c, bp_delete_keys S P))
      | _ \<Rightarrow> ({}, B, P))"

definition bp_pull_set :: "nat \<Rightarrow> 'k bucketed_partition \<Rightarrow> 'k set" where
  "bp_pull_set M P =
     (if length (bp_entries P) \<le> M
      then bp_entry_keys (bp_entries P)
      else {})"

definition bp_pull_bound :: "nat \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow> real" where
  "bp_pull_bound M B P =
     (if length (bp_entries P) \<le> M
      then B
      else bp_min_value B (bp_entries P))"

definition bp_conservative_pull ::
  "nat \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k set \<times> real \<times> 'k bucketed_partition" where
  "bp_conservative_pull M B P =
     (let S = bp_pull_set M P;
        beta = bp_pull_bound M B P
      in (S, beta, bp_delete_keys S P))"

definition bp_can_first_bucket_pull ::
  "nat \<Rightarrow> 'k bucketed_partition \<Rightarrow> bool" where
  "bp_can_first_bucket_pull M P \<longleftrightarrow>
     (case bp_buckets P of
        b # c # bs \<Rightarrow>
          length (bp_entries P) > M \<and>
          length (bp_bucket_entries b) \<le> M \<and>
          bp_bucket_below_bound b (bp_marker c) \<and>
          bp_bucket_entries_flat (c # bs) \<noteq> []
      | _ \<Rightarrow> False)"

definition bp_pull ::
  "nat \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k set \<times> real \<times> 'k bucketed_partition" where
  "bp_pull M B P =
     (if bp_can_first_bucket_pull M P
      then bp_first_bucket_pull M B P
      else bp_conservative_pull M B P)"

lemma bp_can_first_bucket_pullE:
  assumes "bp_can_first_bucket_pull M P"
  obtains b c bs where
    "bp_buckets P = b # c # bs"
    "length (bp_entries P) > M"
    "length (bp_bucket_entries b) \<le> M"
    "bp_bucket_below_bound b (bp_marker c)"
    "bp_bucket_entries_flat (c # bs) \<noteq> []"
  using assms
proof (cases "bp_buckets P")
  case Nil
  then show ?thesis
    using assms unfolding bp_can_first_bucket_pull_def by simp
next
  case (Cons b rest)
  note buckets_outer = Cons
  then show ?thesis
  proof (cases rest)
    case Nil
    then show ?thesis
      using assms buckets_outer unfolding bp_can_first_bucket_pull_def by simp
  next
    case (Cons c bs)
    have buckets: "bp_buckets P = b # c # bs"
      using buckets_outer Cons by simp
    have len_entries: "length (bp_entries P) > M"
      using assms buckets unfolding bp_can_first_bucket_pull_def by simp
    have len_b: "length (bp_bucket_entries b) \<le> M"
      using assms buckets unfolding bp_can_first_bucket_pull_def by simp
    have below: "bp_bucket_below_bound b (bp_marker c)"
      using assms buckets unfolding bp_can_first_bucket_pull_def by simp
    have tail_nonempty: "bp_bucket_entries_flat (c # bs) \<noteq> []"
      using assms buckets unfolding bp_can_first_bucket_pull_def by simp
    show ?thesis
      by (rule that[OF buckets len_entries len_b below tail_nonempty])
  qed
qed

lemma bp_entry_keys_filter_neq [simp]:
  "bp_entry_keys (filter (\<lambda>p. fst p \<noteq> x) xs) = bp_entry_keys xs - {x}"
  unfolding bp_entry_keys_def by auto

lemma bp_entry_keys_filter_notin [simp]:
  "bp_entry_keys (filter (\<lambda>p. fst p \<notin> S) xs) = bp_entry_keys xs - S"
  unfolding bp_entry_keys_def by auto

lemma bp_bucket_keys_alt [simp]:
  "bp_bucket_keys b = fst ` set (bp_bucket_entries b)"
  unfolding bp_bucket_keys_def bp_entry_keys_def by simp

lemma bp_entries_empty [simp]:
  "bp_entries (bp_empty M B) = []"
  unfolding bp_entries_def bp_empty_def bp_bucket_entries_flat_def by simp

lemma bp_bucket_entries_flat_append [simp]:
  "bp_bucket_entries_flat (bs @ cs) =
    bp_bucket_entries_flat bs @ bp_bucket_entries_flat cs"
  unfolding bp_bucket_entries_flat_def by simp

lemma bp_bucket_entries_flat_rebase_first_bucket_marker [simp]:
  "bp_bucket_entries_flat (bp_rebase_first_bucket_marker beta bs) =
    bp_bucket_entries_flat bs"
  by (cases bs) (simp_all add: bp_bucket_entries_flat_def)

lemma bp_bucket_entries_flat_drop_empty_prefix [simp]:
  "bp_bucket_entries_flat (bp_drop_empty_prefix bs) =
    bp_bucket_entries_flat bs"
  by (induction bs) (simp_all add: bp_bucket_entries_flat_def)

lemma length_bp_rebase_first_bucket_marker [simp]:
  "length (bp_rebase_first_bucket_marker beta bs) = length bs"
  by (cases bs) simp_all

lemma length_bp_drop_empty_prefix_le [simp]:
  "length (bp_drop_empty_prefix bs) \<le> length bs"
  by (induction bs) auto

lemma bp_entry_keys_rebase_first_bucket_marker [simp]:
  "bp_entry_keys
    (bp_bucket_entries_flat (bp_rebase_first_bucket_marker beta bs)) =
    bp_entry_keys (bp_bucket_entries_flat bs)"
  by simp

lemma bp_entry_keys_drop_empty_prefix [simp]:
  "bp_entry_keys (bp_bucket_entries_flat (bp_drop_empty_prefix bs)) =
    bp_entry_keys (bp_bucket_entries_flat bs)"
  by simp

lemma bp_drop_empty_prefix_set_subset:
  "set (bp_drop_empty_prefix bs) \<subseteq> set bs"
  by (induction bs) auto

lemma bp_drop_empty_prefix_head_nonempty:
  assumes "bp_drop_empty_prefix bs = b # bs'"
  shows "bp_bucket_entries b \<noteq> []"
  using assms
proof (induction bs)
  case Nil
  then show ?case by simp
next
  case (Cons a bs)
  show ?case
  proof (cases "bp_bucket_entries a = []")
    case True
    then show ?thesis
      using Cons.IH Cons.prems by simp
  next
    case False
    then have "a = b"
      using Cons.prems by simp
    then show ?thesis
      using False by simp
  qed
qed

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
      using Cons.prems by (cases bs) simp_all
    then show ?thesis
      using True Cons.IH by simp
  next
    case False
    then show ?thesis
      using Cons.prems by simp
  qed
qed

lemma bp_bucket_markers_sorted_drop_empty_prefix:
  assumes "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) bs"
  shows "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
    (bp_drop_empty_prefix bs)"
  using assms
proof (induction bs)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  show ?case
  proof (cases "bp_bucket_entries b = []")
    case True
    have "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) bs"
      using Cons.prems by simp
    then show ?thesis
      using True Cons.IH by simp
  next
    case False
    then show ?thesis
      using Cons.prems by simp
  qed
qed

lemma bp_bucket_boundaries_ok_rebase_first_bucket_marker [simp]:
  "bp_bucket_boundaries_ok (bp_rebase_first_bucket_marker beta bs) =
    bp_bucket_boundaries_ok bs"
proof (cases bs)
  case Nil
  then show ?thesis by simp
next
  case (Cons b rest)
  then show ?thesis
    by (cases rest) simp_all
qed

lemma bp_batch_value_update_notin:
  assumes "x \<notin> fst ` set xs"
  shows "bp_batch_value_update xs f x = f x"
  using assms by (induction xs arbitrary: f) auto

lemma bp_batch_value_update_in_set_distinct:
  assumes distinct: "distinct (map fst xs)"
    and member: "(x, b) \<in> set xs"
  shows "bp_batch_value_update xs f x = b"
  using assms
proof (induction xs arbitrary: f)
  case Nil
  then show ?case by simp
next
  case (Cons p xs)
  obtain y c where p_def: "p = (y, c)"
    by force
  show ?case
  proof (cases "x = y")
    case True
    have x_not_tail: "x \<notin> fst ` set xs"
      using True Cons.prems p_def by auto
    then have "(x, b) \<notin> set xs"
      by force
    then have "(x, b) = (y, c)"
      using Cons.prems p_def by auto
    then have bc: "b = c"
      by simp
    have y_not_tail: "y \<notin> fst ` set xs"
      using x_not_tail True by simp
    have unchanged:
      "bp_batch_value_update xs (f(y := c)) y = c"
      using bp_batch_value_update_notin[OF y_not_tail, of "f(y := c)"]
      by simp
    then show ?thesis
      unfolding p_def True bc
      by simp
  next
    case False
    then have "(x, b) \<in> set xs"
      using Cons.prems p_def by auto
    moreover have "distinct (map fst xs)"
      using Cons.prems p_def by simp
    ultimately show ?thesis
      unfolding p_def by (simp add: Cons.IH)
  qed
qed

lemma batch_min_update_value_distinct_disjoint:
  assumes distinct: "distinct (map fst xs)"
    and disjoint: "fst ` set xs \<inter> keys_of D = {}"
  shows "value_of (batch_min_update D xs) =
    bp_batch_value_update xs (value_of D)"
  using distinct disjoint
proof (induction xs arbitrary: D)
  case Nil
  then show ?case
    unfolding batch_min_update_def by simp
next
  case (Cons p xs)
  obtain x b where p_def: "p = (x, b)"
    by force
  have distinct_tail: "distinct (map fst xs)"
    using Cons.prems p_def by simp
  have x_not_tail: "x \<notin> fst ` set xs"
    using Cons.prems p_def by auto
  have x_not_D: "x \<notin> keys_of D"
    using Cons.prems p_def by auto
  have disjoint_tail:
    "fst ` set xs \<inter> keys_of (min_update D x b) = {}"
    using Cons.prems x_not_tail p_def
    unfolding min_update_def by auto
  have tail:
    "value_of (batch_min_update (min_update D x b) xs) =
      bp_batch_value_update xs (value_of (min_update D x b))"
    by (rule Cons.IH[OF distinct_tail disjoint_tail])
  have fold_tail:
    "value_of
      (fold (\<lambda>(x, b) D'. min_update D' x b) xs (min_update D x b)) =
      bp_batch_value_update xs (value_of (min_update D x b))"
    using tail unfolding batch_min_update_def .
  have step_values:
    "value_of (min_update D x b) = (value_of D)(x := b)"
    using x_not_D unfolding min_update_def by simp
  show ?case
    unfolding p_def
    by (simp add: batch_min_update_def fold_tail step_values)
qed

lemma bp_batch_max_value_upper:
  assumes "\<And>p. p \<in> set xs \<Longrightarrow> snd p \<le> gamma"
    and "beta \<le> gamma"
  shows "bp_batch_max_value beta xs \<le> gamma"
  using assms
proof (induction xs arbitrary: beta)
  case Nil
  then show ?case by simp
next
  case (Cons p xs)
  obtain x b where p_def: "p = (x, b)"
    by force
  have head_le: "b \<le> gamma"
    using Cons.prems(1)[of p] p_def by simp
  have max_le: "max beta b \<le> gamma"
    using Cons.prems(2) head_le by simp
  have "bp_batch_max_value (max beta (snd p)) xs \<le> gamma"
  proof (rule Cons.IH)
    fix q
    assume "q \<in> set xs"
    then show "snd q \<le> gamma"
      using Cons.prems by simp
  qed (use max_le p_def in simp)
  then show ?case
    unfolding p_def by simp
qed

lemma bp_batch_max_value_ge_initial:
  "beta \<le> bp_batch_max_value beta xs"
proof (induction xs arbitrary: beta)
  case Nil
  then show ?case by simp
next
  case (Cons p xs)
  obtain x b where p_def: "p = (x, b)"
    by force
  have "beta \<le> max beta b"
    by simp
  moreover have "max beta b \<le> bp_batch_max_value (max beta b) xs"
    by (rule Cons.IH)
  ultimately have "beta \<le> bp_batch_max_value (max beta b) xs"
    by linarith
  then show ?case
    unfolding p_def by simp
qed

lemma bp_batch_max_value_ge_member:
  assumes "p \<in> set xs"
  shows "snd p \<le> bp_batch_max_value beta xs"
  using assms
proof (induction xs arbitrary: beta)
  case Nil
  then show ?case by simp
next
  case (Cons q xs)
  obtain y c where q_def: "q = (y, c)"
    by force
  show ?case
  proof (cases "p = q")
    case True
    have "snd p \<le> max beta c"
      using True q_def by simp
    moreover have "max beta c \<le> bp_batch_max_value (max beta c) xs"
      by (rule bp_batch_max_value_ge_initial)
    ultimately have "snd p \<le> bp_batch_max_value (max beta c) xs"
      by linarith
    then show ?thesis
      unfolding q_def by simp
  next
    case False
    then have "p \<in> set xs"
      using Cons.prems by simp
    then show ?thesis
      unfolding q_def by (simp add: Cons.IH)
  qed
qed

lemma bp_batch_max_value_ge_member_Cons:
  assumes "q \<in> set (p # ps)"
  shows "snd q \<le> bp_batch_max_value (snd p) ps"
  using assms
  by (cases "q = p")
    (simp_all add: bp_batch_max_value_ge_initial bp_batch_max_value_ge_member)

lemma bp_bucket_entries_flat_bucketize_sorted_entries_aux:
  assumes "0 < M"
    and "length xs \<le> fuel"
  shows "bp_bucket_entries_flat
      (bp_bucketize_sorted_entries_aux fuel M xs) = xs"
  using assms
proof (induction fuel arbitrary: xs)
  case 0
  then have "xs = []"
    by simp
  then show ?case
    by (simp add: bp_bucket_entries_flat_def)
next
  case (Suc fuel)
  show ?case
  proof (cases "xs = []")
    case True
    then show ?thesis
      by (simp add: bp_bucket_entries_flat_def)
  next
    case False
    have len_drop: "length (drop M xs) \<le> fuel"
      using Suc.prems False by (cases M) auto
    have tail:
      "bp_bucket_entries_flat
        (bp_bucketize_sorted_entries_aux fuel M (drop M xs)) =
       drop M xs"
      by (rule Suc.IH[OF Suc.prems(1) len_drop])
    show ?thesis
      using Suc.prems False tail
      by (simp add: bp_bucket_entries_flat_def bp_make_bucket_def)
  qed
qed

lemma bp_bucket_entries_flat_bucketize_sorted_entries:
  assumes "0 < M"
  shows "bp_bucket_entries_flat (bp_bucketize_sorted_entries M xs) = xs"
  using assms
  unfolding bp_bucketize_sorted_entries_def
  by (simp add: bp_bucket_entries_flat_bucketize_sorted_entries_aux)

lemma bp_bucket_entries_flat_bucketize_entries:
  assumes "0 < M"
  shows "bp_bucket_entries_flat (bp_bucketize_entries M xs) = sort_key snd xs"
  using assms
  unfolding bp_bucketize_entries_def
  by (simp add: bp_bucket_entries_flat_bucketize_sorted_entries)

lemma set_bp_bucket_entries_flat_bucketize_entries:
  assumes "0 < M"
  shows "set (bp_bucket_entries_flat (bp_bucketize_entries M xs)) = set xs"
  using assms
  by (simp add: bp_bucket_entries_flat_bucketize_entries)

lemma bp_entry_keys_bucketize_entries [simp]:
  assumes "0 < M"
  shows "bp_entry_keys (bp_bucket_entries_flat (bp_bucketize_entries M xs)) =
    bp_entry_keys xs"
  using assms
  unfolding bp_entry_keys_def
  by (simp add: set_bp_bucket_entries_flat_bucketize_entries)

lemma bp_bucketize_sorted_entries_aux_sizes_ok:
  assumes "0 < M"
  shows "\<forall>b\<in>set (bp_bucketize_sorted_entries_aux fuel M xs).
    length (bp_bucket_entries b) \<le> M"
  using assms
  by (induction fuel arbitrary: xs) (auto simp: bp_make_bucket_def)

lemma bp_bucketize_sorted_entries_sizes_ok:
  assumes "0 < M"
  shows "\<forall>b\<in>set (bp_bucketize_sorted_entries M xs).
    length (bp_bucket_entries b) \<le> M"
  using assms
  unfolding bp_bucketize_sorted_entries_def
  by (rule bp_bucketize_sorted_entries_aux_sizes_ok)

lemma bp_bucketize_entries_sizes_ok:
  assumes "0 < M"
  shows "\<forall>b\<in>set (bp_bucketize_entries M xs).
    length (bp_bucket_entries b) \<le> M"
  using assms
  unfolding bp_bucketize_entries_def
  by (rule bp_bucketize_sorted_entries_sizes_ok)

lemma bp_sorted_wrt_snd_sort_key [simp]:
  "sorted_wrt (\<lambda>p q. snd p \<le> snd q) (sort_key snd xs)"
proof -
  have "sorted (map snd (sort_key snd xs))"
    by (rule sorted_sort_key)
  then show ?thesis
    by (simp add: sorted_map)
qed

lemma sorted_wrt_hd_snd_le:
  fixes xs :: "('k \<times> real) list"
  assumes sorted: "sorted_wrt (\<lambda>p q. snd p \<le> snd q) xs"
    and xs: "xs \<noteq> []"
    and p: "p \<in> set xs"
  shows "snd (hd xs) \<le> snd p"
proof (cases xs)
  case Nil
  then show ?thesis
    using xs by simp
next
  case (Cons q qs)
  show ?thesis
  proof (cases "p = q")
    case True
    have "snd (hd xs) = snd p"
      using Cons True by simp
    then show ?thesis
      by simp
  next
    case False
    then have "p \<in> set qs"
      using p Cons by simp
    moreover have "\<forall>r\<in>set qs. snd q \<le> snd r"
      using sorted Cons by simp
    ultimately show ?thesis
      using Cons by simp
  qed
qed

lemma sorted_wrt_snd_take_drop_le:
  fixes xs :: "('k \<times> real) list"
  assumes sorted: "sorted_wrt (\<lambda>p q. snd p \<le> snd q) xs"
    and p: "p \<in> set (take n xs)"
    and q: "q \<in> set (drop n xs)"
  shows "snd p \<le> snd q"
proof -
  have "sorted_wrt (\<lambda>p q. snd p \<le> snd q) (take n xs @ drop n xs)"
    using sorted by simp
  then have "\<forall>p\<in>set (take n xs). \<forall>q\<in>set (drop n xs). snd p \<le> snd q"
    unfolding sorted_wrt_append by blast
  then show ?thesis
    using p q by blast
qed

lemma bp_bucketize_sorted_entries_aux_marker_in_set:
  assumes "b \<in> set (bp_bucketize_sorted_entries_aux fuel M xs)"
  shows "\<exists>p\<in>set xs. bp_marker b = snd p"
  using assms
proof (induction fuel arbitrary: xs)
  case 0
  then show ?case
    by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "M = 0 \<or> xs = []")
    case True
    then show ?thesis
      using Suc.prems by simp
  next
    case False
    have M_pos: "0 < M"
      using False by simp
    have xs_nonempty: "xs \<noteq> []"
      using False by simp
    from Suc.prems have b_cases:
      "b = bp_make_bucket (take M xs) \<or>
       b \<in> set (bp_bucketize_sorted_entries_aux fuel M (drop M xs))"
      using False by simp
    from b_cases show ?thesis
    proof
      assume b_def: "b = bp_make_bucket (take M xs)"
      have "hd (take M xs) \<in> set xs"
        using M_pos xs_nonempty by (cases xs) auto
      then show ?thesis
        unfolding b_def bp_make_bucket_def by auto
    next
      assume b_tail:
        "b \<in> set (bp_bucketize_sorted_entries_aux fuel M (drop M xs))"
      obtain p where p_drop: "p \<in> set (drop M xs)"
        and marker: "bp_marker b = snd p"
        using Suc.IH[OF b_tail] by auto
      have "p \<in> set xs"
        by (meson in_set_dropD p_drop)
      then show ?thesis
        using marker by auto
    qed
  qed
qed

lemma bp_bucketize_sorted_entries_aux_markers_lower_bound:
  fixes xs :: "('k \<times> real) list"
  assumes M_pos: "0 < M"
    and sorted: "sorted_wrt (\<lambda>p q. snd p \<le> snd q) xs"
  shows "\<forall>b\<in>set (bp_bucketize_sorted_entries_aux fuel M xs).
    \<forall>p\<in>set (bp_bucket_entries b). bp_marker b \<le> snd p"
  using M_pos sorted
proof (induction fuel arbitrary: xs)
  case 0
  then show ?case
    by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "xs = []")
    case True
    then show ?thesis
      by simp
  next
    case False
    have current:
      "\<forall>p\<in>set (bp_bucket_entries (bp_make_bucket (take M xs))).
        bp_marker (bp_make_bucket (take M xs)) \<le> snd p"
    proof
      fix p
      assume p: "p \<in> set (bp_bucket_entries (bp_make_bucket (take M xs)))"
      then have p_take: "p \<in> set (take M xs)"
        unfolding bp_make_bucket_def by simp
      have sorted_take: "sorted_wrt (\<lambda>p q. snd p \<le> snd q) (take M xs)"
        using Suc.prems by simp
      have take_nonempty: "take M xs \<noteq> []"
        using p_take by (cases "take M xs") auto
      have "snd (hd (take M xs)) \<le> snd p"
        by (rule sorted_wrt_hd_snd_le[OF sorted_take take_nonempty p_take])
      then show "bp_marker (bp_make_bucket (take M xs)) \<le> snd p"
        unfolding bp_make_bucket_def by simp
    qed
    have tail:
      "\<forall>b\<in>set (bp_bucketize_sorted_entries_aux fuel M (drop M xs)).
        \<forall>p\<in>set (bp_bucket_entries b). bp_marker b \<le> snd p"
      by (rule Suc.IH) (use Suc.prems in simp_all)
    show ?thesis
      using False current tail Suc.prems by simp
  qed
qed

lemma bp_bucketize_sorted_entries_markers_lower_bound:
  fixes xs :: "('k \<times> real) list"
  assumes "0 < M"
    and "sorted_wrt (\<lambda>p q. snd p \<le> snd q) xs"
  shows "\<forall>b\<in>set (bp_bucketize_sorted_entries M xs).
    \<forall>p\<in>set (bp_bucket_entries b). bp_marker b \<le> snd p"
  using assms
  unfolding bp_bucketize_sorted_entries_def
  by (rule bp_bucketize_sorted_entries_aux_markers_lower_bound)

lemma bp_bucketize_entries_markers_lower_bound:
  assumes "0 < M"
  shows "\<forall>b\<in>set (bp_bucketize_entries M xs).
    \<forall>p\<in>set (bp_bucket_entries b). bp_marker b \<le> snd p"
  using assms
  unfolding bp_bucketize_entries_def
  by (rule bp_bucketize_sorted_entries_markers_lower_bound) simp

lemma bp_bucketize_sorted_entries_aux_markers_sorted:
  fixes xs :: "('k \<times> real) list"
  assumes M_pos: "0 < M"
    and sorted: "sorted_wrt (\<lambda>p q. snd p \<le> snd q) xs"
  shows "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
    (bp_bucketize_sorted_entries_aux fuel M xs)"
  using M_pos sorted
proof (induction fuel arbitrary: xs)
  case 0
  then show ?case
    by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "xs = []")
    case True
    then show ?thesis
      by simp
  next
    case False
    let ?tail = "bp_bucketize_sorted_entries_aux fuel M (drop M xs)"
    have tail_sorted:
      "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) ?tail"
      by (rule Suc.IH) (use Suc.prems in simp_all)
    have current_le_tail:
      "\<forall>c\<in>set ?tail.
        bp_marker (bp_make_bucket (take M xs)) \<le> bp_marker c"
    proof
      fix c
      assume c: "c \<in> set ?tail"
      obtain p where p_drop: "p \<in> set (drop M xs)"
        and c_marker: "bp_marker c = snd p"
        using bp_bucketize_sorted_entries_aux_marker_in_set[OF c] by auto
      have p_xs: "p \<in> set xs"
        by (meson in_set_dropD p_drop)
      have head_le: "snd (hd xs) \<le> snd p"
        by (rule sorted_wrt_hd_snd_le[OF Suc.prems(2) False p_xs])
      have marker_eq: "bp_marker (bp_make_bucket (take M xs)) = snd (hd xs)"
        using Suc.prems False by (cases xs) (auto simp: bp_make_bucket_def)
      show "bp_marker (bp_make_bucket (take M xs)) \<le> bp_marker c"
        using head_le marker_eq c_marker by simp
    qed
    show ?thesis
      using False tail_sorted current_le_tail Suc.prems by simp
  qed
qed

lemma bp_bucketize_sorted_entries_markers_sorted:
  fixes xs :: "('k \<times> real) list"
  assumes "0 < M"
    and "sorted_wrt (\<lambda>p q. snd p \<le> snd q) xs"
  shows "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
    (bp_bucketize_sorted_entries M xs)"
  using assms
  unfolding bp_bucketize_sorted_entries_def
  by (rule bp_bucketize_sorted_entries_aux_markers_sorted)

lemma bp_bucketize_entries_markers_sorted:
  assumes "0 < M"
  shows "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
    (bp_bucketize_entries M xs)"
  using assms
  unfolding bp_bucketize_entries_def
  by (rule bp_bucketize_sorted_entries_markers_sorted) simp

lemma bp_bucketize_entries_marker_in_set:
  assumes "b \<in> set (bp_bucketize_entries M xs)"
  shows "\<exists>p\<in>set xs. bp_marker b = snd p"
proof -
  obtain p where p_sort: "p \<in> set (sort_key snd xs)"
    and marker: "bp_marker b = snd p"
    using assms
    unfolding bp_bucketize_entries_def bp_bucketize_sorted_entries_def
    by (auto dest: bp_bucketize_sorted_entries_aux_marker_in_set)
  then have "p \<in> set xs"
    by simp
  then show ?thesis
    using marker by auto
qed

lemma bp_bucketize_sorted_entries_aux_boundaries_ok:
  fixes xs :: "('k \<times> real) list"
  assumes M_pos: "0 < M"
    and sorted: "sorted_wrt (\<lambda>p q. snd p \<le> snd q) xs"
  shows "bp_bucket_boundaries_ok
    (bp_bucketize_sorted_entries_aux fuel M xs)"
  using M_pos sorted
proof (induction fuel arbitrary: xs)
  case 0
  then show ?case
    by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "xs = []")
    case True
    then show ?thesis
      by simp
  next
    case False
    let ?tail = "bp_bucketize_sorted_entries_aux fuel M (drop M xs)"
    have tail_boundaries: "bp_bucket_boundaries_ok ?tail"
      by (rule Suc.IH) (use Suc.prems in simp_all)
    show ?thesis
    proof (cases ?tail)
      case Nil
      then show ?thesis
        using False Suc.prems by simp
    next
      case (Cons c cs)
      have c_in: "c \<in> set ?tail"
        using Cons by simp
      obtain q where q_drop: "q \<in> set (drop M xs)"
        and c_marker: "bp_marker c = snd q"
        using bp_bucketize_sorted_entries_aux_marker_in_set[OF c_in] by auto
      have current_before_c:
        "\<forall>p\<in>set (bp_bucket_entries (bp_make_bucket (take M xs))).
          snd p \<le> bp_marker c"
      proof
        fix p
        assume p:
          "p \<in> set (bp_bucket_entries (bp_make_bucket (take M xs)))"
        then have p_take: "p \<in> set (take M xs)"
          unfolding bp_make_bucket_def by simp
        have "snd p \<le> snd q"
          by (rule sorted_wrt_snd_take_drop_le[OF Suc.prems(2) p_take q_drop])
        then show "snd p \<le> bp_marker c"
          using c_marker by simp
      qed
      show ?thesis
        using False Cons tail_boundaries current_before_c Suc.prems by simp
    qed
  qed
qed

lemma bp_bucketize_sorted_entries_boundaries_ok:
  fixes xs :: "('k \<times> real) list"
  assumes "0 < M"
    and "sorted_wrt (\<lambda>p q. snd p \<le> snd q) xs"
  shows "bp_bucket_boundaries_ok (bp_bucketize_sorted_entries M xs)"
  using assms
  unfolding bp_bucketize_sorted_entries_def
  by (rule bp_bucketize_sorted_entries_aux_boundaries_ok)

lemma bp_bucketize_entries_boundaries_ok:
  assumes "0 < M"
  shows "bp_bucket_boundaries_ok (bp_bucketize_entries M xs)"
  using assms
  unfolding bp_bucketize_entries_def
  by (rule bp_bucketize_sorted_entries_boundaries_ok) simp

lemma distinct_map_fst_sort_key:
  assumes "distinct (map fst xs)"
  shows "distinct (map fst (sort_key f xs))"
proof -
  have distinct_sort: "distinct (sort_key f xs)"
    using assms unfolding distinct_map by simp
  have inj: "inj_on fst (set (sort_key f xs))"
    using assms unfolding distinct_map by simp
  show ?thesis
    unfolding distinct_map using distinct_sort inj by simp
qed

lemma bp_rebucket_view [simp]:
  assumes "0 < bp_block_size P"
  shows "bp_view (bp_rebucket P) = bp_view P"
  using assms
  unfolding bp_rebucket_def bp_view_def bp_entries_def
  by simp

lemma bp_rebucket_invariant:
  assumes inv: "bp_invariant P"
  shows "bp_invariant (bp_rebucket P)"
proof -
  let ?M = "bp_block_size P"
  let ?xs = "bp_entries P"
  have M_pos: "0 < ?M"
    using inv unfolding bp_invariant_def by blast
  have distinct_xs: "distinct (map fst ?xs)"
    using inv unfolding bp_invariant_def bp_distinct_keys_def by blast
  have vals:
    "\<forall>p\<in>set ?xs. bp_values P (fst p) = snd p"
    using inv unfolding bp_invariant_def bp_values_consistent_def by blast
  have flat:
    "bp_bucket_entries_flat (bp_bucketize_entries ?M ?xs) = sort_key snd ?xs"
    by (rule bp_bucket_entries_flat_bucketize_entries[OF M_pos])
  have flat_rebucket:
    "bp_entries (bp_rebucket P) = sort_key snd ?xs"
    using flat unfolding bp_rebucket_def bp_entries_def by simp
  have sizes_ok:
    "\<forall>b\<in>set (bp_bucketize_entries ?M ?xs).
      length (bp_bucket_entries b) \<le> ?M"
    by (rule bp_bucketize_entries_sizes_ok[OF M_pos])
  have markers_sorted:
    "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
      (bp_bucketize_entries ?M ?xs)"
    by (rule bp_bucketize_entries_markers_sorted[OF M_pos])
  have markers_lower:
    "\<forall>b\<in>set (bp_bucketize_entries ?M ?xs).
      \<forall>p\<in>set (bp_bucket_entries b). bp_marker b \<le> snd p"
    by (rule bp_bucketize_entries_markers_lower_bound[OF M_pos])
  have set_flat:
    "set (bp_bucket_entries_flat (bp_bucketize_entries ?M ?xs)) = set ?xs"
    by (rule set_bp_bucket_entries_flat_bucketize_entries[OF M_pos])
  show ?thesis
    unfolding bp_invariant_def
  proof (intro conjI)
    show "0 < bp_block_size (bp_rebucket P)"
      using M_pos unfolding bp_rebucket_def by simp
    show "bp_distinct_keys (bp_rebucket P)"
      using distinct_map_fst_sort_key[OF distinct_xs, of snd]
      unfolding bp_distinct_keys_def flat_rebucket by simp
    show "bp_bucket_sizes_ok (bp_rebucket P)"
      using sizes_ok
      unfolding bp_rebucket_def bp_bucket_sizes_ok_def by simp
    show "bp_bucket_markers_sorted (bp_rebucket P)"
      using markers_sorted
      unfolding bp_rebucket_def bp_bucket_markers_sorted_def by simp
    show "bp_bucket_markers_lower_bound (bp_rebucket P)"
      using markers_lower
      unfolding bp_rebucket_def bp_bucket_markers_lower_bound_def by simp
    show "bp_values_consistent (bp_rebucket P)"
      using vals set_flat
      unfolding bp_rebucket_def bp_values_consistent_def bp_entries_def
        bp_entry_keys_def
      by auto
  qed
qed

lemma bp_rebucket_boundaries_state_ok:
  assumes inv: "bp_invariant P"
  shows "bp_bucket_boundaries_state_ok (bp_rebucket P)"
proof -
  have M_pos: "0 < bp_block_size P"
    using inv unfolding bp_invariant_def by blast
  show ?thesis
    using bp_bucketize_entries_boundaries_ok[OF M_pos, of "bp_entries P"]
    unfolding bp_bucket_boundaries_state_ok_def bp_rebucket_def by simp
qed

lemma bp_rebucket_ordered_invariant:
  assumes inv: "bp_invariant P"
  shows "bp_ordered_invariant (bp_rebucket P)"
  unfolding bp_ordered_invariant_def
  using bp_rebucket_invariant[OF inv] bp_rebucket_boundaries_state_ok[OF inv]
  by blast

text \<open>
  Rebucketing is the canonical repair operation.  It sorts the flat entry list
  by value, chunks it into blocks of size @{const bp_block_size}, and rebuilds
  markers from the first entry of each block.  The view theorem
  @{thm bp_rebucket_view} says this repair is observationally invisible at the
  abstract partition interface: keys and remembered values do not change.
  The invariant theorems above then show that rebucketing restores strict
  bucket sizes, sorted markers, lower-bound markers, and adjacent bucket
  boundaries.  Later regularized operations use this fact when a lazy step has
  accumulated enough debt to warrant a rebuild.
\<close>

lemma bp_ordered_invariant_invariant:
  assumes "bp_ordered_invariant P"
  shows "bp_invariant P"
  using assms unfolding bp_ordered_invariant_def by blast

lemma bp_ordered_invariant_boundaries_state_ok:
  assumes "bp_ordered_invariant P"
  shows "bp_bucket_boundaries_state_ok P"
  using assms unfolding bp_ordered_invariant_def by blast

lemma bp_invariant_lazy_invariant:
  assumes inv: "bp_invariant P"
  shows "bp_lazy_invariant P"
proof -
  have lazy_sizes: "bp_lazy_bucket_sizes_ok P"
  proof -
    have "\<forall>b\<in>set (bp_buckets P).
      length (bp_bucket_entries b) \<le> 2 * bp_block_size P"
      using inv unfolding bp_invariant_def bp_bucket_sizes_ok_def
      by auto
    then show ?thesis
      unfolding bp_lazy_bucket_sizes_ok_def .
  qed
  show ?thesis
    using inv lazy_sizes
    unfolding bp_invariant_def bp_lazy_invariant_def
    by blast
qed

lemma bp_ordered_invariant_lazy_ordered_invariant:
  assumes ord: "bp_ordered_invariant P"
  shows "bp_lazy_ordered_invariant P"
  using bp_invariant_lazy_invariant[OF bp_ordered_invariant_invariant[OF ord]]
    bp_ordered_invariant_boundaries_state_ok[OF ord]
  unfolding bp_lazy_ordered_invariant_def by blast

lemma bp_lazy_ordered_invariant_lazy_invariant:
  assumes "bp_lazy_ordered_invariant P"
  shows "bp_lazy_invariant P"
  using assms unfolding bp_lazy_ordered_invariant_def by blast

lemma bp_lazy_ordered_invariant_boundaries_state_ok:
  assumes "bp_lazy_ordered_invariant P"
  shows "bp_bucket_boundaries_state_ok P"
  using assms unfolding bp_lazy_ordered_invariant_def by blast

lemma bp_rebucket_invariant_from_lazy:
  assumes inv: "bp_lazy_invariant P"
  shows "bp_invariant (bp_rebucket P)"
proof -
  let ?M = "bp_block_size P"
  let ?xs = "bp_entries P"
  have M_pos: "0 < ?M"
    using inv unfolding bp_lazy_invariant_def by blast
  have distinct_xs: "distinct (map fst ?xs)"
    using inv unfolding bp_lazy_invariant_def bp_distinct_keys_def by blast
  have vals:
    "\<forall>p\<in>set ?xs. bp_values P (fst p) = snd p"
    using inv unfolding bp_lazy_invariant_def bp_values_consistent_def
    by blast
  have flat:
    "bp_bucket_entries_flat (bp_bucketize_entries ?M ?xs) = sort_key snd ?xs"
    by (rule bp_bucket_entries_flat_bucketize_entries[OF M_pos])
  have flat_rebucket:
    "bp_entries (bp_rebucket P) = sort_key snd ?xs"
    using flat unfolding bp_rebucket_def bp_entries_def by simp
  have sizes_ok:
    "\<forall>b\<in>set (bp_bucketize_entries ?M ?xs).
      length (bp_bucket_entries b) \<le> ?M"
    by (rule bp_bucketize_entries_sizes_ok[OF M_pos])
  have markers_sorted:
    "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
      (bp_bucketize_entries ?M ?xs)"
    by (rule bp_bucketize_entries_markers_sorted[OF M_pos])
  have markers_lower:
    "\<forall>b\<in>set (bp_bucketize_entries ?M ?xs).
      \<forall>p\<in>set (bp_bucket_entries b). bp_marker b \<le> snd p"
    by (rule bp_bucketize_entries_markers_lower_bound[OF M_pos])
  have set_flat:
    "set (bp_bucket_entries_flat (bp_bucketize_entries ?M ?xs)) = set ?xs"
    by (rule set_bp_bucket_entries_flat_bucketize_entries[OF M_pos])
  show ?thesis
    unfolding bp_invariant_def
  proof (intro conjI)
    show "0 < bp_block_size (bp_rebucket P)"
      using M_pos unfolding bp_rebucket_def by simp
    show "bp_distinct_keys (bp_rebucket P)"
      using distinct_map_fst_sort_key[OF distinct_xs, of snd]
      unfolding bp_distinct_keys_def flat_rebucket by simp
    show "bp_bucket_sizes_ok (bp_rebucket P)"
      using sizes_ok
      unfolding bp_rebucket_def bp_bucket_sizes_ok_def by simp
    show "bp_bucket_markers_sorted (bp_rebucket P)"
      using markers_sorted
      unfolding bp_rebucket_def bp_bucket_markers_sorted_def by simp
    show "bp_bucket_markers_lower_bound (bp_rebucket P)"
      using markers_lower
      unfolding bp_rebucket_def bp_bucket_markers_lower_bound_def by simp
    show "bp_values_consistent (bp_rebucket P)"
      using vals set_flat
      unfolding bp_rebucket_def bp_values_consistent_def bp_entries_def
        bp_entry_keys_def
      by auto
  qed
qed

lemma bp_rebucket_boundaries_state_ok_from_lazy:
  assumes inv: "bp_lazy_invariant P"
  shows "bp_bucket_boundaries_state_ok (bp_rebucket P)"
proof -
  have M_pos: "0 < bp_block_size P"
    using inv unfolding bp_lazy_invariant_def by blast
  show ?thesis
    using bp_bucketize_entries_boundaries_ok[OF M_pos, of "bp_entries P"]
    unfolding bp_bucket_boundaries_state_ok_def bp_rebucket_def by simp
qed

lemma bp_rebucket_ordered_invariant_from_lazy:
  assumes inv: "bp_lazy_invariant P"
  shows "bp_ordered_invariant (bp_rebucket P)"
  unfolding bp_ordered_invariant_def
  using bp_rebucket_invariant_from_lazy[OF inv]
    bp_rebucket_boundaries_state_ok_from_lazy[OF inv]
  by blast

lemma set_bp_bucket_entries_flat_local_insert_bucket:
  assumes "0 < M"
  shows "set (bp_bucket_entries_flat (bp_local_insert_bucket M p bs)) =
    insert p (set (bp_bucket_entries_flat bs))"
  using assms
proof (induction bs arbitrary: p)
  case Nil
  have "set (bp_bucket_entries_flat (bp_bucketize_entries M [p])) = set [p]"
    by (rule set_bp_bucket_entries_flat_bucketize_entries[OF Nil.prems])
  then show ?case
    by (simp add: bp_bucket_entries_flat_def)
next
  case (Cons b bs)
  note IH = Cons.IH
  note prems = Cons.prems
  show ?case
  proof (cases bs)
    case Nil
    have single:
      "set (bp_bucket_entries_flat (bp_bucketize_entries M [p])) = {p}"
      using set_bp_bucket_entries_flat_bucketize_entries[OF prems, of "[p]"]
      by simp
    have inserted:
      "set (bp_bucket_entries_flat
        (bp_bucketize_entries M (p # bp_bucket_entries b))) =
       insert p (set (bp_bucket_entries b))"
      using set_bp_bucket_entries_flat_bucketize_entries
        [OF prems, of "p # bp_bucket_entries b"]
      by simp
    then show ?thesis
      using Nil single inserted
      by (auto simp: bp_bucket_entries_flat_def)
  next
    case (Cons c cs)
    have single:
      "set (bp_bucket_entries_flat (bp_bucketize_entries M [p])) = {p}"
      using set_bp_bucket_entries_flat_bucketize_entries[OF prems, of "[p]"]
      by simp
    have inserted:
      "set (bp_bucket_entries_flat
        (bp_bucketize_entries M (p # bp_bucket_entries b))) =
       insert p (set (bp_bucket_entries b))"
      using set_bp_bucket_entries_flat_bucketize_entries
        [OF prems, of "p # bp_bucket_entries b"]
      by simp
    have tail:
      "set (bp_bucket_entries_flat (bp_local_insert_bucket M p bs)) =
       insert p (set (bp_bucket_entries_flat bs))"
      by (rule IH[OF prems])
    then show ?thesis
      using Cons single inserted tail
      by (auto simp: bp_bucket_entries_flat_def)
  qed
qed

lemma set_bp_bucket_entries_flat_lazy_bucket_insert_entries:
  assumes "0 < M"
  shows "set (bp_bucket_entries_flat
      (bp_lazy_bucket_insert_entries M p b)) =
    insert p (set (bp_bucket_entries b))"
proof (cases "length (bp_bucket_entries b) < 2 * M")
  case True
  then show ?thesis
    unfolding bp_lazy_bucket_insert_entries_def bp_bucket_entries_flat_def
    by simp
next
  case False
  have "set (bp_bucket_entries_flat
      (bp_bucketize_entries M (p # bp_bucket_entries b))) =
    set (p # bp_bucket_entries b)"
    by (rule set_bp_bucket_entries_flat_bucketize_entries[OF assms])
  then show ?thesis
    using False unfolding bp_lazy_bucket_insert_entries_def by simp
qed

lemma set_bp_bucket_entries_flat_lazy_insert_bucket:
  assumes "0 < M"
  shows "set (bp_bucket_entries_flat (bp_lazy_insert_bucket M p bs)) =
    insert p (set (bp_bucket_entries_flat bs))"
  using assms
proof (induction bs arbitrary: p)
  case Nil
  have "set (bp_bucket_entries_flat (bp_bucketize_entries M [p])) = set [p]"
    by (rule set_bp_bucket_entries_flat_bucketize_entries[OF Nil.prems])
  then show ?case
    by (simp add: bp_bucket_entries_flat_def)
next
  case (Cons b bs)
  note IH = Cons.IH
  note M_pos = Cons.prems
  show ?case
  proof (cases bs)
    case Nil
    have single:
      "set (bp_bucket_entries_flat (bp_bucketize_entries M [p])) = {p}"
      using set_bp_bucket_entries_flat_bucketize_entries[OF M_pos, of "[p]"]
      by simp
    have inserted:
      "set (bp_bucket_entries_flat
        (bp_lazy_bucket_insert_entries M p b)) =
       insert p (set (bp_bucket_entries b))"
      by (rule set_bp_bucket_entries_flat_lazy_bucket_insert_entries
          [OF M_pos])
    show ?thesis
      using Nil single inserted by (auto simp: bp_bucket_entries_flat_def)
  next
    case (Cons c cs)
    have single:
      "set (bp_bucket_entries_flat (bp_bucketize_entries M [p])) = {p}"
      using set_bp_bucket_entries_flat_bucketize_entries[OF M_pos, of "[p]"]
      by simp
    have inserted:
      "set (bp_bucket_entries_flat
        (bp_lazy_bucket_insert_entries M p b)) =
       insert p (set (bp_bucket_entries b))"
      by (rule set_bp_bucket_entries_flat_lazy_bucket_insert_entries
          [OF M_pos])
    have tail:
      "set (bp_bucket_entries_flat (bp_lazy_insert_bucket M p bs)) =
       insert p (set (bp_bucket_entries_flat bs))"
      by (rule IH[OF M_pos])
    show ?thesis
      using Cons single inserted tail
      by (auto simp: bp_bucket_entries_flat_def)
  qed
qed

lemma length_bp_bucket_entries_flat_lazy_bucket_insert_entries [simp]:
  assumes "0 < M"
  shows "length (bp_bucket_entries_flat
      (bp_lazy_bucket_insert_entries M p b)) =
    Suc (length (bp_bucket_entries b))"
proof (cases "length (bp_bucket_entries b) < 2 * M")
  case True
  then show ?thesis
    unfolding bp_lazy_bucket_insert_entries_def bp_bucket_entries_flat_def
    by simp
next
  case False
  have "length (bp_bucket_entries_flat
      (bp_bucketize_entries M (p # bp_bucket_entries b))) =
    length (p # bp_bucket_entries b)"
    using bp_bucket_entries_flat_bucketize_entries
      [OF assms, of "p # bp_bucket_entries b"]
    by simp
  then show ?thesis
    using False unfolding bp_lazy_bucket_insert_entries_def by simp
qed

lemma length_bp_bucket_entries_flat_lazy_insert_bucket [simp]:
  assumes "0 < M"
  shows "length (bp_bucket_entries_flat (bp_lazy_insert_bucket M p bs)) =
    Suc (length (bp_bucket_entries_flat bs))"
  using assms
proof (induction bs arbitrary: p)
  case Nil
  have len:
    "length (bp_bucket_entries_flat (bp_bucketize_entries M [p])) =
      length [p]"
    using bp_bucket_entries_flat_bucketize_entries[OF Nil.prems, of "[p]"]
    by simp
  show ?case
    using len by (simp add: bp_bucket_entries_flat_def)
next
  case (Cons b bs)
  note IH = Cons.IH
  note M_pos = Cons.prems
  show ?case
  proof (cases bs)
    case Nil
    have len_single:
      "length (bp_bucket_entries_flat (bp_bucketize_entries M [p])) =
        length [p]"
      using bp_bucket_entries_flat_bucketize_entries[OF M_pos, of "[p]"]
      by simp
    have len_inserted:
      "length (bp_bucket_entries_flat
          (bp_lazy_bucket_insert_entries M p b)) =
        Suc (length (bp_bucket_entries b))"
      by (rule length_bp_bucket_entries_flat_lazy_bucket_insert_entries
          [OF M_pos])
    show ?thesis
      using Nil len_single len_inserted
      by (auto simp: bp_bucket_entries_flat_def)
  next
    case (Cons c cs)
    have len_single:
      "length (bp_bucket_entries_flat (bp_bucketize_entries M [p])) =
        length [p]"
      using bp_bucket_entries_flat_bucketize_entries[OF M_pos, of "[p]"]
      by simp
    have len_inserted:
      "length (bp_bucket_entries_flat
          (bp_lazy_bucket_insert_entries M p b)) =
        Suc (length (bp_bucket_entries b))"
      by (rule length_bp_bucket_entries_flat_lazy_bucket_insert_entries
          [OF M_pos])
    have tail_len:
      "length (bp_bucket_entries_flat
          (bp_lazy_insert_bucket M p (c # cs))) =
        Suc (length (bp_bucket_entries_flat (c # cs)))"
      using IH[OF M_pos, of p] Cons by simp
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      then show ?thesis
        using Cons len_single by (simp add: bp_bucket_entries_flat_def)
    next
      case False
      show ?thesis
      proof (cases "snd p < bp_marker c")
        case True
        then show ?thesis
          using Cons False len_inserted
          by (simp add: bp_bucket_entries_flat_def)
      next
        case False
        then show ?thesis
          using Cons \<open>\<not> snd p < bp_marker b\<close> tail_len
          by (simp add: bp_bucket_entries_flat_def)
      qed
    qed
  qed
qed

lemma bp_lazy_insert_bucket_distinct_keys:
  assumes M_pos: "0 < M"
    and distinct: "distinct (map fst (bp_bucket_entries_flat bs))"
    and fresh: "fst p \<notin> bp_entry_keys (bp_bucket_entries_flat bs)"
  shows "distinct
    (map fst (bp_bucket_entries_flat (bp_lazy_insert_bucket M p bs)))"
proof (rule card_distinct)
  let ?old = "map fst (bp_bucket_entries_flat bs)"
  let ?new =
    "map fst (bp_bucket_entries_flat (bp_lazy_insert_bucket M p bs))"
  have set_new: "set ?new = insert (fst p) (set ?old)"
    using set_bp_bucket_entries_flat_lazy_insert_bucket[OF M_pos, of p bs]
    by auto
  have fresh_set: "fst p \<notin> set ?old"
    using fresh unfolding bp_entry_keys_def by simp
  have "card (set ?new) = Suc (card (set ?old))"
    unfolding set_new using fresh_set by simp
  also have "\<dots> = Suc (length ?old)"
    using distinct_card[OF distinct] by simp
  also have "\<dots> = length ?new"
    using length_bp_bucket_entries_flat_lazy_insert_bucket[OF M_pos, of p bs]
    by simp
  finally show "card (set ?new) = length ?new" .
qed

lemma bp_lazy_bucket_insert_entries_sizes_ok:
  assumes M_pos: "0 < M"
    and size: "length (bp_bucket_entries b) \<le> 2 * M"
  shows "\<forall>c\<in>set (bp_lazy_bucket_insert_entries M p b).
    length (bp_bucket_entries c) \<le> 2 * M"
proof (cases "length (bp_bucket_entries b) < 2 * M")
  case True
  then have "length (p # bp_bucket_entries b) \<le> 2 * M"
    by simp
  then show ?thesis
    using True unfolding bp_lazy_bucket_insert_entries_def by simp
next
  case False
  have strict_sizes:
    "\<forall>c\<in>set (bp_bucketize_entries M (p # bp_bucket_entries b)).
      length (bp_bucket_entries c) \<le> M"
    by (rule bp_bucketize_entries_sizes_ok[OF M_pos])
  have "\<forall>c\<in>set (bp_bucketize_entries M (p # bp_bucket_entries b)).
      length (bp_bucket_entries c) \<le> 2 * M"
    using strict_sizes by auto
  then show ?thesis
    using False unfolding bp_lazy_bucket_insert_entries_def by simp
qed

lemma bp_lazy_insert_bucket_sizes_ok:
  assumes M_pos: "0 < M"
    and sizes: "\<forall>b\<in>set bs. length (bp_bucket_entries b) \<le> 2 * M"
  shows "\<forall>b\<in>set (bp_lazy_insert_bucket M p bs).
    length (bp_bucket_entries b) \<le> 2 * M"
  using sizes
proof (induction bs arbitrary: p)
  case Nil
  have strict:
    "\<forall>b\<in>set (bp_bucketize_entries M [p]).
      length (bp_bucket_entries b) \<le> M"
    by (rule bp_bucketize_entries_sizes_ok[OF M_pos])
  then show ?case
    using M_pos by auto
next
  case (Cons b bs)
  note IH = Cons.IH
  note prems = Cons.prems
  show ?case
  proof (cases bs)
    case Nil
    have single:
      "\<forall>b\<in>set (bp_bucketize_entries M [p]).
        length (bp_bucket_entries b) \<le> 2 * M"
      using bp_bucketize_entries_sizes_ok[OF M_pos, of "[p]"] by auto
    have inserted:
      "\<forall>c\<in>set (bp_lazy_bucket_insert_entries M p b).
        length (bp_bucket_entries c) \<le> 2 * M"
      by (rule bp_lazy_bucket_insert_entries_sizes_ok[OF M_pos])
        (use prems Nil in simp)
    have b_size: "length (bp_bucket_entries b) \<le> 2 * M"
      using prems by simp
    then show ?thesis
      using Nil single inserted b_size by auto
  next
    case (Cons c cs)
    have tail_sizes:
      "\<forall>b\<in>set bs. length (bp_bucket_entries b) \<le> 2 * M"
      using prems by simp
    have single:
      "\<forall>b\<in>set (bp_bucketize_entries M [p]).
        length (bp_bucket_entries b) \<le> 2 * M"
      using bp_bucketize_entries_sizes_ok[OF M_pos, of "[p]"] by auto
    have inserted:
      "\<forall>d\<in>set (bp_lazy_bucket_insert_entries M p b).
        length (bp_bucket_entries d) \<le> 2 * M"
      by (rule bp_lazy_bucket_insert_entries_sizes_ok[OF M_pos])
        (use prems Cons in simp)
    show ?thesis
      using IH[of p, OF tail_sizes] prems Cons single inserted by auto
  qed
qed

lemma bp_local_insert_bucket_sizes_ok:
  assumes M_pos: "0 < M"
    and sizes: "\<forall>b\<in>set bs. length (bp_bucket_entries b) \<le> M"
  shows "\<forall>b\<in>set (bp_local_insert_bucket M p bs).
    length (bp_bucket_entries b) \<le> M"
  using sizes
proof (induction bs arbitrary: p)
  case Nil
  have "\<forall>b\<in>set (bp_bucketize_entries M [p]).
    length (bp_bucket_entries b) \<le> M"
    by (rule bp_bucketize_entries_sizes_ok[OF M_pos])
  then show ?case
    by simp
next
  case (Cons b bs)
  note IH = Cons.IH
  note prems = Cons.prems
  show ?case
  proof (cases bs)
    case Nil
    then show ?thesis
      using prems bp_bucketize_entries_sizes_ok[OF M_pos, of "[p]"]
        bp_bucketize_entries_sizes_ok[OF M_pos, of "p # bp_bucket_entries b"]
      by auto
  next
    case (Cons c cs)
    have tail_sizes:
      "\<forall>b\<in>set bs. length (bp_bucket_entries b) \<le> M"
      using prems by simp
    show ?thesis
      using IH[of p, OF tail_sizes] prems Cons
        bp_bucketize_entries_sizes_ok[OF M_pos, of "[p]"]
        bp_bucketize_entries_sizes_ok[OF M_pos, of "p # bp_bucket_entries b"]
      by auto
  qed
qed

lemma bp_local_insert_bucket_markers_lower_bound:
  assumes M_pos: "0 < M"
    and lower: "\<forall>b\<in>set bs. \<forall>p\<in>set (bp_bucket_entries b).
      bp_marker b \<le> snd p"
  shows "\<forall>b\<in>set (bp_local_insert_bucket M p bs).
    \<forall>q\<in>set (bp_bucket_entries b). bp_marker b \<le> snd q"
  using lower
proof (induction bs arbitrary: p)
  case Nil
  have "\<forall>b\<in>set (bp_bucketize_entries M [p]).
    \<forall>q\<in>set (bp_bucket_entries b). bp_marker b \<le> snd q"
    by (rule bp_bucketize_entries_markers_lower_bound[OF M_pos])
  then show ?case
    by simp
next
  case (Cons b bs)
  note IH = Cons.IH
  note prems = Cons.prems
  show ?case
  proof (cases bs)
    case Nil
    then show ?thesis
      using prems bp_bucketize_entries_markers_lower_bound[OF M_pos, of "[p]"]
        bp_bucketize_entries_markers_lower_bound
          [OF M_pos, of "p # bp_bucket_entries b"]
      by auto
  next
    case (Cons c cs)
    have tail_lower:
      "\<forall>b\<in>set bs. \<forall>p\<in>set (bp_bucket_entries b).
        bp_marker b \<le> snd p"
      using prems by simp
    show ?thesis
      using IH[of p, OF tail_lower] prems Cons
        bp_bucketize_entries_markers_lower_bound[OF M_pos, of "[p]"]
        bp_bucketize_entries_markers_lower_bound
          [OF M_pos, of "p # bp_bucket_entries b"]
      by auto
  qed
qed

lemma bp_lazy_bucket_insert_entries_markers_lower_bound:
  assumes M_pos: "0 < M"
    and lower: "\<forall>q\<in>set (bp_bucket_entries b). bp_marker b \<le> snd q"
    and p_ge: "bp_marker b \<le> snd p"
  shows "\<forall>c\<in>set (bp_lazy_bucket_insert_entries M p b).
    \<forall>q\<in>set (bp_bucket_entries c). bp_marker c \<le> snd q"
proof (cases "length (bp_bucket_entries b) < 2 * M")
  case True
  then show ?thesis
    using lower p_ge unfolding bp_lazy_bucket_insert_entries_def by auto
next
  case False
  have "\<forall>c\<in>set (bp_bucketize_entries M (p # bp_bucket_entries b)).
    \<forall>q\<in>set (bp_bucket_entries c). bp_marker c \<le> snd q"
    by (rule bp_bucketize_entries_markers_lower_bound[OF M_pos])
  then show ?thesis
    using False unfolding bp_lazy_bucket_insert_entries_def by simp
qed

lemma bp_lazy_insert_bucket_markers_lower_bound:
  assumes M_pos: "0 < M"
    and lower: "\<forall>b\<in>set bs. \<forall>p\<in>set (bp_bucket_entries b).
      bp_marker b \<le> snd p"
  shows "\<forall>b\<in>set (bp_lazy_insert_bucket M p bs).
    \<forall>q\<in>set (bp_bucket_entries b). bp_marker b \<le> snd q"
  using lower
proof (induction bs arbitrary: p)
  case Nil
  show ?case
    by (simp add: bp_bucketize_entries_markers_lower_bound[OF M_pos])
next
  case (Cons b bs)
  note IH = Cons.IH
  note prems = Cons.prems
  show ?case
  proof (cases bs)
    case Nil
    have single:
      "\<forall>b\<in>set (bp_bucketize_entries M [p]).
        \<forall>q\<in>set (bp_bucket_entries b). bp_marker b \<le> snd q"
      by (rule bp_bucketize_entries_markers_lower_bound[OF M_pos])
    have b_lower:
      "\<forall>q\<in>set (bp_bucket_entries b). bp_marker b \<le> snd q"
      using prems by simp
    have inserted:
      "bp_marker b \<le> snd p \<Longrightarrow>
        \<forall>c\<in>set (bp_lazy_bucket_insert_entries M p b).
          \<forall>q\<in>set (bp_bucket_entries c). bp_marker c \<le> snd q"
      by (rule bp_lazy_bucket_insert_entries_markers_lower_bound
          [OF M_pos b_lower])
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      show ?thesis
        using Nil True single b_lower by auto
    next
      case False
      have p_ge_b: "bp_marker b \<le> snd p"
        using False by simp
      show ?thesis
        using Nil False inserted[OF p_ge_b] by simp
    qed
  next
    case (Cons c cs)
    have tail_lower:
      "\<forall>b\<in>set bs. \<forall>p\<in>set (bp_bucket_entries b).
        bp_marker b \<le> snd p"
      using prems by simp
    have single:
      "\<forall>b\<in>set (bp_bucketize_entries M [p]).
        \<forall>q\<in>set (bp_bucket_entries b). bp_marker b \<le> snd q"
      by (rule bp_bucketize_entries_markers_lower_bound[OF M_pos])
    have b_lower:
      "\<forall>q\<in>set (bp_bucket_entries b). bp_marker b \<le> snd q"
      using prems by simp
    have inserted:
      "bp_marker b \<le> snd p \<Longrightarrow>
        \<forall>d\<in>set (bp_lazy_bucket_insert_entries M p b).
          \<forall>q\<in>set (bp_bucket_entries d). bp_marker d \<le> snd q"
      by (rule bp_lazy_bucket_insert_entries_markers_lower_bound
          [OF M_pos b_lower])
    have tail: "\<forall>b\<in>set (bp_lazy_insert_bucket M p bs).
        \<forall>q\<in>set (bp_bucket_entries b). bp_marker b \<le> snd q"
      by (rule IH[OF tail_lower])
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      have result:
        "bp_lazy_insert_bucket M p (b # bs) =
          bp_bucketize_entries M [p] @ b # bs"
        using True Cons by simp
      show ?thesis
        unfolding result
        using single prems Cons by auto
    next
      case False
      have p_ge_b: "bp_marker b \<le> snd p"
        using False by simp
      show ?thesis
      proof (cases "snd p < bp_marker c")
        case True
        have result:
        "bp_lazy_insert_bucket M p (b # bs) =
            bp_lazy_bucket_insert_entries M p b @ bs"
          using False True Cons by simp
        show ?thesis
          unfolding result
          using inserted[OF p_ge_b] prems Cons by auto
      next
        case False
        have result:
          "bp_lazy_insert_bucket M p (b # bs) =
            b # bp_lazy_insert_bucket M p bs"
          using \<open>\<not> snd p < bp_marker b\<close> False Cons by simp
        show ?thesis
          unfolding result
          using tail prems Cons by auto
      qed
    qed
  qed
qed

lemma bp_bucketize_entries_markers_le:
  fixes beta :: real
  assumes "\<forall>q\<in>set xs. snd q \<le> beta"
  shows "\<forall>b\<in>set (bp_bucketize_entries M xs). bp_marker b \<le> beta"
proof
  fix b
  assume b: "b \<in> set (bp_bucketize_entries M xs)"
  obtain q where q: "q \<in> set xs" and marker: "bp_marker b = snd q"
    using bp_bucketize_entries_marker_in_set[OF b] by auto
  have "snd q \<le> beta"
    using assms q by blast
  show "bp_marker b \<le> beta"
    using marker \<open>snd q \<le> beta\<close> by simp
qed

lemma bp_bucketize_entries_markers_ge:
  fixes alpha :: real
  assumes "\<forall>q\<in>set xs. alpha \<le> snd q"
  shows "\<forall>b\<in>set (bp_bucketize_entries M xs). alpha \<le> bp_marker b"
proof
  fix b
  assume b: "b \<in> set (bp_bucketize_entries M xs)"
  obtain q where q: "q \<in> set xs" and marker: "bp_marker b = snd q"
    using bp_bucketize_entries_marker_in_set[OF b] by auto
  have "alpha \<le> snd q"
    using assms q by blast
  show "alpha \<le> bp_marker b"
    using marker \<open>alpha \<le> snd q\<close> by simp
qed

lemma bp_bucketize_entries_entry_in_source:
  assumes M_pos: "0 < M"
    and b: "b \<in> set (bp_bucketize_entries M xs)"
    and q: "q \<in> set (bp_bucket_entries b)"
  shows "q \<in> set xs"
proof -
  have "q \<in> set (bp_bucket_entries_flat (bp_bucketize_entries M xs))"
    using b q unfolding bp_bucket_entries_flat_def by auto
  then show ?thesis
    using set_bp_bucket_entries_flat_bucketize_entries[OF M_pos, of xs]
    by simp
qed

lemma bp_bucketize_entries_nonempty:
  assumes "0 < M" and "xs \<noteq> []"
  shows "bp_bucketize_entries M xs \<noteq> []"
proof
  assume empty: "bp_bucketize_entries M xs = []"
  have "set (bp_bucket_entries_flat (bp_bucketize_entries M xs)) = set xs"
    by (rule set_bp_bucket_entries_flat_bucketize_entries[OF assms(1)])
  then have "set xs = {}"
    using empty unfolding bp_bucket_entries_flat_def by simp
  then show False
    using assms(2) by auto
qed

lemma bp_local_insert_bucket_nonempty:
  assumes "0 < M"
  shows "bp_local_insert_bucket M p bs \<noteq> []"
  using assms
proof (induction bs arbitrary: p)
  case Nil
  then show ?case
    by (simp add: bp_bucketize_entries_nonempty)
next
  case (Cons b bs)
  then show ?case
  proof (cases bs)
    case Nil
    then show ?thesis
      using Cons.prems by (simp add: bp_bucketize_entries_nonempty)
  next
    case (Cons c cs)
    then show ?thesis
      using Cons by (simp add: bp_bucketize_entries_nonempty)
  qed
qed

lemma bp_bucket_boundaries_ok_append:
  assumes left: "bp_bucket_boundaries_ok xs"
    and right: "bp_bucket_boundaries_ok ys"
    and cross: "ys \<noteq> [] \<Longrightarrow>
      \<forall>b\<in>set xs. \<forall>p\<in>set (bp_bucket_entries b).
        snd p \<le> bp_marker (hd ys)"
  shows "bp_bucket_boundaries_ok (xs @ ys)"
  using left cross
proof (induction xs)
  case Nil
  then show ?case
    using right by simp
next
  case (Cons b xs)
  note outer_left = Cons.prems(1)
  note outer_cross = Cons.prems(2)
  note outer_IH = Cons.IH
  show ?case
  proof (cases xs)
    case Nil
    show ?thesis
    proof (cases ys)
      case Nil
      then show ?thesis
        using \<open>xs = []\<close> by simp
    next
      case (Cons c cs)
      have cross_all:
        "\<forall>d\<in>set (b # xs). \<forall>p\<in>set (bp_bucket_entries d).
          snd p \<le> bp_marker (hd ys)"
        using outer_cross Cons by simp
      have "\<forall>p\<in>set (bp_bucket_entries b). snd p \<le> bp_marker c"
        using cross_all Cons unfolding \<open>xs = []\<close> by simp
      then show ?thesis
        using right Cons \<open>xs = []\<close> by simp
    qed
  next
    case (Cons c cs)
    have head_boundary:
      "\<forall>p\<in>set (bp_bucket_entries b). snd p \<le> bp_marker c"
      using outer_left Cons by simp
    have tail_boundaries: "bp_bucket_boundaries_ok (xs @ ys)"
    proof (rule outer_IH)
      show "bp_bucket_boundaries_ok xs"
        using outer_left Cons by simp
      show "ys \<noteq> [] \<Longrightarrow>
        \<forall>b\<in>set xs. \<forall>p\<in>set (bp_bucket_entries b).
          snd p \<le> bp_marker (hd ys)"
        using outer_cross by simp
    qed
    show ?thesis
      using Cons head_boundary tail_boundaries by simp
  qed
qed

lemma bp_bucket_boundaries_ok_bucketize_append_Cons:
  assumes M_pos: "0 < M"
    and tail: "bp_bucket_boundaries_ok (c # bs)"
    and upper: "\<forall>q\<in>set xs. snd q \<le> bp_marker c"
  shows "bp_bucket_boundaries_ok (bp_bucketize_entries M xs @ c # bs)"
proof (rule bp_bucket_boundaries_ok_append)
  show "bp_bucket_boundaries_ok (bp_bucketize_entries M xs)"
    by (rule bp_bucketize_entries_boundaries_ok[OF M_pos])
  show "bp_bucket_boundaries_ok (c # bs)"
    by (rule tail)
  show "c # bs \<noteq> [] \<Longrightarrow>
    \<forall>b\<in>set (bp_bucketize_entries M xs).
      \<forall>p\<in>set (bp_bucket_entries b). snd p \<le> bp_marker (hd (c # bs))"
  proof
    fix b
    assume b: "b \<in> set (bp_bucketize_entries M xs)"
    show "\<forall>p\<in>set (bp_bucket_entries b). snd p \<le> bp_marker (hd (c # bs))"
    proof
      fix p
      assume p: "p \<in> set (bp_bucket_entries b)"
      have "p \<in> set xs"
        by (rule bp_bucketize_entries_entry_in_source[OF M_pos b p])
      then show "snd p \<le> bp_marker (hd (c # bs))"
        using upper by simp
    qed
  qed
qed

lemma bp_lazy_bucket_insert_entries_nonempty:
  assumes M_pos: "0 < M"
  shows "bp_lazy_bucket_insert_entries M p b \<noteq> []"
proof (cases "length (bp_bucket_entries b) < 2 * M")
  case True
  then show ?thesis
    unfolding bp_lazy_bucket_insert_entries_def by simp
next
  case False
  have "bp_bucketize_entries M (p # bp_bucket_entries b) \<noteq> []"
    by (rule bp_bucketize_entries_nonempty[OF M_pos]) simp
  then show ?thesis
    using False unfolding bp_lazy_bucket_insert_entries_def by simp
qed

lemma bp_lazy_insert_bucket_nonempty:
  assumes M_pos: "0 < M"
  shows "bp_lazy_insert_bucket M p bs \<noteq> []"
  using assms
proof (induction bs arbitrary: p)
  case Nil
  then show ?case
    by (simp add: bp_bucketize_entries_nonempty)
next
  case (Cons b bs)
  note IH = Cons.IH
  note M_pos = Cons.prems
  show ?case
  proof (cases bs)
    case Nil
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      then show ?thesis
        using Nil by (simp add: bp_bucketize_entries_nonempty[OF M_pos])
    next
      case False
      then show ?thesis
        using Nil bp_lazy_bucket_insert_entries_nonempty[OF M_pos, of p b]
        by simp
    qed
  next
    case (Cons c cs)
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      then show ?thesis
        using Cons by (simp add: bp_bucketize_entries_nonempty[OF M_pos])
    next
      case False
      show ?thesis
      proof (cases "snd p < bp_marker c")
        case True
        then show ?thesis
          using Cons False bp_lazy_bucket_insert_entries_nonempty
            [OF M_pos, of p b]
          by simp
      next
        case False
        then show ?thesis
          using Cons \<open>\<not> snd p < bp_marker b\<close> IH[OF M_pos, of p]
          by simp
      qed
    qed
  qed
qed

lemma bp_lazy_bucket_insert_entries_markers_sorted:
  assumes M_pos: "0 < M"
  shows "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
    (bp_lazy_bucket_insert_entries M p b)"
proof (cases "length (bp_bucket_entries b) < 2 * M")
  case True
  then show ?thesis
    unfolding bp_lazy_bucket_insert_entries_def by simp
next
  case False
  have "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
      (bp_bucketize_entries M (p # bp_bucket_entries b))"
    by (rule bp_bucketize_entries_markers_sorted[OF M_pos])
  then show ?thesis
    using False unfolding bp_lazy_bucket_insert_entries_def by simp
qed

lemma bp_lazy_bucket_insert_entries_markers_ge:
  fixes alpha :: real
  assumes M_pos: "0 < M"
    and lower: "\<forall>q\<in>set (bp_bucket_entries b). bp_marker b \<le> snd q"
    and p_ge: "bp_marker b \<le> snd p"
    and alpha_le: "alpha \<le> bp_marker b"
  shows "\<forall>c\<in>set (bp_lazy_bucket_insert_entries M p b).
    alpha \<le> bp_marker c"
proof (cases "length (bp_bucket_entries b) < 2 * M")
  case True
  then show ?thesis
    using alpha_le unfolding bp_lazy_bucket_insert_entries_def by simp
next
  case False
  have entries_ge:
    "\<forall>q\<in>set (p # bp_bucket_entries b). alpha \<le> snd q"
    using lower p_ge alpha_le by auto
  have "\<forall>c\<in>set (bp_bucketize_entries M (p # bp_bucket_entries b)).
    alpha \<le> bp_marker c"
    by (rule bp_bucketize_entries_markers_ge[OF entries_ge])
  then show ?thesis
    using False unfolding bp_lazy_bucket_insert_entries_def by simp
qed

lemma bp_lazy_bucket_insert_entries_markers_le:
  fixes beta :: real
  assumes M_pos: "0 < M"
    and marker_le: "bp_marker b \<le> beta"
    and upper: "\<forall>q\<in>set (p # bp_bucket_entries b). snd q \<le> beta"
  shows "\<forall>c\<in>set (bp_lazy_bucket_insert_entries M p b).
    bp_marker c \<le> beta"
proof (cases "length (bp_bucket_entries b) < 2 * M")
  case True
  then show ?thesis
    using marker_le unfolding bp_lazy_bucket_insert_entries_def by simp
next
  case False
  have "\<forall>c\<in>set (bp_bucketize_entries M (p # bp_bucket_entries b)).
    bp_marker c \<le> beta"
    by (rule bp_bucketize_entries_markers_le[OF upper])
  then show ?thesis
    using False unfolding bp_lazy_bucket_insert_entries_def by simp
qed

lemma bp_lazy_bucket_insert_entries_entries_le:
  fixes beta :: real
  assumes M_pos: "0 < M"
    and upper: "\<forall>q\<in>set (p # bp_bucket_entries b). snd q \<le> beta"
  shows "\<forall>c\<in>set (bp_lazy_bucket_insert_entries M p b).
    \<forall>q\<in>set (bp_bucket_entries c). snd q \<le> beta"
proof (cases "length (bp_bucket_entries b) < 2 * M")
  case True
  show ?thesis
  proof
    fix c
    assume c: "c \<in> set (bp_lazy_bucket_insert_entries M p b)"
    show "\<forall>q\<in>set (bp_bucket_entries c). snd q \<le> beta"
    proof
      fix q
      assume q: "q \<in> set (bp_bucket_entries c)"
      have "q \<in> set (p # bp_bucket_entries b)"
        using True c q unfolding bp_lazy_bucket_insert_entries_def by auto
      then show "snd q \<le> beta"
        using upper by blast
    qed
  qed
next
  case False
  show ?thesis
  proof
    fix c
    assume c:
      "c \<in> set (bp_lazy_bucket_insert_entries M p b)"
    show "\<forall>q\<in>set (bp_bucket_entries c). snd q \<le> beta"
    proof
      fix q
      assume q: "q \<in> set (bp_bucket_entries c)"
      have c_bucketize:
        "c \<in> set (bp_bucketize_entries M (p # bp_bucket_entries b))"
        using c False unfolding bp_lazy_bucket_insert_entries_def by simp
      have "q \<in> set (p # bp_bucket_entries b)"
        by (rule bp_bucketize_entries_entry_in_source
            [OF M_pos c_bucketize q])
      then show "snd q \<le> beta"
        using upper by blast
    qed
  qed
qed

lemma bp_lazy_bucket_insert_entries_boundaries_ok:
  assumes M_pos: "0 < M"
  shows "bp_bucket_boundaries_ok (bp_lazy_bucket_insert_entries M p b)"
proof (cases "length (bp_bucket_entries b) < 2 * M")
  case True
  then show ?thesis
    unfolding bp_lazy_bucket_insert_entries_def by simp
next
  case False
  have "bp_bucket_boundaries_ok
      (bp_bucketize_entries M (p # bp_bucket_entries b))"
    by (rule bp_bucketize_entries_boundaries_ok[OF M_pos])
  then show ?thesis
    using False unfolding bp_lazy_bucket_insert_entries_def by simp
qed

lemma bp_lazy_insert_bucket_markers_ge_hd:
  assumes M_pos: "0 < M"
    and sorted: "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) bs"
    and lower: "\<forall>b\<in>set bs. \<forall>q\<in>set (bp_bucket_entries b).
      bp_marker b \<le> snd q"
    and nonempty: "bs \<noteq> []"
    and p_ge: "bp_marker (hd bs) \<le> snd p"
  shows "\<forall>b\<in>set (bp_lazy_insert_bucket M p bs).
    bp_marker (hd bs) \<le> bp_marker b"
  using sorted lower nonempty p_ge
proof (induction bs arbitrary: p)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  note IH = Cons.IH
  note sorted = Cons.prems(1)
  note lower = Cons.prems(2)
  note p_ge = Cons.prems(4)
  show ?case
  proof (cases bs)
    case Nil
    have p_ge_b: "bp_marker b \<le> snd p"
      using p_ge by simp
    have inserted_ge:
      "\<forall>c\<in>set (bp_lazy_bucket_insert_entries M p b).
        bp_marker b \<le> bp_marker c"
    proof (rule bp_lazy_bucket_insert_entries_markers_ge
        [where alpha = "bp_marker b", OF M_pos _ p_ge_b])
      show "\<forall>q\<in>set (bp_bucket_entries b). bp_marker b \<le> snd q"
        using lower Nil by simp
      show "bp_marker b \<le> bp_marker b"
        by simp
    qed
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      then show ?thesis
        using p_ge by simp
    next
      case False
      then show ?thesis
        using Nil inserted_ge by simp
    qed
  next
    case (Cons c cs)
    have sorted_tail:
      "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) (c # cs)"
      using sorted Cons by simp
    have lower_tail:
      "\<forall>b\<in>set (c # cs). \<forall>q\<in>set (bp_bucket_entries b).
        bp_marker b \<le> snd q"
      using lower Cons by simp
    have b_le_c: "bp_marker b \<le> bp_marker c"
      using sorted Cons by simp
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      then show ?thesis
        using p_ge by simp
    next
      case False
      show ?thesis
      proof (cases "snd p < bp_marker c")
        case True
        have p_ge_b: "bp_marker b \<le> snd p"
          using False by simp
        have inserted_ge:
          "\<forall>d\<in>set (bp_lazy_bucket_insert_entries M p b).
            bp_marker b \<le> bp_marker d"
        proof (rule bp_lazy_bucket_insert_entries_markers_ge
            [where alpha = "bp_marker b", OF M_pos])
          show "\<forall>q\<in>set (bp_bucket_entries b). bp_marker b \<le> snd q"
            using lower Cons by simp
          show "bp_marker b \<le> snd p"
            by (rule p_ge_b)
          show "bp_marker b \<le> bp_marker b"
            by simp
        qed
        have tail_ge:
          "\<forall>d\<in>set (c # cs). bp_marker b \<le> bp_marker d"
          using sorted Cons by auto
        show ?thesis
          using Cons False True inserted_ge tail_ge by auto
      next
        case False
        have p_ge_c: "bp_marker c \<le> snd p"
          using False by simp
        have tail_ge_c:
          "\<forall>d\<in>set (bp_lazy_insert_bucket M p (c # cs)).
            bp_marker c \<le> bp_marker d"
          using IH[of p] sorted_tail lower_tail p_ge_c Cons by auto
        have tail_ge_b:
          "\<forall>d\<in>set (bp_lazy_insert_bucket M p (c # cs)).
            bp_marker b \<le> bp_marker d"
          using b_le_c tail_ge_c by force
        show ?thesis
          using Cons \<open>\<not> snd p < bp_marker b\<close> False tail_ge_b by simp
      qed
    qed
  qed
qed

lemma bp_lazy_insert_bucket_markers_sorted:
  assumes M_pos: "0 < M"
    and sorted: "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) bs"
    and lower: "\<forall>b\<in>set bs. \<forall>q\<in>set (bp_bucket_entries b).
      bp_marker b \<le> snd q"
    and boundaries: "bp_bucket_boundaries_ok bs"
  shows "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
    (bp_lazy_insert_bucket M p bs)"
  using sorted lower boundaries
proof (induction bs arbitrary: p)
  case Nil
  then show ?case
    by (simp add: bp_bucketize_entries_markers_sorted[OF M_pos])
next
  case (Cons b bs)
  note IH = Cons.IH
  note sorted = Cons.prems(1)
  note lower = Cons.prems(2)
  note boundaries = Cons.prems(3)
  show ?case
  proof (cases bs)
    case Nil
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      have left_sorted:
        "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
          (bp_bucketize_entries M [p])"
        by (rule bp_bucketize_entries_markers_sorted[OF M_pos])
      have left_le_b:
        "\<forall>x\<in>set (bp_bucketize_entries M [p]).
          bp_marker x \<le> bp_marker b"
        by (rule bp_bucketize_entries_markers_le) (use True in simp)
      show ?thesis
        using Nil True left_sorted left_le_b
        by (simp add: sorted_wrt_append)
    next
      case False
      show ?thesis
        using Nil False
          bp_lazy_bucket_insert_entries_markers_sorted[OF M_pos, of p b]
        by simp
    qed
  next
    case (Cons c cs)
    have sorted_tail:
      "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) (c # cs)"
      using sorted Cons by simp
    have lower_tail:
      "\<forall>b\<in>set (c # cs). \<forall>q\<in>set (bp_bucket_entries b).
        bp_marker b \<le> snd q"
      using lower Cons by simp
    have boundaries_tail: "bp_bucket_boundaries_ok (c # cs)"
      using boundaries Cons by simp
    have b_le_c: "bp_marker b \<le> bp_marker c"
      using sorted Cons by simp
    have b_le_all:
      "\<forall>d\<in>set (b # c # cs). bp_marker b \<le> bp_marker d"
      using sorted Cons by auto
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      have left_sorted:
        "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
          (bp_bucketize_entries M [p])"
        by (rule bp_bucketize_entries_markers_sorted[OF M_pos])
      have right_sorted:
        "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) (b # c # cs)"
        using sorted Cons by simp
      have left_le_b:
        "\<forall>x\<in>set (bp_bucketize_entries M [p]).
          bp_marker x \<le> bp_marker b"
        by (rule bp_bucketize_entries_markers_le) (use True in simp)
      have cross:
        "\<forall>x\<in>set (bp_bucketize_entries M [p]).
          \<forall>y\<in>set (b # c # cs). bp_marker x \<le> bp_marker y"
        using left_le_b b_le_all by force
      show ?thesis
        using Cons True left_sorted right_sorted cross
        by (simp add: sorted_wrt_append)
    next
      case False
      show ?thesis
      proof (cases "snd p < bp_marker c")
        case True
        have left_sorted:
          "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
            (bp_lazy_bucket_insert_entries M p b)"
          by (rule bp_lazy_bucket_insert_entries_markers_sorted[OF M_pos])
        have left_le_c:
          "\<forall>x\<in>set (bp_lazy_bucket_insert_entries M p b).
            bp_marker x \<le> bp_marker c"
        proof (rule bp_lazy_bucket_insert_entries_markers_le
            [OF M_pos b_le_c])
          show "\<forall>q\<in>set (p # bp_bucket_entries b).
            snd q \<le> bp_marker c"
            using boundaries Cons True by auto
        qed
        have c_le_all:
          "\<forall>d\<in>set (c # cs). bp_marker c \<le> bp_marker d"
          using sorted_tail by auto
        have cross:
          "\<forall>x\<in>set (bp_lazy_bucket_insert_entries M p b).
            \<forall>y\<in>set (c # cs). bp_marker x \<le> bp_marker y"
          using left_le_c c_le_all by force
        show ?thesis
          using Cons False True left_sorted sorted_tail cross
          by (simp add: sorted_wrt_append)
      next
        case False
        have p_ge_c: "bp_marker c \<le> snd p"
          using False by simp
        have tail_sorted_result:
          "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
            (bp_lazy_insert_bucket M p (c # cs))"
          using IH[of p] sorted_tail lower_tail boundaries_tail Cons by auto
        have tail_ge_hd:
          "\<forall>d\<in>set (bp_lazy_insert_bucket M p (c # cs)).
            bp_marker (hd (c # cs)) \<le> bp_marker d"
        proof (rule bp_lazy_insert_bucket_markers_ge_hd
            [where bs = "c # cs" and p = p and M = M])
          show "0 < M"
            by (rule M_pos)
          show "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) (c # cs)"
            by (rule sorted_tail)
          show "\<forall>b\<in>set (c # cs). \<forall>q\<in>set (bp_bucket_entries b).
            bp_marker b \<le> snd q"
            by (rule lower_tail)
          show "c # cs \<noteq> []"
            by simp
          show "bp_marker (hd (c # cs)) \<le> snd p"
            using p_ge_c by simp
        qed
        have tail_ge_c:
          "\<forall>d\<in>set (bp_lazy_insert_bucket M p (c # cs)).
            bp_marker c \<le> bp_marker d"
          using tail_ge_hd by simp
        have tail_ge_b:
          "\<forall>d\<in>set (bp_lazy_insert_bucket M p (c # cs)).
            bp_marker b \<le> bp_marker d"
          using b_le_c tail_ge_c by force
        show ?thesis
          using Cons \<open>\<not> snd p < bp_marker b\<close> False
            tail_sorted_result tail_ge_b by simp
      qed
    qed
  qed
qed

lemma bp_lazy_insert_bucket_boundaries_ok:
  assumes M_pos: "0 < M"
    and sorted: "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) bs"
    and lower: "\<forall>b\<in>set bs. \<forall>q\<in>set (bp_bucket_entries b).
      bp_marker b \<le> snd q"
    and boundaries: "bp_bucket_boundaries_ok bs"
  shows "bp_bucket_boundaries_ok (bp_lazy_insert_bucket M p bs)"
  using sorted lower boundaries
proof (induction bs arbitrary: p)
  case Nil
  then show ?case
    by (simp add: bp_bucketize_entries_boundaries_ok[OF M_pos])
next
  case (Cons b bs)
  note IH = Cons.IH
  note sorted = Cons.prems(1)
  note lower = Cons.prems(2)
  note boundaries = Cons.prems(3)
  show ?case
  proof (cases bs)
    case Nil
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      have tail: "bp_bucket_boundaries_ok [b]"
        by simp
      have upper: "\<forall>q\<in>set [p]. snd q \<le> bp_marker b"
        using True by simp
      show ?thesis
        using Nil True
        by (simp add: bp_bucket_boundaries_ok_bucketize_append_Cons
            [OF M_pos tail upper])
    next
      case False
      show ?thesis
        using Nil False
          bp_lazy_bucket_insert_entries_boundaries_ok[OF M_pos, of p b]
        by simp
    qed
  next
    case (Cons c cs)
    have sorted_tail:
      "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) (c # cs)"
      using sorted Cons by simp
    have lower_tail:
      "\<forall>b\<in>set (c # cs). \<forall>q\<in>set (bp_bucket_entries b).
        bp_marker b \<le> snd q"
      using lower Cons by simp
    have boundaries_tail: "bp_bucket_boundaries_ok (c # cs)"
      using boundaries Cons by simp
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      have tail_all: "bp_bucket_boundaries_ok (b # c # cs)"
        using boundaries Cons by simp
      have upper: "\<forall>q\<in>set [p]. snd q \<le> bp_marker b"
        using True by simp
      show ?thesis
        using Cons True
        by (simp add: bp_bucket_boundaries_ok_bucketize_append_Cons
            [where c = b and bs = "c # cs" and xs = "[p]",
              OF M_pos tail_all upper])
    next
      case False
      show ?thesis
      proof (cases "snd p < bp_marker c")
        case True
        have upper:
          "\<forall>q\<in>set (p # bp_bucket_entries b). snd q \<le> bp_marker c"
          using boundaries Cons True by auto
        have left_boundaries:
          "bp_bucket_boundaries_ok (bp_lazy_bucket_insert_entries M p b)"
          by (rule bp_lazy_bucket_insert_entries_boundaries_ok[OF M_pos])
        have cross_entries:
          "\<forall>d\<in>set (bp_lazy_bucket_insert_entries M p b).
            \<forall>q\<in>set (bp_bucket_entries d). snd q \<le> bp_marker c"
          by (rule bp_lazy_bucket_insert_entries_entries_le
              [OF M_pos upper])
        have append_ok:
          "bp_bucket_boundaries_ok
            (bp_lazy_bucket_insert_entries M p b @ c # cs)"
        proof (rule bp_bucket_boundaries_ok_append)
          show "bp_bucket_boundaries_ok
              (bp_lazy_bucket_insert_entries M p b)"
            by (rule left_boundaries)
          show "bp_bucket_boundaries_ok (c # cs)"
            by (rule boundaries_tail)
          show "c # cs \<noteq> [] \<Longrightarrow>
            \<forall>b\<in>set (bp_lazy_bucket_insert_entries M p b).
              \<forall>p\<in>set (bp_bucket_entries b).
                snd p \<le> bp_marker (hd (c # cs))"
            using cross_entries by simp
        qed
        show ?thesis
          using Cons False True append_ok by simp
      next
        case False
        have p_ge_c: "bp_marker c \<le> snd p"
          using False by simp
        have tail_boundaries:
          "bp_bucket_boundaries_ok (bp_lazy_insert_bucket M p (c # cs))"
          using IH[of p] sorted_tail lower_tail boundaries_tail Cons by auto
        have tail_ge_hd:
          "\<forall>d\<in>set (bp_lazy_insert_bucket M p (c # cs)).
            bp_marker (hd (c # cs)) \<le> bp_marker d"
        proof (rule bp_lazy_insert_bucket_markers_ge_hd
            [where bs = "c # cs" and p = p and M = M])
          show "0 < M"
            by (rule M_pos)
          show "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) (c # cs)"
            by (rule sorted_tail)
          show "\<forall>b\<in>set (c # cs). \<forall>q\<in>set (bp_bucket_entries b).
            bp_marker b \<le> snd q"
            by (rule lower_tail)
          show "c # cs \<noteq> []"
            by simp
          show "bp_marker (hd (c # cs)) \<le> snd p"
            using p_ge_c by simp
        qed
        have tail_ge_c:
          "\<forall>d\<in>set (bp_lazy_insert_bucket M p (c # cs)).
            bp_marker c \<le> bp_marker d"
          using tail_ge_hd by simp
        have tail_nonempty_result:
          "bp_lazy_insert_bucket M p (c # cs) \<noteq> []"
          by (rule bp_lazy_insert_bucket_nonempty[OF M_pos])
        obtain d ds where tail_eq:
          "bp_lazy_insert_bucket M p (c # cs) = d # ds"
          using tail_nonempty_result
          by (cases "bp_lazy_insert_bucket M p (c # cs)") auto
        have c_le_d: "bp_marker c \<le> bp_marker d"
          using tail_ge_c tail_eq by simp
        have head_boundary:
          "\<forall>q\<in>set (bp_bucket_entries b). snd q \<le> bp_marker d"
        proof
          fix q
          assume q: "q \<in> set (bp_bucket_entries b)"
          have "snd q \<le> bp_marker c"
            using boundaries Cons q by auto
          then show "snd q \<le> bp_marker d"
            using c_le_d by linarith
        qed
        show ?thesis
          using Cons \<open>\<not> snd p < bp_marker b\<close> False tail_eq
            tail_boundaries head_boundary by simp
      qed
    qed
  qed
qed

lemma bp_lazy_insert_bucket_preserves_bucket_shape:
  assumes M_pos: "0 < M"
    and sizes: "\<forall>b\<in>set bs. length (bp_bucket_entries b) \<le> 2 * M"
    and sorted: "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) bs"
    and lower: "\<forall>b\<in>set bs. \<forall>q\<in>set (bp_bucket_entries b).
      bp_marker b \<le> snd q"
    and boundaries: "bp_bucket_boundaries_ok bs"
  shows "(\<forall>b\<in>set (bp_lazy_insert_bucket M p bs).
      length (bp_bucket_entries b) \<le> 2 * M) \<and>
    sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
      (bp_lazy_insert_bucket M p bs) \<and>
    (\<forall>b\<in>set (bp_lazy_insert_bucket M p bs).
      \<forall>q\<in>set (bp_bucket_entries b). bp_marker b \<le> snd q) \<and>
    bp_bucket_boundaries_ok (bp_lazy_insert_bucket M p bs)"
  using bp_lazy_insert_bucket_sizes_ok[OF M_pos sizes, of p]
    bp_lazy_insert_bucket_markers_sorted
      [OF M_pos sorted lower boundaries, of p]
    bp_lazy_insert_bucket_markers_lower_bound[OF M_pos lower, of p]
    bp_lazy_insert_bucket_boundaries_ok
      [OF M_pos sorted lower boundaries, of p]
  by blast

lemma bp_local_insert_bucket_markers_ge_hd:
  assumes M_pos: "0 < M"
    and sorted: "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) bs"
    and lower: "\<forall>b\<in>set bs. \<forall>q\<in>set (bp_bucket_entries b).
      bp_marker b \<le> snd q"
    and nonempty: "bs \<noteq> []"
    and p_ge: "bp_marker (hd bs) \<le> snd p"
  shows "\<forall>b\<in>set (bp_local_insert_bucket M p bs).
    bp_marker (hd bs) \<le> bp_marker b"
  using sorted lower nonempty p_ge
proof (induction bs arbitrary: p)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  note IH = Cons.IH
  note sorted = Cons.prems(1)
  note lower = Cons.prems(2)
  note p_ge = Cons.prems(4)
  show ?case
  proof (cases bs)
    case Nil
    have markers_ge:
      "\<forall>c\<in>set (bp_bucketize_entries M (p # bp_bucket_entries b)).
        bp_marker b \<le> bp_marker c"
    proof (rule bp_bucketize_entries_markers_ge)
      show "\<forall>q\<in>set (p # bp_bucket_entries b). bp_marker b \<le> snd q"
        using lower p_ge by auto
    qed
    show ?thesis
      using Nil p_ge markers_ge by auto
  next
    case (Cons c cs)
    have sorted_tail:
      "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) (c # cs)"
      using sorted Cons by simp
    have lower_tail:
      "\<forall>b\<in>set (c # cs). \<forall>q\<in>set (bp_bucket_entries b).
        bp_marker b \<le> snd q"
      using lower Cons by simp
    have b_le_c: "bp_marker b \<le> bp_marker c"
      using sorted Cons by simp
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      then show ?thesis
        using p_ge by simp
    next
      case False
      note not_before_b = False
      show ?thesis
      proof (cases "snd p < bp_marker c")
        case True
        have markers_ge:
          "\<forall>d\<in>set (bp_bucketize_entries M (p # bp_bucket_entries b)).
            bp_marker b \<le> bp_marker d"
        proof (rule bp_bucketize_entries_markers_ge)
          show "\<forall>q\<in>set (p # bp_bucket_entries b). bp_marker b \<le> snd q"
            using lower p_ge by auto
        qed
        have tail_ge:
          "\<forall>d\<in>set (c # cs). bp_marker b \<le> bp_marker d"
          using sorted Cons by auto
        show ?thesis
          using Cons False True markers_ge tail_ge by auto
      next
        case False
        have p_ge_c: "bp_marker c \<le> snd p"
          using False by simp
        have tail_ge_c:
          "\<forall>d\<in>set (bp_local_insert_bucket M p (c # cs)).
            bp_marker c \<le> bp_marker d"
          using IH[of p] sorted_tail lower_tail p_ge_c Cons by auto
        show ?thesis
          using Cons False b_le_c tail_ge_c by auto
      qed
    qed
  qed
qed

lemma bp_local_insert_bucket_markers_sorted:
  assumes M_pos: "0 < M"
    and sorted: "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) bs"
    and lower: "\<forall>b\<in>set bs. \<forall>q\<in>set (bp_bucket_entries b).
      bp_marker b \<le> snd q"
    and boundaries: "bp_bucket_boundaries_ok bs"
  shows "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
    (bp_local_insert_bucket M p bs)"
  using sorted lower boundaries
proof (induction bs arbitrary: p)
  case Nil
  then show ?case
    by (simp add: bp_bucketize_entries_markers_sorted[OF M_pos])
next
  case (Cons b bs)
  note IH = Cons.IH
  note sorted = Cons.prems(1)
  note lower = Cons.prems(2)
  note boundaries = Cons.prems(3)
  show ?case
  proof (cases bs)
    case Nil
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      have left_sorted:
        "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
          (bp_bucketize_entries M [p])"
        by (rule bp_bucketize_entries_markers_sorted[OF M_pos])
      have left_le_b:
        "\<forall>x\<in>set (bp_bucketize_entries M [p]).
          bp_marker x \<le> bp_marker b"
      proof (rule bp_bucketize_entries_markers_le)
        show "\<forall>q\<in>set [p]. snd q \<le> bp_marker b"
          using True by simp
      qed
      show ?thesis
        using Nil True left_sorted left_le_b
        by (simp add: sorted_wrt_append)
    next
      case False
      show ?thesis
        using Nil False
        by (simp add: bp_bucketize_entries_markers_sorted[OF M_pos])
    qed
  next
    case (Cons c cs)
    have sorted_tail:
      "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) (c # cs)"
      using sorted Cons by simp
    have lower_tail:
      "\<forall>b\<in>set (c # cs). \<forall>q\<in>set (bp_bucket_entries b).
        bp_marker b \<le> snd q"
      using lower Cons by simp
    have boundaries_tail: "bp_bucket_boundaries_ok (c # cs)"
      using boundaries Cons by simp
    have b_le_c: "bp_marker b \<le> bp_marker c"
      using sorted Cons by simp
    have b_le_all_tail:
      "\<forall>d\<in>set (b # c # cs). bp_marker b \<le> bp_marker d"
      using sorted Cons by auto
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      have left_sorted:
        "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
          (bp_bucketize_entries M [p])"
        by (rule bp_bucketize_entries_markers_sorted[OF M_pos])
      have right_sorted:
        "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) (b # c # cs)"
        using sorted Cons by simp
      have left_le_b:
        "\<forall>x\<in>set (bp_bucketize_entries M [p]).
          bp_marker x \<le> bp_marker b"
      proof (rule bp_bucketize_entries_markers_le)
        show "\<forall>q\<in>set [p]. snd q \<le> bp_marker b"
          using True by simp
      qed
      have cross:
        "\<forall>x\<in>set (bp_bucketize_entries M [p]).
          \<forall>y\<in>set (b # c # cs). bp_marker x \<le> bp_marker y"
        using left_le_b b_le_all_tail by force
      show ?thesis
        using Cons True left_sorted right_sorted cross
        by (simp add: sorted_wrt_append)
    next
      case False
      note not_before_b = False
      show ?thesis
      proof (cases "snd p < bp_marker c")
        case True
        have left_sorted:
          "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
            (bp_bucketize_entries M (p # bp_bucket_entries b))"
          by (rule bp_bucketize_entries_markers_sorted[OF M_pos])
        have left_le_c:
          "\<forall>x\<in>set (bp_bucketize_entries M (p # bp_bucket_entries b)).
            bp_marker x \<le> bp_marker c"
        proof (rule bp_bucketize_entries_markers_le)
          show "\<forall>q\<in>set (p # bp_bucket_entries b). snd q \<le> bp_marker c"
            using boundaries Cons True by auto
        qed
        have c_le_all:
          "\<forall>d\<in>set (c # cs). bp_marker c \<le> bp_marker d"
          using sorted_tail by auto
        have cross:
          "\<forall>x\<in>set (bp_bucketize_entries M (p # bp_bucket_entries b)).
            \<forall>y\<in>set (c # cs). bp_marker x \<le> bp_marker y"
          using left_le_c c_le_all by force
        show ?thesis
          using Cons False True left_sorted sorted_tail cross
          by (simp add: sorted_wrt_append)
      next
        case False
        have p_ge_c: "bp_marker c \<le> snd p"
          using False by simp
        have p_ge_hd: "bp_marker (hd (c # cs)) \<le> snd p"
          using p_ge_c by simp
        have tail_nonempty: "c # cs \<noteq> []"
          by simp
        have tail_sorted_result:
          "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
            (bp_local_insert_bucket M p (c # cs))"
          using IH[of p] sorted_tail lower_tail boundaries_tail Cons by auto
        have tail_ge_hd:
          "\<forall>d\<in>set (bp_local_insert_bucket M p (c # cs)).
            bp_marker (hd (c # cs)) \<le> bp_marker d"
          by (rule bp_local_insert_bucket_markers_ge_hd
              [where bs = "c # cs" and p = p and M = M,
                OF M_pos sorted_tail lower_tail tail_nonempty p_ge_hd])
        have tail_ge_c:
          "\<forall>d\<in>set (bp_local_insert_bucket M p (c # cs)).
            bp_marker c \<le> bp_marker d"
          using tail_ge_hd by simp
        have tail_ge_b:
          "\<forall>d\<in>set (bp_local_insert_bucket M p (c # cs)).
            bp_marker b \<le> bp_marker d"
          using b_le_c tail_ge_c by force
        show ?thesis
          using Cons not_before_b False tail_sorted_result tail_ge_b by simp
      qed
    qed
  qed
qed

lemma bp_local_insert_bucket_boundaries_ok:
  assumes M_pos: "0 < M"
    and sorted: "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) bs"
    and lower: "\<forall>b\<in>set bs. \<forall>q\<in>set (bp_bucket_entries b).
      bp_marker b \<le> snd q"
    and boundaries: "bp_bucket_boundaries_ok bs"
  shows "bp_bucket_boundaries_ok (bp_local_insert_bucket M p bs)"
  using sorted lower boundaries
proof (induction bs arbitrary: p)
  case Nil
  then show ?case
    by (simp add: bp_bucketize_entries_boundaries_ok[OF M_pos])
next
  case (Cons b bs)
  note IH = Cons.IH
  note sorted = Cons.prems(1)
  note lower = Cons.prems(2)
  note boundaries = Cons.prems(3)
  show ?case
  proof (cases bs)
    case Nil
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      have tail: "bp_bucket_boundaries_ok [b]"
        by simp
      have upper: "\<forall>q\<in>set [p]. snd q \<le> bp_marker b"
        using True by simp
      show ?thesis
        using Nil True
        by (simp add: bp_bucket_boundaries_ok_bucketize_append_Cons
            [OF M_pos tail upper])
    next
      case False
      show ?thesis
        using Nil False by (simp add: bp_bucketize_entries_boundaries_ok[OF M_pos])
    qed
  next
    case (Cons c cs)
    have sorted_tail:
      "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) (c # cs)"
      using sorted Cons by simp
    have lower_tail:
      "\<forall>b\<in>set (c # cs). \<forall>q\<in>set (bp_bucket_entries b).
        bp_marker b \<le> snd q"
      using lower Cons by simp
    have boundaries_tail: "bp_bucket_boundaries_ok (c # cs)"
      using boundaries Cons by simp
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      have tail_all: "bp_bucket_boundaries_ok (b # c # cs)"
        using boundaries Cons by simp
      have upper: "\<forall>q\<in>set [p]. snd q \<le> bp_marker b"
        using True by simp
      show ?thesis
        using Cons True
        by (simp add: bp_bucket_boundaries_ok_bucketize_append_Cons
            [where c = b and bs = "c # cs" and xs = "[p]",
              OF M_pos tail_all upper])
    next
      case False
      note not_before_b = False
      show ?thesis
      proof (cases "snd p < bp_marker c")
        case True
        have upper:
          "\<forall>q\<in>set (p # bp_bucket_entries b). snd q \<le> bp_marker c"
          using boundaries Cons True by auto
        show ?thesis
          using Cons not_before_b True
          by (simp add: bp_bucket_boundaries_ok_bucketize_append_Cons
              [OF M_pos boundaries_tail upper])
      next
        case False
        have p_ge_c: "bp_marker c \<le> snd p"
          using False by simp
        have p_ge_hd: "bp_marker (hd (c # cs)) \<le> snd p"
          using p_ge_c by simp
        have tail_nonempty: "c # cs \<noteq> []"
          by simp
        have tail_boundaries:
          "bp_bucket_boundaries_ok (bp_local_insert_bucket M p (c # cs))"
          using IH[of p] sorted_tail lower_tail boundaries_tail Cons by auto
        have tail_ge_hd:
          "\<forall>d\<in>set (bp_local_insert_bucket M p (c # cs)).
            bp_marker (hd (c # cs)) \<le> bp_marker d"
          by (rule bp_local_insert_bucket_markers_ge_hd
              [where bs = "c # cs" and p = p and M = M,
                OF M_pos sorted_tail lower_tail tail_nonempty p_ge_hd])
        have tail_nonempty_result:
          "bp_local_insert_bucket M p (c # cs) \<noteq> []"
          by (rule bp_local_insert_bucket_nonempty[OF M_pos])
        obtain d ds where tail_eq:
          "bp_local_insert_bucket M p (c # cs) = d # ds"
          using tail_nonempty_result by (cases "bp_local_insert_bucket M p (c # cs)") auto
        have c_le_d: "bp_marker c \<le> bp_marker d"
          using tail_ge_hd tail_eq by simp
        have head_boundary:
          "\<forall>q\<in>set (bp_bucket_entries b). snd q \<le> bp_marker d"
        proof
          fix q
          assume q: "q \<in> set (bp_bucket_entries b)"
          have "snd q \<le> bp_marker c"
            using boundaries Cons q by auto
          then show "snd q \<le> bp_marker d"
            using c_le_d by linarith
        qed
        show ?thesis
          using Cons not_before_b False tail_eq tail_boundaries head_boundary by simp
      qed
    qed
  qed
qed

lemma bp_local_insert_bucket_preserves_bucket_shape:
  assumes M_pos: "0 < M"
    and sizes: "\<forall>b\<in>set bs. length (bp_bucket_entries b) \<le> M"
    and sorted: "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) bs"
    and lower: "\<forall>b\<in>set bs. \<forall>q\<in>set (bp_bucket_entries b).
      bp_marker b \<le> snd q"
    and boundaries: "bp_bucket_boundaries_ok bs"
  shows "(\<forall>b\<in>set (bp_local_insert_bucket M p bs).
      length (bp_bucket_entries b) \<le> M) \<and>
    sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
      (bp_local_insert_bucket M p bs) \<and>
    (\<forall>b\<in>set (bp_local_insert_bucket M p bs).
      \<forall>q\<in>set (bp_bucket_entries b). bp_marker b \<le> snd q) \<and>
    bp_bucket_boundaries_ok (bp_local_insert_bucket M p bs)"
  using bp_local_insert_bucket_sizes_ok[OF M_pos sizes, of p]
    bp_local_insert_bucket_markers_sorted[OF M_pos sorted lower boundaries, of p]
    bp_local_insert_bucket_markers_lower_bound[OF M_pos lower, of p]
    bp_local_insert_bucket_boundaries_ok[OF M_pos sorted lower boundaries, of p]
  by blast

text \<open>
  The local-insert proof is deliberately split into many list-level lemmas
  because each invariant component has a different reason for being preserved.
  Size preservation depends on re-chunking only the affected bucket.  Marker
  ordering depends on inserting into the unique marker interval selected by the
  value of the new entry.  Boundary preservation depends on the fact that every
  entry of the previous bucket remains below the next bucket marker.  The
  bundled lemma @{thm bp_local_insert_bucket_preserves_bucket_shape} is the
  high-level summary used by the state-level Insert proof.
\<close>

lemma length_bp_bucket_entries_flat_bucketize_entries [simp]:
  assumes "0 < M"
  shows "length (bp_bucket_entries_flat (bp_bucketize_entries M xs)) =
    length xs"
  using bp_bucket_entries_flat_bucketize_entries[OF assms, of xs] by simp

lemma length_bp_bucketize_sorted_entries_aux_le_ratio:
  assumes M_pos: "0 < M"
    and fuel: "length xs \<le> fuel"
  shows "length (bp_bucketize_sorted_entries_aux fuel M xs) \<le>
    Suc (length xs div M)"
  using M_pos fuel
proof (induction fuel arbitrary: xs)
  case 0
  then show ?case
    by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "xs = []")
    case True
    then show ?thesis
      by simp
  next
    case False
    show ?thesis
    proof (cases "length xs < M")
      case True
      then have "drop M xs = []"
        by simp
      then show ?thesis
        using Suc.prems False True by simp
    next
      case False
      have M_le: "M \<le> length xs"
        using False by simp
      have len_drop: "length (drop M xs) \<le> fuel"
        using Suc.prems False by simp
      have tail:
        "length (bp_bucketize_sorted_entries_aux fuel M (drop M xs)) \<le>
          Suc (length (drop M xs) div M)"
        by (rule Suc.IH[OF Suc.prems(1) len_drop])
      have len_xs:
        "length xs = M + length (drop M xs)"
        using M_le by simp
      have div_eq:
        "length xs div M = Suc (length (drop M xs) div M)"
      proof -
        have "length xs div M = (M + length (drop M xs)) div M"
          using len_xs by simp
        also have "\<dots> = length (drop M xs) div M + 1"
          using Suc.prems(1) by (simp add: div_add_self1)
        finally show ?thesis
          by simp
      qed
      show ?thesis
        using Suc.prems False tail div_eq by simp
    qed
  qed
qed

lemma length_bp_bucketize_sorted_entries_le_ratio:
  assumes "0 < M"
  shows "length (bp_bucketize_sorted_entries M xs) \<le>
    Suc (length xs div M)"
  unfolding bp_bucketize_sorted_entries_def
  by (rule length_bp_bucketize_sorted_entries_aux_le_ratio[OF assms]) simp

lemma length_bp_bucketize_entries_le_ratio:
  assumes "0 < M"
  shows "length (bp_bucketize_entries M xs) \<le>
    Suc (length xs div M)"
  unfolding bp_bucketize_entries_def
  using length_bp_bucketize_sorted_entries_le_ratio[OF assms, of "sort_key snd xs"]
  by simp

lemma length_bp_bucketize_entries_singleton [simp]:
  assumes "0 < M"
  shows "length (bp_bucketize_entries M [p]) = 1"
  using assms
  unfolding bp_bucketize_entries_def bp_bucketize_sorted_entries_def
  by (cases M) simp_all

lemma length_bp_bucketize_sorted_entries_aux_le_length:
  assumes M_pos: "0 < M"
    and fuel: "length xs \<le> fuel"
  shows "length (bp_bucketize_sorted_entries_aux fuel M xs) \<le>
    length xs"
  using M_pos fuel
proof (induction fuel arbitrary: xs)
  case 0
  then show ?case
    by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "xs = []")
    case True
    then show ?thesis by simp
  next
    case False
    have len_drop: "length (drop M xs) \<le> fuel"
      using Suc.prems False by (cases M) auto
    have tail:
      "length (bp_bucketize_sorted_entries_aux fuel M (drop M xs)) \<le>
        length (drop M xs)"
      by (rule Suc.IH[OF Suc.prems(1) len_drop])
    have drop_less: "length (drop M xs) < length xs"
      using Suc.prems False by simp
    have drop_le: "Suc (length (drop M xs)) \<le> length xs"
      using drop_less by simp
    have unfold:
      "length (bp_bucketize_sorted_entries_aux (Suc fuel) M xs) =
        Suc (length (bp_bucketize_sorted_entries_aux fuel M (drop M xs)))"
      using Suc.prems False by simp
    show ?thesis
      using tail drop_le unfolding unfold by simp
  qed
qed

lemma length_bp_bucketize_entries_le_length:
  assumes "0 < M"
  shows "length (bp_bucketize_entries M xs) \<le> length xs"
  unfolding bp_bucketize_entries_def bp_bucketize_sorted_entries_def
  using length_bp_bucketize_sorted_entries_aux_le_length
    [OF assms, of "sort_key snd xs" "length xs"]
  by simp

lemma length_bp_bucketize_entries_le_three:
  assumes M_pos: "0 < M"
    and len: "length xs \<le> Suc (2 * M)"
  shows "length (bp_bucketize_entries M xs) \<le> 3"
proof (cases "M = 1")
  case True
  have "length (bp_bucketize_entries M xs) \<le> length xs"
    by (rule length_bp_bucketize_entries_le_length[OF M_pos])
  also have "\<dots> \<le> 3"
    using len True by simp
  finally show ?thesis .
next
  case False
  have M_ge2: "2 \<le> M"
    using M_pos False by simp
  have div_bound: "length xs div M \<le> 2"
  proof -
    have "length xs div M \<le> Suc (2 * M) div M"
      by (rule div_le_mono[OF len])
    moreover have "Suc (2 * M) div M < 3"
    proof -
      have "Suc (2 * M) < 3 * M"
        using M_ge2 by simp
      then show ?thesis
        using M_pos by (simp add: div_less_iff_less_mult)
    qed
    ultimately show ?thesis
      by simp
  qed
  have "length (bp_bucketize_entries M xs) \<le> Suc (length xs div M)"
    by (rule length_bp_bucketize_entries_le_ratio[OF M_pos])
  also have "\<dots> \<le> 3"
    using div_bound by simp
  finally show ?thesis .
qed

lemma length_bp_lazy_bucket_insert_entries_le_three:
  assumes M_pos: "0 < M"
    and size: "length (bp_bucket_entries b) \<le> 2 * M"
  shows "length (bp_lazy_bucket_insert_entries M p b) \<le> 3"
proof (cases "length (bp_bucket_entries b) < 2 * M")
  case True
  then show ?thesis
    unfolding bp_lazy_bucket_insert_entries_def by simp
next
  case False
  have len: "length (p # bp_bucket_entries b) \<le> Suc (2 * M)"
    using size by simp
  show ?thesis
    using False length_bp_bucketize_entries_le_three[OF M_pos len]
    unfolding bp_lazy_bucket_insert_entries_def by simp
qed

lemma length_bp_lazy_insert_bucket_le:
  assumes M_pos: "0 < M"
    and sizes: "\<forall>b\<in>set bs. length (bp_bucket_entries b) \<le> 2 * M"
  shows "length (bp_lazy_insert_bucket M p bs) \<le> length bs + 2"
  using sizes
proof (induction bs arbitrary: p)
  case Nil
  then show ?case
    using length_bp_bucketize_entries_singleton[OF M_pos, of p] by simp
next
  case (Cons b bs)
  note IH = Cons.IH
  note sizes = Cons.prems
  have b_size: "length (bp_bucket_entries b) \<le> 2 * M"
    using sizes by simp
  show ?case
  proof (cases bs)
    case Nil
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      then show ?thesis
        using Nil length_bp_bucketize_entries_singleton[OF M_pos, of p]
        by simp
    next
      case False
      have "length (bp_lazy_bucket_insert_entries M p b) \<le> 3"
        by (rule length_bp_lazy_bucket_insert_entries_le_three
            [OF M_pos b_size])
      then show ?thesis
        using Nil False by simp
    qed
  next
    case (Cons c cs)
    have tail_sizes:
      "\<forall>b\<in>set bs. length (bp_bucket_entries b) \<le> 2 * M"
      using sizes by simp
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      then show ?thesis
        using Cons length_bp_bucketize_entries_singleton[OF M_pos, of p]
        by simp
    next
      case False
      show ?thesis
      proof (cases "snd p < bp_marker c")
        case True
        have "length (bp_lazy_bucket_insert_entries M p b) \<le> 3"
          by (rule length_bp_lazy_bucket_insert_entries_le_three
              [OF M_pos b_size])
        then show ?thesis
          using Cons False True by simp
      next
        case False
        have tail:
          "length (bp_lazy_insert_bucket M p bs) \<le> length bs + 2"
          by (rule IH[OF tail_sizes])
        show ?thesis
          using Cons \<open>\<not> snd p < bp_marker b\<close> False tail by simp
      qed
    qed
  qed
qed

lemma length_bp_bucket_entries_flat_local_insert_bucket [simp]:
  assumes "0 < M"
  shows "length (bp_bucket_entries_flat (bp_local_insert_bucket M p bs)) =
    Suc (length (bp_bucket_entries_flat bs))"
  using assms
proof (induction bs arbitrary: p)
  case Nil
  have len:
    "length (bp_bucket_entries_flat (bp_bucketize_entries M [p])) =
      length [p]"
    by (rule length_bp_bucket_entries_flat_bucketize_entries[OF Nil.prems])
  show ?case
    using len by (simp add: bp_bucket_entries_flat_def)
next
  case (Cons b bs)
  then show ?case
  proof (cases bs)
    case Nil
    have len_single:
      "length (bp_bucket_entries_flat (bp_bucketize_entries M [p])) =
        length [p]"
      by (rule length_bp_bucket_entries_flat_bucketize_entries[OF Cons.prems])
    have len_inserted:
      "length
        (bp_bucket_entries_flat
          (bp_bucketize_entries M (p # bp_bucket_entries b))) =
       length (p # bp_bucket_entries b)"
      by (rule length_bp_bucket_entries_flat_bucketize_entries[OF Cons.prems])
    then show ?thesis
      using Nil len_single len_inserted
      by (auto simp: bp_bucket_entries_flat_def)
  next
    case (Cons c cs)
    have len_single:
      "length (bp_bucket_entries_flat (bp_bucketize_entries M [p])) =
        length [p]"
      by (rule length_bp_bucket_entries_flat_bucketize_entries[OF Cons.prems])
    have len_inserted:
      "length
        (bp_bucket_entries_flat
          (bp_bucketize_entries M (p # bp_bucket_entries b))) =
       length (p # bp_bucket_entries b)"
      by (rule length_bp_bucket_entries_flat_bucketize_entries[OF Cons.prems])
    have tail_len:
      "length (bp_bucket_entries_flat
          (bp_local_insert_bucket M p (c # cs))) =
       Suc (length (bp_bucket_entries_flat (c # cs)))"
      using Cons.IH[OF Cons.prems, of p] Cons by simp
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      then show ?thesis
        using Cons len_single by (simp add: bp_bucket_entries_flat_def)
    next
      case False
      note not_before_b = False
      show ?thesis
      proof (cases "snd p < bp_marker c")
        case True
        then show ?thesis
          using Cons not_before_b len_inserted
          by (simp add: bp_bucket_entries_flat_def)
      next
        case False
        then show ?thesis
          using Cons not_before_b tail_len
          by (simp add: bp_bucket_entries_flat_def)
      qed
    qed
  qed
qed

lemma bp_local_insert_bucket_distinct_keys:
  assumes M_pos: "0 < M"
    and distinct: "distinct (map fst (bp_bucket_entries_flat bs))"
    and fresh: "fst p \<notin> bp_entry_keys (bp_bucket_entries_flat bs)"
  shows "distinct
    (map fst (bp_bucket_entries_flat (bp_local_insert_bucket M p bs)))"
proof (rule card_distinct)
  let ?old = "map fst (bp_bucket_entries_flat bs)"
  let ?new =
    "map fst (bp_bucket_entries_flat (bp_local_insert_bucket M p bs))"
  have set_new: "set ?new = insert (fst p) (set ?old)"
    using set_bp_bucket_entries_flat_local_insert_bucket[OF M_pos, of p bs]
    by auto
  have fresh_set: "fst p \<notin> set ?old"
    using fresh unfolding bp_entry_keys_def by simp
  have "card (set ?new) = Suc (card (set ?old))"
    unfolding set_new using fresh_set by simp
  also have "\<dots> = Suc (length ?old)"
    using distinct_card[OF distinct] by simp
  also have "\<dots> = length ?new"
    using length_bp_bucket_entries_flat_local_insert_bucket[OF M_pos, of p bs]
    by simp
  finally show "card (set ?new) = length ?new" .
qed

lemma bp_local_insert_bucket_values_consistent:
  assumes M_pos: "0 < M"
    and vals: "\<forall>q\<in>set (bp_bucket_entries_flat bs). f (fst q) = snd q"
    and fresh: "fst p \<notin> bp_entry_keys (bp_bucket_entries_flat bs)"
  shows "\<forall>q\<in>set (bp_bucket_entries_flat (bp_local_insert_bucket M p bs)).
    (f(fst p := snd p)) (fst q) = snd q"
proof
  fix q
  assume q: "q \<in>
    set (bp_bucket_entries_flat (bp_local_insert_bucket M p bs))"
  then have q_cases: "q = p \<or> q \<in> set (bp_bucket_entries_flat bs)"
    using set_bp_bucket_entries_flat_local_insert_bucket[OF M_pos, of p bs]
    by auto
  from q_cases show "(f(fst p := snd p)) (fst q) = snd q"
  proof
    assume "q = p"
    then show ?thesis by simp
  next
    assume q_old: "q \<in> set (bp_bucket_entries_flat bs)"
    have "fst q \<in> bp_entry_keys (bp_bucket_entries_flat bs)"
      using q_old unfolding bp_entry_keys_def by auto
    then have "fst q \<noteq> fst p"
      using fresh by auto
    moreover have "f (fst q) = snd q"
      using vals q_old by blast
    ultimately show ?thesis
      by simp
  qed
qed

lemma bp_empty_invariant:
  assumes "0 < M"
  shows "bp_invariant (bp_empty M B)"
  using assms
  unfolding bp_invariant_def bp_empty_def bp_entries_def
    bp_bucket_entries_flat_def bp_bucket_sizes_ok_def
    bp_bucket_markers_sorted_def bp_bucket_markers_lower_bound_def
    bp_values_consistent_def bp_distinct_keys_def
  by simp

lemma bp_empty_boundaries_state_ok [simp]:
  "bp_bucket_boundaries_state_ok (bp_empty M B)"
  unfolding bp_bucket_boundaries_state_ok_def bp_empty_def by simp

lemma bp_empty_ordered_invariant:
  assumes "0 < M"
  shows "bp_ordered_invariant (bp_empty M B)"
  unfolding bp_ordered_invariant_def
  using bp_empty_invariant[OF assms] by simp

lemma bp_empty_view [simp]:
  "bp_view (bp_empty M B) = \<lparr>keys_of = {}, value_of = (\<lambda>_. B)\<rparr>"
  unfolding bp_view_def bp_empty_def bp_entries_def
    bp_bucket_entries_flat_def bp_entry_keys_def
  by simp

lemma bp_empty_partition_upper_bound [simp]:
  "partition_upper_bound (bp_view (bp_empty M B0)) B"
  unfolding partition_upper_bound_def by simp

lemma set_bp_insert_bucket:
  "set (bp_insert_bucket p bs) = insert (bp_singleton_bucket p) (set bs)"
  by (induction bs) auto

lemma set_bp_bucket_entries_flat_insert_bucket:
  "set (bp_bucket_entries_flat (bp_insert_bucket p bs)) =
     insert p (set (bp_bucket_entries_flat bs))"
  unfolding bp_bucket_entries_flat_def
  by (induction bs) auto

lemma length_bp_bucket_entries_flat_insert_bucket [simp]:
  "length (bp_bucket_entries_flat (bp_insert_bucket p bs)) =
     Suc (length (bp_bucket_entries_flat bs))"
  unfolding bp_bucket_entries_flat_def
  by (induction bs) auto

lemma bp_entry_keys_insert_bucket [simp]:
  "bp_entry_keys (bp_bucket_entries_flat (bp_insert_bucket p bs)) =
     insert (fst p) (bp_entry_keys (bp_bucket_entries_flat bs))"
  unfolding bp_entry_keys_def
  using set_bp_bucket_entries_flat_insert_bucket[of p bs] by auto

lemma bp_insert_bucket_sizes_ok:
  assumes "\<forall>b\<in>set bs. length (bp_bucket_entries b) \<le> M"
    and "0 < M"
  shows "\<forall>b\<in>set (bp_insert_bucket p bs).
    length (bp_bucket_entries b) \<le> M"
  using assms unfolding bp_singleton_bucket_def
  by (induction bs) auto

lemma bp_insert_bucket_markers_sorted:
  assumes "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) bs"
  shows "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
    (bp_insert_bucket p bs)"
  using assms
proof (induction bs)
  case Nil
  then show ?case
    unfolding bp_singleton_bucket_def by simp
next
  case (Cons b bs)
  show ?case
  proof (cases "snd p \<le> bp_marker b")
    case True
    then show ?thesis
      using Cons.prems by auto
  next
    case False
    have tail_sorted:
      "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) bs"
      using Cons.prems by simp
    have inserted_sorted:
      "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
        (bp_insert_bucket p bs)"
      by (rule Cons.IH[OF tail_sorted])
    have lower:
      "\<And>c. c \<in> set (bp_insert_bucket p bs) \<Longrightarrow>
        bp_marker b \<le> bp_marker c"
      using Cons.prems False
      by (auto simp: set_bp_insert_bucket bp_singleton_bucket_def)
    show ?thesis
      using False inserted_sorted lower by simp
  qed
qed

lemma bp_insert_bucket_markers_lower_bound:
  assumes "\<forall>b\<in>set bs. \<forall>p\<in>set (bp_bucket_entries b).
      bp_marker b \<le> snd p"
  shows "\<forall>b\<in>set (bp_insert_bucket p bs). \<forall>p\<in>set (bp_bucket_entries b).
      bp_marker b \<le> snd p"
  using assms
  by (induction bs) auto

lemma bp_insert_bucket_values_consistent:
  assumes "\<forall>q\<in>set (bp_bucket_entries_flat bs). f (fst q) = snd q"
    and "fst p \<notin> bp_entry_keys (bp_bucket_entries_flat bs)"
  shows "\<forall>q\<in>set (bp_bucket_entries_flat (bp_insert_bucket p bs)).
    (f(fst p := snd p)) (fst q) = snd q"
proof
  fix q
  assume q: "q \<in> set (bp_bucket_entries_flat (bp_insert_bucket p bs))"
  then have q_cases: "q = p \<or> q \<in> set (bp_bucket_entries_flat bs)"
    using set_bp_bucket_entries_flat_insert_bucket[of p bs] by auto
  from q_cases show "(f(fst p := snd p)) (fst q) = snd q"
  proof
    assume "q = p"
    then show ?thesis by simp
  next
    assume q_old: "q \<in> set (bp_bucket_entries_flat bs)"
    have "fst q \<in> bp_entry_keys (bp_bucket_entries_flat bs)"
      using q_old unfolding bp_entry_keys_def by auto
    then have "fst q \<noteq> fst p"
      using assms(2) by auto
    moreover have "f (fst q) = snd q"
      using assms(1) q_old by blast
    ultimately show ?thesis
      by simp
  qed
qed

lemma bp_insert_bucket_distinct_keys:
  assumes distinct: "distinct (map fst (bp_bucket_entries_flat bs))"
    and fresh: "fst p \<notin> bp_entry_keys (bp_bucket_entries_flat bs)"
  shows "distinct (map fst (bp_bucket_entries_flat (bp_insert_bucket p bs)))"
proof (rule card_distinct)
  let ?old = "map fst (bp_bucket_entries_flat bs)"
  let ?new = "map fst (bp_bucket_entries_flat (bp_insert_bucket p bs))"
  have set_new: "set ?new = insert (fst p) (set ?old)"
    using set_bp_bucket_entries_flat_insert_bucket[of p bs] by auto
  have fresh_set: "fst p \<notin> set ?old"
    using fresh unfolding bp_entry_keys_def by simp
  have "card (set ?new) = Suc (card (set ?old))"
    unfolding set_new using fresh_set by simp
  also have "\<dots> = Suc (length ?old)"
    using distinct_card[OF distinct] by simp
  also have "\<dots> = length ?new"
    by simp
  finally show "card (set ?new) = length ?new" .
qed

lemma distinct_map_fst_filter_neq:
  assumes "distinct (map fst xs)"
  shows "distinct (map fst (filter (\<lambda>p. fst p \<noteq> x) xs))"
  using assms by (induction xs) auto

lemma distinct_map_fst_filter_notin:
  assumes "distinct (map fst xs)"
  shows "distinct (map fst (filter (\<lambda>p. fst p \<notin> S) xs))"
  using assms by (induction xs) auto

lemma bp_bucket_entries_flat_delete_key:
  "bp_bucket_entries_flat (map (bp_delete_key_from_bucket x) bs) =
     filter (\<lambda>p. fst p \<noteq> x) (bp_bucket_entries_flat bs)"
  unfolding bp_bucket_entries_flat_def bp_delete_key_from_bucket_def
  by (induction bs) simp_all

lemma bp_bucket_entries_flat_delete_keys:
  "bp_bucket_entries_flat (map (bp_delete_keys_from_bucket S) bs) =
     filter (\<lambda>p. fst p \<notin> S) (bp_bucket_entries_flat bs)"
  unfolding bp_bucket_entries_flat_def bp_delete_keys_from_bucket_def
  by (induction bs) simp_all

lemma bp_entries_delete_key:
  "bp_entries (bp_delete_key x P) =
     filter (\<lambda>p. fst p \<noteq> x) (bp_entries P)"
  unfolding bp_entries_def bp_delete_key_def
  by (simp add: bp_bucket_entries_flat_delete_key)

lemma bp_entries_delete_keys:
  "bp_entries (bp_delete_keys S P) =
     filter (\<lambda>p. fst p \<notin> S) (bp_entries P)"
  unfolding bp_entries_def bp_delete_keys_def
  by (simp add: bp_bucket_entries_flat_delete_keys)

lemma length_filter_fst_neq_ge_pred:
  assumes distinct: "distinct (map fst xs)"
  shows "length xs \<le> Suc (length (filter (\<lambda>p. fst p \<noteq> x) xs))"
  using distinct
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons p xs)
  show ?case
  proof (cases "fst p = x")
    case True
    have "fst p \<notin> fst ` set xs"
      using Cons.prems by simp
    have "\<forall>q\<in>set xs. fst q \<noteq> x"
    proof
      fix q
      assume "q \<in> set xs"
      then have "fst q \<in> fst ` set xs"
        by blast
      have "fst q \<noteq> fst p"
      proof
        assume "fst q = fst p"
        then have "fst p \<in> fst ` set xs"
          using \<open>fst q \<in> fst ` set xs\<close> by simp
        then show False
          using \<open>fst p \<notin> fst ` set xs\<close> by simp
      qed
      then show "fst q \<noteq> x"
        using True by simp
    qed
    then have "filter (\<lambda>p. fst p \<noteq> x) xs = xs"
      by (simp add: filter_id_conv)
    then show ?thesis
      using True by simp
  next
    case False
    have tail: "length xs \<le> Suc (length (filter (\<lambda>p. fst p \<noteq> x) xs))"
      by (rule Cons.IH) (use Cons.prems in simp)
    show ?thesis
      using False tail by simp
  qed
qed

lemma length_bp_entries_delete_key_ge_pred:
  assumes "bp_distinct_keys P"
  shows "length (bp_entries P) \<le>
    Suc (length (bp_entries (bp_delete_key x P)))"
  using length_filter_fst_neq_ge_pred
    [of "bp_entries P" x] assms
  unfolding bp_entries_delete_key bp_distinct_keys_def by simp

lemma bp_entry_keys_delete_key [simp]:
  "bp_entry_keys (bp_entries (bp_delete_key x P)) =
     bp_entry_keys (bp_entries P) - {x}"
  by (simp add: bp_entries_delete_key)

lemma bp_entry_keys_delete_keys [simp]:
  "bp_entry_keys (bp_entries (bp_delete_keys S P)) =
     bp_entry_keys (bp_entries P) - S"
  by (simp add: bp_entries_delete_keys)

lemma bp_values_delete_key [simp]:
  "bp_values (bp_delete_key x P) = bp_values P"
  unfolding bp_delete_key_def by simp

lemma bp_values_delete_keys [simp]:
  "bp_values (bp_delete_keys S P) = bp_values P"
  unfolding bp_delete_keys_def by simp

lemma bp_delete_key_markers_sorted_list:
  assumes "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) bs"
  shows "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
    (map (bp_delete_key_from_bucket x) bs)"
  using assms unfolding bp_delete_key_from_bucket_def
  by (induction bs) auto

lemma bp_delete_keys_markers_sorted_list:
  assumes "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) bs"
  shows "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
    (map (bp_delete_keys_from_bucket S) bs)"
  using assms unfolding bp_delete_keys_from_bucket_def
  by (induction bs) auto

lemma bp_delete_key_markers_sorted:
  assumes "bp_bucket_markers_sorted P"
  shows "bp_bucket_markers_sorted (bp_delete_key x P)"
  using assms
  unfolding bp_bucket_markers_sorted_def bp_delete_key_def
    bp_delete_key_from_bucket_def
  by (simp add: bp_delete_key_markers_sorted_list
      [unfolded bp_delete_key_from_bucket_def])

lemma bp_delete_keys_markers_sorted:
  assumes "bp_bucket_markers_sorted P"
  shows "bp_bucket_markers_sorted (bp_delete_keys S P)"
  using assms
  unfolding bp_bucket_markers_sorted_def bp_delete_keys_def
    bp_delete_keys_from_bucket_def
  by (simp add: bp_delete_keys_markers_sorted_list
      [unfolded bp_delete_keys_from_bucket_def])

lemma bp_delete_key_bucket_sizes_ok:
  assumes "bp_bucket_sizes_ok P"
  shows "bp_bucket_sizes_ok (bp_delete_key x P)"
  unfolding bp_bucket_sizes_ok_def
proof
  fix b
  assume b: "b \<in> set (bp_buckets (bp_delete_key x P))"
  then obtain b0 where b0: "b0 \<in> set (bp_buckets P)"
    and b_def: "b = bp_delete_key_from_bucket x b0"
    unfolding bp_delete_key_def by auto
  have "length (bp_bucket_entries b) \<le> length (bp_bucket_entries b0)"
    unfolding b_def bp_delete_key_from_bucket_def by simp
  also have "\<dots> \<le> bp_block_size P"
    using assms b0 unfolding bp_bucket_sizes_ok_def by blast
  finally show "length (bp_bucket_entries b) \<le>
    bp_block_size (bp_delete_key x P)"
    unfolding bp_delete_key_def by simp
qed

lemma bp_delete_keys_bucket_sizes_ok:
  assumes "bp_bucket_sizes_ok P"
  shows "bp_bucket_sizes_ok (bp_delete_keys S P)"
  unfolding bp_bucket_sizes_ok_def
proof
  fix b
  assume b: "b \<in> set (bp_buckets (bp_delete_keys S P))"
  then obtain b0 where b0: "b0 \<in> set (bp_buckets P)"
    and b_def: "b = bp_delete_keys_from_bucket S b0"
    unfolding bp_delete_keys_def by auto
  have "length (bp_bucket_entries b) \<le> length (bp_bucket_entries b0)"
    unfolding b_def bp_delete_keys_from_bucket_def by simp
  also have "\<dots> \<le> bp_block_size P"
    using assms b0 unfolding bp_bucket_sizes_ok_def by blast
  finally show "length (bp_bucket_entries b) \<le>
    bp_block_size (bp_delete_keys S P)"
    unfolding bp_delete_keys_def by simp
qed

lemma bp_delete_key_lazy_bucket_sizes_ok:
  assumes "bp_lazy_bucket_sizes_ok P"
  shows "bp_lazy_bucket_sizes_ok (bp_delete_key x P)"
  unfolding bp_lazy_bucket_sizes_ok_def
proof
  fix b
  assume b: "b \<in> set (bp_buckets (bp_delete_key x P))"
  then obtain b0 where b0: "b0 \<in> set (bp_buckets P)"
    and b_def: "b = bp_delete_key_from_bucket x b0"
    unfolding bp_delete_key_def by auto
  have "length (bp_bucket_entries b) \<le> length (bp_bucket_entries b0)"
    unfolding b_def bp_delete_key_from_bucket_def by simp
  also have "\<dots> \<le> 2 * bp_block_size P"
    using assms b0 unfolding bp_lazy_bucket_sizes_ok_def by blast
  finally show "length (bp_bucket_entries b) \<le>
    2 * bp_block_size (bp_delete_key x P)"
    unfolding bp_delete_key_def by simp
qed

lemma bp_delete_keys_lazy_bucket_sizes_ok:
  assumes "bp_lazy_bucket_sizes_ok P"
  shows "bp_lazy_bucket_sizes_ok (bp_delete_keys S P)"
  unfolding bp_lazy_bucket_sizes_ok_def
proof
  fix b
  assume b: "b \<in> set (bp_buckets (bp_delete_keys S P))"
  then obtain b0 where b0: "b0 \<in> set (bp_buckets P)"
    and b_def: "b = bp_delete_keys_from_bucket S b0"
    unfolding bp_delete_keys_def by auto
  have "length (bp_bucket_entries b) \<le> length (bp_bucket_entries b0)"
    unfolding b_def bp_delete_keys_from_bucket_def by simp
  also have "\<dots> \<le> 2 * bp_block_size P"
    using assms b0 unfolding bp_lazy_bucket_sizes_ok_def by blast
  finally show "length (bp_bucket_entries b) \<le>
    2 * bp_block_size (bp_delete_keys S P)"
    unfolding bp_delete_keys_def by simp
qed

lemma bp_delete_key_markers_lower_bound:
  assumes "bp_bucket_markers_lower_bound P"
  shows "bp_bucket_markers_lower_bound (bp_delete_key x P)"
  using assms
  unfolding bp_bucket_markers_lower_bound_def bp_delete_key_def
    bp_delete_key_from_bucket_def
  by auto

lemma bp_delete_keys_markers_lower_bound:
  assumes "bp_bucket_markers_lower_bound P"
  shows "bp_bucket_markers_lower_bound (bp_delete_keys S P)"
  using assms
  unfolding bp_bucket_markers_lower_bound_def bp_delete_keys_def
    bp_delete_keys_from_bucket_def
  by auto

lemma bp_delete_key_values_consistent:
  assumes "bp_values_consistent P"
  shows "bp_values_consistent (bp_delete_key x P)"
  using assms
  unfolding bp_values_consistent_def
  by (auto simp: bp_entries_delete_key)

lemma bp_delete_keys_values_consistent:
  assumes "bp_values_consistent P"
  shows "bp_values_consistent (bp_delete_keys S P)"
  using assms
  unfolding bp_values_consistent_def
  by (auto simp: bp_entries_delete_keys)

lemma bp_delete_key_distinct_keys:
  assumes "bp_distinct_keys P"
  shows "bp_distinct_keys (bp_delete_key x P)"
  using assms
  unfolding bp_distinct_keys_def
  by (simp add: bp_entries_delete_key distinct_map_fst_filter_neq)

lemma bp_delete_keys_distinct_keys:
  assumes "bp_distinct_keys P"
  shows "bp_distinct_keys (bp_delete_keys S P)"
  using assms
  unfolding bp_distinct_keys_def
  by (simp add: bp_entries_delete_keys distinct_map_fst_filter_notin)

lemma bp_bucket_boundaries_ok_delete_key_from_bucket:
  assumes "bp_bucket_boundaries_ok bs"
  shows "bp_bucket_boundaries_ok (map (bp_delete_key_from_bucket x) bs)"
  using assms
proof (induction bs)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  then show ?case
  proof (cases bs)
    case Nil
    then show ?thesis
      by simp
  next
    case (Cons c cs)
    have head:
      "\<forall>p\<in>set (bp_bucket_entries b). snd p \<le> bp_marker c"
      using Cons.prems Cons by simp
    have tail: "bp_bucket_boundaries_ok
      (map (bp_delete_key_from_bucket x) (c # cs))"
      using Cons.IH Cons.prems Cons by simp
    show ?thesis
      using Cons head tail
      unfolding bp_delete_key_from_bucket_def by auto
  qed
qed

lemma bp_bucket_boundaries_ok_delete_keys_from_bucket:
  assumes "bp_bucket_boundaries_ok bs"
  shows "bp_bucket_boundaries_ok (map (bp_delete_keys_from_bucket S) bs)"
  using assms
proof (induction bs)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  then show ?case
  proof (cases bs)
    case Nil
    then show ?thesis
      by simp
  next
    case (Cons c cs)
    have head:
      "\<forall>p\<in>set (bp_bucket_entries b). snd p \<le> bp_marker c"
      using Cons.prems Cons by simp
    have tail: "bp_bucket_boundaries_ok
      (map (bp_delete_keys_from_bucket S) (c # cs))"
      using Cons.IH Cons.prems Cons by simp
    show ?thesis
      using Cons head tail
      unfolding bp_delete_keys_from_bucket_def by auto
  qed
qed

lemma bp_delete_key_boundaries_state_ok:
  assumes "bp_bucket_boundaries_state_ok P"
  shows "bp_bucket_boundaries_state_ok (bp_delete_key x P)"
  using assms
  unfolding bp_bucket_boundaries_state_ok_def bp_delete_key_def
  by (simp add: bp_bucket_boundaries_ok_delete_key_from_bucket)

lemma bp_delete_keys_boundaries_state_ok:
  assumes "bp_bucket_boundaries_state_ok P"
  shows "bp_bucket_boundaries_state_ok (bp_delete_keys S P)"
  using assms
  unfolding bp_bucket_boundaries_state_ok_def bp_delete_keys_def
  by (simp add: bp_bucket_boundaries_ok_delete_keys_from_bucket)

lemma bp_delete_key_invariant:
  assumes "bp_invariant P"
  shows "bp_invariant (bp_delete_key x P)"
proof -
  have block: "0 < bp_block_size (bp_delete_key x P)"
    using assms unfolding bp_invariant_def bp_delete_key_def by simp
  have distinct: "bp_distinct_keys (bp_delete_key x P)"
    using assms unfolding bp_invariant_def
    by (auto intro: bp_delete_key_distinct_keys)
  have sizes: "bp_bucket_sizes_ok (bp_delete_key x P)"
    using assms unfolding bp_invariant_def
    by (auto intro: bp_delete_key_bucket_sizes_ok)
  have sorted: "bp_bucket_markers_sorted (bp_delete_key x P)"
    using assms unfolding bp_invariant_def
    by (auto intro: bp_delete_key_markers_sorted)
  have markers: "bp_bucket_markers_lower_bound (bp_delete_key x P)"
    using assms unfolding bp_invariant_def
    by (auto intro: bp_delete_key_markers_lower_bound)
  have vals: "bp_values_consistent (bp_delete_key x P)"
    using assms unfolding bp_invariant_def
    by (auto intro: bp_delete_key_values_consistent)
  show ?thesis
    unfolding bp_invariant_def using block distinct sizes sorted markers vals by blast
qed

lemma bp_delete_key_ordered_invariant:
  assumes "bp_ordered_invariant P"
  shows "bp_ordered_invariant (bp_delete_key x P)"
  unfolding bp_ordered_invariant_def
  using bp_delete_key_invariant[OF bp_ordered_invariant_invariant[OF assms]]
    bp_delete_key_boundaries_state_ok
      [OF bp_ordered_invariant_boundaries_state_ok[OF assms]]
  by blast

lemma bp_delete_key_lazy_invariant:
  assumes "bp_lazy_invariant P"
  shows "bp_lazy_invariant (bp_delete_key x P)"
proof -
  have block: "0 < bp_block_size (bp_delete_key x P)"
    using assms unfolding bp_lazy_invariant_def bp_delete_key_def by simp
  have distinct: "bp_distinct_keys (bp_delete_key x P)"
    using assms unfolding bp_lazy_invariant_def
    by (auto intro: bp_delete_key_distinct_keys)
  have sizes: "bp_lazy_bucket_sizes_ok (bp_delete_key x P)"
    using assms unfolding bp_lazy_invariant_def
    by (auto intro: bp_delete_key_lazy_bucket_sizes_ok)
  have sorted: "bp_bucket_markers_sorted (bp_delete_key x P)"
    using assms unfolding bp_lazy_invariant_def
    by (auto intro: bp_delete_key_markers_sorted)
  have markers: "bp_bucket_markers_lower_bound (bp_delete_key x P)"
    using assms unfolding bp_lazy_invariant_def
    by (auto intro: bp_delete_key_markers_lower_bound)
  have vals: "bp_values_consistent (bp_delete_key x P)"
    using assms unfolding bp_lazy_invariant_def
    by (auto intro: bp_delete_key_values_consistent)
  show ?thesis
    unfolding bp_lazy_invariant_def
    using block distinct sizes sorted markers vals by blast
qed

lemma bp_delete_key_lazy_ordered_invariant:
  assumes "bp_lazy_ordered_invariant P"
  shows "bp_lazy_ordered_invariant (bp_delete_key x P)"
  unfolding bp_lazy_ordered_invariant_def
  using bp_delete_key_lazy_invariant
      [OF bp_lazy_ordered_invariant_lazy_invariant[OF assms]]
    bp_delete_key_boundaries_state_ok
      [OF bp_lazy_ordered_invariant_boundaries_state_ok[OF assms]]
  by blast

lemma bp_delete_keys_invariant:
  assumes "bp_invariant P"
  shows "bp_invariant (bp_delete_keys S P)"
proof -
  have block: "0 < bp_block_size (bp_delete_keys S P)"
    using assms unfolding bp_invariant_def bp_delete_keys_def by simp
  have distinct: "bp_distinct_keys (bp_delete_keys S P)"
    using assms unfolding bp_invariant_def
    by (auto intro: bp_delete_keys_distinct_keys)
  have sizes: "bp_bucket_sizes_ok (bp_delete_keys S P)"
    using assms unfolding bp_invariant_def
    by (auto intro: bp_delete_keys_bucket_sizes_ok)
  have sorted: "bp_bucket_markers_sorted (bp_delete_keys S P)"
    using assms unfolding bp_invariant_def
    by (auto intro: bp_delete_keys_markers_sorted)
  have markers: "bp_bucket_markers_lower_bound (bp_delete_keys S P)"
    using assms unfolding bp_invariant_def
    by (auto intro: bp_delete_keys_markers_lower_bound)
  have vals: "bp_values_consistent (bp_delete_keys S P)"
    using assms unfolding bp_invariant_def
    by (auto intro: bp_delete_keys_values_consistent)
  show ?thesis
    unfolding bp_invariant_def using block distinct sizes sorted markers vals by blast
qed

lemma bp_delete_keys_ordered_invariant:
  assumes "bp_ordered_invariant P"
  shows "bp_ordered_invariant (bp_delete_keys S P)"
  unfolding bp_ordered_invariant_def
  using bp_delete_keys_invariant[OF bp_ordered_invariant_invariant[OF assms]]
    bp_delete_keys_boundaries_state_ok
      [OF bp_ordered_invariant_boundaries_state_ok[OF assms]]
  by blast

lemma bp_delete_keys_lazy_invariant:
  assumes "bp_lazy_invariant P"
  shows "bp_lazy_invariant (bp_delete_keys S P)"
proof -
  have block: "0 < bp_block_size (bp_delete_keys S P)"
    using assms unfolding bp_lazy_invariant_def bp_delete_keys_def by simp
  have distinct: "bp_distinct_keys (bp_delete_keys S P)"
    using assms unfolding bp_lazy_invariant_def
    by (auto intro: bp_delete_keys_distinct_keys)
  have sizes: "bp_lazy_bucket_sizes_ok (bp_delete_keys S P)"
    using assms unfolding bp_lazy_invariant_def
    by (auto intro: bp_delete_keys_lazy_bucket_sizes_ok)
  have sorted: "bp_bucket_markers_sorted (bp_delete_keys S P)"
    using assms unfolding bp_lazy_invariant_def
    by (auto intro: bp_delete_keys_markers_sorted)
  have markers: "bp_bucket_markers_lower_bound (bp_delete_keys S P)"
    using assms unfolding bp_lazy_invariant_def
    by (auto intro: bp_delete_keys_markers_lower_bound)
  have vals: "bp_values_consistent (bp_delete_keys S P)"
    using assms unfolding bp_lazy_invariant_def
    by (auto intro: bp_delete_keys_values_consistent)
  show ?thesis
    unfolding bp_lazy_invariant_def
    using block distinct sizes sorted markers vals by blast
qed

lemma bp_delete_keys_view:
  "bp_view (bp_delete_keys S P) =
     \<lparr> keys_of = keys_of (bp_view P) - S,
       value_of = value_of (bp_view P) \<rparr>"
  unfolding bp_view_def by (simp add: bp_entries_delete_keys)

lemma bp_entry_keys_insert_bucket_state [simp]:
  "bp_entry_keys (bp_entries
      (P\<lparr>bp_buckets := bp_insert_bucket p (bp_buckets P)\<rparr>)) =
     insert (fst p) (bp_entry_keys (bp_entries P))"
  unfolding bp_entries_def by simp

lemma bp_entry_keys_insert_bucket_state_values [simp]:
  "bp_entry_keys (bp_entries
      (P\<lparr>bp_buckets := bp_insert_bucket p (bp_buckets P),
        bp_values := f\<rparr>)) =
     insert (fst p) (bp_entry_keys (bp_entries P))"
  unfolding bp_entries_def by simp

lemma bp_insert_invariant:
  assumes inv: "bp_invariant P"
  shows "bp_invariant (bp_insert x b P)"
proof -
  let ?old_keys = "bp_entry_keys (bp_entries P)"
  let ?b = "if x \<in> ?old_keys then min (bp_values P x) b else b"
  let ?P0 = "bp_delete_key x P"
  have inv0: "bp_invariant ?P0"
    by (rule bp_delete_key_invariant[OF inv])
  have block_pos: "0 < bp_block_size ?P0"
    using inv0 unfolding bp_invariant_def by blast
  have distinct0:
    "distinct (map fst (bp_entries ?P0))"
    using inv0 unfolding bp_invariant_def bp_distinct_keys_def by blast
  have sizes0:
    "\<forall>c\<in>set (bp_buckets ?P0).
      length (bp_bucket_entries c) \<le> bp_block_size ?P0"
    using inv0 unfolding bp_invariant_def bp_bucket_sizes_ok_def by blast
  have sorted0:
    "sorted_wrt (\<lambda>c d. bp_marker c \<le> bp_marker d) (bp_buckets ?P0)"
    using inv0 unfolding bp_invariant_def bp_bucket_markers_sorted_def by blast
  have markers0:
    "\<forall>c\<in>set (bp_buckets ?P0). \<forall>p\<in>set (bp_bucket_entries c).
      bp_marker c \<le> snd p"
    using inv0 unfolding bp_invariant_def bp_bucket_markers_lower_bound_def by blast
  have values0:
    "\<forall>p\<in>set (bp_entries ?P0). bp_values ?P0 (fst p) = snd p"
    using inv0 by (auto simp: bp_invariant_def bp_values_consistent_def)
  have fresh: "x \<notin> bp_entry_keys (bp_entries ?P0)"
    unfolding bp_entries_delete_key by simp
  have distinct_insert:
    "distinct (map fst
      (bp_bucket_entries_flat (bp_insert_bucket (x, ?b) (bp_buckets ?P0))))"
    by (rule bp_insert_bucket_distinct_keys)
      (use distinct0 fresh in \<open>simp_all add: bp_entries_def\<close>)
  have values0_P:
    "\<forall>p\<in>set (bp_entries ?P0). bp_values P (fst p) = snd p"
    using values0 unfolding bp_delete_key_def by simp
  have values_insert:
    "\<forall>p\<in>set
        (bp_bucket_entries_flat (bp_insert_bucket (x, ?b) (bp_buckets ?P0))).
      ((bp_values P)(x := ?b)) (fst p) = snd p"
  proof
    fix p
    assume p:
      "p \<in> set (bp_bucket_entries_flat
        (bp_insert_bucket (x, ?b) (bp_buckets ?P0)))"
    then have p_cases: "p = (x, ?b) \<or>
        p \<in> set (bp_bucket_entries_flat (bp_buckets ?P0))"
      using set_bp_bucket_entries_flat_insert_bucket[of "(x, ?b)" "bp_buckets ?P0"]
      by auto
    from p_cases show "((bp_values P)(x := ?b)) (fst p) = snd p"
    proof
      assume "p = (x, ?b)"
      then show ?thesis by simp
    next
      assume p_flat: "p \<in> set (bp_bucket_entries_flat (bp_buckets ?P0))"
      then have p_old: "p \<in> set (bp_entries ?P0)"
        unfolding bp_entries_def .
      have "fst p \<noteq> x"
      proof
        assume "fst p = x"
        then have "x \<in> bp_entry_keys (bp_entries ?P0)"
          using p_old unfolding bp_entry_keys_def by auto
        then show False
          using fresh by simp
      qed
      moreover have "bp_values P (fst p) = snd p"
        using values0_P p_old by blast
      ultimately show ?thesis
        by simp
    qed
  qed
  show ?thesis
    unfolding bp_insert_def Let_def bp_invariant_def
  proof (intro conjI)
    show "0 < bp_block_size
      (?P0\<lparr>bp_buckets := bp_insert_bucket (x, ?b) (bp_buckets ?P0),
        bp_values := (bp_values P)(x := ?b)\<rparr>)"
      using block_pos by simp
    show "bp_distinct_keys
      (?P0\<lparr>bp_buckets := bp_insert_bucket (x, ?b) (bp_buckets ?P0),
        bp_values := (bp_values P)(x := ?b)\<rparr>)"
      using distinct_insert
      unfolding bp_distinct_keys_def bp_entries_def by simp
    show "bp_bucket_sizes_ok
      (?P0\<lparr>bp_buckets := bp_insert_bucket (x, ?b) (bp_buckets ?P0),
        bp_values := (bp_values P)(x := ?b)\<rparr>)"
      using bp_insert_bucket_sizes_ok[OF sizes0 block_pos]
      unfolding bp_bucket_sizes_ok_def by simp
    show "bp_bucket_markers_sorted
      (?P0\<lparr>bp_buckets := bp_insert_bucket (x, ?b) (bp_buckets ?P0),
        bp_values := (bp_values P)(x := ?b)\<rparr>)"
      using bp_insert_bucket_markers_sorted[OF sorted0]
      unfolding bp_bucket_markers_sorted_def by simp
    show "bp_bucket_markers_lower_bound
      (?P0\<lparr>bp_buckets := bp_insert_bucket (x, ?b) (bp_buckets ?P0),
        bp_values := (bp_values P)(x := ?b)\<rparr>)"
      using bp_insert_bucket_markers_lower_bound[OF markers0]
      unfolding bp_bucket_markers_lower_bound_def by simp
    show "bp_values_consistent
      (?P0\<lparr>bp_buckets := bp_insert_bucket (x, ?b) (bp_buckets ?P0),
        bp_values := (bp_values P)(x := ?b)\<rparr>)"
      using values_insert
      unfolding bp_values_consistent_def bp_entries_def by simp
  qed
qed

lemma bp_insert_keys [simp]:
  "bp_entry_keys (bp_entries (bp_insert x b P)) =
     insert x (bp_entry_keys (bp_entries P))"
proof -
  let ?b = "if x \<in> bp_entry_keys (bp_entries P)
    then min (bp_values P x) b else b"
  let ?P0 = "bp_delete_key x P"
  have "bp_entry_keys
      (bp_entries
        (?P0\<lparr>bp_buckets := bp_insert_bucket (x, ?b) (bp_buckets ?P0),
          bp_values := (bp_values P)(x := ?b)\<rparr>)) =
    insert x (bp_entry_keys (bp_entries ?P0))"
    by simp
  also have "\<dots> = insert x (bp_entry_keys (bp_entries P))"
    by simp
  finally show ?thesis
    unfolding bp_insert_def Let_def .
qed

lemma bp_insert_values [simp]:
  "bp_values (bp_insert x b P) =
     (bp_values P)
       (x := if x \<in> bp_entry_keys (bp_entries P)
             then min (bp_values P x) b else b)"
  unfolding bp_insert_def Let_def by simp

theorem bp_insert_refines_min_update:
  "bp_view (bp_insert x b P) = min_update (bp_view P) x b"
  unfolding bp_view_def min_update_def by simp

theorem bp_insert_refines_insert_spec:
  "insert_spec (bp_view P) x b (bp_view (bp_insert x b P))"
  unfolding bp_insert_refines_min_update
  by (rule min_update_insert_spec)

theorem bp_insert_preserves_upper_bound:
  assumes upper: "partition_upper_bound (bp_view P) B"
    and b_lt: "b < B"
  shows "partition_upper_bound (bp_view (bp_insert x b P)) B"
  unfolding bp_insert_refines_min_update
  by (rule min_update_preserves_upper_bound[OF upper b_lt])

lemma bp_local_insert_state_keys:
  assumes M_pos: "0 < bp_block_size P"
  shows "bp_entry_keys (bp_entries (bp_local_insert_state x b P)) =
    insert x (bp_entry_keys (bp_entries P))"
proof -
  let ?b = "if x \<in> bp_entry_keys (bp_entries P)
    then min (bp_values P x) b else b"
  let ?P0 = "bp_delete_key x P"
  have M0: "0 < bp_block_size ?P0"
    using M_pos unfolding bp_delete_key_def by simp
  have keys_step:
    "bp_entry_keys
      (bp_entries
        (?P0\<lparr>bp_buckets :=
             bp_local_insert_bucket (bp_block_size ?P0) (x, ?b)
               (bp_buckets ?P0),
           bp_values := (bp_values P)(x := ?b)\<rparr>)) =
     insert x (bp_entry_keys (bp_entries ?P0))"
    using set_bp_bucket_entries_flat_local_insert_bucket
      [OF M0, of "(x, ?b)" "bp_buckets ?P0"]
    unfolding bp_entries_def bp_entry_keys_def by auto
  show ?thesis
    unfolding bp_local_insert_state_def Let_def
    using keys_step by simp
qed

lemma bp_local_insert_state_values [simp]:
  "bp_values (bp_local_insert_state x b P) =
     (bp_values P)
       (x := if x \<in> bp_entry_keys (bp_entries P)
             then min (bp_values P x) b else b)"
  unfolding bp_local_insert_state_def Let_def by simp

theorem bp_local_insert_state_refines_min_update:
  assumes "0 < bp_block_size P"
  shows "bp_view (bp_local_insert_state x b P) = min_update (bp_view P) x b"
  using bp_local_insert_state_keys[OF assms, of x b]
  unfolding bp_view_def min_update_def by simp

theorem bp_local_insert_state_refines_insert_spec:
  assumes "0 < bp_block_size P"
  shows "insert_spec (bp_view P) x b
    (bp_view (bp_local_insert_state x b P))"
  unfolding bp_local_insert_state_refines_min_update[OF assms]
  by (rule min_update_insert_spec)

theorem bp_local_insert_state_preserves_upper_bound:
  assumes M_pos: "0 < bp_block_size P"
    and upper: "partition_upper_bound (bp_view P) B"
    and b_lt: "b < B"
  shows "partition_upper_bound (bp_view (bp_local_insert_state x b P)) B"
  unfolding bp_local_insert_state_refines_min_update[OF M_pos]
  by (rule min_update_preserves_upper_bound[OF upper b_lt])

lemma bp_lazy_insert_state_keys:
  assumes M_pos: "0 < bp_block_size P"
  shows "bp_entry_keys (bp_entries (bp_lazy_insert_state x b P)) =
    insert x (bp_entry_keys (bp_entries P))"
proof -
  let ?b = "if x \<in> bp_entry_keys (bp_entries P)
    then min (bp_values P x) b else b"
  let ?P0 = "bp_delete_key x P"
  have M0: "0 < bp_block_size ?P0"
    using M_pos unfolding bp_delete_key_def by simp
  have keys_step:
    "bp_entry_keys
      (bp_entries
        (?P0\<lparr>bp_buckets :=
             bp_lazy_insert_bucket (bp_block_size ?P0) (x, ?b)
               (bp_buckets ?P0),
           bp_values := (bp_values P)(x := ?b)\<rparr>)) =
     insert x (bp_entry_keys (bp_entries ?P0))"
    using set_bp_bucket_entries_flat_lazy_insert_bucket
      [OF M0, of "(x, ?b)" "bp_buckets ?P0"]
    unfolding bp_entries_def bp_entry_keys_def by auto
  show ?thesis
    unfolding bp_lazy_insert_state_def Let_def
    using keys_step by simp
qed

lemma bp_lazy_insert_state_values [simp]:
  "bp_values (bp_lazy_insert_state x b P) =
     (bp_values P)
       (x := if x \<in> bp_entry_keys (bp_entries P)
             then min (bp_values P x) b else b)"
  unfolding bp_lazy_insert_state_def Let_def by simp

theorem bp_lazy_insert_state_refines_min_update:
  assumes "0 < bp_block_size P"
  shows "bp_view (bp_lazy_insert_state x b P) =
    min_update (bp_view P) x b"
  using bp_lazy_insert_state_keys[OF assms, of x b]
  unfolding bp_view_def min_update_def by simp

theorem bp_lazy_insert_state_refines_insert_spec:
  assumes "0 < bp_block_size P"
  shows "insert_spec (bp_view P) x b
    (bp_view (bp_lazy_insert_state x b P))"
  unfolding bp_lazy_insert_state_refines_min_update[OF assms]
  by (rule min_update_insert_spec)

theorem bp_lazy_insert_state_preserves_upper_bound:
  assumes M_pos: "0 < bp_block_size P"
    and upper: "partition_upper_bound (bp_view P) B"
    and b_lt: "b < B"
  shows "partition_upper_bound (bp_view (bp_lazy_insert_state x b P)) B"
  unfolding bp_lazy_insert_state_refines_min_update[OF M_pos]
  by (rule min_update_preserves_upper_bound[OF upper b_lt])

lemma bp_lazy_insert_state_lazy_bucket_sizes_ok:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "bp_lazy_bucket_sizes_ok (bp_lazy_insert_state x b P)"
proof -
  let ?old_keys = "bp_entry_keys (bp_entries P)"
  let ?b = "if x \<in> ?old_keys then min (bp_values P x) b else b"
  let ?P0 = "bp_delete_key x P"
  have inv: "bp_lazy_invariant P"
    by (rule bp_lazy_ordered_invariant_lazy_invariant[OF lazy])
  have inv0: "bp_lazy_invariant ?P0"
    by (rule bp_delete_key_lazy_invariant[OF inv])
  have M_pos: "0 < bp_block_size ?P0"
    using inv0 unfolding bp_lazy_invariant_def by blast
  have sizes0:
    "\<forall>c\<in>set (bp_buckets ?P0).
      length (bp_bucket_entries c) \<le> 2 * bp_block_size ?P0"
    using inv0 unfolding bp_lazy_invariant_def
      bp_lazy_bucket_sizes_ok_def by blast
  have sizes:
    "\<forall>c\<in>set
        (bp_lazy_insert_bucket (bp_block_size ?P0) (x, ?b)
          (bp_buckets ?P0)).
      length (bp_bucket_entries c) \<le> 2 * bp_block_size ?P0"
    by (rule bp_lazy_insert_bucket_sizes_ok[OF M_pos sizes0])
  show ?thesis
    unfolding bp_lazy_insert_state_def Let_def bp_lazy_bucket_sizes_ok_def
    using sizes by simp
qed

lemma bp_lazy_insert_state_markers_lower_bound:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "bp_bucket_markers_lower_bound (bp_lazy_insert_state x b P)"
proof -
  let ?old_keys = "bp_entry_keys (bp_entries P)"
  let ?b = "if x \<in> ?old_keys then min (bp_values P x) b else b"
  let ?P0 = "bp_delete_key x P"
  have inv: "bp_lazy_invariant P"
    by (rule bp_lazy_ordered_invariant_lazy_invariant[OF lazy])
  have inv0: "bp_lazy_invariant ?P0"
    by (rule bp_delete_key_lazy_invariant[OF inv])
  have M_pos: "0 < bp_block_size ?P0"
    using inv0 unfolding bp_lazy_invariant_def by blast
  have lower0:
    "\<forall>c\<in>set (bp_buckets ?P0). \<forall>p\<in>set (bp_bucket_entries c).
      bp_marker c \<le> snd p"
    using inv0 unfolding bp_lazy_invariant_def
      bp_bucket_markers_lower_bound_def by blast
  have lower:
    "\<forall>c\<in>set
        (bp_lazy_insert_bucket (bp_block_size ?P0) (x, ?b)
          (bp_buckets ?P0)).
      \<forall>q\<in>set (bp_bucket_entries c). bp_marker c \<le> snd q"
    by (rule bp_lazy_insert_bucket_markers_lower_bound[OF M_pos lower0])
  show ?thesis
    unfolding bp_lazy_insert_state_def Let_def
      bp_bucket_markers_lower_bound_def
    using lower by simp
qed

lemma bp_lazy_insert_state_values_consistent:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "bp_values_consistent (bp_lazy_insert_state x b P)"
proof -
  let ?old_keys = "bp_entry_keys (bp_entries P)"
  let ?b = "if x \<in> ?old_keys then min (bp_values P x) b else b"
  let ?P0 = "bp_delete_key x P"
  let ?M = "bp_block_size ?P0"
  let ?bs = "bp_buckets ?P0"
  let ?new_bs = "bp_lazy_insert_bucket ?M (x, ?b) ?bs"
  let ?P' = "?P0\<lparr>bp_buckets := ?new_bs,
      bp_values := (bp_values P)(x := ?b)\<rparr>"
  have inv: "bp_lazy_invariant P"
    by (rule bp_lazy_ordered_invariant_lazy_invariant[OF lazy])
  have inv0: "bp_lazy_invariant ?P0"
    by (rule bp_delete_key_lazy_invariant[OF inv])
  have M_pos: "0 < ?M"
    using inv0 unfolding bp_lazy_invariant_def by blast
  have values0:
    "\<forall>p\<in>set (bp_entries ?P0). bp_values ?P0 (fst p) = snd p"
    using inv0 unfolding bp_lazy_invariant_def bp_values_consistent_def
    by blast
  have values0_P:
    "\<forall>p\<in>set (bp_entries ?P0). bp_values P (fst p) = snd p"
    using values0 unfolding bp_delete_key_def by simp
  have fresh: "x \<notin> bp_entry_keys (bp_entries ?P0)"
    by simp
  have values_insert:
    "\<forall>p\<in>set (bp_bucket_entries_flat ?new_bs).
      ((bp_values P)(x := ?b)) (fst p) = snd p"
  proof
    fix p
    assume p: "p \<in> set (bp_bucket_entries_flat ?new_bs)"
    then have p_cases:
      "p = (x, ?b) \<or> p \<in> set (bp_bucket_entries_flat ?bs)"
      using set_bp_bucket_entries_flat_lazy_insert_bucket
        [OF M_pos, of "(x, ?b)" ?bs]
      by auto
    from p_cases show "((bp_values P)(x := ?b)) (fst p) = snd p"
    proof
      assume "p = (x, ?b)"
      then show ?thesis by simp
    next
      assume p_flat: "p \<in> set (bp_bucket_entries_flat ?bs)"
      then have p_old: "p \<in> set (bp_entries ?P0)"
        unfolding bp_entries_def .
      have "fst p \<noteq> x"
      proof
        assume "fst p = x"
        then have "x \<in> bp_entry_keys (bp_entries ?P0)"
          using p_old unfolding bp_entry_keys_def by auto
        then show False
          using fresh by simp
      qed
      moreover have "bp_values P (fst p) = snd p"
        using values0_P p_old by blast
      ultimately show ?thesis
        by simp
    qed
  qed
  have state: "bp_lazy_insert_state x b P = ?P'"
    unfolding bp_lazy_insert_state_def Let_def by simp
  have "bp_values_consistent ?P'"
    using values_insert
    unfolding bp_values_consistent_def bp_entries_def by simp
  show ?thesis
    unfolding state by (rule \<open>bp_values_consistent ?P'\<close>)
qed

lemma bp_lazy_insert_state_distinct_keys:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "bp_distinct_keys (bp_lazy_insert_state x b P)"
proof -
  let ?old_keys = "bp_entry_keys (bp_entries P)"
  let ?b = "if x \<in> ?old_keys then min (bp_values P x) b else b"
  let ?P0 = "bp_delete_key x P"
  let ?M = "bp_block_size ?P0"
  let ?bs = "bp_buckets ?P0"
  let ?new_bs = "bp_lazy_insert_bucket ?M (x, ?b) ?bs"
  let ?P' = "?P0\<lparr>bp_buckets := ?new_bs,
      bp_values := (bp_values P)(x := ?b)\<rparr>"
  have inv: "bp_lazy_invariant P"
    by (rule bp_lazy_ordered_invariant_lazy_invariant[OF lazy])
  have inv0: "bp_lazy_invariant ?P0"
    by (rule bp_delete_key_lazy_invariant[OF inv])
  have M_pos: "0 < ?M"
    using inv0 unfolding bp_lazy_invariant_def by blast
  have distinct0:
    "distinct (map fst (bp_entries ?P0))"
    using inv0 unfolding bp_lazy_invariant_def bp_distinct_keys_def
    by blast
  have fresh: "x \<notin> bp_entry_keys (bp_entries ?P0)"
    by simp
  have distinct_lazy:
    "distinct (map fst (bp_bucket_entries_flat ?new_bs))"
    by (rule bp_lazy_insert_bucket_distinct_keys[OF M_pos])
      (use distinct0 fresh in \<open>simp_all add: bp_entries_def\<close>)
  have state: "bp_lazy_insert_state x b P = ?P'"
    unfolding bp_lazy_insert_state_def Let_def by simp
  have "bp_distinct_keys ?P'"
    using distinct_lazy unfolding bp_distinct_keys_def bp_entries_def
    by simp
  show ?thesis
    unfolding state by (rule \<open>bp_distinct_keys ?P'\<close>)
qed

lemma bp_lazy_insert_state_markers_sorted:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "bp_bucket_markers_sorted (bp_lazy_insert_state x b P)"
proof -
  let ?old_keys = "bp_entry_keys (bp_entries P)"
  let ?b = "if x \<in> ?old_keys then min (bp_values P x) b else b"
  let ?P0 = "bp_delete_key x P"
  let ?M = "bp_block_size ?P0"
  let ?bs = "bp_buckets ?P0"
  let ?new_bs = "bp_lazy_insert_bucket ?M (x, ?b) ?bs"
  have inv: "bp_lazy_invariant P"
    by (rule bp_lazy_ordered_invariant_lazy_invariant[OF lazy])
  have inv0: "bp_lazy_invariant ?P0"
    by (rule bp_delete_key_lazy_invariant[OF inv])
  have boundaries0_state: "bp_bucket_boundaries_state_ok ?P0"
    by (rule bp_delete_key_boundaries_state_ok
        [OF bp_lazy_ordered_invariant_boundaries_state_ok[OF lazy]])
  have M_pos: "0 < ?M"
    using inv0 unfolding bp_lazy_invariant_def by blast
  have sorted0:
    "sorted_wrt (\<lambda>c d. bp_marker c \<le> bp_marker d) ?bs"
    using inv0 unfolding bp_lazy_invariant_def
      bp_bucket_markers_sorted_def by blast
  have lower0:
    "\<forall>c\<in>set ?bs. \<forall>p\<in>set (bp_bucket_entries c).
      bp_marker c \<le> snd p"
    using inv0 unfolding bp_lazy_invariant_def
      bp_bucket_markers_lower_bound_def by blast
  have boundaries0: "bp_bucket_boundaries_ok ?bs"
    using boundaries0_state unfolding bp_bucket_boundaries_state_ok_def .
  have sorted_new:
    "sorted_wrt (\<lambda>c d. bp_marker c \<le> bp_marker d) ?new_bs"
    by (rule bp_lazy_insert_bucket_markers_sorted
        [OF M_pos sorted0 lower0 boundaries0])
  show ?thesis
    unfolding bp_lazy_insert_state_def Let_def
      bp_bucket_markers_sorted_def
    using sorted_new by simp
qed

lemma bp_lazy_insert_state_boundaries_state_ok:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "bp_bucket_boundaries_state_ok (bp_lazy_insert_state x b P)"
proof -
  let ?old_keys = "bp_entry_keys (bp_entries P)"
  let ?b = "if x \<in> ?old_keys then min (bp_values P x) b else b"
  let ?P0 = "bp_delete_key x P"
  let ?M = "bp_block_size ?P0"
  let ?bs = "bp_buckets ?P0"
  let ?new_bs = "bp_lazy_insert_bucket ?M (x, ?b) ?bs"
  have inv: "bp_lazy_invariant P"
    by (rule bp_lazy_ordered_invariant_lazy_invariant[OF lazy])
  have inv0: "bp_lazy_invariant ?P0"
    by (rule bp_delete_key_lazy_invariant[OF inv])
  have boundaries0_state: "bp_bucket_boundaries_state_ok ?P0"
    by (rule bp_delete_key_boundaries_state_ok
        [OF bp_lazy_ordered_invariant_boundaries_state_ok[OF lazy]])
  have M_pos: "0 < ?M"
    using inv0 unfolding bp_lazy_invariant_def by blast
  have sorted0:
    "sorted_wrt (\<lambda>c d. bp_marker c \<le> bp_marker d) ?bs"
    using inv0 unfolding bp_lazy_invariant_def
      bp_bucket_markers_sorted_def by blast
  have lower0:
    "\<forall>c\<in>set ?bs. \<forall>p\<in>set (bp_bucket_entries c).
      bp_marker c \<le> snd p"
    using inv0 unfolding bp_lazy_invariant_def
      bp_bucket_markers_lower_bound_def by blast
  have boundaries0: "bp_bucket_boundaries_ok ?bs"
    using boundaries0_state unfolding bp_bucket_boundaries_state_ok_def .
  have boundaries_new: "bp_bucket_boundaries_ok ?new_bs"
    by (rule bp_lazy_insert_bucket_boundaries_ok
        [OF M_pos sorted0 lower0 boundaries0])
  show ?thesis
    unfolding bp_lazy_insert_state_def Let_def
      bp_bucket_boundaries_state_ok_def
    using boundaries_new by simp
qed

lemma bp_lazy_insert_state_lazy_invariant:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "bp_lazy_invariant (bp_lazy_insert_state x b P)"
proof -
  have inv: "bp_lazy_invariant P"
    by (rule bp_lazy_ordered_invariant_lazy_invariant[OF lazy])
  have M_pos: "0 < bp_block_size P"
    using inv unfolding bp_lazy_invariant_def by blast
  have block:
    "bp_block_size (bp_lazy_insert_state x b P) = bp_block_size P"
    unfolding bp_lazy_insert_state_def bp_delete_key_def
    by (simp add: Let_def split: if_splits)
  show ?thesis
    unfolding bp_lazy_invariant_def
  proof (intro conjI)
    show "0 < bp_block_size (bp_lazy_insert_state x b P)"
      using M_pos block by simp
    show "bp_distinct_keys (bp_lazy_insert_state x b P)"
      by (rule bp_lazy_insert_state_distinct_keys[OF lazy])
    show "bp_lazy_bucket_sizes_ok (bp_lazy_insert_state x b P)"
      by (rule bp_lazy_insert_state_lazy_bucket_sizes_ok[OF lazy])
    show "bp_bucket_markers_sorted (bp_lazy_insert_state x b P)"
      by (rule bp_lazy_insert_state_markers_sorted[OF lazy])
    show "bp_bucket_markers_lower_bound (bp_lazy_insert_state x b P)"
      by (rule bp_lazy_insert_state_markers_lower_bound[OF lazy])
    show "bp_values_consistent (bp_lazy_insert_state x b P)"
      by (rule bp_lazy_insert_state_values_consistent[OF lazy])
  qed
qed

lemma bp_lazy_insert_state_lazy_ordered_invariant:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "bp_lazy_ordered_invariant (bp_lazy_insert_state x b P)"
  unfolding bp_lazy_ordered_invariant_def
  using bp_lazy_insert_state_lazy_invariant[OF lazy]
    bp_lazy_insert_state_boundaries_state_ok[OF lazy]
  by blast

lemma length_bp_lazy_insert_state_entries:
  assumes M_pos: "0 < bp_block_size P"
  shows "length (bp_entries (bp_lazy_insert_state x b P)) =
    Suc (length (bp_entries (bp_delete_key x P)))"
proof -
  let ?old_keys = "bp_entry_keys (bp_entries P)"
  let ?b = "if x \<in> ?old_keys then min (bp_values P x) b else b"
  let ?P0 = "bp_delete_key x P"
  let ?M = "bp_block_size ?P0"
  let ?new_bs = "bp_lazy_insert_bucket ?M (x, ?b) (bp_buckets ?P0)"
  let ?P' = "?P0\<lparr>bp_buckets := ?new_bs,
      bp_values := (bp_values P)(x := ?b)\<rparr>"
  have M0: "0 < ?M"
    using M_pos unfolding bp_delete_key_def by simp
  have len:
    "length (bp_bucket_entries_flat ?new_bs) =
      Suc (length (bp_bucket_entries_flat (bp_buckets ?P0)))"
    by (rule length_bp_bucket_entries_flat_lazy_insert_bucket[OF M0])
  have state: "bp_lazy_insert_state x b P = ?P'"
    unfolding bp_lazy_insert_state_def Let_def by simp
  have "length (bp_entries ?P') =
    Suc (length (bp_entries ?P0))"
    using len unfolding bp_entries_def by simp
  show ?thesis
    unfolding state by (rule \<open>length (bp_entries ?P') =
      Suc (length (bp_entries ?P0))\<close>)
qed

lemma length_bp_lazy_insert_state_entries_ge:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "length (bp_entries P) \<le>
    length (bp_entries (bp_lazy_insert_state x b P))"
proof -
  have inv: "bp_lazy_invariant P"
    by (rule bp_lazy_ordered_invariant_lazy_invariant[OF lazy])
  have M_pos: "0 < bp_block_size P"
    using inv unfolding bp_lazy_invariant_def by blast
  have distinct: "bp_distinct_keys P"
    using inv unfolding bp_lazy_invariant_def by blast
  have delete_ge:
    "length (bp_entries P) \<le>
      Suc (length (bp_entries (bp_delete_key x P)))"
    by (rule length_bp_entries_delete_key_ge_pred[OF distinct])
  have insert_len:
    "length (bp_entries (bp_lazy_insert_state x b P)) =
      Suc (length (bp_entries (bp_delete_key x P)))"
    by (rule length_bp_lazy_insert_state_entries[OF M_pos])
  show ?thesis
    using delete_ge unfolding insert_len .
qed

lemma length_bp_lazy_insert_state_buckets_le:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "length (bp_buckets (bp_lazy_insert_state x b P)) \<le>
    length (bp_buckets P) + 2"
proof -
  let ?old_keys = "bp_entry_keys (bp_entries P)"
  let ?b = "if x \<in> ?old_keys then min (bp_values P x) b else b"
  let ?P0 = "bp_delete_key x P"
  let ?M = "bp_block_size ?P0"
  let ?bs = "bp_buckets ?P0"
  let ?new_bs = "bp_lazy_insert_bucket ?M (x, ?b) ?bs"
  let ?P' = "?P0\<lparr>bp_buckets := ?new_bs,
      bp_values := (bp_values P)(x := ?b)\<rparr>"
  have inv: "bp_lazy_invariant P"
    by (rule bp_lazy_ordered_invariant_lazy_invariant[OF lazy])
  have inv0: "bp_lazy_invariant ?P0"
    by (rule bp_delete_key_lazy_invariant[OF inv])
  have M_pos: "0 < ?M"
    using inv0 unfolding bp_lazy_invariant_def by blast
  have sizes0:
    "\<forall>b\<in>set ?bs. length (bp_bucket_entries b) \<le> 2 * ?M"
    using inv0 unfolding bp_lazy_invariant_def
      bp_lazy_bucket_sizes_ok_def by blast
  have len_new:
    "length ?new_bs \<le> length ?bs + 2"
    by (rule length_bp_lazy_insert_bucket_le[OF M_pos sizes0])
  have state: "bp_lazy_insert_state x b P = ?P'"
    unfolding bp_lazy_insert_state_def Let_def by simp
  have "length (bp_buckets ?P') \<le> length (bp_buckets P) + 2"
    using len_new unfolding bp_delete_key_def by simp
  show ?thesis
    unfolding state by (rule \<open>length (bp_buckets ?P') \<le>
      length (bp_buckets P) + 2\<close>)
qed

lemma bp_local_insert_state_invariant:
  assumes ord: "bp_ordered_invariant P"
  shows "bp_invariant (bp_local_insert_state x b P)"
proof -
  let ?old_keys = "bp_entry_keys (bp_entries P)"
  let ?b = "if x \<in> ?old_keys then min (bp_values P x) b else b"
  let ?P0 = "bp_delete_key x P"
  let ?M = "bp_block_size ?P0"
  let ?bs = "bp_buckets ?P0"
  let ?new_bs = "bp_local_insert_bucket ?M (x, ?b) ?bs"
  let ?P' = "?P0\<lparr>bp_buckets := ?new_bs,
      bp_values := (bp_values P)(x := ?b)\<rparr>"
  have inv: "bp_invariant P"
    by (rule bp_ordered_invariant_invariant[OF ord])
  have inv0: "bp_invariant ?P0"
    by (rule bp_delete_key_invariant[OF inv])
  have boundaries0_state: "bp_bucket_boundaries_state_ok ?P0"
    by (rule bp_delete_key_boundaries_state_ok
        [OF bp_ordered_invariant_boundaries_state_ok[OF ord]])
  have M_pos: "0 < ?M"
    using inv0 unfolding bp_invariant_def by blast
  have distinct0: "distinct (map fst (bp_entries ?P0))"
    using inv0 unfolding bp_invariant_def bp_distinct_keys_def by blast
  have sizes0:
    "\<forall>c\<in>set ?bs. length (bp_bucket_entries c) \<le> ?M"
    using inv0 unfolding bp_invariant_def bp_bucket_sizes_ok_def by blast
  have sorted0:
    "sorted_wrt (\<lambda>c d. bp_marker c \<le> bp_marker d) ?bs"
    using inv0 unfolding bp_invariant_def bp_bucket_markers_sorted_def by blast
  have markers0:
    "\<forall>c\<in>set ?bs. \<forall>p\<in>set (bp_bucket_entries c).
      bp_marker c \<le> snd p"
    using inv0 unfolding bp_invariant_def bp_bucket_markers_lower_bound_def
    by blast
  have boundaries0: "bp_bucket_boundaries_ok ?bs"
    using boundaries0_state unfolding bp_bucket_boundaries_state_ok_def .
  have shape:
    "(\<forall>c\<in>set ?new_bs. length (bp_bucket_entries c) \<le> ?M) \<and>
     sorted_wrt (\<lambda>c d. bp_marker c \<le> bp_marker d) ?new_bs \<and>
     (\<forall>c\<in>set ?new_bs. \<forall>q\<in>set (bp_bucket_entries c).
        bp_marker c \<le> snd q) \<and>
     bp_bucket_boundaries_ok ?new_bs"
    by (rule bp_local_insert_bucket_preserves_bucket_shape
        [OF M_pos sizes0 sorted0 markers0 boundaries0])
  have fresh: "x \<notin> bp_entry_keys (bp_entries ?P0)"
    by simp
  have distinct_local:
    "distinct (map fst (bp_bucket_entries_flat ?new_bs))"
    by (rule bp_local_insert_bucket_distinct_keys[OF M_pos])
      (use distinct0 fresh in \<open>simp_all add: bp_entries_def\<close>)
  have values0:
    "\<forall>p\<in>set (bp_entries ?P0). bp_values ?P0 (fst p) = snd p"
    using inv0 unfolding bp_invariant_def bp_values_consistent_def by blast
  have values0_P:
    "\<forall>p\<in>set (bp_entries ?P0). bp_values P (fst p) = snd p"
    using values0 unfolding bp_delete_key_def by simp
  have values_insert:
    "\<forall>p\<in>set (bp_bucket_entries_flat ?new_bs).
      ((bp_values P)(x := ?b)) (fst p) = snd p"
  proof
    fix p
    assume p: "p \<in> set (bp_bucket_entries_flat ?new_bs)"
    then have p_cases:
      "p = (x, ?b) \<or> p \<in> set (bp_bucket_entries_flat ?bs)"
      using set_bp_bucket_entries_flat_local_insert_bucket
        [OF M_pos, of "(x, ?b)" ?bs]
      by auto
    from p_cases show "((bp_values P)(x := ?b)) (fst p) = snd p"
    proof
      assume "p = (x, ?b)"
      then show ?thesis by simp
    next
      assume p_old: "p \<in> set (bp_bucket_entries_flat ?bs)"
      then have p_old_entry: "p \<in> set (bp_entries ?P0)"
        unfolding bp_entries_def .
      have "fst p \<noteq> x"
      proof
        assume "fst p = x"
        then have "x \<in> bp_entry_keys (bp_entries ?P0)"
          using p_old_entry unfolding bp_entry_keys_def by auto
        then show False
          using fresh by simp
      qed
      moreover have "bp_values P (fst p) = snd p"
        using values0_P p_old_entry by blast
      ultimately show ?thesis
        by simp
    qed
  qed
  show ?thesis
    unfolding bp_local_insert_state_def Let_def bp_invariant_def
  proof (intro conjI)
    show "0 < bp_block_size ?P'"
      using M_pos by simp
    show "bp_distinct_keys ?P'"
      using distinct_local unfolding bp_distinct_keys_def bp_entries_def
      by simp
    show "bp_bucket_sizes_ok ?P'"
      using shape unfolding bp_bucket_sizes_ok_def by simp
    show "bp_bucket_markers_sorted ?P'"
      using shape unfolding bp_bucket_markers_sorted_def by simp
    show "bp_bucket_markers_lower_bound ?P'"
      using shape unfolding bp_bucket_markers_lower_bound_def by simp
    show "bp_values_consistent ?P'"
      using values_insert unfolding bp_values_consistent_def bp_entries_def
      by simp
  qed
qed

lemma bp_local_insert_state_boundaries_state_ok:
  assumes ord: "bp_ordered_invariant P"
  shows "bp_bucket_boundaries_state_ok (bp_local_insert_state x b P)"
proof -
  let ?old_keys = "bp_entry_keys (bp_entries P)"
  let ?b = "if x \<in> ?old_keys then min (bp_values P x) b else b"
  let ?P0 = "bp_delete_key x P"
  let ?M = "bp_block_size ?P0"
  let ?bs = "bp_buckets ?P0"
  let ?new_bs = "bp_local_insert_bucket ?M (x, ?b) ?bs"
  have inv: "bp_invariant P"
    by (rule bp_ordered_invariant_invariant[OF ord])
  have inv0: "bp_invariant ?P0"
    by (rule bp_delete_key_invariant[OF inv])
  have boundaries0_state: "bp_bucket_boundaries_state_ok ?P0"
    by (rule bp_delete_key_boundaries_state_ok
        [OF bp_ordered_invariant_boundaries_state_ok[OF ord]])
  have M_pos: "0 < ?M"
    using inv0 unfolding bp_invariant_def by blast
  have sizes0:
    "\<forall>c\<in>set ?bs. length (bp_bucket_entries c) \<le> ?M"
    using inv0 unfolding bp_invariant_def bp_bucket_sizes_ok_def by blast
  have sorted0:
    "sorted_wrt (\<lambda>c d. bp_marker c \<le> bp_marker d) ?bs"
    using inv0 unfolding bp_invariant_def bp_bucket_markers_sorted_def by blast
  have markers0:
    "\<forall>c\<in>set ?bs. \<forall>p\<in>set (bp_bucket_entries c).
      bp_marker c \<le> snd p"
    using inv0 unfolding bp_invariant_def bp_bucket_markers_lower_bound_def
    by blast
  have boundaries0: "bp_bucket_boundaries_ok ?bs"
    using boundaries0_state unfolding bp_bucket_boundaries_state_ok_def .
  have shape:
    "(\<forall>c\<in>set ?new_bs. length (bp_bucket_entries c) \<le> ?M) \<and>
     sorted_wrt (\<lambda>c d. bp_marker c \<le> bp_marker d) ?new_bs \<and>
     (\<forall>c\<in>set ?new_bs. \<forall>q\<in>set (bp_bucket_entries c).
        bp_marker c \<le> snd q) \<and>
     bp_bucket_boundaries_ok ?new_bs"
    by (rule bp_local_insert_bucket_preserves_bucket_shape
        [OF M_pos sizes0 sorted0 markers0 boundaries0])
  show ?thesis
    unfolding bp_local_insert_state_def Let_def
      bp_bucket_boundaries_state_ok_def
    using shape by simp
qed

lemma bp_local_insert_state_ordered_invariant:
  assumes ord: "bp_ordered_invariant P"
  shows "bp_ordered_invariant (bp_local_insert_state x b P)"
  unfolding bp_ordered_invariant_def
  using bp_local_insert_state_invariant[OF ord]
    bp_local_insert_state_boundaries_state_ok[OF ord]
  by blast

lemma bp_batch_prepend_invariant:
  assumes "bp_invariant P"
  shows "bp_invariant (bp_batch_prepend xs P)"
  using assms
proof (induction xs arbitrary: P)
  case Nil
  then show ?case
    unfolding bp_batch_prepend_def by simp
next
  case (Cons xb xs)
  obtain x b where xb: "xb = (x, b)"
    by force
  have step: "bp_invariant (bp_insert x b P)"
    by (rule bp_insert_invariant[OF Cons.prems])
  have unfold_step:
    "bp_batch_prepend (xb # xs) P =
      bp_batch_prepend xs (bp_insert x b P)"
    unfolding bp_batch_prepend_def xb by simp
  show ?case
    unfolding unfold_step by (rule Cons.IH[OF step])
qed

theorem bp_batch_prepend_refines_batch_min_update:
  assumes "bp_invariant P"
  shows "bp_view (bp_batch_prepend xs P) =
    batch_min_update (bp_view P) xs"
  using assms
proof (induction xs arbitrary: P)
  case Nil
  then show ?case
    unfolding bp_batch_prepend_def batch_min_update_def by simp
next
  case (Cons xb xs)
  obtain x b where xb: "xb = (x, b)"
    by force
  have step_inv: "bp_invariant (bp_insert x b P)"
    by (rule bp_insert_invariant[OF Cons.prems])
  have step_view: "bp_view (bp_insert x b P) = min_update (bp_view P) x b"
    by (rule bp_insert_refines_min_update)
  have unfold_state:
    "bp_batch_prepend (xb # xs) P =
      bp_batch_prepend xs (bp_insert x b P)"
    unfolding bp_batch_prepend_def xb by simp
  have unfold_view:
    "batch_min_update (bp_view P) (xb # xs) =
      batch_min_update (min_update (bp_view P) x b) xs"
    unfolding batch_min_update_def xb by simp
  show ?case
    unfolding unfold_state unfold_view
    using Cons.IH[OF step_inv] step_view by simp
qed

theorem bp_batch_prepend_preserves_upper_bound:
  assumes inv: "bp_invariant P"
    and upper: "partition_upper_bound (bp_view P) B"
    and values_lt: "\<And>x b. (x, b) \<in> set xs \<Longrightarrow> b < B"
  shows "partition_upper_bound (bp_view (bp_batch_prepend xs P)) B"
  unfolding bp_batch_prepend_refines_batch_min_update[OF inv]
  by (rule batch_min_update_preserves_upper_bound[OF upper values_lt])

definition bp_rebucketed_insert ::
  "'k \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow> 'k bucketed_partition" where
  "bp_rebucketed_insert x b P = bp_rebucket (bp_insert x b P)"

definition bp_rebucketed_batch_prepend ::
  "('k \<times> real) list \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k bucketed_partition" where
  "bp_rebucketed_batch_prepend xs P = bp_rebucket (bp_batch_prepend xs P)"

lemma bp_rebucketed_insert_invariant:
  assumes inv: "bp_invariant P"
  shows "bp_invariant (bp_rebucketed_insert x b P)"
  unfolding bp_rebucketed_insert_def
  by (rule bp_rebucket_invariant[OF bp_insert_invariant[OF inv]])

lemma bp_rebucketed_insert_ordered_invariant:
  assumes inv: "bp_invariant P"
  shows "bp_ordered_invariant (bp_rebucketed_insert x b P)"
  unfolding bp_rebucketed_insert_def
  by (rule bp_rebucket_ordered_invariant[OF bp_insert_invariant[OF inv]])

theorem bp_rebucketed_insert_refines_min_update:
  assumes inv: "bp_invariant P"
  shows "bp_view (bp_rebucketed_insert x b P) = min_update (bp_view P) x b"
proof -
  have step_inv: "bp_invariant (bp_insert x b P)"
    by (rule bp_insert_invariant[OF inv])
  then have block: "0 < bp_block_size (bp_insert x b P)"
    unfolding bp_invariant_def by blast
  have rebucket_view:
    "bp_view (bp_rebucket (bp_insert x b P)) = bp_view (bp_insert x b P)"
    by (rule bp_rebucket_view[OF block])
  show ?thesis
    unfolding bp_rebucketed_insert_def
    using rebucket_view bp_insert_refines_min_update by simp
qed

theorem bp_rebucketed_insert_refines_insert_spec:
  assumes inv: "bp_invariant P"
  shows "insert_spec (bp_view P) x b (bp_view (bp_rebucketed_insert x b P))"
  unfolding bp_rebucketed_insert_refines_min_update[OF inv]
  by (rule min_update_insert_spec)

theorem bp_rebucketed_insert_preserves_upper_bound:
  assumes inv: "bp_invariant P"
    and upper: "partition_upper_bound (bp_view P) B"
    and b_lt: "b < B"
  shows "partition_upper_bound (bp_view (bp_rebucketed_insert x b P)) B"
  unfolding bp_rebucketed_insert_refines_min_update[OF inv]
  by (rule min_update_preserves_upper_bound[OF upper b_lt])

lemma bp_rebucketed_batch_prepend_invariant:
  assumes inv: "bp_invariant P"
  shows "bp_invariant (bp_rebucketed_batch_prepend xs P)"
  unfolding bp_rebucketed_batch_prepend_def
  by (rule bp_rebucket_invariant[OF bp_batch_prepend_invariant[OF inv]])

lemma bp_rebucketed_batch_prepend_ordered_invariant:
  assumes inv: "bp_invariant P"
  shows "bp_ordered_invariant (bp_rebucketed_batch_prepend xs P)"
  unfolding bp_rebucketed_batch_prepend_def
  by (rule bp_rebucket_ordered_invariant[OF bp_batch_prepend_invariant[OF inv]])

theorem bp_rebucketed_batch_prepend_refines_batch_min_update:
  assumes inv: "bp_invariant P"
  shows "bp_view (bp_rebucketed_batch_prepend xs P) =
    batch_min_update (bp_view P) xs"
proof -
  have step_inv: "bp_invariant (bp_batch_prepend xs P)"
    by (rule bp_batch_prepend_invariant[OF inv])
  then have block: "0 < bp_block_size (bp_batch_prepend xs P)"
    unfolding bp_invariant_def by blast
  have rebucket_view:
    "bp_view (bp_rebucket (bp_batch_prepend xs P)) =
      bp_view (bp_batch_prepend xs P)"
    by (rule bp_rebucket_view[OF block])
  show ?thesis
    unfolding bp_rebucketed_batch_prepend_def
    using rebucket_view bp_batch_prepend_refines_batch_min_update[OF inv]
    by simp
qed

theorem bp_rebucketed_batch_prepend_preserves_upper_bound:
  assumes inv: "bp_invariant P"
    and upper: "partition_upper_bound (bp_view P) B"
    and values_lt: "\<And>x b. (x, b) \<in> set xs \<Longrightarrow> b < B"
  shows "partition_upper_bound
    (bp_view (bp_rebucketed_batch_prepend xs P)) B"
  unfolding bp_rebucketed_batch_prepend_refines_batch_min_update[OF inv]
  by (rule batch_min_update_preserves_upper_bound[OF upper values_lt])

lemma bp_min_value_le_entry:
  assumes "(x, b) \<in> set xs"
  shows "bp_min_value B xs \<le> b"
  using assms by (induction xs) auto

lemma bp_entries_Cons:
  assumes "bp_buckets P = b # bs"
  shows "bp_entries P = bp_bucket_entries b @ bp_bucket_entries_flat bs"
  using assms unfolding bp_entries_def bp_bucket_entries_flat_def by simp

lemma bp_tail_entry_ge_head_marker:
  assumes sorted: "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) (c # bs)"
    and lower: "\<And>d p. \<lbrakk>d \<in> set (c # bs); p \<in> set (bp_bucket_entries d)\<rbrakk>
      \<Longrightarrow> bp_marker d \<le> snd p"
    and p: "p \<in> set (bp_bucket_entries_flat (c # bs))"
  shows "bp_marker c \<le> snd p"
proof -
  obtain d where d: "d \<in> set (c # bs)"
    and p_d: "p \<in> set (bp_bucket_entries d)"
    using p unfolding bp_bucket_entries_flat_def by auto
  have c_le_d: "bp_marker c \<le> bp_marker d"
    using sorted d by (cases "d = c") auto
  have d_le_p: "bp_marker d \<le> snd p"
    by (rule lower[OF d p_d])
  show ?thesis
    using c_le_d d_le_p by linarith
qed

lemma bp_first_bucket_pull_invariant:
  assumes inv: "bp_invariant P"
    and pull: "bp_first_bucket_pull M B P = (S, beta, P')"
  shows "bp_invariant P'"
proof (cases "bp_buckets P")
  case Nil
  then have "P' = P"
    using pull unfolding bp_first_bucket_pull_def by simp
  then show ?thesis
    using inv by simp
next
  case (Cons b rest)
  then have buckets_outer: "bp_buckets P = b # rest" .
  then show ?thesis
  proof (cases rest)
    case Nil
    then have "P' = P"
      using buckets_outer pull unfolding bp_first_bucket_pull_def by simp
    then show ?thesis
      using inv by simp
  next
    case (Cons c bs)
    let ?S = "bp_bucket_keys b"
    have pull_eval:
      "bp_first_bucket_pull M B P = (?S, bp_marker c, bp_delete_keys ?S P)"
      using buckets_outer Cons
      unfolding bp_first_bucket_pull_def by (simp add: Let_def)
    have tuple_eq: "(?S, bp_marker c, bp_delete_keys ?S P) = (S, beta, P')"
      using pull_eval pull by simp
    have S_eq: "S = ?S"
      using tuple_eq by simp
    have P'_eq_raw: "bp_delete_keys ?S P = P'"
      using tuple_eq by (metis prod.inject)
    then have "P' = bp_delete_keys ?S P"
      by simp
    then have "P' = bp_delete_keys S P"
      using S_eq by simp
    then show ?thesis
      by (simp add: bp_delete_keys_invariant[OF inv])
  qed
qed

theorem bp_first_bucket_pull_refines_pull_separates:
  assumes inv: "bp_invariant P"
    and buckets: "bp_buckets P = b # c # bs"
    and len_b: "length (bp_bucket_entries b) \<le> M"
    and below: "bp_bucket_below_bound b (bp_marker c)"
    and tail_nonempty: "bp_bucket_entries_flat (c # bs) \<noteq> []"
    and pull: "bp_first_bucket_pull M B P = (S, beta, P')"
  shows "pull_separates (bp_view P) M B S beta (bp_view P')"
proof -
  let ?tail = "bp_bucket_entries_flat (c # bs)"
  have S_def: "S = bp_bucket_keys b"
    and beta_def: "beta = bp_marker c"
    and P'_def: "P' = bp_delete_keys S P"
    using pull buckets unfolding bp_first_bucket_pull_def by (auto simp: Let_def)
  have entries_P: "bp_entries P = bp_bucket_entries b @ ?tail"
    using buckets by (simp add: bp_entries_Cons)
  have distinct_P: "distinct (map fst (bp_entries P))"
    using inv unfolding bp_invariant_def bp_distinct_keys_def by blast
  have values_P:
    "\<And>p. p \<in> set (bp_entries P) \<Longrightarrow> bp_values P (fst p) = snd p"
    using inv unfolding bp_invariant_def bp_values_consistent_def by blast
  have sorted_tail:
    "sorted_wrt (\<lambda>x y. bp_marker x \<le> bp_marker y) (c # bs)"
    using inv buckets unfolding bp_invariant_def bp_bucket_markers_sorted_def by simp
  have lower_tail:
    "\<And>d p. \<lbrakk>d \<in> set (c # bs); p \<in> set (bp_bucket_entries d)\<rbrakk>
      \<Longrightarrow> bp_marker d \<le> snd p"
    using inv buckets unfolding bp_invariant_def
      bp_bucket_markers_lower_bound_def by auto
  have S_subset: "S \<subseteq> keys_of (bp_view P)"
    unfolding S_def bp_view_def bp_bucket_keys_def bp_entry_keys_def entries_P
    by auto
  have card_S: "card S \<le> M"
  proof -
    have "card S \<le> length (bp_bucket_entries b)"
    proof -
      have "card S = card (fst ` set (bp_bucket_entries b))"
        unfolding S_def bp_bucket_keys_def bp_entry_keys_def by simp
      also have "\<dots> \<le> card (set (bp_bucket_entries b))"
        by (rule card_image_le) simp
      also have "\<dots> \<le> length (bp_bucket_entries b)"
        by (rule card_length)
      finally show ?thesis .
    qed
    then show ?thesis
      using len_b by linarith
  qed
  have P'_keys: "keys_of (bp_view P') = keys_of (bp_view P) - S"
    unfolding P'_def bp_delete_keys_view by simp
  have P'_values: "value_of (bp_view P') = value_of (bp_view P)"
    unfolding P'_def bp_delete_keys_view by simp
  have pulled_lt_beta:
    "\<And>u. u \<in> S \<Longrightarrow> value_of (bp_view P) u < beta"
  proof -
    fix u
    assume u: "u \<in> S"
    then obtain p where p_b: "p \<in> set (bp_bucket_entries b)"
      and fst_p: "fst p = u"
      unfolding S_def bp_bucket_keys_def bp_entry_keys_def by auto
    have "snd p < beta"
      using below p_b unfolding bp_bucket_below_bound_def beta_def by blast
    moreover have "bp_values P u = snd p"
      using values_P[of p] p_b fst_p entries_P by simp
    ultimately show "value_of (bp_view P) u < beta"
      unfolding bp_view_def by simp
  qed
  have tail_key_notin_S:
    "\<And>p. p \<in> set ?tail \<Longrightarrow> fst p \<notin> S"
  proof -
    fix p
    assume p_tail: "p \<in> set ?tail"
    show "fst p \<notin> S"
    proof
      assume "fst p \<in> S"
      then obtain q where q_b: "q \<in> set (bp_bucket_entries b)"
        and fst_q: "fst q = fst p"
        unfolding S_def bp_bucket_keys_def bp_entry_keys_def by auto
      have distinct_append: "distinct (map fst (bp_bucket_entries b @ ?tail))"
        using distinct_P unfolding entries_P .
      have disjoint:
        "set (map fst (bp_bucket_entries b)) \<inter> set (map fst ?tail) = {}"
        using distinct_append by simp
      have "fst p \<in> set (map fst ?tail)"
        using p_tail by force
      then have "fst p \<notin> set (map fst (bp_bucket_entries b))"
        using disjoint by blast
      moreover have "fst p \<in> set (map fst (bp_bucket_entries b))"
      proof -
        have "fst q \<in> set (map fst (bp_bucket_entries b))"
          using q_b by force
        then show ?thesis
          using fst_q by simp
      qed
      ultimately show False
        by blast
    qed
  qed
  have tail_key_remaining:
    "\<And>p. p \<in> set ?tail \<Longrightarrow> fst p \<in> keys_of (bp_view P')"
  proof -
    fix p
    assume p_tail: "p \<in> set ?tail"
    have old: "fst p \<in> keys_of (bp_view P)"
      unfolding bp_view_def bp_entry_keys_def entries_P using p_tail by auto
    have not_S: "fst p \<notin> S"
      by (rule tail_key_notin_S[OF p_tail])
    show "fst p \<in> keys_of (bp_view P')"
      using old not_S unfolding P'_keys by blast
  qed
  have remaining_nonempty: "keys_of (bp_view P') \<noteq> {}"
  proof -
    obtain p where p_tail: "p \<in> set ?tail"
      using tail_nonempty by (cases ?tail) auto
    then have "fst p \<in> keys_of (bp_view P')"
      by (rule tail_key_remaining)
    then show ?thesis by blast
  qed
  have lower_remaining:
    "\<And>v. v \<in> keys_of (bp_view P') \<Longrightarrow> beta \<le> value_of (bp_view P') v"
  proof -
    fix v
    assume v: "v \<in> keys_of (bp_view P')"
    then have v_old: "v \<in> keys_of (bp_view P)"
      using P'_keys by blast
    then obtain p where p_entries: "p \<in> set (bp_entries P)"
      and fst_p: "fst p = v"
      unfolding bp_view_def bp_entry_keys_def by auto
    have v_not_S: "v \<notin> S"
      using v P'_keys by blast
    have p_tail: "p \<in> set ?tail"
    proof -
      have "p \<notin> set (bp_bucket_entries b)"
        using v_not_S fst_p unfolding S_def bp_bucket_keys_def bp_entry_keys_def
        by auto
      then show ?thesis
        using p_entries unfolding entries_P by auto
    qed
    have "beta \<le> snd p"
      unfolding beta_def
      by (rule bp_tail_entry_ge_head_marker[OF sorted_tail lower_tail p_tail])
    moreover have "value_of (bp_view P') v = snd p"
    proof -
      have "value_of (bp_view P) v = snd p"
        using values_P[OF p_entries] fst_p unfolding bp_view_def by simp
      moreover have "value_of (bp_view P') v = value_of (bp_view P) v"
        using P'_values by simp
      ultimately show ?thesis by simp
    qed
    ultimately show "beta \<le> value_of (bp_view P') v"
      by simp
  qed
  have pulled_before_remaining:
    "\<And>u v. \<lbrakk>u \<in> S; v \<in> keys_of (bp_view P')\<rbrakk>
      \<Longrightarrow> value_of (bp_view P) u \<le> value_of (bp_view P') v"
  proof -
    fix u v
    assume u: "u \<in> S" and v: "v \<in> keys_of (bp_view P')"
    have "value_of (bp_view P) u < beta"
      by (rule pulled_lt_beta[OF u])
    moreover have "beta \<le> value_of (bp_view P') v"
      by (rule lower_remaining[OF v])
    ultimately show "value_of (bp_view P) u \<le> value_of (bp_view P') v"
      by simp
  qed
  show ?thesis
    unfolding pull_separates_def
    using S_subset card_S P'_keys P'_values remaining_nonempty
      pulled_before_remaining pulled_lt_beta lower_remaining
    by auto
qed

lemma bp_conservative_pull_invariant:
  assumes inv: "bp_invariant P"
    and pull: "bp_conservative_pull M B P = (S, beta, P')"
  shows "bp_invariant P'"
proof -
  have "P' = bp_delete_keys S P"
    using pull unfolding bp_conservative_pull_def by (auto simp: Let_def)
  then show ?thesis
    by (simp add: bp_delete_keys_invariant[OF inv])
qed

theorem bp_conservative_pull_refines_pull_separates:
  assumes inv: "bp_invariant P"
    and upper: "\<And>u. u \<in> keys_of (bp_view P) \<Longrightarrow>
      value_of (bp_view P) u < B"
    and pull: "bp_conservative_pull M B P = (S, beta, P')"
  shows "pull_separates (bp_view P) M B S beta (bp_view P')"
proof -
  have S_def: "S = bp_pull_set M P"
    and beta_def: "beta = bp_pull_bound M B P"
    and P'_def: "P' = bp_delete_keys S P"
    using pull unfolding bp_conservative_pull_def by (auto simp: Let_def)
  show ?thesis
  proof (cases "length (bp_entries P) \<le> M")
    case True
    have S_keys: "S = keys_of (bp_view P)"
      using True unfolding S_def bp_pull_set_def bp_view_def by simp
    have beta_B: "beta = B"
      using True unfolding beta_def bp_pull_bound_def by simp
    have keys_empty: "keys_of (bp_view P') = {}"
      unfolding P'_def bp_delete_keys_view S_keys by simp
    have card_S: "card S \<le> M"
    proof -
      have "card S = card (fst ` set (bp_entries P))"
        unfolding S_keys bp_view_def bp_entry_keys_def by simp
      also have "\<dots> \<le> card (set (bp_entries P))"
        by (rule card_image_le) simp
      also have "\<dots> \<le> length (bp_entries P)"
        by (rule card_length)
      also have "\<dots> \<le> M"
        by (rule True)
      finally show ?thesis .
    qed
    show ?thesis
      unfolding pull_separates_def P'_def bp_delete_keys_view
      using S_keys beta_B keys_empty card_S by auto
  next
    case False
    have S_empty: "S = {}"
      using False unfolding S_def bp_pull_set_def by simp
    have beta_min: "beta = bp_min_value B (bp_entries P)"
      using False unfolding beta_def bp_pull_bound_def by simp
    have P'_same: "P' = P"
      unfolding P'_def S_empty bp_delete_keys_def bp_delete_keys_from_bucket_def
      by simp
    have keys_nonempty: "keys_of (bp_view P') \<noteq> {}"
    proof
      assume empty: "keys_of (bp_view P') = {}"
      then have "set (bp_entries P) = {}"
        unfolding P'_same bp_view_def bp_entry_keys_def by auto
      then have "length (bp_entries P) = 0"
        by simp
      then show False
        using False by simp
    qed
    have lower:
      "\<And>v. v \<in> keys_of (bp_view P') \<Longrightarrow> beta \<le> value_of (bp_view P') v"
    proof -
      fix v
      assume v: "v \<in> keys_of (bp_view P')"
      then obtain b where vb: "(v, b) \<in> set (bp_entries P)"
        unfolding P'_same bp_view_def bp_entry_keys_def by auto
      have "bp_min_value B (bp_entries P) \<le> b"
        by (rule bp_min_value_le_entry[OF vb])
      moreover have "bp_values P v = b"
        using inv vb by (auto simp: bp_invariant_def bp_values_consistent_def)
      ultimately show "beta \<le> value_of (bp_view P') v"
        unfolding beta_min P'_same bp_view_def by simp
    qed
    have keys_nonempty_P: "keys_of (bp_view P) \<noteq> {}"
      using keys_nonempty unfolding P'_same .
    have lower_P:
      "\<And>v. v \<in> keys_of (bp_view P) \<Longrightarrow> beta \<le> value_of (bp_view P) v"
      using lower unfolding P'_same .
    show ?thesis
      unfolding pull_separates_def P'_same S_empty
      using lower_P keys_nonempty_P by auto
  qed
qed

lemma bp_pull_invariant:
  assumes inv: "bp_invariant P"
    and pull: "bp_pull M B P = (S, beta, P')"
  shows "bp_invariant P'"
proof (cases "bp_can_first_bucket_pull M P")
  case True
  have first_pull: "bp_first_bucket_pull M B P = (S, beta, P')"
    using pull True unfolding bp_pull_def by simp
  show ?thesis
    by (rule bp_first_bucket_pull_invariant[OF inv first_pull])
next
  case False
  have conservative_pull: "bp_conservative_pull M B P = (S, beta, P')"
    using pull False unfolding bp_pull_def by simp
  show ?thesis
    by (rule bp_conservative_pull_invariant[OF inv conservative_pull])
qed

lemma bp_first_bucket_pull_ordered_invariant:
  assumes ord: "bp_ordered_invariant P"
    and pull: "bp_first_bucket_pull M B P = (S, beta, P')"
  shows "bp_ordered_invariant P'"
proof -
  have cases: "P' = P \<or> (\<exists>T. P' = bp_delete_keys T P)"
    using pull unfolding bp_first_bucket_pull_def
    by (cases "bp_buckets P"; auto split: list.splits)
  then show ?thesis
  proof
    assume "P' = P"
    then show ?thesis
      using ord by simp
  next
    assume "\<exists>T. P' = bp_delete_keys T P"
    then obtain T where "P' = bp_delete_keys T P"
      by blast
    then show ?thesis
      using bp_delete_keys_ordered_invariant[OF ord] by simp
  qed
qed

lemma bp_conservative_pull_ordered_invariant:
  assumes ord: "bp_ordered_invariant P"
    and pull: "bp_conservative_pull M B P = (S, beta, P')"
  shows "bp_ordered_invariant P'"
proof -
  have "P' = bp_delete_keys S P"
    using pull unfolding bp_conservative_pull_def by (auto simp: Let_def)
  then show ?thesis
    using bp_delete_keys_ordered_invariant[OF ord] by simp
qed

lemma bp_pull_ordered_invariant:
  assumes ord: "bp_ordered_invariant P"
    and pull: "bp_pull M B P = (S, beta, P')"
  shows "bp_ordered_invariant P'"
proof (cases "bp_can_first_bucket_pull M P")
  case True
  have first_pull: "bp_first_bucket_pull M B P = (S, beta, P')"
    using pull True unfolding bp_pull_def by simp
  show ?thesis
    by (rule bp_first_bucket_pull_ordered_invariant[OF ord first_pull])
next
  case False
  have conservative_pull: "bp_conservative_pull M B P = (S, beta, P')"
    using pull False unfolding bp_pull_def by simp
  show ?thesis
    by (rule bp_conservative_pull_ordered_invariant
        [OF ord conservative_pull])
qed

theorem bp_pull_refines_pull_separates:
  assumes inv: "bp_invariant P"
    and upper: "\<And>u. u \<in> keys_of (bp_view P) \<Longrightarrow>
      value_of (bp_view P) u < B"
    and pull: "bp_pull M B P = (S, beta, P')"
  shows "pull_separates (bp_view P) M B S beta (bp_view P')"
proof (cases "bp_can_first_bucket_pull M P")
  case True
  obtain b c bs where buckets: "bp_buckets P = b # c # bs"
    and len_b: "length (bp_bucket_entries b) \<le> M"
    and below: "bp_bucket_below_bound b (bp_marker c)"
    and tail_nonempty: "bp_bucket_entries_flat (c # bs) \<noteq> []"
    by (rule bp_can_first_bucket_pullE[OF True])
  have first_pull: "bp_first_bucket_pull M B P = (S, beta, P')"
    using pull True unfolding bp_pull_def by simp
  show ?thesis
    by (rule bp_first_bucket_pull_refines_pull_separates
        [OF inv buckets len_b below tail_nonempty first_pull])
next
  case False
  have conservative_pull: "bp_conservative_pull M B P = (S, beta, P')"
    using pull False unfolding bp_pull_def by simp
  show ?thesis
    by (rule bp_conservative_pull_refines_pull_separates
        [OF inv upper conservative_pull])
qed

theorem bp_pull_preserves_upper_bound:
  assumes inv: "bp_invariant P"
    and pull_upper: "partition_upper_bound (bp_view P) Bpull"
    and upper: "partition_upper_bound (bp_view P) B"
    and pull: "bp_pull M Bpull P = (S, beta, P')"
  shows "partition_upper_bound (bp_view P') B"
proof -
  have sep: "pull_separates (bp_view P) M Bpull S beta (bp_view P')"
  proof (rule bp_pull_refines_pull_separates[OF inv _ pull])
    fix u
    assume "u \<in> keys_of (bp_view P)"
    then show "value_of (bp_view P) u < Bpull"
      using pull_upper unfolding partition_upper_bound_def by blast
  qed
  show ?thesis
    by (rule pull_separates_preserves_upper_bound[OF sep upper])
qed

text \<open>
  The preceding block completes the functional refinement layer.  Insert and
  BatchPrepend update the view by minimum-value update, while Pull satisfies
  @{const pull_separates}: it returns at most the requested block, removes those
  keys, and establishes the returned boundary between pulled and remaining
  entries.  The implementation attempts a cheap first-bucket pull when the
  ordered boundary proves it is safe; otherwise it uses the
  conservative pull specification.  Both branches preserve @{const bp_invariant}
  and the abstract upper-bound condition.
\<close>


section \<open>Cost Budgets for the Bucketed Structure\<close>

text \<open>
  The cost layer counts primitive functional steps by pairing each operation
  result with a natural number.  The budget definitions isolate the
  paper-critical logarithmic search term as a function of \<open>N / M\<close>, where
  \<open>N\<close> is represented by an entry-list length and \<open>M\<close> by the block size.
  The potential terms record the credits that pay for lazy bucket splitting and
  for restoring the bucket-count ratio after a rebuild.
\<close>

definition bp_steps_of :: "'a \<times> nat \<Rightarrow> nat" where
  "bp_steps_of r = snd r"

definition bp_result_of :: "'a \<times> nat \<Rightarrow> 'a" where
  "bp_result_of r = fst r"

lemma bp_steps_of_pair [simp]:
  "bp_steps_of (x, c) = c"
  unfolding bp_steps_of_def by simp

lemma bp_result_of_pair [simp]:
  "bp_result_of (x, c) = x"
  unfolding bp_result_of_def by simp

lemma bp_result_of_add_cost_case [simp]:
  "bp_result_of (case r of (x, c') \<Rightarrow> (x, c + c')) = bp_result_of r"
  by (cases r) simp

lemma bp_steps_of_add_cost_case [simp]:
  "bp_steps_of (case r of (x, c') \<Rightarrow> (x, c + c')) =
    c + bp_steps_of r"
  by (cases r) simp

definition bp_ratio_log_budget :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bp_ratio_log_budget N M = Suc (floor_log (Suc (N div M)))"

definition bp_insert_search_budget :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bp_insert_search_budget N M = Suc (bp_ratio_log_budget N M)"

definition bp_lazy_insert_amortized_budget ::
  "'k bucketed_partition \<Rightarrow> nat" where
  "bp_lazy_insert_amortized_budget P =
     bp_insert_search_budget (length (bp_entries P)) (bp_block_size P) + 7"

definition bp_batch_prepend_log_budget :: "('k \<times> real) list \<Rightarrow> nat \<Rightarrow> nat" where
  "bp_batch_prepend_log_budget xs M =
     length xs * bp_ratio_log_budget (length xs) M"

definition bp_batch_prepend_per_item_budget ::
  "('k \<times> real) list \<Rightarrow> nat \<Rightarrow> nat" where
  "bp_batch_prepend_per_item_budget xs M =
     Suc (bp_ratio_log_budget (length xs) M)"

definition bp_batch_prepend_amortized_budget ::
  "('k \<times> real) list \<Rightarrow> nat \<Rightarrow> nat" where
  "bp_batch_prepend_amortized_budget xs M =
     length xs + bp_batch_prepend_log_budget xs M"

definition bp_pull_amortized_budget :: "nat \<Rightarrow> nat" where
  "bp_pull_amortized_budget M = 2 * M"

definition bp_local_split_budget :: "nat \<Rightarrow> nat" where
  "bp_local_split_budget M = Suc (2 * Suc M)"

definition bp_lazy_split_budget :: "nat \<Rightarrow> nat" where
  "bp_lazy_split_budget M = 5 + 4 * M"

definition bp_bucket_overflow :: "nat \<Rightarrow> 'k bp_bucket \<Rightarrow> nat" where
  "bp_bucket_overflow M b = length (bp_bucket_entries b) - M"

definition bp_bucket_overflow_sum ::
  "nat \<Rightarrow> 'k bp_bucket list \<Rightarrow> nat" where
  "bp_bucket_overflow_sum M bs =
     sum_list (map (bp_bucket_overflow M) bs)"

definition bp_overflow_potential :: "'k bucketed_partition \<Rightarrow> nat" where
  "bp_overflow_potential P =
     sum_list (map (bp_bucket_overflow (bp_block_size P)) (bp_buckets P))"

definition bp_bucket_count_slack :: "'k bucketed_partition \<Rightarrow> nat" where
  "bp_bucket_count_slack P =
     length (bp_buckets P) -
       Suc (length (bp_entries P) div bp_block_size P)"

definition bp_split_potential :: "'k bucketed_partition \<Rightarrow> nat" where
  "bp_split_potential P =
     4 * bp_overflow_potential P + bp_bucket_count_slack P"

definition bp_amortized_step_bound ::
  "nat \<Rightarrow> 'k bucketed_partition \<Rightarrow> 'k bucketed_partition \<Rightarrow> nat \<Rightarrow> bool" where
  "bp_amortized_step_bound c P P' t \<longleftrightarrow>
     c + bp_split_potential P' \<le> t + bp_split_potential P"

definition bp_pull_state_of ::
  "'k set \<times> real \<times> 'k bucketed_partition \<Rightarrow> 'k bucketed_partition" where
  "bp_pull_state_of R = (case R of (_, _, P') \<Rightarrow> P')"

definition bp_pull_amortized_step_bound ::
  "nat \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    ('k set \<times> real \<times> 'k bucketed_partition) \<Rightarrow> nat \<Rightarrow> bool" where
  "bp_pull_amortized_step_bound c P R t \<longleftrightarrow>
     c + bp_split_potential (bp_pull_state_of R) \<le>
       t + bp_split_potential P"

definition bp_bucket_count_ratio_ok :: "'k bucketed_partition \<Rightarrow> bool" where
  "bp_bucket_count_ratio_ok P \<longleftrightarrow>
     0 < bp_block_size P \<and>
     length (bp_buckets P) \<le>
       Suc (length (bp_entries P) div bp_block_size P)"

definition bp_regular_invariant :: "'k bucketed_partition \<Rightarrow> bool" where
  "bp_regular_invariant P \<longleftrightarrow>
     bp_ordered_invariant P \<and> bp_bucket_count_ratio_ok P"

definition bp_bucket_count_loaded :: "'k bucketed_partition \<Rightarrow> bool" where
  "bp_bucket_count_loaded P \<longleftrightarrow>
     bp_block_size P * (length (bp_buckets P) - 1) \<le>
       length (bp_entries P)"

definition bp_bucket_search_steps :: "'k bucketed_partition \<Rightarrow> nat" where
  "bp_bucket_search_steps P = Suc (floor_log (length (bp_buckets P)))"

fun bp_halving_search_steps :: "nat \<Rightarrow> nat" where
  [simp del]: "bp_halving_search_steps n =
    (if n < 2 then 1 else Suc (bp_halving_search_steps (n div 2)))"

definition bp_local_insert_search_charge :: "'k bucketed_partition \<Rightarrow> nat" where
  "bp_local_insert_search_charge P = Suc (bp_bucket_search_steps P)"

definition c_bp_bucket_directory_search ::
  "'k bp_bucket list \<Rightarrow> real \<Rightarrow> unit \<times> nat" where
  "c_bp_bucket_directory_search bs b =
     ((), bp_halving_search_steps (length bs))"

fun c_bp_bucketize_sorted_entries_aux ::
  "nat \<Rightarrow> nat \<Rightarrow> ('k \<times> real) list \<Rightarrow> 'k bp_bucket list \<times> nat" where
  "c_bp_bucketize_sorted_entries_aux 0 M xs = ([], 0)"
| "c_bp_bucketize_sorted_entries_aux (Suc fuel) M xs =
     (if M = 0 \<or> xs = []
      then ([], 0)
      else (let (bs, c) =
              c_bp_bucketize_sorted_entries_aux fuel M (drop M xs)
            in (bp_make_bucket (take M xs) # bs,
                Suc (length (take M xs) + c))))"

definition c_bp_bucketize_sorted_entries ::
  "nat \<Rightarrow> ('k \<times> real) list \<Rightarrow> 'k bp_bucket list \<times> nat" where
  "c_bp_bucketize_sorted_entries M xs =
     c_bp_bucketize_sorted_entries_aux (length xs) M xs"

definition c_bp_bucketize_entries ::
  "nat \<Rightarrow> ('k \<times> real) list \<Rightarrow> 'k bp_bucket list \<times> nat" where
  "c_bp_bucketize_entries M xs =
     c_bp_bucketize_sorted_entries M (sort_key snd xs)"

definition c_bp_rebucket_build ::
  "'k bucketed_partition \<Rightarrow> 'k bucketed_partition \<times> nat" where
  "c_bp_rebucket_build P =
     (case c_bp_bucketize_entries (bp_block_size P) (bp_entries P) of
        (bs, c) \<Rightarrow> (P\<lparr>bp_buckets := bs\<rparr>, c))"

text \<open>
  The definitions above introduce the amortized accounting used throughout the
  cost proof.  @{const bp_ratio_log_budget} is the formal ratio-log term:
  it applies @{const floor_log} to \<open>Suc (N div M)\<close>, avoiding division by zero
  corner cases at the statement level.  The actual bucket-directory search is
  modeled by @{const bp_halving_search_steps}, and
  @{const bp_bucket_search_steps} records the resulting cost for a state.

  The potential @{const bp_split_potential} has two components.  The weighted
  overflow component @{const bp_overflow_potential} counts entries above the
  strict block size, multiplied by four in the combined potential.  The
  @{const bp_bucket_count_slack} component measures how far the bucket count is
  above the target ratio.  A regular state, captured by
  @{const bp_regular_invariant}, has no such debt: it is ordered and satisfies
  @{const bp_bucket_count_ratio_ok}.  The amortized predicates
  @{const bp_amortized_step_bound} and @{const bp_pull_amortized_step_bound}
  express the usual inequality \<open>actual + Phi(after) <= budget + Phi(before)\<close>.
\<close>

definition c_bp_local_insert_search ::
  "'k \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k bucketed_partition \<times> nat" where
  "c_bp_local_insert_search x b P =
     (bp_local_insert_state x b P, bp_local_insert_search_charge P)"

definition c_bp_local_insert_split ::
  "'k \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k bucketed_partition \<times> nat" where
  "c_bp_local_insert_split x b P =
     (bp_local_insert_state x b P,
      bp_local_insert_search_charge P +
        bp_local_split_budget (bp_block_size P))"

definition c_bp_lazy_insert ::
  "'k \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k bucketed_partition \<times> nat" where
  "c_bp_lazy_insert x b P =
     (bp_lazy_insert_state x b P,
      bp_local_insert_search_charge P +
        bp_lazy_split_budget (bp_block_size P))"

definition bp_lazy_bucket_insert_charge ::
  "nat \<Rightarrow> 'k bp_bucket \<Rightarrow> nat" where
  "bp_lazy_bucket_insert_charge M b =
     (if length (bp_bucket_entries b) < 2 * M
      then 1 else bp_lazy_split_budget M)"

fun bp_lazy_insert_bucket_charge ::
  "nat \<Rightarrow> 'k \<times> real \<Rightarrow> 'k bp_bucket list \<Rightarrow> nat" where
  "bp_lazy_insert_bucket_charge M p [] = 1"
| "bp_lazy_insert_bucket_charge M p [b] =
     (if snd p < bp_marker b then 1
      else bp_lazy_bucket_insert_charge M b)"
| "bp_lazy_insert_bucket_charge M p (b # c # bs) =
     (if snd p < bp_marker b then 1
      else if snd p < bp_marker c
        then bp_lazy_bucket_insert_charge M b
        else bp_lazy_insert_bucket_charge M p (c # bs))"

definition bp_lazy_insert_charge ::
  "'k \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow> nat" where
  "bp_lazy_insert_charge x b P =
     (let b' = (if x \<in> bp_entry_keys (bp_entries P)
          then min (bp_values P x) b else b);
        P0 = bp_delete_key x P
      in bp_lazy_insert_bucket_charge (bp_block_size P0) (x, b')
           (bp_buckets P0))"

definition c_bp_lazy_insert_precise ::
  "'k \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k bucketed_partition \<times> nat" where
  "c_bp_lazy_insert_precise x b P =
     (bp_lazy_insert_state x b P,
      bp_local_insert_search_charge P + bp_lazy_insert_charge x b P)"

fun bp_lazy_batch_prepend_state ::
  "('k \<times> real) list \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k bucketed_partition" where
  "bp_lazy_batch_prepend_state [] P = P"
| "bp_lazy_batch_prepend_state ((x, b) # xs) P =
     bp_lazy_batch_prepend_state xs (bp_lazy_insert_state x b P)"

fun c_bp_lazy_batch_prepend_precise ::
  "('k \<times> real) list \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k bucketed_partition \<times> nat" where
  "c_bp_lazy_batch_prepend_precise [] P = (P, 0)"
| "c_bp_lazy_batch_prepend_precise ((x, b) # xs) P =
     (case c_bp_lazy_insert_precise x b P of
        (P1, c1) \<Rightarrow>
          (case c_bp_lazy_batch_prepend_precise xs P1 of
             (P2, c2) \<Rightarrow> (P2, c1 + c2)))"

fun bp_lazy_batch_ratio_ok ::
  "('k \<times> real) list \<Rightarrow> 'k bucketed_partition \<Rightarrow> bool" where
  "bp_lazy_batch_ratio_ok [] P \<longleftrightarrow> True"
| "bp_lazy_batch_ratio_ok ((x, b) # xs) P \<longleftrightarrow>
     bp_bucket_count_ratio_ok P \<and>
     bp_lazy_batch_ratio_ok xs
       (bp_result_of (c_bp_lazy_insert_precise x b P))"

fun bp_lazy_batch_insert_budget_sum ::
  "('k \<times> real) list \<Rightarrow> 'k bucketed_partition \<Rightarrow> nat" where
  "bp_lazy_batch_insert_budget_sum [] P = 0"
| "bp_lazy_batch_insert_budget_sum ((x, b) # xs) P =
     bp_lazy_insert_amortized_budget P +
     bp_lazy_batch_insert_budget_sum xs
       (bp_result_of (c_bp_lazy_insert_precise x b P))"

lemma c_bp_lazy_insert_precise_eq [simp]:
  "c_bp_lazy_insert_precise x b P =
    (bp_lazy_insert_state x b P,
     bp_local_insert_search_charge P + bp_lazy_insert_charge x b P)"
  unfolding c_bp_lazy_insert_precise_def by simp

definition bp_regularized_local_insert ::
  "'k \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow> 'k bucketed_partition" where
  "bp_regularized_local_insert x b P =
     bp_rebucket (bp_local_insert_state x b P)"

definition c_bp_regularized_local_insert ::
  "'k \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k bucketed_partition \<times> nat" where
  "c_bp_regularized_local_insert x b P =
     (bp_regularized_local_insert x b P, bp_local_insert_search_charge P)"

text \<open>
  This wrapper counts the concrete rebuilding pass explicitly.  It is an
  accounting bridge for the later lazy-split analysis, not the final insert
  operation bound: rebuilding every bucket has a linear term.
\<close>

definition c_bp_regularized_local_insert_build ::
  "'k \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k bucketed_partition \<times> nat" where
  "c_bp_regularized_local_insert_build x b P =
     (case c_bp_rebucket_build (bp_local_insert_state x b P) of
        (P', c) \<Rightarrow> (P', bp_local_insert_search_charge P + c))"

definition c_bp_rebucketed_batch_prepend_bulk ::
  "('k \<times> real) list \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k bucketed_partition \<times> nat" where
  "c_bp_rebucketed_batch_prepend_bulk xs P =
     (bp_rebucketed_batch_prepend xs P,
      bp_batch_prepend_log_budget xs (bp_block_size P))"

definition c_bp_bucketed_batch_prepend_direct ::
  "('k \<times> real) list \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k bucketed_partition \<times> nat" where
  "c_bp_bucketed_batch_prepend_direct xs P =
     (bp_bucketed_batch_prepend_state xs P,
      bp_batch_prepend_amortized_budget xs (bp_block_size P))"

definition c_bp_bucketed_batch_prepend_direct_actual ::
  "('k \<times> real) list \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k bucketed_partition \<times> nat" where
  "c_bp_bucketed_batch_prepend_direct_actual xs P =
     (bp_bucketed_batch_prepend_state xs P,
      bp_batch_prepend_log_budget xs (bp_block_size P))"

definition c_bp_first_bucket_pull ::
  "nat \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    ('k set \<times> real \<times> 'k bucketed_partition) \<times> nat" where
  "c_bp_first_bucket_pull M B P = (bp_first_bucket_pull M B P, M)"

definition c_bp_first_bucket_pull_scan ::
  "nat \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    ('k set \<times> real \<times> 'k bucketed_partition) \<times> nat" where
  "c_bp_first_bucket_pull_scan M B P =
     (case bp_first_bucket_pull M B P of
        (S, beta, P') \<Rightarrow> ((S, beta, P'), card S))"

lemma bp_ratio_log_budget_pos [simp]:
  "0 < bp_ratio_log_budget N M"
  unfolding bp_ratio_log_budget_def by simp

lemma bp_insert_search_budget_pos [simp]:
  "0 < bp_insert_search_budget N M"
  unfolding bp_insert_search_budget_def by simp

lemma bp_lazy_insert_amortized_budget_ratio:
  "bp_lazy_insert_amortized_budget P =
     bp_ratio_log_budget (length (bp_entries P)) (bp_block_size P) + 8"
  unfolding bp_lazy_insert_amortized_budget_def bp_insert_search_budget_def
  by simp

lemma bp_batch_prepend_amortized_budget_alt:
  "bp_batch_prepend_amortized_budget xs M =
     bp_batch_prepend_per_item_budget xs M * length xs"
  unfolding bp_batch_prepend_amortized_budget_def
    bp_batch_prepend_log_budget_def
    bp_batch_prepend_per_item_budget_def
  by (simp add: algebra_simps)

lemma bp_batch_prepend_log_budget_le_amortized_budget:
  "bp_batch_prepend_log_budget xs M \<le>
    bp_batch_prepend_amortized_budget xs M"
  unfolding bp_batch_prepend_amortized_budget_def by simp

lemma bp_halving_search_steps_eq_floor_log:
  "bp_halving_search_steps n = Suc (floor_log n)"
  by (induction n rule: bp_halving_search_steps.induct)
    (simp add: bp_halving_search_steps.simps floor_log.simps)

lemma c_bp_bucket_directory_search_result [simp]:
  "bp_result_of (c_bp_bucket_directory_search bs b) = ()"
  unfolding bp_result_of_def c_bp_bucket_directory_search_def by simp

lemma c_bp_bucket_directory_search_steps [simp]:
  "bp_steps_of (c_bp_bucket_directory_search bs b) =
    bp_halving_search_steps (length bs)"
  unfolding bp_steps_of_def c_bp_bucket_directory_search_def by simp

lemma c_bp_bucket_directory_search_steps_floor_log:
  "bp_steps_of (c_bp_bucket_directory_search bs b) =
    Suc (floor_log (length bs))"
  by (simp add: bp_halving_search_steps_eq_floor_log)

lemma c_bp_bucket_directory_search_state_steps:
  "bp_steps_of (c_bp_bucket_directory_search (bp_buckets P) b) =
    bp_bucket_search_steps P"
proof -
  have "bp_steps_of (c_bp_bucket_directory_search (bp_buckets P) b) =
      Suc (floor_log (length (bp_buckets P)))"
    by (simp add: bp_halving_search_steps_eq_floor_log)
  also have "\<dots> = bp_bucket_search_steps P"
    unfolding bp_bucket_search_steps_def by simp
  finally show ?thesis .
qed

lemma c_bp_bucket_directory_search_ratio_bound:
  assumes count_le: "length bs \<le> Suc (N div M)"
  shows "bp_steps_of (c_bp_bucket_directory_search bs b) \<le>
    bp_ratio_log_budget N M"
proof -
  have "floor_log (length bs) \<le> floor_log (Suc (N div M))"
    by (rule floor_log_le_iff[OF count_le])
  then show ?thesis
    unfolding bp_ratio_log_budget_def
    by (simp add: bp_halving_search_steps_eq_floor_log)
qed

lemma bp_local_insert_search_charge_search_steps:
  "bp_local_insert_search_charge P =
    Suc (bp_steps_of
      (c_bp_bucket_directory_search (bp_buckets P) b))"
proof -
  have search:
    "bp_steps_of (c_bp_bucket_directory_search (bp_buckets P) b) =
      bp_bucket_search_steps P"
    by (rule c_bp_bucket_directory_search_state_steps)
  show ?thesis
    unfolding bp_local_insert_search_charge_def using search by simp
qed

lemma c_bp_bucketize_sorted_entries_aux_empty [simp]:
  "c_bp_bucketize_sorted_entries_aux fuel M [] = ([], 0)"
  by (cases fuel) simp_all

lemma c_bp_bucketize_sorted_entries_aux_result [simp]:
  "bp_result_of (c_bp_bucketize_sorted_entries_aux fuel M xs) =
    bp_bucketize_sorted_entries_aux fuel M xs"
proof (induction fuel arbitrary: xs)
  case 0
  then show ?case
    by (simp add: bp_result_of_def)
next
  case (Suc fuel)
  show ?case
  proof (cases "M = 0 \<or> xs = []")
    case True
    then show ?thesis
      by (simp add: bp_result_of_def)
  next
    case False
    obtain bs c where rec:
      "c_bp_bucketize_sorted_entries_aux fuel M (drop M xs) = (bs, c)"
      by (cases "c_bp_bucketize_sorted_entries_aux fuel M (drop M xs)")
        simp
    have bs:
      "bs = bp_bucketize_sorted_entries_aux fuel M (drop M xs)"
      using Suc.IH[of "drop M xs"] rec
      by (simp add: bp_result_of_def)
    show ?thesis
      using False rec bs by (simp add: bp_result_of_def Let_def)
  qed
qed

lemma c_bp_bucketize_sorted_entries_result [simp]:
  "bp_result_of (c_bp_bucketize_sorted_entries M xs) =
    bp_bucketize_sorted_entries M xs"
  unfolding c_bp_bucketize_sorted_entries_def
    bp_bucketize_sorted_entries_def by simp

lemma c_bp_bucketize_entries_result [simp]:
  "bp_result_of (c_bp_bucketize_entries M xs) = bp_bucketize_entries M xs"
  unfolding c_bp_bucketize_entries_def bp_bucketize_entries_def by simp

lemma c_bp_bucketize_sorted_entries_aux_steps_le:
  assumes M_pos: "0 < M"
    and fuel: "length xs \<le> fuel"
  shows "bp_steps_of (c_bp_bucketize_sorted_entries_aux fuel M xs) \<le>
    length xs + Suc (length xs div M)"
  using M_pos fuel
proof (induction fuel arbitrary: xs)
  case 0
  then show ?case
    by (simp add: bp_steps_of_def)
next
  case (Suc fuel)
  show ?case
  proof (cases "xs = []")
    case True
    then show ?thesis
      by (simp add: bp_steps_of_def)
  next
    case False
    note xs_nonempty = False
    show ?thesis
    proof (cases "length xs < M")
      case True
      then have "drop M xs = []"
        by simp
      then show ?thesis
        using Suc.prems xs_nonempty True by (simp add: bp_steps_of_def)
    next
      case False
      have M_le: "M \<le> length xs"
        using False by simp
      have drop_fuel: "length (drop M xs) \<le> fuel"
        using Suc.prems False by simp
      have tail:
        "bp_steps_of
          (c_bp_bucketize_sorted_entries_aux fuel M (drop M xs)) \<le>
          length (drop M xs) + Suc (length (drop M xs) div M)"
        by (rule Suc.IH[OF Suc.prems(1) drop_fuel])
      have len_xs: "length xs = M + length (drop M xs)"
        using M_le by simp
      have take_len: "length (take M xs) = M"
        using M_le by simp
      have div_eq:
        "length xs div M = Suc (length (drop M xs) div M)"
      proof -
        have "length xs div M = (M + length (drop M xs)) div M"
          using len_xs by simp
        also have "\<dots> = length (drop M xs) div M + 1"
          using Suc.prems(1) by (simp add: div_add_self1)
        finally show ?thesis by simp
      qed
      obtain bs c where rec:
        "c_bp_bucketize_sorted_entries_aux fuel M (drop M xs) = (bs, c)"
        by (cases "c_bp_bucketize_sorted_entries_aux fuel M (drop M xs)")
          simp
      have c_le:
        "c \<le> length (drop M xs) + Suc (length (drop M xs) div M)"
        using tail rec unfolding bp_steps_of_def by simp
      have step_eq:
        "bp_steps_of
          (c_bp_bucketize_sorted_entries_aux (Suc fuel) M xs) =
          Suc (M + c)"
        using Suc.prems xs_nonempty False rec take_len
        by (simp add: bp_steps_of_def Let_def)
      have "Suc (M + c) \<le>
          M + length (drop M xs) +
            Suc (Suc (length (drop M xs) div M))"
        using c_le by linarith
      show ?thesis
        using step_eq len_xs div_eq
          \<open>Suc (M + c) \<le>
            M + length (drop M xs) +
              Suc (Suc (length (drop M xs) div M))\<close>
        by simp
    qed
  qed
qed

lemma c_bp_bucketize_sorted_entries_steps_le:
  assumes "0 < M"
  shows "bp_steps_of (c_bp_bucketize_sorted_entries M xs) \<le>
    length xs + Suc (length xs div M)"
  unfolding c_bp_bucketize_sorted_entries_def
  by (rule c_bp_bucketize_sorted_entries_aux_steps_le[OF assms]) simp

lemma c_bp_bucketize_entries_steps_le:
  assumes "0 < M"
  shows "bp_steps_of (c_bp_bucketize_entries M xs) \<le>
    length xs + Suc (length xs div M)"
  unfolding c_bp_bucketize_entries_def
  using c_bp_bucketize_sorted_entries_steps_le[OF assms,
      of "sort_key snd xs"]
  by simp

lemma c_bp_bucketize_entries_steps_le_linear_length:
  assumes "0 < M"
  shows "bp_steps_of (c_bp_bucketize_entries M xs) \<le>
    Suc (2 * length xs)"
proof -
  have "length xs div M \<le> length xs"
    by simp
  then have "length xs + Suc (length xs div M) \<le>
      Suc (2 * length xs)"
    by linarith
  moreover have "bp_steps_of (c_bp_bucketize_entries M xs) \<le>
      length xs + Suc (length xs div M)"
    by (rule c_bp_bucketize_entries_steps_le[OF assms])
  ultimately show ?thesis
    by linarith
qed

lemma c_bp_bucketize_entries_steps_le_local_split_budget:
  assumes M_pos: "0 < M"
    and len: "length xs \<le> Suc M"
  shows "bp_steps_of (c_bp_bucketize_entries M xs) \<le>
    bp_local_split_budget M"
proof -
  have steps:
    "bp_steps_of (c_bp_bucketize_entries M xs) \<le>
      Suc (2 * length xs)"
    by (rule c_bp_bucketize_entries_steps_le_linear_length[OF M_pos])
  have "Suc (2 * length xs) \<le> bp_local_split_budget M"
    using len unfolding bp_local_split_budget_def by simp
  then show ?thesis
    using steps by linarith
qed

lemma bp_local_split_budget_le_lazy_split_budget:
  "bp_local_split_budget M \<le> bp_lazy_split_budget M"
  unfolding bp_local_split_budget_def bp_lazy_split_budget_def by simp

lemma c_bp_bucketize_entries_steps_le_lazy_split_budget:
  assumes M_pos: "0 < M"
    and len: "length xs \<le> Suc (2 * M)"
  shows "bp_steps_of (c_bp_bucketize_entries M xs) \<le>
    bp_lazy_split_budget M"
proof -
  have steps:
    "bp_steps_of (c_bp_bucketize_entries M xs) \<le>
      Suc (2 * length xs)"
    by (rule c_bp_bucketize_entries_steps_le_linear_length[OF M_pos])
  have "Suc (2 * length xs) \<le> bp_lazy_split_budget M"
    using len unfolding bp_lazy_split_budget_def by simp
  then show ?thesis
    using steps by linarith
qed

lemma bp_lazy_split_budget_paid_by_bucket_overflow:
  assumes large: "2 * M \<le> length (bp_bucket_entries b)"
  shows "bp_lazy_split_budget M \<le>
    5 + 4 * bp_bucket_overflow M b"
proof -
  have "M \<le> bp_bucket_overflow M b"
    using large unfolding bp_bucket_overflow_def by linarith
  then show ?thesis
    unfolding bp_lazy_split_budget_def by simp
qed

lemma bp_bucket_overflow_sum_simps [simp]:
  "bp_bucket_overflow_sum M [] = 0"
  "bp_bucket_overflow_sum M (b # bs) =
    bp_bucket_overflow M b + bp_bucket_overflow_sum M bs"
  "bp_bucket_overflow_sum M (bs @ cs) =
    bp_bucket_overflow_sum M bs + bp_bucket_overflow_sum M cs"
  unfolding bp_bucket_overflow_sum_def by simp_all

lemma bp_overflow_potential_alt:
  "bp_overflow_potential P =
    bp_bucket_overflow_sum (bp_block_size P) (bp_buckets P)"
  unfolding bp_overflow_potential_def bp_bucket_overflow_sum_def by simp

lemma bp_bucket_overflow_sum_zero_if_sizes_ok:
  assumes sizes: "\<forall>b\<in>set bs. length (bp_bucket_entries b) \<le> M"
  shows "bp_bucket_overflow_sum M bs = 0"
  using sizes unfolding bp_bucket_overflow_sum_def bp_bucket_overflow_def
  by (induction bs) auto

lemma bp_bucket_overflow_cons_credit:
  fixes b :: "'k bp_bucket"
  shows "1 + 4 * bp_bucket_overflow M
      (b\<lparr>bp_bucket_entries := p # bp_bucket_entries b\<rparr>) \<le>
    5 + 4 * bp_bucket_overflow M b"
proof -
  let ?l = "length (bp_bucket_entries b)"
  show ?thesis
  proof (cases "?l < M")
    case True
    then have "Suc ?l \<le> M"
      by simp
    then have after: "bp_bucket_overflow M
        (b\<lparr>bp_bucket_entries := p # bp_bucket_entries b\<rparr>) = 0"
      unfolding bp_bucket_overflow_def by simp
    have before: "bp_bucket_overflow M b = 0"
      using True unfolding bp_bucket_overflow_def by simp
    show ?thesis
      unfolding after before by simp
  next
    case False
    then have M_le: "M \<le> ?l"
      by simp
    have after: "bp_bucket_overflow M
        (b\<lparr>bp_bucket_entries := p # bp_bucket_entries b\<rparr>) =
      Suc (bp_bucket_overflow M b)"
      using M_le unfolding bp_bucket_overflow_def by simp
    show ?thesis
      unfolding after by simp
  qed
qed

lemma bp_lazy_bucket_insert_entries_weighted_overflow_credit:
  assumes M_pos: "0 < M"
    and size: "length (bp_bucket_entries b) \<le> 2 * M"
  shows "bp_lazy_bucket_insert_charge M b +
      4 * bp_bucket_overflow_sum M
        (bp_lazy_bucket_insert_entries M p b) \<le>
    5 + 4 * bp_bucket_overflow M b"
proof (cases "length (bp_bucket_entries b) < 2 * M")
  case True
  have charge: "bp_lazy_bucket_insert_charge M b = 1"
    using True unfolding bp_lazy_bucket_insert_charge_def by simp
  have result:
    "bp_lazy_bucket_insert_entries M p b =
      [b\<lparr>bp_bucket_entries := p # bp_bucket_entries b\<rparr>]"
    using True unfolding bp_lazy_bucket_insert_entries_def by simp
  have credit:
    "1 + 4 * bp_bucket_overflow M
        (b\<lparr>bp_bucket_entries := p # bp_bucket_entries b\<rparr>) \<le>
      5 + 4 * bp_bucket_overflow M b"
    by (rule bp_bucket_overflow_cons_credit)
  show ?thesis
    using credit unfolding charge result by simp
next
  case False
  have len_eq: "length (bp_bucket_entries b) = 2 * M"
    using False size by simp
  have charge: "bp_lazy_bucket_insert_charge M b = bp_lazy_split_budget M"
    using False unfolding bp_lazy_bucket_insert_charge_def by simp
  have result:
    "bp_lazy_bucket_insert_entries M p b =
      bp_bucketize_entries M (p # bp_bucket_entries b)"
    using False unfolding bp_lazy_bucket_insert_entries_def by simp
  have sizes:
    "\<forall>c\<in>set (bp_bucketize_entries M (p # bp_bucket_entries b)).
      length (bp_bucket_entries c) \<le> M"
    by (rule bp_bucketize_entries_sizes_ok[OF M_pos])
  have overflow_zero:
    "bp_bucket_overflow_sum M
      (bp_bucketize_entries M (p # bp_bucket_entries b)) = 0"
    by (rule bp_bucket_overflow_sum_zero_if_sizes_ok[OF sizes])
  have before: "bp_bucket_overflow M b = M"
    using len_eq unfolding bp_bucket_overflow_def by simp
  show ?thesis
    unfolding charge result overflow_zero before bp_lazy_split_budget_def
    by simp
qed

lemma bp_lazy_insert_bucket_weighted_overflow_credit:
  assumes M_pos: "0 < M"
    and sizes: "\<forall>b\<in>set bs. length (bp_bucket_entries b) \<le> 2 * M"
  shows "bp_lazy_insert_bucket_charge M p bs +
      4 * bp_bucket_overflow_sum M (bp_lazy_insert_bucket M p bs) \<le>
    5 + 4 * bp_bucket_overflow_sum M bs"
  using sizes
proof (induction bs arbitrary: p)
  case Nil
  have result: "bp_lazy_insert_bucket M p [] = bp_bucketize_entries M [p]"
    by simp
  have sizes_result:
    "\<forall>c\<in>set (bp_bucketize_entries M [p]).
      length (bp_bucket_entries c) \<le> M"
    by (rule bp_bucketize_entries_sizes_ok[OF M_pos])
  have overflow_zero:
    "bp_bucket_overflow_sum M (bp_bucketize_entries M [p]) = 0"
    by (rule bp_bucket_overflow_sum_zero_if_sizes_ok[OF sizes_result])
  show ?case
    unfolding result overflow_zero by simp
next
  case (Cons b bs)
  note IH = Cons.IH
  note sizes = Cons.prems
  have b_size: "length (bp_bucket_entries b) \<le> 2 * M"
    using sizes by simp
  show ?case
  proof (cases bs)
    case Nil
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      have result:
        "bp_lazy_insert_bucket M p (b # bs) =
          bp_bucketize_entries M [p] @ [b]"
        using Nil True by simp
      have charge: "bp_lazy_insert_bucket_charge M p (b # bs) = 1"
        using Nil True by simp
      have sizes_single:
        "\<forall>c\<in>set (bp_bucketize_entries M [p]).
          length (bp_bucket_entries c) \<le> M"
        by (rule bp_bucketize_entries_sizes_ok[OF M_pos])
      have overflow_single:
        "bp_bucket_overflow_sum M (bp_bucketize_entries M [p]) = 0"
        by (rule bp_bucket_overflow_sum_zero_if_sizes_ok[OF sizes_single])
      show ?thesis
        using Nil True overflow_single unfolding result charge by simp
    next
      case False
      have result:
        "bp_lazy_insert_bucket M p (b # bs) =
          bp_lazy_bucket_insert_entries M p b"
        using Nil False by simp
      have charge:
        "bp_lazy_insert_bucket_charge M p (b # bs) =
          bp_lazy_bucket_insert_charge M b"
        using Nil False by simp
      show ?thesis
        unfolding result charge using Nil
        by (simp add: bp_lazy_bucket_insert_entries_weighted_overflow_credit
            [OF M_pos b_size, of p])
    qed
  next
    case (Cons c cs)
    have tail_sizes:
      "\<forall>b\<in>set bs. length (bp_bucket_entries b) \<le> 2 * M"
      using sizes by simp
    show ?thesis
    proof (cases "snd p < bp_marker b")
      case True
      have result:
        "bp_lazy_insert_bucket M p (b # bs) =
          bp_bucketize_entries M [p] @ b # bs"
        using Cons True by simp
      have charge: "bp_lazy_insert_bucket_charge M p (b # bs) = 1"
        using Cons True by simp
      have sizes_single:
        "\<forall>c\<in>set (bp_bucketize_entries M [p]).
          length (bp_bucket_entries c) \<le> M"
        by (rule bp_bucketize_entries_sizes_ok[OF M_pos])
      have overflow_single:
        "bp_bucket_overflow_sum M (bp_bucketize_entries M [p]) = 0"
        by (rule bp_bucket_overflow_sum_zero_if_sizes_ok[OF sizes_single])
      show ?thesis
        using Cons True overflow_single unfolding result charge by simp
    next
      case False
      show ?thesis
      proof (cases "snd p < bp_marker c")
        case True
        have result:
          "bp_lazy_insert_bucket M p (b # bs) =
            bp_lazy_bucket_insert_entries M p b @ bs"
          using Cons False True by simp
        have charge:
          "bp_lazy_insert_bucket_charge M p (b # bs) =
            bp_lazy_bucket_insert_charge M b"
          using Cons False True by simp
        have bucket_credit:
          "bp_lazy_bucket_insert_charge M b +
              4 * bp_bucket_overflow_sum M
                (bp_lazy_bucket_insert_entries M p b) \<le>
            5 + 4 * bp_bucket_overflow M b"
          by (rule bp_lazy_bucket_insert_entries_weighted_overflow_credit
              [OF M_pos b_size])
        show ?thesis
          using bucket_credit unfolding result charge
          by simp
      next
        case False
        have result:
          "bp_lazy_insert_bucket M p (b # bs) =
            b # bp_lazy_insert_bucket M p bs"
          using Cons \<open>\<not> snd p < bp_marker b\<close> False by simp
        have charge:
          "bp_lazy_insert_bucket_charge M p (b # bs) =
            bp_lazy_insert_bucket_charge M p bs"
          using Cons \<open>\<not> snd p < bp_marker b\<close> False by simp
        have tail_credit:
          "bp_lazy_insert_bucket_charge M p bs +
              4 * bp_bucket_overflow_sum M
                (bp_lazy_insert_bucket M p bs) \<le>
            5 + 4 * bp_bucket_overflow_sum M bs"
          by (rule IH[OF tail_sizes])
        show ?thesis
          using tail_credit unfolding result charge by simp
      qed
    qed
  qed
qed

lemma bp_delete_key_from_bucket_overflow_le:
  "bp_bucket_overflow M (bp_delete_key_from_bucket x b) \<le>
    bp_bucket_overflow M b"
proof -
  have len_le:
    "length (bp_bucket_entries (bp_delete_key_from_bucket x b)) \<le>
      length (bp_bucket_entries b)"
    unfolding bp_delete_key_from_bucket_def by simp
  show ?thesis
    using len_le unfolding bp_bucket_overflow_def by simp
qed

lemma bp_bucket_overflow_sum_map_delete_key_le:
  "bp_bucket_overflow_sum M (map (bp_delete_key_from_bucket x) bs) \<le>
    bp_bucket_overflow_sum M bs"
proof (induction bs)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  have head:
    "bp_bucket_overflow M (bp_delete_key_from_bucket x b) \<le>
      bp_bucket_overflow M b"
    by (rule bp_delete_key_from_bucket_overflow_le)
  show ?case
    using head Cons.IH by simp
qed

lemma bp_delete_key_overflow_potential_le:
  "bp_overflow_potential (bp_delete_key x P) \<le> bp_overflow_potential P"
proof -
  have "bp_bucket_overflow_sum (bp_block_size P)
      (map (bp_delete_key_from_bucket x) (bp_buckets P)) \<le>
    bp_bucket_overflow_sum (bp_block_size P) (bp_buckets P)"
    by (rule bp_bucket_overflow_sum_map_delete_key_le)
  then show ?thesis
    unfolding bp_delete_key_def bp_overflow_potential_alt by simp
qed

lemma bp_delete_keys_from_bucket_overflow_le:
  "bp_bucket_overflow M (bp_delete_keys_from_bucket S b) \<le>
    bp_bucket_overflow M b"
proof -
  have len_le:
    "length (bp_bucket_entries (bp_delete_keys_from_bucket S b)) \<le>
      length (bp_bucket_entries b)"
    unfolding bp_delete_keys_from_bucket_def by simp
  show ?thesis
    using len_le unfolding bp_bucket_overflow_def by simp
qed

lemma bp_bucket_overflow_sum_map_delete_keys_le:
  "bp_bucket_overflow_sum M (map (bp_delete_keys_from_bucket S) bs) \<le>
    bp_bucket_overflow_sum M bs"
proof (induction bs)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  have head:
    "bp_bucket_overflow M (bp_delete_keys_from_bucket S b) \<le>
      bp_bucket_overflow M b"
    by (rule bp_delete_keys_from_bucket_overflow_le)
  show ?case
    using head Cons.IH by simp
qed

lemma bp_delete_keys_overflow_potential_le:
  "bp_overflow_potential (bp_delete_keys S P) \<le> bp_overflow_potential P"
proof -
  have "bp_bucket_overflow_sum (bp_block_size P)
      (map (bp_delete_keys_from_bucket S) (bp_buckets P)) \<le>
    bp_bucket_overflow_sum (bp_block_size P) (bp_buckets P)"
    by (rule bp_bucket_overflow_sum_map_delete_keys_le)
  then show ?thesis
    unfolding bp_delete_keys_def bp_overflow_potential_alt by simp
qed

lemma length_filter_fst_notin_le_card:
  assumes distinct: "distinct (map fst xs)"
    and finite: "finite S"
  shows "length xs \<le> length (filter (\<lambda>p. fst p \<notin> S) xs) + card S"
proof -
  let ?removed = "filter (\<lambda>p. fst p \<in> S) xs"
  have len_part:
    "length xs = length (filter (\<lambda>p. fst p \<notin> S) xs) + length ?removed"
    by (induction xs) auto
  have distinct_removed: "distinct (map fst ?removed)"
    using distinct by (induction xs) auto
  have "length ?removed = card (set (map fst ?removed))"
    using distinct_card[OF distinct_removed] by simp
  also have "\<dots> \<le> card S"
    using finite by (intro card_mono) auto
  finally have "length ?removed \<le> card S" .
  then show ?thesis
    using len_part by linarith
qed

lemma div_add_right_le_div_plus:
  fixes n k M :: nat
  assumes M_pos: "0 < M"
  shows "(n + k) div M \<le> n div M + k"
proof -
  have n_less: "n < Suc (n div M) * M"
  proof -
    have "n div M < Suc (n div M)"
      by simp
    moreover have
      "n div M < Suc (n div M) \<longleftrightarrow> n < Suc (n div M) * M"
      by (rule div_less_iff_less_mult[OF M_pos])
    then show ?thesis
      using calculation by simp
  qed
  have k_le: "k \<le> k * M"
    using M_pos by (cases M) auto
  have "n + k < Suc (n div M) * M + k * M"
    using n_less k_le by linarith
  also have "\<dots> = (Suc (n div M) + k) * M"
    by (simp add: algebra_simps)
  finally have "(n + k) div M < Suc (n div M) + k"
    using M_pos by (simp add: div_less_iff_less_mult)
  then show ?thesis by simp
qed

lemma div_bound_after_delete:
  assumes M_pos: "0 < M"
    and len: "n \<le> n' + k"
  shows "Suc (n div M) \<le> Suc (n' div M) + k"
proof -
  have "n div M \<le> (n' + k) div M"
    by (rule div_le_mono[OF len])
  also have "\<dots> \<le> n' div M + k"
    by (rule div_add_right_le_div_plus[OF M_pos])
  finally show ?thesis by simp
qed

lemma nat_diff_le_diff_add_right:
  fixes a c d k :: nat
  assumes "c \<le> d + k"
  shows "a - d \<le> (a - c) + k"
proof -
  have base: "a - d \<le> (a - c) + (c - d)"
    by simp
  have "c - d \<le> k"
    using assms by simp
  then show ?thesis
    using base by linarith
qed

lemma nat_diff_add_right_le:
  fixes a b c d k :: nat
  assumes a_le: "a \<le> k + b"
    and d_le_c: "d \<le> c"
  shows "a - c \<le> k + (b - d)"
proof -
  have "a - c \<le> (k + b) - c"
    using a_le by simp
  also have "\<dots> \<le> k + (b - c)"
    by arith
  also have "\<dots> \<le> k + (b - d)"
    using d_le_c by simp
  finally show ?thesis .
qed

lemma bp_delete_keys_entries_length_le:
  assumes distinct: "bp_distinct_keys P"
    and finite: "finite S"
  shows "length (bp_entries P) \<le>
    length (bp_entries (bp_delete_keys S P)) + card S"
  using length_filter_fst_notin_le_card[OF _ finite, of "bp_entries P"]
    distinct
  unfolding bp_entries_delete_keys bp_distinct_keys_def by simp

lemma bp_delete_keys_bucket_count_slack_le:
  assumes M_pos: "0 < bp_block_size P"
    and distinct: "bp_distinct_keys P"
    and finite: "finite S"
  shows "bp_bucket_count_slack (bp_delete_keys S P) \<le>
    bp_bucket_count_slack P + card S"
proof -
  let ?M = "bp_block_size P"
  let ?N = "length (bp_entries P)"
  let ?N' = "length (bp_entries (bp_delete_keys S P))"
  let ?K = "length (bp_buckets P)"
  have len: "?N \<le> ?N' + card S"
    by (rule bp_delete_keys_entries_length_le[OF distinct finite])
  have divs: "Suc (?N div ?M) \<le> Suc (?N' div ?M) + card S"
    by (rule div_bound_after_delete[OF M_pos len])
  have slack:
    "?K - Suc (?N' div ?M) \<le> (?K - Suc (?N div ?M)) + card S"
    by (rule nat_diff_le_diff_add_right[OF divs])
  show ?thesis
    using slack unfolding bp_bucket_count_slack_def bp_delete_keys_def by simp
qed

lemma bp_delete_keys_split_potential_le:
  assumes M_pos: "0 < bp_block_size P"
    and distinct: "bp_distinct_keys P"
    and finite: "finite S"
  shows "bp_split_potential (bp_delete_keys S P) \<le>
    bp_split_potential P + card S"
proof -
  have overflow:
    "bp_overflow_potential (bp_delete_keys S P) \<le> bp_overflow_potential P"
    by (rule bp_delete_keys_overflow_potential_le)
  have slack:
    "bp_bucket_count_slack (bp_delete_keys S P) \<le>
      bp_bucket_count_slack P + card S"
    by (rule bp_delete_keys_bucket_count_slack_le[OF M_pos distinct finite])
  show ?thesis
    using overflow slack unfolding bp_split_potential_def by linarith
qed

lemma bp_lazy_insert_state_weighted_overflow_credit_after_delete:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "bp_lazy_insert_charge x b P +
      4 * bp_overflow_potential (bp_lazy_insert_state x b P) \<le>
    5 + 4 * bp_overflow_potential (bp_delete_key x P)"
proof -
  let ?old_keys = "bp_entry_keys (bp_entries P)"
  let ?b = "if x \<in> ?old_keys then min (bp_values P x) b else b"
  let ?P0 = "bp_delete_key x P"
  let ?M = "bp_block_size ?P0"
  let ?bs = "bp_buckets ?P0"
  let ?new_bs = "bp_lazy_insert_bucket ?M (x, ?b) ?bs"
  let ?P' = "?P0\<lparr>bp_buckets := ?new_bs,
      bp_values := (bp_values P)(x := ?b)\<rparr>"
  have inv: "bp_lazy_invariant P"
    by (rule bp_lazy_ordered_invariant_lazy_invariant[OF lazy])
  have inv0: "bp_lazy_invariant ?P0"
    by (rule bp_delete_key_lazy_invariant[OF inv])
  have M_pos: "0 < ?M"
    using inv0 unfolding bp_lazy_invariant_def by blast
  have sizes0:
    "\<forall>c\<in>set ?bs. length (bp_bucket_entries c) \<le> 2 * ?M"
    using inv0 unfolding bp_lazy_invariant_def
      bp_lazy_bucket_sizes_ok_def by blast
  have list_credit:
    "bp_lazy_insert_bucket_charge ?M (x, ?b) ?bs +
        4 * bp_bucket_overflow_sum ?M ?new_bs \<le>
      5 + 4 * bp_bucket_overflow_sum ?M ?bs"
    by (rule bp_lazy_insert_bucket_weighted_overflow_credit
        [OF M_pos sizes0])
  have state: "bp_lazy_insert_state x b P = ?P'"
    unfolding bp_lazy_insert_state_def Let_def by simp
  have charge:
    "bp_lazy_insert_charge x b P =
      bp_lazy_insert_bucket_charge ?M (x, ?b) ?bs"
    unfolding bp_lazy_insert_charge_def Let_def by simp
  show ?thesis
    using list_credit
    unfolding state charge bp_overflow_potential_alt by simp
qed

lemma bp_lazy_insert_state_weighted_overflow_credit:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "bp_lazy_insert_charge x b P +
      4 * bp_overflow_potential (bp_lazy_insert_state x b P) \<le>
    5 + 4 * bp_overflow_potential P"
proof -
  have after_delete:
    "bp_lazy_insert_charge x b P +
        4 * bp_overflow_potential (bp_lazy_insert_state x b P) \<le>
      5 + 4 * bp_overflow_potential (bp_delete_key x P)"
    by (rule bp_lazy_insert_state_weighted_overflow_credit_after_delete
        [OF lazy])
  have delete_le:
    "bp_overflow_potential (bp_delete_key x P) \<le> bp_overflow_potential P"
    by (rule bp_delete_key_overflow_potential_le)
  show ?thesis
    using after_delete delete_le by linarith
qed

lemma nat_diff_le_diff_add:
  fixes a b c d k :: nat
  assumes a_le: "a \<le> b + k"
    and c_le: "c \<le> d"
  shows "a - d \<le> (b - c) + k"
proof -
  have "a - d \<le> a - c"
    using c_le by simp
  also have "\<dots> \<le> (b + k) - c"
    using a_le by simp
  also have "\<dots> \<le> (b - c) + k"
    by simp
  finally show ?thesis .
qed

lemma bp_lazy_insert_state_bucket_count_slack_le:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "bp_bucket_count_slack (bp_lazy_insert_state x b P) \<le>
    bp_bucket_count_slack P + 2"
proof -
  let ?P' = "bp_lazy_insert_state x b P"
  let ?M = "bp_block_size P"
  have inv: "bp_lazy_invariant P"
    by (rule bp_lazy_ordered_invariant_lazy_invariant[OF lazy])
  have M_pos: "0 < ?M"
    using inv unfolding bp_lazy_invariant_def by blast
  have block: "bp_block_size ?P' = ?M"
    unfolding bp_lazy_insert_state_def bp_delete_key_def
    by (simp add: Let_def split: if_splits)
  have buckets:
    "length (bp_buckets ?P') \<le> length (bp_buckets P) + 2"
    by (rule length_bp_lazy_insert_state_buckets_le[OF lazy])
  have entries:
    "length (bp_entries P) \<le> length (bp_entries ?P')"
    by (rule length_bp_lazy_insert_state_entries_ge[OF lazy])
  have divs:
    "Suc (length (bp_entries P) div ?M) \<le>
      Suc (length (bp_entries ?P') div ?M)"
    using entries by (simp add: div_le_mono)
  have slack:
    "length (bp_buckets ?P') -
        Suc (length (bp_entries ?P') div ?M) \<le>
      (length (bp_buckets P) -
        Suc (length (bp_entries P) div ?M)) + 2"
    by (rule nat_diff_le_diff_add[OF buckets divs])
  show ?thesis
    using slack unfolding bp_bucket_count_slack_def block by simp
qed

lemma bp_lazy_insert_state_split_potential_credit:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "bp_lazy_insert_charge x b P +
      bp_split_potential (bp_lazy_insert_state x b P) \<le>
    7 + bp_split_potential P"
proof -
  have overflow:
    "bp_lazy_insert_charge x b P +
        4 * bp_overflow_potential (bp_lazy_insert_state x b P) \<le>
      5 + 4 * bp_overflow_potential P"
    by (rule bp_lazy_insert_state_weighted_overflow_credit[OF lazy])
  have slack:
    "bp_bucket_count_slack (bp_lazy_insert_state x b P) \<le>
      bp_bucket_count_slack P + 2"
    by (rule bp_lazy_insert_state_bucket_count_slack_le[OF lazy])
  show ?thesis
    using overflow slack unfolding bp_split_potential_def by linarith
qed

text \<open>
  The lazy Insert credit proof is the core amortized argument.  A local insert
  either adds an entry to a bucket below the lazy threshold or splits the bucket
  into strict chunks.  The weighted overflow lemma pays for the expensive case:
  any actual lazy-insert charge plus four times the post-state overflow is at
  most a constant plus four times the pre-state overflow.  The bucket-count
  slack can increase by only a small constant.  Combining those facts yields
  @{thm bp_lazy_insert_state_split_potential_credit}, which is the precise
  credit inequality used by the costed Insert operation.
\<close>

lemma c_bp_rebucket_build_result [simp]:
  "bp_result_of (c_bp_rebucket_build P) = bp_rebucket P"
proof -
  obtain bs c where build:
    "c_bp_bucketize_entries (bp_block_size P) (bp_entries P) = (bs, c)"
    by (cases "c_bp_bucketize_entries (bp_block_size P) (bp_entries P)")
      simp
  have bs:
    "bs = bp_bucketize_entries (bp_block_size P) (bp_entries P)"
    using c_bp_bucketize_entries_result[of "bp_block_size P" "bp_entries P"]
      build
    by (simp add: bp_result_of_def)
  show ?thesis
    using build bs unfolding bp_result_of_def c_bp_rebucket_build_def
      bp_rebucket_def
    by simp
qed

lemma c_bp_rebucket_build_steps_le:
  assumes inv: "bp_invariant P"
  shows "bp_steps_of (c_bp_rebucket_build P) \<le>
    length (bp_entries P) +
      Suc (length (bp_entries P) div bp_block_size P)"
proof -
  have M_pos: "0 < bp_block_size P"
    using inv unfolding bp_invariant_def by blast
  have steps:
    "bp_steps_of
      (c_bp_bucketize_entries (bp_block_size P) (bp_entries P)) \<le>
      length (bp_entries P) +
        Suc (length (bp_entries P) div bp_block_size P)"
    by (rule c_bp_bucketize_entries_steps_le[OF M_pos])
  show ?thesis
    using steps unfolding bp_steps_of_def c_bp_rebucket_build_def
    by (auto split: prod.splits)
qed

lemma bp_bucket_overflow_zero:
  assumes "length (bp_bucket_entries b) \<le> M"
  shows "bp_bucket_overflow M b = 0"
  using assms unfolding bp_bucket_overflow_def by simp

lemma bp_overflow_potential_zero_if_sizes_ok:
  assumes "bp_bucket_sizes_ok P"
  shows "bp_overflow_potential P = 0"
proof -
  have "\<forall>b\<in>set (bp_buckets P). bp_bucket_overflow (bp_block_size P) b = 0"
    using assms
    unfolding bp_bucket_sizes_ok_def
    by (simp add: bp_bucket_overflow_zero)
  then show ?thesis
    unfolding bp_overflow_potential_def by (induction "bp_buckets P") auto
qed

lemma bp_invariant_overflow_potential_zero:
  assumes "bp_invariant P"
  shows "bp_overflow_potential P = 0"
  by (rule bp_overflow_potential_zero_if_sizes_ok)
    (use assms in \<open>simp add: bp_invariant_def\<close>)

lemma bp_bucket_count_slack_zero_if_ratio_ok:
  assumes "bp_bucket_count_ratio_ok P"
  shows "bp_bucket_count_slack P = 0"
  using assms unfolding bp_bucket_count_ratio_ok_def
    bp_bucket_count_slack_def by simp

lemma bp_split_potential_zero_if_regular:
  assumes inv: "bp_invariant P"
    and ratio: "bp_bucket_count_ratio_ok P"
  shows "bp_split_potential P = 0"
  using bp_invariant_overflow_potential_zero[OF inv]
    bp_bucket_count_slack_zero_if_ratio_ok[OF ratio]
  unfolding bp_split_potential_def by simp

lemma bp_bucket_search_steps_ratio_bound:
  assumes ratio: "bp_bucket_count_ratio_ok P"
  shows "bp_bucket_search_steps P \<le>
    bp_ratio_log_budget (length (bp_entries P)) (bp_block_size P)"
proof -
  have count_le:
    "length (bp_buckets P) \<le>
      Suc (length (bp_entries P) div bp_block_size P)"
    using ratio unfolding bp_bucket_count_ratio_ok_def by blast
  have "floor_log (length (bp_buckets P)) \<le>
      floor_log (Suc (length (bp_entries P) div bp_block_size P))"
    by (rule floor_log_le_iff[OF count_le])
  then show ?thesis
    unfolding bp_bucket_search_steps_def bp_ratio_log_budget_def by simp
qed

lemma bp_bucket_count_ratio_okI_loaded:
  assumes M_pos: "0 < bp_block_size P"
    and loaded: "bp_bucket_count_loaded P"
  shows "bp_bucket_count_ratio_ok P"
proof -
  let ?M = "bp_block_size P"
  let ?k = "length (bp_buckets P)"
  let ?N = "length (bp_entries P)"
  have count_le: "?k \<le> Suc (?N div ?M)"
  proof (cases ?k)
    case 0
    then show ?thesis by simp
  next
    case (Suc j)
    have "?M * j \<le> ?N"
      using loaded Suc unfolding bp_bucket_count_loaded_def by simp
    then have "j \<le> ?N div ?M"
    proof -
      have "j = (?M * j) div ?M"
        using M_pos by simp
      also have "\<dots> \<le> ?N div ?M"
        by (rule div_le_mono) (rule \<open>?M * j \<le> ?N\<close>)
      finally show ?thesis .
    qed
    then show ?thesis
      using Suc by simp
  qed
  show ?thesis
    unfolding bp_bucket_count_ratio_ok_def using M_pos count_le by blast
qed

lemma bp_empty_bucket_count_ratio_ok:
  assumes "0 < M"
  shows "bp_bucket_count_ratio_ok (bp_empty M B)"
  using assms unfolding bp_bucket_count_ratio_ok_def bp_empty_def
    bp_entries_def bp_bucket_entries_flat_def by simp

lemma bp_regular_invariant_ordered_invariant:
  assumes "bp_regular_invariant P"
  shows "bp_ordered_invariant P"
  using assms unfolding bp_regular_invariant_def by blast

lemma bp_regular_invariant_ratio_ok:
  assumes "bp_regular_invariant P"
  shows "bp_bucket_count_ratio_ok P"
  using assms unfolding bp_regular_invariant_def by blast

lemma bp_empty_regular_invariant:
  assumes "0 < M"
  shows "bp_regular_invariant (bp_empty M B)"
  unfolding bp_regular_invariant_def
  using bp_empty_ordered_invariant[OF assms]
    bp_empty_bucket_count_ratio_ok[OF assms]
  by blast

lemma bp_rebucket_bucket_count_ratio_ok:
  assumes inv: "bp_invariant P"
  shows "bp_bucket_count_ratio_ok (bp_rebucket P)"
proof -
  let ?M = "bp_block_size P"
  let ?xs = "bp_entries P"
  have M_pos: "0 < ?M"
    using inv unfolding bp_invariant_def by blast
  have count:
    "length (bp_bucketize_entries ?M ?xs) \<le>
      Suc (length ?xs div ?M)"
    by (rule length_bp_bucketize_entries_le_ratio[OF M_pos])
  have entries_len:
    "length (bp_entries (bp_rebucket P)) = length ?xs"
    using bp_bucket_entries_flat_bucketize_entries[OF M_pos, of ?xs]
    unfolding bp_rebucket_def bp_entries_def by simp
  have block_eq [simp]: "bp_block_size (bp_rebucket P) = ?M"
    unfolding bp_rebucket_def by simp
  have buckets_eq [simp]:
    "bp_buckets (bp_rebucket P) = bp_bucketize_entries ?M ?xs"
    unfolding bp_rebucket_def by simp
  show ?thesis
    unfolding bp_bucket_count_ratio_ok_def
    using M_pos count entries_len by simp
qed

lemma bp_rebucket_bucket_count_ratio_ok_from_lazy:
  assumes inv: "bp_lazy_invariant P"
  shows "bp_bucket_count_ratio_ok (bp_rebucket P)"
proof -
  let ?M = "bp_block_size P"
  let ?xs = "bp_entries P"
  have M_pos: "0 < ?M"
    using inv unfolding bp_lazy_invariant_def by blast
  have count:
    "length (bp_bucketize_entries ?M ?xs) \<le>
      Suc (length ?xs div ?M)"
    by (rule length_bp_bucketize_entries_le_ratio[OF M_pos])
  have entries_len:
    "length (bp_entries (bp_rebucket P)) = length ?xs"
    using bp_bucket_entries_flat_bucketize_entries[OF M_pos, of ?xs]
    unfolding bp_rebucket_def bp_entries_def by simp
  have block_eq [simp]: "bp_block_size (bp_rebucket P) = ?M"
    unfolding bp_rebucket_def by simp
  have buckets_eq [simp]:
    "bp_buckets (bp_rebucket P) = bp_bucketize_entries ?M ?xs"
    unfolding bp_rebucket_def by simp
  show ?thesis
    unfolding bp_bucket_count_ratio_ok_def
    using M_pos count entries_len by simp
qed

lemma bp_rebucket_regular_split_potential_zero:
  assumes inv: "bp_invariant P"
  shows "bp_split_potential (bp_rebucket P) = 0"
proof (rule bp_split_potential_zero_if_regular)
  show "bp_invariant (bp_rebucket P)"
    by (rule bp_rebucket_invariant[OF inv])
  show "bp_bucket_count_ratio_ok (bp_rebucket P)"
    by (rule bp_rebucket_bucket_count_ratio_ok[OF inv])
qed

lemma bp_rebucket_regular_invariant:
  assumes inv: "bp_invariant P"
  shows "bp_regular_invariant (bp_rebucket P)"
  unfolding bp_regular_invariant_def
  using bp_rebucket_ordered_invariant[OF inv]
    bp_rebucket_bucket_count_ratio_ok[OF inv]
  by blast

lemma bp_rebucket_regular_split_potential_zero_from_lazy:
  assumes inv: "bp_lazy_invariant P"
  shows "bp_split_potential (bp_rebucket P) = 0"
proof (rule bp_split_potential_zero_if_regular)
  show "bp_invariant (bp_rebucket P)"
    by (rule bp_rebucket_invariant_from_lazy[OF inv])
  show "bp_bucket_count_ratio_ok (bp_rebucket P)"
    by (rule bp_rebucket_bucket_count_ratio_ok_from_lazy[OF inv])
qed

lemma bp_rebucket_regular_invariant_from_lazy:
  assumes inv: "bp_lazy_invariant P"
  shows "bp_regular_invariant (bp_rebucket P)"
  unfolding bp_regular_invariant_def
  using bp_rebucket_ordered_invariant_from_lazy[OF inv]
    bp_rebucket_bucket_count_ratio_ok_from_lazy[OF inv]
  by blast

lemma c_bp_rebucket_build_steps_le_from_lazy:
  assumes inv: "bp_lazy_invariant P"
  shows "bp_steps_of (c_bp_rebucket_build P) \<le>
    length (bp_entries P) +
      Suc (length (bp_entries P) div bp_block_size P)"
proof -
  have M_pos: "0 < bp_block_size P"
    using inv unfolding bp_lazy_invariant_def by blast
  have steps:
    "bp_steps_of
      (c_bp_bucketize_entries (bp_block_size P) (bp_entries P)) \<le>
      length (bp_entries P) +
        Suc (length (bp_entries P) div bp_block_size P)"
    by (rule c_bp_bucketize_entries_steps_le[OF M_pos])
  show ?thesis
    using steps unfolding bp_steps_of_def c_bp_rebucket_build_def
    by (auto split: prod.splits)
qed

lemma c_bp_rebucket_build_regular_invariant_from_lazy:
  assumes inv: "bp_lazy_invariant P"
  shows "bp_regular_invariant (bp_result_of (c_bp_rebucket_build P))"
  by (simp add: bp_rebucket_regular_invariant_from_lazy[OF inv])

lemma c_bp_rebucket_build_split_potential_zero_from_lazy:
  assumes inv: "bp_lazy_invariant P"
  shows "bp_split_potential (bp_result_of (c_bp_rebucket_build P)) = 0"
  by (simp add: bp_rebucket_regular_split_potential_zero_from_lazy[OF inv])

lemma c_bp_rebucket_build_regular_invariant:
  assumes inv: "bp_invariant P"
  shows "bp_regular_invariant (bp_result_of (c_bp_rebucket_build P))"
  by (simp add: bp_rebucket_regular_invariant[OF inv])

lemma c_bp_rebucket_build_split_potential_zero:
  assumes inv: "bp_invariant P"
  shows "bp_split_potential (bp_result_of (c_bp_rebucket_build P)) = 0"
  by (simp add: bp_rebucket_regular_split_potential_zero[OF inv])

lemma bp_rebucketed_insert_regular_invariant:
  assumes inv: "bp_invariant P"
  shows "bp_regular_invariant (bp_rebucketed_insert x b P)"
  unfolding bp_rebucketed_insert_def
  by (rule bp_rebucket_regular_invariant[OF bp_insert_invariant[OF inv]])

lemma bp_rebucketed_batch_prepend_regular_invariant:
  assumes inv: "bp_invariant P"
  shows "bp_regular_invariant (bp_rebucketed_batch_prepend xs P)"
  unfolding bp_rebucketed_batch_prepend_def
  by (rule bp_rebucket_regular_invariant[OF bp_batch_prepend_invariant[OF inv]])

lemma bp_rebucketed_insert_split_potential_zero:
  assumes inv: "bp_invariant P"
  shows "bp_split_potential (bp_rebucketed_insert x b P) = 0"
  unfolding bp_rebucketed_insert_def
  by (rule bp_rebucket_regular_split_potential_zero
      [OF bp_insert_invariant[OF inv]])

lemma bp_rebucketed_batch_prepend_split_potential_zero:
  assumes inv: "bp_invariant P"
  shows "bp_split_potential (bp_rebucketed_batch_prepend xs P) = 0"
  unfolding bp_rebucketed_batch_prepend_def
  by (rule bp_rebucket_regular_split_potential_zero
      [OF bp_batch_prepend_invariant[OF inv]])

lemma bp_regularized_local_insert_invariant:
  assumes ord: "bp_ordered_invariant P"
  shows "bp_invariant (bp_regularized_local_insert x b P)"
  unfolding bp_regularized_local_insert_def
  by (rule bp_rebucket_invariant[OF bp_local_insert_state_invariant[OF ord]])

lemma bp_regularized_local_insert_ordered_invariant:
  assumes ord: "bp_ordered_invariant P"
  shows "bp_ordered_invariant (bp_regularized_local_insert x b P)"
  unfolding bp_regularized_local_insert_def
  by (rule bp_rebucket_ordered_invariant
      [OF bp_local_insert_state_invariant[OF ord]])

lemma bp_regularized_local_insert_regular_invariant:
  assumes ord: "bp_ordered_invariant P"
  shows "bp_regular_invariant (bp_regularized_local_insert x b P)"
  unfolding bp_regularized_local_insert_def
  by (rule bp_rebucket_regular_invariant
      [OF bp_local_insert_state_invariant[OF ord]])

lemma bp_regularized_local_insert_refines_min_update:
  assumes ord: "bp_ordered_invariant P"
  shows "bp_view (bp_regularized_local_insert x b P) =
    min_update (bp_view P) x b"
proof -
  have inv: "bp_invariant P"
    by (rule bp_ordered_invariant_invariant[OF ord])
  then have M_pos: "0 < bp_block_size P"
    unfolding bp_invariant_def by blast
  have step_inv: "bp_invariant (bp_local_insert_state x b P)"
    by (rule bp_local_insert_state_invariant[OF ord])
  then have step_M_pos:
    "0 < bp_block_size (bp_local_insert_state x b P)"
    unfolding bp_invariant_def by blast
  have view_rebucket:
    "bp_view (bp_rebucket (bp_local_insert_state x b P)) =
      bp_view (bp_local_insert_state x b P)"
    by (rule bp_rebucket_view[OF step_M_pos])
  show ?thesis
    unfolding bp_regularized_local_insert_def
    using view_rebucket bp_local_insert_state_refines_min_update[OF M_pos, of x b]
    by simp
qed

lemma bp_regularized_local_insert_refines_insert_spec:
  assumes ord: "bp_ordered_invariant P"
  shows "insert_spec (bp_view P) x b
    (bp_view (bp_regularized_local_insert x b P))"
  unfolding bp_regularized_local_insert_refines_min_update[OF ord]
  by (rule min_update_insert_spec)

lemma bp_regularized_local_insert_split_potential_zero:
  assumes ord: "bp_ordered_invariant P"
  shows "bp_split_potential (bp_regularized_local_insert x b P) = 0"
  unfolding bp_regularized_local_insert_def
  by (rule bp_rebucket_regular_split_potential_zero
      [OF bp_local_insert_state_invariant[OF ord]])

lemma bp_local_insert_search_charge_ratio_bound:
  assumes ratio: "bp_bucket_count_ratio_ok P"
  shows "bp_local_insert_search_charge P \<le>
    bp_insert_search_budget (length (bp_entries P)) (bp_block_size P)"
  using bp_bucket_search_steps_ratio_bound[OF ratio]
  unfolding bp_local_insert_search_charge_def bp_insert_search_budget_def
  by simp

lemma c_bp_local_insert_search_result [simp]:
  "bp_result_of (c_bp_local_insert_search x b P) =
    bp_local_insert_state x b P"
  unfolding bp_result_of_def c_bp_local_insert_search_def by simp

lemma c_bp_local_insert_search_steps [simp]:
  "bp_steps_of (c_bp_local_insert_search x b P) =
    bp_local_insert_search_charge P"
  unfolding bp_steps_of_def c_bp_local_insert_search_def by simp

lemma c_bp_local_insert_search_refines_min_update:
  assumes "0 < bp_block_size P"
  shows "bp_view (bp_result_of (c_bp_local_insert_search x b P)) =
    min_update (bp_view P) x b"
  unfolding c_bp_local_insert_search_result
  by (rule bp_local_insert_state_refines_min_update[OF assms])

lemma c_bp_local_insert_search_invariant:
  assumes "bp_ordered_invariant P"
  shows "bp_invariant (bp_result_of (c_bp_local_insert_search x b P))"
  unfolding c_bp_local_insert_search_result
  by (rule bp_local_insert_state_invariant[OF assms])

lemma c_bp_local_insert_search_ordered_invariant:
  assumes "bp_ordered_invariant P"
  shows "bp_ordered_invariant
    (bp_result_of (c_bp_local_insert_search x b P))"
  unfolding c_bp_local_insert_search_result
  by (rule bp_local_insert_state_ordered_invariant[OF assms])

lemma c_bp_local_insert_search_refines_insert_spec:
  assumes "0 < bp_block_size P"
  shows "insert_spec (bp_view P) x b
    (bp_view (bp_result_of (c_bp_local_insert_search x b P)))"
  unfolding c_bp_local_insert_search_refines_min_update[OF assms]
  by (rule min_update_insert_spec)

lemma c_bp_local_insert_search_ratio_bound:
  assumes ratio: "bp_bucket_count_ratio_ok P"
  shows "bp_steps_of (c_bp_local_insert_search x b P) \<le>
    bp_insert_search_budget (length (bp_entries P)) (bp_block_size P)"
  by (simp add: bp_local_insert_search_charge_ratio_bound[OF ratio])

lemma c_bp_local_insert_search_partition_insert_cost_bound:
  assumes ratio: "bp_bucket_count_ratio_ok P"
  shows "partition_insert_cost_bound
    (bp_steps_of (c_bp_local_insert_search x b P))
    (bp_insert_search_budget (length (bp_entries P)) (bp_block_size P))"
  using c_bp_local_insert_search_ratio_bound[OF ratio]
  unfolding partition_insert_cost_bound_def .

lemma c_bp_local_insert_split_result [simp]:
  "bp_result_of (c_bp_local_insert_split x b P) =
    bp_local_insert_state x b P"
  unfolding bp_result_of_def c_bp_local_insert_split_def by simp

lemma c_bp_local_insert_split_steps [simp]:
  "bp_steps_of (c_bp_local_insert_split x b P) =
    bp_local_insert_search_charge P +
      bp_local_split_budget (bp_block_size P)"
  unfolding bp_steps_of_def c_bp_local_insert_split_def by simp

lemma c_bp_local_insert_split_refines_min_update:
  assumes "0 < bp_block_size P"
  shows "bp_view (bp_result_of (c_bp_local_insert_split x b P)) =
    min_update (bp_view P) x b"
  unfolding c_bp_local_insert_split_result
  by (rule bp_local_insert_state_refines_min_update[OF assms])

lemma c_bp_local_insert_split_invariant:
  assumes "bp_ordered_invariant P"
  shows "bp_invariant (bp_result_of (c_bp_local_insert_split x b P))"
  unfolding c_bp_local_insert_split_result
  by (rule bp_local_insert_state_invariant[OF assms])

lemma c_bp_local_insert_split_ordered_invariant:
  assumes "bp_ordered_invariant P"
  shows "bp_ordered_invariant
    (bp_result_of (c_bp_local_insert_split x b P))"
  unfolding c_bp_local_insert_split_result
  by (rule bp_local_insert_state_ordered_invariant[OF assms])

lemma c_bp_local_insert_split_refines_insert_spec:
  assumes "0 < bp_block_size P"
  shows "insert_spec (bp_view P) x b
    (bp_view (bp_result_of (c_bp_local_insert_split x b P)))"
  unfolding c_bp_local_insert_split_refines_min_update[OF assms]
  by (rule min_update_insert_spec)

lemma c_bp_local_insert_split_steps_le:
  assumes ratio: "bp_bucket_count_ratio_ok P"
  shows "bp_steps_of (c_bp_local_insert_split x b P) \<le>
    bp_insert_search_budget (length (bp_entries P)) (bp_block_size P) +
      bp_local_split_budget (bp_block_size P)"
  using bp_local_insert_search_charge_ratio_bound[OF ratio]
  by simp

lemma c_bp_local_insert_split_steps_le_lazy_budget:
  assumes ratio: "bp_bucket_count_ratio_ok P"
  shows "bp_steps_of (c_bp_local_insert_split x b P) \<le>
    bp_insert_search_budget (length (bp_entries P)) (bp_block_size P) +
      bp_lazy_split_budget (bp_block_size P)"
proof -
  have local:
    "bp_steps_of (c_bp_local_insert_split x b P) \<le>
      bp_insert_search_budget (length (bp_entries P)) (bp_block_size P) +
        bp_local_split_budget (bp_block_size P)"
    by (rule c_bp_local_insert_split_steps_le[OF ratio])
  have "bp_local_split_budget (bp_block_size P) \<le>
      bp_lazy_split_budget (bp_block_size P)"
    by (rule bp_local_split_budget_le_lazy_split_budget)
  then show ?thesis
    using local by linarith
qed

lemma c_bp_local_insert_split_amortized_if_split_credit:
  assumes ratio: "bp_bucket_count_ratio_ok P"
    and paid:
      "bp_local_split_budget (bp_block_size P) +
        bp_split_potential
          (bp_result_of (c_bp_local_insert_split x b P)) \<le>
        bp_split_potential P"
  shows "bp_amortized_step_bound
    (bp_steps_of (c_bp_local_insert_split x b P)) P
    (bp_result_of (c_bp_local_insert_split x b P))
    (bp_insert_search_budget (length (bp_entries P)) (bp_block_size P))"
proof -
  have search:
    "bp_local_insert_search_charge P \<le>
      bp_insert_search_budget (length (bp_entries P)) (bp_block_size P)"
    by (rule bp_local_insert_search_charge_ratio_bound[OF ratio])
  have steps:
    "bp_steps_of (c_bp_local_insert_split x b P) =
      bp_local_insert_search_charge P +
        bp_local_split_budget (bp_block_size P)"
    by simp
  show ?thesis
    using search paid steps
    unfolding bp_amortized_step_bound_def
    by linarith
qed

lemma c_bp_lazy_insert_result [simp]:
  "bp_result_of (c_bp_lazy_insert x b P) =
    bp_lazy_insert_state x b P"
  unfolding bp_result_of_def c_bp_lazy_insert_def by simp

lemma c_bp_lazy_insert_steps [simp]:
  "bp_steps_of (c_bp_lazy_insert x b P) =
    bp_local_insert_search_charge P +
      bp_lazy_split_budget (bp_block_size P)"
  unfolding bp_steps_of_def c_bp_lazy_insert_def by simp

lemma c_bp_lazy_insert_refines_min_update:
  assumes "0 < bp_block_size P"
  shows "bp_view (bp_result_of (c_bp_lazy_insert x b P)) =
    min_update (bp_view P) x b"
  unfolding c_bp_lazy_insert_result
  by (rule bp_lazy_insert_state_refines_min_update[OF assms])

lemma c_bp_lazy_insert_lazy_ordered_invariant:
  assumes "bp_lazy_ordered_invariant P"
  shows "bp_lazy_ordered_invariant
    (bp_result_of (c_bp_lazy_insert x b P))"
  unfolding c_bp_lazy_insert_result
  by (rule bp_lazy_insert_state_lazy_ordered_invariant[OF assms])

lemma c_bp_lazy_insert_refines_insert_spec:
  assumes "0 < bp_block_size P"
  shows "insert_spec (bp_view P) x b
    (bp_view (bp_result_of (c_bp_lazy_insert x b P)))"
  unfolding c_bp_lazy_insert_refines_min_update[OF assms]
  by (rule min_update_insert_spec)

lemma c_bp_lazy_insert_steps_le_lazy_budget:
  assumes ratio: "bp_bucket_count_ratio_ok P"
  shows "bp_steps_of (c_bp_lazy_insert x b P) \<le>
    bp_insert_search_budget (length (bp_entries P)) (bp_block_size P) +
      bp_lazy_split_budget (bp_block_size P)"
  using bp_local_insert_search_charge_ratio_bound[OF ratio]
  by simp

lemma c_bp_lazy_insert_amortized_if_split_credit:
  assumes ratio: "bp_bucket_count_ratio_ok P"
    and paid:
      "bp_lazy_split_budget (bp_block_size P) +
        bp_split_potential (bp_result_of (c_bp_lazy_insert x b P)) \<le>
        bp_split_potential P"
  shows "bp_amortized_step_bound
    (bp_steps_of (c_bp_lazy_insert x b P)) P
    (bp_result_of (c_bp_lazy_insert x b P))
    (bp_insert_search_budget (length (bp_entries P)) (bp_block_size P))"
proof -
  have search:
    "bp_local_insert_search_charge P \<le>
      bp_insert_search_budget (length (bp_entries P)) (bp_block_size P)"
    by (rule bp_local_insert_search_charge_ratio_bound[OF ratio])
  have steps:
    "bp_steps_of (c_bp_lazy_insert x b P) =
      bp_local_insert_search_charge P +
        bp_lazy_split_budget (bp_block_size P)"
    by simp
  show ?thesis
    using search paid steps
    unfolding bp_amortized_step_bound_def
    by linarith
qed

lemma bp_lazy_bucket_insert_charge_le:
  "bp_lazy_bucket_insert_charge M b \<le> bp_lazy_split_budget M"
  unfolding bp_lazy_bucket_insert_charge_def bp_lazy_split_budget_def
  by simp

lemma bp_lazy_insert_bucket_charge_le:
  "bp_lazy_insert_bucket_charge M p bs \<le> bp_lazy_split_budget M"
proof (induction bs arbitrary: p)
  case Nil
  then show ?case
    unfolding bp_lazy_split_budget_def by simp
next
  case (Cons b bs)
  note IH = Cons.IH
  show ?case
  proof (cases bs)
    case Nil
    then show ?thesis
      using bp_lazy_bucket_insert_charge_le[of M b]
      unfolding bp_lazy_split_budget_def by auto
  next
    case (Cons c cs)
    have one_le: "1 \<le> bp_lazy_split_budget M"
      unfolding bp_lazy_split_budget_def by simp
    then show ?thesis
      using Cons IH[of p] bp_lazy_bucket_insert_charge_le[of M b] one_le
      by auto
  qed
qed

lemma bp_lazy_insert_charge_le:
  "bp_lazy_insert_charge x b P \<le> bp_lazy_split_budget (bp_block_size P)"
proof -
  let ?old_keys = "bp_entry_keys (bp_entries P)"
  let ?b = "if x \<in> ?old_keys then min (bp_values P x) b else b"
  let ?P0 = "bp_delete_key x P"
  have charge:
    "bp_lazy_insert_bucket_charge (bp_block_size ?P0) (x, ?b)
      (bp_buckets ?P0) \<le> bp_lazy_split_budget (bp_block_size ?P0)"
    by (rule bp_lazy_insert_bucket_charge_le)
  have block: "bp_block_size ?P0 = bp_block_size P"
    unfolding bp_delete_key_def by simp
  show ?thesis
    using charge unfolding bp_lazy_insert_charge_def Let_def block by simp
qed

lemma c_bp_lazy_insert_precise_result [simp]:
  "bp_result_of (c_bp_lazy_insert_precise x b P) =
    bp_lazy_insert_state x b P"
  unfolding bp_result_of_def c_bp_lazy_insert_precise_def by simp

lemma c_bp_lazy_insert_precise_steps [simp]:
  "bp_steps_of (c_bp_lazy_insert_precise x b P) =
    bp_local_insert_search_charge P + bp_lazy_insert_charge x b P"
  unfolding bp_steps_of_def c_bp_lazy_insert_precise_def by simp

lemma c_bp_lazy_insert_precise_refines_min_update:
  assumes "0 < bp_block_size P"
  shows "bp_view (bp_result_of (c_bp_lazy_insert_precise x b P)) =
    min_update (bp_view P) x b"
  unfolding c_bp_lazy_insert_precise_result
  by (rule bp_lazy_insert_state_refines_min_update[OF assms])

lemma c_bp_lazy_insert_precise_lazy_ordered_invariant:
  assumes "bp_lazy_ordered_invariant P"
  shows "bp_lazy_ordered_invariant
    (bp_result_of (c_bp_lazy_insert_precise x b P))"
  unfolding c_bp_lazy_insert_precise_result
  by (rule bp_lazy_insert_state_lazy_ordered_invariant[OF assms])

lemma c_bp_lazy_insert_precise_refines_insert_spec:
  assumes "0 < bp_block_size P"
  shows "insert_spec (bp_view P) x b
    (bp_view (bp_result_of (c_bp_lazy_insert_precise x b P)))"
  unfolding c_bp_lazy_insert_precise_refines_min_update[OF assms]
  by (rule min_update_insert_spec)

lemma c_bp_lazy_insert_precise_steps_le_lazy_budget:
  assumes ratio: "bp_bucket_count_ratio_ok P"
  shows "bp_steps_of (c_bp_lazy_insert_precise x b P) \<le>
    bp_insert_search_budget (length (bp_entries P)) (bp_block_size P) +
      bp_lazy_split_budget (bp_block_size P)"
proof -
  have search:
    "bp_local_insert_search_charge P \<le>
      bp_insert_search_budget (length (bp_entries P)) (bp_block_size P)"
    by (rule bp_local_insert_search_charge_ratio_bound[OF ratio])
  have charge:
    "bp_lazy_insert_charge x b P \<le>
      bp_lazy_split_budget (bp_block_size P)"
    by (rule bp_lazy_insert_charge_le)
  show ?thesis
    using search charge by simp
qed

lemma c_bp_lazy_insert_precise_steps_le_coarse:
  "bp_steps_of (c_bp_lazy_insert_precise x b P) \<le>
    bp_steps_of (c_bp_lazy_insert x b P)"
  using bp_lazy_insert_charge_le[of x b P] by simp

lemma c_bp_lazy_insert_precise_amortized_if_credit:
  assumes ratio: "bp_bucket_count_ratio_ok P"
    and paid:
      "bp_lazy_insert_charge x b P +
        bp_split_potential
          (bp_result_of (c_bp_lazy_insert_precise x b P)) \<le>
        extra + bp_split_potential P"
  shows "bp_amortized_step_bound
    (bp_steps_of (c_bp_lazy_insert_precise x b P)) P
    (bp_result_of (c_bp_lazy_insert_precise x b P))
    (bp_insert_search_budget (length (bp_entries P)) (bp_block_size P) +
      extra)"
proof -
  have search:
    "bp_local_insert_search_charge P \<le>
      bp_insert_search_budget (length (bp_entries P)) (bp_block_size P)"
    by (rule bp_local_insert_search_charge_ratio_bound[OF ratio])
  show ?thesis
    using search paid
    unfolding bp_amortized_step_bound_def
    by simp
qed

lemma c_bp_lazy_insert_precise_amortized_bound:
  assumes lazy: "bp_lazy_ordered_invariant P"
    and ratio: "bp_bucket_count_ratio_ok P"
  shows "bp_amortized_step_bound
    (bp_steps_of (c_bp_lazy_insert_precise x b P)) P
    (bp_result_of (c_bp_lazy_insert_precise x b P))
    (bp_insert_search_budget (length (bp_entries P)) (bp_block_size P) + 7)"
proof (rule c_bp_lazy_insert_precise_amortized_if_credit[OF ratio])
  show "bp_lazy_insert_charge x b P +
    bp_split_potential (bp_result_of (c_bp_lazy_insert_precise x b P)) \<le>
    7 + bp_split_potential P"
    using bp_lazy_insert_state_split_potential_credit[OF lazy, of x b]
    by simp
qed

lemma c_bp_lazy_insert_precise_amortized_ratio_budget:
  assumes lazy: "bp_lazy_ordered_invariant P"
    and ratio: "bp_bucket_count_ratio_ok P"
  shows "bp_amortized_step_bound
    (bp_steps_of (c_bp_lazy_insert_precise x b P)) P
    (bp_result_of (c_bp_lazy_insert_precise x b P))
    (bp_lazy_insert_amortized_budget P)"
  unfolding bp_lazy_insert_amortized_budget_def
  by (rule c_bp_lazy_insert_precise_amortized_bound[OF lazy ratio])

lemma c_bp_lazy_insert_precise_regular_ratio_bound:
  assumes reg: "bp_regular_invariant P"
  shows "bp_steps_of (c_bp_lazy_insert_precise x b P) \<le>
    bp_lazy_insert_amortized_budget P"
proof -
  have ord: "bp_ordered_invariant P"
    by (rule bp_regular_invariant_ordered_invariant[OF reg])
  have lazy: "bp_lazy_ordered_invariant P"
    by (rule bp_ordered_invariant_lazy_ordered_invariant[OF ord])
  have ratio: "bp_bucket_count_ratio_ok P"
    by (rule bp_regular_invariant_ratio_ok[OF reg])
  have am: "bp_amortized_step_bound
      (bp_steps_of (c_bp_lazy_insert_precise x b P)) P
      (bp_result_of (c_bp_lazy_insert_precise x b P))
      (bp_lazy_insert_amortized_budget P)"
    by (rule c_bp_lazy_insert_precise_amortized_ratio_budget[OF lazy ratio])
  have pot: "bp_split_potential P = 0"
    by (rule bp_split_potential_zero_if_regular
        [OF bp_ordered_invariant_invariant[OF ord] ratio])
  show ?thesis
    using am pot unfolding bp_amortized_step_bound_def by linarith
qed

lemma c_bp_lazy_insert_precise_regular_partition_insert_cost_bound:
  assumes reg: "bp_regular_invariant P"
  shows "partition_insert_cost_bound
    (bp_steps_of (c_bp_lazy_insert_precise x b P))
    (bp_lazy_insert_amortized_budget P)"
  using c_bp_lazy_insert_precise_regular_ratio_bound[OF reg]
  unfolding partition_insert_cost_bound_def .

lemma c_bp_lazy_batch_prepend_precise_result [simp]:
  "bp_result_of (c_bp_lazy_batch_prepend_precise xs P) =
    bp_lazy_batch_prepend_state xs P"
proof (induction xs arbitrary: P)
  case Nil
  then show ?case by simp
next
  case (Cons xb xs)
  obtain x b where xb: "xb = (x, b)"
    by force
  show ?case
    unfolding xb by (simp add: Cons.IH)
qed

lemma c_bp_lazy_batch_prepend_precise_steps_Nil [simp]:
  "bp_steps_of (c_bp_lazy_batch_prepend_precise [] P) = 0"
  unfolding bp_steps_of_def by simp

lemma c_bp_lazy_batch_prepend_precise_steps_Cons [simp]:
  "bp_steps_of (c_bp_lazy_batch_prepend_precise ((x, b) # xs) P) =
    bp_steps_of (c_bp_lazy_insert_precise x b P) +
    bp_steps_of
      (c_bp_lazy_batch_prepend_precise xs
        (bp_result_of (c_bp_lazy_insert_precise x b P)))"
  unfolding bp_steps_of_def bp_result_of_def
  by (simp split: prod.splits)

lemma c_bp_lazy_batch_prepend_precise_lazy_ordered_invariant:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "bp_lazy_ordered_invariant
    (bp_result_of (c_bp_lazy_batch_prepend_precise xs P))"
  using lazy
proof (induction xs arbitrary: P)
  case Nil
  then show ?case by simp
next
  case (Cons xb xs)
  obtain x b where xb: "xb = (x, b)"
    by force
  have step_lazy: "bp_lazy_ordered_invariant
      (bp_result_of (c_bp_lazy_insert_precise x b P))"
    by (rule c_bp_lazy_insert_precise_lazy_ordered_invariant[OF Cons.prems])
  show ?case
    unfolding xb using Cons.IH[OF step_lazy] by simp
qed

lemma c_bp_lazy_batch_prepend_precise_refines_batch_min_update:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "bp_view (bp_result_of (c_bp_lazy_batch_prepend_precise xs P)) =
    batch_min_update (bp_view P) xs"
  using lazy
proof (induction xs arbitrary: P)
  case Nil
  then show ?case
    unfolding batch_min_update_def by simp
next
  case (Cons xb xs)
  obtain x b where xb: "xb = (x, b)"
    by force
  have M_pos: "0 < bp_block_size P"
    using Cons.prems unfolding bp_lazy_ordered_invariant_def
      bp_lazy_invariant_def by blast
  have step_view:
    "bp_view (bp_result_of (c_bp_lazy_insert_precise x b P)) =
      min_update (bp_view P) x b"
    by (rule c_bp_lazy_insert_precise_refines_min_update[OF M_pos])
  have step_lazy: "bp_lazy_ordered_invariant
      (bp_result_of (c_bp_lazy_insert_precise x b P))"
    by (rule c_bp_lazy_insert_precise_lazy_ordered_invariant[OF Cons.prems])
  show ?case
    unfolding xb
    using Cons.IH[OF step_lazy] step_view
    by (simp add: batch_min_update_def)
qed

lemma c_bp_lazy_batch_prepend_precise_amortized_bound:
  assumes lazy: "bp_lazy_ordered_invariant P"
    and ratios: "bp_lazy_batch_ratio_ok xs P"
  shows "bp_amortized_step_bound
    (bp_steps_of (c_bp_lazy_batch_prepend_precise xs P)) P
    (bp_result_of (c_bp_lazy_batch_prepend_precise xs P))
    (bp_lazy_batch_insert_budget_sum xs P)"
  using lazy ratios
proof (induction xs arbitrary: P)
  case Nil
  then show ?case
    unfolding bp_amortized_step_bound_def by simp
next
  case (Cons xb xs)
  obtain x b where xb: "xb = (x, b)"
    by force
  let ?I = "c_bp_lazy_insert_precise x b P"
  let ?P1 = "bp_result_of ?I"
  have ratio: "bp_bucket_count_ratio_ok P"
    using Cons.prems(2) unfolding xb by simp
  have tail_ratios: "bp_lazy_batch_ratio_ok xs ?P1"
    using Cons.prems(2) unfolding xb by simp
  have step_lazy: "bp_lazy_ordered_invariant ?P1"
    by (rule c_bp_lazy_insert_precise_lazy_ordered_invariant[OF Cons.prems(1)])
  have insert_bound:
    "bp_steps_of ?I + bp_split_potential ?P1 \<le>
      bp_lazy_insert_amortized_budget P + bp_split_potential P"
    using c_bp_lazy_insert_precise_amortized_ratio_budget
      [OF Cons.prems(1) ratio, of x b]
    unfolding bp_amortized_step_bound_def .
  have tail_bound:
    "bp_steps_of (c_bp_lazy_batch_prepend_precise xs ?P1) +
        bp_split_potential
          (bp_result_of (c_bp_lazy_batch_prepend_precise xs ?P1)) \<le>
      bp_lazy_batch_insert_budget_sum xs ?P1 + bp_split_potential ?P1"
    using Cons.IH[OF step_lazy tail_ratios]
    unfolding bp_amortized_step_bound_def .
  show ?case
    unfolding xb bp_amortized_step_bound_def
    using insert_bound tail_bound by simp
qed

lemma c_bp_lazy_batch_prepend_precise_regular_steps_le_budget_sum:
  assumes reg: "bp_regular_invariant P"
    and ratios: "bp_lazy_batch_ratio_ok xs P"
  shows "bp_steps_of (c_bp_lazy_batch_prepend_precise xs P) \<le>
    bp_lazy_batch_insert_budget_sum xs P"
proof -
  have ord: "bp_ordered_invariant P"
    by (rule bp_regular_invariant_ordered_invariant[OF reg])
  have lazy: "bp_lazy_ordered_invariant P"
    by (rule bp_ordered_invariant_lazy_ordered_invariant[OF ord])
  have am: "bp_amortized_step_bound
      (bp_steps_of (c_bp_lazy_batch_prepend_precise xs P)) P
      (bp_result_of (c_bp_lazy_batch_prepend_precise xs P))
      (bp_lazy_batch_insert_budget_sum xs P)"
    by (rule c_bp_lazy_batch_prepend_precise_amortized_bound[OF lazy ratios])
  have pot: "bp_split_potential P = 0"
    by (rule bp_split_potential_zero_if_regular
        [OF bp_ordered_invariant_invariant[OF ord]
          bp_regular_invariant_ratio_ok[OF reg]])
  show ?thesis
    using am pot unfolding bp_amortized_step_bound_def by linarith
qed

lemma c_bp_regularized_local_insert_result [simp]:
  "bp_result_of (c_bp_regularized_local_insert x b P) =
    bp_regularized_local_insert x b P"
  unfolding bp_result_of_def c_bp_regularized_local_insert_def by simp

lemma c_bp_regularized_local_insert_steps [simp]:
  "bp_steps_of (c_bp_regularized_local_insert x b P) =
    bp_local_insert_search_charge P"
  unfolding bp_steps_of_def c_bp_regularized_local_insert_def by simp

lemma c_bp_regularized_local_insert_regular_invariant:
  assumes reg: "bp_regular_invariant P"
  shows "bp_regular_invariant
    (bp_result_of (c_bp_regularized_local_insert x b P))"
  unfolding c_bp_regularized_local_insert_result
  by (rule bp_regularized_local_insert_regular_invariant
      [OF bp_regular_invariant_ordered_invariant[OF reg]])

lemma c_bp_regularized_local_insert_refines_min_update:
  assumes reg: "bp_regular_invariant P"
  shows "bp_view (bp_result_of (c_bp_regularized_local_insert x b P)) =
    min_update (bp_view P) x b"
  unfolding c_bp_regularized_local_insert_result
  by (rule bp_regularized_local_insert_refines_min_update
      [OF bp_regular_invariant_ordered_invariant[OF reg]])

lemma c_bp_regularized_local_insert_refines_insert_spec:
  assumes reg: "bp_regular_invariant P"
  shows "insert_spec (bp_view P) x b
    (bp_view (bp_result_of (c_bp_regularized_local_insert x b P)))"
  unfolding c_bp_regularized_local_insert_refines_min_update[OF reg]
  by (rule min_update_insert_spec)

lemma c_bp_regularized_local_insert_ratio_bound:
  assumes reg: "bp_regular_invariant P"
  shows "bp_steps_of (c_bp_regularized_local_insert x b P) \<le>
    bp_insert_search_budget (length (bp_entries P)) (bp_block_size P)"
  by (simp add: bp_local_insert_search_charge_ratio_bound
      [OF bp_regular_invariant_ratio_ok[OF reg]])

lemma c_bp_regularized_local_insert_split_potential_zero:
  assumes reg: "bp_regular_invariant P"
  shows "bp_split_potential
    (bp_result_of (c_bp_regularized_local_insert x b P)) = 0"
  unfolding c_bp_regularized_local_insert_result
  by (rule bp_regularized_local_insert_split_potential_zero
      [OF bp_regular_invariant_ordered_invariant[OF reg]])

lemma bp_regular_invariant_split_potential_zero:
  assumes reg: "bp_regular_invariant P"
  shows "bp_split_potential P = 0"
proof (rule bp_split_potential_zero_if_regular)
  show "bp_invariant P"
    by (rule bp_ordered_invariant_invariant
        [OF bp_regular_invariant_ordered_invariant[OF reg]])
  show "bp_bucket_count_ratio_ok P"
    by (rule bp_regular_invariant_ratio_ok[OF reg])
qed

lemma c_bp_regularized_local_insert_amortized_ratio_bound:
  assumes reg: "bp_regular_invariant P"
  shows "bp_amortized_step_bound
    (bp_steps_of (c_bp_regularized_local_insert x b P)) P
    (bp_result_of (c_bp_regularized_local_insert x b P))
    (bp_insert_search_budget (length (bp_entries P)) (bp_block_size P))"
  using c_bp_regularized_local_insert_ratio_bound[OF reg]
    c_bp_regularized_local_insert_split_potential_zero[OF reg, of x b]
    bp_regular_invariant_split_potential_zero[OF reg]
  unfolding bp_amortized_step_bound_def by simp

lemma c_bp_regularized_local_insert_partition_insert_cost_bound:
  assumes reg: "bp_regular_invariant P"
  shows "partition_insert_cost_bound
    (bp_steps_of (c_bp_regularized_local_insert x b P))
    (bp_insert_search_budget (length (bp_entries P)) (bp_block_size P))"
  using c_bp_regularized_local_insert_ratio_bound[OF reg]
  unfolding partition_insert_cost_bound_def .

lemma c_bp_regularized_local_insert_build_result [simp]:
  "bp_result_of (c_bp_regularized_local_insert_build x b P) =
    bp_regularized_local_insert x b P"
proof -
  let ?Q = "bp_local_insert_state x b P"
  obtain P' c where build: "c_bp_rebucket_build ?Q = (P', c)"
    by (cases "c_bp_rebucket_build ?Q")
  have P': "P' = bp_rebucket ?Q"
    using c_bp_rebucket_build_result[of ?Q] build
    unfolding bp_result_of_def by simp
  show ?thesis
    using build P'
    unfolding c_bp_regularized_local_insert_build_def
      bp_regularized_local_insert_def bp_result_of_def
    by simp
qed

lemma c_bp_regularized_local_insert_build_steps:
  "bp_steps_of (c_bp_regularized_local_insert_build x b P) =
    bp_local_insert_search_charge P +
      bp_steps_of (c_bp_rebucket_build (bp_local_insert_state x b P))"
  unfolding c_bp_regularized_local_insert_build_def
  by (auto simp: bp_steps_of_def split: prod.splits)

lemma c_bp_regularized_local_insert_build_regular_invariant:
  assumes reg: "bp_regular_invariant P"
  shows "bp_regular_invariant
    (bp_result_of (c_bp_regularized_local_insert_build x b P))"
  unfolding c_bp_regularized_local_insert_build_result
  by (rule bp_regularized_local_insert_regular_invariant
      [OF bp_regular_invariant_ordered_invariant[OF reg]])

lemma c_bp_regularized_local_insert_build_refines_min_update:
  assumes reg: "bp_regular_invariant P"
  shows "bp_view (bp_result_of
      (c_bp_regularized_local_insert_build x b P)) =
    min_update (bp_view P) x b"
  unfolding c_bp_regularized_local_insert_build_result
  by (rule bp_regularized_local_insert_refines_min_update
      [OF bp_regular_invariant_ordered_invariant[OF reg]])

lemma c_bp_regularized_local_insert_build_refines_insert_spec:
  assumes reg: "bp_regular_invariant P"
  shows "insert_spec (bp_view P) x b
    (bp_view (bp_result_of
      (c_bp_regularized_local_insert_build x b P)))"
  unfolding c_bp_regularized_local_insert_build_refines_min_update[OF reg]
  by (rule min_update_insert_spec)

lemma c_bp_regularized_local_insert_build_split_potential_zero:
  assumes reg: "bp_regular_invariant P"
  shows "bp_split_potential
    (bp_result_of (c_bp_regularized_local_insert_build x b P)) = 0"
  unfolding c_bp_regularized_local_insert_build_result
  by (rule bp_regularized_local_insert_split_potential_zero
      [OF bp_regular_invariant_ordered_invariant[OF reg]])

lemma c_bp_regularized_local_insert_build_rebuild_steps_le:
  assumes ord: "bp_ordered_invariant P"
  shows "bp_steps_of (c_bp_regularized_local_insert_build x b P) \<le>
    bp_local_insert_search_charge P +
      length (bp_entries (bp_local_insert_state x b P)) +
      Suc (length (bp_entries (bp_local_insert_state x b P)) div
        bp_block_size P)"
proof -
  have step_inv: "bp_invariant (bp_local_insert_state x b P)"
    by (rule bp_local_insert_state_invariant[OF ord])
  have build:
    "bp_steps_of (c_bp_rebucket_build (bp_local_insert_state x b P)) \<le>
      length (bp_entries (bp_local_insert_state x b P)) +
      Suc (length (bp_entries (bp_local_insert_state x b P)) div
        bp_block_size (bp_local_insert_state x b P))"
    by (rule c_bp_rebucket_build_steps_le[OF step_inv])
  have block:
    "bp_block_size (bp_local_insert_state x b P) = bp_block_size P"
    unfolding bp_local_insert_state_def bp_delete_key_def
    by (simp add: Let_def split: if_splits)
  show ?thesis
    using build
    unfolding c_bp_regularized_local_insert_build_steps block
    by simp
qed

lemma c_bp_regularized_local_insert_build_steps_le:
  assumes reg: "bp_regular_invariant P"
  shows "bp_steps_of (c_bp_regularized_local_insert_build x b P) \<le>
    bp_insert_search_budget (length (bp_entries P)) (bp_block_size P) +
      length (bp_entries (bp_local_insert_state x b P)) +
      Suc (length (bp_entries (bp_local_insert_state x b P)) div
        bp_block_size P)"
proof -
  have ord: "bp_ordered_invariant P"
    by (rule bp_regular_invariant_ordered_invariant[OF reg])
  have search:
    "bp_local_insert_search_charge P \<le>
      bp_insert_search_budget (length (bp_entries P)) (bp_block_size P)"
    by (rule bp_local_insert_search_charge_ratio_bound
        [OF bp_regular_invariant_ratio_ok[OF reg]])
  have build:
    "bp_steps_of (c_bp_regularized_local_insert_build x b P) \<le>
      bp_local_insert_search_charge P +
        length (bp_entries (bp_local_insert_state x b P)) +
        Suc (length (bp_entries (bp_local_insert_state x b P)) div
          bp_block_size P)"
    by (rule c_bp_regularized_local_insert_build_rebuild_steps_le[OF ord])
  show ?thesis
    using search build by linarith
qed

lemma c_bp_regularized_local_insert_build_amortized_rebuild_bound:
  assumes reg: "bp_regular_invariant P"
  shows "bp_amortized_step_bound
    (bp_steps_of (c_bp_regularized_local_insert_build x b P)) P
    (bp_result_of (c_bp_regularized_local_insert_build x b P))
    (bp_insert_search_budget (length (bp_entries P)) (bp_block_size P) +
      length (bp_entries (bp_local_insert_state x b P)) +
      Suc (length (bp_entries (bp_local_insert_state x b P)) div
        bp_block_size P))"
  using c_bp_regularized_local_insert_build_steps_le[OF reg, of x b]
    c_bp_regularized_local_insert_build_split_potential_zero[OF reg, of x b]
    bp_regular_invariant_split_potential_zero[OF reg]
  unfolding bp_amortized_step_bound_def by simp

lemma c_bp_rebucketed_batch_prepend_bulk_result [simp]:
  "bp_result_of (c_bp_rebucketed_batch_prepend_bulk xs P) =
    bp_rebucketed_batch_prepend xs P"
  unfolding bp_result_of_def c_bp_rebucketed_batch_prepend_bulk_def by simp

lemma c_bp_rebucketed_batch_prepend_bulk_steps [simp]:
  "bp_steps_of (c_bp_rebucketed_batch_prepend_bulk xs P) =
    bp_batch_prepend_log_budget xs (bp_block_size P)"
  unfolding bp_steps_of_def c_bp_rebucketed_batch_prepend_bulk_def by simp

lemma c_bp_bucketed_batch_prepend_direct_result [simp]:
  "bp_result_of (c_bp_bucketed_batch_prepend_direct xs P) =
    bp_bucketed_batch_prepend_state xs P"
  unfolding c_bp_bucketed_batch_prepend_direct_def by simp

lemma c_bp_bucketed_batch_prepend_direct_steps [simp]:
  "bp_steps_of (c_bp_bucketed_batch_prepend_direct xs P) =
    bp_batch_prepend_amortized_budget xs (bp_block_size P)"
  unfolding c_bp_bucketed_batch_prepend_direct_def by simp

lemma c_bp_bucketed_batch_prepend_direct_actual_result [simp]:
  "bp_result_of (c_bp_bucketed_batch_prepend_direct_actual xs P) =
    bp_bucketed_batch_prepend_state xs P"
  unfolding c_bp_bucketed_batch_prepend_direct_actual_def by simp

lemma c_bp_bucketed_batch_prepend_direct_actual_steps [simp]:
  "bp_steps_of (c_bp_bucketed_batch_prepend_direct_actual xs P) =
    bp_batch_prepend_log_budget xs (bp_block_size P)"
  unfolding c_bp_bucketed_batch_prepend_direct_actual_def by simp

lemma c_bp_bucketed_batch_prepend_direct_paper_batch_cost_bound:
  "partition_batch_cost_bound
    (bp_steps_of (c_bp_bucketed_batch_prepend_direct xs P))
    (bp_batch_prepend_per_item_budget xs (bp_block_size P)) xs"
  unfolding partition_batch_cost_bound_def
  by (simp add: bp_batch_prepend_amortized_budget_alt)

lemma bp_bucketed_batch_prepend_state_empty [simp]:
  "bp_bucketed_batch_prepend_state [] P = P"
  unfolding bp_bucketed_batch_prepend_state_def by simp

lemma bp_bucketed_batch_prepend_state_entries_nonempty:
  assumes M_pos: "0 < bp_block_size P"
    and xs: "xs \<noteq> []"
  shows "bp_entries (bp_bucketed_batch_prepend_state xs P) =
    sort_key snd xs @ bp_entries P"
proof -
  obtain p ps where xs_def: "xs = p # ps"
    using xs by (cases xs) auto
  have flat:
    "bp_bucket_entries_flat
      (bp_bucketize_entries (bp_block_size P) xs) = sort_key snd xs"
    by (rule bp_bucket_entries_flat_bucketize_entries[OF M_pos])
  have flat':
    "bp_bucket_entries_flat
      (bp_bucketize_entries (bp_block_size P) (p # ps)) =
      sort_key snd (p # ps)"
    using flat unfolding xs_def .
  show ?thesis
    unfolding bp_bucketed_batch_prepend_state_def xs_def bp_entries_def
    using flat' by simp
qed

lemma bp_bucketed_batch_prepend_state_keys_nonempty:
  assumes M_pos: "0 < bp_block_size P"
    and xs: "xs \<noteq> []"
  shows "keys_of (bp_view (bp_bucketed_batch_prepend_state xs P)) =
    bp_entry_keys xs \<union> keys_of (bp_view P)"
  unfolding bp_view_def
    bp_bucketed_batch_prepend_state_entries_nonempty[OF M_pos xs]
    bp_entry_keys_def
  by auto

lemma bp_bucketed_batch_prepend_state_values:
  assumes distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
  shows "value_of (bp_view (bp_bucketed_batch_prepend_state xs P)) =
    value_of (batch_min_update (bp_view P) xs)"
proof -
  have disjoint': "fst ` set xs \<inter> keys_of (bp_view P) = {}"
    using disjoint unfolding bp_entry_keys_def by simp
  have vals_abs: "value_of (batch_min_update (bp_view P) xs) =
      bp_batch_value_update xs (value_of (bp_view P))"
    by (rule batch_min_update_value_distinct_disjoint
        [OF distinct disjoint'])
  show ?thesis
    using vals_abs
    unfolding bp_view_def bp_bucketed_batch_prepend_state_def
    by (cases xs) simp_all
qed

theorem bp_bucketed_batch_prepend_state_refines_batch_min_update:
  assumes inv: "bp_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
  shows "bp_view (bp_bucketed_batch_prepend_state xs P) =
    batch_min_update (bp_view P) xs"
proof (cases "xs = []")
  case True
  then show ?thesis
    unfolding batch_min_update_def by simp
next
  case False
  have M_pos: "0 < bp_block_size P"
    using inv unfolding bp_invariant_def by blast
  have keys: "keys_of (bp_view (bp_bucketed_batch_prepend_state xs P)) =
      keys_of (batch_min_update (bp_view P) xs)"
  proof -
    have state: "keys_of (bp_view (bp_bucketed_batch_prepend_state xs P)) =
        bp_entry_keys xs \<union> keys_of (bp_view P)"
      by (rule bp_bucketed_batch_prepend_state_keys_nonempty[OF M_pos False])
    have abstract: "keys_of (batch_min_update (bp_view P) xs) =
        keys_of (bp_view P) \<union> bp_entry_keys xs"
      by (simp add: batch_min_update_keys bp_entry_keys_def)
    show ?thesis
      using state abstract by auto
  qed
  have vals_state: "value_of (bp_view (bp_bucketed_batch_prepend_state xs P)) =
      value_of (batch_min_update (bp_view P) xs)"
    by (rule bp_bucketed_batch_prepend_state_values
        [OF distinct disjoint])
  show ?thesis
    using keys vals_state
    by (cases "bp_view (bp_bucketed_batch_prepend_state xs P)";
        cases "batch_min_update (bp_view P) xs"; simp)
qed

lemma bp_rebase_first_bucket_marker_markers_lower_bound:
  assumes lower:
    "\<forall>b\<in>set bs. \<forall>p\<in>set (bp_bucket_entries b). bp_marker b \<le> snd p"
    and beta_le: "\<forall>p\<in>set (bp_bucket_entries_flat bs). beta \<le> snd p"
  shows "\<forall>b\<in>set (bp_rebase_first_bucket_marker beta bs).
    \<forall>p\<in>set (bp_bucket_entries b). bp_marker b \<le> snd p"
  using assms
  by (cases bs) (auto simp: bp_bucket_entries_flat_def)

lemma bp_rebase_first_bucket_marker_markers_sorted:
  assumes sorted: "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) bs"
    and boundaries: "bp_bucket_boundaries_ok bs"
    and head_nonempty:
      "\<And>b bs'. bp_drop_empty_prefix bs = b # bs' \<Longrightarrow>
        bp_bucket_entries b \<noteq> []"
    and beta_le:
      "\<forall>p\<in>set (bp_bucket_entries_flat (bp_drop_empty_prefix bs)).
        beta \<le> snd p"
  shows "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
    (bp_rebase_first_bucket_marker beta (bp_drop_empty_prefix bs))"
proof (cases "bp_drop_empty_prefix bs")
  case Nil
  then show ?thesis by simp
next
  case (Cons b rest)
  note old0 = Cons
  have old0_sorted: "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c)
      (bp_drop_empty_prefix bs)"
    by (rule bp_bucket_markers_sorted_drop_empty_prefix[OF sorted])
  have old0_boundaries:
    "bp_bucket_boundaries_ok (bp_drop_empty_prefix bs)"
    by (rule bp_bucket_boundaries_ok_drop_empty_prefix[OF boundaries])
  have b_nonempty: "bp_bucket_entries b \<noteq> []"
    using head_nonempty Cons by blast
  show ?thesis
  proof (cases rest)
    case Nil
    then show ?thesis
      using old0 by simp
  next
    case (Cons c cs)
    obtain q where q: "q \<in> set (bp_bucket_entries b)"
      using b_nonempty by (cases "bp_bucket_entries b") auto
    have beta_le_q: "beta \<le> snd q"
      using beta_le old0 q unfolding bp_bucket_entries_flat_def by auto
    have q_le_c: "snd q \<le> bp_marker c"
      using old0_boundaries old0 Cons q by simp
    have beta_le_c: "beta \<le> bp_marker c"
      using beta_le_q q_le_c by linarith
    have tail_sorted:
      "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) (c # cs)"
      using old0_sorted old0 Cons by simp
    have beta_le_tail:
      "\<forall>d\<in>set (c # cs). beta \<le> bp_marker d"
    proof
      fix d
      assume d: "d \<in> set (c # cs)"
      have "bp_marker c \<le> bp_marker d"
        using tail_sorted d by (cases "d = c") auto
      then show "beta \<le> bp_marker d"
        using beta_le_c by linarith
    qed
    show ?thesis
      using old0 Cons tail_sorted beta_le_tail by simp
  qed
qed

lemma bp_batch_max_value_le_old_entry:
  assumes xs: "xs = p # ps"
    and admissible: "batch_prepend_admissible (bp_view P) xs"
    and inv: "bp_invariant P"
    and r: "r \<in> set (bp_entries P)"
  shows "bp_batch_max_value (snd p) ps \<le> snd r"
proof -
  have r_key: "fst r \<in> keys_of (bp_view P)"
    using r unfolding bp_view_def bp_entry_keys_def by auto
  have r_value: "value_of (bp_view P) (fst r) = snd r"
    using inv r unfolding bp_invariant_def bp_values_consistent_def
      bp_view_def by simp
  have all_le: "\<And>q. q \<in> set xs \<Longrightarrow> snd q \<le> snd r"
  proof -
    fix q
    assume q: "q \<in> set xs"
    then have "snd q \<le> value_of (bp_view P) (fst r)"
      using admissible r_key
      unfolding batch_prepend_admissible_def by force
    then show "snd q \<le> snd r"
      using r_value by simp
  qed
  have ps_le: "\<And>q. q \<in> set ps \<Longrightarrow> snd q \<le> snd r"
    using all_le xs by auto
  have p_le: "snd p \<le> snd r"
    using all_le xs by simp
  show ?thesis
    by (rule bp_batch_max_value_upper[OF ps_le p_le])
qed

lemma bp_bucketed_batch_prepend_state_invariant:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
    and admissible: "batch_prepend_admissible (bp_view P) xs"
  shows "bp_invariant (bp_bucketed_batch_prepend_state xs P)"
proof (cases xs)
  case Nil
  then show ?thesis
    using bp_ordered_invariant_invariant[OF ord] by simp
next
  case (Cons p ps)
  let ?M = "bp_block_size P"
  let ?beta = "bp_batch_max_value (snd p) ps"
  let ?new = "bp_bucketize_entries ?M xs"
  let ?trimmed = "bp_drop_empty_prefix (bp_buckets P)"
  let ?old = "bp_rebase_first_bucket_marker ?beta ?trimmed"
  let ?P' = "bp_bucketed_batch_prepend_state xs P"
  have inv: "bp_invariant P"
    by (rule bp_ordered_invariant_invariant[OF ord])
  have boundaries: "bp_bucket_boundaries_ok (bp_buckets P)"
    using bp_ordered_invariant_boundaries_state_ok[OF ord]
    unfolding bp_bucket_boundaries_state_ok_def .
  have M_pos: "0 < ?M"
    using inv unfolding bp_invariant_def by blast
  have entries_state: "bp_entries ?P' = sort_key snd xs @ bp_entries P"
    by (rule bp_bucketed_batch_prepend_state_entries_nonempty[OF M_pos])
      (simp add: Cons)
  have old_distinct: "distinct (map fst (bp_entries P))"
    using inv unfolding bp_invariant_def bp_distinct_keys_def by blast
  have new_distinct: "distinct (map fst (sort_key snd xs))"
    by (rule distinct_map_fst_sort_key[OF distinct])
  have disj_keys:
    "set (map fst (sort_key snd xs)) \<inter> set (map fst (bp_entries P)) = {}"
    using disjoint unfolding bp_entry_keys_def bp_view_def by auto
  have distinct_entries:
    "distinct (map fst (sort_key snd xs @ bp_entries P))"
    using new_distinct old_distinct disj_keys by simp
  have beta_le_old:
    "\<forall>r\<in>set (bp_entries P). ?beta \<le> snd r"
  proof
    fix r
    assume r: "r \<in> set (bp_entries P)"
    show "?beta \<le> snd r"
      by (rule bp_batch_max_value_le_old_entry
          [OF Cons admissible inv r])
  qed
  have beta_le_trimmed:
    "\<forall>r\<in>set (bp_bucket_entries_flat ?trimmed). ?beta \<le> snd r"
    using beta_le_old unfolding bp_entries_def by simp
  have new_sizes:
    "\<forall>b\<in>set ?new. length (bp_bucket_entries b) \<le> ?M"
    by (rule bp_bucketize_entries_sizes_ok[OF M_pos])
  have trimmed_subset: "set ?trimmed \<subseteq> set (bp_buckets P)"
    by (rule bp_drop_empty_prefix_set_subset)
  have trimmed_sizes:
    "\<forall>b\<in>set ?trimmed. length (bp_bucket_entries b) \<le> ?M"
    using inv trimmed_subset unfolding bp_invariant_def bp_bucket_sizes_ok_def
    by blast
  have old_sizes:
    "\<forall>b\<in>set ?old. length (bp_bucket_entries b) \<le> ?M"
  proof (cases ?trimmed)
    case Nil
    then show ?thesis by simp
  next
    case (Cons b bs)
    then show ?thesis
      using trimmed_sizes by simp
  qed
  have new_sorted:
    "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) ?new"
    by (rule bp_bucketize_entries_markers_sorted[OF M_pos])
  have old_sorted:
    "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) ?old"
  proof (rule bp_rebase_first_bucket_marker_markers_sorted)
    show "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) (bp_buckets P)"
      using inv unfolding bp_invariant_def bp_bucket_markers_sorted_def
      by blast
    show "bp_bucket_boundaries_ok (bp_buckets P)"
      by (rule boundaries)
    show "\<And>b bs'. bp_drop_empty_prefix (bp_buckets P) = b # bs' \<Longrightarrow>
        bp_bucket_entries b \<noteq> []"
      by (rule bp_drop_empty_prefix_head_nonempty)
    show "\<forall>r\<in>set (bp_bucket_entries_flat
        (bp_drop_empty_prefix (bp_buckets P))). ?beta \<le> snd r"
      by (rule beta_le_trimmed)
  qed
  have new_marker_le_beta:
    "\<forall>b\<in>set ?new. bp_marker b \<le> ?beta"
  proof (rule bp_bucketize_entries_markers_le)
    show "\<forall>q\<in>set xs. snd q \<le> ?beta"
      using Cons
      by (auto simp: bp_batch_max_value_ge_member_Cons)
  qed
  have beta_le_old_markers:
    "\<forall>b\<in>set ?old. ?beta \<le> bp_marker b"
  proof (cases ?old)
    case Nil
    then show ?thesis by simp
  next
    case (Cons b bs)
    have head: "bp_marker b = ?beta"
      using Cons by (cases ?trimmed) auto
    have tail_ge: "\<forall>c\<in>set bs. bp_marker b \<le> bp_marker c"
      using old_sorted Cons by simp
    show ?thesis
      using Cons head tail_ge by auto
  qed
  have sorted_all:
    "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) (?new @ ?old)"
    unfolding sorted_wrt_append
  proof (intro conjI ballI)
    show "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) ?new"
      by (rule new_sorted)
    show "sorted_wrt (\<lambda>b c. bp_marker b \<le> bp_marker c) ?old"
      by (rule old_sorted)
    fix b c
    assume b: "b \<in> set ?new" and c: "c \<in> set ?old"
    have "bp_marker b \<le> ?beta"
      using new_marker_le_beta b by blast
    moreover have "?beta \<le> bp_marker c"
      using beta_le_old_markers c by blast
    ultimately show "bp_marker b \<le> bp_marker c"
      by linarith
  qed
  have new_lower:
    "\<forall>b\<in>set ?new. \<forall>q\<in>set (bp_bucket_entries b).
      bp_marker b \<le> snd q"
    by (rule bp_bucketize_entries_markers_lower_bound[OF M_pos])
  have trimmed_lower:
    "\<forall>b\<in>set ?trimmed. \<forall>q\<in>set (bp_bucket_entries b).
      bp_marker b \<le> snd q"
    using inv trimmed_subset
    unfolding bp_invariant_def bp_bucket_markers_lower_bound_def by blast
  have old_lower:
    "\<forall>b\<in>set ?old. \<forall>q\<in>set (bp_bucket_entries b).
      bp_marker b \<le> snd q"
    by (rule bp_rebase_first_bucket_marker_markers_lower_bound
        [OF trimmed_lower beta_le_trimmed])
  have lower_all:
    "\<forall>b\<in>set (?new @ ?old). \<forall>q\<in>set (bp_bucket_entries b).
      bp_marker b \<le> snd q"
    using new_lower old_lower by auto
  have values_entries:
    "\<forall>r\<in>set (sort_key snd xs @ bp_entries P).
      bp_batch_value_update xs (bp_values P) (fst r) = snd r"
  proof
    fix r
    assume r: "r \<in> set (sort_key snd xs @ bp_entries P)"
    show "bp_batch_value_update xs (bp_values P) (fst r) = snd r"
    proof (cases "r \<in> set (sort_key snd xs)")
      case True
      then have "r \<in> set xs"
        by simp
      obtain x b where r_def: "r = (x, b)"
        by force
      then have "(x, b) \<in> set xs"
        using \<open>r \<in> set xs\<close> by simp
      then have "bp_batch_value_update xs (bp_values P) x = b"
        by (rule bp_batch_value_update_in_set_distinct[OF distinct])
      then show ?thesis
        unfolding r_def by simp
    next
      case False
      then have r_old: "r \<in> set (bp_entries P)"
        using r by simp
      have "fst r \<notin> fst ` set xs"
        using disjoint r_old unfolding bp_entry_keys_def bp_view_def
        by auto
      then have unchanged:
        "bp_batch_value_update xs (bp_values P) (fst r) =
          bp_values P (fst r)"
        by (rule bp_batch_value_update_notin)
      have "bp_values P (fst r) = snd r"
        using inv r_old unfolding bp_invariant_def bp_values_consistent_def
        by blast
      then show ?thesis
        using unchanged by simp
    qed
  qed
  have flat_new: "bp_bucket_entries_flat ?new = sort_key snd xs"
    by (rule bp_bucket_entries_flat_bucketize_entries[OF M_pos])
  have flat_old: "bp_bucket_entries_flat ?old = bp_entries P"
    unfolding bp_entries_def by simp
  show ?thesis
    using M_pos distinct_entries new_sizes old_sizes sorted_all lower_all
      values_entries flat_new flat_old
    unfolding bp_bucketed_batch_prepend_state_def Cons Let_def
      bp_invariant_def bp_distinct_keys_def bp_bucket_sizes_ok_def
      bp_bucket_markers_sorted_def bp_bucket_markers_lower_bound_def
      bp_values_consistent_def bp_entries_def
    by auto
qed

lemma bp_bucketed_batch_prepend_state_boundaries_state_ok:
  assumes ord: "bp_ordered_invariant P"
    and admissible: "batch_prepend_admissible (bp_view P) xs"
  shows "bp_bucket_boundaries_state_ok
    (bp_bucketed_batch_prepend_state xs P)"
proof (cases xs)
  case Nil
  then show ?thesis
    using bp_ordered_invariant_boundaries_state_ok[OF ord] by simp
next
  case (Cons p ps)
  let ?M = "bp_block_size P"
  let ?beta = "bp_batch_max_value (snd p) ps"
  let ?new = "bp_bucketize_entries ?M xs"
  let ?trimmed = "bp_drop_empty_prefix (bp_buckets P)"
  let ?old = "bp_rebase_first_bucket_marker ?beta ?trimmed"
  have inv: "bp_invariant P"
    by (rule bp_ordered_invariant_invariant[OF ord])
  have M_pos: "0 < ?M"
    using inv unfolding bp_invariant_def by blast
  have trimmed_boundaries:
    "bp_bucket_boundaries_ok ?trimmed"
    by (rule bp_bucket_boundaries_ok_drop_empty_prefix)
      (use bp_ordered_invariant_boundaries_state_ok[OF ord] in
        \<open>simp add: bp_bucket_boundaries_state_ok_def\<close>)
  have old_boundaries: "bp_bucket_boundaries_ok ?old"
  proof (cases ?trimmed)
    case Nil
    then show ?thesis by simp
  next
    case (Cons b bs)
    then show ?thesis
    proof (cases bs)
      case Nil
      then show ?thesis
        using Cons by simp
    next
      case (Cons c cs)
      then show ?thesis
        using Cons trimmed_boundaries by simp
    qed
  qed
  have new_boundaries: "bp_bucket_boundaries_ok ?new"
    by (rule bp_bucketize_entries_boundaries_ok[OF M_pos])
  have new_entries_le_beta:
    "\<forall>b\<in>set ?new. \<forall>q\<in>set (bp_bucket_entries b).
      snd q \<le> ?beta"
  proof (intro ballI)
    fix b q
    assume b: "b \<in> set ?new"
      and q: "q \<in> set (bp_bucket_entries b)"
    have "q \<in> set xs"
      by (rule bp_bucketize_entries_entry_in_source[OF M_pos b q])
    then show "snd q \<le> ?beta"
      using Cons by (auto simp: bp_batch_max_value_ge_member_Cons)
  qed
  have cross:
    "?old \<noteq> [] \<Longrightarrow>
      \<forall>b\<in>set ?new. \<forall>q\<in>set (bp_bucket_entries b).
        snd q \<le> bp_marker (hd ?old)"
  proof -
    assume old_nonempty: "?old \<noteq> []"
    have "bp_marker (hd ?old) = ?beta"
      using old_nonempty by (cases ?trimmed) auto
    then show "\<forall>b\<in>set ?new. \<forall>q\<in>set (bp_bucket_entries b).
        snd q \<le> bp_marker (hd ?old)"
      using new_entries_le_beta by simp
  qed
  have appended: "bp_bucket_boundaries_ok (?new @ ?old)"
    by (rule bp_bucket_boundaries_ok_append
        [OF new_boundaries old_boundaries cross])
  show ?thesis
    using appended Cons
    unfolding bp_bucketed_batch_prepend_state_def Let_def
      bp_bucket_boundaries_state_ok_def
    by simp
qed

lemma bp_bucketed_batch_prepend_state_ordered_invariant:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
    and admissible: "batch_prepend_admissible (bp_view P) xs"
  shows "bp_ordered_invariant (bp_bucketed_batch_prepend_state xs P)"
  unfolding bp_ordered_invariant_def
  using bp_bucketed_batch_prepend_state_invariant
      [OF ord distinct disjoint admissible]
    bp_bucketed_batch_prepend_state_boundaries_state_ok
      [OF ord admissible]
  by blast

text \<open>
  Bucketed BatchPrepend is not implemented as repeated Insert.  The incoming
  batch is first bucketized on its own, then placed before the existing
  buckets.  To preserve the boundary condition, the old prefix of empty buckets
  is dropped and the first surviving old bucket is rebased to the maximum value
  of the batch.  The admissibility assumption is the abstract promise that
  every old entry is above the batch range.  Together with distinctness and
  disjointness of keys, this yields both the view refinement
  @{thm bp_bucketed_batch_prepend_state_refines_batch_min_update} and the
  ordered invariant theorem above.
\<close>

lemma c_bp_bucketed_batch_prepend_direct_invariant:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
    and admissible: "batch_prepend_admissible (bp_view P) xs"
  shows "bp_invariant
    (bp_result_of (c_bp_bucketed_batch_prepend_direct xs P))"
  unfolding c_bp_bucketed_batch_prepend_direct_result
  by (rule bp_bucketed_batch_prepend_state_invariant
      [OF ord distinct disjoint admissible])

lemma c_bp_bucketed_batch_prepend_direct_ordered_invariant:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
    and admissible: "batch_prepend_admissible (bp_view P) xs"
  shows "bp_ordered_invariant
    (bp_result_of (c_bp_bucketed_batch_prepend_direct xs P))"
  unfolding c_bp_bucketed_batch_prepend_direct_result
  by (rule bp_bucketed_batch_prepend_state_ordered_invariant
      [OF ord distinct disjoint admissible])

lemma c_bp_bucketed_batch_prepend_direct_refines_batch_min_update:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
  shows "bp_view (bp_result_of (c_bp_bucketed_batch_prepend_direct xs P)) =
    batch_min_update (bp_view P) xs"
  unfolding c_bp_bucketed_batch_prepend_direct_result
  by (rule bp_bucketed_batch_prepend_state_refines_batch_min_update
      [OF bp_ordered_invariant_invariant[OF ord] distinct disjoint])

lemma c_bp_bucketed_batch_prepend_direct_preserves_upper_bound:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
    and upper: "partition_upper_bound (bp_view P) B"
    and values_lt: "\<And>x b. (x, b) \<in> set xs \<Longrightarrow> b < B"
  shows "partition_upper_bound
    (bp_view (bp_result_of (c_bp_bucketed_batch_prepend_direct xs P))) B"
  unfolding c_bp_bucketed_batch_prepend_direct_refines_batch_min_update
    [OF ord distinct disjoint]
  by (rule batch_min_update_preserves_upper_bound[OF upper values_lt])

lemma c_bp_bucketed_batch_prepend_direct_batch_cost_bound:
  "partition_batch_cost_bound
    (bp_steps_of (c_bp_bucketed_batch_prepend_direct xs P))
    (bp_batch_prepend_per_item_budget xs (bp_block_size P)) xs"
  by (rule c_bp_bucketed_batch_prepend_direct_paper_batch_cost_bound)

lemma bp_bucketed_batch_prepend_state_buckets_length_nonempty:
  assumes M_pos: "0 < bp_block_size P"
    and xs: "xs \<noteq> []"
  shows "length (bp_buckets (bp_bucketed_batch_prepend_state xs P)) \<le>
    length xs + length (bp_buckets P)"
proof -
  obtain p ps where xs_def: "xs = p # ps"
    using xs by (cases xs) auto
  have new:
    "length (bp_bucketize_entries (bp_block_size P) xs) \<le> length xs"
    by (rule length_bp_bucketize_entries_le_length[OF M_pos])
  have new':
    "length (bp_bucketize_entries (bp_block_size P) (p # ps)) \<le>
      Suc (length ps)"
    using new unfolding xs_def by simp
  have old:
    "length (bp_rebase_first_bucket_marker
        (bp_batch_max_value (snd p) ps)
        (bp_drop_empty_prefix (bp_buckets P))) \<le>
      length (bp_buckets P)"
    by simp
  have old':
    "length (bp_drop_empty_prefix (bp_buckets P)) \<le>
      length (bp_buckets P)"
    by simp
  have total:
    "length (bp_bucketize_entries (bp_block_size P) (p # ps)) +
      length (bp_drop_empty_prefix (bp_buckets P)) \<le>
      Suc (length ps) + length (bp_buckets P)"
    using new' old' by linarith
  show ?thesis
    unfolding bp_bucketed_batch_prepend_state_def xs_def Let_def
    using total by simp
qed

lemma bp_bucketed_batch_prepend_state_bucket_count_slack_le:
  assumes inv: "bp_invariant P"
  shows "bp_bucket_count_slack (bp_bucketed_batch_prepend_state xs P) \<le>
    length xs + bp_bucket_count_slack P"
proof (cases "xs = []")
  case True
  then show ?thesis by simp
next
  case False
  let ?P' = "bp_bucketed_batch_prepend_state xs P"
  let ?M = "bp_block_size P"
  let ?N = "length (bp_entries P)"
  let ?N' = "length (bp_entries ?P')"
  let ?K = "length (bp_buckets P)"
  let ?K' = "length (bp_buckets ?P')"
  let ?L = "length xs"
  have M_pos: "0 < ?M"
    using inv unfolding bp_invariant_def by blast
  have entries_len: "?N' = ?L + ?N"
    using bp_bucketed_batch_prepend_state_entries_nonempty[OF M_pos False]
    by simp
  have buckets_len: "?K' \<le> ?L + ?K"
    by (rule bp_bucketed_batch_prepend_state_buckets_length_nonempty
        [OF M_pos False])
  have div_le: "Suc (?N div ?M) \<le> Suc (?N' div ?M)"
    unfolding entries_len by (simp add: div_le_mono)
  have block: "bp_block_size ?P' = ?M"
    unfolding bp_bucketed_batch_prepend_state_def
    by (cases xs) (simp_all add: Let_def)
  have diff:
    "?K' - Suc (?N' div ?M) \<le>
      ?L + (?K - Suc (?N div ?M))"
    by (rule nat_diff_add_right_le[OF buckets_len div_le])
  show ?thesis
    using diff
    unfolding bp_bucket_count_slack_def entries_len block
    by simp
qed

lemma bp_bucketed_batch_prepend_state_split_potential_le:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
    and admissible: "batch_prepend_admissible (bp_view P) xs"
  shows "bp_split_potential (bp_bucketed_batch_prepend_state xs P) \<le>
    length xs + bp_split_potential P"
proof -
  have inv: "bp_invariant P"
    by (rule bp_ordered_invariant_invariant[OF ord])
  have inv':
    "bp_invariant (bp_bucketed_batch_prepend_state xs P)"
    by (rule bp_bucketed_batch_prepend_state_invariant
        [OF ord distinct disjoint admissible])
  have overflow':
    "bp_overflow_potential (bp_bucketed_batch_prepend_state xs P) = 0"
    by (rule bp_invariant_overflow_potential_zero[OF inv'])
  have slack:
    "bp_bucket_count_slack (bp_bucketed_batch_prepend_state xs P) \<le>
      length xs + bp_bucket_count_slack P"
    by (rule bp_bucketed_batch_prepend_state_bucket_count_slack_le[OF inv])
  have "bp_split_potential (bp_bucketed_batch_prepend_state xs P) =
      bp_bucket_count_slack (bp_bucketed_batch_prepend_state xs P)"
    unfolding bp_split_potential_def using overflow' by simp
  also have "\<dots> \<le> length xs + bp_bucket_count_slack P"
    by (rule slack)
  also have "\<dots> \<le> length xs + bp_split_potential P"
    unfolding bp_split_potential_def by simp
  finally show ?thesis .
qed

lemma c_bp_bucketed_batch_prepend_direct_actual_refines_batch_min_update:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
  shows "bp_view
    (bp_result_of (c_bp_bucketed_batch_prepend_direct_actual xs P)) =
    batch_min_update (bp_view P) xs"
  unfolding c_bp_bucketed_batch_prepend_direct_actual_result
  by (rule bp_bucketed_batch_prepend_state_refines_batch_min_update
      [OF bp_ordered_invariant_invariant[OF ord] distinct disjoint])

lemma c_bp_bucketed_batch_prepend_direct_actual_invariant:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
    and admissible: "batch_prepend_admissible (bp_view P) xs"
  shows "bp_invariant
    (bp_result_of (c_bp_bucketed_batch_prepend_direct_actual xs P))"
  unfolding c_bp_bucketed_batch_prepend_direct_actual_result
  by (rule bp_bucketed_batch_prepend_state_invariant
      [OF ord distinct disjoint admissible])

lemma c_bp_bucketed_batch_prepend_direct_actual_ordered_invariant:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
    and admissible: "batch_prepend_admissible (bp_view P) xs"
  shows "bp_ordered_invariant
    (bp_result_of (c_bp_bucketed_batch_prepend_direct_actual xs P))"
  unfolding c_bp_bucketed_batch_prepend_direct_actual_result
  by (rule bp_bucketed_batch_prepend_state_ordered_invariant
      [OF ord distinct disjoint admissible])

lemma c_bp_bucketed_batch_prepend_direct_actual_preserves_upper_bound:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
    and upper: "partition_upper_bound (bp_view P) B"
    and values_lt: "\<And>x b. (x, b) \<in> set xs \<Longrightarrow> b < B"
  shows "partition_upper_bound
    (bp_view
      (bp_result_of (c_bp_bucketed_batch_prepend_direct_actual xs P))) B"
  unfolding c_bp_bucketed_batch_prepend_direct_actual_refines_batch_min_update
    [OF ord distinct disjoint]
  by (rule batch_min_update_preserves_upper_bound[OF upper values_lt])

lemma c_bp_bucketed_batch_prepend_direct_actual_amortized_paper_bound:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
    and admissible: "batch_prepend_admissible (bp_view P) xs"
  shows "bp_amortized_step_bound
    (bp_steps_of (c_bp_bucketed_batch_prepend_direct_actual xs P)) P
    (bp_result_of (c_bp_bucketed_batch_prepend_direct_actual xs P))
    (bp_batch_prepend_amortized_budget xs (bp_block_size P))"
proof -
  have pot:
    "bp_split_potential
        (bp_bucketed_batch_prepend_state xs P) \<le>
      length xs + bp_split_potential P"
    by (rule bp_bucketed_batch_prepend_state_split_potential_le
        [OF ord distinct disjoint admissible])
  show ?thesis
    using pot
    unfolding bp_amortized_step_bound_def
      bp_batch_prepend_amortized_budget_def
    by simp
qed

lemma c_bp_bucketed_batch_prepend_direct_actual_batch_cost_bound:
  "partition_batch_cost_bound
    (bp_steps_of (c_bp_bucketed_batch_prepend_direct_actual xs P))
    (bp_ratio_log_budget (length xs) (bp_block_size P)) xs"
  unfolding partition_batch_cost_bound_def
    c_bp_bucketed_batch_prepend_direct_actual_steps
    bp_batch_prepend_log_budget_def
  by (simp add: mult.commute)

lemma c_bp_rebucketed_batch_prepend_bulk_regular_invariant:
  assumes reg: "bp_regular_invariant P"
  shows "bp_regular_invariant
    (bp_result_of (c_bp_rebucketed_batch_prepend_bulk xs P))"
  unfolding c_bp_rebucketed_batch_prepend_bulk_result
  by (rule bp_rebucketed_batch_prepend_regular_invariant
      [OF bp_ordered_invariant_invariant
        [OF bp_regular_invariant_ordered_invariant[OF reg]]])

lemma c_bp_rebucketed_batch_prepend_bulk_refines_batch_min_update:
  assumes reg: "bp_regular_invariant P"
  shows "bp_view (bp_result_of (c_bp_rebucketed_batch_prepend_bulk xs P)) =
    batch_min_update (bp_view P) xs"
  unfolding c_bp_rebucketed_batch_prepend_bulk_result
  by (rule bp_rebucketed_batch_prepend_refines_batch_min_update
      [OF bp_ordered_invariant_invariant
        [OF bp_regular_invariant_ordered_invariant[OF reg]]])

lemma c_bp_rebucketed_batch_prepend_bulk_preserves_upper_bound:
  assumes reg: "bp_regular_invariant P"
    and upper: "partition_upper_bound (bp_view P) B"
    and values_lt: "\<And>x b. (x, b) \<in> set xs \<Longrightarrow> b < B"
  shows "partition_upper_bound
    (bp_view (bp_result_of (c_bp_rebucketed_batch_prepend_bulk xs P))) B"
  unfolding c_bp_rebucketed_batch_prepend_bulk_result
  by (rule bp_rebucketed_batch_prepend_preserves_upper_bound
      [OF bp_ordered_invariant_invariant
        [OF bp_regular_invariant_ordered_invariant[OF reg]]
        upper values_lt])

lemma c_bp_rebucketed_batch_prepend_bulk_split_potential_zero:
  assumes reg: "bp_regular_invariant P"
  shows "bp_split_potential
    (bp_result_of (c_bp_rebucketed_batch_prepend_bulk xs P)) = 0"
  unfolding c_bp_rebucketed_batch_prepend_bulk_result
  by (rule bp_rebucketed_batch_prepend_split_potential_zero
      [OF bp_ordered_invariant_invariant
        [OF bp_regular_invariant_ordered_invariant[OF reg]]])

lemma c_bp_rebucketed_batch_prepend_bulk_amortized_bound:
  assumes reg: "bp_regular_invariant P"
  shows "bp_amortized_step_bound
    (bp_steps_of (c_bp_rebucketed_batch_prepend_bulk xs P)) P
    (bp_result_of (c_bp_rebucketed_batch_prepend_bulk xs P))
    (bp_batch_prepend_log_budget xs (bp_block_size P))"
  using c_bp_rebucketed_batch_prepend_bulk_split_potential_zero[OF reg, of xs]
    bp_regular_invariant_split_potential_zero[OF reg]
  unfolding bp_amortized_step_bound_def by simp

lemma c_bp_rebucketed_batch_prepend_bulk_steps_le_amortized_budget:
  "bp_steps_of (c_bp_rebucketed_batch_prepend_bulk xs P) \<le>
    bp_batch_prepend_amortized_budget xs (bp_block_size P)"
  using bp_batch_prepend_log_budget_le_amortized_budget[of xs "bp_block_size P"]
  by simp

lemma c_bp_rebucketed_batch_prepend_bulk_amortized_paper_bound:
  assumes reg: "bp_regular_invariant P"
  shows "bp_amortized_step_bound
    (bp_steps_of (c_bp_rebucketed_batch_prepend_bulk xs P)) P
    (bp_result_of (c_bp_rebucketed_batch_prepend_bulk xs P))
    (bp_batch_prepend_amortized_budget xs (bp_block_size P))"
proof -
  have base: "bp_amortized_step_bound
      (bp_steps_of (c_bp_rebucketed_batch_prepend_bulk xs P)) P
      (bp_result_of (c_bp_rebucketed_batch_prepend_bulk xs P))
      (bp_batch_prepend_log_budget xs (bp_block_size P))"
    by (rule c_bp_rebucketed_batch_prepend_bulk_amortized_bound[OF reg])
  have budget:
    "bp_batch_prepend_log_budget xs (bp_block_size P) \<le>
      bp_batch_prepend_amortized_budget xs (bp_block_size P)"
    by (rule bp_batch_prepend_log_budget_le_amortized_budget)
  show ?thesis
    using base budget unfolding bp_amortized_step_bound_def by linarith
qed

lemma c_bp_rebucketed_batch_prepend_bulk_batch_cost_bound:
  "partition_batch_cost_bound
    (bp_steps_of (c_bp_rebucketed_batch_prepend_bulk xs P))
    (bp_ratio_log_budget (length xs) (bp_block_size P)) xs"
  unfolding partition_batch_cost_bound_def
  by (simp add: c_bp_rebucketed_batch_prepend_bulk_steps
      bp_batch_prepend_log_budget_def mult.commute)

lemma c_bp_rebucketed_batch_prepend_bulk_paper_batch_cost_bound:
  "partition_batch_cost_bound
    (bp_steps_of (c_bp_rebucketed_batch_prepend_bulk xs P))
    (bp_batch_prepend_per_item_budget xs (bp_block_size P)) xs"
proof -
  have steps:
    "bp_steps_of (c_bp_rebucketed_batch_prepend_bulk xs P) \<le>
      bp_batch_prepend_amortized_budget xs (bp_block_size P)"
    by (rule c_bp_rebucketed_batch_prepend_bulk_steps_le_amortized_budget)
  show ?thesis
    using steps
    unfolding partition_batch_cost_bound_def
      bp_batch_prepend_amortized_budget_alt
    by simp
qed

lemma c_bp_first_bucket_pull_result [simp]:
  "bp_result_of (c_bp_first_bucket_pull M B P) =
    bp_first_bucket_pull M B P"
  unfolding bp_result_of_def c_bp_first_bucket_pull_def by simp

lemma c_bp_first_bucket_pull_steps [simp]:
  "bp_steps_of (c_bp_first_bucket_pull M B P) = M"
  unfolding bp_steps_of_def c_bp_first_bucket_pull_def by simp

lemma c_bp_first_bucket_pull_M_bound:
  "bp_steps_of (c_bp_first_bucket_pull M B P) \<le> M"
  by simp

lemma c_bp_first_bucket_pull_scan_result [simp]:
  "bp_result_of (c_bp_first_bucket_pull_scan M B P) =
    bp_first_bucket_pull M B P"
  unfolding bp_result_of_def c_bp_first_bucket_pull_scan_def
  by (auto split: prod.splits)

lemma c_bp_first_bucket_pull_scan_steps:
  assumes "bp_first_bucket_pull M B P = (S, beta, P')"
  shows "bp_steps_of (c_bp_first_bucket_pull_scan M B P) = card S"
  using assms unfolding bp_steps_of_def c_bp_first_bucket_pull_scan_def
  by simp

lemma bp_bucket_keys_card_le_length:
  "card (bp_bucket_keys b) \<le> length (bp_bucket_entries b)"
  unfolding bp_bucket_keys_def bp_entry_keys_def
  by (metis card_length length_map set_map)

lemma c_bp_first_bucket_pull_scan_M_bound:
  assumes can: "bp_can_first_bucket_pull M P"
  shows "bp_steps_of (c_bp_first_bucket_pull_scan M B P) \<le> M"
proof -
  obtain b c bs where buckets: "bp_buckets P = b # c # bs"
    and len_b: "length (bp_bucket_entries b) \<le> M"
    by (rule bp_can_first_bucket_pullE[OF can])
  have pull:
    "bp_first_bucket_pull M B P =
      (bp_bucket_keys b, bp_marker c, bp_delete_keys (bp_bucket_keys b) P)"
    unfolding bp_first_bucket_pull_def buckets by simp
  have "bp_steps_of (c_bp_first_bucket_pull_scan M B P) =
      card (bp_bucket_keys b)"
    by (rule c_bp_first_bucket_pull_scan_steps[OF pull])
  also have "\<dots> \<le> length (bp_bucket_entries b)"
    by (rule bp_bucket_keys_card_le_length)
  also have "\<dots> \<le> M"
    by (rule len_b)
  finally show ?thesis .
qed

lemma c_bp_first_bucket_pull_scan_partition_pull_cost_bound:
  assumes pull: "bp_first_bucket_pull M B P = (S, beta, P')"
  shows "partition_pull_cost_bound
    (bp_steps_of (c_bp_first_bucket_pull_scan M B P)) S"
  using c_bp_first_bucket_pull_scan_steps[OF pull]
  unfolding partition_pull_cost_bound_def by simp

lemma c_bp_first_bucket_pull_scan_partition_pull_cost_bound_from_result:
  assumes pull:
    "bp_result_of (c_bp_first_bucket_pull_scan M B P) = (S, beta, P')"
  shows "partition_pull_cost_bound
    (bp_steps_of (c_bp_first_bucket_pull_scan M B P)) S"
proof -
  have pull': "bp_first_bucket_pull M B P = (S, beta, P')"
    using pull by simp
  show ?thesis
    by (rule c_bp_first_bucket_pull_scan_partition_pull_cost_bound[OF pull'])
qed

lemma c_bp_first_bucket_pull_scan_invariant:
  assumes inv: "bp_invariant P"
  shows "bp_invariant
    (bp_pull_state_of (bp_result_of (c_bp_first_bucket_pull_scan M B P)))"
proof -
  obtain S beta P' where pull: "bp_first_bucket_pull M B P = (S, beta, P')"
    by (cases "bp_first_bucket_pull M B P")
  have "bp_invariant P'"
    by (rule bp_first_bucket_pull_invariant[OF inv pull])
  then show ?thesis
    using pull unfolding bp_pull_state_of_def by simp
qed

lemma c_bp_first_bucket_pull_scan_amortized_M_bound:
  assumes inv: "bp_invariant P"
    and can: "bp_can_first_bucket_pull M P"
  shows "bp_pull_amortized_step_bound
    (bp_steps_of (c_bp_first_bucket_pull_scan M B P)) P
    (bp_result_of (c_bp_first_bucket_pull_scan M B P)) (2 * M)"
proof -
  obtain b c bs where buckets: "bp_buckets P = b # c # bs"
    and len_b: "length (bp_bucket_entries b) \<le> M"
    by (rule bp_can_first_bucket_pullE[OF can])
  let ?S = "bp_bucket_keys b"
  have pull:
    "bp_first_bucket_pull M B P =
      (?S, bp_marker c, bp_delete_keys ?S P)"
    unfolding bp_first_bucket_pull_def buckets by simp
  have state:
    "bp_pull_state_of
      (bp_result_of (c_bp_first_bucket_pull_scan M B P)) =
      bp_delete_keys ?S P"
    unfolding bp_pull_state_of_def using pull by simp
  have steps: "bp_steps_of (c_bp_first_bucket_pull_scan M B P) \<le> M"
    by (rule c_bp_first_bucket_pull_scan_M_bound[OF can])
  have card_S: "card ?S \<le> M"
  proof -
    have "card ?S \<le> length (bp_bucket_entries b)"
      by (rule bp_bucket_keys_card_le_length)
    also have "\<dots> \<le> M"
      by (rule len_b)
    finally show ?thesis .
  qed
  have finite_S: "finite ?S"
    unfolding bp_bucket_keys_def bp_entry_keys_def by simp
  have potential:
    "bp_split_potential (bp_delete_keys ?S P) \<le>
      bp_split_potential P + card ?S"
  proof (rule bp_delete_keys_split_potential_le)
    show "0 < bp_block_size P"
      using inv unfolding bp_invariant_def by blast
    show "bp_distinct_keys P"
      using inv unfolding bp_invariant_def by blast
    show "finite ?S"
      by (rule finite_S)
  qed
  show ?thesis
    using steps card_S potential unfolding bp_pull_amortized_step_bound_def
      state
    by linarith
qed

lemma c_bp_first_bucket_pull_scan_amortized_paper_bound:
  assumes inv: "bp_invariant P"
    and can: "bp_can_first_bucket_pull M P"
  shows "bp_pull_amortized_step_bound
    (bp_steps_of (c_bp_first_bucket_pull_scan M B P)) P
    (bp_result_of (c_bp_first_bucket_pull_scan M B P))
    (bp_pull_amortized_budget M)"
  unfolding bp_pull_amortized_budget_def
  by (rule c_bp_first_bucket_pull_scan_amortized_M_bound[OF inv can])

lemma c_bp_first_bucket_pull_scan_refines_pull_separates:
  assumes inv: "bp_invariant P"
    and can: "bp_can_first_bucket_pull M P"
    and pull:
      "bp_result_of (c_bp_first_bucket_pull_scan M B P) = (S, beta, P')"
  shows "pull_separates (bp_view P) M B S beta (bp_view P')"
proof -
  obtain b c bs where buckets: "bp_buckets P = b # c # bs"
    and len_b: "length (bp_bucket_entries b) \<le> M"
    and below: "bp_bucket_below_bound b (bp_marker c)"
    and tail_nonempty: "bp_bucket_entries_flat (c # bs) \<noteq> []"
    by (rule bp_can_first_bucket_pullE[OF can])
  have pull': "bp_first_bucket_pull M B P = (S, beta, P')"
    using pull by simp
  show ?thesis
    by (rule bp_first_bucket_pull_refines_pull_separates
        [OF inv buckets len_b below tail_nonempty pull'])
qed

text \<open>
  Pull is charged by the size of the set it returns.  The first-bucket policy is
  sound when @{const bp_can_first_bucket_pull} exposes two adjacent nonempty
  ranges and the first bucket lies entirely below the next marker.  In that
  case the returned boundary is the next marker, the deleted set is the key set
  of the first bucket, and @{const pull_separates} follows from the bucket
  boundary invariant.  The scan-cost lemmas count exactly the returned keys, so
  the primitive cost is at most \<open>M\<close>; the amortized Pull bound additionally
  allows potential to change after deleting those keys.
\<close>


subsection \<open>Paper-Facing Costed Operations\<close>

text \<open>
  The following aliases are the operations exported to the rest of the BMSSP
  development.  They choose the lazy precise Insert, the direct bucketed
  BatchPrepend, and the first-bucket Pull scan.  The aliases keep the public
  layer small: clients do not need to know which internal costed variant proved
  the bound, only that the selected operation refines the abstract interface
  and has the paper budget.
\<close>

definition c_bp_paper_insert ::
  "'k \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k bucketed_partition \<times> nat" where
  "c_bp_paper_insert x b P = c_bp_lazy_insert_precise x b P"

definition c_bp_paper_batch_prepend ::
  "('k \<times> real) list \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    'k bucketed_partition \<times> nat" where
  "c_bp_paper_batch_prepend xs P =
     c_bp_bucketed_batch_prepend_direct_actual xs P"

definition c_bp_paper_pull ::
  "nat \<Rightarrow> real \<Rightarrow> 'k bucketed_partition \<Rightarrow>
    ('k set \<times> real \<times> 'k bucketed_partition) \<times> nat" where
  "c_bp_paper_pull M B P = c_bp_first_bucket_pull_scan M B P"

definition bp_insert_paper_budget :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bp_insert_paper_budget N M =
     9 + floor_log (Suc (N div M))"

definition bp_batch_prepend_paper_budget :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bp_batch_prepend_paper_budget N M =
     2 + floor_log (Suc (N div M))"

definition bp_pull_paper_budget :: "nat \<Rightarrow> nat" where
  "bp_pull_paper_budget M = 2 * M"

lemma bp_lazy_insert_amortized_budget_paper_form:
  "bp_lazy_insert_amortized_budget P =
    bp_insert_paper_budget (length (bp_entries P)) (bp_block_size P)"
  unfolding bp_lazy_insert_amortized_budget_def
    bp_insert_search_budget_def bp_ratio_log_budget_def
    bp_insert_paper_budget_def
  by simp

lemma bp_batch_prepend_amortized_budget_paper_form:
  "bp_batch_prepend_amortized_budget xs M =
    length xs * bp_batch_prepend_paper_budget (length xs) M"
  unfolding bp_batch_prepend_amortized_budget_def
    bp_batch_prepend_log_budget_def bp_ratio_log_budget_def
    bp_batch_prepend_paper_budget_def
  by (simp add: algebra_simps)

lemma bp_ratio_log_budget_le_insert_paper_budget:
  "bp_ratio_log_budget N M \<le> bp_insert_paper_budget N M"
  unfolding bp_ratio_log_budget_def bp_insert_paper_budget_def by simp

lemma bp_ratio_log_budget_le_batch_prepend_paper_budget:
  "bp_ratio_log_budget N M \<le> bp_batch_prepend_paper_budget N M"
  unfolding bp_ratio_log_budget_def bp_batch_prepend_paper_budget_def by simp

lemma bp_insert_paper_budget_bigo_ratio_log:
  "(\<lambda>N. real (bp_insert_paper_budget N M)) \<in>
    O(\<lambda>N. real (bp_ratio_log_budget N M))"
proof -
  have bound:
    "\<And>N. norm (real (bp_insert_paper_budget N M)) \<le>
      9 * norm (real (bp_ratio_log_budget N M))"
  proof -
    fix N
    have "bp_insert_paper_budget N M \<le>
        9 * bp_ratio_log_budget N M"
      unfolding bp_insert_paper_budget_def bp_ratio_log_budget_def by simp
    then show "norm (real (bp_insert_paper_budget N M)) \<le>
      9 * norm (real (bp_ratio_log_budget N M))"
      by simp
  qed
  show ?thesis
    unfolding bigo_def
    by (intro CollectI exI[of _ 9] eventuallyI)
      (simp add: bp_insert_paper_budget_def bp_ratio_log_budget_def)
qed

lemma bp_batch_prepend_paper_budget_bigo_ratio_log:
  "(\<lambda>N. real (bp_batch_prepend_paper_budget N M)) \<in>
    O(\<lambda>N. real (bp_ratio_log_budget N M))"
proof -
  have bound:
    "\<And>N. norm (real (bp_batch_prepend_paper_budget N M)) \<le>
      2 * norm (real (bp_ratio_log_budget N M))"
  proof -
    fix N
    have "bp_batch_prepend_paper_budget N M \<le>
        2 * bp_ratio_log_budget N M"
      unfolding bp_batch_prepend_paper_budget_def bp_ratio_log_budget_def
      by simp
    then show "norm (real (bp_batch_prepend_paper_budget N M)) \<le>
      2 * norm (real (bp_ratio_log_budget N M))"
      by simp
  qed
  show ?thesis
    unfolding bigo_def
    by (intro CollectI exI[of _ 2] eventuallyI)
      (simp add: bp_batch_prepend_paper_budget_def bp_ratio_log_budget_def)
qed

lemma bp_pull_paper_budget_bigo_linear:
  "(\<lambda>M. real (bp_pull_paper_budget M)) \<in> O(\<lambda>M. real M)"
  unfolding bp_pull_paper_budget_def bigo_def
  by (intro CollectI exI[of _ 2] eventuallyI) simp

text \<open>
  The named paper budgets are intentionally simple.  The Insert budget
  @{const bp_insert_paper_budget} is a constant plus the ratio-log term over
  stored entries and block size.  The BatchPrepend budget
  @{const bp_batch_prepend_paper_budget} is the corresponding per-item budget;
  the abstract batch predicate then multiplies it by the batch length.  Pull
  uses @{const bp_pull_paper_budget}, linear in the requested block size.  The
  Big-O lemmas above record exactly the envelopes consumed by the headline
  bridge.
\<close>

lemma c_bp_paper_insert_result [simp]:
  "bp_result_of (c_bp_paper_insert x b P) =
    bp_lazy_insert_state x b P"
  unfolding c_bp_paper_insert_def by simp

lemma c_bp_paper_insert_steps [simp]:
  "bp_steps_of (c_bp_paper_insert x b P) =
    bp_local_insert_search_charge P + bp_lazy_insert_charge x b P"
  unfolding c_bp_paper_insert_def by simp

lemma c_bp_paper_insert_refines_min_update:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "bp_view (bp_result_of (c_bp_paper_insert x b P)) =
    min_update (bp_view P) x b"
proof -
  have M_pos: "0 < bp_block_size P"
    using lazy unfolding bp_lazy_ordered_invariant_def
      bp_lazy_invariant_def by blast
  show ?thesis
    unfolding c_bp_paper_insert_def
    by (rule c_bp_lazy_insert_precise_refines_min_update[OF M_pos])
qed

lemma c_bp_paper_insert_refines_insert_spec:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "insert_spec (bp_view P) x b
    (bp_view (bp_result_of (c_bp_paper_insert x b P)))"
  unfolding c_bp_paper_insert_refines_min_update[OF lazy]
  by (rule min_update_insert_spec)

lemma c_bp_paper_insert_lazy_ordered_invariant:
  assumes lazy: "bp_lazy_ordered_invariant P"
  shows "bp_lazy_ordered_invariant
    (bp_result_of (c_bp_paper_insert x b P))"
  unfolding c_bp_paper_insert_def
  by (rule c_bp_lazy_insert_precise_lazy_ordered_invariant[OF lazy])

lemma c_bp_paper_insert_amortized_paper_bound:
  assumes lazy: "bp_lazy_ordered_invariant P"
    and ratio: "bp_bucket_count_ratio_ok P"
  shows "bp_amortized_step_bound
    (bp_steps_of (c_bp_paper_insert x b P)) P
    (bp_result_of (c_bp_paper_insert x b P))
    (bp_lazy_insert_amortized_budget P)"
  unfolding c_bp_paper_insert_def
  by (rule c_bp_lazy_insert_precise_amortized_ratio_budget
      [OF lazy ratio])

lemma c_bp_paper_insert_regular_partition_insert_cost_bound:
  assumes reg: "bp_regular_invariant P"
  shows "partition_insert_cost_bound
    (bp_steps_of (c_bp_paper_insert x b P))
    (bp_lazy_insert_amortized_budget P)"
  unfolding c_bp_paper_insert_def
  by (rule c_bp_lazy_insert_precise_regular_partition_insert_cost_bound
      [OF reg])

lemma c_bp_paper_batch_prepend_result [simp]:
  "bp_result_of (c_bp_paper_batch_prepend xs P) =
    bp_bucketed_batch_prepend_state xs P"
  unfolding c_bp_paper_batch_prepend_def by simp

lemma c_bp_paper_batch_prepend_steps [simp]:
  "bp_steps_of (c_bp_paper_batch_prepend xs P) =
    bp_batch_prepend_log_budget xs (bp_block_size P)"
  unfolding c_bp_paper_batch_prepend_def by simp

lemma c_bp_paper_batch_prepend_refines_batch_min_update:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
  shows "bp_view (bp_result_of (c_bp_paper_batch_prepend xs P)) =
    batch_min_update (bp_view P) xs"
  unfolding c_bp_paper_batch_prepend_def
  by (rule c_bp_bucketed_batch_prepend_direct_actual_refines_batch_min_update
      [OF ord distinct disjoint])

lemma c_bp_paper_batch_prepend_ordered_invariant:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
    and admissible: "batch_prepend_admissible (bp_view P) xs"
  shows "bp_ordered_invariant
    (bp_result_of (c_bp_paper_batch_prepend xs P))"
  unfolding c_bp_paper_batch_prepend_def
  by (rule c_bp_bucketed_batch_prepend_direct_actual_ordered_invariant
      [OF ord distinct disjoint admissible])

lemma c_bp_paper_batch_prepend_preserves_upper_bound:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
    and upper: "partition_upper_bound (bp_view P) B"
    and values_lt: "\<And>x b. (x, b) \<in> set xs \<Longrightarrow> b < B"
  shows "partition_upper_bound
    (bp_view (bp_result_of (c_bp_paper_batch_prepend xs P))) B"
  unfolding c_bp_paper_batch_prepend_def
  by (rule c_bp_bucketed_batch_prepend_direct_actual_preserves_upper_bound
      [OF ord distinct disjoint upper values_lt])

lemma c_bp_paper_batch_prepend_amortized_paper_bound:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
    and admissible: "batch_prepend_admissible (bp_view P) xs"
  shows "bp_amortized_step_bound
    (bp_steps_of (c_bp_paper_batch_prepend xs P)) P
    (bp_result_of (c_bp_paper_batch_prepend xs P))
    (bp_batch_prepend_amortized_budget xs (bp_block_size P))"
  unfolding c_bp_paper_batch_prepend_def
  by (rule c_bp_bucketed_batch_prepend_direct_actual_amortized_paper_bound
      [OF ord distinct disjoint admissible])

lemma c_bp_paper_batch_prepend_batch_cost_bound:
  "partition_batch_cost_bound
    (bp_steps_of (c_bp_paper_batch_prepend xs P))
    (bp_ratio_log_budget (length xs) (bp_block_size P)) xs"
  unfolding c_bp_paper_batch_prepend_def
  by (rule c_bp_bucketed_batch_prepend_direct_actual_batch_cost_bound)

lemma c_bp_paper_pull_result [simp]:
  "bp_result_of (c_bp_paper_pull M B P) =
    bp_first_bucket_pull M B P"
  unfolding c_bp_paper_pull_def by simp

lemma c_bp_paper_pull_M_bound:
  assumes can: "bp_can_first_bucket_pull M P"
  shows "bp_steps_of (c_bp_paper_pull M B P) \<le> M"
  unfolding c_bp_paper_pull_def
  by (rule c_bp_first_bucket_pull_scan_M_bound[OF can])

lemma c_bp_paper_pull_partition_pull_cost_bound:
  assumes pull:
    "bp_result_of (c_bp_paper_pull M B P) = (S, beta, P')"
  shows "partition_pull_cost_bound
    (bp_steps_of (c_bp_paper_pull M B P)) S"
  unfolding c_bp_paper_pull_def
  by (rule c_bp_first_bucket_pull_scan_partition_pull_cost_bound_from_result
      [OF pull[unfolded c_bp_paper_pull_def]])

lemma c_bp_paper_pull_invariant:
  assumes inv: "bp_invariant P"
  shows "bp_invariant
    (bp_pull_state_of (bp_result_of (c_bp_paper_pull M B P)))"
  unfolding c_bp_paper_pull_def
  by (rule c_bp_first_bucket_pull_scan_invariant[OF inv])

lemma c_bp_paper_pull_amortized_paper_bound:
  assumes inv: "bp_invariant P"
    and can: "bp_can_first_bucket_pull M P"
  shows "bp_pull_amortized_step_bound
    (bp_steps_of (c_bp_paper_pull M B P)) P
    (bp_result_of (c_bp_paper_pull M B P))
    (bp_pull_amortized_budget M)"
  unfolding c_bp_paper_pull_def
  by (rule c_bp_first_bucket_pull_scan_amortized_paper_bound[OF inv can])

lemma c_bp_paper_pull_refines_pull_separates:
  assumes inv: "bp_invariant P"
    and can: "bp_can_first_bucket_pull M P"
    and pull:
      "bp_result_of (c_bp_paper_pull M B P) = (S, beta, P')"
  shows "pull_separates (bp_view P) M B S beta (bp_view P')"
  unfolding c_bp_paper_pull_def
  by (rule c_bp_first_bucket_pull_scan_refines_pull_separates
      [OF inv can pull[unfolded c_bp_paper_pull_def]])

corollary bp_realises_partition_insert_cost_bound:
  assumes reg: "bp_regular_invariant P"
  shows "\<exists>t. partition_insert_cost_bound
      (bp_steps_of (c_bp_paper_insert x b P)) t \<and>
    t = bp_insert_paper_budget (length (bp_entries P)) (bp_block_size P)"
proof (intro exI conjI)
  show "partition_insert_cost_bound
      (bp_steps_of (c_bp_paper_insert x b P))
      (bp_insert_paper_budget (length (bp_entries P)) (bp_block_size P))"
    using c_bp_paper_insert_regular_partition_insert_cost_bound[OF reg, of x b]
    by (simp add: bp_lazy_insert_amortized_budget_paper_form)
qed simp

corollary bp_realises_partition_batch_cost_bound:
  shows "\<exists>t. partition_batch_cost_bound
      (bp_steps_of (c_bp_paper_batch_prepend xs P)) t xs \<and>
    t = bp_batch_prepend_paper_budget (length xs) (bp_block_size P)"
proof (intro exI conjI)
  have cost:
    "partition_batch_cost_bound
      (bp_steps_of (c_bp_paper_batch_prepend xs P))
      (bp_ratio_log_budget (length xs) (bp_block_size P)) xs"
    by (rule c_bp_paper_batch_prepend_batch_cost_bound)
  have le:
    "bp_ratio_log_budget (length xs) (bp_block_size P) \<le>
      bp_batch_prepend_paper_budget (length xs) (bp_block_size P)"
    by (rule bp_ratio_log_budget_le_batch_prepend_paper_budget)
  show "partition_batch_cost_bound
      (bp_steps_of (c_bp_paper_batch_prepend xs P))
      (bp_batch_prepend_paper_budget (length xs) (bp_block_size P)) xs"
  proof -
    have steps_le:
      "bp_steps_of (c_bp_paper_batch_prepend xs P) \<le>
        bp_ratio_log_budget (length xs) (bp_block_size P) * length xs"
      using cost unfolding partition_batch_cost_bound_def .
    have budget_le:
      "bp_ratio_log_budget (length xs) (bp_block_size P) * length xs \<le>
        bp_batch_prepend_paper_budget (length xs) (bp_block_size P) *
          length xs"
      using le by simp
    show ?thesis
      using steps_le budget_le unfolding partition_batch_cost_bound_def
      by linarith
  qed
qed simp

corollary bp_realises_partition_pull_cost_bound:
  assumes pull:
    "bp_result_of (c_bp_paper_pull M B P) = (S, beta, P')"
  shows "partition_pull_cost_bound
    (bp_steps_of (c_bp_paper_pull M B P)) S"
  by (rule c_bp_paper_pull_partition_pull_cost_bound[OF pull])

text \<open>
  The realization corollaries are the interface-facing summary.  They convert
  the concrete step counters of @{const c_bp_paper_insert},
  @{const c_bp_paper_batch_prepend}, and @{const c_bp_paper_pull} into the
  abstract predicates @{const partition_insert_cost_bound},
  @{const partition_batch_cost_bound}, and @{const partition_pull_cost_bound}.
  These are the facts imported by the headline bridge; the operation-specific
  theorems below keep the sharper amortized statements visible for readers who
  want to inspect the data-structure proof itself.
\<close>

theorem bp_insert_cost_bound:
  assumes lazy: "bp_lazy_ordered_invariant P"
    and ratio: "bp_bucket_count_ratio_ok P"
  shows "bp_amortized_step_bound
    (bp_steps_of (c_bp_paper_insert x b P)) P
    (bp_result_of (c_bp_paper_insert x b P))
    (9 + floor_log
      (Suc (length (bp_entries P) div bp_block_size P)))"
  using c_bp_paper_insert_amortized_paper_bound[OF lazy ratio, of x b]
  by (simp add: bp_lazy_insert_amortized_budget_paper_form
      bp_insert_paper_budget_def)

theorem bp_batch_prepend_cost_bound:
  assumes ord: "bp_ordered_invariant P"
    and distinct: "distinct (map fst xs)"
    and disjoint: "bp_entry_keys xs \<inter> keys_of (bp_view P) = {}"
    and admissible: "batch_prepend_admissible (bp_view P) xs"
  shows "bp_amortized_step_bound
    (bp_steps_of (c_bp_paper_batch_prepend xs P)) P
    (bp_result_of (c_bp_paper_batch_prepend xs P))
    (length xs *
      (2 + floor_log (Suc (length xs div bp_block_size P))))"
  using c_bp_paper_batch_prepend_amortized_paper_bound
      [OF ord distinct disjoint admissible]
  by (simp add: bp_batch_prepend_amortized_budget_paper_form
      bp_batch_prepend_paper_budget_def)

theorem bp_pull_cost_bound:
  assumes inv: "bp_invariant P"
    and can: "bp_can_first_bucket_pull M P"
  shows "bp_pull_amortized_step_bound
    (bp_steps_of (c_bp_paper_pull M B P)) P
    (bp_result_of (c_bp_paper_pull M B P))
    (2 * M)"
  using c_bp_paper_pull_amortized_paper_bound[OF inv can, of B]
  unfolding bp_pull_amortized_budget_def .

text \<open>
  The three theorems above are the exported paper-tight cost bounds for the
  bucketed structure.  @{thm bp_insert_cost_bound} combines a ratio-log bucket
  search with the lazy split potential, giving an amortized Insert budget of a
  constant plus @{const floor_log} of \<open>Suc (N div M)\<close>.  This is the formal
  \<open>log(N/M)\<close> term required by the BMSSP parameter schedule.  The batch theorem
  @{thm bp_batch_prepend_cost_bound} charges the same ratio-log scale per
  incoming item, matching the paper's batched prepend cost.  Finally,
  @{thm bp_pull_cost_bound} gives the amortized linear Pull budget \<open>2 * M\<close>.
  These statements are intentionally stronger and more concrete than the
  abstract cost-interface corollaries: they expose the primitive-step and
  potential accounting that justifies plugging the structure into the
  top-level runtime proof.
\<close>

end
