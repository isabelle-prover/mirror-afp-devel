theory BMSSP_Partition_Pull_Bridge
  imports BMSSP_Pull_Minimum BMSSP_Partition_Interface
begin

section \<open>Partition Pull to BMSSP Pull Minimum\<close>

text \<open>
  The partition interface is graph-independent: it knows about keys and labels,
  but not about shortest-path trees.  BMSSP, on the other hand, phrases a child
  recursive call as a lower split of the current source set by a tentative
  distance bound.  This small bridge theory identifies those two views.

  The conversion is simple but important.  A label function \<open>d\<close> and a source
  set \<open>S\<close> induce a partition view whose keys are exactly \<open>S\<close> and whose
  values are the labels \<open>d\<close>.  A pull from that view is therefore a pull by
  tentative distance.  The theorems below prove that the pulled key set is
  exactly \<open>split_below\<close> at the returned bound, and that the BMSSP
  precondition descends from the parent problem to the child problem selected by
  the pull.

  This file is used twice in the development.  The sorted reference pull uses it
  to justify the executable specification path.  The operational and bucketed
  theories use the abstract @{const pull_separates} statement, so they can
  reason about BMSSP recursion without mentioning the representation of the
  partition data structure.
\<close>

context unique_shortest_digraph
begin

definition label_partition_view where
  "label_partition_view d S = \<lparr>keys_of = S, value_of = d\<rparr>"

lemma label_partition_view_keys [simp]:
  "keys_of (label_partition_view d S) = S"
  unfolding label_partition_view_def by simp

lemma label_partition_view_value [simp]:
  "value_of (label_partition_view d S) = d"
  unfolding label_partition_view_def by simp

text \<open>
  The first two theorems are the semantic translation.  For the sorted reference
  operation, \<open>sorted_pull_set_eq_split_below\<close> unfolds the sorted pull and the
  label partition view to obtain the mathematical lower split.  For any
  implementation satisfying the abstract separator predicate,
  \<open>pull_separates_label_set_eq_split_below\<close> gives the same conclusion from
  @{const pull_separates}.  The latter is the theorem used by the bucketed
  implementation after it proves its pull operation realises the separator
  contract.
\<close>

theorem sorted_pull_set_eq_split_below:
  fixes M :: nat
    and Bmax :: real
  assumes finite_S: "finite S"
    and upper: "\<And>u. u \<in> S \<Longrightarrow> d u < Bmax"
    and D_def: "D = label_partition_view d S"
    and beta_def: "beta = sorted_pull_bound M Bmax D"
  shows "sorted_pull_set M D = split_below d S beta"
proof -
  have "sorted_pull_set M D =
    {u \<in> keys_of D. value_of D u < sorted_pull_bound M Bmax D}"
    using sorted_pull_exact_split[of D Bmax M] finite_S upper
    unfolding D_def by simp
  then show ?thesis
    unfolding D_def beta_def split_below_def by simp
qed

theorem pull_separates_label_set_eq_split_below:
  fixes Bmax :: real
  assumes pull: "pull_separates (label_partition_view d S) M Bmax S' beta D'"
    and upper: "\<And>u. u \<in> S \<Longrightarrow> d u < Bmax"
  shows "S' = split_below d S beta"
proof -
  have "S' =
      {u \<in> keys_of (label_partition_view d S).
        value_of (label_partition_view d S) u < beta}"
    by (rule pull_separates_exact_split[OF pull]) (simp add: upper)
  then show ?thesis
    unfolding split_below_def by simp
qed

theorem sorted_pull_establishes_lower_pre:
  fixes M :: nat
    and Bmax :: real
  assumes pre: "bmssp_pre_full d S (Fin Bmax)"
    and upper: "\<And>u. u \<in> S \<Longrightarrow> d u < Bmax"
    and D_def: "D = label_partition_view d S"
    and S'_def: "S' = sorted_pull_set M D"
    and beta_def: "beta = sorted_pull_bound M Bmax D"
  shows "bmssp_pre_full d S' (Fin beta)"
proof -
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have finite_S: "finite S"
    using finite_subset[OF S_subset finite_V] .
  let ?xs = "partition_key_order D"
  have set_xs: "set ?xs = S"
    using partition_key_order_properties(1)[of D] finite_S
    unfolding D_def by simp
  show ?thesis
  proof (cases "length ?xs \<le> M")
    case True
    have S'_eq: "S' = S"
      using True set_xs unfolding S'_def sorted_pull_set_def by (simp add: Let_def)
    have beta_eq: "beta = Bmax"
      using True unfolding beta_def sorted_pull_bound_def by (simp add: Let_def)
    show ?thesis
      using pre unfolding S'_eq beta_eq .
  next
    case False
    then have M_lt: "M < length ?xs"
      by simp
    have beta_eq: "beta = d (?xs ! M)"
      using False unfolding beta_def sorted_pull_bound_def D_def by (simp add: Let_def)
    have nth_in: "?xs ! M \<in> S"
      using set_xs M_lt nth_mem by metis
    have beta_lt: "beta < Bmax"
      using upper[OF nth_in] beta_eq by simp
    have S'_split: "S' = split_below d S beta"
      using sorted_pull_set_eq_split_below[OF finite_S upper D_def beta_def]
      unfolding S'_def .
    show ?thesis
      unfolding S'_split
      by (rule pull_minimum_pre_for_lower_split[OF pre]) (simp add: beta_lt)
  qed
qed

text \<open>
  The final theorem packages the precondition transfer needed by a recursive
  BMSSP child call.  If the parent problem is valid up to \<open>Bmax\<close> and all
  current source labels lie below \<open>Bmax\<close>, then the set returned by a sorted
  pull is valid up to the returned child bound.  The all-keys case is just the
  parent precondition again; the proper-prefix case uses the pull-minimum lemma
  for lower splits.

  Later operational proofs use this theorem as a template for arbitrary
  partition implementations: once a pull is known to select the same lower
  split, the recursive child precondition follows from the same argument.
\<close>

end

end
