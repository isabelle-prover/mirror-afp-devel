theory BMSSP_Exact_Concrete_Cost
  imports BMSSP_Direct_Insert_Costed BMSSP_Partition_Data_Structure
begin

section \<open>Exact Concrete Cost Runs\<close>

text \<open>
  The existing direct-insert costed run relation records data-structure costs by
  upper-bound predicates.  The relation below is a concrete-cost refinement
  layer: pulls and batch-prepends are performed by the concrete partition state
  operations, whose costs are exact.  Its main theorem shows that every exact
  concrete run is accepted by the existing direct-insert costed relation, so all
  already-proved graph-time bounds apply to such runs.

  Initial insertion is kept as a separate exact initial-state predicate.  It
  records an exact insertion trace and the resulting abstract view; future
  totality work can instantiate it with a concrete enumeration of the pivot set.

  This theory is not the final executable bucketed structure.  It is the bridge
  from abstract cost predicates to concrete partition-state operations.  The
  direct-insert relation says "there exists a pull cost satisfying the pull
  predicate" and similarly for batch costs.  Here those costs are the values
  returned by \<open>costed_partition_state_pull\<close> and
  \<open>costed_partition_state_batch_prepend\<close>.  The refinement theorem then proves
  that these exact operations satisfy the abstract cost relation.

  The file also contains witness lemmas.  They show that an initial partition
  can be built by inserting the pivot set, that terminal loop cases can be
  produced directly, and that nonterminal loop cases can be assembled from one
  concrete pull, one recursive child call, and three concrete batch prepends.
  These witnesses make the concrete-cost layer a useful target for later
  totality or executable-search work, even though the main Track 2 deliverable
  uses the bucketed amortised bounds.
\<close>

inductive exact_partition_state_insert_list ::
  "nat \<Rightarrow> 'k partition_state \<Rightarrow> ('k \<times> real) list \<Rightarrow> nat \<Rightarrow>
    'k partition_state \<Rightarrow> bool" where
  Exact_Insert_List_Nil:
    "exact_partition_state_insert_list t P [] 0 P"
| Exact_Insert_List_Cons:
    "costed_partition_state_insert t P x b c_x P\<^sub>1 \<Longrightarrow>
     exact_partition_state_insert_list t P\<^sub>1 xs c_tail P' \<Longrightarrow>
     c = c_x + c_tail \<Longrightarrow>
     exact_partition_state_insert_list t P ((x, b) # xs) c P'"

text \<open>
  Exact initial insertion is represented as a list trace.  The trace is small
  enough to reason about directly: each element costs exactly \<open>t\<close>, preserves
  the partition invariant, and refines to a minimum-update on the abstract
  partition view.  Building an initial partition from a distinct enumeration of
  the pivot set therefore gives the abstract label partition view expected by
  the BMSSP loop.
\<close>

lemma batch_min_update_append [simp]:
  "batch_min_update (batch_min_update D xs) ys = batch_min_update D (xs @ ys)"
  unfolding batch_min_update_def by simp

lemma exact_partition_state_insert_list_cost:
  assumes "exact_partition_state_insert_list t P xs c P'"
  shows "c = t * length xs"
  using assms
proof (induction)
  case Exact_Insert_List_Nil
  then show ?case
    by simp
next
  case (Exact_Insert_List_Cons t P x b c_x P\<^sub>1 xs c_tail P' c)
  then show ?case
    unfolding costed_partition_state_insert_def by simp
qed

lemma exact_partition_state_insert_list_invar:
  assumes inv: "partition_state_invar P"
    and inserts: "exact_partition_state_insert_list t P xs c P'"
  shows "partition_state_invar P'"
  using inserts inv
proof (induction)
  case (Exact_Insert_List_Nil t P)
  then show ?case
    by simp
next
  case (Exact_Insert_List_Cons t P x b c_x P\<^sub>1 xs c_tail P' c)
  have inv1: "partition_state_invar P\<^sub>1"
    using costed_partition_state_insert_refines
      [OF Exact_Insert_List_Cons.prems Exact_Insert_List_Cons.hyps(1)]
    by blast
  show ?case
    by (rule Exact_Insert_List_Cons.IH[OF inv1])
qed

lemma exact_partition_state_insert_list_batch_prepend:
  "exact_partition_state_insert_list t P xs (t * length xs)
    (partition_state_batch_prepend xs P)"
proof (induction xs arbitrary: P)
  case Nil
  then show ?case
    unfolding partition_state_batch_prepend_def by (simp add: Exact_Insert_List_Nil)
next
  case (Cons xb xs)
  obtain x b where xb: "xb = (x, b)"
    by force
  have step:
    "costed_partition_state_insert t P x b t (partition_state_insert x b P)"
    unfolding costed_partition_state_insert_def by simp
  have tail:
    "exact_partition_state_insert_list t (partition_state_insert x b P) xs
      (t * length xs)
      (partition_state_batch_prepend xs (partition_state_insert x b P))"
    by (rule Cons.IH)
  have run:
    "exact_partition_state_insert_list t P (xb # xs)
      (t + t * length xs)
      (partition_state_batch_prepend xs (partition_state_insert x b P))"
    unfolding xb by (rule Exact_Insert_List_Cons[OF step tail refl])
  then show ?case
    unfolding xb partition_state_batch_prepend_def by simp
qed

context unique_shortest_digraph
begin

lemma batch_min_update_label_pairs_value_disjoint:
  assumes distinct: "distinct xs"
    and disjoint: "set xs \<inter> keys_of D = {}"
  shows "value_of (batch_min_update D (map (\<lambda>x. (x, d x)) xs)) y =
    (if y \<in> set xs then d y else value_of D y)"
  using distinct disjoint
proof (induction xs arbitrary: D y)
  case Nil
  then show ?case
    unfolding batch_min_update_def by simp
next
  case (Cons x xs)
  have x_not_D: "x \<notin> keys_of D"
    using Cons.prems by auto
  have xs_disjoint:
    "set xs \<inter> keys_of (min_update D x (d x)) = {}"
    using Cons.prems unfolding min_update_def by auto
  have tail:
    "value_of
      (batch_min_update (min_update D x (d x))
        (map (\<lambda>x. (x, d x)) xs)) y =
      (if y \<in> set xs then d y else value_of (min_update D x (d x)) y)"
    by (rule Cons.IH) (use Cons.prems xs_disjoint in auto)
  have unfold:
    "batch_min_update D (map (\<lambda>x. (x, d x)) (x # xs)) =
      batch_min_update (min_update D x (d x)) (map (\<lambda>x. (x, d x)) xs)"
    unfolding batch_min_update_def by simp
  show ?case
  proof (cases "y = x")
    case True
    then have "y \<notin> set xs"
      using Cons.prems(1) by simp
    then show ?thesis
      using tail x_not_D True unfolding unfold by (simp add: min_update_def)
  next
    case False
    then show ?thesis
      using tail unfolding unfold by (simp add: min_update_def)
  qed
qed

lemma min_update_label_partition_view_new:
  assumes "x \<notin> S"
  shows "min_update (label_partition_view d S) x (d x) =
    label_partition_view d (insert x S)"
  using assms unfolding min_update_def label_partition_view_def by simp

lemma batch_min_update_label_partition_view_disjoint:
  assumes distinct: "distinct xs"
    and disjoint: "set xs \<inter> S = {}"
  shows "batch_min_update (label_partition_view d S)
      (map (\<lambda>x. (x, d x)) xs) =
    label_partition_view d (S \<union> set xs)"
  using distinct disjoint
proof (induction xs arbitrary: S)
  case Nil
  then show ?case
    unfolding batch_min_update_def label_partition_view_def by simp
next
  case (Cons x xs)
  have x_not_S: "x \<notin> S"
    using Cons.prems by auto
  have xs_disjoint: "set xs \<inter> insert x S = {}"
    using Cons.prems by auto
  have step:
    "min_update (label_partition_view d S) x (d x) =
      label_partition_view d (insert x S)"
    by (rule min_update_label_partition_view_new[OF x_not_S])
  have tail:
    "batch_min_update (label_partition_view d (insert x S))
      (map (\<lambda>x. (x, d x)) xs) =
      label_partition_view d (insert x S \<union> set xs)"
    by (rule Cons.IH) (use Cons.prems xs_disjoint in auto)
  show ?case
    unfolding batch_min_update_def
    using step tail[unfolded batch_min_update_def] by auto
qed

lemma batch_min_update_empty_label_view:
  assumes distinct: "distinct xs"
  shows "batch_min_update (partition_state_view (empty_partition_state d))
      (map (\<lambda>x. (x, d x)) xs) =
    label_partition_view d (set xs)"
proof -
  have empty_view:
    "partition_state_view (empty_partition_state d) = label_partition_view d {}"
    unfolding label_partition_view_def by simp
  have "batch_min_update (partition_state_view (empty_partition_state d))
      (map (\<lambda>x. (x, d x)) xs) =
    batch_min_update (label_partition_view d {}) (map (\<lambda>x. (x, d x)) xs)"
    unfolding empty_view by simp
  also have "\<dots> = label_partition_view d ({} \<union> set xs)"
    by (rule batch_min_update_label_partition_view_disjoint[OF distinct]) simp
  finally show ?thesis
    by simp
qed

definition exact_partition_initial_state where
  "exact_partition_initial_state t d P P\<^sub>D c \<longleftrightarrow>
     partition_state_invar P\<^sub>D \<and>
     partition_state_view P\<^sub>D = label_partition_view d P \<and>
     c = t * card P \<and>
     (\<exists>xs. distinct xs \<and> set xs = P \<and>
       exact_partition_state_insert_list t (empty_partition_state d)
         (map (\<lambda>x. (x, d x)) xs) c P\<^sub>D)"

text \<open>
  The predicate \<open>exact_partition_initial_state\<close> packages the initial build
  phase for a non-base BMSSP call.  It records three facts at once: the concrete
  partition state is well formed, its abstract view is exactly the label view
  of the pivot set, and the build cost is exactly \<open>t * card P\<close>.  The existence
  lemmas below use finite pivot sets to construct such a state by a batch of
  concrete inserts.
\<close>

lemma exact_partition_initial_state_invar:
  assumes "exact_partition_initial_state t d P P\<^sub>D c"
  shows "partition_state_invar P\<^sub>D"
  using assms unfolding exact_partition_initial_state_def by blast

lemma exact_partition_initial_state_view:
  assumes "exact_partition_initial_state t d P P\<^sub>D c"
  shows "partition_state_view P\<^sub>D = label_partition_view d P"
  using assms unfolding exact_partition_initial_state_def by blast

lemma exact_partition_initial_state_cost_bound:
  assumes "exact_partition_initial_state t d P P\<^sub>D c"
  shows "partition_initial_insert_cost_bound c t P"
  using assms unfolding exact_partition_initial_state_def
    partition_initial_insert_cost_bound_def by simp

lemma exact_partition_initial_state_cost:
  assumes "exact_partition_initial_state t d P P\<^sub>D c"
  shows "c = t * card P"
  using assms unfolding exact_partition_initial_state_def by blast

lemma exact_partition_initial_state_exists:
  assumes finite_P: "finite P"
  shows "\<exists>P\<^sub>D c. exact_partition_initial_state t d P P\<^sub>D c"
proof -
  obtain xs where xs: "set xs = P" "distinct xs"
    using finite_distinct_list[OF finite_P] by blast
  let ?pairs = "map (\<lambda>x. (x, d x)) xs"
  let ?P\<^sub>D = "partition_state_batch_prepend ?pairs (empty_partition_state d)"
  let ?c = "t * card P"
  have run:
    "exact_partition_state_insert_list t (empty_partition_state d) ?pairs
      (t * length ?pairs) ?P\<^sub>D"
    by (rule exact_partition_state_insert_list_batch_prepend)
  have len: "length xs = card P"
    using xs finite_P distinct_card by fastforce
  have run_c:
    "exact_partition_state_insert_list t (empty_partition_state d) ?pairs
      ?c ?P\<^sub>D"
    using run len by simp
  have inv: "partition_state_invar ?P\<^sub>D"
    by (rule exact_partition_state_insert_list_invar[OF empty_partition_state_invar run])
  have view: "partition_state_view ?P\<^sub>D = label_partition_view d P"
  proof -
    have "partition_state_view ?P\<^sub>D =
        batch_min_update (partition_state_view (empty_partition_state d)) ?pairs"
      by (rule partition_state_batch_prepend_refines_batch_min_update)
        (rule empty_partition_state_invar)
    also have "\<dots> = label_partition_view d (set xs)"
      by (rule batch_min_update_empty_label_view[OF xs(2)])
    also have "\<dots> = label_partition_view d P"
      using xs(1) by simp
    finally show ?thesis .
  qed
  have "exact_partition_initial_state t d P ?P\<^sub>D ?c"
    unfolding exact_partition_initial_state_def
    using inv view run_c xs by blast
  then show ?thesis
    by blast
qed

lemma exact_partition_initial_state_exists_for_capped_pivots:
  assumes S_subset: "S \<subseteq> V"
  shows "\<exists>P\<^sub>D c. exact_partition_initial_state t
    (find_pivots_label_capped k cap d S B)
    (find_pivots_pivots_capped k cap d S B) P\<^sub>D c"
proof -
  have pivots_subset_V:
    "find_pivots_pivots_capped k cap d S B \<subseteq> V"
    using find_pivots_pivots_capped_subset S_subset by blast
  have finite_pivots: "finite (find_pivots_pivots_capped k cap d S B)"
    by (rule finite_subset[OF pivots_subset_V finite_V])
  show ?thesis
    by (rule exact_partition_initial_state_exists[OF finite_pivots])
qed

lemma exact_partition_initial_state_exists_for_capped_pivots_with_cost:
  assumes S_subset: "S \<subseteq> V"
  shows "\<exists>P\<^sub>D. exact_partition_initial_state t
    (find_pivots_label_capped k cap d S B)
    (find_pivots_pivots_capped k cap d S B) P\<^sub>D
    (t * card (find_pivots_pivots_capped k cap d S B))"
proof -
  have pivots_subset_V:
    "find_pivots_pivots_capped k cap d S B \<subseteq> V"
    using find_pivots_pivots_capped_subset S_subset by blast
  have finite_pivots: "finite (find_pivots_pivots_capped k cap d S B)"
    by (rule finite_subset[OF pivots_subset_V finite_V])
  obtain P\<^sub>D c where init: "exact_partition_initial_state t
    (find_pivots_label_capped k cap d S B)
    (find_pivots_pivots_capped k cap d S B) P\<^sub>D c"
    using exact_partition_initial_state_exists[OF finite_pivots] by blast
  have "c = t * card (find_pivots_pivots_capped k cap d S B)"
    by (rule exact_partition_initial_state_cost[OF init])
  then show ?thesis
    using init by blast
qed

lemma find_pivots_pivots_capped_reaches:
  assumes reaches: "\<forall>x\<in>S. reachable s x"
  shows "\<forall>x\<in>find_pivots_pivots_capped k cap d S B. reachable s x"
  using reaches find_pivots_pivots_capped_subset by blast

lemma find_pivots_pivots_capped_label_less_finite:
  assumes below: "\<And>y. y \<in> S \<Longrightarrow> d y < Bmax"
    and xP: "x \<in> find_pivots_pivots_capped k cap d S (Fin Bmax)"
  shows "find_pivots_label_capped k cap d S (Fin Bmax) x < Bmax"
proof -
  have below_bound: "\<And>y. y \<in> S \<Longrightarrow> below_bound (d y) (Fin Bmax)"
    using below by simp
  have "below_bound (find_pivots_label_capped k cap d S (Fin Bmax) x)
    (Fin Bmax)"
    by (rule find_pivots_pivots_capped_label_below[OF below_bound xP])
  then show ?thesis
    by simp
qed

text \<open>
  The main exact concrete run relation follows the same tree as the direct-
  insert costed relation, but it keeps concrete partition states in the loop.
  A step performs a concrete pull, recursively solves the pulled lower split,
  then performs three concrete batch prepends: direct edge relaxations, lower
  edge relaxations, and source labels.  The accumulated cost is not merely
  bounded by predicates; it is the exact sum of the concrete operation costs,
  the child cost, and the tail-loop cost.

  This exactness is useful for refinement.  The direct-insert relation is the
  mature cost interface used by the graph-time theorems.  By proving that every
  exact concrete run refines to that relation, all existing correctness and
  runtime results become available for the concrete partition-state execution.
\<close>

inductive exact_concrete_partition_loop_state
  and exact_concrete_bmssp where
  Exact_Concrete_State_Done:
    "keys_of (partition_state_view D) = {} \<Longrightarrow>
     bound_le (Fin a) B \<Longrightarrow>
     complete_on d' (bound_tree P B) \<Longrightarrow>
     exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
       [] [] B [range_tree P a B]
       (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a B])) 0 []"
| Exact_Concrete_State_Stop:
    "bound_le (Fin a) B \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     k * cap \<le> card (bound_tree P (Fin a)) \<Longrightarrow>
     exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
       [] [] (Fin a) [range_tree P a (Fin a)]
       (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a (Fin a)])) 0 []"
| Exact_Concrete_State_Step:
    "partition_state_invar D \<Longrightarrow>
     partition_upper_bound (partition_state_view D) Bmax \<Longrightarrow>
     costed_partition_state_pull (M_of l) Bmax D S_pull beta D_pull c_pull \<Longrightarrow>
     bound_le (Fin beta) B \<Longrightarrow>
     bmssp_pre_full d S_pull (Fin beta) \<Longrightarrow>
     S_pull = split_below d P beta \<Longrightarrow>
     (\<forall>x\<in>S_pull. reachable s x) \<Longrightarrow>
     a \<le> b \<Longrightarrow>
     bound_le (Fin a) B' \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     card (bound_tree P (Fin a)) < k * cap \<Longrightarrow>
     exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
       d_child (Fin b) U_child c_child \<Longrightarrow>
     U_child = range_tree P a (Fin b) \<Longrightarrow>
     complete_preserved d_child d' U_child \<Longrightarrow>
     direct_edge_batch = edge_relaxation_pairs_in_bound d_child U_child beta B \<Longrightarrow>
     lower_edge_batch = edge_relaxation_pairs_between d_child U_child b beta \<Longrightarrow>
     source_batch = label_pairs_between d S_pull b beta \<Longrightarrow>
     costed_partition_state_batch_prepend t D_pull direct_edge_batch c_direct D_direct \<Longrightarrow>
     costed_partition_state_batch_prepend h D_direct lower_edge_batch c_lower D_lower \<Longrightarrow>
     costed_partition_state_batch_prepend h D_lower source_batch c_sources D_next \<Longrightarrow>
     exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d'
       D_next b betas bs B' Us_tail U_tail c_tail child_costs_tail \<Longrightarrow>
     c = c_pull + c_direct + c_lower + c_sources + c_child + c_tail \<Longrightarrow>
     exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
       (beta # betas) (b # bs) B'
       (range_tree P a (Fin b) # Us_tail)
       (bound_tree P (Fin a) \<union>
        \<Union>(set (range_tree P a (Fin b) # Us_tail))) c
       (c_child # child_costs_tail)"
| Exact_Concrete_Base:
    "S = {x} \<Longrightarrow>
     exact_concrete_bmssp \<Delta> M_of t h k cap 0 d S B
       (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
       (base_case_bound k x B)
       (base_case_vertices k x B)
       (base_case_scan_cost \<Delta> k x B)"
| Exact_Concrete_Step:
    "exact_partition_initial_state t
       (find_pivots_label_capped k cap d S B)
       (find_pivots_pivots_capped k cap d S B) D c_insert \<Longrightarrow>
     exact_concrete_partition_loop_state \<Delta> M_of t h k cap l
       (find_pivots_label_capped k cap d S B)
       (find_pivots_pivots_capped k cap d S B) B d' D a
       betas bs B' Us U_loop c_loop child_costs_loop \<Longrightarrow>
     complete_on d'
       {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
     U = U_loop \<union>
       {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
     c = fp_iter_capped_scan_cost k cap d S S B + c_insert + c_loop \<Longrightarrow>
     exact_concrete_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"

inductive_cases exact_concrete_bmssp_zeroE:
  "exact_concrete_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"

inductive_cases exact_concrete_bmssp_SucE:
  "exact_concrete_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"

lemma exact_partition_initial_state_cost_unique:
  assumes "exact_partition_initial_state t d P P\<^sub>D c"
    and "exact_partition_initial_state t d P P\<^sub>D' c'"
  shows "c = c'"
  using exact_partition_initial_state_cost[OF assms(1)]
    exact_partition_initial_state_cost[OF assms(2)]
  by simp

lemma exact_partition_initial_state_upper_bound:
  assumes init: "exact_partition_initial_state t d P P\<^sub>D c"
    and upper: "\<And>u. u \<in> P \<Longrightarrow> d u < B"
  shows "partition_upper_bound (partition_state_view P\<^sub>D) B"
  using exact_partition_initial_state_view[OF init] upper
  unfolding partition_upper_bound_def by simp

lemma exact_partition_initial_state_pull_split:
  assumes init: "exact_partition_initial_state t d P P\<^sub>D c"
    and upper: "\<And>u. u \<in> P \<Longrightarrow> d u < B"
    and pull: "partition_state_pull M B P\<^sub>D = (S_pull, beta, P\<^sub>D')"
  shows "S_pull = split_below d P beta"
proof -
  have inv: "partition_state_invar P\<^sub>D"
    by (rule exact_partition_initial_state_invar[OF init])
  have view: "partition_state_view P\<^sub>D = label_partition_view d P"
    by (rule exact_partition_initial_state_view[OF init])
  show ?thesis
    by (rule partition_state_pull_label_set_eq_split_below
      [OF inv view upper pull])
qed

lemma exact_partition_initial_state_pull_exact_data:
  assumes init: "exact_partition_initial_state t d P P\<^sub>D c"
    and pre: "bmssp_pre_full d P (Fin B)"
    and upper: "\<And>u. u \<in> P \<Longrightarrow> d u < B"
    and pull: "partition_state_pull M B P\<^sub>D = (S_pull, beta, P\<^sub>D')"
  shows "costed_partition_state_pull M B P\<^sub>D S_pull beta P\<^sub>D' (card S_pull) \<and>
    S_pull = split_below d P beta \<and>
    bmssp_pre_full d S_pull (Fin beta) \<and>
    partition_state_invar P\<^sub>D'"
proof -
  have inv: "partition_state_invar P\<^sub>D"
    by (rule exact_partition_initial_state_invar[OF init])
  have view: "partition_state_view P\<^sub>D = label_partition_view d P"
    by (rule exact_partition_initial_state_view[OF init])
  have costed:
    "costed_partition_state_pull M B P\<^sub>D S_pull beta P\<^sub>D' (card S_pull)"
    using pull unfolding costed_partition_state_pull_def by simp
  have split: "S_pull = split_below d P beta"
    by (rule partition_state_pull_label_set_eq_split_below
      [OF inv view upper pull])
  have lower_pre: "bmssp_pre_full d S_pull (Fin beta)"
    by (rule partition_state_pull_establishes_lower_pre
      [OF inv view pre upper pull])
  have inv': "partition_state_invar P\<^sub>D'"
    by (rule partition_state_pull_invar[OF inv pull])
  show ?thesis
    using costed split lower_pre inv' by blast
qed

lemma exact_partition_initial_state_pull_reaches:
  assumes init: "exact_partition_initial_state t d P P\<^sub>D c"
    and upper: "\<And>u. u \<in> P \<Longrightarrow> d u < B"
    and pull: "partition_state_pull M B P\<^sub>D = (S_pull, beta, P\<^sub>D')"
    and P_reaches: "\<forall>x\<in>P. reachable s x"
  shows "\<forall>x\<in>S_pull. reachable s x"
proof -
  have "S_pull = split_below d P beta"
    by (rule exact_partition_initial_state_pull_split[OF init upper pull])
  then show ?thesis
    using P_reaches unfolding split_below_def by blast
qed

lemma exact_partition_initial_state_pull_beta_bound:
  assumes init: "exact_partition_initial_state t d P P\<^sub>D c"
    and upper: "\<And>u. u \<in> P \<Longrightarrow> d u < B"
    and pull: "partition_state_pull M B P\<^sub>D = (S_pull, beta, P\<^sub>D')"
  shows "bound_le (Fin beta) (Fin B)"
proof -
  have inv: "partition_state_invar P\<^sub>D"
    by (rule exact_partition_initial_state_invar[OF init])
  have view: "partition_state_view P\<^sub>D = label_partition_view d P"
    by (rule exact_partition_initial_state_view[OF init])
  have upper_D: "partition_upper_bound (partition_state_view P\<^sub>D) B"
    by (rule exact_partition_initial_state_upper_bound[OF init upper])
  have pull_sep:
    "pull_separates (partition_state_view P\<^sub>D) M B S_pull beta
      (partition_state_view P\<^sub>D')"
  proof (rule partition_state_pull_refines_pull_separates[OF inv _ pull])
    fix u
    assume "u \<in> keys_of (partition_state_view P\<^sub>D)"
    then show "value_of (partition_state_view P\<^sub>D) u < B"
      using upper unfolding view by simp
  qed
  have "beta \<le> B"
    by (rule pull_separates_bound_le[OF pull_sep upper_D])
  then show ?thesis
    by simp
qed

text \<open>
  The pull lemmas are the local bridge from a concrete partition state to the
  BMSSP child problem.  Starting from an exact initial state, a concrete pull
  refines to \<open>pull_separates\<close> on the abstract label partition view.  Therefore
  the pulled source set is exactly \<open>split_below d P beta\<close>, it inherits the
  child BMSSP precondition, and its vertices remain reachable.  These are the
  premises required by the recursive exact concrete step.
\<close>

lemma exact_partition_initial_state_exists_with_cost:
  assumes finite_P: "finite P"
  shows "\<exists>P\<^sub>D. exact_partition_initial_state t d P P\<^sub>D (t * card P)"
proof -
  obtain P\<^sub>D c where init: "exact_partition_initial_state t d P P\<^sub>D c"
    using exact_partition_initial_state_exists[OF finite_P] by blast
  have "c = t * card P"
    by (rule exact_partition_initial_state_cost[OF init])
  then show ?thesis
    using init by blast
qed

lemma exact_concrete_bmssp_base_exists:
  assumes "S = {x}"
  shows "exact_concrete_bmssp \<Delta> M_of t h k cap 0 d S B
    (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
    (base_case_bound k x B)
    (base_case_vertices k x B)
    (base_case_scan_cost \<Delta> k x B)"
  by (rule Exact_Concrete_Base[OF assms])

lemma exact_concrete_bmssp_zero_singletonD:
  assumes run: "exact_concrete_bmssp \<Delta> M_of t h k cap 0 d {x} B d' B' U c"
  shows "d' =
      (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v) \<and>
    B' = base_case_bound k x B \<and>
    U = base_case_vertices k x B \<and>
    c = base_case_scan_cost \<Delta> k x B"
  using run by cases auto

lemma exact_concrete_bmssp_zero_singleton_cost_unique:
  assumes run: "exact_concrete_bmssp \<Delta> M_of t h k cap 0 d {x} B d' B' U c"
    and run': "exact_concrete_bmssp \<Delta> M_of t h k cap 0 d {x} B d'' B'' U' c'"
  shows "c = c'"
  using exact_concrete_bmssp_zero_singletonD[OF run]
    exact_concrete_bmssp_zero_singletonD[OF run']
  by simp

lemma exact_concrete_bmssp_zeroD:
  assumes run: "exact_concrete_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
  shows "\<exists>x. S = {x} \<and>
    d' = (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v) \<and>
    B' = base_case_bound k x B \<and>
    U = base_case_vertices k x B \<and>
    c = base_case_scan_cost \<Delta> k x B"
  using run
proof cases
  case (Exact_Concrete_Base x)
  then show ?thesis
    by blast
qed

lemma exact_concrete_bmssp_zero_deterministic:
  assumes run: "exact_concrete_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
    and run': "exact_concrete_bmssp \<Delta> M_of t h k cap 0 d S B d'' B'' U' c'"
  shows "d' = d'' \<and> B' = B'' \<and> U = U' \<and> c = c'"
proof -
  obtain x where x:
    "S = {x}"
    "d' = (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)"
    "B' = base_case_bound k x B"
    "U = base_case_vertices k x B"
    "c = base_case_scan_cost \<Delta> k x B"
    using exact_concrete_bmssp_zeroD[OF run] by blast
  obtain y where y:
    "S = {y}"
    "d'' = (\<lambda>v. if v \<in> base_case_vertices k y B then dist s v else d v)"
    "B'' = base_case_bound k y B"
    "U' = base_case_vertices k y B"
    "c' = base_case_scan_cost \<Delta> k y B"
    using exact_concrete_bmssp_zeroD[OF run'] by blast
  have "x = y"
    using x(1) y(1) by simp
  then show ?thesis
    using x y by simp
qed

lemma exact_concrete_bmssp_zero_exists_iff_singleton:
  "(\<exists>d' B' U c. exact_concrete_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c)
    \<longleftrightarrow> (\<exists>x. S = {x})"
proof
  assume "\<exists>d' B' U c.
    exact_concrete_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
  then obtain d' B' U c where
    run: "exact_concrete_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
    by blast
  obtain x where "S = {x}"
    using exact_concrete_bmssp_zeroD[OF run] by blast
  then show "\<exists>x. S = {x}"
    by blast
next
  assume "\<exists>x. S = {x}"
  then obtain x where "S = {x}"
    by blast
  then show "\<exists>d' B' U c.
    exact_concrete_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
    by (intro exI) (rule exact_concrete_bmssp_base_exists)
qed

lemma complete_on_dist:
  "complete_on (dist s) U"
  unfolding complete_on_def by simp

lemma exact_concrete_partition_loop_state_done_witness:
  assumes empty: "keys_of (partition_state_view D) = {}"
    and a_bound: "bound_le (Fin a) B"
    and complete: "complete_on d' (bound_tree P B)"
  shows "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d'
    D a [] [] B [range_tree P a B]
    (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a B])) 0 []"
  by (rule Exact_Concrete_State_Done[OF empty a_bound complete])

lemma exact_concrete_partition_loop_state_stop_witness:
  assumes a_bound: "bound_le (Fin a) B"
    and complete: "complete_on d' (bound_tree P (Fin a))"
    and threshold: "k * cap \<le> card (bound_tree P (Fin a))"
  shows "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d'
    D a [] [] (Fin a) [range_tree P a (Fin a)]
    (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a (Fin a)])) 0 []"
  by (rule Exact_Concrete_State_Stop[OF a_bound complete threshold])

lemma exact_concrete_partition_loop_state_done_exists:
  assumes empty: "keys_of (partition_state_view D) = {}"
    and a_bound: "bound_le (Fin a) B"
    and complete: "complete_on d' (bound_tree P B)"
  shows "\<exists>betas bs B' Us U c child_costs.
    exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d'
      D a betas bs B' Us U c child_costs"
proof -
  have run:
    "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d'
      D a [] [] B [range_tree P a B]
      (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a B])) 0 []"
    by (rule exact_concrete_partition_loop_state_done_witness
      [OF empty a_bound complete])
  then show ?thesis
    by blast
qed

lemma exact_concrete_partition_loop_state_stop_exists:
  assumes a_bound: "bound_le (Fin a) B"
    and complete: "complete_on d' (bound_tree P (Fin a))"
    and threshold: "k * cap \<le> card (bound_tree P (Fin a))"
  shows "\<exists>betas bs B' Us U c child_costs.
    exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d'
      D a betas bs B' Us U c child_costs"
proof -
  have run:
    "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d'
      D a [] [] (Fin a) [range_tree P a (Fin a)]
      (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a (Fin a)])) 0 []"
    by (rule exact_concrete_partition_loop_state_stop_witness
      [OF a_bound complete threshold])
  then show ?thesis
    by blast
qed

lemma exact_concrete_partition_loop_state_step_from_concrete_ops:
  assumes inv_D: "partition_state_invar D"
    and upper_D: "partition_upper_bound (partition_state_view D) Bmax"
    and pull:
      "partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull)"
    and beta_bound: "bound_le (Fin beta) B"
    and child_pre: "bmssp_pre_full d S_pull (Fin beta)"
    and S_pull_def: "S_pull = split_below d P beta"
    and S_pull_reaches: "\<forall>x\<in>S_pull. reachable s x"
    and a_le_b: "a \<le> b"
    and a_bound: "bound_le (Fin a) B'"
    and complete_prefix: "complete_on d' (bound_tree P (Fin a))"
    and below_threshold: "card (bound_tree P (Fin a)) < k * cap"
    and child:
      "exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
        d_child (Fin b) U_child c_child"
    and U_child: "U_child = range_tree P a (Fin b)"
    and preserved: "complete_preserved d_child d' U_child"
    and tail:
      "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d'
        (partition_state_batch_prepend (label_pairs_between d S_pull b beta)
          (partition_state_batch_prepend
            (edge_relaxation_pairs_between d_child U_child b beta)
            (partition_state_batch_prepend
              (edge_relaxation_pairs_in_bound d_child U_child beta B)
              D_pull)))
        b betas bs B' Us_tail U_tail c_tail child_costs_tail"
  shows "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
    (beta # betas) (b # bs) B'
    (range_tree P a (Fin b) # Us_tail)
    (bound_tree P (Fin a) \<union>
      \<Union>(set (range_tree P a (Fin b) # Us_tail)))
    (card S_pull +
      t * length (edge_relaxation_pairs_in_bound d_child U_child beta B) +
      h * length (edge_relaxation_pairs_between d_child U_child b beta) +
      h * length (label_pairs_between d S_pull b beta) +
      c_child + c_tail)
    (c_child # child_costs_tail)"
proof -
  let ?direct = "edge_relaxation_pairs_in_bound d_child U_child beta B"
  let ?lower = "edge_relaxation_pairs_between d_child U_child b beta"
  let ?sources = "label_pairs_between d S_pull b beta"
  let ?D_direct = "partition_state_batch_prepend ?direct D_pull"
  let ?D_lower = "partition_state_batch_prepend ?lower ?D_direct"
  let ?D_next = "partition_state_batch_prepend ?sources ?D_lower"
  have pull_op:
    "costed_partition_state_pull (M_of l) Bmax D S_pull beta D_pull
      (card S_pull)"
    using pull unfolding costed_partition_state_pull_def by simp
  have direct_op:
    "costed_partition_state_batch_prepend t D_pull ?direct
      (t * length ?direct) ?D_direct"
    unfolding costed_partition_state_batch_prepend_def by simp
  have lower_op:
    "costed_partition_state_batch_prepend h ?D_direct ?lower
      (h * length ?lower) ?D_lower"
    unfolding costed_partition_state_batch_prepend_def by simp
  have source_op:
    "costed_partition_state_batch_prepend h ?D_lower ?sources
      (h * length ?sources) ?D_next"
    unfolding costed_partition_state_batch_prepend_def by simp
  show ?thesis
    by (rule Exact_Concrete_State_Step
      [OF inv_D upper_D pull_op beta_bound child_pre S_pull_def
        S_pull_reaches a_le_b a_bound complete_prefix below_threshold child
        U_child preserved refl refl refl direct_op lower_op source_op tail])
      simp
qed

text \<open>
  The witness lemmas turn concrete operations into one exact loop step.  The
  most explicit version assumes the concrete pull and the concrete tail state
  are already known, then constructs the exact step and computes its cost.  The
  initialized version derives the pull split and child precondition from
  \<open>exact_partition_initial_state\<close>.  Later existence lemmas use these builders
  to cover the terminal, threshold, and recursive cases of a non-base call.
\<close>

lemma exact_concrete_initialized_partition_loop_state_step:
  assumes init: "exact_partition_initial_state t d P D c_insert"
    and pre: "bmssp_pre_full d P (Fin Bmax)"
    and upper: "\<And>u. u \<in> P \<Longrightarrow> d u < Bmax"
    and pull: "partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull)"
    and beta_bound: "bound_le (Fin beta) B"
    and S_pull_reaches: "\<forall>x\<in>S_pull. reachable s x"
    and a_le_b: "a \<le> b"
    and a_bound: "bound_le (Fin a) B'"
    and complete_prefix: "complete_on d' (bound_tree P (Fin a))"
    and below_threshold: "card (bound_tree P (Fin a)) < k * cap"
    and child:
      "exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
        d_child (Fin b) U_child c_child"
    and U_child: "U_child = range_tree P a (Fin b)"
    and preserved: "complete_preserved d_child d' U_child"
    and tail:
      "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d'
        (partition_state_batch_prepend (label_pairs_between d S_pull b beta)
          (partition_state_batch_prepend
            (edge_relaxation_pairs_between d_child U_child b beta)
            (partition_state_batch_prepend
              (edge_relaxation_pairs_in_bound d_child U_child beta B)
              D_pull)))
        b betas bs B' Us_tail U_tail c_tail child_costs_tail"
  shows "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
    (beta # betas) (b # bs) B'
    (range_tree P a (Fin b) # Us_tail)
    (bound_tree P (Fin a) \<union>
      \<Union>(set (range_tree P a (Fin b) # Us_tail)))
    (card S_pull +
      t * length (edge_relaxation_pairs_in_bound d_child U_child beta B) +
      h * length (edge_relaxation_pairs_between d_child U_child b beta) +
      h * length (label_pairs_between d S_pull b beta) +
      c_child + c_tail)
    (c_child # child_costs_tail)"
proof -
  have inv_D: "partition_state_invar D"
    by (rule exact_partition_initial_state_invar[OF init])
  have upper_D: "partition_upper_bound (partition_state_view D) Bmax"
    by (rule exact_partition_initial_state_upper_bound[OF init upper])
  have pull_data:
    "costed_partition_state_pull (M_of l) Bmax D S_pull beta D_pull
        (card S_pull) \<and>
     S_pull = split_below d P beta \<and>
     bmssp_pre_full d S_pull (Fin beta) \<and>
     partition_state_invar D_pull"
    by (rule exact_partition_initial_state_pull_exact_data
      [OF init pre upper pull])
  have child_pre: "bmssp_pre_full d S_pull (Fin beta)"
    using pull_data by blast
  have S_pull_def: "S_pull = split_below d P beta"
    using pull_data by blast
  show ?thesis
    by (rule exact_concrete_partition_loop_state_step_from_concrete_ops
      [OF inv_D upper_D pull beta_bound child_pre S_pull_def
        S_pull_reaches a_le_b a_bound complete_prefix below_threshold child
        U_child preserved tail])
qed

lemma partition_state_pull_three_batch_prepend_invar:
  assumes inv: "partition_state_invar D"
    and pull: "partition_state_pull M B D = (S_pull, beta, D_pull)"
  shows "partition_state_invar
    (partition_state_batch_prepend zs
      (partition_state_batch_prepend ys
        (partition_state_batch_prepend xs D_pull)))"
proof -
  have inv_pull: "partition_state_invar D_pull"
    by (rule partition_state_pull_invar[OF inv pull])
  have inv_xs: "partition_state_invar (partition_state_batch_prepend xs D_pull)"
    by (rule partition_state_batch_prepend_invar[OF inv_pull])
  have inv_ys:
    "partition_state_invar
      (partition_state_batch_prepend ys
        (partition_state_batch_prepend xs D_pull))"
    by (rule partition_state_batch_prepend_invar[OF inv_xs])
  show ?thesis
    by (rule partition_state_batch_prepend_invar[OF inv_ys])
qed

lemma exact_concrete_initialized_partition_loop_state_step_exists:
  assumes init: "exact_partition_initial_state t d P D c_insert"
    and pre: "bmssp_pre_full d P (Fin Bmax)"
    and upper: "\<And>u. u \<in> P \<Longrightarrow> d u < Bmax"
    and pull: "partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull)"
    and beta_bound: "bound_le (Fin beta) B"
    and S_pull_reaches: "\<forall>x\<in>S_pull. reachable s x"
    and a_le_b: "a \<le> b"
    and a_bound: "bound_le (Fin a) B'"
    and complete_prefix: "complete_on d' (bound_tree P (Fin a))"
    and below_threshold: "card (bound_tree P (Fin a)) < k * cap"
    and child:
      "exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
        d_child (Fin b) U_child c_child"
    and U_child: "U_child = range_tree P a (Fin b)"
    and preserved: "complete_preserved d_child d' U_child"
    and tail:
      "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d'
        (partition_state_batch_prepend (label_pairs_between d S_pull b beta)
          (partition_state_batch_prepend
            (edge_relaxation_pairs_between d_child U_child b beta)
            (partition_state_batch_prepend
              (edge_relaxation_pairs_in_bound d_child U_child beta B)
              D_pull)))
        b betas bs B' Us_tail U_tail c_tail child_costs_tail"
  shows "\<exists>c child_costs.
    exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      (beta # betas) (b # bs) B'
      (range_tree P a (Fin b) # Us_tail)
      (bound_tree P (Fin a) \<union>
        \<Union>(set (range_tree P a (Fin b) # Us_tail))) c child_costs"
proof -
  have run:
    "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      (beta # betas) (b # bs) B'
      (range_tree P a (Fin b) # Us_tail)
      (bound_tree P (Fin a) \<union>
        \<Union>(set (range_tree P a (Fin b) # Us_tail)))
      (card S_pull +
        t * length (edge_relaxation_pairs_in_bound d_child U_child beta B) +
        h * length (edge_relaxation_pairs_between d_child U_child b beta) +
        h * length (label_pairs_between d S_pull b beta) +
        c_child + c_tail)
      (c_child # child_costs_tail)"
    by (rule exact_concrete_initialized_partition_loop_state_step
      [OF init pre upper pull beta_bound S_pull_reaches a_le_b a_bound
        complete_prefix below_threshold child U_child preserved tail])
  show ?thesis
    using run by blast
qed

lemma exact_concrete_initialized_partition_loop_state_step_exists_finite_bound:
  assumes init: "exact_partition_initial_state t d P D c_insert"
    and pre: "bmssp_pre_full d P (Fin Bmax)"
    and upper: "\<And>u. u \<in> P \<Longrightarrow> d u < Bmax"
    and pull: "partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull)"
    and P_reaches: "\<forall>x\<in>P. reachable s x"
    and a_le_b: "a \<le> b"
    and a_bound: "bound_le (Fin a) B'"
    and complete_prefix: "complete_on d' (bound_tree P (Fin a))"
    and below_threshold: "card (bound_tree P (Fin a)) < k * cap"
    and child:
      "exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
        d_child (Fin b) (range_tree P a (Fin b)) c_child"
    and preserved:
      "complete_preserved d_child d' (range_tree P a (Fin b))"
    and tail:
      "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
        (Fin Bmax) d'
        (partition_state_batch_prepend (label_pairs_between d S_pull b beta)
          (partition_state_batch_prepend
            (edge_relaxation_pairs_between d_child
              (range_tree P a (Fin b)) b beta)
            (partition_state_batch_prepend
              (edge_relaxation_pairs_in_bound d_child
                (range_tree P a (Fin b)) beta (Fin Bmax))
              D_pull)))
        b betas bs B' Us_tail U_tail c_tail child_costs_tail"
  shows "\<exists>c child_costs.
    exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
      (Fin Bmax) d' D a (beta # betas) (b # bs) B'
      (range_tree P a (Fin b) # Us_tail)
      (bound_tree P (Fin a) \<union>
        \<Union>(set (range_tree P a (Fin b) # Us_tail))) c child_costs"
proof -
  have beta_bound: "bound_le (Fin beta) (Fin Bmax)"
    by (rule exact_partition_initial_state_pull_beta_bound[OF init upper pull])
  have S_pull_reaches: "\<forall>x\<in>S_pull. reachable s x"
    by (rule exact_partition_initial_state_pull_reaches
      [OF init upper pull P_reaches])
  show ?thesis
    by (rule exact_concrete_initialized_partition_loop_state_step_exists
      [OF init pre upper pull beta_bound S_pull_reaches a_le_b a_bound
        complete_prefix below_threshold child refl preserved tail])
qed

lemma exact_concrete_initialized_partition_loop_state_nonterminal_exists:
  assumes init: "exact_partition_initial_state t d P D c_insert"
    and pre: "bmssp_pre_full d P (Fin Bmax)"
    and upper: "\<And>u. u \<in> P \<Longrightarrow> d u < Bmax"
    and pull: "partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull)"
    and beta_bound: "bound_le (Fin beta) B"
    and P_reaches: "\<forall>x\<in>P. reachable s x"
    and complete_prefix: "complete_on d' (bound_tree P (Fin a))"
    and below_threshold: "card (bound_tree P (Fin a)) < k * cap"
    and step:
      "\<exists>d_child b c_child betas bs B' Us_tail U_tail c_tail
          child_costs_tail.
        a \<le> b \<and>
        bound_le (Fin a) B' \<and>
        exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
          d_child (Fin b) (range_tree P a (Fin b)) c_child \<and>
        complete_preserved d_child d' (range_tree P a (Fin b)) \<and>
        exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d'
          (partition_state_batch_prepend (label_pairs_between d S_pull b beta)
            (partition_state_batch_prepend
              (edge_relaxation_pairs_between d_child
                (range_tree P a (Fin b)) b beta)
              (partition_state_batch_prepend
                (edge_relaxation_pairs_in_bound d_child
                  (range_tree P a (Fin b)) beta B)
                D_pull)))
          b betas bs B' Us_tail U_tail c_tail child_costs_tail"
  shows "\<exists>betas bs B' Us U c child_costs.
    exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d'
      D a betas bs B' Us U c child_costs"
proof -
  have S_pull_reaches: "\<forall>x\<in>S_pull. reachable s x"
    by (rule exact_partition_initial_state_pull_reaches
      [OF init upper pull P_reaches])
  obtain d_child b c_child betas bs B' Us_tail U_tail c_tail
      child_costs_tail where
    a_le_b: "a \<le> b"
    and a_bound: "bound_le (Fin a) B'"
    and child:
      "exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
        d_child (Fin b) (range_tree P a (Fin b)) c_child"
    and preserved:
      "complete_preserved d_child d' (range_tree P a (Fin b))"
    and tail:
      "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d'
        (partition_state_batch_prepend (label_pairs_between d S_pull b beta)
          (partition_state_batch_prepend
            (edge_relaxation_pairs_between d_child
              (range_tree P a (Fin b)) b beta)
            (partition_state_batch_prepend
              (edge_relaxation_pairs_in_bound d_child
                (range_tree P a (Fin b)) beta B)
              D_pull)))
        b betas bs B' Us_tail U_tail c_tail child_costs_tail"
    using step by blast
  have run:
    "\<exists>c child_costs.
      exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d'
        D a (beta # betas) (b # bs) B'
        (range_tree P a (Fin b) # Us_tail)
        (bound_tree P (Fin a) \<union>
          \<Union>(set (range_tree P a (Fin b) # Us_tail))) c child_costs"
    by (rule exact_concrete_initialized_partition_loop_state_step_exists
      [OF init pre upper pull beta_bound S_pull_reaches a_le_b a_bound
        complete_prefix below_threshold child refl preserved tail])
  then show ?thesis
    by blast
qed

lemma exact_concrete_initialized_partition_loop_state_nonterminal_exists_finite_bound:
  assumes init: "exact_partition_initial_state t d P D c_insert"
    and pre: "bmssp_pre_full d P (Fin Bmax)"
    and upper: "\<And>u. u \<in> P \<Longrightarrow> d u < Bmax"
    and pull: "partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull)"
    and P_reaches: "\<forall>x\<in>P. reachable s x"
    and complete_prefix: "complete_on d' (bound_tree P (Fin a))"
    and below_threshold: "card (bound_tree P (Fin a)) < k * cap"
    and step:
      "\<exists>d_child b c_child betas bs B' Us_tail U_tail c_tail
          child_costs_tail.
        a \<le> b \<and>
        bound_le (Fin a) B' \<and>
        exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
          d_child (Fin b) (range_tree P a (Fin b)) c_child \<and>
        complete_preserved d_child d' (range_tree P a (Fin b)) \<and>
        exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
          (Fin Bmax) d'
          (partition_state_batch_prepend (label_pairs_between d S_pull b beta)
            (partition_state_batch_prepend
              (edge_relaxation_pairs_between d_child
                (range_tree P a (Fin b)) b beta)
              (partition_state_batch_prepend
                (edge_relaxation_pairs_in_bound d_child
                  (range_tree P a (Fin b)) beta (Fin Bmax))
                D_pull)))
          b betas bs B' Us_tail U_tail c_tail child_costs_tail"
  shows "\<exists>betas bs B' Us U c child_costs.
    exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
      (Fin Bmax) d' D a betas bs B' Us U c child_costs"
proof (rule exact_concrete_initialized_partition_loop_state_nonterminal_exists
    [OF init pre upper pull _ P_reaches complete_prefix below_threshold step])
  show "bound_le (Fin beta) (Fin Bmax)"
    by (rule exact_partition_initial_state_pull_beta_bound[OF init upper pull])
qed

lemma exact_concrete_initialized_partition_loop_state_cases_exists_finite_bound:
  assumes init: "exact_partition_initial_state t d P D c_insert"
    and pre: "bmssp_pre_full d P (Fin Bmax)"
    and upper: "\<And>u. u \<in> P \<Longrightarrow> d u < Bmax"
    and P_reaches: "\<forall>x\<in>P. reachable s x"
    and cases:
      "(keys_of (partition_state_view D) = {} \<and>
        bound_le (Fin a) (Fin Bmax) \<and>
        complete_on d' (bound_tree P (Fin Bmax))) \<or>
       (bound_le (Fin a) (Fin Bmax) \<and>
        complete_on d' (bound_tree P (Fin a)) \<and>
        k * cap \<le> card (bound_tree P (Fin a))) \<or>
       (\<exists>S_pull beta D_pull.
        partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull) \<and>
        complete_on d' (bound_tree P (Fin a)) \<and>
        card (bound_tree P (Fin a)) < k * cap \<and>
        (\<exists>d_child b c_child betas bs B' Us_tail U_tail c_tail
            child_costs_tail.
          a \<le> b \<and>
          bound_le (Fin a) B' \<and>
          exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
            d_child (Fin b) (range_tree P a (Fin b)) c_child \<and>
          complete_preserved d_child d' (range_tree P a (Fin b)) \<and>
          exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
            (Fin Bmax) d'
            (partition_state_batch_prepend
              (label_pairs_between d S_pull b beta)
              (partition_state_batch_prepend
                (edge_relaxation_pairs_between d_child
                  (range_tree P a (Fin b)) b beta)
                (partition_state_batch_prepend
                  (edge_relaxation_pairs_in_bound d_child
                    (range_tree P a (Fin b)) beta (Fin Bmax))
                  D_pull)))
            b betas bs B' Us_tail U_tail c_tail child_costs_tail))"
  shows "\<exists>betas bs B' Us U c child_costs.
  exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
      (Fin Bmax) d' D a betas bs B' Us U c child_costs"
proof -
  consider
    (Done_Case) "keys_of (partition_state_view D) = {}"
      "bound_le (Fin a) (Fin Bmax)"
      "complete_on d' (bound_tree P (Fin Bmax))"
  | (Stop_Case) "bound_le (Fin a) (Fin Bmax)"
      "complete_on d' (bound_tree P (Fin a))"
      "k * cap \<le> card (bound_tree P (Fin a))"
  | (Step_Case) S_pull beta D_pull where
      "partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull)"
      "complete_on d' (bound_tree P (Fin a))"
      "card (bound_tree P (Fin a)) < k * cap"
      "\<exists>d_child b c_child betas bs B' Us_tail U_tail c_tail
          child_costs_tail.
        a \<le> b \<and>
        bound_le (Fin a) B' \<and>
        exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
          d_child (Fin b) (range_tree P a (Fin b)) c_child \<and>
        complete_preserved d_child d' (range_tree P a (Fin b)) \<and>
        exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
          (Fin Bmax) d'
          (partition_state_batch_prepend (label_pairs_between d S_pull b beta)
            (partition_state_batch_prepend
              (edge_relaxation_pairs_between d_child
                (range_tree P a (Fin b)) b beta)
              (partition_state_batch_prepend
                (edge_relaxation_pairs_in_bound d_child
                  (range_tree P a (Fin b)) beta (Fin Bmax))
                D_pull)))
          b betas bs B' Us_tail U_tail c_tail child_costs_tail"
    using cases by blast
  then show ?thesis
  proof cases
    case Done_Case
    show ?thesis
      by (rule exact_concrete_partition_loop_state_done_exists
        [OF Done_Case])
  next
    case Stop_Case
    show ?thesis
      by (rule exact_concrete_partition_loop_state_stop_exists
        [OF Stop_Case])
  next
    case (Step_Case S_pull beta D_pull)
    show ?thesis
      by (rule exact_concrete_initialized_partition_loop_state_nonterminal_exists_finite_bound
        [OF init pre upper Step_Case(1) P_reaches Step_Case(2)
          Step_Case(3) Step_Case(4)])
  qed
qed

lemma exact_concrete_initialized_partition_loop_state_cases_exists_finite_bound_with_complete:
  fixes W :: "bound \<Rightarrow> 'a set"
  assumes init: "exact_partition_initial_state t d P D c_insert"
    and pre: "bmssp_pre_full d P (Fin Bmax)"
    and upper: "\<And>u. u \<in> P \<Longrightarrow> d u < Bmax"
    and P_reaches: "\<forall>x\<in>P. reachable s x"
    and cases:
      "(keys_of (partition_state_view D) = {} \<and>
        bound_le (Fin a) (Fin Bmax) \<and>
        complete_on d' (bound_tree P (Fin Bmax)) \<and>
        complete_on d' (W (Fin Bmax))) \<or>
       (bound_le (Fin a) (Fin Bmax) \<and>
        complete_on d' (bound_tree P (Fin a)) \<and>
        k * cap \<le> card (bound_tree P (Fin a)) \<and>
        complete_on d' (W (Fin a))) \<or>
       (\<exists>S_pull beta D_pull B'.
        partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull) \<and>
        complete_on d' (bound_tree P (Fin a)) \<and>
        card (bound_tree P (Fin a)) < k * cap \<and>
        complete_on d' (W B') \<and>
        (\<exists>d_child b c_child betas bs Us_tail U_tail c_tail
            child_costs_tail.
          a \<le> b \<and>
          bound_le (Fin a) B' \<and>
          exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
            d_child (Fin b) (range_tree P a (Fin b)) c_child \<and>
          complete_preserved d_child d' (range_tree P a (Fin b)) \<and>
          exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
            (Fin Bmax) d'
            (partition_state_batch_prepend
              (label_pairs_between d S_pull b beta)
              (partition_state_batch_prepend
                (edge_relaxation_pairs_between d_child
                  (range_tree P a (Fin b)) b beta)
                (partition_state_batch_prepend
                  (edge_relaxation_pairs_in_bound d_child
                    (range_tree P a (Fin b)) beta (Fin Bmax))
                  D_pull)))
            b betas bs B' Us_tail U_tail c_tail child_costs_tail))"
  shows "\<exists>betas bs B' Us U c child_costs.
    exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
      (Fin Bmax) d' D a betas bs B' Us U c child_costs \<and>
    complete_on d' (W B')"
proof -
  consider
    (Done_Case) "keys_of (partition_state_view D) = {}"
      "bound_le (Fin a) (Fin Bmax)"
      "complete_on d' (bound_tree P (Fin Bmax))"
      "complete_on d' (W (Fin Bmax))"
  | (Stop_Case) "bound_le (Fin a) (Fin Bmax)"
      "complete_on d' (bound_tree P (Fin a))"
      "k * cap \<le> card (bound_tree P (Fin a))"
      "complete_on d' (W (Fin a))"
  | (Step_Case) S_pull beta D_pull B' where
      "partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull)"
      "complete_on d' (bound_tree P (Fin a))"
      "card (bound_tree P (Fin a)) < k * cap"
      "complete_on d' (W B')"
      "\<exists>d_child b c_child betas bs Us_tail U_tail c_tail
          child_costs_tail.
        a \<le> b \<and>
        bound_le (Fin a) B' \<and>
        exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
          d_child (Fin b) (range_tree P a (Fin b)) c_child \<and>
        complete_preserved d_child d' (range_tree P a (Fin b)) \<and>
        exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
          (Fin Bmax) d'
          (partition_state_batch_prepend (label_pairs_between d S_pull b beta)
            (partition_state_batch_prepend
              (edge_relaxation_pairs_between d_child
                (range_tree P a (Fin b)) b beta)
              (partition_state_batch_prepend
                (edge_relaxation_pairs_in_bound d_child
                  (range_tree P a (Fin b)) beta (Fin Bmax))
                D_pull)))
          b betas bs B' Us_tail U_tail c_tail child_costs_tail"
    using cases by blast
  then show ?thesis
  proof cases
    case Done_Case
    have run:
      "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
        (Fin Bmax) d' D a [] [] (Fin Bmax)
        [range_tree P a (Fin Bmax)]
        (bound_tree P (Fin a) \<union>
          \<Union>(set [range_tree P a (Fin Bmax)])) 0 []"
      by (rule exact_concrete_partition_loop_state_done_witness
        [OF Done_Case(1) Done_Case(2) Done_Case(3)])
    then show ?thesis
      using Done_Case(4) by blast
  next
    case Stop_Case
    have run:
      "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
        (Fin Bmax) d' D a [] [] (Fin a)
        [range_tree P a (Fin a)]
        (bound_tree P (Fin a) \<union>
          \<Union>(set [range_tree P a (Fin a)])) 0 []"
      by (rule exact_concrete_partition_loop_state_stop_witness
        [OF Stop_Case(1) Stop_Case(2) Stop_Case(3)])
    then show ?thesis
      using Stop_Case(4) by blast
  next
    case (Step_Case S_pull beta D_pull B')
    then obtain d_child b c_child betas bs Us_tail U_tail c_tail
        child_costs_tail where
      a_le_b: "a \<le> b"
      and a_bound: "bound_le (Fin a) B'"
      and child:
        "exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
          d_child (Fin b) (range_tree P a (Fin b)) c_child"
      and preserved:
        "complete_preserved d_child d' (range_tree P a (Fin b))"
      and tail:
        "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
          (Fin Bmax) d'
          (partition_state_batch_prepend (label_pairs_between d S_pull b beta)
            (partition_state_batch_prepend
              (edge_relaxation_pairs_between d_child
                (range_tree P a (Fin b)) b beta)
              (partition_state_batch_prepend
                (edge_relaxation_pairs_in_bound d_child
                  (range_tree P a (Fin b)) beta (Fin Bmax))
                D_pull)))
          b betas bs B' Us_tail U_tail c_tail child_costs_tail"
      by blast
    have loop:
      "\<exists>c child_costs.
        exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
          (Fin Bmax) d' D a (beta # betas) (b # bs) B'
          (range_tree P a (Fin b) # Us_tail)
          (bound_tree P (Fin a) \<union>
            \<Union>(set (range_tree P a (Fin b) # Us_tail))) c child_costs"
      by (rule exact_concrete_initialized_partition_loop_state_step_exists_finite_bound
        [OF init pre upper Step_Case(1) P_reaches a_le_b a_bound
          Step_Case(2) Step_Case(3) child preserved tail])
    then show ?thesis
      using Step_Case(4) by blast
  qed
qed

lemma exact_concrete_initialized_partition_loop_state_cases_exists_with_complete:
  fixes W :: "bound \<Rightarrow> 'a set"
  assumes init: "exact_partition_initial_state t d P D c_insert"
    and pre: "bmssp_pre_full d P (Fin Bmax)"
    and upper: "\<And>u. u \<in> P \<Longrightarrow> d u < Bmax"
    and P_reaches: "\<forall>x\<in>P. reachable s x"
    and cases:
      "(keys_of (partition_state_view D) = {} \<and>
        bound_le (Fin a) B \<and>
        complete_on d' (bound_tree P B) \<and>
        complete_on d' (W B)) \<or>
       (bound_le (Fin a) B \<and>
        complete_on d' (bound_tree P (Fin a)) \<and>
        k * cap \<le> card (bound_tree P (Fin a)) \<and>
        complete_on d' (W (Fin a))) \<or>
       (\<exists>S_pull beta D_pull B'.
        partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull) \<and>
        bound_le (Fin beta) B \<and>
        complete_on d' (bound_tree P (Fin a)) \<and>
        card (bound_tree P (Fin a)) < k * cap \<and>
        complete_on d' (W B') \<and>
        (\<exists>d_child b c_child betas bs Us_tail U_tail c_tail
            child_costs_tail.
          a \<le> b \<and>
          bound_le (Fin a) B' \<and>
          exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
            d_child (Fin b) (range_tree P a (Fin b)) c_child \<and>
          complete_preserved d_child d' (range_tree P a (Fin b)) \<and>
          exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
            B d'
            (partition_state_batch_prepend
              (label_pairs_between d S_pull b beta)
              (partition_state_batch_prepend
                (edge_relaxation_pairs_between d_child
                  (range_tree P a (Fin b)) b beta)
                (partition_state_batch_prepend
                  (edge_relaxation_pairs_in_bound d_child
                    (range_tree P a (Fin b)) beta B)
                  D_pull)))
            b betas bs B' Us_tail U_tail c_tail child_costs_tail))"
  shows "\<exists>betas bs B' Us U c child_costs.
    exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
      B d' D a betas bs B' Us U c child_costs \<and>
    complete_on d' (W B')"
proof -
  consider
    (Done_Case) "keys_of (partition_state_view D) = {}"
      "bound_le (Fin a) B"
      "complete_on d' (bound_tree P B)"
      "complete_on d' (W B)"
  | (Stop_Case) "bound_le (Fin a) B"
      "complete_on d' (bound_tree P (Fin a))"
      "k * cap \<le> card (bound_tree P (Fin a))"
      "complete_on d' (W (Fin a))"
  | (Step_Case) S_pull beta D_pull B' where
      "partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull)"
      "bound_le (Fin beta) B"
      "complete_on d' (bound_tree P (Fin a))"
      "card (bound_tree P (Fin a)) < k * cap"
      "complete_on d' (W B')"
      "\<exists>d_child b c_child betas bs Us_tail U_tail c_tail
          child_costs_tail.
        a \<le> b \<and>
        bound_le (Fin a) B' \<and>
        exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
          d_child (Fin b) (range_tree P a (Fin b)) c_child \<and>
        complete_preserved d_child d' (range_tree P a (Fin b)) \<and>
        exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
          B d'
          (partition_state_batch_prepend (label_pairs_between d S_pull b beta)
            (partition_state_batch_prepend
              (edge_relaxation_pairs_between d_child
                (range_tree P a (Fin b)) b beta)
              (partition_state_batch_prepend
                (edge_relaxation_pairs_in_bound d_child
                  (range_tree P a (Fin b)) beta B)
                D_pull)))
          b betas bs B' Us_tail U_tail c_tail child_costs_tail"
    using cases by blast
  then show ?thesis
  proof cases
    case Done_Case
    have run:
      "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
        B d' D a [] [] B [range_tree P a B]
        (bound_tree P (Fin a) \<union>
          \<Union>(set [range_tree P a B])) 0 []"
      by (rule exact_concrete_partition_loop_state_done_witness
        [OF Done_Case(1) Done_Case(2) Done_Case(3)])
    then show ?thesis
      using Done_Case(4) by blast
  next
    case Stop_Case
    have run:
      "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
        B d' D a [] [] (Fin a)
        [range_tree P a (Fin a)]
        (bound_tree P (Fin a) \<union>
          \<Union>(set [range_tree P a (Fin a)])) 0 []"
      by (rule exact_concrete_partition_loop_state_stop_witness
        [OF Stop_Case(1) Stop_Case(2) Stop_Case(3)])
    then show ?thesis
      using Stop_Case(4) by blast
  next
    case (Step_Case S_pull beta D_pull B')
    then obtain d_child b c_child betas bs Us_tail U_tail c_tail
        child_costs_tail where
      a_le_b: "a \<le> b"
      and a_bound: "bound_le (Fin a) B'"
      and child:
        "exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
          d_child (Fin b) (range_tree P a (Fin b)) c_child"
      and preserved:
        "complete_preserved d_child d' (range_tree P a (Fin b))"
      and tail:
        "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
          B d'
          (partition_state_batch_prepend (label_pairs_between d S_pull b beta)
            (partition_state_batch_prepend
              (edge_relaxation_pairs_between d_child
                (range_tree P a (Fin b)) b beta)
              (partition_state_batch_prepend
                (edge_relaxation_pairs_in_bound d_child
                  (range_tree P a (Fin b)) beta B)
                D_pull)))
          b betas bs B' Us_tail U_tail c_tail child_costs_tail"
      by blast
    have S_pull_reaches: "\<forall>x\<in>S_pull. reachable s x"
      by (rule exact_partition_initial_state_pull_reaches
        [OF init upper Step_Case(1) P_reaches])
    have loop:
      "\<exists>c child_costs.
        exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P
          B d' D a (beta # betas) (b # bs) B'
          (range_tree P a (Fin b) # Us_tail)
          (bound_tree P (Fin a) \<union>
            \<Union>(set (range_tree P a (Fin b) # Us_tail))) c child_costs"
      by (rule exact_concrete_initialized_partition_loop_state_step_exists
        [OF init pre upper Step_Case(1) Step_Case(2) S_pull_reaches
          a_le_b a_bound Step_Case(3) Step_Case(4) child refl
          preserved tail])
    then show ?thesis
      using Step_Case(5) by blast
  qed
qed

lemma exact_concrete_partition_loop_state_step_exists_from_concrete_ops:
  assumes inv_D: "partition_state_invar D"
    and upper_D: "partition_upper_bound (partition_state_view D) Bmax"
    and pull:
      "partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull)"
    and beta_bound: "bound_le (Fin beta) B"
    and child_pre: "bmssp_pre_full d S_pull (Fin beta)"
    and S_pull_def: "S_pull = split_below d P beta"
    and S_pull_reaches: "\<forall>x\<in>S_pull. reachable s x"
    and a_le_b: "a \<le> b"
    and a_bound: "bound_le (Fin a) B'"
    and complete_prefix: "complete_on d' (bound_tree P (Fin a))"
    and below_threshold: "card (bound_tree P (Fin a)) < k * cap"
    and child:
      "exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
        d_child (Fin b) U_child c_child"
    and U_child: "U_child = range_tree P a (Fin b)"
    and preserved: "complete_preserved d_child d' U_child"
    and tail:
      "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d'
        (partition_state_batch_prepend (label_pairs_between d S_pull b beta)
          (partition_state_batch_prepend
            (edge_relaxation_pairs_between d_child U_child b beta)
            (partition_state_batch_prepend
              (edge_relaxation_pairs_in_bound d_child U_child beta B)
              D_pull)))
        b betas bs B' Us_tail U_tail c_tail child_costs_tail"
  shows "\<exists>c child_costs.
    exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      (beta # betas) (b # bs) B'
      (range_tree P a (Fin b) # Us_tail)
      (bound_tree P (Fin a) \<union>
        \<Union>(set (range_tree P a (Fin b) # Us_tail))) c child_costs"
proof -
  have run:
    "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      (beta # betas) (b # bs) B'
      (range_tree P a (Fin b) # Us_tail)
      (bound_tree P (Fin a) \<union>
        \<Union>(set (range_tree P a (Fin b) # Us_tail)))
      (card S_pull +
        t * length (edge_relaxation_pairs_in_bound d_child U_child beta B) +
        h * length (edge_relaxation_pairs_between d_child U_child b beta) +
        h * length (label_pairs_between d S_pull b beta) +
        c_child + c_tail)
      (c_child # child_costs_tail)"
    by (rule exact_concrete_partition_loop_state_step_from_concrete_ops
      [OF inv_D upper_D pull beta_bound child_pre S_pull_def
        S_pull_reaches a_le_b a_bound complete_prefix below_threshold child
        U_child preserved tail])
  show ?thesis
    using run by blast
qed

lemma exact_concrete_bmssp_step_with_exact_insert_cost:
  assumes init: "exact_partition_initial_state t
      (find_pivots_label_capped k cap d S B)
      (find_pivots_pivots_capped k cap d S B) D c_insert"
    and loop:
      "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a
        betas bs B' Us U_loop c_loop child_costs_loop"
    and complete:
      "complete_on d'
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v =
          dist s v}"
    and U:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v =
          dist s v}"
  shows "exact_concrete_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U
    (fp_iter_capped_scan_cost k cap d S S B +
      t * card (find_pivots_pivots_capped k cap d S B) + c_loop)"
proof -
  have c_insert:
    "c_insert = t * card (find_pivots_pivots_capped k cap d S B)"
    by (rule exact_partition_initial_state_cost[OF init])
  show ?thesis
    by (rule Exact_Concrete_Step[OF init loop complete U])
      (simp add: c_insert)
qed

lemma exact_concrete_bmssp_Suc_exists_from_initial_loop:
  assumes S_subset: "S \<subseteq> V"
    and loop:
      "\<And>D. exact_partition_initial_state t
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) D
        (t * card (find_pivots_pivots_capped k cap d S B)) \<Longrightarrow>
        \<exists>d' a betas bs B' Us U_loop c_loop child_costs_loop.
          exact_concrete_partition_loop_state \<Delta> M_of t h k cap l
            (find_pivots_label_capped k cap d S B)
            (find_pivots_pivots_capped k cap d S B) B d' D a
            betas bs B' Us U_loop c_loop child_costs_loop \<and>
          complete_on d'
            {v \<in> bound_tree S B'.
              find_pivots_label_capped k cap d S B v = dist s v}"
  shows "\<exists>d' B' U c.
    exact_concrete_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"
proof -
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  obtain D where init:
    "exact_partition_initial_state t ?d_fp ?P D (t * card ?P)"
    using exact_partition_initial_state_exists_for_capped_pivots_with_cost
      [OF S_subset] by blast
  obtain d' a betas bs B' Us U_loop c_loop child_costs_loop where
    loop_run:
      "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l
        ?d_fp ?P B d' D a betas bs B' Us U_loop c_loop child_costs_loop"
    and complete:
      "complete_on d'
        {v \<in> bound_tree S B'. ?d_fp v = dist s v}"
    using loop[OF init] by blast
  let ?U = "U_loop \<union> {v \<in> bound_tree S B'. ?d_fp v = dist s v}"
  have run:
    "exact_concrete_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' ?U
      (fp_iter_capped_scan_cost k cap d S S B + t * card ?P + c_loop)"
    by (rule exact_concrete_bmssp_step_with_exact_insert_cost
      [OF init loop_run complete refl])
  show ?thesis
    using run by blast
qed

text \<open>
  The non-base existence lemmas are phrased as case combinators.  They do not
  decide which branch an implementation should take; instead they say that if a
  client can provide one of the expected witnesses (empty partition, threshold,
  or a recursive child plus tail loop), then a full exact concrete BMSSP step
  exists.  This keeps totality concerns separate from the correctness and cost
  refinement already proved for any exact run.
\<close>

lemma exact_concrete_bmssp_Suc_exists_from_initial_loop_cases:
  fixes d :: "'a \<Rightarrow> real"
    and S :: "'a set"
    and B :: bound
    and Bmax :: real
    and k cap :: nat
    and d_fp :: "'a \<Rightarrow> real"
    and P :: "'a set"
  defines d_fp_def:
    "d_fp \<equiv> find_pivots_label_capped k cap d S B"
    and P_def:
    "P \<equiv> find_pivots_pivots_capped k cap d S B"
  assumes S_subset: "S \<subseteq> V"
    and pre_fp: "bmssp_pre_full d_fp P (Fin Bmax)"
    and upper: "\<And>x. x \<in> P \<Longrightarrow> d_fp x < Bmax"
    and P_reaches: "\<forall>x\<in>P. reachable s x"
    and cases:
      "\<And>D. exact_partition_initial_state t d_fp P D (t * card P) \<Longrightarrow>
        \<exists>d' a.
          (keys_of (partition_state_view D) = {} \<and>
            bound_le (Fin a) B \<and>
            complete_on d' (bound_tree P B) \<and>
            complete_on d'
              {v \<in> bound_tree S B. d_fp v = dist s v}) \<or>
          (bound_le (Fin a) B \<and>
            complete_on d' (bound_tree P (Fin a)) \<and>
            k * cap \<le> card (bound_tree P (Fin a)) \<and>
            complete_on d'
              {v \<in> bound_tree S (Fin a). d_fp v = dist s v}) \<or>
          (\<exists>S_pull beta D_pull B'.
            partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull) \<and>
            bound_le (Fin beta) B \<and>
            complete_on d' (bound_tree P (Fin a)) \<and>
            card (bound_tree P (Fin a)) < k * cap \<and>
            complete_on d'
              {v \<in> bound_tree S B'. d_fp v = dist s v} \<and>
            (\<exists>d_child b c_child betas bs Us_tail U_tail c_tail
                child_costs_tail.
              a \<le> b \<and>
              bound_le (Fin a) B' \<and>
              exact_concrete_bmssp \<Delta> M_of t h k cap l d_fp S_pull
                (Fin beta) d_child (Fin b) (range_tree P a (Fin b))
                c_child \<and>
              complete_preserved d_child d' (range_tree P a (Fin b)) \<and>
              exact_concrete_partition_loop_state \<Delta> M_of t h k cap l
                d_fp P B d'
                (partition_state_batch_prepend
                  (label_pairs_between d_fp S_pull b beta)
                  (partition_state_batch_prepend
                    (edge_relaxation_pairs_between d_child
                      (range_tree P a (Fin b)) b beta)
                    (partition_state_batch_prepend
                      (edge_relaxation_pairs_in_bound d_child
                        (range_tree P a (Fin b)) beta B)
                      D_pull)))
                b betas bs B' Us_tail U_tail c_tail child_costs_tail))"
  shows "\<exists>d' B' U c.
    exact_concrete_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"
proof -
  obtain D where init:
    "exact_partition_initial_state t d_fp P D (t * card P)"
    using exact_partition_initial_state_exists_for_capped_pivots_with_cost
      [OF S_subset]
    unfolding d_fp_def P_def by blast
  obtain d' a where case_data:
    "(keys_of (partition_state_view D) = {} \<and>
      bound_le (Fin a) B \<and>
      complete_on d' (bound_tree P B) \<and>
      complete_on d'
        {v \<in> bound_tree S B. d_fp v = dist s v}) \<or>
     (bound_le (Fin a) B \<and>
      complete_on d' (bound_tree P (Fin a)) \<and>
      k * cap \<le> card (bound_tree P (Fin a)) \<and>
      complete_on d'
        {v \<in> bound_tree S (Fin a). d_fp v = dist s v}) \<or>
     (\<exists>S_pull beta D_pull B'.
      partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull) \<and>
      bound_le (Fin beta) B \<and>
      complete_on d' (bound_tree P (Fin a)) \<and>
      card (bound_tree P (Fin a)) < k * cap \<and>
      complete_on d'
        {v \<in> bound_tree S B'. d_fp v = dist s v} \<and>
      (\<exists>d_child b c_child betas bs Us_tail U_tail c_tail
          child_costs_tail.
        a \<le> b \<and>
        bound_le (Fin a) B' \<and>
        exact_concrete_bmssp \<Delta> M_of t h k cap l d_fp S_pull
          (Fin beta) d_child (Fin b) (range_tree P a (Fin b))
          c_child \<and>
        complete_preserved d_child d' (range_tree P a (Fin b)) \<and>
        exact_concrete_partition_loop_state \<Delta> M_of t h k cap l
          d_fp P B d'
          (partition_state_batch_prepend
            (label_pairs_between d_fp S_pull b beta)
            (partition_state_batch_prepend
              (edge_relaxation_pairs_between d_child
                (range_tree P a (Fin b)) b beta)
              (partition_state_batch_prepend
                (edge_relaxation_pairs_in_bound d_child
                  (range_tree P a (Fin b)) beta B)
                D_pull)))
          b betas bs B' Us_tail U_tail c_tail child_costs_tail))"
    using cases[OF init] by blast
  obtain betas bs B' Us U_loop c_loop child_costs_loop where
    loop:
      "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d_fp P
        B d' D a betas bs B' Us U_loop c_loop child_costs_loop"
    and complete:
      "complete_on d'
        {v \<in> bound_tree S B'. d_fp v = dist s v}"
    using exact_concrete_initialized_partition_loop_state_cases_exists_with_complete
      [where W = "\<lambda>B'. {v \<in> bound_tree S B'. d_fp v = dist s v}",
        OF init pre_fp upper P_reaches case_data]
    by blast
  have init_actual:
    "exact_partition_initial_state t
      (find_pivots_label_capped k cap d S B)
      (find_pivots_pivots_capped k cap d S B) D
      (t * card (find_pivots_pivots_capped k cap d S B))"
    using init unfolding d_fp_def P_def .
  have loop_actual:
    "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l
      (find_pivots_label_capped k cap d S B)
      (find_pivots_pivots_capped k cap d S B)
      B d' D a betas bs B' Us U_loop c_loop child_costs_loop"
    using loop unfolding d_fp_def P_def .
  have complete_actual:
    "complete_on d'
      {v \<in> bound_tree S B'.
        find_pivots_label_capped k cap d S B v = dist s v}"
    using complete unfolding d_fp_def .
  let ?U =
    "U_loop \<union>
      {v \<in> bound_tree S B'.
        find_pivots_label_capped k cap d S B v = dist s v}"
  have run:
    "exact_concrete_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' ?U
      (fp_iter_capped_scan_cost k cap d S S B +
        t * card (find_pivots_pivots_capped k cap d S B) + c_loop)"
    by (rule exact_concrete_bmssp_step_with_exact_insert_cost
      [OF init_actual loop_actual complete_actual refl])
  then show ?thesis
    by blast
qed

lemma exact_concrete_bmssp_Suc_exists_from_finite_initial_loop_cases:
  fixes d :: "'a \<Rightarrow> real"
    and S :: "'a set"
    and Bmax :: real
    and k cap :: nat
    and d_fp :: "'a \<Rightarrow> real"
    and P :: "'a set"
  defines d_fp_def:
    "d_fp \<equiv> find_pivots_label_capped k cap d S (Fin Bmax)"
    and P_def:
    "P \<equiv> find_pivots_pivots_capped k cap d S (Fin Bmax)"
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S (Fin Bmax)"
    and S_reaches: "\<forall>x\<in>S. reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> d x < Bmax"
    and cases:
      "\<And>D. exact_partition_initial_state t d_fp P D (t * card P) \<Longrightarrow>
        \<exists>d' a.
          (keys_of (partition_state_view D) = {} \<and>
            bound_le (Fin a) (Fin Bmax) \<and>
            complete_on d' (bound_tree P (Fin Bmax)) \<and>
            complete_on d'
              {v \<in> bound_tree S (Fin Bmax). d_fp v = dist s v}) \<or>
          (bound_le (Fin a) (Fin Bmax) \<and>
            complete_on d' (bound_tree P (Fin a)) \<and>
            k * cap \<le> card (bound_tree P (Fin a)) \<and>
            complete_on d'
              {v \<in> bound_tree S (Fin a). d_fp v = dist s v}) \<or>
          (\<exists>S_pull beta D_pull B'.
            partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull) \<and>
            complete_on d' (bound_tree P (Fin a)) \<and>
            card (bound_tree P (Fin a)) < k * cap \<and>
            complete_on d'
              {v \<in> bound_tree S B'. d_fp v = dist s v} \<and>
            (\<exists>d_child b c_child betas bs Us_tail U_tail c_tail
                child_costs_tail.
              a \<le> b \<and>
              bound_le (Fin a) B' \<and>
              exact_concrete_bmssp \<Delta> M_of t h k cap l d_fp S_pull
                (Fin beta) d_child (Fin b) (range_tree P a (Fin b))
                c_child \<and>
              complete_preserved d_child d' (range_tree P a (Fin b)) \<and>
              exact_concrete_partition_loop_state \<Delta> M_of t h k cap l
                d_fp P (Fin Bmax) d'
                (partition_state_batch_prepend
                  (label_pairs_between d_fp S_pull b beta)
                  (partition_state_batch_prepend
                    (edge_relaxation_pairs_between d_child
                      (range_tree P a (Fin b)) b beta)
                    (partition_state_batch_prepend
                      (edge_relaxation_pairs_in_bound d_child
                        (range_tree P a (Fin b)) beta (Fin Bmax))
                      D_pull)))
                b betas bs B' Us_tail U_tail c_tail child_costs_tail))"
  shows "\<exists>d' B' U c.
    exact_concrete_bmssp \<Delta> M_of t h k cap (Suc l) d S (Fin Bmax)
      d' B' U c"
proof -
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  obtain D where init:
    "exact_partition_initial_state t d_fp P D (t * card P)"
    using exact_partition_initial_state_exists_for_capped_pivots_with_cost
      [OF S_subset]
    unfolding d_fp_def P_def by blast
  have pre_fp: "bmssp_pre_full d_fp P (Fin Bmax)"
    unfolding d_fp_def P_def
    by (rule find_pivots_capped_establishes_pivot_pre_concrete
      [OF sound pre]) (use S_reaches in blast)
  have upper: "\<And>u. u \<in> P \<Longrightarrow> d_fp u < Bmax"
    unfolding d_fp_def P_def
    by (rule find_pivots_pivots_capped_label_less_finite[OF below])
  have P_reaches: "\<forall>x\<in>P. reachable s x"
    unfolding P_def
    by (rule find_pivots_pivots_capped_reaches[OF S_reaches])
  obtain d' a where case_data:
    "(keys_of (partition_state_view D) = {} \<and>
      bound_le (Fin a) (Fin Bmax) \<and>
      complete_on d' (bound_tree P (Fin Bmax)) \<and>
      complete_on d'
        {v \<in> bound_tree S (Fin Bmax). d_fp v = dist s v}) \<or>
     (bound_le (Fin a) (Fin Bmax) \<and>
      complete_on d' (bound_tree P (Fin a)) \<and>
      k * cap \<le> card (bound_tree P (Fin a)) \<and>
      complete_on d'
        {v \<in> bound_tree S (Fin a). d_fp v = dist s v}) \<or>
     (\<exists>S_pull beta D_pull B'.
      partition_state_pull (M_of l) Bmax D = (S_pull, beta, D_pull) \<and>
      complete_on d' (bound_tree P (Fin a)) \<and>
      card (bound_tree P (Fin a)) < k * cap \<and>
      complete_on d'
        {v \<in> bound_tree S B'. d_fp v = dist s v} \<and>
      (\<exists>d_child b c_child betas bs Us_tail U_tail c_tail
          child_costs_tail.
        a \<le> b \<and>
        bound_le (Fin a) B' \<and>
        exact_concrete_bmssp \<Delta> M_of t h k cap l d_fp S_pull
          (Fin beta) d_child (Fin b) (range_tree P a (Fin b))
          c_child \<and>
        complete_preserved d_child d' (range_tree P a (Fin b)) \<and>
        exact_concrete_partition_loop_state \<Delta> M_of t h k cap l
          d_fp P (Fin Bmax) d'
          (partition_state_batch_prepend
            (label_pairs_between d_fp S_pull b beta)
            (partition_state_batch_prepend
              (edge_relaxation_pairs_between d_child
                (range_tree P a (Fin b)) b beta)
              (partition_state_batch_prepend
                (edge_relaxation_pairs_in_bound d_child
                  (range_tree P a (Fin b)) beta (Fin Bmax))
                D_pull)))
          b betas bs B' Us_tail U_tail c_tail child_costs_tail))"
    using cases[OF init] by blast
  obtain betas bs B' Us U_loop c_loop child_costs_loop where
    loop:
      "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d_fp P
        (Fin Bmax) d' D a betas bs B' Us U_loop c_loop
        child_costs_loop"
    and complete:
      "complete_on d'
        {v \<in> bound_tree S B'. d_fp v = dist s v}"
    using exact_concrete_initialized_partition_loop_state_cases_exists_finite_bound_with_complete
      [where W = "\<lambda>B'. {v \<in> bound_tree S B'. d_fp v = dist s v}",
        OF init pre_fp upper P_reaches case_data]
    by blast
  have init_actual:
    "exact_partition_initial_state t
      (find_pivots_label_capped k cap d S (Fin Bmax))
      (find_pivots_pivots_capped k cap d S (Fin Bmax)) D
      (t * card (find_pivots_pivots_capped k cap d S (Fin Bmax)))"
    using init unfolding d_fp_def P_def .
  have loop_actual:
    "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l
      (find_pivots_label_capped k cap d S (Fin Bmax))
      (find_pivots_pivots_capped k cap d S (Fin Bmax))
      (Fin Bmax) d' D a betas bs B' Us U_loop c_loop
      child_costs_loop"
    using loop unfolding d_fp_def P_def .
  have complete_actual:
    "complete_on d'
      {v \<in> bound_tree S B'.
        find_pivots_label_capped k cap d S (Fin Bmax) v = dist s v}"
    using complete unfolding d_fp_def .
  let ?U =
    "U_loop \<union>
      {v \<in> bound_tree S B'.
        find_pivots_label_capped k cap d S (Fin Bmax) v = dist s v}"
  have run:
    "exact_concrete_bmssp \<Delta> M_of t h k cap (Suc l) d S (Fin Bmax)
      d' B' ?U
      (fp_iter_capped_scan_cost k cap d S S (Fin Bmax) +
        t * card (find_pivots_pivots_capped k cap d S (Fin Bmax)) +
        c_loop)"
    by (rule exact_concrete_bmssp_step_with_exact_insert_cost
      [OF init_actual loop_actual complete_actual refl])
  then show ?thesis
    by blast
qed

lemma exact_concrete_bmssp_Suc_exists_if_pivots_empty:
  assumes S_subset: "S \<subseteq> V"
    and a_bound: "bound_le (Fin a) B"
    and pivots_empty:
      "find_pivots_pivots_capped k cap d S B = {}"
  shows "\<exists>d' B' U c.
    exact_concrete_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"
proof (rule exact_concrete_bmssp_Suc_exists_from_initial_loop[OF S_subset])
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  fix D
  assume init: "exact_partition_initial_state t ?d_fp ?P D (t * card ?P)"
  have view: "partition_state_view D = label_partition_view ?d_fp ?P"
    by (rule exact_partition_initial_state_view[OF init])
  have empty: "keys_of (partition_state_view D) = {}"
    using view pivots_empty unfolding label_partition_view_def by simp
  have loop:
    "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l
      ?d_fp ?P B (dist s) D a [] [] B [range_tree ?P a B]
      (bound_tree ?P (Fin a) \<union> \<Union>(set [range_tree ?P a B])) 0 []"
    by (rule exact_concrete_partition_loop_state_done_witness
      [OF empty a_bound complete_on_dist])
  have complete:
    "complete_on (dist s)
      {v \<in> bound_tree S B. ?d_fp v = dist s v}"
    by (rule complete_on_dist)
  show "\<exists>d' a betas bs B' Us U_loop c_loop child_costs_loop.
      exact_concrete_partition_loop_state \<Delta> M_of t h k cap l
        ?d_fp ?P B d' D a betas bs B' Us U_loop c_loop
        child_costs_loop \<and>
      complete_on d'
        {v \<in> bound_tree S B'. ?d_fp v = dist s v}"
    using loop complete by blast
qed

lemma exact_concrete_bmssp_Suc_exists_if_initial_threshold:
  assumes S_subset: "S \<subseteq> V"
    and a_bound: "bound_le (Fin a) B"
    and threshold:
      "k * cap \<le>
        card (bound_tree (find_pivots_pivots_capped k cap d S B) (Fin a))"
  shows "\<exists>d' B' U c.
    exact_concrete_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"
proof (rule exact_concrete_bmssp_Suc_exists_from_initial_loop[OF S_subset])
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  fix D
  assume init: "exact_partition_initial_state t ?d_fp ?P D (t * card ?P)"
  have loop:
    "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l
      ?d_fp ?P B (dist s) D a [] [] (Fin a)
      [range_tree ?P a (Fin a)]
      (bound_tree ?P (Fin a) \<union> \<Union>(set [range_tree ?P a (Fin a)]))
      0 []"
    by (rule exact_concrete_partition_loop_state_stop_witness
      [OF a_bound complete_on_dist threshold])
  have complete:
    "complete_on (dist s)
      {v \<in> bound_tree S (Fin a). ?d_fp v = dist s v}"
    by (rule complete_on_dist)
  show "\<exists>d' a betas bs B' Us U_loop c_loop child_costs_loop.
      exact_concrete_partition_loop_state \<Delta> M_of t h k cap l
        ?d_fp ?P B d' D a betas bs B' Us U_loop c_loop
        child_costs_loop \<and>
      complete_on d'
        {v \<in> bound_tree S B'. ?d_fp v = dist s v}"
    using loop complete by blast
qed

lemma exact_concrete_bmssp_Suc_exists_if_pivots_empty_same_bound:
  assumes S_subset: "S \<subseteq> V"
    and a_bound: "bound_le (Fin a) B"
    and pivots_empty:
      "find_pivots_pivots_capped k cap d S B = {}"
  shows "\<exists>d' U c.
    exact_concrete_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B U c"
proof -
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  let ?U_loop =
    "bound_tree ?P (Fin a) \<union> \<Union>(set [range_tree ?P a B])"
  obtain D where init:
    "exact_partition_initial_state t ?d_fp ?P D (t * card ?P)"
    using exact_partition_initial_state_exists_for_capped_pivots_with_cost
      [OF S_subset] by blast
  have view: "partition_state_view D = label_partition_view ?d_fp ?P"
    by (rule exact_partition_initial_state_view[OF init])
  have empty: "keys_of (partition_state_view D) = {}"
    using view pivots_empty unfolding label_partition_view_def by simp
  have loop:
    "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l
      ?d_fp ?P B (dist s) D a [] [] B [range_tree ?P a B] ?U_loop
      0 []"
    by (rule exact_concrete_partition_loop_state_done_witness
      [OF empty a_bound complete_on_dist])
  have complete:
    "complete_on (dist s)
      {v \<in> bound_tree S B. ?d_fp v = dist s v}"
    by (rule complete_on_dist)
  let ?U = "?U_loop \<union> {v \<in> bound_tree S B. ?d_fp v = dist s v}"
  have run:
    "exact_concrete_bmssp \<Delta> M_of t h k cap (Suc l) d S B
      (dist s) B ?U
      (fp_iter_capped_scan_cost k cap d S S B + t * card ?P + 0)"
    by (rule exact_concrete_bmssp_step_with_exact_insert_cost
      [OF init loop complete refl])
  show ?thesis
    using run by blast
qed

lemma exact_concrete_bmssp_Suc_exists_if_initial_threshold_bound:
  assumes S_subset: "S \<subseteq> V"
    and a_bound: "bound_le (Fin a) B"
    and threshold:
      "k * cap \<le>
        card (bound_tree (find_pivots_pivots_capped k cap d S B) (Fin a))"
  shows "\<exists>d' U c.
    exact_concrete_bmssp \<Delta> M_of t h k cap (Suc l) d S B
      d' (Fin a) U c"
proof -
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  let ?U_loop =
    "bound_tree ?P (Fin a) \<union> \<Union>(set [range_tree ?P a (Fin a)])"
  obtain D where init:
    "exact_partition_initial_state t ?d_fp ?P D (t * card ?P)"
    using exact_partition_initial_state_exists_for_capped_pivots_with_cost
      [OF S_subset] by blast
  have loop:
    "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l
      ?d_fp ?P B (dist s) D a [] [] (Fin a)
      [range_tree ?P a (Fin a)] ?U_loop 0 []"
    by (rule exact_concrete_partition_loop_state_stop_witness
      [OF a_bound complete_on_dist threshold])
  have complete:
    "complete_on (dist s)
      {v \<in> bound_tree S (Fin a). ?d_fp v = dist s v}"
    by (rule complete_on_dist)
  let ?U =
    "?U_loop \<union> {v \<in> bound_tree S (Fin a). ?d_fp v = dist s v}"
  have run:
    "exact_concrete_bmssp \<Delta> M_of t h k cap (Suc l) d S B
      (dist s) (Fin a) ?U
      (fp_iter_capped_scan_cost k cap d S S B + t * card ?P + 0)"
    by (rule exact_concrete_bmssp_step_with_exact_insert_cost
      [OF init loop complete refl])
  show ?thesis
    using run by blast
qed

text \<open>
  The central refinement theorem forgets the concrete partition state and keeps
  only its abstract view.  Concrete pulls refine to @{const pull_separates} and
  concrete batch prepends refine to @{const batch_min_update} with the expected
  cost predicates.  After this projection, the exact run is a direct-insert
  costed run with the same labels, bounds, output sets, and total cost.

  The final two theorems are immediate consequences of that projection:
  exact concrete BMSSP runs inherit the success-or-threshold property and the
  full BMSSP correctness theorem from the direct-insert layer.
\<close>

theorem exact_concrete_refines_direct_insert:
  "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
     betas bs B' Us U c child_costs \<Longrightarrow>
   direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d'
     (partition_state_view D) a betas bs B' Us U c child_costs"
and exact_concrete_bmssp_refines_direct_insert:
  "exact_concrete_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow>
   direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
proof (induction rule: exact_concrete_partition_loop_state_exact_concrete_bmssp.inducts)
  case (Exact_Concrete_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  then show ?case
    by (rule Direct_Insert_Costed_State_Done)
next
  case (Exact_Concrete_State_Stop D a B d' P k cap \<Delta> M_of t h l d)
  then show ?case
    by (rule Direct_Insert_Costed_State_Stop)
next
  case (Exact_Concrete_State_Step D Bmax M_of l S_pull beta D_pull c_pull B
      d P a b B' d' k cap \<Delta> t h d_child U_child c_child
      direct_edge_batch lower_edge_batch source_batch c_direct D_direct c_lower
      D_lower c_sources D_next betas bs Us_tail U_tail c_tail
      child_costs_tail c)
  have inv_D: "partition_state_invar D"
    using Exact_Concrete_State_Step by blast
  have upper_D: "partition_upper_bound (partition_state_view D) Bmax"
    using Exact_Concrete_State_Step by blast
  have pull_op:
    "costed_partition_state_pull (M_of l) Bmax D S_pull beta D_pull c_pull"
    using Exact_Concrete_State_Step by blast
  have pull:
    "pull_separates (partition_state_view D) (M_of l) Bmax S_pull beta
      (partition_state_view D_pull)"
    and pull_cost: "partition_pull_cost_bound c_pull S_pull"
    and inv_pull: "partition_state_invar D_pull"
    using costed_partition_state_pull_refines
      [OF inv_D _ pull_op] upper_D
    unfolding partition_upper_bound_def by blast+
  have direct_op:
    "costed_partition_state_batch_prepend t D_pull direct_edge_batch c_direct D_direct"
    using Exact_Concrete_State_Step by blast
  have direct_ref:
    "partition_state_invar D_direct \<and>
     partition_state_view D_direct =
       batch_min_update (partition_state_view D_pull) direct_edge_batch \<and>
     partition_batch_cost_bound c_direct t direct_edge_batch"
    by (rule costed_partition_state_batch_prepend_refines
      [OF inv_pull direct_op])
  have inv_direct: "partition_state_invar D_direct"
    using direct_ref by blast
  have direct_view:
    "partition_state_view D_direct =
      batch_min_update (partition_state_view D_pull) direct_edge_batch"
    using direct_ref by blast
  have direct_cost:
    "partition_batch_cost_bound c_direct t direct_edge_batch"
    using direct_ref by blast
  have lower_op:
    "costed_partition_state_batch_prepend h D_direct lower_edge_batch c_lower D_lower"
    using Exact_Concrete_State_Step by blast
  have lower_ref:
    "partition_state_invar D_lower \<and>
     partition_state_view D_lower =
       batch_min_update (partition_state_view D_direct) lower_edge_batch \<and>
     partition_batch_cost_bound c_lower h lower_edge_batch"
    by (rule costed_partition_state_batch_prepend_refines
      [OF inv_direct lower_op])
  have inv_lower: "partition_state_invar D_lower"
    using lower_ref by blast
  have lower_view:
    "partition_state_view D_lower =
      batch_min_update (partition_state_view D_direct) lower_edge_batch"
    using lower_ref by blast
  have lower_cost:
    "partition_batch_cost_bound c_lower h lower_edge_batch"
    using lower_ref by blast
  have source_op:
    "costed_partition_state_batch_prepend h D_lower source_batch c_sources D_next"
    using Exact_Concrete_State_Step by blast
  have source_ref:
    "partition_state_invar D_next \<and>
     partition_state_view D_next =
       batch_min_update (partition_state_view D_lower) source_batch \<and>
     partition_batch_cost_bound c_sources h source_batch"
    by (rule costed_partition_state_batch_prepend_refines
      [OF inv_lower source_op])
  have source_view:
    "partition_state_view D_next =
      batch_min_update (partition_state_view D_lower) source_batch"
    using source_ref by blast
  have source_cost:
    "partition_batch_cost_bound c_sources h source_batch"
    using source_ref by blast
  have D_next_view:
    "partition_state_view D_next =
      batch_min_update (partition_state_view D_pull)
        (direct_edge_batch @ lower_edge_batch @ source_batch)"
    using direct_view lower_view source_view by simp
  have child_ref:
    "direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
      d_child (Fin b) U_child c_child"
    using Exact_Concrete_State_Step by blast
  have tail_ref:
    "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d'
      (partition_state_view D_next) b betas bs B' Us_tail U_tail c_tail
      child_costs_tail"
    using Exact_Concrete_State_Step by blast
  show ?case
    by (rule Direct_Insert_Costed_State_Step
      [where batch = "direct_edge_batch @ lower_edge_batch @ source_batch"
        and D_next = "partition_state_view D_next"])
      (use Exact_Concrete_State_Step pull child_ref D_next_view pull_cost
        direct_cost lower_cost source_cost tail_ref in auto)
next
  case (Exact_Concrete_Base S x \<Delta> M_of t h k cap d B)
  then show ?case
    by (rule Direct_Insert_Costed_Base)
next
  case (Exact_Concrete_Step t k cap d S B D c_insert \<Delta> M_of h l d' a
      betas bs B' Us U_loop c_loop child_costs_loop U c)
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  have init: "exact_partition_initial_state t ?d_fp ?P D c_insert"
    and loop:
      "exact_concrete_partition_loop_state \<Delta> M_of t h k cap l ?d_fp ?P B d' D a
        betas bs B' Us U_loop c_loop child_costs_loop"
    and complete:
      "complete_on d' {v \<in> bound_tree S B'. ?d_fp v = dist s v}"
    and U_def:
      "U = U_loop \<union> {v \<in> bound_tree S B'. ?d_fp v = dist s v}"
    and c_def:
      "c = fp_iter_capped_scan_cost k cap d S S B + c_insert + c_loop"
    using Exact_Concrete_Step by blast+
  have view: "partition_state_view D = label_partition_view ?d_fp ?P"
    using exact_partition_initial_state_view[OF init] .
  have insert_cost: "partition_initial_insert_cost_bound c_insert t ?P"
    using exact_partition_initial_state_cost_bound[OF init] .
  have loop_ref:
    "direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l ?d_fp
      ?P B d' (partition_state_view D) a betas bs B' Us U_loop c_loop
      child_costs_loop"
    using Exact_Concrete_Step by blast
  show ?case
    by (rule Direct_Insert_Costed_Step
      [OF view insert_cost loop_ref complete U_def c_def])
qed

theorem exact_concrete_bmssp_Suc_success_or_threshold:
  assumes run:
      "exact_concrete_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "B' = B \<or> k * cap \<le> card U"
  by (rule direct_insert_costed_bmssp_Suc_success_or_threshold
    [OF exact_concrete_bmssp_refines_direct_insert[OF run] sound pre
      S_reaches])

theorem exact_concrete_bmssp_correct:
  assumes run:
    "exact_concrete_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "bmssp_post_full d S B d' B' U"
  by (rule direct_insert_costed_bmssp_correct
    [OF exact_concrete_bmssp_refines_direct_insert[OF run] sound pre S_reaches])

end

end
