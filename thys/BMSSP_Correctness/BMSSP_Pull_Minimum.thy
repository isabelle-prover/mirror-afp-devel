theory BMSSP_Pull_Minimum
  imports BMSSP_Find_Pivots
begin

section \<open>Pull Minimum\<close>

text \<open>
  This theory starts replacing the abstract partition-loop contract by concrete
  range-splitting lemmas.  In the BMSSP loop, a partition Pull returns a
  boundary and a lower batch of candidate sources.  The recursive child call is
  made below that boundary.  To justify that call, we need to know that every
  incomplete vertex below the boundary is still covered by a complete source in
  the pulled lower part.

  The rest of the theory is range algebra.  It defines the half-open range tree
  between two distance boundaries, proves that a monotone boundary list
  partitions a bounded tree into disjoint child ranges, and assembles
  completeness of the lower prefix and every child range into the BMSSP
  postcondition.  These lemmas are the semantic counterpart of the operational
  partition loop and are later used by the concrete one-step assembly theory.
\<close>

context unique_shortest_digraph
begin

definition split_below where
  "split_below d S beta = {x \<in> S. d x < beta}"

lemma split_below_label_below:
  assumes "x \<in> split_below d S beta"
  shows "below_bound (d x) (Fin beta)"
  using assms unfolding split_below_def by simp

lemma split_below_tree_antichain:
  assumes anti: "tree_antichain S"
  shows "tree_antichain (split_below d S beta)"
  by (rule tree_antichain_subset[OF anti]) (simp add: split_below_def)

lemma split_below_scaled_card_le:
  assumes S_subset: "S \<subseteq> V"
    and S_k_cap: "k * card S \<le> cap"
  shows "k * card (split_below d S beta) \<le> cap"
proof -
  have finite_S: "finite S"
    using finite_subset[OF S_subset finite_V] .
  have "card (split_below d S beta) \<le> card S"
    by (rule card_mono[OF finite_S]) (simp add: split_below_def)
  then have "k * card (split_below d S beta) \<le> k * card S"
    by simp
  then show ?thesis
    using S_k_cap by linarith
qed

text \<open>
  The set @{const split_below} is the lower part produced by a Pull boundary:
  it keeps exactly those sources whose current labels are below \<open>beta\<close>.  The
  first lemmas show that this split respects the finite bound, preserves the
  tree-antichain property, and cannot increase the scaled cardinality used by
  the FindPivots cap.  These are small facts, but they are the side conditions
  needed before the lower recursive call can be formed.
\<close>

definition complete_tree_cover where
  "complete_tree_cover d S B \<longleftrightarrow> (\<forall>v\<in>bound_tree S B. through_complete d S v)"

definition range_tree where
  "range_tree S a B =
    {v \<in> tree_set S. a \<le> dist s v \<and> below_bound (dist s v) B}"

fun nondecreasing_from where
  "nondecreasing_from a [] \<longleftrightarrow> True"
| "nondecreasing_from a (b # bs) \<longleftrightarrow> a \<le> b \<and> nondecreasing_from b bs"

fun bounds_le where
  "bounds_le B [] \<longleftrightarrow> True"
| "bounds_le B (b # bs) \<longleftrightarrow> bound_le (Fin b) B \<and> bounds_le B bs"

fun range_tree_chain where
  "range_tree_chain S a [] B = range_tree S a B"
| "range_tree_chain S a (b # bs) B =
    range_tree S a (Fin b) \<union> range_tree_chain S b bs B"

fun range_tree_chain_list where
  "range_tree_chain_list S a [] B = [range_tree S a B]"
| "range_tree_chain_list S a (b # bs) B =
    range_tree S a (Fin b) # range_tree_chain_list S b bs B"

text \<open>
  The predicates @{const complete_tree_cover} and @{const range_tree} describe
  the two main geometric facts used by the loop.  A complete tree cover says
  every vertex in a bounded tree is certified by a complete source.  A range
  tree is the part of a source tree whose true distances lie between a lower
  boundary and an upper bound.  The functions @{const range_tree_chain} and
  @{const range_tree_chain_list} extend this to a monotone list of child
  boundaries; the list form is convenient for relating one child postcondition
  to one child range.
\<close>

lemma below_bound_strict_trans:
  assumes "a < b" "below_bound b B"
  shows "below_bound a B"
  using assms by (cases B) auto

lemma complete_verticesD:
  assumes "u \<in> complete_vertices d"
  shows "u \<in> V" "reachable s u" "d u = dist s u"
  using assms unfolding complete_vertices_def by auto

lemma bound_tree_complete_vertices_eq:
  assumes cover:
    "\<And>u. \<lbrakk>u \<in> S; reachable s u; below_bound (dist s u) B;
       d u \<noteq> dist s u\<rbrakk> \<Longrightarrow> through_complete d S u"
  shows "bound_tree S B = bound_tree (S \<inter> complete_vertices d) B"
proof
  show "bound_tree (S \<inter> complete_vertices d) B \<subseteq> bound_tree S B"
    using bound_tree_mono[of "S \<inter> complete_vertices d" S B] by blast
next
  show "bound_tree S B \<subseteq> bound_tree (S \<inter> complete_vertices d) B"
  proof
    fix v
    assume v_bound: "v \<in> bound_tree S B"
    then have vV: "v \<in> V" and reach_v: "reachable s v"
      and through_S: "through S v" and below_v: "below_bound (dist s v) B"
      unfolding bound_tree_def by auto
    obtain u where uS: "u \<in> S" and uv: "tree_path u v"
      using through_iff_tree_path[OF reach_v, of S] through_S by blast
    have reach_u: "reachable s u"
      using tree_path_root_reachable[OF uv] .
    have u_below: "below_bound (dist s u) B"
      using tree_path_dist_le[OF uv] below_v
      by (cases B) auto
    have "through (S \<inter> complete_vertices d) v"
    proof (cases "d u = dist s u")
      case True
      have u_complete: "u \<in> complete_vertices d"
        using tree_path_root_in_V[OF uv] reach_u True
        unfolding complete_vertices_def by blast
      have u_path: "u \<in> set (shortest_path_to v)"
        using uv by (auto dest: tree_pathD)
      have sp_v: "shortest_walk s (shortest_path_to v) v"
        using shortest_path_to_shortest[OF reach_v] .
      show ?thesis
        using uS u_complete sp_v u_path unfolding through_def by blast
    next
      case False
      have "through_complete d S u"
        using cover[OF uS reach_u u_below False] .
      then have "through (S \<inter> complete_vertices d) u"
        unfolding through_complete_def .
      then obtain q where qS: "q \<in> S \<inter> complete_vertices d"
        and qu: "tree_path q u"
        using through_iff_tree_path[OF reach_u, of "S \<inter> complete_vertices d"]
        by blast
      have qv: "tree_path q v"
        using tree_path_trans[OF uv qu] .
      have q_path: "q \<in> set (shortest_path_to v)"
        using qv by (auto dest: tree_pathD)
      have sp_v: "shortest_walk s (shortest_path_to v) v"
        using shortest_path_to_shortest[OF reach_v] .
      show ?thesis
        using qS sp_v q_path unfolding through_def by blast
    qed
    then show "v \<in> bound_tree (S \<inter> complete_vertices d) B"
      using vV reach_v below_v unfolding bound_tree_def by blast
  qed
qed

lemma bmssp_pre_full_bound_tree_complete_vertices_eq:
  assumes pre: "bmssp_pre_full d S B"
  shows "bound_tree S B = bound_tree (S \<inter> complete_vertices d) B"
proof (rule bound_tree_complete_vertices_eq)
  fix u
  assume uS: "u \<in> S" and reach_u: "reachable s u"
    and below_u: "below_bound (dist s u) B"
    and incomplete_u: "d u \<noteq> dist s u"
  have "u \<in> V"
    using uS pre unfolding bmssp_pre_full_def by blast
  then show "through_complete d S u"
    using uS reach_u below_u incomplete_u pre unfolding bmssp_pre_full_def by blast
qed

lemma bound_tree_complete_vertices_eq_imp_cover:
  assumes eq: "bound_tree S B = bound_tree (S \<inter> complete_vertices d) B"
  shows "complete_tree_cover d S B"
proof (unfold complete_tree_cover_def, intro ballI)
  fix v
  assume "v \<in> bound_tree S B"
  then have "v \<in> bound_tree (S \<inter> complete_vertices d) B"
    using eq by simp
  then have "through (S \<inter> complete_vertices d) v"
    unfolding bound_tree_def by blast
  then show "through_complete d S v"
    unfolding through_complete_def by simp
qed

lemma bmssp_pre_full_complete_tree_cover:
  assumes pre: "bmssp_pre_full d S B"
  shows "complete_tree_cover d S B"
  using bound_tree_complete_vertices_eq_imp_cover
    [OF bmssp_pre_full_bound_tree_complete_vertices_eq[OF pre]] .

lemma bmssp_pre_full_bound_mono:
  assumes pre: "bmssp_pre_full d S B"
    and le: "bound_le B' B"
  shows "bmssp_pre_full d S B'"
proof -
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have cover:
    "\<And>v. \<lbrakk>v \<in> V; reachable s v; below_bound (dist s v) B';
       d v \<noteq> dist s v\<rbrakk> \<Longrightarrow> through_complete d S v"
  proof -
    fix v
    assume v: "v \<in> V" "reachable s v" "below_bound (dist s v) B'"
      "d v \<noteq> dist s v"
    have "below_bound (dist s v) B"
      using le v(3) by (cases B'; cases B) auto
    then show "through_complete d S v"
      using pre v unfolding bmssp_pre_full_def by blast
  qed
  show ?thesis
    using S_subset cover unfolding bmssp_pre_full_def by blast
qed

theorem concrete_find_pivots_complete_pivot_tree:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "bound_tree (find_pivots_pivots k d S B) B =
    bound_tree
      (find_pivots_pivots k d S B \<inter>
        complete_vertices (find_pivots_label k d S B)) B"
  using bmssp_pre_full_bound_tree_complete_vertices_eq
    [OF find_pivots_establishes_pivot_pre_concrete[OF sound pre S_reaches]] .

theorem concrete_find_pivots_pivot_tree_cover:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "complete_tree_cover
    (find_pivots_label k d S B)
    (find_pivots_pivots k d S B) B"
  using bmssp_pre_full_complete_tree_cover
    [OF find_pivots_establishes_pivot_pre_concrete[OF sound pre S_reaches]] .

theorem concrete_capped_find_pivots_complete_pivot_tree:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "bound_tree (find_pivots_pivots_capped k cap d S B) B =
    bound_tree
      (find_pivots_pivots_capped k cap d S B \<inter>
        complete_vertices (find_pivots_label_capped k cap d S B)) B"
  using bmssp_pre_full_bound_tree_complete_vertices_eq
    [OF find_pivots_capped_establishes_pivot_pre_concrete[OF sound pre S_reaches]] .

theorem concrete_capped_find_pivots_pivot_tree_cover:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "complete_tree_cover
    (find_pivots_label_capped k cap d S B)
    (find_pivots_pivots_capped k cap d S B) B"
  using bmssp_pre_full_complete_tree_cover
    [OF find_pivots_capped_establishes_pivot_pre_concrete[OF sound pre S_reaches]] .

lemma through_complete_obtain:
  assumes "through_complete d S v"
  obtains u p where
    "u \<in> S"
    "u \<in> complete_vertices d"
    "shortest_walk s p v"
    "u \<in> set p"
    "d u = dist s u"
    "dist s u \<le> dist s v"
proof -
  obtain u p where u: "u \<in> S" "u \<in> complete_vertices d" "shortest_walk s p v" "u \<in> set p"
    using assms unfolding through_complete_def through_def by blast
  have "d u = dist s u"
    using u(2) unfolding complete_vertices_def by blast
  moreover have "dist s u \<le> dist s v"
    using shortest_walk_prefix_dist_le u by blast
  ultimately show thesis
    using that u by blast
qed

lemma pull_minimum_incomplete_covered:
  assumes pre: "bmssp_pre_full d S B"
    and beta: "below_bound beta B"
    and vV: "v \<in> V"
    and reach: "reachable s v"
    and lt: "dist s v < beta"
    and incomplete: "d v \<noteq> dist s v"
  shows "through_complete d (split_below d S beta) v"
proof -
  have below_v_B: "below_bound (dist s v) B"
    using below_bound_strict_trans[OF lt beta] .
  have cover: "through_complete d S v"
    using pre vV reach below_v_B incomplete unfolding bmssp_pre_full_def by blast
  then obtain u p where uS: "u \<in> S" and ucomp: "u \<in> complete_vertices d"
    and p: "shortest_walk s p v" and up: "u \<in> set p"
    and du: "d u = dist s u" and dist_le: "dist s u \<le> dist s v"
    by (rule through_complete_obtain)
  have "d u < beta"
    using du dist_le lt by linarith
  then have "u \<in> split_below d S beta"
    using uS unfolding split_below_def by blast
  then have "through (split_below d S beta \<inter> complete_vertices d) v"
    using ucomp p up unfolding through_def by blast
  then show ?thesis
    unfolding through_complete_def .
qed

lemma pull_minimum_pre_for_lower_split:
  assumes pre: "bmssp_pre_full d S B"
    and beta: "below_bound beta B"
  shows "bmssp_pre_full d (split_below d S beta) (Fin beta)"
proof -
  have S_subset: "split_below d S beta \<subseteq> V"
    using pre unfolding bmssp_pre_full_def split_below_def by blast
  have cover:
    "\<And>v. \<lbrakk>v \<in> V; reachable s v; below_bound (dist s v) (Fin beta); d v \<noteq> dist s v\<rbrakk>
      \<Longrightarrow> through_complete d (split_below d S beta) v"
    using pull_minimum_incomplete_covered[OF pre beta] by auto
  show ?thesis
    using S_subset cover unfolding bmssp_pre_full_def by blast
qed

lemma split_below_subset:
  "split_below d S beta \<subseteq> S"
  unfolding split_below_def by blast

lemma range_tree_eq_bound_diff:
  "range_tree S a B = bound_tree S B - bound_tree S (Fin a)"
  unfolding range_tree_def bound_tree_eq_tree_set by auto

lemma range_tree_subset_bound_tree:
  "range_tree S a B \<subseteq> bound_tree S B"
  unfolding range_tree_eq_bound_diff by blast

lemma finite_bound_tree [simp]:
  "finite (bound_tree S B)"
proof -
  have "bound_tree S B \<subseteq> V"
    unfolding bound_tree_def by blast
  then show ?thesis
    using finite_subset[OF _ finite_V] by blast
qed

lemma finite_range_tree [simp]:
  "finite (range_tree S a B)"
proof -
  have "range_tree S a B \<subseteq> V"
    unfolding range_tree_def tree_set_def by blast
  then show ?thesis
    using finite_subset[OF _ finite_V] by blast
qed

lemma finite_range_tree_chain [simp]:
  "finite (range_tree_chain S a bs B)"
  by (induction bs arbitrary: a) simp_all

lemma finite_range_tree_chain_list_sets [simp]:
  assumes "X \<in> set (range_tree_chain_list S a bs B)"
  shows "finite X"
  using assms by (induction bs arbitrary: a) auto

lemma Union_range_tree_chain_list:
  "\<Union>(set (range_tree_chain_list S a bs B)) = range_tree_chain S a bs B"
  by (induction bs arbitrary: a) auto

lemma range_tree_chain_lower_bound:
  assumes mono: "nondecreasing_from a bs"
    and x: "x \<in> range_tree_chain S a bs B"
  shows "a \<le> dist s x"
  using assms
proof (induction bs arbitrary: a)
  case Nil
  then show ?case
    by (simp add: range_tree_def)
next
  case (Cons b bs)
  then consider "x \<in> range_tree S a (Fin b)" |
    "x \<in> range_tree_chain S b bs B"
    by auto
  then show ?case
  proof cases
    case 1
    then show ?thesis
      unfolding range_tree_def by blast
  next
    case 2
    have "b \<le> dist s x"
      using Cons.IH[of b] Cons.prems 2 by simp
    moreover have "a \<le> b"
      using Cons.prems by simp
    ultimately show ?thesis
      by linarith
  qed
qed

lemma range_tree_disjoint_lower:
  "bound_tree S (Fin a) \<inter> range_tree S a B = {}"
  unfolding range_tree_eq_bound_diff by blast

lemma bound_tree_disjoint_range_tree_chain:
  assumes mono: "nondecreasing_from a bs"
  shows "bound_tree S (Fin a) \<inter> range_tree_chain S a bs B = {}"
proof
  show "bound_tree S (Fin a) \<inter> range_tree_chain S a bs B \<subseteq> {}"
  proof
    fix x
    assume x: "x \<in> bound_tree S (Fin a) \<inter> range_tree_chain S a bs B"
    then have "dist s x < a"
      unfolding bound_tree_def by auto
    moreover have "a \<le> dist s x"
      using range_tree_chain_lower_bound[OF mono] x by blast
    ultimately show "x \<in> {}"
      by simp
  qed
qed simp

lemma range_tree_disjoint_range_tree_chain_tail:
  assumes a_le_b: "a \<le> b"
    and mono_tail: "nondecreasing_from b bs"
  shows "range_tree S a (Fin b) \<inter> range_tree_chain S b bs B = {}"
proof
  show "range_tree S a (Fin b) \<inter> range_tree_chain S b bs B \<subseteq> {}"
  proof
    fix x
    assume x: "x \<in> range_tree S a (Fin b) \<inter> range_tree_chain S b bs B"
    then have "dist s x < b"
      unfolding range_tree_def by auto
    moreover have "b \<le> dist s x"
      using range_tree_chain_lower_bound[OF mono_tail] x by blast
    ultimately show "x \<in> {}"
      by simp
  qed
qed simp

lemma card_range_tree_chain_eq_sum_list:
  assumes mono: "nondecreasing_from a bs"
  shows "card (range_tree_chain S a bs B) =
    sum_list (map card (range_tree_chain_list S a bs B))"
  using mono
proof (induction bs arbitrary: a)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  have a_le_b: "a \<le> b"
    using Cons.prems by simp
  have mono_tail: "nondecreasing_from b bs"
    using Cons.prems by simp
  have disjoint:
    "range_tree S a (Fin b) \<inter> range_tree_chain S b bs B = {}"
    using range_tree_disjoint_range_tree_chain_tail[OF a_le_b mono_tail] .
  have card_union:
    "card (range_tree S a (Fin b) \<union> range_tree_chain S b bs B) =
      card (range_tree S a (Fin b)) + card (range_tree_chain S b bs B)"
    by (rule card_Un_disjoint) (simp_all add: disjoint)
  show ?case
    using card_union Cons.IH[OF mono_tail] by simp
qed

lemma sum_list_map_mult_left:
  fixes c :: nat
    and f :: "'a \<Rightarrow> nat"
  shows "sum_list (map (\<lambda>x. c * f x) xs) = c * sum_list (map f xs)"
  by (induction xs) (simp_all add: algebra_simps)

lemma sum_list_map_card_mult_left:
  fixes C :: nat
    and Xs :: "'v set list"
  shows "sum_list (map (\<lambda>X. C * card X) Xs) = C * sum_list (map card Xs)"
  by (induction Xs) (simp_all add: algebra_simps)

lemma sum_list_le_if_list_all2:
  assumes "list_all2 (\<lambda>c X. c \<le> C * card X) costs Xs"
  shows "sum_list costs \<le> sum_list (map (\<lambda>X. C * card X) Xs)"
  using assms
proof (induction rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons c X costs Xs)
  then show ?case by simp
qed

lemma child_costs_le_range_tree_chain_card:
  assumes mono: "nondecreasing_from a bs"
    and costs: "list_all2 (\<lambda>c X. c \<le> C * card X) costs
      (range_tree_chain_list S a bs B)"
  shows "sum_list costs \<le> C * card (range_tree_chain S a bs B)"
proof -
  have "sum_list costs \<le>
    sum_list (map (\<lambda>X. C * card X) (range_tree_chain_list S a bs B))"
    using sum_list_le_if_list_all2[OF costs] .
  also have "\<dots> =
    C * sum_list (map card (range_tree_chain_list S a bs B))"
    by (rule sum_list_map_card_mult_left)
  also have "\<dots> = C * card (range_tree_chain S a bs B)"
    using card_range_tree_chain_eq_sum_list[OF mono, of S B] by simp
  finally show ?thesis .
qed

lemma range_tree_adjacent_disjoint:
  "range_tree S a (Fin b) \<inter> range_tree S b B = {}"
  unfolding range_tree_def by auto

lemma range_tree_adjacent_union:
  assumes "a \<le> b"
    and "bound_le (Fin b) B"
  shows "range_tree S a (Fin b) \<union> range_tree S b B = range_tree S a B"
  using assms unfolding range_tree_def by (cases B) auto

lemma bound_tree_split_at:
  assumes "bound_le (Fin a) B"
  shows "bound_tree S B = bound_tree S (Fin a) \<union> range_tree S a B"
  using assms unfolding range_tree_def bound_tree_eq_tree_set
  by (cases B) auto

lemma bound_tree_adjacent_union:
  assumes "a \<le> b"
    and "bound_le (Fin b) B"
  shows "bound_tree S (Fin a) \<union> range_tree S a (Fin b) \<union> range_tree S b B =
    bound_tree S B"
proof -
  have union: "range_tree S a (Fin b) \<union> range_tree S b B = range_tree S a B"
    using range_tree_adjacent_union[OF assms] .
  have le_a_B: "bound_le (Fin a) B"
    using assms by (cases B) auto
  show ?thesis
    using union bound_tree_split_at[OF le_a_B, of S]
    by (cases B) auto
qed

lemma complete_on_Un:
  assumes "complete_on d A" "complete_on d B"
  shows "complete_on d (A \<union> B)"
  using assms unfolding complete_on_def by blast

lemma complete_on_Union_list:
  assumes "\<And>X. X \<in> set Xs \<Longrightarrow> complete_on d X"
  shows "complete_on d (\<Union>(set Xs))"
  using assms unfolding complete_on_def by blast

lemma complete_on_bound_tree_split:
  assumes "bound_le (Fin a) B"
    and lower: "complete_on d (bound_tree S (Fin a))"
    and upper: "complete_on d (range_tree S a B)"
  shows "complete_on d (bound_tree S B)"
proof -
  have "complete_on d (bound_tree S (Fin a) \<union> range_tree S a B)"
    using complete_on_Un[OF lower upper] .
  then show ?thesis
    using bound_tree_split_at[OF assms(1), of S] by simp
qed

lemma bound_tree_range_chain_union:
  assumes mono: "nondecreasing_from a bs"
    and bounds: "bounds_le B (a # bs)"
  shows "bound_tree S (Fin a) \<union> range_tree_chain S a bs B = bound_tree S B"
  using assms
proof (induction bs arbitrary: a)
  case Nil
  then show ?case
    using bound_tree_split_at[of a B S] by simp
next
  case (Cons b bs)
  have a_le_b: "a \<le> b"
    using Cons.prems(1) by simp
  have mono_tail: "nondecreasing_from b bs"
    using Cons.prems(1) by simp
  have b_le_B: "bound_le (Fin b) B"
    using Cons.prems(2) by simp
  have bounds_tail: "bounds_le B (b # bs)"
    using Cons.prems(2) by simp
  have split_ab:
    "bound_tree S (Fin b) = bound_tree S (Fin a) \<union> range_tree S a (Fin b)"
    using bound_tree_split_at[of a "Fin b" S] a_le_b by simp
  have tail:
    "bound_tree S (Fin b) \<union> range_tree_chain S b bs B = bound_tree S B"
    using Cons.IH[OF mono_tail bounds_tail] .
  show ?case
    using split_ab tail by auto
qed

lemma card_bound_tree_range_chain_union:
  assumes mono: "nondecreasing_from a bs"
    and bounds: "bounds_le B (a # bs)"
  shows "card (bound_tree S B) =
    card (bound_tree S (Fin a)) + card (range_tree_chain S a bs B)"
proof -
  have union: "bound_tree S (Fin a) \<union> range_tree_chain S a bs B = bound_tree S B"
    using bound_tree_range_chain_union[OF mono bounds, of S] .
  have disjoint: "bound_tree S (Fin a) \<inter> range_tree_chain S a bs B = {}"
    using bound_tree_disjoint_range_tree_chain[OF mono, of S] .
  have "card (bound_tree S (Fin a) \<union> range_tree_chain S a bs B) =
    card (bound_tree S (Fin a)) + card (range_tree_chain S a bs B)"
    by (rule card_Un_disjoint) (simp_all add: disjoint)
  then show ?thesis
    using union by simp
qed

lemma complete_on_range_chain_union:
  assumes mono: "nondecreasing_from a bs"
    and bounds: "bounds_le B (a # bs)"
    and lower: "complete_on d (bound_tree S (Fin a))"
    and chain: "complete_on d (range_tree_chain S a bs B)"
  shows "complete_on d (bound_tree S B)"
proof -
  have "complete_on d (bound_tree S (Fin a) \<union> range_tree_chain S a bs B)"
    using complete_on_Un[OF lower chain] .
  then show ?thesis
    using bound_tree_range_chain_union[OF mono bounds, of S] by simp
qed

lemma complete_on_range_tree_chain_list:
  assumes "\<And>X. X \<in> set (range_tree_chain_list S a bs B) \<Longrightarrow> complete_on d X"
  shows "complete_on d (range_tree_chain S a bs B)"
proof -
  have "complete_on d (\<Union>(set (range_tree_chain_list S a bs B)))"
    using complete_on_Union_list[OF assms] .
  then show ?thesis
    using Union_range_tree_chain_list[of S a bs B] by simp
qed

theorem partition_loop_trace_assembly_post:
  assumes le: "bound_le B' B"
    and mono: "nondecreasing_from a bs"
    and bounds: "bounds_le B' (a # bs)"
    and lower: "complete_on d' (bound_tree S (Fin a))"
    and children: "list_all2 (\<lambda>U X. U = X \<and> complete_on d' U) Us
      (range_tree_chain_list S a bs B')"
    and U_def: "U = bound_tree S (Fin a) \<union> \<Union>(set Us)"
  shows "bmssp_post_full d S B d' B' U"
proof -
  have Union_eq:
    "\<Union>(set Us) = \<Union>(set (range_tree_chain_list S a bs B'))"
    using children by (induction rule: list_all2_induct) auto
  have children_complete: "\<And>X. X \<in> set Us \<Longrightarrow> complete_on d' X"
    using children by (induction rule: list_all2_induct) auto
  have chain_complete: "complete_on d' (range_tree_chain S a bs B')"
  proof -
    have "complete_on d' (\<Union>(set Us))"
      by (rule complete_on_Union_list[OF children_complete])
    then show ?thesis
      using Union_eq Union_range_tree_chain_list[of S a bs B'] by simp
  qed
  have U_tree: "U = bound_tree S B'"
    using U_def Union_eq Union_range_tree_chain_list[of S a bs B']
      bound_tree_range_chain_union[OF mono bounds, of S]
    by simp
  have "complete_on d' U"
    unfolding U_def
    using complete_on_Un[OF lower]
      complete_on_Union_list[OF children_complete] by blast
  then show ?thesis
    using le U_tree unfolding bmssp_post_full_def by blast
qed

text \<open>
  The range-chain lemmas culminate in
  @{thm partition_loop_trace_assembly_post}.  The hypotheses are exactly the
  certificate carried by the concrete partition trace: a returned bound below
  the input bound, nondecreasing child boundaries, child bounds below the
  returned bound, completeness of the lower prefix, and one completed set for
  each range in @{const range_tree_chain_list}.  The theorem proves that their
  union is precisely @{const bound_tree} for the returned bound and that the
  final labels are complete there.
\<close>

lemma pull_minimum_bound_tree_lower_split:
  assumes cover: "complete_tree_cover d S (Fin beta)"
    and beta'_le: "beta' \<le> beta"
  shows "bound_tree S (Fin beta') = bound_tree (split_below d S beta) (Fin beta')"
proof
  show "bound_tree S (Fin beta') \<subseteq> bound_tree (split_below d S beta) (Fin beta')"
  proof
    fix v
    assume v: "v \<in> bound_tree S (Fin beta')"
    then have vV: "v \<in> V" and reach_v: "reachable s v"
      and through_S: "through S v" and lt_beta': "dist s v < beta'"
      unfolding bound_tree_def by auto
    have v_beta: "v \<in> bound_tree S (Fin beta)"
      using v beta'_le unfolding bound_tree_def by auto
    then have "through_complete d S v"
      using cover unfolding complete_tree_cover_def by blast
    then obtain u p where uS: "u \<in> S" and ucomp: "u \<in> complete_vertices d"
      and p: "shortest_walk s p v" and up: "u \<in> set p"
      and du: "d u = dist s u" and dist_le: "dist s u \<le> dist s v"
      by (rule through_complete_obtain)
    have "d u < beta"
      using du dist_le lt_beta' beta'_le by linarith
    then have "u \<in> split_below d S beta"
      using uS unfolding split_below_def by blast
    then have "through (split_below d S beta) v"
      using p up unfolding through_def by blast
    then show "v \<in> bound_tree (split_below d S beta) (Fin beta')"
      using vV reach_v lt_beta' unfolding bound_tree_def by auto
  qed
next
  show "bound_tree (split_below d S beta) (Fin beta') \<subseteq> bound_tree S (Fin beta')"
    using bound_tree_mono[OF split_below_subset[of d S beta], of "Fin beta'"] by blast
qed

lemma pull_recursive_post_lifts_bound_tree:
  assumes cover: "complete_tree_cover d S (Fin beta)"
    and post: "bmssp_post_full d (split_below d S beta) (Fin beta) d' B' U"
  shows "U = bound_tree S B'"
proof -
  have le: "bound_le B' (Fin beta)"
    and U: "U = bound_tree (split_below d S beta) B'"
    using post unfolding bmssp_post_full_def by auto
  show ?thesis
  proof (cases B')
    case Infinity
    then have False
      using le by simp
    then show ?thesis
      by blast
  next
    case (Fin beta')
    then have beta'_le: "beta' \<le> beta"
      using le by simp
    have "bound_tree S (Fin beta') =
      bound_tree (split_below d S beta) (Fin beta')"
      using pull_minimum_bound_tree_lower_split[OF cover beta'_le] .
    then show ?thesis
      using U Fin by simp
  qed
qed

theorem concrete_find_pivots_pull_pre:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and beta: "below_bound beta B"
  shows "bmssp_pre_full
    (find_pivots_label k d S B)
    (split_below (find_pivots_label k d S B)
      (find_pivots_pivots k d S B) beta)
    (Fin beta)"
proof -
  have pivot_pre:
    "bmssp_pre_full
      (find_pivots_label k d S B)
      (find_pivots_pivots k d S B) B"
    using find_pivots_establishes_pivot_pre_concrete[OF sound pre S_reaches] .
  show ?thesis
    using pull_minimum_pre_for_lower_split[OF pivot_pre beta] .
qed

theorem concrete_capped_find_pivots_pull_pre:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and beta: "below_bound beta B"
  shows "bmssp_pre_full
    (find_pivots_label_capped k cap d S B)
    (split_below (find_pivots_label_capped k cap d S B)
      (find_pivots_pivots_capped k cap d S B) beta)
    (Fin beta)"
proof -
  have pivot_pre:
    "bmssp_pre_full
      (find_pivots_label_capped k cap d S B)
      (find_pivots_pivots_capped k cap d S B) B"
    using find_pivots_capped_establishes_pivot_pre_concrete[OF sound pre S_reaches] .
  show ?thesis
    using pull_minimum_pre_for_lower_split[OF pivot_pre beta] .
qed

theorem concrete_find_pivots_pull_bound_tree_lower:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and beta: "below_bound beta B"
    and beta'_le: "beta' \<le> beta"
  shows "bound_tree (find_pivots_pivots k d S B) (Fin beta') =
    bound_tree
      (split_below (find_pivots_label k d S B)
        (find_pivots_pivots k d S B) beta)
      (Fin beta')"
proof -
  let ?d' = "find_pivots_label k d S B"
  let ?P = "find_pivots_pivots k d S B"
  have pivot_pre_B: "bmssp_pre_full ?d' ?P B"
    using find_pivots_establishes_pivot_pre_concrete[OF sound pre S_reaches] .
  have pivot_pre_beta: "bmssp_pre_full ?d' ?P (Fin beta)"
    using bmssp_pre_full_bound_mono[OF pivot_pre_B] beta
    by (cases B) auto
  have cover_beta: "complete_tree_cover ?d' ?P (Fin beta)"
    using bmssp_pre_full_complete_tree_cover[OF pivot_pre_beta] .
  show ?thesis
    using pull_minimum_bound_tree_lower_split[OF cover_beta beta'_le] .
qed

theorem concrete_capped_find_pivots_pull_bound_tree_lower:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and beta: "below_bound beta B"
    and beta'_le: "beta' \<le> beta"
  shows "bound_tree (find_pivots_pivots_capped k cap d S B) (Fin beta') =
    bound_tree
      (split_below (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) beta)
      (Fin beta')"
proof -
  let ?d' = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  have pivot_pre_B: "bmssp_pre_full ?d' ?P B"
    using find_pivots_capped_establishes_pivot_pre_concrete[OF sound pre S_reaches] .
  have pivot_pre_beta: "bmssp_pre_full ?d' ?P (Fin beta)"
    using bmssp_pre_full_bound_mono[OF pivot_pre_B] beta
    by (cases B) auto
  have cover_beta: "complete_tree_cover ?d' ?P (Fin beta)"
    using bmssp_pre_full_complete_tree_cover[OF pivot_pre_beta] .
  show ?thesis
    using pull_minimum_bound_tree_lower_split[OF cover_beta beta'_le] .
qed

theorem concrete_find_pivots_pull_recursive_post_lifts:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and beta: "below_bound beta B"
    and post: "bmssp_post_full
      (find_pivots_label k d S B)
      (split_below (find_pivots_label k d S B)
        (find_pivots_pivots k d S B) beta)
      (Fin beta) d'' B' U"
  shows "U = bound_tree (find_pivots_pivots k d S B) B'"
proof -
  let ?d' = "find_pivots_label k d S B"
  let ?P = "find_pivots_pivots k d S B"
  have pivot_pre_B: "bmssp_pre_full ?d' ?P B"
    using find_pivots_establishes_pivot_pre_concrete[OF sound pre S_reaches] .
  have pivot_pre_beta: "bmssp_pre_full ?d' ?P (Fin beta)"
    using bmssp_pre_full_bound_mono[OF pivot_pre_B] beta
    by (cases B) auto
  have cover_beta: "complete_tree_cover ?d' ?P (Fin beta)"
    using bmssp_pre_full_complete_tree_cover[OF pivot_pre_beta] .
  show ?thesis
    using pull_recursive_post_lifts_bound_tree[OF cover_beta post] .
qed

theorem concrete_capped_find_pivots_pull_recursive_post_lifts:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and beta: "below_bound beta B"
    and post: "bmssp_post_full
      (find_pivots_label_capped k cap d S B)
      (split_below (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) beta)
      (Fin beta) d'' B' U"
  shows "U = bound_tree (find_pivots_pivots_capped k cap d S B) B'"
proof -
  let ?d' = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  have pivot_pre_B: "bmssp_pre_full ?d' ?P B"
    using find_pivots_capped_establishes_pivot_pre_concrete[OF sound pre S_reaches] .
  have pivot_pre_beta: "bmssp_pre_full ?d' ?P (Fin beta)"
    using bmssp_pre_full_bound_mono[OF pivot_pre_B] beta
    by (cases B) auto
  have cover_beta: "complete_tree_cover ?d' ?P (Fin beta)"
    using bmssp_pre_full_complete_tree_cover[OF pivot_pre_beta] .
  show ?thesis
    using pull_recursive_post_lifts_bound_tree[OF cover_beta post] .
qed

text \<open>
  The Pull-minimum lemmas connect the range algebra to FindPivots.  Once
  FindPivots establishes a pivot precondition, @{const split_below} can be used
  as the source set for a recursive call below a Pull boundary.  If that
  recursive call returns a BMSSP postcondition for the split set, the lifting
  lemmas identify its output tree with the corresponding pivot tree.  Both
  capped and uncapped FindPivots variants have parallel theorems because later
  operational relations use the capped executable search.
\<close>

theorem concrete_find_pivots_final_tree_assembly:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and loop: "bmssp_post_full
      (find_pivots_label k d S B)
      (find_pivots_pivots k d S B) B d_loop B' U_loop"
  shows "U_loop \<union>
      {v \<in> bound_tree S B'. find_pivots_label k d S B v = dist s v} =
    bound_tree S B'"
proof -
  let ?d' = "find_pivots_label k d S B"
  let ?P = "find_pivots_pivots k d S B"
  let ?W = "{v \<in> bound_tree S B'. ?d' v = dist s v}"
  have loop_le: "bound_le B' B" and U_loop: "U_loop = bound_tree ?P B'"
    using loop unfolding bmssp_post_full_def by auto
  have P_subset_S: "?P \<subseteq> S"
    unfolding find_pivots_pivots_def by blast
  have pivot_pre: "bmssp_pre_full ?d' ?P B"
    using find_pivots_establishes_pivot_pre_concrete[OF sound pre S_reaches] .
  show ?thesis
  proof
    show "U_loop \<union> ?W \<subseteq> bound_tree S B'"
    proof
      fix v
      assume "v \<in> U_loop \<union> ?W"
      then show "v \<in> bound_tree S B'"
      proof
        assume "v \<in> U_loop"
        then have "v \<in> bound_tree ?P B'"
          using U_loop by simp
        then show ?thesis
          using bound_tree_mono[OF P_subset_S, of B'] by blast
      next
        assume "v \<in> ?W"
        then show ?thesis
          by blast
      qed
    qed
  next
    show "bound_tree S B' \<subseteq> U_loop \<union> ?W"
    proof
      fix v
      assume v_bound: "v \<in> bound_tree S B'"
      then have vV: "v \<in> V" and reach_v: "reachable s v"
        and below_B': "below_bound (dist s v) B'"
        unfolding bound_tree_def by auto
      show "v \<in> U_loop \<union> ?W"
      proof (cases "?d' v = dist s v")
        case True
        then show ?thesis
          using v_bound by blast
      next
        case False
        have below_B: "below_bound (dist s v) B"
          using loop_le below_B' by (cases B'; cases B) auto
        have "through_complete ?d' ?P v"
          using pivot_pre vV reach_v below_B False
          unfolding bmssp_pre_full_def by blast
        then have "through ?P v"
          by (rule through_complete_imp_through)
        then have "v \<in> bound_tree ?P B'"
          using vV reach_v below_B' unfolding bound_tree_def by blast
        then show ?thesis
          using U_loop by blast
      qed
    qed
  qed
qed

theorem concrete_capped_find_pivots_final_tree_assembly:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and loop: "bmssp_post_full
      (find_pivots_label_capped k cap d S B)
      (find_pivots_pivots_capped k cap d S B) B d_loop B' U_loop"
  shows "U_loop \<union>
      {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} =
    bound_tree S B'"
proof -
  let ?d' = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  let ?W = "{v \<in> bound_tree S B'. ?d' v = dist s v}"
  have loop_le: "bound_le B' B" and U_loop: "U_loop = bound_tree ?P B'"
    using loop unfolding bmssp_post_full_def by auto
  have pivot_pre: "bmssp_pre_full ?d' ?P B"
    using find_pivots_capped_establishes_pivot_pre_concrete[OF sound pre S_reaches] .
  have P_subset_V: "?P \<subseteq> V"
    using pivot_pre unfolding bmssp_pre_full_def by blast
  have P_through_S:
    "\<And>v. v \<in> bound_tree ?P B' \<Longrightarrow> v \<in> bound_tree S B'"
  proof -
    fix v
    assume vP: "v \<in> bound_tree ?P B'"
    then have vV: "v \<in> V" and reach_v: "reachable s v"
      and through_P: "through ?P v" and below_v: "below_bound (dist s v) B'"
      unfolding bound_tree_def by auto
    have "through S v"
    proof -
      obtain u p where uP: "u \<in> ?P" and sp: "shortest_walk s p v" and up: "u \<in> set p"
        using through_P unfolding through_def by blast
      have "u \<in> S"
      proof (cases "card (find_pivots_seen_capped k cap d S B) > cap")
        case True
        then show ?thesis
          using uP unfolding find_pivots_pivots_capped_def by simp
      next
        case False
        then show ?thesis
          using uP unfolding find_pivots_pivots_capped_def by auto
      qed
      then show ?thesis
        using sp up unfolding through_def by blast
    qed
    then show "v \<in> bound_tree S B'"
      using vV reach_v below_v unfolding bound_tree_def by blast
  qed
  show ?thesis
  proof
    show "U_loop \<union> ?W \<subseteq> bound_tree S B'"
      using U_loop P_through_S by blast
  next
    show "bound_tree S B' \<subseteq> U_loop \<union> ?W"
    proof
      fix v
      assume v_bound: "v \<in> bound_tree S B'"
      then have vV: "v \<in> V" and reach_v: "reachable s v"
        and below_B': "below_bound (dist s v) B'"
        unfolding bound_tree_def by auto
      show "v \<in> U_loop \<union> ?W"
      proof (cases "?d' v = dist s v")
        case True
        then show ?thesis
          using v_bound by blast
      next
        case False
        have below_B: "below_bound (dist s v) B"
          using loop_le below_B' by (cases B'; cases B) auto
        have "through_complete ?d' ?P v"
          using pivot_pre vV reach_v below_B False
          unfolding bmssp_pre_full_def by blast
        then have "through ?P v"
          by (rule through_complete_imp_through)
        then have "v \<in> bound_tree ?P B'"
          using vV reach_v below_B' unfolding bound_tree_def by blast
        then show ?thesis
          using U_loop by blast
      qed
    qed
  qed
qed

theorem concrete_find_pivots_final_assembly_post:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and loop: "bmssp_post_full
      (find_pivots_label k d S B)
      (find_pivots_pivots k d S B) B d_final B' U_loop"
    and compW: "complete_on d_final
      {v \<in> bound_tree S B'. find_pivots_label k d S B v = dist s v}"
  defines "U \<equiv> U_loop \<union>
      {v \<in> bound_tree S B'. find_pivots_label k d S B v = dist s v}"
  shows "bmssp_post_full d S B d_final B' U"
proof -
  let ?W = "{v \<in> bound_tree S B'. find_pivots_label k d S B v = dist s v}"
  have le: "bound_le B' B"
    using loop unfolding bmssp_post_full_def by blast
  have U_eq: "U = bound_tree S B'"
    using concrete_find_pivots_final_tree_assembly[OF sound pre S_reaches loop]
    unfolding U_def by simp
  have loop_complete: "complete_on d_final U_loop"
    using loop unfolding bmssp_post_full_def by blast
  have "complete_on d_final U"
    unfolding U_def using complete_on_Un[OF loop_complete compW] .
  then show ?thesis
    using le U_eq unfolding bmssp_post_full_def by blast
qed

theorem concrete_capped_find_pivots_final_assembly_post:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and loop: "bmssp_post_full
      (find_pivots_label_capped k cap d S B)
      (find_pivots_pivots_capped k cap d S B) B d_final B' U_loop"
    and compW: "complete_on d_final
      {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v}"
  defines "U \<equiv> U_loop \<union>
      {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v}"
  shows "bmssp_post_full d S B d_final B' U"
proof -
  let ?W = "{v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v}"
  have le: "bound_le B' B"
    using loop unfolding bmssp_post_full_def by blast
  have U_eq: "U = bound_tree S B'"
    using concrete_capped_find_pivots_final_tree_assembly[OF sound pre S_reaches loop]
    unfolding U_def by simp
  have loop_complete: "complete_on d_final U_loop"
    using loop unfolding bmssp_post_full_def by blast
  have "complete_on d_final U"
    unfolding U_def using complete_on_Un[OF loop_complete compW] .
  then show ?thesis
    using le U_eq unfolding bmssp_post_full_def by blast
qed

text \<open>
  The final assembly theorems are the facts used by
  \<open>concrete_capped_bmssp_step\<close>.  The loop solves the pivot tree, while
  FindPivots may have completed additional vertices in the caller's original
  tree.  The assembly theorem proves that the union of those two regions is
  the caller's returned bounded tree.  The postcondition theorems then add
  completeness of the explicitly completed FindPivots region and conclude
  @{const bmssp_post_full} for the whole non-base step.
\<close>

end

end
