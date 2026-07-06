theory BMSSP_Base_Case
  imports BMSSP_Algorithm_Correctness BMSSP_Shortest_Path_Lemmas
begin

section \<open>Concrete Base Case\<close>

text \<open>
  The algorithm's level-0 BMSSP call is a bounded Dijkstra-style search from a
  singleton source.  It explores the bounded tree below the input bound and
  stops once the next extracted distance would exceed the first \<open>k\<close> vertices.
  Operationally, the paper describes this with a priority queue.  For
  correctness, only one property of that queue matters here: vertices are
  extracted in nondecreasing true distance order.

  This theory turns that observation into a compact semantic base case.  Since
  the graph is finite, the bounded tree can be listed in sorted distance order.
  If the list has at most \<open>k\<close> vertices, the base case completes the whole
  bounded tree and returns the original bound.  If the list is longer, the
  \<open>k\<close>-th distance becomes the returned finite bound and the completed set is
  exactly the part of the bounded tree strictly below that bound.  The final
  lemma packages this as a BMSSP postcondition without assuming any recursive
  postcondition for the base case itself.
\<close>

context finite_weighted_digraph
begin

definition min_dist_vertex :: "'v set \<Rightarrow> 'v" where
  "min_dist_vertex A = (SOME x. x \<in> A \<and> dist s x = Min (dist s ` A))"

lemma finite_bound_tree [simp]: "finite (bound_tree S B)"
  unfolding bound_tree_def using finite_V by auto

lemma min_dist_vertex_prop:
  assumes "finite A" "A \<noteq> {}"
  shows "min_dist_vertex A \<in> A \<and> dist s (min_dist_vertex A) = Min (dist s ` A)"
proof -
  obtain a where "a \<in> A"
    using assms by auto
  then have "Min (dist s ` A) \<in> dist s ` A"
    using assms by (intro Min_in) auto
  then have "\<exists>x. x \<in> A \<and> dist s x = Min (dist s ` A)"
    by auto
  then have "(SOME x. x \<in> A \<and> dist s x = Min (dist s ` A)) \<in> A \<and>
      dist s (SOME x. x \<in> A \<and> dist s x = Min (dist s ` A)) = Min (dist s ` A)"
    by (rule someI_ex)
  then show ?thesis
    unfolding min_dist_vertex_def .
qed

lemma min_dist_vertex_in:
  assumes "finite A" "A \<noteq> {}"
  shows "min_dist_vertex A \<in> A"
  using min_dist_vertex_prop[OF assms] by blast

lemma min_dist_vertex_min:
  assumes "finite A" "A \<noteq> {}" "y \<in> A"
  shows "dist s (min_dist_vertex A) \<le> dist s y"
proof -
  have "dist s (min_dist_vertex A) = Min (dist s ` A)"
    using min_dist_vertex_prop[OF assms(1,2)] by blast
  also have "\<dots> \<le> dist s y"
    using assms by auto
  finally show ?thesis .
qed

lemma ordered_extraction_exists:
  assumes "finite A"
  shows "\<exists>xs. set xs = A \<and> distinct xs \<and> sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) xs"
proof -
  obtain xs where xs: "set xs = A" "distinct xs"
    using finite_distinct_list[OF assms] by blast
  let ?ys = "sort_key (dist s) xs"
  have "set ?ys = A"
    using xs(1) by simp
  moreover have "distinct ?ys"
    using xs(2) by simp
  moreover have "sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) ?ys"
  proof -
    have "sorted (map (dist s) ?ys)"
      by (rule sorted_sort_key)
    then show ?thesis
      by (simp add: sorted_map)
  qed
  ultimately show ?thesis
    by blast
qed

definition closest_vertices :: "'v set \<Rightarrow> 'v list" where
  "closest_vertices A =
    (SOME xs. set xs = A \<and> distinct xs \<and> sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) xs)"

lemma closest_vertices_properties:
  assumes "finite A"
  shows "set (closest_vertices A) = A"
    and "distinct (closest_vertices A)"
    and "sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) (closest_vertices A)"
proof -
  have "\<exists>xs. set xs = A \<and> distinct xs \<and>
      sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) xs"
    using ordered_extraction_exists[OF assms] .
  then have cv_props: "set (closest_vertices A) = A \<and>
     distinct (closest_vertices A) \<and>
     sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) (closest_vertices A)"
    unfolding closest_vertices_def by (rule someI_ex)
  then show "set (closest_vertices A) = A"
    by blast
  from cv_props show "distinct (closest_vertices A)"
    by blast
  from cv_props show "sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) (closest_vertices A)"
    by blast
qed

definition base_case_order :: "'v \<Rightarrow> bound \<Rightarrow> 'v list" where
  "base_case_order x B = closest_vertices (bound_tree {x} B)"

definition base_case_vertices :: "nat \<Rightarrow> 'v \<Rightarrow> bound \<Rightarrow> 'v set" where
  "base_case_vertices k x B =
    (let xs = base_case_order x B in
      if length xs \<le> k then set xs
      else {v \<in> set (take (Suc k) xs). dist s v < dist s (xs ! k)})"

definition base_case_bound :: "nat \<Rightarrow> 'v \<Rightarrow> bound \<Rightarrow> bound" where
  "base_case_bound k x B =
    (let xs = base_case_order x B in
      if length xs \<le> k then B else Fin (dist s (xs ! k)))"

definition base_case_result :: "nat \<Rightarrow> 'v \<Rightarrow> bound \<Rightarrow> bound \<times> 'v set" where
  "base_case_result k x B =
    (base_case_bound k x B, base_case_vertices k x B)"

text \<open>
  The helper @{const closest_vertices} is a choice of a distinct list sorted by
  true distance.  It is intentionally non-executable: the base-case proof is
  semantic, and later executable theories provide their own finite procedure.
  The public base-case result is described by @{const base_case_result}, whose
  components are @{const base_case_bound} and @{const base_case_vertices}.  The
  strict inequality in @{const base_case_vertices} mirrors the main BMSSP
  convention for finite bounds.
\<close>

lemma base_case_order_set:
  "set (base_case_order x B) = bound_tree {x} B"
  unfolding base_case_order_def
  using closest_vertices_properties(1)[OF finite_bound_tree] .

lemma base_case_order_sorted:
  "sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) (base_case_order x B)"
  unfolding base_case_order_def
  using closest_vertices_properties(3)[OF finite_bound_tree] .

lemma base_case_order_distinct:
  "distinct (base_case_order x B)"
  unfolding base_case_order_def
  using closest_vertices_properties(2)[OF finite_bound_tree] .

lemma in_set_take_dist_lt_nth:
  assumes sorted: "sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) xs"
    and y: "y \<in> set xs"
    and lt: "dist s y < dist s (xs ! k)"
    and k: "k < length xs"
  shows "y \<in> set (take k xs)"
proof -
  obtain i where i: "i < length xs" "xs ! i = y"
    using y by (auto simp: in_set_conv_nth)
  have "i < k"
  proof (rule ccontr)
    assume "\<not> i < k"
    then have k_le_i: "k \<le> i"
      by simp
    show False
    proof (cases "k = i")
      case True
      then show ?thesis
        using lt i(2) by simp
    next
      case False
      with k_le_i have "k < i"
        by simp
      then have "dist s (xs ! k) \<le> dist s (xs ! i)"
        using sorted_wrt_nth_less[OF sorted, of k i] i(1) by simp
      then show ?thesis
        using lt i(2) by simp
    qed
  qed
  then have "i < length (take k xs)" "take k xs ! i = y"
    using i by auto
  then show ?thesis
    using nth_mem by metis
qed

lemma base_case_success:
  assumes "length (base_case_order x B) \<le> k"
  shows "base_case_vertices k x B = bound_tree {x} B"
  using assms base_case_order_set[of x B]
  unfolding base_case_vertices_def by (simp add: Let_def)

lemma below_bound_less_trans:
  assumes "a < b" "below_bound b B"
  shows "below_bound a B"
  using assms by (cases B) auto

lemma Fin_below_bound_le:
  assumes "below_bound a B"
  shows "bound_le (Fin a) B"
  using assms by (cases B) auto

lemma base_case_partial:
  assumes len: "k < length (base_case_order x B)"
  shows "base_case_vertices k x B = bound_tree {x} (Fin (dist s ((base_case_order x B) ! k)))"
proof -
  let ?xs = "base_case_order x B"
  let ?b = "dist s (?xs ! k)"
  have set_xs: "set ?xs = bound_tree {x} B"
    using base_case_order_set[of x B] .
  have sorted: "sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) ?xs"
    using base_case_order_sorted[of x B] .
  have kth_in: "?xs ! k \<in> bound_tree {x} B"
    using len set_xs nth_mem by metis
  show ?thesis
  proof
    show "base_case_vertices k x B \<subseteq> bound_tree {x} (Fin ?b)"
    proof
      fix v
      assume "v \<in> base_case_vertices k x B"
      moreover have "base_case_vertices k x B =
          {v \<in> set (take (Suc k) ?xs). dist s v < ?b}"
        using len unfolding base_case_vertices_def by (simp add: Let_def)
      ultimately have v: "v \<in> set (take (Suc k) ?xs)" "dist s v < ?b"
        by auto
      have "v \<in> set ?xs"
        using v(1) by (meson in_set_takeD)
      then have "v \<in> bound_tree {x} B"
        using set_xs by simp
      then show "v \<in> bound_tree {x} (Fin ?b)"
        using v(2) unfolding bound_tree_def by auto
    qed
  next
    show "bound_tree {x} (Fin ?b) \<subseteq> base_case_vertices k x B"
    proof
      fix v
      assume v: "v \<in> bound_tree {x} (Fin ?b)"
      then have lt: "dist s v < ?b"
        unfolding bound_tree_def by auto
      have kth_below: "below_bound (dist s (?xs ! k)) B"
        using kth_in unfolding bound_tree_def by auto
      have "below_bound (dist s v) B"
        using below_bound_less_trans[OF lt kth_below] .
      then have "v \<in> bound_tree {x} B"
        using v unfolding bound_tree_def by auto
      then have "v \<in> set ?xs"
        using set_xs by simp
      then have "v \<in> set (take k ?xs)"
        using in_set_take_dist_lt_nth[OF sorted _ lt len] by blast
      then have "v \<in> set (take (Suc k) ?xs)"
        using set_take_subset_set_take[of k "Suc k" ?xs] by auto
      then show "v \<in> base_case_vertices k x B"
        using len lt unfolding base_case_vertices_def by (simp add: Let_def)
    qed
  qed
qed

lemma base_case_result_correct:
  assumes "S = {x}"
  shows "case base_case_result k x B of (B', U) \<Rightarrow>
    U = bound_tree S B' \<and> complete_on (\<lambda>v. if v \<in> U then dist s v else d v) U"
proof (cases "length (base_case_order x B) \<le> k")
  case True
  then have U: "base_case_vertices k x B = bound_tree {x} B"
    using base_case_success by blast
  have B': "base_case_bound k x B = B"
    using True unfolding base_case_bound_def by (simp add: Let_def)
  have "complete_on (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
      (base_case_vertices k x B)"
    unfolding complete_on_def by simp
  then show ?thesis
    using assms U B' unfolding base_case_result_def by simp
next
  case False
  then have len: "k < length (base_case_order x B)"
    by simp
  let ?B = "Fin (dist s ((base_case_order x B) ! k))"
  have U: "base_case_vertices k x B = bound_tree {x} ?B"
    using base_case_partial[OF len] .
  have B': "base_case_bound k x B = ?B"
    using False unfolding base_case_bound_def by (simp add: Let_def)
  have "complete_on (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
      (base_case_vertices k x B)"
    unfolding complete_on_def by simp
  then show ?thesis
    using assms U B' unfolding base_case_result_def by simp
qed

lemma base_case_bound_le:
  "bound_le (base_case_bound k x B) B"
proof (cases "length (base_case_order x B) \<le> k")
  case True
  then show ?thesis
    unfolding base_case_bound_def by (cases B) (simp_all add: Let_def)
next
  case False
  then have len: "k < length (base_case_order x B)"
    by simp
  let ?xs = "base_case_order x B"
  have "?xs ! k \<in> bound_tree {x} B"
    using len base_case_order_set[of x B] nth_mem by metis
  then have "below_bound (dist s (?xs ! k)) B"
    unfolding bound_tree_def by auto
  then show ?thesis
    using False Fin_below_bound_le unfolding base_case_bound_def by (simp add: Let_def)
qed

lemma base_case_result_bound_le:
  "case base_case_result k x B of (B', U) \<Rightarrow> bound_le B' B"
  unfolding base_case_result_def using base_case_bound_le by simp

lemma base_case_result_bmssp_post:
  assumes "S = {x}"
  shows "case base_case_result k x B of (B', U) \<Rightarrow>
    bmssp_post d S B (\<lambda>v. if v \<in> U then dist s v else d v) B' U"
proof -
  have corr: "case base_case_result k x B of (B', U) \<Rightarrow>
      U = bound_tree S B' \<and> complete_on (\<lambda>v. if v \<in> U then dist s v else d v) U"
    using base_case_result_correct[OF assms, where k=k and B=B and d=d] .
  have le: "case base_case_result k x B of (B', U) \<Rightarrow> bound_le B' B"
    using base_case_result_bound_le[where k=k and x=x and B=B] .
  show ?thesis
    using corr le unfolding bmssp_post_def by (cases "base_case_result k x B") auto
qed

text \<open>
  The proof splits on whether the sorted bounded tree has already fit inside
  the base-case budget.  In the success case, @{thm base_case_success} says the
  returned set is the entire input tree.  In the partial case,
  @{thm base_case_partial} identifies the returned set with the same tree under
  the newly returned finite bound.  Lemma @{thm base_case_result_bmssp_post}
  is the result consumed by the recursive relation: updating labels to
  @{const dist} on the returned set establishes the BMSSP postcondition.
\<close>

lemma base_case_label_sound:
  assumes sound: "sound_label d"
  shows "sound_label (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)"
  using sound unfolding sound_label_def by auto

lemma finite_base_case_vertices [simp]:
  "finite (base_case_vertices k x B)"
proof (cases "length (base_case_order x B) \<le> k")
  case True
  then show ?thesis
    using base_case_success[of x B k] by simp
next
  case False
  then show ?thesis
    unfolding base_case_vertices_def by (simp add: Let_def)
qed

lemma card_base_case_vertices_le:
  "card (base_case_vertices k x B) \<le> k"
proof (cases "length (base_case_order x B) \<le> k")
  case True
  have "card (base_case_vertices k x B) = length (base_case_order x B)"
    using True base_case_order_distinct[of x B]
    unfolding base_case_vertices_def by (simp add: Let_def distinct_card)
  then show ?thesis
    using True by simp
next
  case False
  then have len: "k < length (base_case_order x B)"
    by simp
  let ?xs = "base_case_order x B"
  let ?U = "base_case_vertices k x B"
  have U_subset: "?U \<subseteq> set (take k ?xs)"
  proof
    fix v
    assume "v \<in> ?U"
    moreover have "?U = {v \<in> set (take (Suc k) ?xs). dist s v < dist s (?xs ! k)}"
      using len unfolding base_case_vertices_def by (simp add: Let_def)
    ultimately have v: "v \<in> set (take (Suc k) ?xs)" "dist s v < dist s (?xs ! k)"
      by auto
    then have v_set: "v \<in> set ?xs"
      by (meson in_set_takeD)
    then show "v \<in> set (take k ?xs)"
      using in_set_take_dist_lt_nth[OF base_case_order_sorted[of x B] v_set v(2) len] by blast
  qed
  have card_U_le: "card ?U \<le> card (set (take k ?xs))"
    using U_subset by (simp add: card_mono)
  have card_take_le: "card (set (take k ?xs)) \<le> length (take k ?xs)"
    by (rule card_length)
  have "length (take k ?xs) = k"
    using len by simp
  then show ?thesis
    using card_U_le card_take_le by linarith
qed

text \<open>
  The remaining facts are bookkeeping for the costed and recursive layers.  The
  base-case label update preserves @{const sound_label}, the returned set is
  finite, and @{thm card_base_case_vertices_le} records the intended cap.  The
  strict cutoff in the partial case is what makes this cardinality bound hold:
  ties at the \<open>k\<close>-th distance are not included.
\<close>

end

end
