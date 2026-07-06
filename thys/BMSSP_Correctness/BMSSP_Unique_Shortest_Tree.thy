theory BMSSP_Unique_Shortest_Tree
  imports BMSSP_Shortest_Path_Lemmas
begin

section \<open>Unique Shortest-Path Tree\<close>

text \<open>
  After tie-breaking, shortest paths form a tree rooted at the source.  This
  locale makes that assumption explicit and derives the tree notions used by
  later BMSSP arguments from the graph model.
\<close>

locale unique_shortest_digraph = finite_weighted_digraph +
  assumes unique_shortest_walk:
    "\<lbrakk>shortest_walk s p v; shortest_walk s q v\<rbrakk> \<Longrightarrow> p = q"
begin

definition shortest_path_to where
  "shortest_path_to v = (THE p. shortest_walk s p v)"

definition tree_path where
  "tree_path u v \<longleftrightarrow> reachable s v \<and> u \<in> set (shortest_path_to v)"

definition tree_of where
  "tree_of u = {v \<in> V. tree_path u v}"

definition tree_set where
  "tree_set S = {v \<in> V. \<exists>u\<in>S. tree_path u v}"

definition tree_antichain where
  "tree_antichain S \<longleftrightarrow> (\<forall>u\<in>S. \<forall>v\<in>S. tree_path u v \<longrightarrow> u = v)"

lemma tree_antichain_subset:
  assumes anti: "tree_antichain T"
    and subset: "S \<subseteq> T"
  shows "tree_antichain S"
  using anti subset unfolding tree_antichain_def by blast

lemma tree_antichain_singleton [simp]:
  "tree_antichain {x}"
  unfolding tree_antichain_def by blast

lemma tree_pathD:
  assumes "tree_path u v"
  shows "reachable s v" "u \<in> set (shortest_path_to v)"
  using assms unfolding tree_path_def by auto

lemma tree_pathI:
  assumes "reachable s v" "u \<in> set (shortest_path_to v)"
  shows "tree_path u v"
  using assms unfolding tree_path_def by auto

lemma shortest_path_to_ex1:
  assumes "reachable s v"
  shows "\<exists>!p. shortest_walk s p v"
proof -
  obtain p where p: "shortest_walk s p v"
    using assms by (rule shortest_walk_exists)
  have "\<And>q. shortest_walk s q v \<Longrightarrow> q = p"
    using p unique_shortest_walk by blast
  then show ?thesis
    using p by blast
qed

lemma shortest_path_to_shortest:
  assumes "reachable s v"
  shows "shortest_walk s (shortest_path_to v) v"
  unfolding shortest_path_to_def
  using shortest_path_to_ex1[OF assms] by (rule theI')

lemma shortest_path_to_successively_tight:
  assumes "reachable s v"
  shows "successively tight_edge_step (shortest_path_to v)"
  using shortest_walk_successively_tight[OF shortest_path_to_shortest[OF assms]] .

lemma shortest_path_prefix_eq:
  assumes reach_v: "reachable s v"
    and i: "i < length (shortest_path_to v)"
  shows "shortest_path_to (shortest_path_to v ! i) =
    take (Suc i) (shortest_path_to v)"
proof -
  let ?p = "shortest_path_to v"
  have sp: "shortest_walk s ?p v"
    using shortest_path_to_shortest[OF reach_v] .
  have pref_short: "shortest_walk s (take (Suc i) ?p) (?p ! i)"
    using shortest_walk_prefix_shortest[OF sp i] .
  have reach_i: "reachable s (?p ! i)"
    using pref_short unfolding shortest_walk_def reachable_def by blast
  have canon_short: "shortest_walk s (shortest_path_to (?p ! i)) (?p ! i)"
    using shortest_path_to_shortest[OF reach_i] .
  show ?thesis
    using unique_shortest_walk[OF canon_short pref_short] by simp
qed

lemma tree_path_between_shortest_path_indices:
  assumes reach_v: "reachable s v"
    and ij: "i \<le> j"
    and j: "j < length (shortest_path_to v)"
  shows "tree_path (shortest_path_to v ! i) (shortest_path_to v ! j)"
proof -
  let ?p = "shortest_path_to v"
  have sp: "shortest_walk s ?p v"
    using shortest_path_to_shortest[OF reach_v] .
  have pref_j: "shortest_walk s (take (Suc j) ?p) (?p ! j)"
    using shortest_walk_prefix_shortest[OF sp j] .
  have reach_j: "reachable s (?p ! j)"
    using pref_j unfolding shortest_walk_def reachable_def by blast
  have i_take: "i < length (take (Suc j) ?p)"
    using ij j by simp
  have take_i: "take (Suc j) ?p ! i = ?p ! i"
    using ij by simp
  have "?p ! i \<in> set (take (Suc j) ?p)"
    using nth_mem[OF i_take] take_i by metis
  then have in_canon: "?p ! i \<in> set (shortest_path_to (?p ! j))"
    using shortest_path_prefix_eq[OF reach_v j] by simp
  show ?thesis
    using reach_j in_canon by (rule tree_pathI)
qed

lemma tree_prefix_of_shortest_path_suffix:
  assumes reach_v: "reachable s v"
    and i: "i < length (shortest_path_to v)"
  shows "set (take k (drop i (shortest_path_to v))) \<subseteq>
    tree_of (shortest_path_to v ! i)"
proof
  let ?p = "shortest_path_to v"
  fix x
  assume x_take: "x \<in> set (take k (drop i ?p))"
  obtain r where r: "r < length (take k (drop i ?p))"
    "take k (drop i ?p) ! r = x"
    using x_take by (auto simp: in_set_conv_nth)
  have r_drop: "r < length (drop i ?p)"
    using r(1) by simp
  have j_len: "i + r < length ?p"
    using r_drop i by simp
  have x_drop: "x = drop i ?p ! r"
    using r by simp
  have x_eq: "x = ?p ! (i + r)"
    using x_drop r_drop by simp
  have tree: "tree_path (?p ! i) x"
    using tree_path_between_shortest_path_indices[OF reach_v _ j_len, of i]
      x_eq by simp
  have xV: "x \<in> V"
  proof -
    have "shortest_walk s ?p v"
      using shortest_path_to_shortest[OF reach_v] .
    then have "walk ?p"
      unfolding shortest_walk_def simple_walk_betw_def walk_betw_def by blast
    moreover have "x \<in> set ?p"
      using x_eq nth_mem[OF j_len] by simp
    ultimately show ?thesis
      using walk_set_subset by blast
  qed
  show "x \<in> tree_of (?p ! i)"
    using xV tree unfolding tree_of_def by blast
qed

lemma tree_path_dist_le:
  assumes "tree_path u v"
  shows "dist s u \<le> dist s v"
proof -
  have reach: "reachable s v" and u: "u \<in> set (shortest_path_to v)"
    using assms by (auto dest: tree_pathD)
  have "shortest_walk s (shortest_path_to v) v"
    using shortest_path_to_shortest[OF reach] .
  then show ?thesis
    using shortest_walk_prefix_dist_le u by blast
qed

lemma tree_path_root_reachable:
  assumes "tree_path u v"
  shows "reachable s u"
proof -
  have reach_v: "reachable s v" and u_path: "u \<in> set (shortest_path_to v)"
    using assms by (auto dest: tree_pathD)
  obtain i where i: "i < length (shortest_path_to v)" "shortest_path_to v ! i = u"
    using u_path by (auto simp: in_set_conv_nth)
  have sp: "shortest_walk s (shortest_path_to v) v"
    using shortest_path_to_shortest[OF reach_v] .
  have "shortest_walk s (take (Suc i) (shortest_path_to v)) u"
    using shortest_walk_prefix_shortest[OF sp i(1)] i(2) by simp
  then show ?thesis
    unfolding shortest_walk_def reachable_def by blast
qed

lemma tree_path_root_in_V:
  assumes "tree_path u v"
  shows "u \<in> V"
proof -
  have "reachable s u"
    using tree_path_root_reachable[OF assms] .
  then obtain p where p: "simple_walk_betw s p u"
    unfolding reachable_def by blast
  then have "walk p" and "u \<in> set p"
    unfolding simple_walk_betw_def walk_betw_def
    by (auto intro: last_in_set)
  then show ?thesis
    using walk_set_subset by blast
qed

lemma tree_path_trans:
  assumes uv: "tree_path u v"
    and xu: "tree_path x u"
  shows "tree_path x v"
proof -
  have reach_v: "reachable s v" and u_path: "u \<in> set (shortest_path_to v)"
    using uv by (auto dest: tree_pathD)
  have x_path_u: "x \<in> set (shortest_path_to u)"
    using xu by (auto dest: tree_pathD)
  obtain i where i: "i < length (shortest_path_to v)" "shortest_path_to v ! i = u"
    using u_path by (auto simp: in_set_conv_nth)
  have "shortest_path_to u = take (Suc i) (shortest_path_to v)"
    using shortest_path_prefix_eq[OF reach_v i(1)] i(2) by simp
  then have "x \<in> set (take (Suc i) (shortest_path_to v))"
    using x_path_u by simp
  then have "x \<in> set (shortest_path_to v)"
    by (meson in_set_takeD)
  then show ?thesis
    by (rule tree_pathI[OF reach_v])
qed

lemma tree_path_comparable:
  assumes ux: "tree_path u x"
    and vx: "tree_path v x"
  shows "tree_path u v \<or> tree_path v u"
proof -
  have reach_x: "reachable s x"
    using ux by (auto dest: tree_pathD)
  have u_path: "u \<in> set (shortest_path_to x)"
    and v_path: "v \<in> set (shortest_path_to x)"
    using ux vx by (auto dest: tree_pathD)
  obtain i where i: "i < length (shortest_path_to x)" "shortest_path_to x ! i = u"
    using u_path by (auto simp: in_set_conv_nth)
  obtain j where j: "j < length (shortest_path_to x)" "shortest_path_to x ! j = v"
    using v_path by (auto simp: in_set_conv_nth)
  show ?thesis
  proof (cases "i \<le> j")
    case True
    have "tree_path u v"
      using tree_path_between_shortest_path_indices[OF reach_x True j(1)] i(2) j(2)
      by simp
    then show ?thesis
      by blast
  next
    case False
    then have "j \<le> i"
      by simp
    have "tree_path v u"
      using tree_path_between_shortest_path_indices[OF reach_x \<open>j \<le> i\<close> i(1)] i(2) j(2)
      by simp
    then show ?thesis
      by blast
  qed
qed

lemma tree_antichainD:
  assumes "tree_antichain S"
    and "u \<in> S" "v \<in> S" "tree_path u v"
  shows "u = v"
  using assms unfolding tree_antichain_def by blast

lemma tree_of_disjoint_if_antichain:
  assumes anti: "tree_antichain S"
    and uS: "u \<in> S"
    and vS: "v \<in> S"
    and neq: "u \<noteq> v"
  shows "tree_of u \<inter> tree_of v = {}"
proof
  show "tree_of u \<inter> tree_of v \<subseteq> {}"
  proof
    fix x
    assume x: "x \<in> tree_of u \<inter> tree_of v"
    then have ux: "tree_path u x" and vx: "tree_path v x"
      unfolding tree_of_def by auto
    have "tree_path u v \<or> tree_path v u"
      using tree_path_comparable[OF ux vx] .
    then have "u = v"
    proof
      assume uv': "tree_path u v"
      then show ?thesis
        using tree_antichainD[OF anti uS vS uv'] by simp
    next
      assume vu': "tree_path v u"
      then show ?thesis
        using tree_antichainD[OF anti vS uS vu'] by simp
    qed
    with neq show "x \<in> {}"
      by blast
  qed
qed simp

lemma through_iff_tree_path:
  assumes "reachable s v"
  shows "through S v \<longleftrightarrow> (\<exists>u\<in>S. tree_path u v)"
proof
  assume "through S v"
  then obtain u p where u: "u \<in> S" "shortest_walk s p v" "u \<in> set p"
    unfolding through_def by blast
  have "p = shortest_path_to v"
    using shortest_path_to_shortest[OF assms] u(2) unique_shortest_walk by blast
  then have "tree_path u v"
    using assms u by (auto intro: tree_pathI)
  then show "\<exists>u\<in>S. tree_path u v"
    using u(1) by blast
next
  assume "\<exists>u\<in>S. tree_path u v"
  then obtain u where u: "u \<in> S" "tree_path u v"
    by blast
  then have "u \<in> set (shortest_path_to v)"
    by (auto dest: tree_pathD)
  moreover have "shortest_walk s (shortest_path_to v) v"
    using shortest_path_to_shortest[OF assms] .
  ultimately show "through S v"
    using u(1) unfolding through_def by blast
qed

lemma bound_tree_eq_tree_set:
  "bound_tree S B = {v \<in> tree_set S. below_bound (dist s v) B}"
proof
  show "bound_tree S B \<subseteq> {v \<in> tree_set S. below_bound (dist s v) B}"
  proof
    fix v
    assume v: "v \<in> bound_tree S B"
    then have reach: "reachable s v" and "through S v" and below: "below_bound (dist s v) B" and "v \<in> V"
      unfolding bound_tree_def by auto
    then obtain u where "u \<in> S" "tree_path u v"
      using through_iff_tree_path[OF reach, of S] by blast
    then have "v \<in> tree_set S"
      using \<open>v \<in> V\<close> unfolding tree_set_def by blast
    then show "v \<in> {v \<in> tree_set S. below_bound (dist s v) B}"
      using below by simp
  qed
next
  show "{v \<in> tree_set S. below_bound (dist s v) B} \<subseteq> bound_tree S B"
  proof
    fix v
    assume v: "v \<in> {v \<in> tree_set S. below_bound (dist s v) B}"
    then obtain u where vV: "v \<in> V" and uS: "u \<in> S" and tp: "tree_path u v"
      and below: "below_bound (dist s v) B"
      unfolding tree_set_def by blast
    then have reach: "reachable s v"
      by (auto dest: tree_pathD)
    have "through S v"
      using through_iff_tree_path[OF reach, of S] uS tp by blast
    then show "v \<in> bound_tree S B"
      using vV reach below unfolding bound_tree_def by blast
  qed
qed

end

end
