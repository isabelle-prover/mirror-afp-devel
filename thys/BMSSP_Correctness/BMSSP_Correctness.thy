theory BMSSP_Correctness
  imports Complex_Main
begin

section \<open>Correctness Interface for BMSSP\<close>

text \<open>
  This is the entry point of the correctness layer.  It deliberately avoids
  committing to the paper's data structure, cost accounting, perturbation
  reduction, or executable representation.  The purpose here is to state the
  mathematical contract that every later algorithmic refinement has to meet.

  The ambient object is a finite directed graph with non-negative real edge
  weights and a distinguished source vertex.  Distances are not imported from a
  library shortest-path algorithm.  Instead, they are defined directly as
  minima of finite sets of simple-walk weights.  This gives the later proofs a
  small, transparent semantic target: a label is correct exactly when it agrees
  with the minimum simple-walk distance from the source.

  BMSSP means bounded multi-source shortest path.  A recursive BMSSP call is
  not asked to solve all of single-source shortest paths.  It receives a set of
  sources, a bound, and a current label function.  It must complete the
  vertices whose shortest paths pass through the source set and whose
  distances lie below the bound returned by the call.  This bounded contract is
  the reason the paper can recurse on distance ranges rather than repeatedly
  extracting one global minimum vertex.

  The definitions below therefore introduce three pieces of vocabulary that
  recur throughout the development.  A bound can be finite or infinite; a
  bound tree is the set of vertices relevant to a source set below such a
  bound; and the BMSSP postcondition says that the output labels are complete
  on exactly that tree.  Later theories refine how the tree is assembled:
  FindPivots identifies useful sources, the partition loop splits the distance
  range, and the bucketed data structure realizes the required Insert,
  BatchPrepend, and Pull operations.  The final theorems of this file show
  that a successful root BMSSP call is already enough to establish ordinary
  single-source shortest-path correctness.
\<close>

datatype bound = Fin real | Infinity

fun below_bound :: "real \<Rightarrow> bound \<Rightarrow> bool" where
  "below_bound x Infinity \<longleftrightarrow> True"
| "below_bound x (Fin b) \<longleftrightarrow> x < b"

fun bound_le :: "bound \<Rightarrow> bound \<Rightarrow> bool" where
  "bound_le _ Infinity \<longleftrightarrow> True"
| "bound_le Infinity (Fin _) \<longleftrightarrow> False"
| "bound_le (Fin a) (Fin b) \<longleftrightarrow> a \<le> b"

text \<open>
  The datatype @{typ bound} is intentionally small.  The predicate
  @{const below_bound} is strict for finite bounds, matching the paper's
  range convention, while @{const bound_le} is the preorder used when a
  recursive call returns a possibly smaller upper bound.  Keeping this type
  separate from raw reals makes the top-level call with @{term Infinity}
  explicit and avoids ad hoc sentinel values in the correctness proof.
\<close>

locale finite_weighted_digraph =
  fixes V :: "'v set"
    and E :: "('v \<times> 'v) set"
    and w :: "'v \<Rightarrow> 'v \<Rightarrow> real"
    and s :: "'v"
  assumes finite_V: "finite V"
    and source_in_V: "s \<in> V"
    and edge_in_V: "(u, v) \<in> E \<Longrightarrow> u \<in> V \<and> v \<in> V"
    and nonneg_weight: "(u, v) \<in> E \<Longrightarrow> 0 \<le> w u v"
begin

fun walk :: "'v list \<Rightarrow> bool" where
  "walk [] \<longleftrightarrow> False"
| "walk [x] \<longleftrightarrow> x \<in> V"
| "walk (x # y # xs) \<longleftrightarrow> x \<in> V \<and> (x, y) \<in> E \<and> walk (y # xs)"

fun walk_weight :: "'v list \<Rightarrow> real" where
  "walk_weight [] = 0"
| "walk_weight [x] = 0"
| "walk_weight (x # y # xs) = w x y + walk_weight (y # xs)"

definition walk_betw :: "'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool" where
  "walk_betw a p b \<longleftrightarrow> p \<noteq> [] \<and> hd p = a \<and> last p = b \<and> walk p"

definition simple_walk_betw :: "'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool" where
  "simple_walk_betw a p b \<longleftrightarrow> walk_betw a p b \<and> distinct p"

definition reachable :: "'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "reachable a b \<longleftrightarrow> (\<exists>p. simple_walk_betw a p b)"

definition simple_walk_weights :: "'v \<Rightarrow> 'v \<Rightarrow> real set" where
  "simple_walk_weights a b = walk_weight ` {p. simple_walk_betw a p b}"

definition dist :: "'v \<Rightarrow> 'v \<Rightarrow> real" where
  "dist a b = Min (simple_walk_weights a b)"

definition shortest_walk :: "'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool" where
  "shortest_walk a p b \<longleftrightarrow> simple_walk_betw a p b \<and> walk_weight p = dist a b"

definition through :: "'v set \<Rightarrow> 'v \<Rightarrow> bool" where
  "through S v \<longleftrightarrow> (\<exists>u\<in>S. \<exists>p. shortest_walk s p v \<and> u \<in> set p)"

definition bound_tree :: "'v set \<Rightarrow> bound \<Rightarrow> 'v set" where
  "bound_tree S B =
     {v \<in> V. reachable s v \<and> through S v \<and> below_bound (dist s v) B}"

definition complete_on :: "('v \<Rightarrow> real) \<Rightarrow> 'v set \<Rightarrow> bool" where
  "complete_on d U \<longleftrightarrow> (\<forall>v\<in>U. reachable s v \<longrightarrow> d v = dist s v)"

definition sssp_correct :: "('v \<Rightarrow> real) \<Rightarrow> bool" where
  "sssp_correct d \<longleftrightarrow> (\<forall>v\<in>V. reachable s v \<longrightarrow> d v = dist s v)"

definition bmssp_pre :: "('v \<Rightarrow> real) \<Rightarrow> 'v set \<Rightarrow> bound \<Rightarrow> bool" where
  "bmssp_pre d S B \<longleftrightarrow>
     S \<subseteq> V \<and>
     (\<forall>v\<in>V. reachable s v \<longrightarrow> below_bound (dist s v) B \<longrightarrow>
       d v \<noteq> dist s v \<longrightarrow> through S v)"

definition bmssp_post ::
  "('v \<Rightarrow> real) \<Rightarrow> 'v set \<Rightarrow> bound \<Rightarrow> ('v \<Rightarrow> real) \<Rightarrow> bound \<Rightarrow> 'v set \<Rightarrow> bool" where
  "bmssp_post d S B d' B' U \<longleftrightarrow>
     bound_le B' B \<and> U = bound_tree S B' \<and> complete_on d' U"

text \<open>
  The graph locale makes the semantic model finite at the point where finiteness
  is needed.  A walk is a list of vertices following edges; a simple walk is a
  walk with no repeated vertices; and @{const dist} is the minimum weight over
  simple walks.  Because all edge weights are non-negative, restricting to
  simple walks preserves shortest distances while making the set minimized by
  @{const dist} finite.

  The central BMSSP contract is expressed by @{const bmssp_pre} and
  @{const bmssp_post}.  The precondition says that every not-yet-complete
  reachable vertex below the input bound must be reachable through the current
  source set, as formalized by @{const through}.  The postcondition returns a
  new bound, an output set, and an updated label function; it demands that the
  output set is exactly @{const bound_tree} for the returned bound and that
  labels are complete there via @{const complete_on}.  This is intentionally
  weaker than global SSSP correctness, because the recursive algorithm only
  solves the range assigned to the current call.
\<close>

lemma walk_set_subset:
  assumes "walk p"
  shows "set p \<subseteq> V"
  using assms edge_in_V
  by (induction p rule: walk.induct) auto

lemma simple_walk_length_le_card:
  assumes "simple_walk_betw a p b"
  shows "length p \<le> card V"
proof -
  have "walk p" and "distinct p"
    using assms unfolding simple_walk_betw_def walk_betw_def by auto
  then have "set p \<subseteq> V"
    using walk_set_subset by blast
  with \<open>distinct p\<close> have "length p = card (set p)"
    by (simp add: distinct_card)
  also have "\<dots> \<le> card V"
    using \<open>set p \<subseteq> V\<close> finite_V by (simp add: card_mono)
  finally show ?thesis .
qed

lemma finite_simple_walks:
  shows "finite {p. simple_walk_betw a p b}"
proof (rule finite_subset)
  show "{p. simple_walk_betw a p b}
      \<subseteq> {p. set p \<subseteq> V \<and> length p \<le> card V}"
    using simple_walk_length_le_card walk_set_subset
    unfolding simple_walk_betw_def walk_betw_def by auto
  show "finite {p. set p \<subseteq> V \<and> length p \<le> card V}"
    using finite_lists_length_le[OF finite_V] .
qed

lemma finite_simple_walk_weights:
  shows "finite (simple_walk_weights a b)"
  unfolding simple_walk_weights_def
  using finite_simple_walks by simp

lemma simple_walk_weights_nonempty:
  assumes "reachable a b"
  shows "simple_walk_weights a b \<noteq> {}"
  using assms unfolding reachable_def simple_walk_weights_def by blast

lemma dist_is_simple_walk_weight:
  assumes "reachable a b"
  shows "dist a b \<in> simple_walk_weights a b"
  unfolding dist_def
  using finite_simple_walk_weights simple_walk_weights_nonempty[OF assms] by (rule Min_in)

lemma shortest_walk_exists:
  assumes "reachable a b"
  obtains p where "shortest_walk a p b"
proof -
  have "dist a b \<in> simple_walk_weights a b"
    using assms by (rule dist_is_simple_walk_weight)
  then have "\<exists>p. simple_walk_betw a p b \<and> walk_weight p = dist a b"
    unfolding simple_walk_weights_def by (auto simp: image_iff)
  then obtain p where "simple_walk_betw a p b" "walk_weight p = dist a b"
    by blast
  then have "shortest_walk a p b"
    unfolding shortest_walk_def by blast
  then show thesis
    using that by blast
qed

lemma shortest_walk_hd:
  assumes "shortest_walk a p b"
  shows "p \<noteq> []" "hd p = a" "last p = b"
  using assms unfolding shortest_walk_def simple_walk_betw_def walk_betw_def by auto

lemma reachable_refl:
  assumes "v \<in> V"
  shows "reachable v v"
  using assms unfolding reachable_def simple_walk_betw_def walk_betw_def by auto

lemma reachable_source_through:
  assumes "reachable s v"
  shows "through {s} v"
proof -
  obtain p where p: "shortest_walk s p v"
    using assms by (rule shortest_walk_exists)
  then have "p \<noteq> []" "hd p = s"
    using shortest_walk_hd by blast+
  then have "s \<in> set p"
    by (metis hd_in_set)
  with p show ?thesis
    unfolding through_def by blast
qed

lemma top_bmssp_pre:
  assumes "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
  shows "bmssp_pre d {s} Infinity"
  using assms reachable_source_through source_in_V
  unfolding bmssp_pre_def by auto

lemma bound_tree_source_infinity:
  assumes "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
  shows "bound_tree {s} Infinity = V"
  using assms reachable_source_through
  unfolding bound_tree_def by auto

lemma bound_tree_source_infinity_reachable:
  shows "bound_tree {s} Infinity = {v \<in> V. reachable s v}"
  using reachable_source_through
  unfolding bound_tree_def by auto

lemma bmssp_post_complete_bound_tree:
  assumes "bmssp_post d S B d' B' U"
    and "v \<in> bound_tree S B'"
  shows "d' v = dist s v"
proof -
  have "U = bound_tree S B'" and "complete_on d' U"
    using assms(1) unfolding bmssp_post_def by auto
  then have "v \<in> U"
    using assms(2) by simp
  moreover have "reachable s v"
    using assms(2) unfolding bound_tree_def by auto
  then show ?thesis
    using \<open>complete_on d' U\<close> calculation unfolding complete_on_def by auto
qed

lemma bmssp_success_completes_requested_tree:
  assumes "bmssp_post d S B d' B U"
    and "v \<in> bound_tree S B"
  shows "d' v = dist s v"
  using bmssp_post_complete_bound_tree[OF assms] .

lemma sssp_correctI:
  assumes "\<And>v. \<lbrakk>v \<in> V; reachable s v\<rbrakk> \<Longrightarrow> d v = dist s v"
  shows "sssp_correct d"
  using assms unfolding sssp_correct_def by blast

text \<open>
  The remaining lemmas discharge the semantic obligations introduced above.
  Finiteness of simple walks justifies the use of @{const Min}; reachability
  of the source shows that the root source set covers every reachable vertex;
  and @{thm bmssp_post_complete_bound_tree} extracts a pointwise distance
  equality from the BMSSP postcondition.  The final two theorems are the
  bridge from a root BMSSP result to the ordinary SSSP predicate
  @{const sssp_correct}.  Later files prove BMSSP postconditions for concrete
  recursive executions, and then reuse these root theorems unchanged.
\<close>

theorem successful_root_bmssp_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and post: "bmssp_post d {s} Infinity d' Infinity U"
  shows "sssp_correct d'"
proof -
  have "U = V"
    using post bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  moreover have "complete_on d' U"
    using post unfolding bmssp_post_def by auto
  ultimately show ?thesis
    unfolding complete_on_def sssp_correct_def by auto
qed

theorem successful_root_bmssp_sssp_correct:
  assumes post: "bmssp_post d {s} Infinity d' Infinity U"
  shows "sssp_correct d'"
proof (rule sssp_correctI)
  fix v
  assume vV: "v \<in> V" and reach_v: "reachable s v"
  have "v \<in> bound_tree {s} Infinity"
    using vV reach_v reachable_source_through unfolding bound_tree_def by auto
  then show "d' v = dist s v"
    by (rule bmssp_post_complete_bound_tree[OF post])
qed

end

end
