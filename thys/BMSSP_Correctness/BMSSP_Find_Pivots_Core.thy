theory BMSSP_Find_Pivots_Core
  imports BMSSP_Unique_Shortest_Tree
begin

section \<open>FindPivots Core Relaxation Lemmas\<close>

text \<open>
  The concrete FindPivots procedure performs bounded Bellman-Ford-style
  relaxations.  This theory packages the generic relaxation facts in the form
  needed for that proof: vertices reached by a bounded tight path from a
  complete source are complete after the corresponding path relaxations, and
  remain complete through additional valid relaxations.
\<close>

context unique_shortest_digraph
begin

lemma finite_E [simp]: "finite E"
proof -
  have "E \<subseteq> V \<times> V"
    using edge_in_V by auto
  moreover have "finite (V \<times> V)"
    using finite_V by simp
  ultimately show ?thesis
    by (rule finite_subset)
qed

definition outgoing_edges where
  "outgoing_edges F = {(u, v) \<in> E. u \<in> F}"

lemma finite_outgoing_edges [simp]:
  "finite (outgoing_edges F)"
proof -
  have "outgoing_edges F \<subseteq> E"
    unfolding outgoing_edges_def by blast
  then show ?thesis
    by (rule finite_subset) simp
qed

definition edge_list_of where
  "edge_list_of A = (SOME xs. set xs = A \<and> distinct xs)"

lemma edge_list_of_properties:
  assumes "finite A"
  shows "set (edge_list_of A) = A"
    and "distinct (edge_list_of A)"
proof -
  have "\<exists>xs. set xs = A \<and> distinct xs"
    using finite_distinct_list[OF assms] .
  then have props: "set (edge_list_of A) = A \<and> distinct (edge_list_of A)"
    unfolding edge_list_of_def by (rule someI_ex)
  then show "set (edge_list_of A) = A"
    by blast
  from props show "distinct (edge_list_of A)"
    by blast
qed

definition relax_frontier where
  "relax_frontier d F = relax_edges d (edge_list_of (outgoing_edges F))"

lemma relax_frontier_le:
  "relax_frontier d F x \<le> d x"
  unfolding relax_frontier_def by (rule relax_edges_le)

lemma relax_frontier_sound:
  assumes sound: "sound_label d"
    and frontier_reaches: "\<And>u. u \<in> F \<Longrightarrow> reachable s u"
  shows "sound_label (relax_frontier d F)"
proof -
  let ?es = "edge_list_of (outgoing_edges F)"
  have set_es: "set ?es = outgoing_edges F"
    using edge_list_of_properties(1)[OF finite_outgoing_edges] .
  have edge: "\<And>u v. (u, v) \<in> set ?es \<Longrightarrow> (u, v) \<in> E"
    using set_es unfolding outgoing_edges_def by blast
  have reach: "\<And>u v. (u, v) \<in> set ?es \<Longrightarrow> reachable s u"
    using set_es frontier_reaches unfolding outgoing_edges_def by blast
  show ?thesis
    unfolding relax_frontier_def using relax_edges_sound[OF sound edge reach] .
qed

fun relax_rounds where
  "relax_rounds d [] = d"
| "relax_rounds d (r # rs) = relax_rounds (relax_edges d r) rs"

definition within_k_edges where
  "within_k_edges p k \<longleftrightarrow> p \<noteq> [] \<and> length (path_edges p) \<le> k"

lemma relax_rounds_concat:
  "relax_rounds d rounds = relax_edges d (concat rounds)"
  by (induction rounds arbitrary: d) (simp_all add: relax_edges_append)

lemma relax_rounds_sound:
  assumes sound: "sound_label d"
    and edges: "\<And>u v. (u, v) \<in> set (concat rounds) \<Longrightarrow> (u, v) \<in> E"
    and reaches: "\<And>u v. (u, v) \<in> set (concat rounds) \<Longrightarrow> reachable s u"
  shows "sound_label (relax_rounds d rounds)"
proof -
  have "sound_label (relax_edges d (concat rounds))"
    by (rule relax_edges_sound[OF sound edges reaches])
  then show ?thesis
    by (simp add: relax_rounds_concat)
qed

lemma relax_rounds_preserves_complete_sound:
  assumes sound: "sound_label d"
    and complete_x: "d x = dist s x"
    and edges: "\<And>u v. (u, v) \<in> set (concat rounds) \<Longrightarrow> (u, v) \<in> E"
    and reaches: "\<And>u v. (u, v) \<in> set (concat rounds) \<Longrightarrow> reachable s u"
  shows "relax_rounds d rounds x = dist s x"
proof -
  have "relax_edges d (concat rounds) x = dist s x"
    by (rule relax_edges_preserves_complete_sound[OF sound complete_x edges reaches])
  then show ?thesis
    by (simp add: relax_rounds_concat)
qed

lemma path_edges_length:
  "length (path_edges p) = length p - 1"
  by (induction p rule: path_edges.induct) auto

lemma within_k_edgesD:
  assumes "within_k_edges p k"
  shows "p \<noteq> []" "length (path_edges p) \<le> k"
  using assms unfolding within_k_edges_def by auto

lemma find_pivots_tight_path_prefix_completion:
  assumes bounded: "within_k_edges p k"
    and sound: "sound_label d"
    and complete_source: "d (hd p) = dist s (hd p)"
    and tight: "successively tight_edge_step p"
    and es: "es = path_edges p @ extra"
    and extra_edges: "\<And>u v. (u, v) \<in> set extra \<Longrightarrow> (u, v) \<in> E"
    and extra_reaches: "\<And>u v. (u, v) \<in> set extra \<Longrightarrow> reachable s u"
  shows "sound_label (relax_edges d es)"
    and "relax_edges d es (last p) = dist s (last p)"
proof -
  have nonempty: "p \<noteq> []"
    using within_k_edgesD(1)[OF bounded] .
  show "sound_label (relax_edges d es)"
    using relax_edges_with_tight_path_prefix_complete(1)
      [OF nonempty sound complete_source tight es extra_edges extra_reaches] .
  show "relax_edges d es (last p) = dist s (last p)"
    using relax_edges_with_tight_path_prefix_complete(2)
      [OF nonempty sound complete_source tight es extra_edges extra_reaches] .
qed

lemma find_pivots_tight_path_block_completion:
  assumes bounded: "within_k_edges p k"
    and sound: "sound_label d"
    and complete_source: "d (hd p) = dist s (hd p)"
    and tight: "successively tight_edge_step p"
    and es: "es = pre @ path_edges p @ extra"
    and pre_edges: "\<And>u v. (u, v) \<in> set pre \<Longrightarrow> (u, v) \<in> E"
    and pre_reaches: "\<And>u v. (u, v) \<in> set pre \<Longrightarrow> reachable s u"
    and extra_edges: "\<And>u v. (u, v) \<in> set extra \<Longrightarrow> (u, v) \<in> E"
    and extra_reaches: "\<And>u v. (u, v) \<in> set extra \<Longrightarrow> reachable s u"
  shows "sound_label (relax_edges d es)"
    and "relax_edges d es (last p) = dist s (last p)"
proof -
  let ?d0 = "relax_edges d pre"
  have nonempty: "p \<noteq> []"
    using within_k_edgesD(1)[OF bounded] .
  have sound0: "sound_label ?d0"
    using relax_edges_sound[OF sound pre_edges pre_reaches] .
  have complete0: "?d0 (hd p) = dist s (hd p)"
    using relax_edges_preserves_complete_sound[OF sound complete_source pre_edges pre_reaches] .
  have tail_sound: "sound_label (relax_edges ?d0 (path_edges p @ extra))"
    using relax_edges_with_tight_path_prefix_complete(1)
      [OF nonempty sound0 complete0 tight refl extra_edges extra_reaches] .
  have tail_complete: "relax_edges ?d0 (path_edges p @ extra) (last p) = dist s (last p)"
    using relax_edges_with_tight_path_prefix_complete(2)
      [OF nonempty sound0 complete0 tight refl extra_edges extra_reaches] .
  have unfold_es: "relax_edges d es = relax_edges ?d0 (path_edges p @ extra)"
    using es relax_edges_append[of d pre "path_edges p @ extra"] by simp
  show "sound_label (relax_edges d es)"
    using tail_sound unfold_es by simp
  show "relax_edges d es (last p) = dist s (last p)"
    using tail_complete unfold_es by simp
qed

lemma find_pivots_rounds_block_completion:
  assumes bounded: "within_k_edges p k"
    and sound: "sound_label d"
    and complete_source: "d (hd p) = dist s (hd p)"
    and tight: "successively tight_edge_step p"
    and rounds: "concat rounds = pre @ path_edges p @ extra"
    and pre_edges: "\<And>u v. (u, v) \<in> set pre \<Longrightarrow> (u, v) \<in> E"
    and pre_reaches: "\<And>u v. (u, v) \<in> set pre \<Longrightarrow> reachable s u"
    and extra_edges: "\<And>u v. (u, v) \<in> set extra \<Longrightarrow> (u, v) \<in> E"
    and extra_reaches: "\<And>u v. (u, v) \<in> set extra \<Longrightarrow> reachable s u"
  shows "sound_label (relax_rounds d rounds)"
    and "relax_rounds d rounds (last p) = dist s (last p)"
proof -
  have edge_sound: "sound_label (relax_edges d (concat rounds))"
    using find_pivots_tight_path_block_completion(1)
      [OF bounded sound complete_source tight rounds pre_edges pre_reaches extra_edges extra_reaches] .
  have endpoint: "relax_edges d (concat rounds) (last p) = dist s (last p)"
    using find_pivots_tight_path_block_completion(2)
      [OF bounded sound complete_source tight rounds pre_edges pre_reaches extra_edges extra_reaches] .
  show "sound_label (relax_rounds d rounds)"
    using edge_sound by (simp add: relax_rounds_concat)
  show "relax_rounds d rounds (last p) = dist s (last p)"
    using endpoint by (simp add: relax_rounds_concat)
qed

lemma relax_frontier_tight_successor_complete:
  assumes sound: "sound_label d"
    and uF: "u \<in> F"
    and frontier_reaches: "\<And>x. x \<in> F \<Longrightarrow> reachable s x"
    and complete_u: "d u = dist s u"
    and tight: "tight_edge_step u v"
  shows "sound_label (relax_frontier d F)"
    and "relax_frontier d F v = dist s v"
proof -
  let ?es = "edge_list_of (outgoing_edges F)"
  have set_es: "set ?es = outgoing_edges F"
    using edge_list_of_properties(1)[OF finite_outgoing_edges] .
  have edge_uv: "(u, v) \<in> E"
    using tight unfolding tight_edge_step_def by blast
  have mem_uv: "(u, v) \<in> set ?es"
    using set_es edge_uv uF unfolding outgoing_edges_def by blast
  obtain pre extra where es_split: "?es = pre @ (u, v) # extra"
    using split_list[OF mem_uv] by blast
  have bounded: "within_k_edges [u, v] (Suc 0)"
    unfolding within_k_edges_def by simp
  have tight_path: "successively tight_edge_step [u, v]"
    using tight by simp
  have es_path: "?es = pre @ path_edges [u, v] @ extra"
    using es_split by simp
  have pre_edges: "\<And>a b. (a, b) \<in> set pre \<Longrightarrow> (a, b) \<in> E"
    using set_es es_split unfolding outgoing_edges_def by auto
  have pre_reaches: "\<And>a b. (a, b) \<in> set pre \<Longrightarrow> reachable s a"
    using set_es es_split frontier_reaches unfolding outgoing_edges_def by auto
  have extra_edges: "\<And>a b. (a, b) \<in> set extra \<Longrightarrow> (a, b) \<in> E"
    using set_es es_split unfolding outgoing_edges_def by auto
  have extra_reaches: "\<And>a b. (a, b) \<in> set extra \<Longrightarrow> reachable s a"
    using set_es es_split frontier_reaches unfolding outgoing_edges_def by auto
  have core1_path: "sound_label (relax_edges d (pre @ path_edges [u, v] @ extra))"
  proof (rule find_pivots_tight_path_block_completion(1)
      [where p = "[u, v]" and k = "Suc 0" and pre = pre and extra = extra])
    show "within_k_edges [u, v] (Suc 0)"
      using bounded .
    show "sound_label d"
      using sound .
    show "d (hd [u, v]) = dist s (hd [u, v])"
      using complete_u by simp
    show "successively tight_edge_step [u, v]"
      using tight_path .
    show "pre @ path_edges [u, v] @ extra = pre @ path_edges [u, v] @ extra"
      by simp
    show "\<And>a b. (a, b) \<in> set pre \<Longrightarrow> (a, b) \<in> E"
      using pre_edges .
    show "\<And>a b. (a, b) \<in> set pre \<Longrightarrow> reachable s a"
      using pre_reaches .
    show "\<And>a b. (a, b) \<in> set extra \<Longrightarrow> (a, b) \<in> E"
      using extra_edges .
    show "\<And>a b. (a, b) \<in> set extra \<Longrightarrow> reachable s a"
      using extra_reaches .
  qed
  have core2_path: "relax_edges d (pre @ path_edges [u, v] @ extra) v = dist s v"
  proof -
    have "relax_edges d (pre @ path_edges [u, v] @ extra) (last [u, v]) =
        dist s (last [u, v])"
    proof (rule find_pivots_tight_path_block_completion(2)
        [where p = "[u, v]" and k = "Suc 0" and pre = pre and extra = extra])
      show "within_k_edges [u, v] (Suc 0)"
        using bounded .
      show "sound_label d"
        using sound .
      show "d (hd [u, v]) = dist s (hd [u, v])"
        using complete_u by simp
      show "successively tight_edge_step [u, v]"
        using tight_path .
      show "pre @ path_edges [u, v] @ extra = pre @ path_edges [u, v] @ extra"
        by simp
      show "\<And>a b. (a, b) \<in> set pre \<Longrightarrow> (a, b) \<in> E"
        using pre_edges .
      show "\<And>a b. (a, b) \<in> set pre \<Longrightarrow> reachable s a"
        using pre_reaches .
      show "\<And>a b. (a, b) \<in> set extra \<Longrightarrow> (a, b) \<in> E"
        using extra_edges .
      show "\<And>a b. (a, b) \<in> set extra \<Longrightarrow> reachable s a"
        using extra_reaches .
    qed
    then show ?thesis
      by simp
  qed
  have core1: "sound_label (relax_edges d ?es)"
    using core1_path es_path by simp
  have core2: "relax_edges d ?es v = dist s v"
    using core2_path es_path by simp
  show "sound_label (relax_frontier d F)"
    using core1 unfolding relax_frontier_def .
  show "relax_frontier d F v = dist s v"
    using core2 unfolding relax_frontier_def .
qed

end

end
