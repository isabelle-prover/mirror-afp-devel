theory BMSSP_Runtime_Instance
  imports BMSSP_Top_Level_Bounds BMSSP_Executable_Base_Case
begin

section \<open>A Concrete Non-Vacuous Instance of the Runtime Locale\<close>

text \<open>
  The asymptotic running-time headline lives in the
  @{locale bounded_reduced_positive_instance} locale, whose interpretation
  yields the closed theorem @{thm [source]
  bmssp_runtime_headline_instance.bmssp_runtime_bigo_target}.  A locale theorem
  only carries content once the locale is shown to be inhabited.  This theory
  exhibits a concrete, non-trivial graph---the unit-weight directed path
  \<open>0 \<rightarrow> 1 \<rightarrow> 2 \<rightarrow> 3\<close>---and discharges every assumption of that locale,
  obtaining the \<open>O(m * (ln n) powr (2 / 3))\<close> bound for it as a closed,
  assumption-free statement.  This certifies that the runtime headline is not
  vacuously true.

  Uniqueness of shortest walks---the only non-routine locale assumption---is
  obtained from the verified simple-walk enumerator
  @{const exec_simple_walks_betw}: on this graph the enumerator returns exactly
  one simple walk to each vertex, so any two shortest walks to a vertex
  coincide.
\<close>

definition path_vs :: "nat list" where
  "path_vs = [0, 1, 2, 3]"

definition path_es :: "(nat \<times> nat) list" where
  "path_es = [(0, 1), (1, 2), (2, 3)]"

definition path_V :: "nat set" where
  "path_V = set path_vs"

definition path_E :: "(nat \<times> nat) set" where
  "path_E = set path_es"

definition path_weight :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "path_weight u v = (if (u, v) \<in> path_E then 1 else 0)"

lemma path_vs_V: "set path_vs = path_V"
  unfolding path_V_def by (rule refl)

lemma path_es_E: "set path_es = path_E"
  unfolding path_E_def by (rule refl)

lemma path_positive_weight: "(u, v) \<in> path_E \<Longrightarrow> 0 < path_weight u v"
  unfolding path_weight_def by simp

lemma path_finite_weighted_digraph:
  "finite_weighted_digraph path_V path_E path_weight 0"
  unfolding finite_weighted_digraph_def
    path_V_def path_vs_def path_E_def path_es_def path_weight_def
  by auto

interpretation pfw: finite_weighted_digraph path_V path_E path_weight 0
  by (rule path_finite_weighted_digraph)

text \<open>
  The enumerator returns exactly one simple walk from \<open>0\<close> to each vertex,
  checked by evaluation of the generated code.
\<close>

lemma path_walk_lists:
  "exec_simple_walks_betw path_vs path_es 0 0 = [[0]]"
  "exec_simple_walks_betw path_vs path_es 0 (Suc 0) = [[0, 1]]"
  "exec_simple_walks_betw path_vs path_es 0 2 = [[0, 1, 2]]"
  "exec_simple_walks_betw path_vs path_es 0 3 = [[0, 1, 2, 3]]"
  by eval+

lemma path_simple_walk_sets:
  "{p. pfw.simple_walk_betw 0 p 0} = {[0]}"
  "{p. pfw.simple_walk_betw 0 p (Suc 0)} = {[0, 1]}"
  "{p. pfw.simple_walk_betw 0 p 2} = {[0, 1, 2]}"
  "{p. pfw.simple_walk_betw 0 p 3} = {[0, 1, 2, 3]}"
  using pfw.set_exec_simple_walks_betw[OF path_vs_V path_es_E, symmetric]
  by (simp_all add: path_walk_lists)

lemma path_walk_vertex:
  assumes "pfw.simple_walk_betw 0 p v"
  shows "v \<in> path_V"
proof -
  have walk_p: "pfw.walk p" and p_ne: "p \<noteq> []" and last_p: "last p = v"
    using assms unfolding pfw.simple_walk_betw_def pfw.walk_betw_def by auto
  have "v \<in> set p"
    using p_ne last_p by (metis last_in_set)
  moreover have "set p \<subseteq> path_V"
    using walk_p by (rule pfw.walk_set_subset)
  ultimately show ?thesis by blast
qed

lemma path_unique_shortest_walk:
  assumes "pfw.shortest_walk 0 p v" and "pfw.shortest_walk 0 q v"
  shows "p = q"
proof -
  have p: "pfw.simple_walk_betw 0 p v" and q: "pfw.simple_walk_betw 0 q v"
    using assms unfolding pfw.shortest_walk_def by blast+
  have vV: "v \<in> path_V"
    using p by (rule path_walk_vertex)
  have pm: "p \<in> {r. pfw.simple_walk_betw 0 r v}"
    using p by simp
  have qm: "q \<in> {r. pfw.simple_walk_betw 0 r v}"
    using q by simp
  from vV consider "v = 0" | "v = Suc 0" | "v = 2" | "v = 3"
    unfolding path_V_def path_vs_def by auto
  then show "p = q"
  proof cases
    case 1 with pm qm show ?thesis by (simp add: path_simple_walk_sets)
  next
    case 2 with pm qm show ?thesis by (simp add: path_simple_walk_sets)
  next
    case 3 with pm qm show ?thesis by (simp add: path_simple_walk_sets)
  next
    case 4 with pm qm show ?thesis by (simp add: path_simple_walk_sets)
  qed
qed

lemma path_all_reachable:
  assumes "v \<in> path_V"
  shows "pfw.reachable 0 v"
proof -
  from assms consider "v = 0" | "v = Suc 0" | "v = 2" | "v = 3"
    unfolding path_V_def path_vs_def by auto
  then show ?thesis
  proof cases
    case 1
    have "[0] \<in> {r. pfw.simple_walk_betw 0 r 0}"
      by (simp add: path_simple_walk_sets)
    with 1 show ?thesis unfolding pfw.reachable_def by auto
  next
    case 2
    have "[0, 1] \<in> {r. pfw.simple_walk_betw 0 r (Suc 0)}"
      by (simp add: path_simple_walk_sets)
    with 2 show ?thesis unfolding pfw.reachable_def by auto
  next
    case 3
    have "[0, 1, 2] \<in> {r. pfw.simple_walk_betw 0 r 2}"
      by (simp add: path_simple_walk_sets)
    with 3 show ?thesis unfolding pfw.reachable_def by auto
  next
    case 4
    have "[0, 1, 2, 3] \<in> {r. pfw.simple_walk_betw 0 r 3}"
      by (simp add: path_simple_walk_sets)
    with 4 show ?thesis unfolding pfw.reachable_def by auto
  qed
qed

interpretation pusd: unique_shortest_digraph path_V path_E path_weight 0
  by unfold_locales (rule path_unique_shortest_walk)

lemma path_edge_outdegree: "pusd.edge_outdegree_le 1"
  unfolding pusd.edge_outdegree_le_def
proof
  fix u :: nat
  assume "u \<in> path_V"
  then consider "u = 0" | "u = Suc 0" | "u = 2" | "u = 3"
    unfolding path_V_def path_vs_def by auto
  then show "card (pusd.outgoing_edges {u}) \<le> 1"
  proof cases
    case 1
    then have "pusd.outgoing_edges {u} = {(0, 1)}"
      unfolding pusd.outgoing_edges_def by (auto simp: path_E_def path_es_def)
    then show ?thesis by simp
  next
    case 2
    then have "pusd.outgoing_edges {u} = {(1, 2)}"
      unfolding pusd.outgoing_edges_def by (auto simp: path_E_def path_es_def)
    then show ?thesis by simp
  next
    case 3
    then have "pusd.outgoing_edges {u} = {(2, 3)}"
      unfolding pusd.outgoing_edges_def by (auto simp: path_E_def path_es_def)
    then show ?thesis by simp
  next
    case 4
    then have "pusd.outgoing_edges {u} = {}"
      unfolding pusd.outgoing_edges_def by (auto simp: path_E_def path_es_def)
    then show ?thesis by simp
  qed
qed

interpretation pbr: bounded_reduced_positive_instance path_V path_E path_weight 0 1
  by unfold_locales
     (use path_positive_weight path_all_reachable path_edge_outdegree in auto)

text \<open>
  The closed running-time bound for the concrete path instance.  Because it is
  obtained by interpreting @{locale bounded_reduced_positive_instance} on an
  explicit graph, it has no remaining locale hypotheses: it is an
  assumption-free witness that the BMSSP runtime headline is satisfiable by a
  genuine non-trivial digraph.
\<close>

lemmas path_runtime_bigo_target =
  pbr.runtime_headline.bmssp_runtime_bigo_target

end
