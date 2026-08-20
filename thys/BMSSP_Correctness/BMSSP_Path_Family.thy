theory BMSSP_Path_Family
  imports BMSSP_Top_Level_Bounds BMSSP_Executable_Base_Case
begin

section \<open>A Size-Indexed Family of Runtime Instances\<close>

text \<open>
  The runtime headline
  @{thm bmssp_runtime_headline_instance.bmssp_runtime_bigo_target} is a theorem
  of the @{locale bounded_reduced_positive_instance} locale.  The theory
  \<^file>\<open>BMSSP_Runtime_Instance.thy\<close> interprets that locale on the single fixed
  graph \<open>0 \<rightarrow> 1 \<rightarrow> 2 \<rightarrow> 3\<close>, which certifies non-vacuity at one size only, and
  whose edge count is therefore a constant.

  This theory removes that limitation.  For every \<open>n\<close> it builds the unit-weight
  directed path \<open>0 \<rightarrow> 1 \<rightarrow> \<dots> \<rightarrow> n\<close>, proves that it satisfies all assumptions of
  @{locale bounded_reduced_positive_instance} \emph{uniformly in \<open>n\<close>}, and
  obtains the deterministic running-time bound for a family whose vertex count
  \<open>n + 1\<close> and edge count \<open>n\<close> grow without bound.  The only non-routine
  assumption, uniqueness of shortest walks, is discharged by the structural fact
  that in such a path the only walk starting at \<open>0\<close> is an initial segment
  \<open>[0, 1, \<dots>, k]\<close>.  Unlike the fixed instance, no step uses code evaluation; the
  argument is a single induction valid for all \<open>n\<close>.
\<close>

subsection \<open>The Path Graph of Size \<open>n\<close>\<close>

definition pf_V :: "nat \<Rightarrow> nat set" where
  "pf_V n = {0..n}"

definition pf_E :: "nat \<Rightarrow> (nat \<times> nat) set" where
  "pf_E n = {(i, Suc i) | i. i < n}"

definition pf_w :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "pf_w u v = 1"

lemma pf_E_iff: "(a, b) \<in> pf_E n \<longleftrightarrow> a < n \<and> b = Suc a"
  unfolding pf_E_def by auto

lemma pf_finite_weighted_digraph:
  "finite_weighted_digraph (pf_V n) (pf_E n) pf_w 0"
proof
  show "finite (pf_V n)"
    unfolding pf_V_def by simp
  show "0 \<in> pf_V n"
    unfolding pf_V_def by simp
  show "\<And>u v. (u, v) \<in> pf_E n \<Longrightarrow> u \<in> pf_V n \<and> v \<in> pf_V n"
    unfolding pf_V_def by (auto simp: pf_E_iff)
  show "\<And>u v. (u, v) \<in> pf_E n \<Longrightarrow> 0 \<le> pf_w u v"
    unfolding pf_w_def by simp
qed

subsection \<open>The Path Family Locale\<close>

text \<open>
  Fixing the size \<open>n\<close> in a locale lets us interpret the graph locales for
  \<open>pf_V n\<close>, \<open>pf_E n\<close>, while keeping \<open>n\<close> schematic across the whole development.
\<close>

locale path_family =
  fixes n :: nat
begin

interpretation pf: finite_weighted_digraph "pf_V n" "pf_E n" pf_w 0
  by (rule pf_finite_weighted_digraph)

subsubsection \<open>The Only Walk From the Source Is an Initial Segment\<close>

text \<open>
  Vertex \<open>i\<close> has the single out-edge \<open>(i, Suc i)\<close>, so any walk starting at \<open>0\<close>
  is forced to visit \<open>0, 1, 2, \<dots>\<close> in order: its \<open>i\<close>-th element is \<open>i\<close>.
\<close>

lemma pf_walk_nth:
  assumes walk: "pf.walk p"
    and hd0: "hd p = 0"
    and i: "i < length p"
  shows "p ! i = i"
  using i
proof (induction i)
  case 0
  have "p \<noteq> []" using assms(3) by auto
  then show ?case using hd0 by (simp add: hd_conv_nth)
next
  case (Suc i)
  have i_lt: "i < length p" using Suc.prems by simp
  have ih: "p ! i = i" using Suc.IH[OF i_lt] .
  have edge: "(p ! i, p ! Suc i) \<in> pf_E n"
    by (rule pf.walk_nth_edge[OF walk Suc.prems])
  have "p ! Suc i = Suc (p ! i)"
    using edge by (simp add: pf_E_iff)
  then show ?case using ih by simp
qed

lemma pf_walk_from_0_eq_upt:
  assumes walk: "pf.walk p"
    and hd0: "hd p = 0"
  shows "p = [0..<length p]"
proof (rule nth_equalityI)
  show "length p = length [0..<length p]" by simp
  fix i assume "i < length p"
  then show "p ! i = [0..<length p] ! i"
    using pf_walk_nth[OF walk hd0] by simp
qed

lemma pf_simple_walk_betw_eq:
  assumes "pf.simple_walk_betw 0 p v"
  shows "p = [0..<Suc v]"
proof -
  have walk: "pf.walk p" and ne: "p \<noteq> []"
    and hd0: "hd p = 0" and last_v: "last p = v"
    using assms unfolding pf.simple_walk_betw_def pf.walk_betw_def by auto
  have p_eq: "p = [0..<length p]"
    by (rule pf_walk_from_0_eq_upt[OF walk hd0])
  have len_pos: "0 < length p" using ne by auto
  have "p ! (length p - 1) = length p - 1"
    using pf_walk_nth[OF walk hd0] len_pos by simp
  moreover have "last p = p ! (length p - 1)"
    using ne by (simp add: last_conv_nth)
  ultimately have "v = length p - 1" using last_v by simp
  then have "length p = Suc v" using len_pos by simp
  then show ?thesis using p_eq by simp
qed

subsubsection \<open>Reachability and Uniqueness\<close>

lemma pf_upt_simple_walk:
  assumes "v \<le> n"
  shows "pf.simple_walk_betw 0 [0..<Suc v] v"
proof -
  have walk: "pf.walk [0..<Suc v]"
    using assms
  proof (induction v)
    case 0
    have "[0..<Suc 0] = [0]" by simp
    moreover have "pf.walk [0]"
      using pf.walk.simps(2)[of 0] unfolding pf_V_def by simp
    ultimately show ?case by simp
  next
    case (Suc v)
    have v_le: "v \<le> n" using Suc.prems by simp
    have wv: "pf.walk [0..<Suc v]" by (rule Suc.IH[OF v_le])
    have upt_eq: "[0..<Suc (Suc v)] = [0..<Suc v] @ [Suc v]"
      by (simp add: upt_Suc_append)
    have edge: "(v, Suc v) \<in> pf_E n"
      using Suc.prems by (simp add: pf_E_iff)
    have last_wv: "last [0..<Suc v] = v" by simp
    have ne: "[0..<Suc v] \<noteq> []" by simp
    have hd_wv: "hd [0..<Suc v] = 0"
      using upt_conv_Cons[of 0 "Suc v"] by simp
    have sb: "pf.simple_walk_betw 0 [0..<Suc v] v"
      unfolding pf.simple_walk_betw_def pf.walk_betw_def
      using wv last_wv ne hd_wv by simp
    have fresh: "Suc v \<notin> set [0..<Suc v]" by simp
    have sw: "pf.simple_walk_betw 0 ([0..<Suc v] @ [Suc v]) (Suc v)"
      by (rule pf.simple_walk_snoc[OF sb edge fresh])
    then have "pf.walk ([0..<Suc v] @ [Suc v])"
      unfolding pf.simple_walk_betw_def pf.walk_betw_def by simp
    then show ?case
      unfolding upt_eq .
  qed
  have hd0: "hd [0..<Suc v] = 0"
    using upt_conv_Cons[of 0 "Suc v"] by simp
  have last_v: "last [0..<Suc v] = v" by simp
  show ?thesis
    unfolding pf.simple_walk_betw_def pf.walk_betw_def
    using walk hd0 last_v by simp
qed

lemma pf_all_reachable:
  assumes "v \<in> pf_V n"
  shows "pf.reachable 0 v"
proof -
  have "v \<le> n" using assms unfolding pf_V_def by simp
  then have "pf.simple_walk_betw 0 [0..<Suc v] v"
    by (rule pf_upt_simple_walk)
  then show ?thesis unfolding pf.reachable_def by blast
qed

lemma pf_unique_shortest_walk:
  assumes "pf.shortest_walk 0 p v" and "pf.shortest_walk 0 q v"
  shows "p = q"
proof -
  have sp: "pf.simple_walk_betw 0 p v" and sq: "pf.simple_walk_betw 0 q v"
    using assms unfolding pf.shortest_walk_def by blast+
  have "p = [0..<Suc v]" by (rule pf_simple_walk_betw_eq[OF sp])
  moreover have "q = [0..<Suc v]" by (rule pf_simple_walk_betw_eq[OF sq])
  ultimately show ?thesis by simp
qed

text \<open>
  With uniqueness in hand we may interpret the @{locale unique_shortest_digraph}
  layer, which is where @{const unique_shortest_digraph.edge_outdegree_le} and
  @{const unique_shortest_digraph.outgoing_edges} live.
\<close>

interpretation pf_usd: unique_shortest_digraph "pf_V n" "pf_E n" pf_w 0
  by unfold_locales (rule pf_unique_shortest_walk)

subsubsection \<open>Bounded Out-Degree and Positive Weights\<close>

lemma pf_positive_weight: "(u, v) \<in> pf_E n \<Longrightarrow> 0 < pf_w u v"
  unfolding pf_w_def by simp

lemma pf_edge_outdegree: "pf_usd.edge_outdegree_le 1"
  unfolding pf_usd.edge_outdegree_le_def
proof
  fix u :: nat
  assume "u \<in> pf_V n"
  have sub: "pf_usd.outgoing_edges {u} \<subseteq> {(u, Suc u)}"
    unfolding pf_usd.outgoing_edges_def by (auto simp: pf_E_iff)
  have "card (pf_usd.outgoing_edges {u}) \<le> card {(u, Suc u)}"
    by (rule card_mono[OF _ sub]) simp
  then show "card (pf_usd.outgoing_edges {u}) \<le> 1" by simp
qed

subsubsection \<open>The Reduced Positive Instance and Its Running-Time Bound\<close>

sublocale pf_bri: bounded_reduced_positive_instance "pf_V n" "pf_E n" pf_w 0 1
proof unfold_locales
  show "\<And>u v. (u, v) \<in> pf_E n \<Longrightarrow> 0 < pf_w u v"
    by (rule pf_positive_weight)
  show "\<And>v. v \<in> pf_V n \<Longrightarrow> pf.reachable 0 v"
    by (rule pf_all_reachable)
  show "pf_usd.edge_outdegree_le 1"
    by (rule pf_edge_outdegree)
qed

text \<open>
  The vertex count is \<open>n + 1\<close> and the edge count is exactly \<open>n\<close>: both grow with
  the size parameter, unlike the constant edge count of the fixed instance.
\<close>

lemma pf_vertex_count: "pf_usd.vertex_count = Suc n"
proof -
  have "pf_usd.vertex_count = card (pf_V n)"
    by (rule pf_usd.vertex_count_def)
  also have "\<dots> = card {0..n}"
    unfolding pf_V_def by (rule refl)
  also have "\<dots> = Suc n"
    by simp
  finally show ?thesis .
qed

lemma pf_edge_count: "pf_usd.edge_count = n"
proof -
  have inj: "inj_on (\<lambda>i. (i, Suc i)) {i. i < n}"
    by (rule inj_onI) auto
  have "pf_E n = (\<lambda>i. (i, Suc i)) ` {i. i < n}"
    unfolding pf_E_def by auto
  then have "pf_usd.edge_count = card ((\<lambda>i. (i, Suc i)) ` {i. i < n})"
    unfolding pf_usd.edge_count_def by simp
  also have "\<dots> = card {i. i < n}"
    using inj by (simp add: card_image)
  also have "\<dots> = n" by simp
  finally show ?thesis .
qed

text \<open>
  The closed running-time bound for the path of size \<open>n\<close>, with all locale
  hypotheses discharged.  This is the deterministic
  \<open>O(m * (ln N) powr (2/3))\<close> envelope of the headline, now holding for a member
  of the family of \emph{every} size.  The time and size functions are named
  locally so the re-exported statement below is free of deep qualified names.
\<close>

definition pf_T :: "nat \<Rightarrow> nat" where
  "pf_T = pf_bri.runtime_headline.T_bmssp"

definition pf_m :: "nat \<Rightarrow> nat" where
  "pf_m = pf_bri.runtime_headline.m"

lemma pf_runtime_bigo_target:
  "(\<lambda>N. real (pf_T N)) \<in>
    O(\<lambda>N. real (pf_m N) * (ln (real N + 2)) powr (2 / 3))"
  unfolding pf_T_def pf_m_def
  by (rule pf_bri.runtime_headline.bmssp_runtime_bigo_target)

text \<open>
  Locale-level names for the graph-size measures, so the external re-exports
  avoid deep interpretation-qualified constants.
\<close>

definition pf_verts :: nat where
  "pf_verts = pf_usd.vertex_count"

definition pf_edges :: nat where
  "pf_edges = pf_usd.edge_count"

lemma pf_verts_eq: "pf_verts = Suc n"
  unfolding pf_verts_def by (rule pf_vertex_count)

lemma pf_edges_eq: "pf_edges = n"
  unfolding pf_edges_def by (rule pf_edge_count)

end

subsection \<open>The Bound Holds at Every Size\<close>

text \<open>
  Re-exported outside the locale: for every size parameter \<open>n\<close>, the path graph
  on \<open>n + 1\<close> vertices and \<open>n\<close> edges satisfies the deterministic BMSSP
  running-time bound, and its edge count really is \<open>n\<close>.  Because \<open>n\<close> is
  universally quantified, this is a single statement witnessing non-vacuity of
  the runtime locale across all sizes, not merely at one fixed graph.
\<close>

theorem path_family_runtime_bigo_target:
  fixes n :: nat
  shows "(\<lambda>N. real (path_family.pf_T n N)) \<in>
    O(\<lambda>N. real (path_family.pf_m n N) * (ln (real N + 2)) powr (2 / 3))"
proof -
  interpret path_family n .
  show ?thesis
    by (rule pf_runtime_bigo_target)
qed

theorem path_family_edge_count:
  fixes n :: nat
  shows "path_family.pf_edges n = n"
proof -
  interpret path_family n .
  show ?thesis
    by (rule pf_edges_eq)
qed

theorem path_family_vertex_count:
  fixes n :: nat
  shows "path_family.pf_verts n = Suc n"
proof -
  interpret path_family n .
  show ?thesis
    by (rule pf_verts_eq)
qed

end
