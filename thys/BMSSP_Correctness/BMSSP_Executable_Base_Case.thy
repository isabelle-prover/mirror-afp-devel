theory BMSSP_Executable_Base_Case
  imports BMSSP_Base_Case BMSSP_Code_Export "HOL-Library.Multiset"
begin

section \<open>Executable Base-Case Ordering\<close>

text \<open>
  The semantic base-case theory orders a finite set by
  @{const finite_weighted_digraph.dist}.  The functions below provide an
  executable finite counterpart: enumerate simple walks over explicit vertex
  and edge lists, compute their weights by a list minimum, and sort the target
  vertices by the resulting finite distance scan.
\<close>

fun exec_walk :: "'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "exec_walk vs es [] \<longleftrightarrow> False"
| "exec_walk vs es [x] \<longleftrightarrow> x \<in> set vs"
| "exec_walk vs es (x # y # xs) \<longleftrightarrow>
     x \<in> set vs \<and> (x, y) \<in> set es \<and> exec_walk vs es (y # xs)"

fun exec_walk_weight :: "('v \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> 'v list \<Rightarrow> real" where
  "exec_walk_weight W [] = 0"
| "exec_walk_weight W [x] = 0"
| "exec_walk_weight W (x # y # xs) = W x y + exec_walk_weight W (y # xs)"

definition exec_simple_walks_betw ::
  "'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v list list" where
  "exec_simple_walks_betw vs es a b =
     filter (\<lambda>p. p \<noteq> [] \<and> hd p = a \<and> last p = b \<and>
       exec_walk vs es p \<and> distinct p)
       (concat (map (\<lambda>n. List.n_lists n vs) [1..<Suc (length vs)]))"

definition exec_walk_weights ::
  "'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> real list" where
  "exec_walk_weights vs es W a b =
     map (exec_walk_weight W) (exec_simple_walks_betw vs es a b)"

definition exec_dist ::
  "'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> real" where
  "exec_dist vs es W a b =
     (case exec_walk_weights vs es W a b of [] \<Rightarrow> 0 | ws \<Rightarrow> min_list ws)"

definition exec_closest_vertices ::
  "'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'v list" where
  "exec_closest_vertices vs es W src xs =
     sort_key (exec_dist vs es W src) (remdups xs)"

definition exec_reachable ::
  "'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "exec_reachable vs es a b \<longleftrightarrow> exec_simple_walks_betw vs es a b \<noteq> []"

definition exec_shortest_through ::
  "'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "exec_shortest_through vs es W src x v \<longleftrightarrow>
     (\<exists>p\<in>set (exec_simple_walks_betw vs es src v).
        exec_walk_weight W p = exec_dist vs es W src v \<and> x \<in> set p)"

definition exec_bound_tree_vertices ::
  "'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bound \<Rightarrow> 'v list" where
  "exec_bound_tree_vertices vs es W src x B =
     filter (\<lambda>v. exec_reachable vs es src v \<and>
       exec_shortest_through vs es W src x v \<and>
       below_bound (exec_dist vs es W src v) B)
       (remdups vs)"

definition exec_base_case_order ::
  "('v \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow>
    'v \<Rightarrow> bound \<Rightarrow> 'v list" where
  "exec_base_case_order W src vs es x B =
     exec_closest_vertices vs es W src (exec_bound_tree_vertices vs es W src x B)"

definition exec_base_case_vertices ::
  "('v \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow>
    nat \<Rightarrow> 'v \<Rightarrow> bound \<Rightarrow> 'v set" where
  "exec_base_case_vertices W src vs es k x B =
     (let xs = exec_base_case_order W src vs es x B in
       if length xs \<le> k then set xs
       else set (filter (\<lambda>v. exec_dist vs es W src v < exec_dist vs es W src (xs ! k))
              (take (Suc k) xs)))"

definition exec_base_case_bound ::
  "('v \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow>
    nat \<Rightarrow> 'v \<Rightarrow> bound \<Rightarrow> bound" where
  "exec_base_case_bound W src vs es k x B =
     (let xs = exec_base_case_order W src vs es x B in
       if length xs \<le> k then B else Fin (exec_dist vs es W src (xs ! k)))"

definition exec_base_case_result ::
  "('v \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow>
    nat \<Rightarrow> 'v \<Rightarrow> bound \<Rightarrow> bound \<times> 'v set" where
  "exec_base_case_result W src vs es k x B =
     (exec_base_case_bound W src vs es k x B,
      exec_base_case_vertices W src vs es k x B)"

context finite_weighted_digraph
begin

lemma exec_walk_iff_walk:
  assumes "set vs = V" "set es = E"
  shows "exec_walk vs es p \<longleftrightarrow> walk p"
  using assms by (induction p rule: exec_walk.induct) simp_all

lemma exec_walk_weight_eq_walk_weight [simp]:
  "exec_walk_weight w p = walk_weight p"
  by (induction p rule: walk_weight.induct) simp_all

lemma set_exec_simple_walks_betw:
  assumes vs: "set vs = V"
    and es: "set es = E"
  shows "set (exec_simple_walks_betw vs es a b) = {p. simple_walk_betw a p b}"
proof
  show "set (exec_simple_walks_betw vs es a b) \<subseteq> {p. simple_walk_betw a p b}"
    unfolding exec_simple_walks_betw_def simple_walk_betw_def walk_betw_def
    using exec_walk_iff_walk[OF vs es] by auto
next
  show "{p. simple_walk_betw a p b} \<subseteq> set (exec_simple_walks_betw vs es a b)"
  proof
    fix p
    assume p: "p \<in> {p. simple_walk_betw a p b}"
    then have simple: "simple_walk_betw a p b"
      by simp
    then have walk_p: "walk p" and distinct_p: "distinct p"
      and p_ne: "p \<noteq> []" and hd_p: "hd p = a" and last_p: "last p = b"
      unfolding simple_walk_betw_def walk_betw_def by auto
    have len_le_card: "length p \<le> card V"
      by (rule simple_walk_length_le_card[OF simple])
    have card_le_len: "card V \<le> length vs"
      using card_length[of vs] vs by simp
    have len_le: "length p \<le> length vs"
      using len_le_card card_le_len by linarith
    have len_pos: "0 < length p"
      using p_ne by (cases p) auto
    have p_in_lists: "p \<in> set (List.n_lists (length p) vs)"
      using walk_set_subset[OF walk_p] vs
      by (auto simp: set_n_lists)
    have len_mem: "length p \<in> set [1..<Suc (length vs)]"
    proof -
      have "1 \<le> length p"
        using len_pos by linarith
      moreover have "length p < Suc (length vs)"
        using len_le by simp
      ultimately show ?thesis
        by auto
    qed
    have enum: "p \<in> set (concat (map (\<lambda>n. List.n_lists n vs) [1..<Suc (length vs)]))"
      using p_in_lists len_mem by auto
    have exec: "exec_walk vs es p"
      using exec_walk_iff_walk[OF vs es] walk_p by simp
    show "p \<in> set (exec_simple_walks_betw vs es a b)"
      unfolding exec_simple_walks_betw_def
      using enum exec distinct_p hd_p last_p p_ne by auto
  qed
qed

lemma set_exec_walk_weights:
  assumes vs: "set vs = V"
    and es: "set es = E"
  shows "set (exec_walk_weights vs es w a b) = simple_walk_weights a b"
  unfolding exec_walk_weights_def simple_walk_weights_def
  using set_exec_simple_walks_betw[OF vs es, of a b] by auto

lemma exec_walk_weights_nonempty:
  assumes vs: "set vs = V"
    and es: "set es = E"
    and reach: "reachable a b"
  shows "exec_walk_weights vs es w a b \<noteq> []"
proof
  assume empty: "exec_walk_weights vs es w a b = []"
  then have "simple_walk_weights a b = {}"
    using set_exec_walk_weights[OF vs es, of a b] by simp
  then show False
    using simple_walk_weights_nonempty[OF reach] by simp
qed

lemma exec_dist_eq_dist:
  assumes vs: "set vs = V"
    and es: "set es = E"
    and reach: "reachable a b"
  shows "exec_dist vs es w a b = dist a b"
proof -
  have nonempty: "exec_walk_weights vs es w a b \<noteq> []"
    using exec_walk_weights_nonempty[OF vs es reach] .
  have "exec_dist vs es w a b = min_list (exec_walk_weights vs es w a b)"
    using nonempty unfolding exec_dist_def by (cases "exec_walk_weights vs es w a b") simp_all
  also have "\<dots> = Min (set (exec_walk_weights vs es w a b))"
    using min_list_Min[OF nonempty] .
  also have "\<dots> = Min (simple_walk_weights a b)"
    using set_exec_walk_weights[OF vs es, of a b] by simp
  also have "\<dots> = dist a b"
    unfolding dist_def by simp
  finally show ?thesis .
qed

lemma exec_closest_vertices_properties:
  assumes vs: "set vs = V"
    and es: "set es = E"
    and xs: "set xs = A"
    and reach_A: "A \<subseteq> {v. reachable s v}"
  shows "set (exec_closest_vertices vs es w s xs) = A"
    and "distinct (exec_closest_vertices vs es w s xs)"
    and "sorted_wrt (\<lambda>u v. dist s u \<le> dist s v)
      (exec_closest_vertices vs es w s xs)"
proof -
  let ?ys = "exec_closest_vertices vs es w s xs"
  have set_ys: "set ?ys = A"
    unfolding exec_closest_vertices_def using xs by simp
  then show "set ?ys = A" .
  show "distinct ?ys"
    unfolding exec_closest_vertices_def by simp
  have eq_on: "\<And>v. v \<in> set ?ys \<Longrightarrow> exec_dist vs es w s v = dist s v"
    using exec_dist_eq_dist[OF vs es] reach_A set_ys by blast
  have "sorted (map (exec_dist vs es w s) ?ys)"
    unfolding exec_closest_vertices_def by (rule sorted_sort_key)
  then have "sorted (map (dist s) ?ys)"
    by (simp add: map_cong[OF refl eq_on])
  then show "sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) ?ys"
    by (simp add: sorted_map)
qed

lemma closest_vertices_executable:
  assumes vs: "set vs = V"
    and es: "set es = E"
    and xs: "set xs = A"
    and reach_A: "A \<subseteq> {v. reachable s v}"
  shows "set (exec_closest_vertices vs es w s xs) = A"
    and "distinct (exec_closest_vertices vs es w s xs)"
    and "sorted_wrt (\<lambda>u v. dist s u \<le> dist s v)
      (exec_closest_vertices vs es w s xs)"
  using exec_closest_vertices_properties[OF assms] by blast+

lemma closest_vertices_eq_exec_if_inj:
  assumes vs: "set vs = V"
    and es: "set es = E"
    and xs: "set xs = A"
    and reach_A: "A \<subseteq> {v. reachable s v}"
    and inj: "inj_on (dist s) A"
  shows "closest_vertices A = exec_closest_vertices vs es w s xs"
proof -
  have finite_A: "finite A"
    using xs by auto
  have cv_set: "set (closest_vertices A) = A"
    by (rule closest_vertices_properties(1)[OF finite_A])
  have cv_distinct: "distinct (closest_vertices A)"
    by (rule closest_vertices_properties(2)[OF finite_A])
  have cv_sorted: "sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) (closest_vertices A)"
    by (rule closest_vertices_properties(3)[OF finite_A])
  have ex_set: "set (exec_closest_vertices vs es w s xs) = A"
    by (rule exec_closest_vertices_properties(1)[OF vs es xs reach_A])
  have ex_distinct: "distinct (exec_closest_vertices vs es w s xs)"
    by (rule exec_closest_vertices_properties(2)[OF vs es xs reach_A])
  have ex_sorted:
    "sorted_wrt (\<lambda>u v. dist s u \<le> dist s v)
      (exec_closest_vertices vs es w s xs)"
    by (rule exec_closest_vertices_properties(3)[OF vs es xs reach_A])
  have inj_union:
    "inj_on (dist s)
      (set (closest_vertices A) \<union> set (exec_closest_vertices vs es w s xs))"
    using inj cv_set ex_set by simp
  have cv_sorted_map: "sorted (map (dist s) (closest_vertices A))"
    using cv_sorted by (simp add: sorted_map)
  have ex_sorted_map: "sorted (map (dist s) (exec_closest_vertices vs es w s xs))"
    using ex_sorted by (simp add: sorted_map)
  have cv_distinct_map: "distinct (map (dist s) (closest_vertices A))"
    using cv_distinct inj cv_set by (simp add: distinct_map)
  have ex_distinct_map: "distinct (map (dist s) (exec_closest_vertices vs es w s xs))"
    using ex_distinct inj ex_set by (simp add: distinct_map)
  show ?thesis
    by (rule map_sorted_distinct_set_unique
      [OF inj_union cv_sorted_map cv_distinct_map ex_sorted_map ex_distinct_map])
      (simp add: cv_set ex_set)
qed

lemma exec_reachable_iff_reachable:
  assumes vs: "set vs = V"
    and es: "set es = E"
  shows "exec_reachable vs es a b \<longleftrightarrow> reachable a b"
proof -
  have "exec_reachable vs es a b \<longleftrightarrow>
      set (exec_simple_walks_betw vs es a b) \<noteq> {}"
    unfolding exec_reachable_def by auto
  also have "\<dots> \<longleftrightarrow> {p. simple_walk_betw a p b} \<noteq> {}"
    using set_exec_simple_walks_betw[OF vs es, of a b] by simp
  also have "\<dots> \<longleftrightarrow> reachable a b"
    unfolding reachable_def by auto
  finally show ?thesis .
qed

lemma exec_shortest_through_iff_through_single:
  assumes vs: "set vs = V"
    and es: "set es = E"
  shows "exec_shortest_through vs es w s x v \<longleftrightarrow> through {x} v"
proof
  assume exec: "exec_shortest_through vs es w s x v"
  then obtain p where p_exec:
      "p \<in> set (exec_simple_walks_betw vs es s v)"
      "exec_walk_weight w p = exec_dist vs es w s v"
      "x \<in> set p"
    unfolding exec_shortest_through_def by blast
  have p_simple: "simple_walk_betw s p v"
    using p_exec(1) set_exec_simple_walks_betw[OF vs es, of s v] by blast
  then have reach_v: "reachable s v"
    unfolding reachable_def by blast
  have "walk_weight p = dist s v"
    using p_exec(2) exec_dist_eq_dist[OF vs es reach_v] by simp
  then have "shortest_walk s p v"
    using p_simple unfolding shortest_walk_def by blast
  then show "through {x} v"
    using p_exec(3) unfolding through_def by blast
next
  assume through: "through {x} v"
  then obtain p where p: "shortest_walk s p v" "x \<in> set p"
    unfolding through_def by blast
  have p_simple: "simple_walk_betw s p v"
    using p(1) unfolding shortest_walk_def by blast
  have reach_v: "reachable s v"
    using p_simple unfolding reachable_def by blast
  have "p \<in> set (exec_simple_walks_betw vs es s v)"
    using p_simple set_exec_simple_walks_betw[OF vs es, of s v] by blast
  moreover have "exec_walk_weight w p = exec_dist vs es w s v"
    using p(1) exec_dist_eq_dist[OF vs es reach_v]
    unfolding shortest_walk_def by simp
  ultimately show "exec_shortest_through vs es w s x v"
    using p(2) unfolding exec_shortest_through_def by blast
qed

lemma set_exec_bound_tree_vertices:
  assumes vs: "set vs = V"
    and es: "set es = E"
  shows "set (exec_bound_tree_vertices vs es w s x B) = bound_tree {x} B"
proof
  show "set (exec_bound_tree_vertices vs es w s x B) \<subseteq> bound_tree {x} B"
  proof
    fix v
    assume v: "v \<in> set (exec_bound_tree_vertices vs es w s x B)"
    then have vV: "v \<in> V"
      using vs unfolding exec_bound_tree_vertices_def by auto
    have reach_v: "reachable s v"
      using v exec_reachable_iff_reachable[OF vs es, of s v]
      unfolding exec_bound_tree_vertices_def by auto
    have through_v: "through {x} v"
      using v exec_shortest_through_iff_through_single[OF vs es, of x v]
      unfolding exec_bound_tree_vertices_def by auto
    have below_v: "below_bound (dist s v) B"
      using v exec_dist_eq_dist[OF vs es reach_v]
      unfolding exec_bound_tree_vertices_def by auto
    show "v \<in> bound_tree {x} B"
      using vV reach_v through_v below_v unfolding bound_tree_def by blast
  qed
next
  show "bound_tree {x} B \<subseteq> set (exec_bound_tree_vertices vs es w s x B)"
  proof
    fix v
    assume v: "v \<in> bound_tree {x} B"
    then have vV: "v \<in> V" and reach_v: "reachable s v"
      and through_v: "through {x} v" and below_v: "below_bound (dist s v) B"
      unfolding bound_tree_def by auto
    have "exec_reachable vs es s v"
      using exec_reachable_iff_reachable[OF vs es, of s v] reach_v by simp
    moreover have "exec_shortest_through vs es w s x v"
      using exec_shortest_through_iff_through_single[OF vs es, of x v] through_v by simp
    moreover have "below_bound (exec_dist vs es w s v) B"
      using below_v exec_dist_eq_dist[OF vs es reach_v] by simp
    ultimately show "v \<in> set (exec_bound_tree_vertices vs es w s x B)"
      using vV vs unfolding exec_bound_tree_vertices_def by auto
  qed
qed

definition base_case_order_impl ::
  "'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 'v \<Rightarrow> bound \<Rightarrow> 'v list" where
  "base_case_order_impl vs es x B =
     exec_closest_vertices vs es w s (exec_bound_tree_vertices vs es w s x B)"

definition base_case_vertices_impl ::
  "'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> bound \<Rightarrow> 'v set" where
  "base_case_vertices_impl vs es k x B =
     (let xs = base_case_order_impl vs es x B in
       if length xs \<le> k then set xs
       else set (filter (\<lambda>v. exec_dist vs es w s v < exec_dist vs es w s (xs ! k))
              (take (Suc k) xs)))"

definition base_case_bound_impl ::
  "'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> bound \<Rightarrow> bound" where
  "base_case_bound_impl vs es k x B =
     (let xs = base_case_order_impl vs es x B in
       if length xs \<le> k then B else Fin (exec_dist vs es w s (xs ! k)))"

definition base_case_result_impl ::
  "'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> bound \<Rightarrow> bound \<times> 'v set" where
  "base_case_result_impl vs es k x B =
     (base_case_bound_impl vs es k x B, base_case_vertices_impl vs es k x B)"

declare base_case_order_impl_def [code]
declare base_case_vertices_impl_def [code]
declare base_case_bound_impl_def [code]
declare base_case_result_impl_def [code]

lemma base_case_order_impl_set:
  assumes vs: "set vs = V"
    and es: "set es = E"
  shows "set (base_case_order_impl vs es x B) = bound_tree {x} B"
  unfolding base_case_order_impl_def
  by (rule exec_closest_vertices_properties(1)
      [OF vs es set_exec_bound_tree_vertices[OF vs es]])
    (auto simp: bound_tree_def)

lemma base_case_order_impl_eq_if_inj:
  assumes vs: "set vs = V"
    and es: "set es = E"
    and inj: "inj_on (dist s) (bound_tree {x} B)"
  shows "base_case_order x B = base_case_order_impl vs es x B"
  unfolding base_case_order_def base_case_order_impl_def
  by (rule closest_vertices_eq_exec_if_inj
      [OF vs es set_exec_bound_tree_vertices[OF vs es]])
    (use inj in \<open>auto simp: bound_tree_def\<close>)

lemma base_case_order_impl_distinct:
  "distinct (base_case_order_impl vs es x B)"
  unfolding base_case_order_impl_def exec_closest_vertices_def by simp

lemma base_case_order_impl_sorted:
  assumes vs: "set vs = V"
    and es: "set es = E"
  shows "sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) (base_case_order_impl vs es x B)"
  unfolding base_case_order_impl_def
  by (rule exec_closest_vertices_properties(3)
      [OF vs es set_exec_bound_tree_vertices[OF vs es]])
    (auto simp: bound_tree_def)

lemma base_case_order_impl_length_eq:
  assumes vs: "set vs = V"
    and es: "set es = E"
  shows "length (base_case_order_impl vs es x B) = length (base_case_order x B)"
proof -
  have "length (base_case_order_impl vs es x B) =
      card (set (base_case_order_impl vs es x B))"
    using base_case_order_impl_distinct[of vs es x B] by (simp add: distinct_card)
  also have "\<dots> = card (bound_tree {x} B)"
    using base_case_order_impl_set[OF vs es, of x B] by simp
  also have "\<dots> = card (set (base_case_order x B))"
    using base_case_order_set[of x B] by simp
  also have "\<dots> = length (base_case_order x B)"
    using base_case_order_distinct[of x B] by (simp add: distinct_card)
  finally show ?thesis .
qed

lemma dist_map_eq_if_same_sorted_set:
  assumes sorted_x: "sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) xs"
    and sorted_y: "sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) ys"
    and distinct_x: "distinct xs"
    and distinct_y: "distinct ys"
    and set_eq: "set xs = set ys"
  shows "map (dist s) xs = map (dist s) ys"
proof -
  have sorted_x': "sorted (map (dist s) xs)"
    using sorted_x by (simp add: sorted_map)
  have sorted_y': "sorted (map (dist s) ys)"
    using sorted_y by (simp add: sorted_map)
  have "mset xs = mset ys"
    using distinct_x distinct_y set_eq
    by (simp add: set_eq_iff_mset_eq_distinct)
  then have mset_dist: "mset (map (dist s) xs) = mset (map (dist s) ys)"
    by simp
  have "sort (map (dist s) ys) = map (dist s) xs"
    by (rule properties_for_sort[OF mset_dist sorted_x'])
  moreover have "sort (map (dist s) ys) = map (dist s) ys"
    using sorted_y' by (simp add: sort_key_id_if_sorted)
  ultimately show ?thesis
    by simp
qed

lemma base_case_order_impl_kth_dist_eq:
  assumes vs: "set vs = V"
    and es: "set es = E"
    and k: "k < length (base_case_order x B)"
  shows "dist s ((base_case_order x B) ! k) =
    dist s ((base_case_order_impl vs es x B) ! k)"
proof -
  let ?xs = "base_case_order x B"
  let ?ys = "base_case_order_impl vs es x B"
  have len_y: "k < length ?ys"
    using k base_case_order_impl_length_eq[OF vs es, of x B] by simp
  have map_eq: "map (dist s) ?xs = map (dist s) ?ys"
    by (rule dist_map_eq_if_same_sorted_set)
      (use base_case_order_sorted base_case_order_impl_sorted[OF vs es]
        base_case_order_distinct base_case_order_impl_distinct
        base_case_order_set base_case_order_impl_set[OF vs es] in auto)
  have "map (dist s) ?xs ! k = map (dist s) ?ys ! k"
    using map_eq by simp
  then show ?thesis
    using k len_y by simp
qed

lemma exec_dist_eq_dist_on_base_case_order_impl:
  assumes vs: "set vs = V"
    and es: "set es = E"
    and v: "v \<in> set (base_case_order_impl vs es x B)"
  shows "exec_dist vs es w s v = dist s v"
proof -
  have "v \<in> bound_tree {x} B"
    using v base_case_order_impl_set[OF vs es, of x B] by simp
  then have "reachable s v"
    unfolding bound_tree_def by blast
  then show ?thesis
    by (rule exec_dist_eq_dist[OF vs es])
qed

lemma base_case_bound_impl_eq:
  assumes vs: "set vs = V"
    and es: "set es = E"
  shows "base_case_bound_impl vs es k x B = base_case_bound k x B"
proof (cases "length (base_case_order x B) \<le> k")
  case True
  then have "length (base_case_order_impl vs es x B) \<le> k"
    using base_case_order_impl_length_eq[OF vs es, of x B] by simp
  then show ?thesis
    using True unfolding base_case_bound_impl_def base_case_bound_def by (simp add: Let_def)
next
  case False
  then have k: "k < length (base_case_order x B)"
    by simp
  let ?ys = "base_case_order_impl vs es x B"
  have len_y: "k < length ?ys"
    using k base_case_order_impl_length_eq[OF vs es, of x B] by simp
  have y_mem: "?ys ! k \<in> set ?ys"
    using len_y by simp
  have exec_eq: "exec_dist vs es w s (?ys ! k) = dist s (?ys ! k)"
    using exec_dist_eq_dist_on_base_case_order_impl[OF vs es y_mem] .
  have dist_eq: "dist s ((base_case_order x B) ! k) = dist s (?ys ! k)"
    by (rule base_case_order_impl_kth_dist_eq[OF vs es k])
  show ?thesis
    using False len_y exec_eq dist_eq
    unfolding base_case_bound_impl_def base_case_bound_def
    by (simp add: Let_def)
qed

lemma base_case_vertices_impl_success:
  assumes vs: "set vs = V"
    and es: "set es = E"
    and len: "length (base_case_order_impl vs es x B) \<le> k"
  shows "base_case_vertices_impl vs es k x B = bound_tree {x} B"
  using len base_case_order_impl_set[OF vs es, of x B]
  unfolding base_case_vertices_impl_def by (simp add: Let_def)

lemma base_case_vertices_impl_partial:
  assumes vs: "set vs = V"
    and es: "set es = E"
    and len: "k < length (base_case_order_impl vs es x B)"
  shows "base_case_vertices_impl vs es k x B =
    bound_tree {x} (Fin (exec_dist vs es w s ((base_case_order_impl vs es x B) ! k)))"
proof -
  let ?xs = "base_case_order_impl vs es x B"
  let ?b = "dist s (?xs ! k)"
  have set_xs: "set ?xs = bound_tree {x} B"
    using base_case_order_impl_set[OF vs es, of x B] .
  have sorted: "sorted_wrt (\<lambda>u v. dist s u \<le> dist s v) ?xs"
    using base_case_order_impl_sorted[OF vs es, of x B] .
  have kth_in: "?xs ! k \<in> bound_tree {x} B"
    using len set_xs nth_mem by metis
  have kth_exec: "exec_dist vs es w s (?xs ! k) = ?b"
    using exec_dist_eq_dist_on_base_case_order_impl[OF vs es] len nth_mem by blast
  have exec_on_xs: "\<And>v. v \<in> set ?xs \<Longrightarrow> exec_dist vs es w s v = dist s v"
    by (rule exec_dist_eq_dist_on_base_case_order_impl[OF vs es])
  have exec_on_take: "\<And>v. v \<in> set (take (Suc k) ?xs) \<Longrightarrow>
      exec_dist vs es w s v = dist s v"
  proof -
    fix v
    assume "v \<in> set (take (Suc k) ?xs)"
    then have "v \<in> set ?xs"
      by (rule in_set_takeD)
    then show "exec_dist vs es w s v = dist s v"
      by (rule exec_on_xs)
  qed
  have vertices_eq:
    "base_case_vertices_impl vs es k x B =
      {v \<in> set (take (Suc k) ?xs). dist s v < ?b}"
    using len kth_exec exec_on_take
    unfolding base_case_vertices_impl_def by (auto simp: Let_def)
  have "base_case_vertices_impl vs es k x B = bound_tree {x} (Fin ?b)"
  proof
    show "base_case_vertices_impl vs es k x B \<subseteq> bound_tree {x} (Fin ?b)"
    proof
      fix v
      assume "v \<in> base_case_vertices_impl vs es k x B"
      then have v: "v \<in> set (take (Suc k) ?xs)" "dist s v < ?b"
        using vertices_eq by auto
      have "v \<in> set ?xs"
        using v(1) by (meson in_set_takeD)
      then have "v \<in> bound_tree {x} B"
        using set_xs by simp
      then show "v \<in> bound_tree {x} (Fin ?b)"
        using v(2) unfolding bound_tree_def by auto
    qed
  next
    show "bound_tree {x} (Fin ?b) \<subseteq> base_case_vertices_impl vs es k x B"
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
      then show "v \<in> base_case_vertices_impl vs es k x B"
        using vertices_eq lt by simp
    qed
  qed
  then show ?thesis
    using kth_exec by simp
qed

lemma base_case_vertices_impl_eq:
  assumes vs: "set vs = V"
    and es: "set es = E"
  shows "base_case_vertices_impl vs es k x B = base_case_vertices k x B"
proof (cases "length (base_case_order x B) \<le> k")
  case True
  then have len_impl: "length (base_case_order_impl vs es x B) \<le> k"
    using base_case_order_impl_length_eq[OF vs es, of x B] by simp
  show ?thesis
    using base_case_success[OF True] base_case_vertices_impl_success[OF vs es len_impl] by simp
next
  case False
  then have k: "k < length (base_case_order x B)"
    by simp
  have len_impl: "k < length (base_case_order_impl vs es x B)"
    using k base_case_order_impl_length_eq[OF vs es, of x B] by simp
  let ?ys = "base_case_order_impl vs es x B"
  have y_mem: "?ys ! k \<in> set ?ys"
    using len_impl by simp
  have exec_eq: "exec_dist vs es w s (?ys ! k) = dist s (?ys ! k)"
    using exec_dist_eq_dist_on_base_case_order_impl[OF vs es y_mem] .
  have dist_eq: "dist s ((base_case_order x B) ! k) = dist s (?ys ! k)"
    by (rule base_case_order_impl_kth_dist_eq[OF vs es k])
  have impl: "base_case_vertices_impl vs es k x B =
      bound_tree {x} (Fin (exec_dist vs es w s (?ys ! k)))"
    by (rule base_case_vertices_impl_partial[OF vs es len_impl])
  have sem: "base_case_vertices k x B =
      bound_tree {x} (Fin (dist s ((base_case_order x B) ! k)))"
    by (rule base_case_partial[OF k])
  show ?thesis
    using impl sem exec_eq dist_eq by simp
qed

lemma base_case_result_impl_eq:
  assumes vs: "set vs = V"
    and es: "set es = E"
  shows "base_case_result_impl vs es k x B = base_case_result k x B"
  using base_case_bound_impl_eq[OF vs es, of k x B]
    base_case_vertices_impl_eq[OF vs es, of k x B]
  unfolding base_case_result_impl_def base_case_result_def by simp

lemma base_case_result_impl_bmssp_post:
  assumes vs: "set vs = V"
    and es: "set es = E"
    and S: "S = {x}"
  shows "case base_case_result_impl vs es k x B of (B', U) \<Rightarrow>
    bmssp_post d S B (\<lambda>v. if v \<in> U then dist s v else d v) B' U"
  using base_case_result_bmssp_post[OF S, where k=k and B=B and d=d]
    base_case_result_impl_eq[OF vs es, of k x B]
  by simp

lemma base_case_order_impl_eq_exec_base_case_order:
  "base_case_order_impl vs es x B = exec_base_case_order w s vs es x B"
  unfolding base_case_order_impl_def exec_base_case_order_def by simp

lemma base_case_vertices_impl_eq_exec_base_case_vertices:
  "base_case_vertices_impl vs es k x B = exec_base_case_vertices w s vs es k x B"
  unfolding base_case_vertices_impl_def exec_base_case_vertices_def
    base_case_order_impl_eq_exec_base_case_order by simp

lemma base_case_bound_impl_eq_exec_base_case_bound:
  "base_case_bound_impl vs es k x B = exec_base_case_bound w s vs es k x B"
  unfolding base_case_bound_impl_def exec_base_case_bound_def
    base_case_order_impl_eq_exec_base_case_order by simp

lemma base_case_result_impl_eq_exec_base_case_result:
  "base_case_result_impl vs es k x B = exec_base_case_result w s vs es k x B"
  unfolding base_case_result_impl_def exec_base_case_result_def
    base_case_bound_impl_eq_exec_base_case_bound
    base_case_vertices_impl_eq_exec_base_case_vertices by simp

lemma exec_base_case_bound_eq:
  assumes vs: "set vs = V"
    and es: "set es = E"
  shows "exec_base_case_bound w s vs es k x B = base_case_bound k x B"
  using base_case_bound_impl_eq[OF vs es, of k x B]
  unfolding base_case_bound_impl_eq_exec_base_case_bound .

lemma exec_base_case_vertices_eq:
  assumes vs: "set vs = V"
    and es: "set es = E"
  shows "exec_base_case_vertices w s vs es k x B = base_case_vertices k x B"
  using base_case_vertices_impl_eq[OF vs es, of k x B]
  unfolding base_case_vertices_impl_eq_exec_base_case_vertices .

lemma exec_base_case_result_eq:
  assumes vs: "set vs = V"
    and es: "set es = E"
  shows "exec_base_case_result w s vs es k x B = base_case_result k x B"
  using base_case_result_impl_eq[OF vs es, of k x B]
  unfolding base_case_result_impl_eq_exec_base_case_result .

lemmas base_case_bound_exec_code [code] = exec_base_case_bound_eq[symmetric]
lemmas base_case_vertices_exec_code [code] = exec_base_case_vertices_eq[symmetric]
lemmas base_case_result_exec_code [code] = exec_base_case_result_eq[symmetric]

end

declare finite_weighted_digraph.base_case_bound_exec_code [code]
declare finite_weighted_digraph.base_case_vertices_exec_code [code]
declare finite_weighted_digraph.base_case_result_exec_code [code]

definition example_edges :: "(nat \<times> nat) list" where
  "example_edges = map (\<lambda>(u, v, c). (u, v)) example_graph"

definition example_vertices :: "nat list" where
  "example_vertices = bmssp_vertices example_graph 0"

definition example_V :: "nat set" where
  "example_V = set example_vertices"

definition example_E :: "(nat \<times> nat) set" where
  "example_E = set example_edges"

definition example_weight :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "example_weight u v =
     (case map_of (map (\<lambda>(a, b, c). ((a, b), real c)) example_graph) (u, v) of
        None \<Rightarrow> 0
      | Some c \<Rightarrow> c)"

lemma example_vertices_set [simp]: "set example_vertices = example_V"
  unfolding example_vertices_def example_V_def by simp

lemma example_edges_set [simp]: "set example_edges = example_E"
  unfolding example_edges_def example_E_def by simp

lemma example_finite_weighted_digraph:
  "finite_weighted_digraph example_V example_E example_weight 0"
  unfolding finite_weighted_digraph_def
    example_V_def example_E_def example_vertices_def example_edges_def
    bmssp_vertices_def example_graph_def example_weight_def
  by (auto split: prod.splits option.splits)

interpretation example_fw: finite_weighted_digraph example_V example_E example_weight 0
  by (rule example_finite_weighted_digraph)

lemma example_exec_simple_walk_0:
  "[0] \<in> set (exec_simple_walks_betw example_vertices example_edges 0 0)"
  by eval

lemma example_exec_simple_walk_1:
  "[0, 1] \<in> set (exec_simple_walks_betw example_vertices example_edges 0 1)"
  by eval

lemma example_exec_simple_walk_2:
  "[0, 1, 2] \<in> set (exec_simple_walks_betw example_vertices example_edges 0 2)"
  by eval

lemma example_exec_simple_walk_3:
  "[0, 1, 2, 3] \<in> set (exec_simple_walks_betw example_vertices example_edges 0 3)"
  by eval

lemma example_exec_simple_walk_4:
  "[0, 4] \<in> set (exec_simple_walks_betw example_vertices example_edges 0 4)"
  by eval

lemma example_exec_reachable_if_in_V:
  assumes "v \<in> example_V"
  shows "exec_reachable example_vertices example_edges 0 v"
proof -
  have "v = 0 \<or> v = 1 \<or> v = 2 \<or> v = 3 \<or> v = 4"
    using assms
    unfolding example_V_def example_vertices_def bmssp_vertices_def example_graph_def
    by auto
  then show ?thesis
    using example_exec_simple_walk_0 example_exec_simple_walk_1
      example_exec_simple_walk_2 example_exec_simple_walk_3
      example_exec_simple_walk_4
    unfolding exec_reachable_def by auto
qed

lemma example_dist_inj_on_V:
  "inj_on (finite_weighted_digraph.dist example_V example_E example_weight 0) example_V"
proof (rule inj_onI)
  fix u v
  assume uV: "u \<in> example_V" and vV: "v \<in> example_V"
    and dist_eq:
      "finite_weighted_digraph.dist example_V example_E example_weight 0 u =
       finite_weighted_digraph.dist example_V example_E example_weight 0 v"
  have reach_u: "finite_weighted_digraph.reachable example_V example_E 0 u"
    using example_exec_reachable_if_in_V[OF uV]
      example_fw.exec_reachable_iff_reachable[of example_vertices example_edges 0 u]
    by simp
  have reach_v: "finite_weighted_digraph.reachable example_V example_E 0 v"
    using example_exec_reachable_if_in_V[OF vV]
      example_fw.exec_reachable_iff_reachable[of example_vertices example_edges 0 v]
    by simp
  have u_eq:
    "exec_dist example_vertices example_edges example_weight 0 u =
     finite_weighted_digraph.dist example_V example_E example_weight 0 u"
    using example_fw.exec_dist_eq_dist[OF example_vertices_set example_edges_set reach_u] .
  have v_eq:
    "exec_dist example_vertices example_edges example_weight 0 v =
     finite_weighted_digraph.dist example_V example_E example_weight 0 v"
    using example_fw.exec_dist_eq_dist[OF example_vertices_set example_edges_set reach_v] .
  have exec_inj:
    "inj_on (exec_dist example_vertices example_edges example_weight 0) example_V"
    by eval
  show "u = v"
    using inj_onD[OF exec_inj _ _] uV vV dist_eq u_eq v_eq by metis
qed

lemma example_base_case_order_code [code_unfold]:
  "finite_weighted_digraph.base_case_order example_V example_E example_weight 0 x B =
    exec_base_case_order example_weight 0 example_vertices example_edges x B"
proof -
  have tree_subset:
    "finite_weighted_digraph.bound_tree example_V example_E example_weight 0 {x} B \<subseteq>
      example_V"
    unfolding example_fw.bound_tree_def by auto
  have inj:
    "inj_on (finite_weighted_digraph.dist example_V example_E example_weight 0)
      (finite_weighted_digraph.bound_tree example_V example_E example_weight 0 {x} B)"
    by (rule inj_on_subset[OF example_dist_inj_on_V tree_subset])
  have "finite_weighted_digraph.base_case_order example_V example_E example_weight 0 x B =
      finite_weighted_digraph.base_case_order_impl example_weight 0
        example_vertices example_edges x B"
    using example_fw.base_case_order_impl_eq_if_inj
      [OF example_vertices_set example_edges_set inj] .
  then show ?thesis
    using example_fw.base_case_order_impl_eq_exec_base_case_order
      [of example_vertices example_edges x B]
    by simp
qed

lemma example_base_case_vertices_code [code_unfold]:
  "finite_weighted_digraph.base_case_vertices example_V example_E example_weight 0 k x B =
    exec_base_case_vertices example_weight 0 example_vertices example_edges k x B"
  using example_fw.exec_base_case_vertices_eq[of example_vertices example_edges k x B]
  by simp

lemma example_base_case_result_code [code_unfold]:
  "finite_weighted_digraph.base_case_result example_V example_E example_weight 0 k x B =
    exec_base_case_result example_weight 0 example_vertices example_edges k x B"
  using example_fw.exec_base_case_result_eq[of example_vertices example_edges k x B]
  by simp

value "exec_closest_vertices
  (bmssp_vertices example_graph 0) example_edges example_weight 0
  (bmssp_vertices example_graph 0)"

value "exec_base_case_order
  example_weight 0 (bmssp_vertices example_graph 0) example_edges 0 (Fin 100)"

value "exec_base_case_result
  example_weight 0 (bmssp_vertices example_graph 0) example_edges 3 0 (Fin 100) ::
  bound \<times> nat set"

value "finite_weighted_digraph.base_case_vertices
  example_V example_E example_weight 0 3 0 (Fin 100) :: nat set"

value "finite_weighted_digraph.base_case_order
  example_V example_E example_weight 0 0 (Fin 100)"

value "finite_weighted_digraph.base_case_result
  example_V example_E example_weight 0 3 0 (Fin 100) :: bound \<times> nat set"

end
