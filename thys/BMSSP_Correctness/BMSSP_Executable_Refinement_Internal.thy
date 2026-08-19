theory BMSSP_Executable_Refinement_Internal
  imports BMSSP_Executable_Base_Case BMSSP_Top_Level_Bounds
begin

section \<open>Executable Graph Refinement Bridge\<close>

text \<open>
  This theory starts the refinement bridge between the concrete executable
  entry point @{const bmssp_distances} and the locale-based BMSSP correctness
  stack.  The executable graph is a list of natural-number edge triples; the
  abstract semantics expects a finite weighted digraph locale.  The definitions
  below name the carrier, edge set, and weight function induced by the list
  representation, then package the assumptions needed before the executable
  loop can be related to the direct-insert BMSSP relation.
\<close>

fun nat_edge_source :: "nat_edge \<Rightarrow> nat" where
  "nat_edge_source (u, v, w) = u"

fun nat_edge_target :: "nat_edge \<Rightarrow> nat" where
  "nat_edge_target (u, v, w) = v"

fun nat_edge_weight :: "nat_edge \<Rightarrow> nat" where
  "nat_edge_weight (u, v, w) = w"

definition nat_graph_edge_list :: "nat_graph \<Rightarrow> (nat \<times> nat) list" where
  "nat_graph_edge_list G = map (\<lambda>e. (nat_edge_source e, nat_edge_target e)) G"

definition nat_graph_edges :: "nat_graph \<Rightarrow> (nat \<times> nat) set" where
  "nat_graph_edges G = set (nat_graph_edge_list G)"

definition nat_graph_vertices :: "nat_graph \<Rightarrow> nat set" where
  "nat_graph_vertices G = set (map nat_edge_source G) \<union> set (map nat_edge_target G)"

definition nat_graph_vertex_list :: "nat_graph \<Rightarrow> nat list" where
  "nat_graph_vertex_list G =
     sort (remdups (map nat_edge_source G @ map nat_edge_target G))"

definition nat_graph_weight :: "nat_graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "nat_graph_weight G u v =
     (case map_of
        (map (\<lambda>e. ((nat_edge_source e, nat_edge_target e),
                 real (nat_edge_weight e))) G) (u, v) of
        None \<Rightarrow> 0
      | Some c \<Rightarrow> c)"

definition nat_graph_total_weight :: "nat_graph \<Rightarrow> nat" where
  "nat_graph_total_weight G = sum_list (map nat_edge_weight G)"

definition nat_graph_well_formed :: "nat_graph \<Rightarrow> bool" where
  "nat_graph_well_formed G \<longleftrightarrow>
     distinct (nat_graph_edge_list G) \<and>
     nat_graph_total_weight G < bmssp_infinity"

lemma nat_graph_well_formed_distinct_edge_list:
  assumes "nat_graph_well_formed G"
  shows "distinct (nat_graph_edge_list G)"
  using assms unfolding nat_graph_well_formed_def by blast

definition nat_graph_reachable :: "nat_graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "nat_graph_reachable G a b \<longleftrightarrow>
     finite_weighted_digraph.reachable
       (nat_graph_vertices G) (nat_graph_edges G) a b"

definition nat_graph_dist :: "nat_graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "nat_graph_dist G a b =
     finite_weighted_digraph.dist
       (nat_graph_vertices G) (nat_graph_edges G) (nat_graph_weight G) a b"

definition executable_label_of :: "nat_dist \<Rightarrow> nat \<Rightarrow> real" where
  "executable_label_of ds v =
     (case bmssp_lookup_dist ds v of
        None \<Rightarrow> bmssp_bound
      | Some d \<Rightarrow> real d)"

lemma bmssp_lookup_dist_mem_key:
  assumes "bmssp_lookup_dist ds v = Some d"
  shows "v \<in> set (map fst ds)"
  using assms
proof (induction ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ds)
  obtain x e where p: "p = (x, e)"
    by (cases p)
  show ?case
  proof (cases "v = x")
    case True
    then show ?thesis
      using p by simp
  next
    case False
    then have "bmssp_lookup_dist ds v = Some d"
      using Cons.prems p by simp
    then have "v \<in> set (map fst ds)"
      by (rule Cons.IH)
    then show ?thesis
      using p by simp
  qed
qed

lemma bmssp_lookup_dist_Some_pair_mem:
  assumes "bmssp_lookup_dist ds v = Some d"
  shows "(v, d) \<in> set ds"
  using assms
proof (induction ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ds)
  obtain x e where p: "p = (x, e)"
    by (cases p)
  show ?case
  proof (cases "v = x")
    case True
    then show ?thesis
      using Cons.prems unfolding p by simp
  next
    case False
    then have "bmssp_lookup_dist ds v = Some d"
      using Cons.prems unfolding p by simp
    then have "(v, d) \<in> set ds"
      by (rule Cons.IH)
    then show ?thesis
      unfolding p by simp
  qed
qed

lemma bmssp_lookup_dist_Some_if_distinct_mem:
  assumes distinct: "distinct (map fst ds)"
    and mem: "(v, d) \<in> set ds"
  shows "bmssp_lookup_dist ds v = Some d"
  using distinct mem
proof (induction ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ds)
  obtain x e where p: "p = (x, e)"
    by (cases p)
  show ?case
  proof (cases "v = x")
    case True
    have d_eq: "d = e"
    proof -
      have mem_cases: "(v, d) = p \<or> (v, d) \<in> set ds"
        using Cons.prems p by simp
      then show ?thesis
      proof
        assume "(v, d) = p"
        then show ?thesis
          using True p by simp
      next
        assume "(v, d) \<in> set ds"
        then have "x \<in> set (map fst ds)"
          using True by force
        then show ?thesis
          using Cons.prems p by simp
      qed
    qed
    then show ?thesis
      using True p by simp
  next
    case False
    then have mem_tail: "(v, d) \<in> set ds"
      using Cons.prems p by auto
    have distinct_tail: "distinct (map fst ds)"
      using Cons.prems p by simp
    show ?thesis
      using False p Cons.IH[OF distinct_tail mem_tail] by simp
  qed
qed

lemma bmssp_lookup_dist_None_if_distinct_not_mem:
  assumes distinct: "distinct (map fst ds)"
    and not_mem: "v \<notin> set (map fst ds)"
  shows "bmssp_lookup_dist ds v = None"
  using distinct not_mem by (induction ds) auto

lemma bmssp_set_dist_keys:
  "set (map fst (bmssp_set_dist v d ds)) = insert v (set (map fst ds))"
proof (induction ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ds)
  obtain x e where p: "p = (x, e)"
    by (cases p)
  show ?case
  proof (cases "v = x")
    case True
    then show ?thesis
      unfolding p by simp
  next
    case False
    then show ?thesis
      using Cons.IH unfolding p by auto
  qed
qed

lemma bmssp_set_dist_fst_image [simp]:
  "fst ` set (bmssp_set_dist v d ds) = insert v (fst ` set ds)"
  using bmssp_set_dist_keys[of v d ds] by simp

lemma bmssp_set_dist_preserves_distinct:
  assumes "distinct (map fst ds)"
  shows "distinct (map fst (bmssp_set_dist v d ds))"
  using assms
proof (induction ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ds)
  obtain x e where p: "p = (x, e)"
    by (cases p)
  have distinct_tail: "distinct (map fst ds)"
    using Cons.prems p by simp
  show ?case
  proof (cases "v = x")
    case True
    then show ?thesis
      using Cons.prems p by simp
  next
    case False
    have x_not_tail: "x \<notin> set (map fst ds)"
      using Cons.prems p by simp
    have x_not_updated: "x \<notin> set (map fst (bmssp_set_dist v d ds))"
      using x_not_tail False unfolding bmssp_set_dist_keys by simp
    have updated_distinct: "distinct (map fst (bmssp_set_dist v d ds))"
      by (rule Cons.IH[OF distinct_tail])
    show ?thesis
      using False p x_not_updated updated_distinct by simp
  qed
qed

lemma bmssp_lookup_dist_set_dist_other:
  assumes "v \<noteq> x"
  shows "bmssp_lookup_dist (bmssp_set_dist x dx ds) v =
    bmssp_lookup_dist ds v"
  using assms
proof (induction ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ds)
  obtain y e where p: "p = (y, e)"
    by (cases p)
  then show ?case
    using Cons by auto
qed

lemma bmssp_lookup_dist_set_dist_same:
  "bmssp_lookup_dist (bmssp_set_dist x dx ds) x = Some dx"
  by (induction ds) auto

lemma bmssp_normalize_dist_key_set [simp]:
  "set (map fst (bmssp_normalize_dist ds)) = set (map fst ds)"
  unfolding bmssp_normalize_dist_def by (metis set_map set_sort)

lemma bmssp_normalize_dist_fst_image [simp]:
  "fst ` set (bmssp_normalize_dist ds) = fst ` set ds"
  unfolding bmssp_normalize_dist_def by simp

lemma bmssp_lookup_dist_None_iff_not_key:
  assumes distinct: "distinct (map fst ds)"
  shows "bmssp_lookup_dist ds v = None \<longleftrightarrow> v \<notin> set (map fst ds)"
proof
  assume none: "bmssp_lookup_dist ds v = None"
  show "v \<notin> set (map fst ds)"
  proof
    assume "v \<in> set (map fst ds)"
    then obtain d where "(v, d) \<in> set ds"
      by force
    then have "bmssp_lookup_dist ds v = Some d"
      by (rule bmssp_lookup_dist_Some_if_distinct_mem[OF distinct])
    then show False
      using none by simp
  qed
next
  assume "v \<notin> set (map fst ds)"
  then show "bmssp_lookup_dist ds v = None"
    by (rule bmssp_lookup_dist_None_if_distinct_not_mem[OF distinct])
qed

lemma bmssp_lookup_dist_normalize_dist:
  assumes distinct: "distinct (map fst ds)"
  shows "bmssp_lookup_dist (bmssp_normalize_dist ds) v =
    bmssp_lookup_dist ds v"
proof (cases "bmssp_lookup_dist ds v")
  case None
  have distinct_norm:
    "distinct (map fst (bmssp_normalize_dist ds))"
    using distinct unfolding bmssp_normalize_dist_def
    by (rule distinct_map_fst_sort_key)
  have "v \<notin> set (map fst (bmssp_normalize_dist ds))"
    using None distinct
    unfolding bmssp_lookup_dist_None_iff_not_key[OF distinct] by simp
  then show ?thesis
    using None bmssp_lookup_dist_None_if_distinct_not_mem[OF distinct_norm]
    by simp
next
  case (Some d)
  have mem: "(v, d) \<in> set (bmssp_normalize_dist ds)"
    using bmssp_lookup_dist_Some_pair_mem[OF Some]
    unfolding bmssp_normalize_dist_def by simp
  have distinct_norm:
    "distinct (map fst (bmssp_normalize_dist ds))"
    using distinct unfolding bmssp_normalize_dist_def
    by (rule distinct_map_fst_sort_key)
  have "bmssp_lookup_dist (bmssp_normalize_dist ds) v = Some d"
    by (rule bmssp_lookup_dist_Some_if_distinct_mem[OF distinct_norm mem])
  then show ?thesis
    using Some by simp
qed

lemma bmssp_relax_edges_preserves_distinct_dist:
  assumes distinct: "distinct (map fst ds)"
  shows "distinct (map fst (snd (bmssp_relax_edges G settled u du ds)))"
  using distinct
proof (induction G arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons e es)
  obtain a b w where e: "e = (a, b, w)"
    by (cases e)
  obtain updates ds1 where rec:
    "bmssp_relax_edges es settled u du ds = (updates, ds1)"
    by force
  have distinct_ds1: "distinct (map fst ds1)"
    using Cons.IH[OF Cons.prems] rec by simp
  show ?case
  proof (cases "a = u \<and> b \<notin> set settled")
    case False
    then show ?thesis
      using distinct_ds1 rec unfolding e
      by (auto simp: Let_def split: option.splits if_splits)
  next
    case True
    note active = True
    show ?thesis
    proof (cases "bmssp_lookup_dist ds1 b")
      case None
      then show ?thesis
        using active rec bmssp_set_dist_preserves_distinct[OF distinct_ds1]
        unfolding e by (simp add: Let_def)
    next
      case (Some old)
      show ?thesis
      proof (cases "du + w < old")
        case True
        then show ?thesis
          using active rec Some
            bmssp_set_dist_preserves_distinct[OF distinct_ds1]
          unfolding e by (simp add: Let_def)
      next
        case False
        then show ?thesis
          using active rec Some distinct_ds1 unfolding e by (simp add: Let_def)
      qed
    qed
  qed
qed

lemma bmssp_relax_vertices_preserves_distinct_dist:
  assumes distinct: "distinct (map fst ds)"
  shows "distinct (map fst (snd (bmssp_relax_vertices G settled xs ds)))"
  using distinct
proof (induction xs arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons u us)
  show ?case
  proof (cases "bmssp_lookup_dist ds u")
    case None
    then show ?thesis
      using Cons.IH[OF Cons.prems] by simp
  next
    case (Some du)
    obtain updates ds1 where edge_rec:
      "bmssp_relax_edges G settled u du ds = (updates, ds1)"
      by force
    have distinct_ds1: "distinct (map fst ds1)"
      using bmssp_relax_edges_preserves_distinct_dist[OF Cons.prems,
          of G settled u du] edge_rec by simp
    obtain updates_us ds2 where vertices_rec:
      "bmssp_relax_vertices G settled us ds1 = (updates_us, ds2)"
      by force
    have distinct_ds2: "distinct (map fst ds2)"
      using Cons.IH[OF distinct_ds1] vertices_rec by simp
    show ?thesis
      using Some edge_rec vertices_rec distinct_ds2 by simp
  qed
qed

lemma bmssp_relax_edges_dist_keys_subset:
  assumes keys: "set (map fst ds) \<subseteq> set vertices"
    and uV: "u \<in> set vertices"
    and edge_targets:
      "\<And>a b w. (a, b, w) \<in> set G \<Longrightarrow> b \<in> set vertices"
  shows "set (map fst (snd (bmssp_relax_edges G settled u du ds)))
    \<subseteq> set vertices"
  using keys edge_targets
proof (induction G arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons e es)
  obtain a b w where e: "e = (a, b, w)"
    by (cases e)
  obtain updates ds1 where rec:
    "bmssp_relax_edges es settled u du ds = (updates, ds1)"
    by force
  have tail_subset: "set (map fst ds1) \<subseteq> set vertices"
  proof -
    have targets_tail:
      "\<And>x y z. (x, y, z) \<in> set es \<Longrightarrow> y \<in> set vertices"
    proof -
      fix x y z
      assume xyz: "(x, y, z) \<in> set es"
      have "(x, y, z) \<in> set (e # es)"
        using xyz by simp
      then show "y \<in> set vertices"
        by (rule Cons.prems(2))
    qed
    show ?thesis
      using Cons.IH[OF Cons.prems(1) targets_tail] rec by simp
  qed
  have bV: "b \<in> set vertices"
    using Cons.prems(2)[of a b w] unfolding e by simp
  show ?case
  proof (cases "a = u \<and> b \<notin> set settled")
    case False
    then show ?thesis
      using tail_subset rec unfolding e
      by (auto simp: Let_def split: option.splits if_splits)
  next
    case True
    note active = True
    let ?nd = "du + w"
    show ?thesis
    proof (cases "bmssp_lookup_dist ds1 b")
      case None
      then show ?thesis
        using active rec tail_subset bV
        unfolding e by (simp add: Let_def bmssp_set_dist_keys)
    next
      case (Some old)
      show ?thesis
      proof (cases "?nd < old")
        case True
        then show ?thesis
          using active rec Some tail_subset bV
          unfolding e by (simp add: Let_def bmssp_set_dist_keys)
      next
        case False
        then show ?thesis
          using active rec Some tail_subset unfolding e by (simp add: Let_def)
      qed
    qed
  qed
qed

lemma bmssp_relax_vertices_dist_keys_subset:
  assumes keys: "set (map fst ds) \<subseteq> set vertices"
    and xs_subset: "set xs \<subseteq> set vertices"
    and edge_targets:
      "\<And>a b w. (a, b, w) \<in> set G \<Longrightarrow> b \<in> set vertices"
  shows "set (map fst (snd (bmssp_relax_vertices G settled xs ds)))
    \<subseteq> set vertices"
  using keys xs_subset
proof (induction xs arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons u us)
  have uV: "u \<in> set vertices"
    using Cons.prems by simp
  have us_subset: "set us \<subseteq> set vertices"
    using Cons.prems by simp
  show ?case
  proof (cases "bmssp_lookup_dist ds u")
    case None
    then show ?thesis
      using Cons.IH[OF Cons.prems(1) us_subset] by simp
  next
    case (Some du)
    obtain updates ds1 where edge_rec:
      "bmssp_relax_edges G settled u du ds = (updates, ds1)"
      by force
    have keys1: "set (map fst ds1) \<subseteq> set vertices"
    proof -
      have "set (map fst (snd (bmssp_relax_edges G settled u du ds)))
          \<subseteq> set vertices"
        by (rule bmssp_relax_edges_dist_keys_subset
            [OF Cons.prems(1) uV edge_targets])
      then show ?thesis
        using edge_rec by simp
    qed
    obtain updates_us ds2 where vertices_rec:
      "bmssp_relax_vertices G settled us ds1 = (updates_us, ds2)"
      by force
    have keys2: "set (map fst ds2) \<subseteq> set vertices"
      using Cons.IH[OF keys1 us_subset] vertices_rec by simp
    show ?thesis
      using Some edge_rec vertices_rec keys2 by simp
  qed
qed

definition real_label_integral_on :: "nat set \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> bool" where
  "real_label_integral_on U d \<longleftrightarrow>
     (\<forall>v\<in>U. real (nat (floor (d v))) = d v)"

definition encode_dist_assoc_list :: "nat list \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat_dist" where
  "encode_dist_assoc_list xs d =
     map (\<lambda>v. (v, nat (floor (d v)))) (sort (remdups xs))"

lemma encode_dist_assoc_list_memI:
  assumes "v \<in> set xs"
  shows "\<exists>d. (v, d) \<in> set (encode_dist_assoc_list xs f)"
  using assms unfolding encode_dist_assoc_list_def by auto

lemma encode_dist_assoc_list_memD:
  assumes "(v, d) \<in> set (encode_dist_assoc_list xs f)"
  shows "v \<in> set xs"
  using assms unfolding encode_dist_assoc_list_def by auto

lemma sort_remdups_eq_if_set_eq:
  assumes "set xs = set ys"
  shows "sort (remdups xs) = sort (remdups ys)"
proof -
  have set_eq: "set (sort (remdups xs)) = set (sort (remdups ys))"
    using assms by simp
  have distinct_x: "distinct (sort (remdups xs))"
    by simp
  have distinct_y: "distinct (sort (remdups ys))"
    by simp
  have sorted_x: "sorted (sort (remdups xs))"
    by simp
  have sorted_y: "sorted (sort (remdups ys))"
    by simp
  have mset_eq:
    "mset (sort (remdups xs)) = mset (sort (remdups ys))"
    using distinct_x distinct_y set_eq
    by (metis set_eq_iff_mset_eq_distinct)
  have "sort (sort (remdups ys)) = sort (remdups xs)"
  proof (rule properties_for_sort)
    show "mset (sort (remdups xs)) = mset (sort (remdups ys))"
      by (rule mset_eq)
    show "sorted (sort (remdups xs))"
      by (rule sorted_x)
  qed
  moreover have "sort (sort (remdups ys)) = sort (remdups ys)"
  proof (rule sort_key_id_if_sorted)
    show "sorted (map (\<lambda>x. x) (sort (remdups ys)))"
      using sorted_y by simp
  qed
  ultimately show ?thesis
    by simp
qed

lemma encode_dist_assoc_list_cong_set:
  assumes "set xs = set ys"
  shows "encode_dist_assoc_list xs f = encode_dist_assoc_list ys f"
  unfolding encode_dist_assoc_list_def
  using sort_remdups_eq_if_set_eq[OF assms] by simp

lemma encode_dist_assoc_list_cong_set_floor:
  assumes set_eq: "set xs = set ys"
    and floors:
      "\<And>v. v \<in> set xs \<Longrightarrow>
        nat (floor (f v)) = nat (floor (g v))"
  shows "encode_dist_assoc_list xs f = encode_dist_assoc_list ys g"
proof -
  have order_eq: "sort (remdups xs) = sort (remdups ys)"
    by (rule sort_remdups_eq_if_set_eq[OF set_eq])
  have map_eq:
    "map (\<lambda>v. (v, nat (floor (f v)))) (sort (remdups xs)) =
      map (\<lambda>v. (v, nat (floor (g v)))) (sort (remdups xs))"
    by (rule map_cong[OF refl]) (use floors in auto)
  show ?thesis
    unfolding encode_dist_assoc_list_def using order_eq map_eq by simp
qed

lemma encode_dist_assoc_list_partition_key:
  "encode_dist_assoc_list xs (\<lambda>v. bmssp_partition_key v (f v)) =
    map (\<lambda>v. (v, f v)) (sort (remdups xs))"
  unfolding encode_dist_assoc_list_def
  by (simp add: bmssp_partition_key_floor)

lemma map_fst_pair_map [simp]:
  "map fst (map (\<lambda>x. (x, f x)) xs) = xs"
  by (induction xs) simp_all

lemma bmssp_normalize_dist_encode:
  assumes distinct: "distinct (map fst ds)"
  shows "bmssp_normalize_dist ds =
    encode_dist_assoc_list (map fst ds) (executable_label_of ds)"
proof -
  let ?lhs = "bmssp_normalize_dist ds"
  let ?rhs = "encode_dist_assoc_list (map fst ds) (executable_label_of ds)"
  have lhs_sorted: "sorted (map fst ?lhs)"
    unfolding bmssp_normalize_dist_def by simp
  have rhs_sorted: "sorted (map fst ?rhs)"
  proof -
    have "map fst ?rhs = sort (remdups (map fst ds))"
      unfolding encode_dist_assoc_list_def by (simp add: o_def)
    then show ?thesis
      by simp
  qed
  have lhs_distinct: "distinct (map fst ?lhs)"
    unfolding bmssp_normalize_dist_def
    by (rule distinct_map_fst_sort_key[OF distinct])
  have rhs_distinct: "distinct (map fst ?rhs)"
  proof -
    have "map fst ?rhs = sort (remdups (map fst ds))"
      unfolding encode_dist_assoc_list_def by (simp add: o_def)
    then show ?thesis
      by simp
  qed
  have lhs_set: "set ?lhs = set ds"
    unfolding bmssp_normalize_dist_def by simp
  have rhs_set: "set ?rhs = set ds"
  proof
    show "set ?rhs \<subseteq> set ds"
    proof
      fix p
      assume p: "p \<in> set ?rhs"
      then obtain v where v:
          "v \<in> set (map fst ds)"
          "p = (v, nat (floor (executable_label_of ds v)))"
        unfolding encode_dist_assoc_list_def by auto
      then obtain d where mem: "(v, d) \<in> set ds"
        by force
      have lookup: "bmssp_lookup_dist ds v = Some d"
        by (rule bmssp_lookup_dist_Some_if_distinct_mem[OF distinct mem])
      then have "nat (floor (executable_label_of ds v)) = d"
        unfolding executable_label_of_def by simp
      then show "p \<in> set ds"
        using v mem by simp
    qed
  next
    show "set ds \<subseteq> set ?rhs"
    proof
      fix p
      assume p: "p \<in> set ds"
      obtain v d where p_eq: "p = (v, d)"
        by (cases p)
      then have mem: "(v, d) \<in> set ds"
        using p by simp
      have lookup: "bmssp_lookup_dist ds v = Some d"
        by (rule bmssp_lookup_dist_Some_if_distinct_mem[OF distinct mem])
      then have encoded_d: "nat (floor (executable_label_of ds v)) = d"
        unfolding executable_label_of_def by simp
      have "v \<in> set (map fst ds)"
        using mem by force
      then have "(v, nat (floor (executable_label_of ds v))) \<in> set ?rhs"
        unfolding encode_dist_assoc_list_def by simp
      then show "p \<in> set ?rhs"
        using p_eq encoded_d by simp
    qed
  qed
  have inj: "inj_on fst (set ?lhs \<union> set ?rhs)"
  proof -
    have "inj_on fst (set ds)"
      using distinct by (simp add: distinct_map inj_on_def)
    then show ?thesis
      using lhs_set rhs_set by simp
  qed
  show ?thesis
    by (rule map_sorted_distinct_set_unique
      [OF inj lhs_sorted lhs_distinct rhs_sorted rhs_distinct])
      (simp add: lhs_set rhs_set)
qed

lemma bmssp_loop_zero_encode:
  assumes "distinct (map fst ds)"
  shows "bmssp_loop 0 G vertices settled ds P =
    encode_dist_assoc_list (map fst ds) (executable_label_of ds)"
  using bmssp_normalize_dist_encode[OF assms] by simp

lemma bmssp_loop_empty_pull_encode:
  assumes pull: "bp_pull bmssp_block_size bmssp_bound P = (S, beta, P1)"
    and empty: "filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices = []"
    and distinct: "distinct (map fst ds)"
  shows "bmssp_loop (Suc fuel) G vertices settled ds P =
    encode_dist_assoc_list (map fst ds) (executable_label_of ds)"
  using pull empty bmssp_normalize_dist_encode[OF distinct] by simp

lemma bmssp_loop_preserves_distinct_output:
  assumes distinct: "distinct (map fst ds)"
  shows "distinct (map fst (bmssp_loop fuel G vertices settled ds P))"
  using distinct
  by (induction fuel arbitrary: settled ds P)
    (auto simp: Let_def bmssp_normalize_dist_def
      split: prod.splits
      intro: distinct_map_fst_sort_key
      dest: bmssp_relax_vertices_preserves_distinct_dist)

lemma bmssp_loop_output_sorted_keys:
  "sorted (map fst (bmssp_loop fuel G vertices settled ds P))"
  by (induction fuel arbitrary: settled ds P)
    (auto simp: Let_def bmssp_normalize_dist_def split: prod.splits)

lemma distinct_sorted_dist_encode:
  assumes distinct: "distinct (map fst ds)"
    and sorted: "sorted (map fst ds)"
  shows "ds = encode_dist_assoc_list (map fst ds) (executable_label_of ds)"
proof -
  have "bmssp_normalize_dist ds = ds"
    using sorted unfolding bmssp_normalize_dist_def
    by (simp add: sort_key_id_if_sorted)
  then show ?thesis
    using bmssp_normalize_dist_encode[OF distinct] by simp
qed

lemma bmssp_loop_output_encode:
  assumes distinct: "distinct (map fst ds)"
  shows "bmssp_loop fuel G vertices settled ds P =
    encode_dist_assoc_list
      (map fst (bmssp_loop fuel G vertices settled ds P))
      (executable_label_of (bmssp_loop fuel G vertices settled ds P))"
proof -
  have distinct_out:
    "distinct (map fst (bmssp_loop fuel G vertices settled ds P))"
    by (rule bmssp_loop_preserves_distinct_output[OF distinct])
  have sorted_out:
    "sorted (map fst (bmssp_loop fuel G vertices settled ds P))"
    by (rule bmssp_loop_output_sorted_keys)
  show ?thesis
    by (rule distinct_sorted_dist_encode[OF distinct_out sorted_out])
qed

lemma bmssp_loop_output_keys_subset_vertices:
  assumes keys: "set (map fst ds) \<subseteq> set vertices"
    and edge_targets:
      "\<And>a b w. (a, b, w) \<in> set G \<Longrightarrow> b \<in> set vertices"
  shows "set (map fst (bmssp_loop fuel G vertices settled ds P))
    \<subseteq> set vertices"
  using keys
proof (induction fuel arbitrary: settled ds P)
  case 0
  then show ?case
    unfolding bmssp_normalize_dist_def by simp
next
  case (Suc fuel)
  obtain S beta P1 where pull:
    "bp_pull bmssp_block_size bmssp_bound P = (S, beta, P1)"
    by (cases "bp_pull bmssp_block_size bmssp_bound P") auto
  let ?pulled = "filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices"
  show ?case
  proof (cases "?pulled = []")
    case True
    then show ?thesis
      using pull Suc.prems unfolding bmssp_normalize_dist_def by simp
  next
    case False
    let ?settled' = "?pulled @ settled"
    obtain updates ds' where relaxed:
      "bmssp_relax_vertices G ?settled' ?pulled ds = (updates, ds')"
      by force
    have pulled_subset: "set ?pulled \<subseteq> set vertices"
      by simp
    have keys_ds': "set (map fst ds') \<subseteq> set vertices"
    proof -
      have "set (map fst
          (snd (bmssp_relax_vertices G ?settled' ?pulled ds)))
          \<subseteq> set vertices"
        by (rule bmssp_relax_vertices_dist_keys_subset
            [OF Suc.prems pulled_subset edge_targets])
      then show ?thesis
        using relaxed by simp
    qed
    have rec:
      "set (map fst
        (bmssp_loop fuel G vertices ?settled' ds'
          (bmssp_apply_updates updates P1))) \<subseteq> set vertices"
      by (rule Suc.IH[OF keys_ds'])
    show ?thesis
      using pull False relaxed rec by (simp add: Let_def)
  qed
qed

lemma executable_label_integral_on_keys:
  assumes distinct: "distinct (map fst ds)"
  shows "real_label_integral_on (set (map fst ds)) (executable_label_of ds)"
  unfolding real_label_integral_on_def
proof
  fix v
  assume "v \<in> set (map fst ds)"
  then obtain d where mem: "(v, d) \<in> set ds"
    by force
  have lookup: "bmssp_lookup_dist ds v = Some d"
    by (rule bmssp_lookup_dist_Some_if_distinct_mem[OF distinct mem])
  then show "real (nat (floor (executable_label_of ds v))) =
    executable_label_of ds v"
    unfolding executable_label_of_def by simp
qed

lemma nat_graph_vertex_list_set [simp]:
  "set (nat_graph_vertex_list G) = nat_graph_vertices G"
  unfolding nat_graph_vertex_list_def nat_graph_vertices_def by simp

lemma nat_graph_edge_list_set [simp]:
  "set (nat_graph_edge_list G) = nat_graph_edges G"
  unfolding nat_graph_edge_list_def nat_graph_edges_def by simp

lemma bmssp_relax_edges_update_edge:
  assumes "(v, b) \<in> set (fst (bmssp_relax_edges G settled u du ds))"
  shows "(u, v) \<in> set (nat_graph_edge_list G)"
  using assms
proof (induction G arbitrary: ds v b)
  case Nil
  then show ?case
    by simp
next
  case (Cons e es)
  obtain a c w where e: "e = (a, c, w)"
    by (cases e)
  obtain updates ds1 where rec:
    "bmssp_relax_edges es settled u du ds = (updates, ds1)"
    by force
  have tail:
    "\<And>v b. (v, b) \<in> set updates \<Longrightarrow>
      (u, v) \<in> set (nat_graph_edge_list es)"
  proof -
    fix v b
    assume update: "(v, b) \<in> set updates"
    have "(v, b) \<in> set (fst (bmssp_relax_edges es settled u du ds))"
      using update rec by simp
    then show "(u, v) \<in> set (nat_graph_edge_list es)"
      by (rule Cons.IH)
  qed
  show ?case
  proof (cases "a = u \<and> c \<notin> set settled")
    case False
    then have "(v, b) \<in> set updates"
      using Cons.prems by (auto simp: e rec split: option.splits if_splits)
    then have "(u, v) \<in> set (nat_graph_edge_list es)"
      by (rule tail)
    then show ?thesis
      unfolding e nat_graph_edge_list_def by simp
  next
    case True
    note active = True
    let ?nd = "du + w"
    show ?thesis
    proof (cases "bmssp_lookup_dist ds1 c")
      case None
      then have update_or_tail:
        "(v, b) = (c, bmssp_partition_key c ?nd) \<or>
          (v, b) \<in> set updates"
        using Cons.prems active unfolding e by (simp add: rec Let_def)
      then show ?thesis
      proof
        assume "(v, b) = (c, bmssp_partition_key c ?nd)"
        then show ?thesis
          using True unfolding e nat_graph_edge_list_def by simp
      next
        assume "(v, b) \<in> set updates"
        then have "(u, v) \<in> set (nat_graph_edge_list es)"
          by (rule tail)
        then show ?thesis
          unfolding e nat_graph_edge_list_def by simp
      qed
    next
      case (Some old)
      show ?thesis
      proof (cases "?nd < old")
        case False
        then have "(v, b) \<in> set updates"
          using Cons.prems active Some unfolding e by (simp add: rec Let_def)
        then have "(u, v) \<in> set (nat_graph_edge_list es)"
          by (rule tail)
        then show ?thesis
          unfolding e nat_graph_edge_list_def by simp
      next
        case True
        then have update_or_tail:
          "(v, b) = (c, bmssp_partition_key c ?nd) \<or>
            (v, b) \<in> set updates"
          using Cons.prems active Some unfolding e by (simp add: rec Let_def)
        then show ?thesis
        proof
          assume "(v, b) = (c, bmssp_partition_key c ?nd)"
          then show ?thesis
            using active unfolding e nat_graph_edge_list_def by simp
        next
          assume "(v, b) \<in> set updates"
          then have "(u, v) \<in> set (nat_graph_edge_list es)"
            by (rule tail)
          then show ?thesis
            unfolding e nat_graph_edge_list_def by simp
        qed
      qed
    qed
  qed
qed

lemma bmssp_relax_edges_update_partition_key:
  assumes "(v, b) \<in> set (fst (bmssp_relax_edges G settled u du ds))"
  shows "\<exists>d. b = bmssp_partition_key v d"
  using assms
proof (induction G arbitrary: ds v b)
  case Nil
  then show ?case
    by simp
next
  case (Cons e es)
  obtain a c w where e: "e = (a, c, w)"
    by (cases e)
  obtain updates ds1 where rec:
    "bmssp_relax_edges es settled u du ds = (updates, ds1)"
    by force
  have tail:
    "\<And>v b. (v, b) \<in> set updates \<Longrightarrow>
      \<exists>d. b = bmssp_partition_key v d"
  proof -
    fix v b
    assume update: "(v, b) \<in> set updates"
    have "(v, b) \<in> set (fst (bmssp_relax_edges es settled u du ds))"
      using update rec by simp
    then show "\<exists>d. b = bmssp_partition_key v d"
      by (rule Cons.IH)
  qed
  show ?case
  proof (cases "a = u \<and> c \<notin> set settled")
    case False
    then have "(v, b) \<in> set updates"
      using Cons.prems by (auto simp: e rec split: option.splits if_splits)
    then show ?thesis
      by (rule tail)
  next
    case True
    note active = True
    let ?nd = "du + w"
    show ?thesis
    proof (cases "bmssp_lookup_dist ds1 c")
      case None
      then have update_or_tail:
        "(v, b) = (c, bmssp_partition_key c ?nd) \<or>
          (v, b) \<in> set updates"
        using Cons.prems active unfolding e by (simp add: rec Let_def)
      then show ?thesis
      proof
        assume "(v, b) = (c, bmssp_partition_key c ?nd)"
        then show ?thesis
          by auto
      next
        assume "(v, b) \<in> set updates"
        then show ?thesis
          by (rule tail)
      qed
    next
      case (Some old)
      show ?thesis
      proof (cases "?nd < old")
        case False
        then have "(v, b) \<in> set updates"
          using Cons.prems active Some unfolding e by (simp add: rec Let_def)
        then show ?thesis
          by (rule tail)
      next
        case True
        then have update_or_tail:
          "(v, b) = (c, bmssp_partition_key c ?nd) \<or>
            (v, b) \<in> set updates"
          using Cons.prems active Some unfolding e by (simp add: rec Let_def)
        then show ?thesis
        proof
          assume "(v, b) = (c, bmssp_partition_key c ?nd)"
          then show ?thesis
            by auto
        next
          assume "(v, b) \<in> set updates"
          then show ?thesis
            by (rule tail)
        qed
      qed
    qed
  qed
qed

lemma bmssp_relax_vertices_update_partition_key:
  assumes "(v, b) \<in> set (fst (bmssp_relax_vertices G settled xs ds))"
  shows "\<exists>d. b = bmssp_partition_key v d"
  using assms
proof (induction xs arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons u us)
  show ?case
  proof (cases "bmssp_lookup_dist ds u")
    case None
    then have "(v, b) \<in> set (fst (bmssp_relax_vertices G settled us ds))"
      using Cons.prems by simp
    then show ?thesis
      by (rule Cons.IH)
  next
    case (Some du)
    obtain updates_u ds1 where edge_rec:
      "bmssp_relax_edges G settled u du ds = (updates_u, ds1)"
      by force
    obtain updates_us ds2 where vertices_rec:
      "bmssp_relax_vertices G settled us ds1 = (updates_us, ds2)"
      by force
    have update_cases:
      "(v, b) \<in> set updates_u \<or> (v, b) \<in> set updates_us"
      using Cons.prems Some edge_rec vertices_rec by auto
    then show ?thesis
    proof
      assume "(v, b) \<in> set updates_u"
      then have "(v, b) \<in> set (fst (bmssp_relax_edges G settled u du ds))"
        using edge_rec by simp
      then show ?thesis
        by (rule bmssp_relax_edges_update_partition_key)
    next
      assume "(v, b) \<in> set updates_us"
      then have "(v, b) \<in> set (fst (bmssp_relax_vertices G settled us ds1))"
        using vertices_rec by simp
      then show ?thesis
        by (rule Cons.IH)
    qed
  qed
qed

lemma bmssp_relax_vertices_update_floor:
  assumes "(v, b) \<in> set (fst (bmssp_relax_vertices G settled xs ds))"
  shows "\<exists>d. b = bmssp_partition_key v d \<and> nat (floor b) = d"
proof -
  obtain d where d: "b = bmssp_partition_key v d"
    using bmssp_relax_vertices_update_partition_key[OF assms] by blast
  then have "nat (floor b) = d"
    by (simp add: bmssp_partition_key_floor)
  then show ?thesis
    using d by blast
qed

lemma bmssp_relax_edges_update_floor:
  assumes "(v, b) \<in> set (fst (bmssp_relax_edges G settled u du ds))"
  shows "\<exists>d. b = bmssp_partition_key v d \<and> nat (floor b) = d"
proof -
  obtain d where d: "b = bmssp_partition_key v d"
    using bmssp_relax_edges_update_partition_key[OF assms] by blast
  then have "nat (floor b) = d"
    by (simp add: bmssp_partition_key_floor)
  then show ?thesis
    using d by blast
qed

lemma bmssp_relax_edges_update_not_settled:
  assumes "(v, b) \<in> set (fst (bmssp_relax_edges G settled u du ds))"
  shows "v \<notin> set settled"
  using assms
proof (induction G arbitrary: ds v b)
  case Nil
  then show ?case
    by simp
next
  case (Cons e es)
  obtain a c w where e: "e = (a, c, w)"
    by (cases e)
  obtain updates ds1 where rec:
    "bmssp_relax_edges es settled u du ds = (updates, ds1)"
    by force
  have tail:
    "\<And>v b. (v, b) \<in> set updates \<Longrightarrow> v \<notin> set settled"
  proof -
    fix v b
    assume update: "(v, b) \<in> set updates"
    have "(v, b) \<in> set (fst (bmssp_relax_edges es settled u du ds))"
      using update rec by simp
    then show "v \<notin> set settled"
      by (rule Cons.IH)
  qed
  show ?case
  proof (cases "a = u \<and> c \<notin> set settled")
    case False
    then have "(v, b) \<in> set updates"
      using Cons.prems rec unfolding e
      by (auto simp: Let_def split: option.splits if_splits)
    then show ?thesis
      by (rule tail)
  next
    case True
    note active = True
    let ?nd = "du + w"
    show ?thesis
    proof (cases "bmssp_lookup_dist ds1 c")
      case None
      then have update_or_tail:
        "(v, b) = (c, bmssp_partition_key c ?nd) \<or>
          (v, b) \<in> set updates"
        using Cons.prems active rec unfolding e by (simp add: Let_def)
      then show ?thesis
      proof
        assume "(v, b) = (c, bmssp_partition_key c ?nd)"
        then show ?thesis
          using active by simp
      next
        assume "(v, b) \<in> set updates"
        then show ?thesis
          by (rule tail)
      qed
    next
      case (Some old)
      show ?thesis
      proof (cases "?nd < old")
        case False
        then have "(v, b) \<in> set updates"
          using Cons.prems active Some rec unfolding e by (simp add: Let_def)
        then show ?thesis
          by (rule tail)
      next
        case True
        then have update_or_tail:
          "(v, b) = (c, bmssp_partition_key c ?nd) \<or>
            (v, b) \<in> set updates"
          using Cons.prems active Some rec unfolding e by (simp add: Let_def)
        then show ?thesis
        proof
          assume "(v, b) = (c, bmssp_partition_key c ?nd)"
          then show ?thesis
            using active by simp
        next
          assume "(v, b) \<in> set updates"
          then show ?thesis
            by (rule tail)
        qed
      qed
    qed
  qed
qed

lemma bmssp_relax_vertices_update_not_settled:
  assumes "(v, b) \<in> set (fst (bmssp_relax_vertices G settled xs ds))"
  shows "v \<notin> set settled"
  using assms
proof (induction xs arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons u us)
  show ?case
  proof (cases "bmssp_lookup_dist ds u")
    case None
    then have "(v, b) \<in> set (fst (bmssp_relax_vertices G settled us ds))"
      using Cons.prems by simp
    then show ?thesis
      by (rule Cons.IH)
  next
    case (Some du)
    obtain updates_u ds1 where edge_rec:
      "bmssp_relax_edges G settled u du ds = (updates_u, ds1)"
      by force
    obtain updates_us ds2 where vertices_rec:
      "bmssp_relax_vertices G settled us ds1 = (updates_us, ds2)"
      by force
    have update_cases:
      "(v, b) \<in> set updates_u \<or> (v, b) \<in> set updates_us"
      using Cons.prems Some edge_rec vertices_rec by auto
    then show ?thesis
    proof
      assume "(v, b) \<in> set updates_u"
      then have "(v, b) \<in> set (fst (bmssp_relax_edges G settled u du ds))"
        using edge_rec by simp
      then show ?thesis
        by (rule bmssp_relax_edges_update_not_settled)
    next
      assume "(v, b) \<in> set updates_us"
      then have "(v, b) \<in> set (fst (bmssp_relax_vertices G settled us ds1))"
        using vertices_rec by simp
      then show ?thesis
        by (rule Cons.IH)
    qed
  qed
qed

lemma bmssp_relax_edges_dist_keys:
  "set (map fst (snd (bmssp_relax_edges G settled u du ds))) =
    set (map fst ds) \<union> fst ` set (fst (bmssp_relax_edges G settled u du ds))"
proof (induction G arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons e es)
  obtain a c w where e: "e = (a, c, w)"
    by (cases e)
  obtain updates ds1 where rec:
    "bmssp_relax_edges es settled u du ds = (updates, ds1)"
    by force
  have tail:
    "set (map fst ds1) = set (map fst ds) \<union> fst ` set updates"
    using Cons.IH[of ds] rec by simp
  show ?case
  proof (cases "a = u \<and> c \<notin> set settled")
    case False
    then show ?thesis
      using rec tail unfolding e
      by (auto simp: Let_def split: option.splits if_splits)
  next
    case True
    note active = True
    let ?nd = "du + w"
    show ?thesis
    proof (cases "bmssp_lookup_dist ds1 c")
      case None
      then show ?thesis
        using active rec tail unfolding e
        by (auto simp: Let_def bmssp_set_dist_keys)
    next
      case (Some old)
      show ?thesis
      proof (cases "?nd < old")
        case False
        then show ?thesis
          using active rec Some tail unfolding e by (auto simp: Let_def)
      next
        case True
        then show ?thesis
          using active rec Some tail unfolding e
          by (auto simp: Let_def bmssp_set_dist_keys)
      qed
    qed
  qed
qed

lemma bmssp_relax_vertices_dist_keys:
  "set (map fst (snd (bmssp_relax_vertices G settled xs ds))) =
    set (map fst ds) \<union> fst ` set (fst (bmssp_relax_vertices G settled xs ds))"
proof (induction xs arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons u us)
  show ?case
  proof (cases "bmssp_lookup_dist ds u")
    case None
    then show ?thesis
      using Cons.IH[of ds] by simp
  next
    case (Some du)
    obtain updates_u ds1 where edge_rec:
      "bmssp_relax_edges G settled u du ds = (updates_u, ds1)"
      by force
    obtain updates_us ds2 where vertices_rec:
      "bmssp_relax_vertices G settled us ds1 = (updates_us, ds2)"
      by force
    have edge_keys:
      "set (map fst ds1) = set (map fst ds) \<union> fst ` set updates_u"
      using bmssp_relax_edges_dist_keys[of G settled u du ds] edge_rec
      by simp
    have tail_keys:
      "set (map fst ds2) = set (map fst ds1) \<union> fst ` set updates_us"
      using Cons.IH[of ds1] vertices_rec by simp
    show ?thesis
      using Some edge_rec vertices_rec edge_keys tail_keys by auto
  qed
qed

lemma bmssp_relax_edges_lookup_not_updated:
  assumes "v \<notin> fst ` set (fst (bmssp_relax_edges G settled u du ds))"
  shows "bmssp_lookup_dist (snd (bmssp_relax_edges G settled u du ds)) v =
    bmssp_lookup_dist ds v"
  using assms
proof (induction G arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons e es)
  obtain a c w where e: "e = (a, c, w)"
    by (cases e)
  obtain updates ds1 where rec:
    "bmssp_relax_edges es settled u du ds = (updates, ds1)"
    by force
  have v_not_tail: "v \<notin> fst ` set updates"
    using Cons.prems rec unfolding e
    by (auto simp: Let_def split: option.splits if_splits)
  have tail_lookup: "bmssp_lookup_dist ds1 v = bmssp_lookup_dist ds v"
    using Cons.IH[of ds] v_not_tail rec by simp
  show ?case
  proof (cases "a = u \<and> c \<notin> set settled")
    case False
    then show ?thesis
      using rec tail_lookup unfolding e
      by (auto simp: Let_def split: option.splits if_splits)
  next
    case True
    note active = True
    let ?nd = "du + w"
    show ?thesis
    proof (cases "bmssp_lookup_dist ds1 c")
      case None
      then have v_ne_c: "v \<noteq> c"
        using Cons.prems active rec unfolding e by (auto simp: Let_def)
      show ?thesis
        using active rec None tail_lookup v_ne_c unfolding e
        by (simp add: Let_def bmssp_lookup_dist_set_dist_other)
    next
      case (Some old)
      show ?thesis
      proof (cases "?nd < old")
        case False
        then show ?thesis
          using active rec Some tail_lookup unfolding e by (simp add: Let_def)
      next
        case True
        then have v_ne_c: "v \<noteq> c"
          using Cons.prems active rec Some unfolding e by (auto simp: Let_def)
        show ?thesis
          using active rec Some True tail_lookup v_ne_c unfolding e
          by (simp add: Let_def bmssp_lookup_dist_set_dist_other)
      qed
    qed
  qed
qed

lemma bmssp_relax_vertices_lookup_not_updated:
  assumes "v \<notin> fst ` set (fst (bmssp_relax_vertices G settled xs ds))"
  shows "bmssp_lookup_dist (snd (bmssp_relax_vertices G settled xs ds)) v =
    bmssp_lookup_dist ds v"
  using assms
proof (induction xs arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons u us)
  show ?case
  proof (cases "bmssp_lookup_dist ds u")
    case None
    then have v_not_tail:
      "v \<notin> fst ` set (fst (bmssp_relax_vertices G settled us ds))"
      using Cons.prems by simp
    show ?thesis
      using None Cons.IH[OF v_not_tail] by simp
  next
    case (Some du)
    obtain updates_u ds1 where edge_rec:
      "bmssp_relax_edges G settled u du ds = (updates_u, ds1)"
      by force
    obtain updates_us ds2 where vertices_rec:
      "bmssp_relax_vertices G settled us ds1 = (updates_us, ds2)"
      by force
    have v_not_u: "v \<notin> fst ` set updates_u"
      using Cons.prems Some edge_rec vertices_rec by auto
    have v_not_us: "v \<notin> fst ` set updates_us"
      using Cons.prems Some edge_rec vertices_rec by auto
    have lookup_u: "bmssp_lookup_dist ds1 v = bmssp_lookup_dist ds v"
      using bmssp_relax_edges_lookup_not_updated[of v G settled u du ds]
        v_not_u edge_rec by simp
    have lookup_us: "bmssp_lookup_dist ds2 v = bmssp_lookup_dist ds1 v"
      using Cons.IH[of ds1] v_not_us vertices_rec by simp
    show ?thesis
      using Some edge_rec vertices_rec lookup_u lookup_us by simp
  qed
qed

lemma bmssp_relax_edges_update_lookup_floor:
  assumes distinct_updates:
      "distinct (map fst (fst (bmssp_relax_edges G settled u du ds)))"
    and update: "(v, b) \<in> set (fst (bmssp_relax_edges G settled u du ds))"
  shows "bmssp_lookup_dist (snd (bmssp_relax_edges G settled u du ds)) v =
    Some (nat (floor b))"
  using distinct_updates update
proof (induction G arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons e es)
  obtain a c w where e: "e = (a, c, w)"
    by (cases e)
  obtain updates ds1 where rec:
    "bmssp_relax_edges es settled u du ds = (updates, ds1)"
    by force
  show ?case
  proof (cases "a = u \<and> c \<notin> set settled")
    case False
    have distinct_tail: "distinct (map fst updates)"
      using Cons.prems(1) False rec unfolding e
      by (auto simp: Let_def split: option.splits if_splits)
    have update_tail: "(v, b) \<in> set updates"
      using Cons.prems(2) False rec unfolding e
      by (auto simp: Let_def split: option.splits if_splits)
    have tail_lookup:
      "bmssp_lookup_dist ds1 v = Some (nat (floor b))"
      using Cons.IH[of ds] distinct_tail update_tail rec by simp
    then show ?thesis
      using False rec unfolding e
      by (auto simp: Let_def split: option.splits if_splits)
  next
    case True
    note active = True
    let ?nd = "du + w"
    show ?thesis
    proof (cases "bmssp_lookup_dist ds1 c")
      case None
      let ?new = "(c, bmssp_partition_key c ?nd)"
      have all_updates:
        "fst (bmssp_relax_edges (e # es) settled u du ds) = ?new # updates"
        using active None rec unfolding e by (simp add: Let_def)
      have all_ds:
        "snd (bmssp_relax_edges (e # es) settled u du ds) =
          bmssp_set_dist c ?nd ds1"
        using active None rec unfolding e by (simp add: Let_def)
      have distinct_tail: "distinct (map fst updates)"
        using Cons.prems(1) all_updates by simp
      have c_not_tail: "c \<notin> fst ` set updates"
        using Cons.prems(1) all_updates by simp
      show ?thesis
      proof (cases "(v, b) = ?new")
        case True
        then show ?thesis
          using all_ds by (simp add: bmssp_partition_key_floor
              bmssp_lookup_dist_set_dist_same)
      next
        case False
        then have update_tail: "(v, b) \<in> set updates"
          using Cons.prems(2) all_updates by auto
        have v_ne_c: "v \<noteq> c"
          using update_tail c_not_tail by force
        have tail_lookup:
          "bmssp_lookup_dist ds1 v = Some (nat (floor b))"
          using Cons.IH[of ds] distinct_tail update_tail rec by simp
        show ?thesis
          using all_ds v_ne_c tail_lookup
          by (simp add: bmssp_lookup_dist_set_dist_other)
      qed
    next
      case (Some old)
      show ?thesis
      proof (cases "?nd < old")
        case False
        have distinct_tail: "distinct (map fst updates)"
          using Cons.prems(1) active Some False rec unfolding e
          by (simp add: Let_def)
        have update_tail: "(v, b) \<in> set updates"
          using Cons.prems(2) active Some False rec unfolding e
          by (simp add: Let_def)
        have tail_lookup:
          "bmssp_lookup_dist ds1 v = Some (nat (floor b))"
          using Cons.IH[of ds] distinct_tail update_tail rec by simp
        then show ?thesis
          using active Some False rec unfolding e by (simp add: Let_def)
      next
        case True
        let ?new = "(c, bmssp_partition_key c ?nd)"
        have all_updates:
          "fst (bmssp_relax_edges (e # es) settled u du ds) = ?new # updates"
          using active Some True rec unfolding e by (simp add: Let_def)
        have all_ds:
          "snd (bmssp_relax_edges (e # es) settled u du ds) =
            bmssp_set_dist c ?nd ds1"
          using active Some True rec unfolding e by (simp add: Let_def)
        have distinct_tail: "distinct (map fst updates)"
          using Cons.prems(1) all_updates by simp
        have c_not_tail: "c \<notin> fst ` set updates"
          using Cons.prems(1) all_updates by simp
        show ?thesis
        proof (cases "(v, b) = ?new")
          case True
          then show ?thesis
            using all_ds by (simp add: bmssp_partition_key_floor
                bmssp_lookup_dist_set_dist_same)
        next
          case False
          then have update_tail: "(v, b) \<in> set updates"
            using Cons.prems(2) all_updates by auto
          have v_ne_c: "v \<noteq> c"
            using update_tail c_not_tail by force
          have tail_lookup:
            "bmssp_lookup_dist ds1 v = Some (nat (floor b))"
            using Cons.IH[of ds] distinct_tail update_tail rec by simp
          show ?thesis
            using all_ds v_ne_c tail_lookup
            by (simp add: bmssp_lookup_dist_set_dist_other)
        qed
      qed
    qed
  qed
qed

lemma bmssp_relax_vertices_update_lookup_floor:
  assumes distinct_updates:
      "distinct (map fst (fst (bmssp_relax_vertices G settled xs ds)))"
    and update: "(v, b) \<in> set (fst (bmssp_relax_vertices G settled xs ds))"
  shows "bmssp_lookup_dist (snd (bmssp_relax_vertices G settled xs ds)) v =
    Some (nat (floor b))"
  using distinct_updates update
proof (induction xs arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons u us)
  show ?case
  proof (cases "bmssp_lookup_dist ds u")
    case None
    have distinct_tail:
      "distinct (map fst (fst (bmssp_relax_vertices G settled us ds)))"
      using Cons.prems(1) None by simp
    have update_tail:
      "(v, b) \<in> set (fst (bmssp_relax_vertices G settled us ds))"
      using Cons.prems(2) None by simp
    show ?thesis
      using None Cons.IH[OF distinct_tail update_tail] by simp
  next
    case (Some du)
    obtain updates_u ds1 where edge_rec:
      "bmssp_relax_edges G settled u du ds = (updates_u, ds1)"
      by force
    obtain updates_us ds2 where vertices_rec:
      "bmssp_relax_vertices G settled us ds1 = (updates_us, ds2)"
      by force
    have updates_eq:
      "fst (bmssp_relax_vertices G settled (u # us) ds) =
        updates_u @ updates_us"
      using Some edge_rec vertices_rec by simp
    have ds_eq:
      "snd (bmssp_relax_vertices G settled (u # us) ds) = ds2"
      using Some edge_rec vertices_rec by simp
    have distinct_append: "distinct (map fst (updates_u @ updates_us))"
      using Cons.prems(1) updates_eq by simp
    show ?thesis
    proof (cases "(v, b) \<in> set updates_u")
      case True
      have distinct_u: "distinct (map fst updates_u)"
        using distinct_append by simp
      have lookup_u: "bmssp_lookup_dist ds1 v = Some (nat (floor b))"
        using bmssp_relax_edges_update_lookup_floor[of G settled u du ds v b]
          distinct_u True edge_rec by simp
      have v_not_us: "v \<notin> fst ` set updates_us"
        using distinct_append True by force
      have lookup_us: "bmssp_lookup_dist ds2 v = bmssp_lookup_dist ds1 v"
        using bmssp_relax_vertices_lookup_not_updated[of v G settled us ds1]
          v_not_us vertices_rec by simp
      show ?thesis
        using ds_eq lookup_u lookup_us by simp
    next
      case False
      have update_us: "(v, b) \<in> set updates_us"
        using Cons.prems(2) updates_eq False by auto
      have distinct_us: "distinct (map fst updates_us)"
        using distinct_append by simp
      have lookup_us: "bmssp_lookup_dist ds2 v = Some (nat (floor b))"
        using Cons.IH[of ds1] distinct_us update_us vertices_rec by simp
      show ?thesis
        using ds_eq lookup_us by simp
    qed
  qed
qed

lemma bmssp_relax_edges_lookup_Some_preserved:
  assumes distinct: "distinct (map fst ds)"
    and lookup: "bmssp_lookup_dist ds v = Some d"
  shows "\<exists>d'. bmssp_lookup_dist
    (snd (bmssp_relax_edges G settled u du ds)) v = Some d'"
proof -
  have v_key: "v \<in> set (map fst ds)"
    using lookup by (rule bmssp_lookup_dist_mem_key)
  have keys:
    "set (map fst (snd (bmssp_relax_edges G settled u du ds))) =
      set (map fst ds) \<union> fst ` set (fst (bmssp_relax_edges G settled u du ds))"
    by (rule bmssp_relax_edges_dist_keys)
  have distinct':
    "distinct (map fst (snd (bmssp_relax_edges G settled u du ds)))"
    by (rule bmssp_relax_edges_preserves_distinct_dist[OF distinct])
  have "v \<in> set (map fst (snd (bmssp_relax_edges G settled u du ds)))"
    using v_key keys by blast
  then obtain d' where "(v, d') \<in>
      set (snd (bmssp_relax_edges G settled u du ds))"
    by force
  then have "bmssp_lookup_dist
      (snd (bmssp_relax_edges G settled u du ds)) v = Some d'"
    by (rule bmssp_lookup_dist_Some_if_distinct_mem[OF distinct'])
  then show ?thesis
    by blast
qed

lemma bmssp_relax_vertices_lookup_Some_preserved:
  assumes distinct: "distinct (map fst ds)"
    and lookup: "bmssp_lookup_dist ds v = Some d"
  shows "\<exists>d'. bmssp_lookup_dist
    (snd (bmssp_relax_vertices G settled xs ds)) v = Some d'"
proof -
  have v_key: "v \<in> set (map fst ds)"
    using lookup by (rule bmssp_lookup_dist_mem_key)
  have keys:
    "set (map fst (snd (bmssp_relax_vertices G settled xs ds))) =
      set (map fst ds) \<union>
        fst ` set (fst (bmssp_relax_vertices G settled xs ds))"
    by (rule bmssp_relax_vertices_dist_keys)
  have distinct':
    "distinct (map fst (snd (bmssp_relax_vertices G settled xs ds)))"
    by (rule bmssp_relax_vertices_preserves_distinct_dist[OF distinct])
  have "v \<in> set (map fst (snd (bmssp_relax_vertices G settled xs ds)))"
    using v_key keys by blast
  then obtain d' where "(v, d') \<in>
      set (snd (bmssp_relax_vertices G settled xs ds))"
    by force
  then have "bmssp_lookup_dist
      (snd (bmssp_relax_vertices G settled xs ds)) v = Some d'"
    by (rule bmssp_lookup_dist_Some_if_distinct_mem[OF distinct'])
  then show ?thesis
    by blast
qed

lemma bmssp_relax_edges_lookup_le:
  assumes distinct: "distinct (map fst ds)"
    and old: "bmssp_lookup_dist ds v = Some old"
    and new:
      "bmssp_lookup_dist (snd (bmssp_relax_edges G settled u du ds)) v =
        Some new"
  shows "new \<le> old"
  using distinct old new
proof (induction G arbitrary: ds v old new)
  case Nil
  then show ?case
    by simp
next
  case (Cons e es)
  obtain a c w where e: "e = (a, c, w)"
    by (cases e)
  obtain updates ds1 where rec:
    "bmssp_relax_edges es settled u du ds = (updates, ds1)"
    by force
  have tail_distinct: "distinct (map fst ds1)"
    using bmssp_relax_edges_preserves_distinct_dist[OF Cons.prems(1),
        of es settled u du] rec by simp
  show ?case
  proof (cases "a = u \<and> c \<notin> set settled")
    case False
    have tail_new:
      "bmssp_lookup_dist (snd (bmssp_relax_edges es settled u du ds)) v =
        Some new"
      using Cons.prems(3) False rec unfolding e
      by (auto simp: Let_def split: option.splits if_splits)
    show ?thesis
      by (rule Cons.IH[OF Cons.prems(1) Cons.prems(2) tail_new])
  next
    case True
    note active = True
    let ?nd = "du + w"
    show ?thesis
    proof (cases "bmssp_lookup_dist ds1 c")
      case None
      show ?thesis
      proof (cases "v = c")
        case True
        have old_c: "bmssp_lookup_dist ds c = Some old"
          using Cons.prems(2) True by simp
        have "\<exists>d'. bmssp_lookup_dist
            (snd (bmssp_relax_edges es settled u du ds)) c = Some d'"
          by (rule bmssp_relax_edges_lookup_Some_preserved
              [OF Cons.prems(1) old_c])
        then show ?thesis
          using None rec by simp
      next
        case False
        have tail_new:
          "bmssp_lookup_dist
            (snd (bmssp_relax_edges es settled u du ds)) v = Some new"
          using Cons.prems(3) active None False rec unfolding e
          by (simp add: Let_def bmssp_lookup_dist_set_dist_other)
        show ?thesis
          by (rule Cons.IH[OF Cons.prems(1) Cons.prems(2) tail_new])
      qed
    next
      case (Some cur)
      show ?thesis
      proof (cases "?nd < cur")
        case False
        have tail_new:
          "bmssp_lookup_dist
            (snd (bmssp_relax_edges es settled u du ds)) v = Some new"
          using Cons.prems(3) active Some False rec unfolding e
          by (simp add: Let_def)
        show ?thesis
          by (rule Cons.IH[OF Cons.prems(1) Cons.prems(2) tail_new])
      next
        case True
        note improves = True
        show ?thesis
        proof (cases "v = c")
          case True
          have old_c: "bmssp_lookup_dist ds c = Some old"
            using Cons.prems(2) True by simp
          have tail_cur:
            "bmssp_lookup_dist
              (snd (bmssp_relax_edges es settled u du ds)) c = Some cur"
            using Some rec by simp
          have cur_le_old: "cur \<le> old"
            by (rule Cons.IH[OF Cons.prems(1) old_c tail_cur])
          have new_eq: "new = ?nd"
            using Cons.prems(3) active Some improves \<open>v = c\<close> rec unfolding e
            by (simp add: Let_def bmssp_lookup_dist_set_dist_same)
          then show ?thesis
            using improves cur_le_old by linarith
        next
          case False
          have tail_new:
            "bmssp_lookup_dist
              (snd (bmssp_relax_edges es settled u du ds)) v = Some new"
            using Cons.prems(3) active Some True False rec unfolding e
            by (simp add: Let_def bmssp_lookup_dist_set_dist_other)
          show ?thesis
            by (rule Cons.IH[OF Cons.prems(1) Cons.prems(2) tail_new])
        qed
      qed
    qed
  qed
qed

lemma bmssp_relax_vertices_lookup_le:
  assumes distinct: "distinct (map fst ds)"
    and old: "bmssp_lookup_dist ds v = Some old"
    and new:
      "bmssp_lookup_dist (snd (bmssp_relax_vertices G settled xs ds)) v =
        Some new"
  shows "new \<le> old"
  using distinct old new
proof (induction xs arbitrary: ds v old new)
  case Nil
  then show ?case
    by simp
next
  case (Cons u us)
  show ?case
  proof (cases "bmssp_lookup_dist ds u")
    case None
    have tail_new:
      "bmssp_lookup_dist (snd (bmssp_relax_vertices G settled us ds)) v =
        Some new"
      using Cons.prems(3) None by simp
    show ?thesis
      by (rule Cons.IH[OF Cons.prems(1) Cons.prems(2) tail_new])
  next
    case (Some du)
    obtain updates_u ds1 where edge_rec:
      "bmssp_relax_edges G settled u du ds = (updates_u, ds1)"
      by force
    obtain updates_us ds2 where vertices_rec:
      "bmssp_relax_vertices G settled us ds1 = (updates_us, ds2)"
      by force
    have distinct_ds1: "distinct (map fst ds1)"
      using bmssp_relax_edges_preserves_distinct_dist[OF Cons.prems(1),
          of G settled u du] edge_rec by simp
    obtain mid where mid: "bmssp_lookup_dist ds1 v = Some mid"
    proof -
      have "\<exists>d'. bmssp_lookup_dist
          (snd (bmssp_relax_edges G settled u du ds)) v = Some d'"
        by (rule bmssp_relax_edges_lookup_Some_preserved
            [OF Cons.prems(1) Cons.prems(2)])
      then obtain d' where "bmssp_lookup_dist
          (snd (bmssp_relax_edges G settled u du ds)) v = Some d'"
        by blast
      then have "bmssp_lookup_dist ds1 v = Some d'"
        using edge_rec by simp
      then show ?thesis
        by (rule that)
    qed
    have mid_le_old: "mid \<le> old"
    proof -
      have "bmssp_lookup_dist
          (snd (bmssp_relax_edges G settled u du ds)) v = Some mid"
        using mid edge_rec by simp
      then show ?thesis
        by (rule bmssp_relax_edges_lookup_le[OF Cons.prems(1) Cons.prems(2)])
    qed
    have final_new:
      "bmssp_lookup_dist (snd (bmssp_relax_vertices G settled us ds1)) v =
        Some new"
      using Cons.prems(3) Some edge_rec vertices_rec by simp
    have new_le_mid: "new \<le> mid"
      by (rule Cons.IH[OF distinct_ds1 mid final_new])
    then show ?thesis
      using mid_le_old by linarith
  qed
qed

lemma bmssp_relax_edges_edge_lookup_le_candidate:
  assumes edge: "(u, v, w) \<in> set G"
    and v_unsettled: "v \<notin> set settled"
  shows "\<exists>dv.
    bmssp_lookup_dist (snd (bmssp_relax_edges G settled u du ds)) v =
      Some dv \<and>
    dv \<le> du + w"
  using edge
proof (induction G arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons e es)
  obtain a b c where e: "e = (a, b, c)"
    by (cases e)
  obtain updates ds1 where rec:
    "bmssp_relax_edges es settled u du ds = (updates, ds1)"
    by force
  show ?case
  proof (cases "(u, v, w) \<in> set es")
    case True
    then obtain dv where tail_lookup:
        "bmssp_lookup_dist
          (snd (bmssp_relax_edges es settled u du ds)) v = Some dv"
      and tail_le: "dv \<le> du + w"
      using Cons.IH by blast
    have ds1_lookup: "bmssp_lookup_dist ds1 v = Some dv"
      using tail_lookup rec by simp
    show ?thesis
    proof (cases "a = u \<and> b \<notin> set settled")
      case False
      then have final_lookup:
        "bmssp_lookup_dist
          (snd (bmssp_relax_edges (e # es) settled u du ds)) v =
          Some dv"
        using rec ds1_lookup unfolding e
        by (auto simp: Let_def split: option.splits if_splits)
      show ?thesis
        using final_lookup tail_le by blast
    next
      case True
      note active = True
      let ?nd = "du + c"
      show ?thesis
      proof (cases "bmssp_lookup_dist ds1 b")
        case None
        show ?thesis
        proof (cases "v = b")
          case True
          note v_eq_b = True
          then have final_lookup:
            "bmssp_lookup_dist
              (snd (bmssp_relax_edges (e # es) settled u du ds)) v =
              Some ?nd"
            using active v_eq_b None rec unfolding e
            by (simp add: Let_def bmssp_lookup_dist_set_dist_same)
          have "?nd \<le> du + w"
            using v_eq_b None ds1_lookup by simp
          then show ?thesis
            using final_lookup by blast
        next
          case False
          note v_ne_b = False
          then have final_lookup:
            "bmssp_lookup_dist
              (snd (bmssp_relax_edges (e # es) settled u du ds)) v =
              Some dv"
            using active v_ne_b None rec ds1_lookup unfolding e
            by (simp add: Let_def bmssp_lookup_dist_set_dist_other)
          show ?thesis
            using final_lookup tail_le by blast
        qed
      next
        case (Some old)
        show ?thesis
        proof (cases "?nd < old")
          case False
          then have final_lookup:
            "bmssp_lookup_dist
              (snd (bmssp_relax_edges (e # es) settled u du ds)) v =
              Some dv"
            using active Some rec ds1_lookup unfolding e by (simp add: Let_def)
          show ?thesis
            using final_lookup tail_le by blast
        next
          case True
          note improves = True
          show ?thesis
          proof (cases "v = b")
            case True
            note v_eq_b = True
            then have final_lookup:
              "bmssp_lookup_dist
                (snd (bmssp_relax_edges (e # es) settled u du ds)) v =
                Some ?nd"
              using active Some improves rec v_eq_b
              unfolding e
              by (simp add: Let_def bmssp_lookup_dist_set_dist_same)
            have "?nd \<le> du + w"
            proof -
              have old_eq: "old = dv"
                using v_eq_b Some ds1_lookup by simp
              show ?thesis
                using improves old_eq tail_le by linarith
            qed
            then show ?thesis
              using final_lookup by blast
          next
            case False
            note v_ne_b = False
            then have final_lookup:
              "bmssp_lookup_dist
                (snd (bmssp_relax_edges (e # es) settled u du ds)) v =
                Some dv"
              using active Some improves rec ds1_lookup v_ne_b
              unfolding e
              by (simp add: Let_def bmssp_lookup_dist_set_dist_other)
            show ?thesis
              using final_lookup tail_le by blast
          qed
        qed
      qed
    qed
  next
    case False
    then have head: "e = (u, v, w)"
      using Cons.prems by simp
    have active: "a = u \<and> b \<notin> set settled"
      using head v_unsettled unfolding e by simp
    let ?nd = "du + w"
    show ?thesis
    proof (cases "bmssp_lookup_dist ds1 v")
      case None
      then have final_lookup:
        "bmssp_lookup_dist
          (snd (bmssp_relax_edges (e # es) settled u du ds)) v =
          Some ?nd"
        using active rec head unfolding e
        by (simp add: Let_def bmssp_lookup_dist_set_dist_same)
      show ?thesis
        using final_lookup by blast
    next
      case (Some old)
      show ?thesis
      proof (cases "?nd < old")
        case True
        then have final_lookup:
          "bmssp_lookup_dist
            (snd (bmssp_relax_edges (e # es) settled u du ds)) v =
            Some ?nd"
          using active Some rec head unfolding e
          by (simp add: Let_def bmssp_lookup_dist_set_dist_same)
        show ?thesis
          using final_lookup by blast
      next
        case False
        then have final_lookup:
          "bmssp_lookup_dist
            (snd (bmssp_relax_edges (e # es) settled u du ds)) v =
            Some old"
          using active Some rec head unfolding e by (simp add: Let_def)
        have "old \<le> ?nd"
          using False by simp
        then show ?thesis
          using final_lookup by blast
      qed
    qed
  qed
qed

lemma bmssp_relax_edges_update_improves_lookup:
  assumes distinct: "distinct (map fst ds)"
    and update: "(v, b) \<in> set (fst (bmssp_relax_edges G settled u du ds))"
    and old: "bmssp_lookup_dist ds v = Some old"
  shows "nat (floor b) < old"
  using distinct update old
proof (induction G arbitrary: ds v b old)
  case Nil
  then show ?case
    by simp
next
  case (Cons e es)
  obtain a c w where e: "e = (a, c, w)"
    by (cases e)
  obtain updates ds1 where rec:
    "bmssp_relax_edges es settled u du ds = (updates, ds1)"
    by force
  show ?case
  proof (cases "a = u \<and> c \<notin> set settled")
    case False
    have update_tail:
      "(v, b) \<in> set (fst (bmssp_relax_edges es settled u du ds))"
      using Cons.prems(2) False rec unfolding e
      by (auto simp: Let_def split: option.splits if_splits)
    show ?thesis
      by (rule Cons.IH[OF Cons.prems(1) update_tail Cons.prems(3)])
  next
    case True
    note active = True
    let ?nd = "du + w"
    show ?thesis
    proof (cases "bmssp_lookup_dist ds1 c")
      case None
      have update_or_tail:
        "(v, b) = (c, bmssp_partition_key c ?nd) \<or>
          (v, b) \<in> set updates"
        using Cons.prems(2) active None rec unfolding e by (simp add: Let_def)
      then show ?thesis
      proof
        assume current: "(v, b) = (c, bmssp_partition_key c ?nd)"
        have old_c: "bmssp_lookup_dist ds c = Some old"
          using Cons.prems(3) current by simp
        have "\<exists>d'. bmssp_lookup_dist
            (snd (bmssp_relax_edges es settled u du ds)) c = Some d'"
          by (rule bmssp_relax_edges_lookup_Some_preserved
              [OF Cons.prems(1) old_c])
        then show ?thesis
          using None rec by simp
      next
        assume "(v, b) \<in> set updates"
        then have update_tail:
          "(v, b) \<in> set (fst (bmssp_relax_edges es settled u du ds))"
          using rec by simp
        show ?thesis
          by (rule Cons.IH[OF Cons.prems(1) update_tail Cons.prems(3)])
      qed
    next
      case (Some cur)
      show ?thesis
      proof (cases "?nd < cur")
        case False
        have update_tail:
          "(v, b) \<in> set (fst (bmssp_relax_edges es settled u du ds))"
          using Cons.prems(2) active Some False rec unfolding e
          by (simp add: Let_def)
        show ?thesis
          by (rule Cons.IH[OF Cons.prems(1) update_tail Cons.prems(3)])
      next
        case True
        have update_or_tail:
          "(v, b) = (c, bmssp_partition_key c ?nd) \<or>
            (v, b) \<in> set updates"
          using Cons.prems(2) active Some True rec unfolding e
          by (simp add: Let_def)
        then show ?thesis
        proof
          assume current: "(v, b) = (c, bmssp_partition_key c ?nd)"
          have old_c: "bmssp_lookup_dist ds c = Some old"
            using Cons.prems(3) current by simp
          have tail_cur:
            "bmssp_lookup_dist
              (snd (bmssp_relax_edges es settled u du ds)) c = Some cur"
            using Some rec by simp
          have cur_le_old: "cur \<le> old"
            by (rule bmssp_relax_edges_lookup_le
                [OF Cons.prems(1) old_c tail_cur])
          have "nat (floor b) = ?nd"
            using current by (simp add: bmssp_partition_key_floor)
          then show ?thesis
            using True cur_le_old by linarith
        next
          assume "(v, b) \<in> set updates"
          then have update_tail:
            "(v, b) \<in> set (fst (bmssp_relax_edges es settled u du ds))"
            using rec by simp
          show ?thesis
            by (rule Cons.IH[OF Cons.prems(1) update_tail Cons.prems(3)])
        qed
      qed
    qed
  qed
qed

lemma bmssp_relax_vertices_update_improves_lookup:
  assumes distinct: "distinct (map fst ds)"
    and update: "(v, b) \<in> set (fst (bmssp_relax_vertices G settled xs ds))"
    and old: "bmssp_lookup_dist ds v = Some old"
  shows "nat (floor b) < old"
  using distinct update old
proof (induction xs arbitrary: ds v b old)
  case Nil
  then show ?case
    by simp
next
  case (Cons u us)
  show ?case
  proof (cases "bmssp_lookup_dist ds u")
    case None
    have update_tail:
      "(v, b) \<in> set (fst (bmssp_relax_vertices G settled us ds))"
      using Cons.prems(2) None by simp
    show ?thesis
      by (rule Cons.IH[OF Cons.prems(1) update_tail Cons.prems(3)])
  next
    case (Some du)
    obtain updates_u ds1 where edge_rec:
      "bmssp_relax_edges G settled u du ds = (updates_u, ds1)"
      by force
    obtain updates_us ds2 where vertices_rec:
      "bmssp_relax_vertices G settled us ds1 = (updates_us, ds2)"
      by force
    have update_cases: "(v, b) \<in> set updates_u \<or> (v, b) \<in> set updates_us"
      using Cons.prems(2) Some edge_rec vertices_rec by auto
    then show ?thesis
    proof
      assume "(v, b) \<in> set updates_u"
      then have edge_update:
        "(v, b) \<in> set (fst (bmssp_relax_edges G settled u du ds))"
        using edge_rec by simp
      show ?thesis
        by (rule bmssp_relax_edges_update_improves_lookup
            [OF Cons.prems(1) edge_update Cons.prems(3)])
    next
      assume update_us: "(v, b) \<in> set updates_us"
      have distinct_ds1: "distinct (map fst ds1)"
        using bmssp_relax_edges_preserves_distinct_dist[OF Cons.prems(1),
            of G settled u du] edge_rec by simp
      obtain mid where mid: "bmssp_lookup_dist ds1 v = Some mid"
      proof -
        have "\<exists>d'. bmssp_lookup_dist
            (snd (bmssp_relax_edges G settled u du ds)) v = Some d'"
          by (rule bmssp_relax_edges_lookup_Some_preserved
              [OF Cons.prems(1) Cons.prems(3)])
        then obtain d' where "bmssp_lookup_dist
            (snd (bmssp_relax_edges G settled u du ds)) v = Some d'"
          by blast
        then have "bmssp_lookup_dist ds1 v = Some d'"
          using edge_rec by simp
        then show ?thesis
          by (rule that)
      qed
      have mid_le_old: "mid \<le> old"
      proof -
        have "bmssp_lookup_dist
            (snd (bmssp_relax_edges G settled u du ds)) v = Some mid"
          using mid edge_rec by simp
        then show ?thesis
          by (rule bmssp_relax_edges_lookup_le
              [OF Cons.prems(1) Cons.prems(3)])
      qed
      have update_tail:
        "(v, b) \<in> set (fst (bmssp_relax_vertices G settled us ds1))"
        using update_us vertices_rec by simp
      have "nat (floor b) < mid"
        by (rule Cons.IH[OF distinct_ds1 update_tail mid])
      then show ?thesis
        using mid_le_old by linarith
    qed
  qed
qed

lemma bmssp_relax_edges_updates_distinct:
  assumes distinct_edges: "distinct (nat_graph_edge_list G)"
  shows "distinct (map fst (fst (bmssp_relax_edges G settled u du ds)))"
  using distinct_edges
proof (induction G arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons e es)
  obtain a c w where e: "e = (a, c, w)"
    by (cases e)
  obtain updates ds1 where rec:
    "bmssp_relax_edges es settled u du ds = (updates, ds1)"
    by force
  have tail_edges: "distinct (nat_graph_edge_list es)"
    using Cons.prems unfolding e nat_graph_edge_list_def by simp
  have tail_distinct: "distinct (map fst updates)"
    using Cons.IH[OF tail_edges, of ds] rec by simp
  have c_notin_tail:
    "a = u \<Longrightarrow> c \<notin> fst ` set updates"
  proof
    assume a_u: "a = u" and c_tail: "c \<in> fst ` set updates"
    then obtain b where update: "(c, b) \<in> set updates"
      by force
    have update_rec:
      "(c, b) \<in> set (fst (bmssp_relax_edges es settled u du ds))"
      using update rec by simp
    have "(u, c) \<in> set (nat_graph_edge_list es)"
      by (rule bmssp_relax_edges_update_edge[OF update_rec])
    then show False
      using Cons.prems a_u unfolding e nat_graph_edge_list_def by simp
  qed
  show ?case
  proof (cases "a = u \<and> c \<notin> set settled")
    case False
    then show ?thesis
      using tail_distinct by (auto simp: e rec split: option.splits if_splits)
  next
    case True
    note active = True
    let ?nd = "du + w"
    have c_notin: "c \<notin> fst ` set updates"
      using c_notin_tail active by blast
    show ?thesis
    proof (cases "bmssp_lookup_dist ds1 c")
      case None
      then show ?thesis
        using tail_distinct c_notin active unfolding e
        by (simp add: rec Let_def)
    next
      case (Some old)
      show ?thesis
      proof (cases "?nd < old")
        case False
        then show ?thesis
          using tail_distinct active Some unfolding e by (simp add: rec Let_def)
      next
        case True
        then show ?thesis
          using tail_distinct c_notin active Some unfolding e
          by (simp add: rec Let_def)
      qed
    qed
  qed
qed

lemma bmssp_relax_vertices_singleton_updates_distinct:
  assumes distinct_edges: "distinct (nat_graph_edge_list G)"
  shows "distinct
    (map fst (fst (bmssp_relax_vertices G settled [u] ds)))"
  using bmssp_relax_edges_updates_distinct[OF distinct_edges]
  by (cases "bmssp_lookup_dist ds u") (auto split: prod.splits)

lemma bmssp_relax_vertices_updates_distinct_if_length_le_one:
  assumes distinct_edges: "distinct (nat_graph_edge_list G)"
    and len: "length xs \<le> 1"
  shows "distinct (map fst (fst (bmssp_relax_vertices G settled xs ds)))"
proof (cases xs)
  case Nil
  then show ?thesis
    by simp
next
  case (Cons u us)
  then have "us = []"
    using len by (cases us) simp_all
  then show ?thesis
    using Cons bmssp_relax_vertices_singleton_updates_distinct[OF distinct_edges]
    by simp
qed

lemma bmssp_relax_vertices_pulled_updates_distinct:
  assumes wf: "nat_graph_well_formed G"
    and distinct_vertices: "distinct vertices"
    and pull: "pull_separates (bp_view P) bmssp_block_size B S beta D'"
  shows "distinct
    (map fst
      (fst (bmssp_relax_vertices G settled
        (filter (\<lambda>x. x \<in> S \<and> x \<notin> set old_settled) vertices) ds)))"
proof -
  have len:
    "length (filter (\<lambda>x. x \<in> S \<and> x \<notin> set old_settled) vertices)
      \<le> 1"
    by (rule bmssp_pulled_length_le_one[OF distinct_vertices pull])
  have distinct_edges: "distinct (nat_graph_edge_list G)"
    by (rule nat_graph_well_formed_distinct_edge_list[OF wf])
  show ?thesis
    by (rule bmssp_relax_vertices_updates_distinct_if_length_le_one
        [OF distinct_edges len])
qed

lemma bmssp_apply_updates_ordered_after_pull:
  fixes old_settled settled :: "nat list"
  assumes wf: "nat_graph_well_formed G"
    and distinct_vertices: "distinct vertices"
    and ord: "bp_ordered_invariant P"
    and upper: "partition_upper_bound (bp_view P) B"
    and pull: "bp_pull bmssp_block_size B P = (S, beta, P1)"
  shows "bp_ordered_invariant
    (bmssp_apply_updates
      (fst (bmssp_relax_vertices G settled
        (filter (\<lambda>x. x \<in> S \<and> x \<notin> set old_settled) vertices) ds))
      P1)"
proof -
  let ?pulled =
    "filter (\<lambda>x. x \<in> S \<and> x \<notin> set old_settled) vertices"
  let ?updates = "fst (bmssp_relax_vertices G settled ?pulled ds)"
  have sep: "pull_separates (bp_view P) bmssp_block_size B S beta (bp_view P1)"
    by (rule bmssp_pull_refines_pull_separates[OF ord upper pull])
  have P1_ord: "bp_ordered_invariant P1"
    by (rule bmssp_pull_ordered_invariant[OF ord pull])
  have distinct_updates: "distinct (map fst ?updates)"
    by (rule bmssp_relax_vertices_pulled_updates_distinct
        [OF wf distinct_vertices sep])
  show ?thesis
    by (rule bmssp_apply_updates_ordered_invariant_from_ordered
        [OF P1_ord distinct_updates])
qed

lemma bmssp_partition_key_zero_lt_bound [simp]:
  "bmssp_partition_key s 0 < bmssp_bound"
proof -
  have "bmssp_partition_key s 0 < real (Suc 0)"
    by (rule bmssp_partition_key_lt_suc_distance)
  then show ?thesis
    unfolding bmssp_bound_def bmssp_infinity_def by simp
qed

lemma bmssp_partition_key_lt_bound_if_distance_lt:
  assumes "d < bmssp_infinity"
  shows "bmssp_partition_key v d < bmssp_bound"
proof -
  have "bmssp_partition_key v d < real (Suc d)"
    by (rule bmssp_partition_key_lt_suc_distance)
  also have "\<dots> \<le> real bmssp_infinity"
    using assms by simp
  finally show ?thesis
    unfolding bmssp_bound_def .
qed

lemma bmssp_initial_partition_bridge:
  shows "bp_ordered_invariant
      (bp_result_of
        (c_bp_regularized_local_insert s (bmssp_partition_key s 0)
          (bp_empty bmssp_block_size bmssp_bound)))"
    and "partition_upper_bound
      (bp_view
        (bp_result_of
          (c_bp_regularized_local_insert s (bmssp_partition_key s 0)
            (bp_empty bmssp_block_size bmssp_bound))))
      bmssp_bound"
    and "bp_view
        (bp_result_of
          (c_bp_regularized_local_insert s (bmssp_partition_key s 0)
            (bp_empty bmssp_block_size bmssp_bound))) =
      min_update (bp_view (bp_empty bmssp_block_size bmssp_bound))
        s (bmssp_partition_key s 0)"
proof -
  let ?P0 = "bp_empty bmssp_block_size bmssp_bound"
  let ?P1 =
    "bp_result_of
      (c_bp_regularized_local_insert s (bmssp_partition_key s 0) ?P0)"
  have block_pos: "0 < bmssp_block_size"
    unfolding bmssp_block_size_def by simp
  have reg0: "bp_regular_invariant ?P0"
    by (rule bp_empty_regular_invariant[OF block_pos])
  have reg1: "bp_regular_invariant ?P1"
    by (rule c_bp_regularized_local_insert_regular_invariant[OF reg0])
  show "bp_ordered_invariant ?P1"
    by (rule bp_regular_invariant_ordered_invariant[OF reg1])
  have view:
    "bp_view ?P1 = min_update (bp_view ?P0) s (bmssp_partition_key s 0)"
    by (rule c_bp_regularized_local_insert_refines_min_update[OF reg0])
  show "bp_view ?P1 =
      min_update (bp_view ?P0) s (bmssp_partition_key s 0)"
    by (rule view)
  have upper0: "partition_upper_bound (bp_view ?P0) bmssp_bound"
    unfolding partition_upper_bound_def by simp
  have "partition_upper_bound
      (min_update (bp_view ?P0) s (bmssp_partition_key s 0)) bmssp_bound"
    by (rule min_update_preserves_upper_bound[OF upper0])
      (rule bmssp_partition_key_zero_lt_bound)
  then show "partition_upper_bound (bp_view ?P1) bmssp_bound"
    unfolding view .
qed

lemma bmssp_loop_partition_step_bridge:
  fixes old_settled settled vertices :: "nat list"
    and pulled :: "nat list"
    and updates :: "(nat \<times> real) list"
  assumes pulled_def:
      "pulled =
        filter (\<lambda>x. x \<in> S \<and> x \<notin> set old_settled) vertices"
    and updates_def: "updates = fst (bmssp_relax_vertices G settled pulled ds)"
    and P2_def: "P2 = bmssp_apply_updates updates P1"
    and wf: "nat_graph_well_formed G"
    and distinct_vertices: "distinct vertices"
    and ord: "bp_ordered_invariant P"
    and upper: "partition_upper_bound (bp_view P) B"
    and pull: "bp_pull bmssp_block_size B P = (S, beta, P1)"
  shows "pull_separates (bp_view P) bmssp_block_size B S beta (bp_view P1)"
    and "bp_ordered_invariant P1"
    and "partition_upper_bound (bp_view P1) B"
    and "length pulled \<le> 1"
    and "distinct (map fst updates)"
    and "(\<And>x b. (x, b) \<in> set updates \<Longrightarrow>
      \<exists>d. b = bmssp_partition_key x d \<and> nat (floor b) = d)"
    and "bp_view P2 = batch_min_update (bp_view P1) updates"
    and "bp_ordered_invariant P2"
    and "(\<And>x b. (x, b) \<in> set updates \<Longrightarrow> b < B) \<Longrightarrow>
      partition_upper_bound (bp_view P2) B"
proof -
  have sep:
    "pull_separates (bp_view P) bmssp_block_size B S beta (bp_view P1)"
    by (rule bmssp_pull_refines_pull_separates[OF ord upper pull])
  have P1_ord: "bp_ordered_invariant P1"
    by (rule bmssp_pull_ordered_invariant[OF ord pull])
  have P1_upper: "partition_upper_bound (bp_view P1) B"
    by (rule bmssp_pull_preserves_upper_bound[OF ord upper pull])
  have pulled_len: "length pulled \<le> 1"
    unfolding pulled_def
    by (rule bmssp_pulled_length_le_one[OF distinct_vertices sep])
  have updates_distinct: "distinct (map fst updates)"
    unfolding updates_def pulled_def
    by (rule bmssp_relax_vertices_pulled_updates_distinct
        [OF wf distinct_vertices sep])
  have updates_floor:
    "\<And>x b. (x, b) \<in> set updates \<Longrightarrow>
      \<exists>d. b = bmssp_partition_key x d \<and> nat (floor b) = d"
  proof -
    fix x b
    assume "(x, b) \<in> set updates"
    then have "(x, b) \<in>
      set (fst (bmssp_relax_vertices G settled pulled ds))"
      unfolding updates_def .
    then show "\<exists>d. b = bmssp_partition_key x d \<and> nat (floor b) = d"
      by (rule bmssp_relax_vertices_update_floor)
  qed
  have view:
    "bp_view P2 = batch_min_update (bp_view P1) updates"
    unfolding P2_def
    by (rule bmssp_apply_updates_refines_batch_min_update_from_ordered
        [OF P1_ord updates_distinct])
  have P2_ord: "bp_ordered_invariant P2"
    unfolding P2_def
    by (rule bmssp_apply_updates_ordered_invariant_from_ordered
        [OF P1_ord updates_distinct])
  show "pull_separates (bp_view P) bmssp_block_size B S beta (bp_view P1)"
    by (rule sep)
  show "bp_ordered_invariant P1"
    by (rule P1_ord)
  show "partition_upper_bound (bp_view P1) B"
    by (rule P1_upper)
  show "length pulled \<le> 1"
    by (rule pulled_len)
  show "distinct (map fst updates)"
    by (rule updates_distinct)
  show "\<And>x b. (x, b) \<in> set updates \<Longrightarrow>
      \<exists>d. b = bmssp_partition_key x d \<and> nat (floor b) = d"
    by (rule updates_floor)
  show "bp_view P2 = batch_min_update (bp_view P1) updates"
    by (rule view)
  show "bp_ordered_invariant P2"
    by (rule P2_ord)
  show "(\<And>x b. (x, b) \<in> set updates \<Longrightarrow> b < B) \<Longrightarrow>
      partition_upper_bound (bp_view P2) B"
    unfolding P2_def
    by (rule bmssp_apply_updates_preserves_upper_bound_from_ordered
        [OF P1_ord P1_upper updates_distinct])
qed

definition bmssp_partition_keys_match ::
  "nat list \<Rightarrow> nat_dist \<Rightarrow> nat bucketed_partition \<Rightarrow> bool" where
  "bmssp_partition_keys_match settled ds P \<longleftrightarrow>
     keys_of (bp_view P) = set (map fst ds) - set settled"

lemma bmssp_partition_keys_match_initial:
  "bmssp_partition_keys_match [] [(src, 0)]
    (bp_result_of
      (c_bp_regularized_local_insert src (bmssp_partition_key src 0)
        (bp_empty bmssp_block_size bmssp_bound)))"
proof -
  have view:
    "bp_view
      (bp_result_of
        (c_bp_regularized_local_insert src (bmssp_partition_key src 0)
          (bp_empty bmssp_block_size bmssp_bound))) =
      min_update (bp_view (bp_empty bmssp_block_size bmssp_bound))
        src (bmssp_partition_key src 0)"
    by (rule bmssp_initial_partition_bridge(3))
  show ?thesis
    unfolding bmssp_partition_keys_match_def view by simp
qed

lemma bmssp_filter_pulled_set_eq:
  assumes S_vertices: "S \<subseteq> set vertices"
    and S_unsettled: "S \<inter> set settled = {}"
  shows "set (filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices) = S"
proof
  show "set (filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices)
      \<subseteq> S"
    by auto
next
  show "S \<subseteq>
      set (filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices)"
  proof
    fix x
    assume xS: "x \<in> S"
    then have "x \<in> set vertices"
      using S_vertices by blast
    moreover have "x \<notin> set settled"
      using S_unsettled xS by blast
    ultimately show "x \<in>
        set (filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices)"
      using xS by simp
  qed
qed

lemma bmssp_partition_keys_match_step:
  fixes old_settled settled vertices :: "nat list"
    and pulled :: "nat list"
    and updates :: "(nat \<times> real) list"
  assumes match: "bmssp_partition_keys_match old_settled ds P"
    and keys_vertices: "keys_of (bp_view P) \<subseteq> set vertices"
    and pulled_def:
      "pulled =
        filter (\<lambda>x. x \<in> S \<and> x \<notin> set old_settled) vertices"
    and settled_def: "settled = pulled @ old_settled"
    and relaxed: "bmssp_relax_vertices G settled pulled ds = (updates, ds')"
    and pull: "pull_separates (bp_view P) bmssp_block_size B S beta
      (bp_view P1)"
    and view: "bp_view P2 = batch_min_update (bp_view P1) updates"
  shows "bmssp_partition_keys_match settled ds' P2"
proof -
  have S_subset_keys: "S \<subseteq> keys_of (bp_view P)"
    by (rule pull_separates_subset[OF pull])
  have S_vertices: "S \<subseteq> set vertices"
    using S_subset_keys keys_vertices by blast
  have S_unsettled: "S \<inter> set old_settled = {}"
    using S_subset_keys match unfolding bmssp_partition_keys_match_def by auto
  have pulled_set: "set pulled = S"
    unfolding pulled_def
    by (rule bmssp_filter_pulled_set_eq[OF S_vertices S_unsettled])
  have settled_set: "set settled = S \<union> set old_settled"
    unfolding settled_def using pulled_set by auto
  have P1_keys: "keys_of (bp_view P1) = keys_of (bp_view P) - S"
    by (rule pull_separates_remaining_keys[OF pull])
  have P2_keys:
    "keys_of (bp_view P2) =
      (set (map fst ds) - set old_settled - S) \<union> fst ` set updates"
    using match view P1_keys
    unfolding bmssp_partition_keys_match_def
    by (auto simp: batch_min_update_keys)
  have ds'_keys:
    "set (map fst ds') = set (map fst ds) \<union> fst ` set updates"
    using bmssp_relax_vertices_dist_keys[of G settled pulled ds] relaxed
    by simp
  have updates_unsettled:
    "fst ` set updates \<inter> set settled = {}"
  proof
    show "fst ` set updates \<inter> set settled \<subseteq> {}"
    proof
      fix x
      assume x: "x \<in> fst ` set updates \<inter> set settled"
      then obtain b where xb: "(x, b) \<in> set updates"
        by auto
      have "(x, b) \<in> set (fst (bmssp_relax_vertices G settled pulled ds))"
        using xb relaxed by simp
      then have "x \<notin> set settled"
        by (rule bmssp_relax_vertices_update_not_settled)
      then show "x \<in> {}"
        using x by simp
    qed
    show "{} \<subseteq> fst ` set updates \<inter> set settled"
      by simp
  qed
  have "set (map fst ds') - set settled =
      (set (map fst ds) - set old_settled - S) \<union> fst ` set updates"
    using ds'_keys settled_set updates_unsettled by auto
  then show ?thesis
    using P2_keys unfolding bmssp_partition_keys_match_def by simp
qed

lemma bmssp_partition_keys_match_loop_step_bridge:
  fixes old_settled settled vertices :: "nat list"
    and pulled :: "nat list"
    and updates :: "(nat \<times> real) list"
  assumes match: "bmssp_partition_keys_match old_settled ds P"
    and keys_vertices: "keys_of (bp_view P) \<subseteq> set vertices"
    and pulled_def:
      "pulled =
        filter (\<lambda>x. x \<in> S \<and> x \<notin> set old_settled) vertices"
    and settled_def: "settled = pulled @ old_settled"
    and relaxed: "bmssp_relax_vertices G settled pulled ds = (updates, ds')"
    and P2_def: "P2 = bmssp_apply_updates updates P1"
    and wf: "nat_graph_well_formed G"
    and distinct_vertices: "distinct vertices"
    and ord: "bp_ordered_invariant P"
    and upper: "partition_upper_bound (bp_view P) B"
    and pull: "bp_pull bmssp_block_size B P = (S, beta, P1)"
  shows "bmssp_partition_keys_match settled ds' P2"
proof -
  have updates_def: "updates = fst (bmssp_relax_vertices G settled pulled ds)"
    using relaxed by simp
  have sep:
    "pull_separates (bp_view P) bmssp_block_size B S beta (bp_view P1)"
    by (rule bmssp_loop_partition_step_bridge(1)
        [OF pulled_def updates_def P2_def wf distinct_vertices ord upper pull])
  have view: "bp_view P2 = batch_min_update (bp_view P1) updates"
    by (rule bmssp_loop_partition_step_bridge(7)
        [OF pulled_def updates_def P2_def wf distinct_vertices ord upper pull])
  show ?thesis
    by (rule bmssp_partition_keys_match_step
        [OF match keys_vertices pulled_def settled_def relaxed sep view])
qed

lemma batch_min_update_value_not_updated:
  assumes "x \<notin> fst ` set xs"
  shows "value_of (batch_min_update D xs) x = value_of D x"
  using assms
proof (induction xs arbitrary: D)
  case Nil
  then show ?case
    unfolding batch_min_update_def by simp
next
  case (Cons xb xs)
  obtain y b where xb: "xb = (y, b)"
    by force
  have x_ne_y: "x \<noteq> y"
    using Cons.prems unfolding xb by simp
  have x_not_tail: "x \<notin> fst ` set xs"
    using Cons.prems unfolding xb by simp
  have tail:
    "value_of (batch_min_update (min_update D y b) xs) x =
      value_of (min_update D y b) x"
    by (rule Cons.IH[OF x_not_tail])
  have step: "value_of (min_update D y b) x = value_of D x"
    using min_update_value_same[OF x_ne_y, of D b] .
  show ?case
  proof -
    have "value_of (batch_min_update D (xb # xs)) x =
        value_of (batch_min_update (min_update D y b) xs) x"
      unfolding batch_min_update_def xb by simp
    also have "\<dots> = value_of (min_update D y b) x"
      by (rule tail)
    also have "\<dots> = value_of D x"
      by (rule step)
    finally show ?case .
  qed
qed

lemma batch_min_update_value_pair_less_old:
  assumes distinct: "distinct (map fst xs)"
    and pair: "(x, b) \<in> set xs"
    and better: "x \<in> keys_of D \<Longrightarrow> b < value_of D x"
  shows "value_of (batch_min_update D xs) x = b"
  using distinct pair better
proof (induction xs arbitrary: D)
  case Nil
  then show ?case
    by simp
next
  case (Cons xb xs)
  obtain y c where xb: "xb = (y, c)"
    by force
  have distinct_tail: "distinct (map fst xs)"
    using Cons.prems(1) unfolding xb by simp
  show ?case
  proof (cases "x = y")
    case True
    have x_not_tail: "x \<notin> fst ` set xs"
      using Cons.prems(1) True unfolding xb by simp
    have not_pair_tail: "(x, b) \<notin> set xs"
      using x_not_tail by force
    have c_eq: "c = b"
    proof -
      have "(x, b) = (y, c)"
        using Cons.prems(2) not_pair_tail unfolding xb by auto
      then show ?thesis
        using True by simp
    qed
    have step: "value_of (min_update D y c) x = b"
    proof (cases "x \<in> keys_of D")
      case True
      then have "c < value_of D x"
        using Cons.prems(3) c_eq by simp
      then show ?thesis
        using True \<open>x = y\<close> c_eq min_update_value_key_old[of x D c]
        by simp
    next
      case False
      then show ?thesis
        using \<open>x = y\<close> c_eq min_update_value_key_new[of y D c]
        by simp
    qed
    have tail:
      "value_of (batch_min_update (min_update D y c) xs) x =
        value_of (min_update D y c) x"
      by (rule batch_min_update_value_not_updated[OF x_not_tail])
    show ?thesis
    proof -
      have "value_of (batch_min_update D (xb # xs)) x =
          value_of (batch_min_update (min_update D y c) xs) x"
        unfolding batch_min_update_def xb by simp
      also have "\<dots> = value_of (min_update D y c) x"
        by (rule tail)
      also have "\<dots> = b"
        by (rule step)
      finally show ?thesis .
    qed
  next
    case False
    have pair_tail: "(x, b) \<in> set xs"
      using Cons.prems(2) False unfolding xb by auto
    have better_tail:
      "x \<in> keys_of (min_update D y c) \<Longrightarrow>
        b < value_of (min_update D y c) x"
    proof -
      assume x_in: "x \<in> keys_of (min_update D y c)"
      then have "x \<in> keys_of D"
        using False by simp
      then have "b < value_of D x"
        by (rule Cons.prems(3))
      moreover have "value_of (min_update D y c) x = value_of D x"
        using min_update_value_same[OF False, of D c] .
      ultimately show "b < value_of (min_update D y c) x"
        by simp
    qed
    have tail:
      "value_of (batch_min_update (min_update D y c) xs) x = b"
      by (rule Cons.IH[OF distinct_tail pair_tail better_tail])
    show ?thesis
    proof -
      have "value_of (batch_min_update D (xb # xs)) x =
          value_of (batch_min_update (min_update D y c) xs) x"
        unfolding batch_min_update_def xb by simp
      also have "\<dots> = b"
        by (rule tail)
      finally show ?thesis .
    qed
  qed
qed

definition bmssp_partition_values_match ::
  "nat list \<Rightarrow> nat_dist \<Rightarrow> nat partition_view \<Rightarrow> bool" where
  "bmssp_partition_values_match settled ds D \<longleftrightarrow>
     (\<forall>v d. bmssp_lookup_dist ds v = Some d \<longrightarrow>
       v \<notin> set settled \<longrightarrow> value_of D v = bmssp_partition_key v d)"

lemma bmssp_partition_values_match_initial:
  "bmssp_partition_values_match [] [(src, 0)]
    (bp_view
      (bp_result_of
        (c_bp_regularized_local_insert src (bmssp_partition_key src 0)
          (bp_empty bmssp_block_size bmssp_bound))))"
proof -
  have view:
    "bp_view
      (bp_result_of
        (c_bp_regularized_local_insert src (bmssp_partition_key src 0)
          (bp_empty bmssp_block_size bmssp_bound))) =
      min_update (bp_view (bp_empty bmssp_block_size bmssp_bound))
        src (bmssp_partition_key src 0)"
    by (rule bmssp_initial_partition_bridge(3))
  show ?thesis
    unfolding bmssp_partition_values_match_def view
    by (auto simp: min_update_def)
qed

lemma bmssp_partition_values_match_pull:
  "bmssp_partition_values_match settled ds D \<Longrightarrow>
    value_of Dp = value_of D \<Longrightarrow>
    bmssp_partition_values_match settled ds Dp"
  unfolding bmssp_partition_values_match_def by simp

lemma bmssp_partition_values_match_step:
  fixes old_settled settled vertices :: "nat list"
    and pulled :: "nat list"
    and updates :: "(nat \<times> real) list"
  assumes vals: "bmssp_partition_values_match old_settled ds (bp_view P)"
    and keys: "bmssp_partition_keys_match old_settled ds P"
    and distinct_ds: "distinct (map fst ds)"
    and pulled_def:
      "pulled =
        filter (\<lambda>x. x \<in> S \<and> x \<notin> set old_settled) vertices"
    and settled_def: "settled = pulled @ old_settled"
    and relaxed: "bmssp_relax_vertices G settled pulled ds = (updates, ds')"
    and distinct_updates: "distinct (map fst updates)"
    and pull: "pull_separates (bp_view P) bmssp_block_size B S beta
      (bp_view P1)"
    and view: "bp_view P2 = batch_min_update (bp_view P1) updates"
  shows "bmssp_partition_values_match settled ds' (bp_view P2)"
proof -
  have pull_values: "value_of (bp_view P1) = value_of (bp_view P)"
    using pull unfolding pull_separates_def by simp
  show ?thesis
    unfolding bmssp_partition_values_match_def
  proof (intro allI impI)
    fix v d
    assume lookup': "bmssp_lookup_dist ds' v = Some d"
    assume v_unsettled: "v \<notin> set settled"
    show "value_of (bp_view P2) v = bmssp_partition_key v d"
    proof (cases "v \<in> fst ` set updates")
      case True
      then obtain b where update: "(v, b) \<in> set updates"
        by auto
      have update_rel:
        "(v, b) \<in> set (fst (bmssp_relax_vertices G settled pulled ds))"
        using update relaxed by simp
      have distinct_rel:
        "distinct (map fst (fst (bmssp_relax_vertices G settled pulled ds)))"
        using distinct_updates relaxed by simp
      have lookup_floor:
        "bmssp_lookup_dist ds' v = Some (nat (floor b))"
        using bmssp_relax_vertices_update_lookup_floor
            [OF distinct_rel update_rel] relaxed by simp
      have d_floor: "d = nat (floor b)"
        using lookup' lookup_floor by simp
      obtain du where b_key: "b = bmssp_partition_key v du"
        and du_floor: "nat (floor b) = du"
        using bmssp_relax_vertices_update_floor[OF update_rel] by blast
      have b_d: "b = bmssp_partition_key v d"
        using b_key du_floor d_floor by simp
      have better:
        "v \<in> keys_of (bp_view P1) \<Longrightarrow> b < value_of (bp_view P1) v"
      proof -
        assume vP1: "v \<in> keys_of (bp_view P1)"
        have P1_keys: "keys_of (bp_view P1) = keys_of (bp_view P) - S"
          by (rule pull_separates_remaining_keys[OF pull])
        have vP: "v \<in> keys_of (bp_view P)"
          using vP1 P1_keys by blast
        have v_key_ds: "v \<in> set (map fst ds)"
          using keys vP unfolding bmssp_partition_keys_match_def by blast
        have v_not_old: "v \<notin> set old_settled"
          using keys vP unfolding bmssp_partition_keys_match_def by blast
        obtain old where old_pair: "(v, old) \<in> set ds"
          using v_key_ds by force
        have old_lookup: "bmssp_lookup_dist ds v = Some old"
          by (rule bmssp_lookup_dist_Some_if_distinct_mem
              [OF distinct_ds old_pair])
        have old_value:
          "value_of (bp_view P) v = bmssp_partition_key v old"
          using vals old_lookup v_not_old
          unfolding bmssp_partition_values_match_def by blast
        have du_lt_old: "du < old"
          using bmssp_relax_vertices_update_improves_lookup
              [OF distinct_ds update_rel old_lookup] du_floor by simp
        have "bmssp_partition_key v du < bmssp_partition_key v old"
          by (rule bmssp_partition_key_strict_mono_distance[OF du_lt_old])
        then have "b < value_of (bp_view P) v"
          using b_key old_value by simp
        then show "b < value_of (bp_view P1) v"
          using pull_values by simp
      qed
      have "value_of (bp_view P2) v = b"
        unfolding view
        by (rule batch_min_update_value_pair_less_old
            [OF distinct_updates update better])
      then show ?thesis
        using b_d by simp
    next
      case False
      have lookup_same: "bmssp_lookup_dist ds' v = bmssp_lookup_dist ds v"
        using bmssp_relax_vertices_lookup_not_updated[of v G settled pulled ds]
          False relaxed by simp
      have lookup_old: "bmssp_lookup_dist ds v = Some d"
        using lookup' lookup_same by simp
      have v_not_old: "v \<notin> set old_settled"
        using v_unsettled settled_def by auto
      have old_value:
        "value_of (bp_view P) v = bmssp_partition_key v d"
        using vals lookup_old v_not_old
        unfolding bmssp_partition_values_match_def by blast
      have p2_p1: "value_of (bp_view P2) v = value_of (bp_view P1) v"
        unfolding view
        by (rule batch_min_update_value_not_updated[OF False])
      show ?thesis
        using p2_p1 pull_values old_value by simp
    qed
  qed
qed

lemma bmssp_partition_values_match_loop_step_bridge:
  fixes old_settled settled vertices :: "nat list"
    and pulled :: "nat list"
    and updates :: "(nat \<times> real) list"
  assumes vals: "bmssp_partition_values_match old_settled ds (bp_view P)"
    and keys: "bmssp_partition_keys_match old_settled ds P"
    and distinct_ds: "distinct (map fst ds)"
    and pulled_def:
      "pulled =
        filter (\<lambda>x. x \<in> S \<and> x \<notin> set old_settled) vertices"
    and settled_def: "settled = pulled @ old_settled"
    and relaxed: "bmssp_relax_vertices G settled pulled ds = (updates, ds')"
    and P2_def: "P2 = bmssp_apply_updates updates P1"
    and wf: "nat_graph_well_formed G"
    and distinct_vertices: "distinct vertices"
    and ord: "bp_ordered_invariant P"
    and upper: "partition_upper_bound (bp_view P) B"
    and pull: "bp_pull bmssp_block_size B P = (S, beta, P1)"
  shows "bmssp_partition_values_match settled ds' (bp_view P2)"
proof -
  have updates_def: "updates = fst (bmssp_relax_vertices G settled pulled ds)"
    using relaxed by simp
  have sep:
    "pull_separates (bp_view P) bmssp_block_size B S beta (bp_view P1)"
    by (rule bmssp_loop_partition_step_bridge(1)
        [OF pulled_def updates_def P2_def wf distinct_vertices ord upper pull])
  have distinct_updates: "distinct (map fst updates)"
    by (rule bmssp_loop_partition_step_bridge(5)
        [OF pulled_def updates_def P2_def wf distinct_vertices ord upper pull])
  have view: "bp_view P2 = batch_min_update (bp_view P1) updates"
    by (rule bmssp_loop_partition_step_bridge(7)
        [OF pulled_def updates_def P2_def wf distinct_vertices ord upper pull])
  show ?thesis
    by (rule bmssp_partition_values_match_step
        [OF vals keys distinct_ds pulled_def settled_def relaxed
          distinct_updates sep view])
qed

lemma bmssp_partition_key_le_imp_distance_le:
  assumes "bmssp_partition_key u du \<le> bmssp_partition_key v dv"
  shows "du \<le> dv"
proof (rule ccontr)
  assume "\<not> du \<le> dv"
  then have "dv < du"
    by simp
  then have "bmssp_partition_key v dv < bmssp_partition_key u du"
    by (rule bmssp_partition_key_strict_mono_distance)
  then show False
    using assms by linarith
qed

lemma bmssp_pull_residual_label_le:
  assumes vals: "bmssp_partition_values_match old_settled ds (bp_view P)"
    and keys: "bmssp_partition_keys_match old_settled ds P"
    and pull: "pull_separates (bp_view P) bmssp_block_size B S beta
      (bp_view P1)"
    and uS: "u \<in> S"
    and u_lookup: "bmssp_lookup_dist ds u = Some du"
    and v_lookup: "bmssp_lookup_dist ds v = Some dv"
    and v_unsettled: "v \<notin> set old_settled"
    and v_not_S: "v \<notin> S"
  shows "du \<le> dv"
proof -
  have S_keys: "S \<subseteq> keys_of (bp_view P)"
    by (rule pull_separates_subset[OF pull])
  have u_unsettled: "u \<notin> set old_settled"
    using keys S_keys uS unfolding bmssp_partition_keys_match_def by blast
  have u_value: "value_of (bp_view P) u = bmssp_partition_key u du"
    using vals u_lookup u_unsettled
    unfolding bmssp_partition_values_match_def by blast
  have P1_keys: "keys_of (bp_view P1) = keys_of (bp_view P) - S"
    by (rule pull_separates_remaining_keys[OF pull])
  have v_key: "v \<in> set (map fst ds)"
    using v_lookup by (rule bmssp_lookup_dist_mem_key)
  have vP: "v \<in> keys_of (bp_view P)"
    using keys v_key v_unsettled unfolding bmssp_partition_keys_match_def
    by blast
  have vP1: "v \<in> keys_of (bp_view P1)"
    using P1_keys vP v_not_S by blast
  have v_value: "value_of (bp_view P) v = bmssp_partition_key v dv"
    using vals v_lookup v_unsettled
    unfolding bmssp_partition_values_match_def by blast
  have pull_values: "value_of (bp_view P1) = value_of (bp_view P)"
    using pull unfolding pull_separates_def by simp
  have "value_of (bp_view P) u \<le> value_of (bp_view P1) v"
    by (rule pull_separates_pulled_smallest[OF pull uS vP1])
  then have "bmssp_partition_key u du \<le> bmssp_partition_key v dv"
    using u_value v_value pull_values by simp
  then show ?thesis
    by (rule bmssp_partition_key_le_imp_distance_le)
qed

definition bmssp_partition_state_match ::
  "nat list \<Rightarrow> nat list \<Rightarrow> nat_dist \<Rightarrow> nat bucketed_partition \<Rightarrow> bool" where
  "bmssp_partition_state_match vertices settled ds P \<longleftrightarrow>
     distinct (map fst ds) \<and>
     set (map fst ds) \<subseteq> set vertices \<and>
     bmssp_partition_keys_match settled ds P \<and>
     bmssp_partition_values_match settled ds (bp_view P)"

lemma bmssp_partition_state_match_initial:
  assumes src_vertices: "src \<in> set vertices"
  shows "bmssp_partition_state_match vertices [] [(src, 0)]
    (bp_result_of
      (c_bp_regularized_local_insert src (bmssp_partition_key src 0)
        (bp_empty bmssp_block_size bmssp_bound)))"
proof -
  have distinct: "distinct (map fst [(src, 0)])"
    by simp
  have keys_subset: "set (map fst [(src, 0)]) \<subseteq> set vertices"
    using src_vertices by simp
  have keys:
    "bmssp_partition_keys_match [] [(src, 0)]
      (bp_result_of
        (c_bp_regularized_local_insert src (bmssp_partition_key src 0)
          (bp_empty bmssp_block_size bmssp_bound)))"
    by (rule bmssp_partition_keys_match_initial)
  have vals:
    "bmssp_partition_values_match [] [(src, 0)]
      (bp_view
        (bp_result_of
          (c_bp_regularized_local_insert src (bmssp_partition_key src 0)
            (bp_empty bmssp_block_size bmssp_bound))))"
    by (rule bmssp_partition_values_match_initial)
  show ?thesis
    unfolding bmssp_partition_state_match_def
    using distinct keys_subset keys vals by simp
qed

lemma bmssp_partition_state_match_keys_subset:
  assumes "bmssp_partition_state_match vertices settled ds P"
  shows "keys_of (bp_view P) \<subseteq> set vertices"
proof -
  have keys: "bmssp_partition_keys_match settled ds P"
    and ds_keys: "set (map fst ds) \<subseteq> set vertices"
    using assms unfolding bmssp_partition_state_match_def by auto
  show ?thesis
    using keys ds_keys unfolding bmssp_partition_keys_match_def by blast
qed

lemma bmssp_partition_state_match_step_bridge:
  fixes old_settled settled vertices :: "nat list"
    and pulled :: "nat list"
    and updates :: "(nat \<times> real) list"
  assumes match: "bmssp_partition_state_match vertices old_settled ds P"
    and edge_targets:
      "\<And>a b w. (a, b, w) \<in> set G \<Longrightarrow> b \<in> set vertices"
    and pulled_def:
      "pulled =
        filter (\<lambda>x. x \<in> S \<and> x \<notin> set old_settled) vertices"
    and settled_def: "settled = pulled @ old_settled"
    and relaxed: "bmssp_relax_vertices G settled pulled ds = (updates, ds')"
    and P2_def: "P2 = bmssp_apply_updates updates P1"
    and wf: "nat_graph_well_formed G"
    and distinct_vertices: "distinct vertices"
    and ord: "bp_ordered_invariant P"
    and upper: "partition_upper_bound (bp_view P) B"
    and pull: "bp_pull bmssp_block_size B P = (S, beta, P1)"
  shows "bmssp_partition_state_match vertices settled ds' P2"
proof -
  have distinct_ds: "distinct (map fst ds)"
    and ds_keys: "set (map fst ds) \<subseteq> set vertices"
    and keys: "bmssp_partition_keys_match old_settled ds P"
    and vals: "bmssp_partition_values_match old_settled ds (bp_view P)"
    using match unfolding bmssp_partition_state_match_def by auto
  have pulled_subset: "set pulled \<subseteq> set vertices"
    unfolding pulled_def by auto
  have distinct_ds': "distinct (map fst ds')"
    using bmssp_relax_vertices_preserves_distinct_dist
        [OF distinct_ds, of G settled pulled] relaxed by simp
  have ds'_keys: "set (map fst ds') \<subseteq> set vertices"
  proof -
    have "set (map fst (snd (bmssp_relax_vertices G settled pulled ds)))
        \<subseteq> set vertices"
      by (rule bmssp_relax_vertices_dist_keys_subset
          [OF ds_keys pulled_subset edge_targets])
    then show ?thesis
      using relaxed by simp
  qed
  have keys_vertices: "keys_of (bp_view P) \<subseteq> set vertices"
    by (rule bmssp_partition_state_match_keys_subset[OF match])
  have keys':
    "bmssp_partition_keys_match settled ds' P2"
    by (rule bmssp_partition_keys_match_loop_step_bridge
        [OF keys keys_vertices pulled_def settled_def relaxed P2_def
          wf distinct_vertices ord upper pull])
  have vals':
    "bmssp_partition_values_match settled ds' (bp_view P2)"
    by (rule bmssp_partition_values_match_loop_step_bridge
        [OF vals keys distinct_ds pulled_def settled_def relaxed P2_def
          wf distinct_vertices ord upper pull])
  show ?thesis
    unfolding bmssp_partition_state_match_def
    using distinct_ds' ds'_keys keys' vals' by simp
qed

lemma bmssp_partition_state_pull_residual_label_le:
  assumes match: "bmssp_partition_state_match vertices old_settled ds P"
    and pull: "pull_separates (bp_view P) bmssp_block_size B S beta
      (bp_view P1)"
    and uS: "u \<in> S"
    and u_lookup: "bmssp_lookup_dist ds u = Some du"
    and v_lookup: "bmssp_lookup_dist ds v = Some dv"
    and v_unsettled: "v \<notin> set old_settled"
    and v_not_S: "v \<notin> S"
  shows "du \<le> dv"
proof -
  have vals: "bmssp_partition_values_match old_settled ds (bp_view P)"
    and keys: "bmssp_partition_keys_match old_settled ds P"
    using match unfolding bmssp_partition_state_match_def by auto
  show ?thesis
    by (rule bmssp_pull_residual_label_le
        [OF vals keys pull uS u_lookup v_lookup v_unsettled v_not_S])
qed

lemma bmssp_partition_state_pulled_not_settled:
  assumes match: "bmssp_partition_state_match vertices settled ds P"
    and pull: "pull_separates (bp_view P) bmssp_block_size B S beta D'"
    and uS: "u \<in> S"
  shows "u \<notin> set settled"
proof -
  have keys: "bmssp_partition_keys_match settled ds P"
    using match unfolding bmssp_partition_state_match_def by blast
  have S_keys: "S \<subseteq> keys_of (bp_view P)"
    by (rule pull_separates_subset[OF pull])
  show ?thesis
    using keys S_keys uS unfolding bmssp_partition_keys_match_def by blast
qed

lemma bmssp_partition_state_pulled_lookup:
  assumes match: "bmssp_partition_state_match vertices settled ds P"
    and pull: "pull_separates (bp_view P) bmssp_block_size B S beta D'"
    and uS: "u \<in> S"
  obtains d where "bmssp_lookup_dist ds u = Some d"
proof -
  have distinct_ds: "distinct (map fst ds)"
    and keys: "bmssp_partition_keys_match settled ds P"
    using match unfolding bmssp_partition_state_match_def by auto
  have S_keys: "S \<subseteq> keys_of (bp_view P)"
    by (rule pull_separates_subset[OF pull])
  have u_key: "u \<in> set (map fst ds)"
    using keys S_keys uS unfolding bmssp_partition_keys_match_def by blast
  then obtain d where mem: "(u, d) \<in> set ds"
    by force
  have "bmssp_lookup_dist ds u = Some d"
    by (rule bmssp_lookup_dist_Some_if_distinct_mem[OF distinct_ds mem])
  then show ?thesis
    by (rule that)
qed

lemma bmssp_partition_state_pulled_list_lookup:
  assumes match: "bmssp_partition_state_match vertices old_settled ds P"
    and pull: "pull_separates (bp_view P) bmssp_block_size B S beta D'"
    and pulled_def:
      "pulled =
        filter (\<lambda>x. x \<in> S \<and> x \<notin> set old_settled) vertices"
    and u_pulled: "u \<in> set pulled"
  obtains d where "bmssp_lookup_dist ds u = Some d"
proof -
  have uS: "u \<in> S"
    using u_pulled unfolding pulled_def by auto
  show ?thesis
    by (rule bmssp_partition_state_pulled_lookup
        [OF match pull uS that])
qed

lemma nat_graph_edge_in_vertices:
  assumes "(u, v) \<in> nat_graph_edges G"
  shows "u \<in> nat_graph_vertices G" "v \<in> nat_graph_vertices G"
  using assms
  unfolding nat_graph_edges_def nat_graph_edge_list_def nat_graph_vertices_def
  by auto

lemma nat_graph_weight_nonneg [simp]:
  "0 \<le> nat_graph_weight G u v"
proof (cases "map_of
    (map (\<lambda>e. ((nat_edge_source e, nat_edge_target e),
             real (nat_edge_weight e))) G) (u, v)")
  case None
  then show ?thesis
    unfolding nat_graph_weight_def by simp
next
  case (Some c)
  then have "((u, v), c) \<in> set
      (map (\<lambda>e. ((nat_edge_source e, nat_edge_target e),
             real (nat_edge_weight e))) G)"
    by (rule map_of_SomeD)
  then show ?thesis
    using Some unfolding nat_graph_weight_def by auto
qed

lemma bmssp_edge_vertices_set:
  "set (concat (map bmssp_edge_vertices G)) = nat_graph_vertices G"
  unfolding nat_graph_vertices_def
  by (induction G) (auto split: prod.splits)

lemma bmssp_vertices_set:
  "set (bmssp_vertices G src) = insert src (nat_graph_vertices G)"
  unfolding bmssp_vertices_def using bmssp_edge_vertices_set[of G] by auto

lemma bmssp_vertices_set_if_source:
  assumes "src \<in> nat_graph_vertices G"
  shows "set (bmssp_vertices G src) = nat_graph_vertices G"
  using bmssp_vertices_set[of G src] assms by auto

lemma bmssp_edge_target_in_vertices:
  assumes "(a, b, w) \<in> set G"
  shows "b \<in> set (bmssp_vertices G src)"
proof -
  have "b \<in> nat_graph_vertices G"
    using assms unfolding nat_graph_vertices_def by force
  then show ?thesis
    using bmssp_vertices_set[of G src] by auto
qed

lemma bmssp_lookup_dist_Some_mem:
  assumes "bmssp_lookup_dist ds v = Some d"
  shows "(v, d) \<in> set ds"
  using assms
proof (induction ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ds)
  obtain x e where p: "p = (x, e)"
    by (cases p)
  show ?case
  proof (cases "v = x")
    case True
    then show ?thesis
      using Cons.prems unfolding p by simp
  next
    case False
    then have "bmssp_lookup_dist ds v = Some d"
      using Cons.prems unfolding p by simp
    then have "(v, d) \<in> set ds"
      by (rule Cons.IH)
    then show ?thesis
      unfolding p by simp
  qed
qed

lemma bmssp_set_dist_mem_cases:
  assumes "(v, d) \<in> set (bmssp_set_dist x dx ds)"
  shows "(v = x \<and> d = dx) \<or> (v, d) \<in> set ds"
  using assms
proof (induction ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ds)
  obtain y e where p: "p = (y, e)"
    by (cases p)
  show ?case
  proof (cases "x = y")
    case True
    then show ?thesis
      using Cons.prems unfolding p by auto
  next
    case False
    then have mem:
      "(v, d) = (y, e) \<or> (v, d) \<in> set (bmssp_set_dist x dx ds)"
      using Cons.prems unfolding p by auto
    then show ?thesis
    proof
      assume "(v, d) = (y, e)"
      then show ?thesis
        using False unfolding p by auto
    next
      assume "(v, d) \<in> set (bmssp_set_dist x dx ds)"
      then show ?thesis
        using Cons.IH by auto
    qed
  qed
qed

lemma nat_graph_weight_of_edge:
  assumes wf: "nat_graph_well_formed G"
    and edge: "(u, v, w) \<in> set G"
  shows "nat_graph_weight G u v = real w"
proof -
  let ?xs =
    "map (\<lambda>e. ((nat_edge_source e, nat_edge_target e),
       real (nat_edge_weight e))) G"
  have distinct_edges: "distinct (nat_graph_edge_list G)"
    by (rule nat_graph_well_formed_distinct_edge_list[OF wf])
  have fst_xs: "map fst ?xs = nat_graph_edge_list G"
    unfolding nat_graph_edge_list_def by (induction G) auto
  have distinct_xs: "distinct (map fst ?xs)"
    using distinct_edges unfolding fst_xs .
  have mem: "((u, v), real w) \<in> set ?xs"
    using edge by force
  have "map_of ?xs (u, v) = Some (real w)"
    using map_of_eq_Some_iff[OF distinct_xs] mem by blast
  then show ?thesis
    unfolding nat_graph_weight_def by simp
qed

lemma exec_walk_append_edge:
  assumes walk: "exec_walk vs es p"
    and p_ne: "p \<noteq> []"
    and last_p: "last p = u"
    and vV: "v \<in> set vs"
    and edge: "(u, v) \<in> set es"
  shows "exec_walk vs es (p @ [v])"
proof -
  obtain x xs where p_def: "p = x # xs"
    using p_ne by (cases p) auto
  have aux:
    "\<And>x u. \<lbrakk>exec_walk vs es (x # xs); last (x # xs) = u;
      (u, v) \<in> set es\<rbrakk> \<Longrightarrow>
      exec_walk vs es ((x # xs) @ [v])"
  proof (induction xs)
    case Nil
    then show ?case
      using vV by simp
  next
    case (Cons y ys)
    have tail_walk: "exec_walk vs es (y # ys)"
      using Cons.prems by simp
    have tail_last: "last (y # ys) = u"
      using Cons.prems by simp
    have tail_app: "exec_walk vs es ((y # ys) @ [v])"
      by (rule Cons.IH[OF tail_walk tail_last Cons.prems(3)])
    show ?case
      using Cons.prems tail_app by simp
  qed
  show ?thesis
    unfolding p_def
    by (rule aux[OF _ _ edge]) (use walk last_p p_def in simp_all)
qed

lemma exec_walk_weight_append_edge:
  assumes "p \<noteq> []"
  shows "exec_walk_weight W (p @ [v]) =
    exec_walk_weight W p + W (last p) v"
  using assms
proof (induction W p rule: exec_walk_weight.induct)
  case (1 W)
  then show ?case
    by simp
next
  case (2 W x)
  then show ?case
    by simp
next
  case (3 W x y xs)
  have tail: "exec_walk_weight W ((y # xs) @ [v]) =
      exec_walk_weight W (y # xs) + W (last (y # xs)) v"
    by (rule "3.IH") simp
  then show ?case
    by simp
qed

fun exec_path_edges where
  "exec_path_edges [] = []"
| "exec_path_edges [x] = []"
| "exec_path_edges (x # y # xs) = (x, y) # exec_path_edges (y # xs)"

lemma exec_walk_path_edges_subset:
  assumes "exec_walk vs es p"
  shows "set (exec_path_edges p) \<subseteq> set es"
  using assms by (induction p rule: exec_path_edges.induct) auto

lemma exec_path_edges_vertices:
  assumes "e \<in> set (exec_path_edges p)"
  shows "fst e \<in> set p" "snd e \<in> set p"
  using assms by (induction p rule: exec_path_edges.induct) auto

lemma exec_path_edges_distinct_if_distinct:
  assumes "distinct p"
  shows "distinct (exec_path_edges p)"
  using assms
proof (induction p rule: exec_path_edges.induct)
  case 1
  then show ?case
    by simp
next
  case (2 x)
  then show ?case
    by simp
next
  case (3 x y xs)
  have "(x, y) \<notin> set (exec_path_edges (y # xs))"
  proof
    assume edge: "(x, y) \<in> set (exec_path_edges (y # xs))"
    then have "x \<in> set (y # xs)"
      using exec_path_edges_vertices(1)[OF edge] by simp
    then show False
      using "3.prems" by simp
  qed
  moreover have "distinct (exec_path_edges (y # xs))"
    using "3.IH" "3.prems" by simp
  ultimately show ?case
    by simp
qed

lemma exec_walk_weight_sum_path_edges:
  "exec_walk_weight W p =
    sum_list (map (\<lambda>e. W (fst e) (snd e)) (exec_path_edges p))"
  by (induction p rule: exec_path_edges.induct) simp_all

lemma nat_graph_weight_edge_list_sum:
  assumes wf: "nat_graph_well_formed G"
  shows "sum_list
      (map (\<lambda>e. nat_graph_weight G (fst e) (snd e))
        (nat_graph_edge_list G)) =
    real (nat_graph_total_weight G)"
proof -
  have weights:
    "\<And>e. e \<in> set G \<Longrightarrow>
      nat_graph_weight G (nat_edge_source e) (nat_edge_target e) =
        real (nat_edge_weight e)"
  proof -
    fix e
    assume e: "e \<in> set G"
    obtain u v w where e_def: "e = (u, v, w)"
      by (cases e)
    show "nat_graph_weight G (nat_edge_source e) (nat_edge_target e) =
        real (nat_edge_weight e)"
      unfolding e_def
      by (rule nat_graph_weight_of_edge[OF wf]) (use e e_def in simp)
  qed
  have "sum_list
      (map (\<lambda>e. nat_graph_weight G (fst e) (snd e))
        (nat_graph_edge_list G)) =
    sum_list
      (map (\<lambda>e. nat_graph_weight G (nat_edge_source e)
        (nat_edge_target e)) G)"
    unfolding nat_graph_edge_list_def by (simp add: o_def)
  also have "\<dots> = sum_list (map (\<lambda>e. real (nat_edge_weight e)) G)"
  proof -
    have aux: "\<And>xs. set xs \<subseteq> set G \<Longrightarrow>
      sum_list (map (\<lambda>e. nat_graph_weight G (nat_edge_source e)
          (nat_edge_target e)) xs) =
      sum_list (map (\<lambda>e. real (nat_edge_weight e)) xs)"
    proof -
      fix xs
      assume "set xs \<subseteq> set G"
      then show "sum_list (map (\<lambda>e. nat_graph_weight G
            (nat_edge_source e) (nat_edge_target e)) xs) =
          sum_list (map (\<lambda>e. real (nat_edge_weight e)) xs)"
        by (induction xs) (auto simp: weights)
    qed
    show ?thesis
      by (rule aux) simp
  qed
  also have "\<dots> = real (sum_list (map nat_edge_weight G))"
    by (induction G) auto
  finally show ?thesis
    unfolding nat_graph_total_weight_def .
qed

lemma nat_graph_weight_nonnegative:
  "0 \<le> nat_graph_weight G u v"
proof (cases "map_of
    (map (\<lambda>e. ((nat_edge_source e, nat_edge_target e),
             real (nat_edge_weight e))) G) (u, v)")
  case None
  then show ?thesis
    unfolding nat_graph_weight_def by simp
next
  case (Some c)
  then have "((u, v), c) \<in> set
      (map (\<lambda>e. ((nat_edge_source e, nat_edge_target e),
             real (nat_edge_weight e))) G)"
    by (rule map_of_SomeD)
  then obtain e where "e \<in> set G"
    and c: "c = real (nat_edge_weight e)"
    by auto
  then show ?thesis
    unfolding nat_graph_weight_def using Some by simp
qed

lemma exec_walk_weight_nat_graph_le_total:
  assumes wf: "nat_graph_well_formed G"
    and walk: "exec_walk vs (nat_graph_edge_list G) p"
    and distinct: "distinct p"
  shows "exec_walk_weight (nat_graph_weight G) p \<le>
    real (nat_graph_total_weight G)"
proof -
  let ?w = "\<lambda>e. nat_graph_weight G (fst e) (snd e)"
  have path_subset: "set (exec_path_edges p) \<subseteq> set (nat_graph_edge_list G)"
    by (rule exec_walk_path_edges_subset[OF walk])
  have path_distinct: "distinct (exec_path_edges p)"
    by (rule exec_path_edges_distinct_if_distinct[OF distinct])
  have graph_distinct: "distinct (nat_graph_edge_list G)"
    by (rule nat_graph_well_formed_distinct_edge_list[OF wf])
  have path_sum:
    "sum_list (map ?w (exec_path_edges p)) =
      sum ?w (set (exec_path_edges p))"
    by (rule sum_list_distinct_conv_sum_set[OF path_distinct])
  have graph_sum:
    "sum_list (map ?w (nat_graph_edge_list G)) =
      sum ?w (set (nat_graph_edge_list G))"
    by (rule sum_list_distinct_conv_sum_set[OF graph_distinct])
  have finite_graph: "finite (set (nat_graph_edge_list G))"
    by (rule finite_set)
  have "sum ?w (set (exec_path_edges p)) \<le>
      sum ?w (set (nat_graph_edge_list G))"
    by (rule sum_mono2[OF finite_graph path_subset])
      (simp add: nat_graph_weight_nonnegative)
  also have "\<dots> = real (nat_graph_total_weight G)"
    using graph_sum nat_graph_weight_edge_list_sum[OF wf] by simp
  finally have "sum_list (map ?w (exec_path_edges p)) \<le>
      real (nat_graph_total_weight G)"
    using path_sum by simp
  then show ?thesis
    unfolding exec_walk_weight_sum_path_edges .
qed

definition bmssp_label_witnesses ::
  "nat_graph \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat_dist \<Rightarrow> bool" where
  "bmssp_label_witnesses G src settled ds \<longleftrightarrow>
     (\<forall>v d. (v, d) \<in> set ds \<longrightarrow>
       (\<exists>p. p \<noteq> [] \<and> hd p = src \<and> last p = v \<and> distinct p \<and>
         exec_walk (bmssp_vertices G src) (nat_graph_edge_list G) p \<and>
         exec_walk_weight (nat_graph_weight G) p = real d \<and>
         set (butlast p) \<subseteq> set settled))"

lemma bmssp_label_witnesses_mono_settled:
  assumes witnesses: "bmssp_label_witnesses G src settled ds"
    and subset: "set settled \<subseteq> set settled'"
  shows "bmssp_label_witnesses G src settled' ds"
  unfolding bmssp_label_witnesses_def
proof (intro allI impI)
  fix v d
  assume "(v, d) \<in> set ds"
  then obtain p where p:
    "p \<noteq> []" "hd p = src" "last p = v" "distinct p"
    "exec_walk (bmssp_vertices G src) (nat_graph_edge_list G) p"
    "exec_walk_weight (nat_graph_weight G) p = real d"
    "set (butlast p) \<subseteq> set settled"
    using witnesses unfolding bmssp_label_witnesses_def by blast
  have "set (butlast p) \<subseteq> set settled'"
    using p(7) subset by blast
  then show "\<exists>p. p \<noteq> [] \<and> hd p = src \<and> last p = v \<and> distinct p \<and>
      exec_walk (bmssp_vertices G src) (nat_graph_edge_list G) p \<and>
      exec_walk_weight (nat_graph_weight G) p = real d \<and>
      set (butlast p) \<subseteq> set settled'"
    using p(1-6) by blast
qed

lemma bmssp_label_witnesses_initial:
  "bmssp_label_witnesses G src [] [(src, 0)]"
  unfolding bmssp_label_witnesses_def
  by (intro allI impI, auto simp: bmssp_vertices_set intro!: exI[of _ "[src]"])

lemma bmssp_label_witnesses_set_dist:
  assumes witnesses: "bmssp_label_witnesses G src settled ds"
    and p: "p \<noteq> []" "hd p = src" "last p = x" "distinct p"
      "exec_walk (bmssp_vertices G src) (nat_graph_edge_list G) p"
      "exec_walk_weight (nat_graph_weight G) p = real dx"
      "set (butlast p) \<subseteq> set settled"
  shows "bmssp_label_witnesses G src settled (bmssp_set_dist x dx ds)"
  unfolding bmssp_label_witnesses_def
proof (intro allI impI)
  fix v d
  assume mem: "(v, d) \<in> set (bmssp_set_dist x dx ds)"
  consider (new) "v = x" "d = dx" | (old) "(v, d) \<in> set ds"
    using bmssp_set_dist_mem_cases[OF mem] by blast
  then show "\<exists>p. p \<noteq> [] \<and> hd p = src \<and> last p = v \<and> distinct p \<and>
      exec_walk (bmssp_vertices G src) (nat_graph_edge_list G) p \<and>
      exec_walk_weight (nat_graph_weight G) p = real d \<and>
      set (butlast p) \<subseteq> set settled"
  proof cases
    case new
    then show ?thesis
      using p by blast
  next
    case old
    then show ?thesis
      using witnesses unfolding bmssp_label_witnesses_def by blast
  qed
qed

lemma bmssp_relax_edges_lookup_settled:
  assumes "v \<in> set settled"
  shows "bmssp_lookup_dist (snd (bmssp_relax_edges G settled u du ds)) v =
    bmssp_lookup_dist ds v"
  using assms
proof (induction G arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons e es)
  obtain a b w where e: "e = (a, b, w)"
    by (cases e)
  obtain updates ds1 where rec:
    "bmssp_relax_edges es settled u du ds = (updates, ds1)"
    by force
  have lookup_tail: "bmssp_lookup_dist ds1 v = bmssp_lookup_dist ds v"
    using Cons.IH[OF Cons.prems, of ds] rec by simp
  show ?case
  proof (cases "a = u \<and> b \<notin> set settled")
    case False
    then show ?thesis
      using rec lookup_tail unfolding e
      by (auto simp: Let_def split: option.splits if_splits)
  next
    case True
    then have b_ne_v: "b \<noteq> v"
      using Cons.prems by auto
    show ?thesis
    proof (cases "bmssp_lookup_dist ds1 b")
      case None
      then show ?thesis
        using True rec lookup_tail b_ne_v
        unfolding e by (simp add: Let_def bmssp_lookup_dist_set_dist_other)
    next
      case (Some old)
      show ?thesis
      proof (cases "du + w < old")
        case True
        then show ?thesis
          using \<open>a = u \<and> b \<notin> set settled\<close> rec Some lookup_tail b_ne_v
          unfolding e by (simp add: Let_def bmssp_lookup_dist_set_dist_other)
      next
        case False
        then show ?thesis
          using \<open>a = u \<and> b \<notin> set settled\<close> rec Some lookup_tail
          unfolding e by (simp add: Let_def)
      qed
    qed
  qed
qed

lemma bmssp_relax_vertices_lookup_settled:
  assumes "v \<in> set settled"
  shows "bmssp_lookup_dist (snd (bmssp_relax_vertices G settled xs ds)) v =
    bmssp_lookup_dist ds v"
proof (induction xs arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons u us)
  show ?case
  proof (cases "bmssp_lookup_dist ds u")
    case None
    then show ?thesis
      using Cons.IH by simp
  next
    case (Some du)
    obtain updates_u ds1 where edge_rec:
      "bmssp_relax_edges G settled u du ds = (updates_u, ds1)"
      by force
    have lookup_ds1:
      "bmssp_lookup_dist ds1 v = bmssp_lookup_dist ds v"
      using bmssp_relax_edges_lookup_settled[OF assms, of G u du ds]
        edge_rec by simp
    obtain updates_us ds2 where vertices_rec:
      "bmssp_relax_vertices G settled us ds1 = (updates_us, ds2)"
      by force
    have lookup_ds2:
      "bmssp_lookup_dist ds2 v = bmssp_lookup_dist ds1 v"
      using Cons.IH[of ds1] vertices_rec by simp
    show ?thesis
      using Some edge_rec vertices_rec lookup_ds1 lookup_ds2 by simp
  qed
qed

lemma bmssp_relax_vertices_edge_lookup_le_candidate:
  assumes distinct: "distinct (map fst ds)"
    and xs_subset: "set xs \<subseteq> set settled"
    and u_xs: "u \<in> set xs"
    and lookup_u: "bmssp_lookup_dist ds u = Some du"
    and edge: "(u, v, w) \<in> set G"
    and v_unsettled: "v \<notin> set settled"
  shows "\<exists>dv.
    bmssp_lookup_dist (snd (bmssp_relax_vertices G settled xs ds)) v =
      Some dv \<and>
    dv \<le> du + w"
  using distinct xs_subset u_xs lookup_u
proof (induction xs arbitrary: ds du)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "bmssp_lookup_dist ds x")
    case None
    have u_ne_x: "u \<noteq> x"
      using None Cons.prems(4) by auto
    then have u_tail: "u \<in> set xs"
      using Cons.prems(3) by simp
    obtain dv where tail_lookup:
        "bmssp_lookup_dist
          (snd (bmssp_relax_vertices G settled xs ds)) v = Some dv"
      and tail_le: "dv \<le> du + w"
      using Cons.IH[OF Cons.prems(1) _ u_tail Cons.prems(4)]
      using Cons.prems(2) by auto
    have final_lookup:
      "bmssp_lookup_dist
        (snd (bmssp_relax_vertices G settled (x # xs) ds)) v = Some dv"
      using None tail_lookup by simp
    show ?thesis
      using final_lookup tail_le by blast
  next
    case (Some dx)
    obtain updates_x ds1 where edge_rec:
      "bmssp_relax_edges G settled x dx ds = (updates_x, ds1)"
      by force
    have distinct_ds1: "distinct (map fst ds1)"
      using bmssp_relax_edges_preserves_distinct_dist[OF Cons.prems(1),
          of G settled x dx] edge_rec by simp
    have xs_subset: "set xs \<subseteq> set settled"
      using Cons.prems(2) by simp
    obtain updates_xs ds2 where vertices_rec:
      "bmssp_relax_vertices G settled xs ds1 = (updates_xs, ds2)"
      by force
    show ?thesis
    proof (cases "u = x")
      case True
      then have du_eq: "du = dx"
        using Some Cons.prems(4) by simp
      have edge_x: "(x, v, w) \<in> set G"
        using edge True by simp
      obtain mid where mid_lookup:
          "bmssp_lookup_dist (snd (bmssp_relax_edges G settled x dx ds)) v =
            Some mid"
        and mid_le: "mid \<le> dx + w"
        using bmssp_relax_edges_edge_lookup_le_candidate
            [OF edge_x v_unsettled, of dx ds]
        by blast
      have mid_ds1: "bmssp_lookup_dist ds1 v = Some mid"
        using mid_lookup edge_rec by simp
      obtain dv where final_lookup:
          "bmssp_lookup_dist
            (snd (bmssp_relax_vertices G settled xs ds1)) v = Some dv"
        using bmssp_relax_vertices_lookup_Some_preserved
            [OF distinct_ds1 mid_ds1]
        by blast
      have dv_le_mid:
        "dv \<le> mid"
        by (rule bmssp_relax_vertices_lookup_le
            [OF distinct_ds1 mid_ds1 final_lookup])
      have "dv \<le> du + w"
        using dv_le_mid mid_le du_eq by linarith
      then show ?thesis
        using Some edge_rec vertices_rec final_lookup by auto
    next
      case False
      have u_tail: "u \<in> set xs"
        using Cons.prems(3) False by simp
      have u_settled: "u \<in> set settled"
        using xs_subset u_tail by blast
      have lookup_u_ds1: "bmssp_lookup_dist ds1 u = Some du"
        using bmssp_relax_edges_lookup_settled[OF u_settled, of G x dx ds]
          Cons.prems(4) edge_rec by simp
      obtain dv where final_lookup:
          "bmssp_lookup_dist
            (snd (bmssp_relax_vertices G settled xs ds1)) v = Some dv"
        and final_le: "dv \<le> du + w"
        using Cons.IH[OF distinct_ds1 xs_subset u_tail lookup_u_ds1]
        by blast
      show ?thesis
        using Some edge_rec vertices_rec final_lookup final_le by auto
    qed
  qed
qed

definition bmssp_settled_exact ::
  "nat_graph \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat_dist \<Rightarrow> bool" where
  "bmssp_settled_exact G src settled ds \<longleftrightarrow>
     (\<forall>v d. v \<in> set settled \<longrightarrow>
       bmssp_lookup_dist ds v = Some d \<longrightarrow>
       real d = nat_graph_dist G src v)"

lemma bmssp_settled_exact_initial:
  "bmssp_settled_exact G src [] ds"
  unfolding bmssp_settled_exact_def by simp

lemma bmssp_settled_exact_step:
  assumes exact_old: "bmssp_settled_exact G src old_settled ds"
    and pulled_exact:
      "\<And>v d. \<lbrakk>v \<in> set pulled; bmssp_lookup_dist ds v = Some d\<rbrakk>
        \<Longrightarrow> real d = nat_graph_dist G src v"
    and settled_def: "settled = pulled @ old_settled"
    and relaxed: "bmssp_relax_vertices G settled pulled ds = (updates, ds')"
  shows "bmssp_settled_exact G src settled ds'"
  unfolding bmssp_settled_exact_def
proof (intro allI impI)
  fix v d
  assume v_settled: "v \<in> set settled"
    and lookup': "bmssp_lookup_dist ds' v = Some d"
  have lookup_old: "bmssp_lookup_dist ds v = Some d"
    using bmssp_relax_vertices_lookup_settled[OF v_settled, of G pulled ds]
      relaxed lookup' by simp
  have "v \<in> set pulled \<or> v \<in> set old_settled"
    using v_settled settled_def by auto
  then show "real d = nat_graph_dist G src v"
  proof
    assume "v \<in> set pulled"
    then show ?thesis
      by (rule pulled_exact[OF _ lookup_old])
  next
    assume "v \<in> set old_settled"
    then show ?thesis
      using exact_old lookup_old unfolding bmssp_settled_exact_def by blast
  qed
qed

definition bmssp_frontier_relaxed ::
  "nat_graph \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat_dist \<Rightarrow> bool" where
  "bmssp_frontier_relaxed G src settled ds \<longleftrightarrow>
     (\<forall>u v w du. (u, v, w) \<in> set G \<longrightarrow>
       u \<in> set settled \<longrightarrow>
       v \<notin> set settled \<longrightarrow>
       bmssp_lookup_dist ds u = Some du \<longrightarrow>
       real du = nat_graph_dist G src u \<longrightarrow>
       (\<exists>dv. bmssp_lookup_dist ds v = Some dv \<and>
         real dv \<le> real du + real w))"

lemma bmssp_frontier_relaxed_initial:
  "bmssp_frontier_relaxed G src [] ds"
  unfolding bmssp_frontier_relaxed_def by simp

lemma bmssp_frontier_relaxed_step:
  assumes frontier_old: "bmssp_frontier_relaxed G src old_settled ds"
    and distinct: "distinct (map fst ds)"
    and settled_def: "settled = pulled @ old_settled"
    and relaxed: "bmssp_relax_vertices G settled pulled ds = (updates, ds')"
  shows "bmssp_frontier_relaxed G src settled ds'"
  unfolding bmssp_frontier_relaxed_def
proof (intro allI impI)
  fix u v w du
  assume edge: "(u, v, w) \<in> set G"
    and u_settled: "u \<in> set settled"
    and v_unsettled: "v \<notin> set settled"
    and lookup_u': "bmssp_lookup_dist ds' u = Some du"
    and exact_u: "real du = nat_graph_dist G src u"
  have lookup_u: "bmssp_lookup_dist ds u = Some du"
    using bmssp_relax_vertices_lookup_settled[OF u_settled, of G pulled ds]
      relaxed lookup_u' by simp
  have u_cases: "u \<in> set pulled \<or> u \<in> set old_settled"
    using u_settled settled_def by auto
  show "\<exists>dv. bmssp_lookup_dist ds' v = Some dv \<and>
      real dv \<le> real du + real w"
  proof (cases "u \<in> set old_settled")
    case True
    have v_old_unsettled: "v \<notin> set old_settled"
      using v_unsettled settled_def by auto
    obtain old_dv where old_lookup:
        "bmssp_lookup_dist ds v = Some old_dv"
      and old_le: "real old_dv \<le> real du + real w"
      using frontier_old edge True v_old_unsettled lookup_u exact_u
      unfolding bmssp_frontier_relaxed_def by blast
    obtain dv where final_lookup:
        "bmssp_lookup_dist
          (snd (bmssp_relax_vertices G settled pulled ds)) v = Some dv"
      using bmssp_relax_vertices_lookup_Some_preserved
          [OF distinct old_lookup]
      by blast
    have dv_le_old: "dv \<le> old_dv"
      by (rule bmssp_relax_vertices_lookup_le
          [OF distinct old_lookup final_lookup])
    have "real dv \<le> real du + real w"
      using dv_le_old old_le by linarith
    then show ?thesis
      using final_lookup relaxed by auto
  next
    case False
    then have u_pulled: "u \<in> set pulled"
      using u_cases by blast
    have pulled_subset: "set pulled \<subseteq> set settled"
      using settled_def by auto
    obtain dv where lookup:
        "bmssp_lookup_dist
          (snd (bmssp_relax_vertices G settled pulled ds)) v = Some dv"
      and dv_le: "dv \<le> du + w"
      using bmssp_relax_vertices_edge_lookup_le_candidate
          [OF distinct pulled_subset u_pulled lookup_u edge v_unsettled]
      by blast
    have "real dv \<le> real du + real w"
      using dv_le by simp
    then show ?thesis
      using lookup relaxed by auto
  qed
qed

definition bmssp_source_zero :: "nat \<Rightarrow> nat_dist \<Rightarrow> bool" where
  "bmssp_source_zero src ds \<longleftrightarrow> bmssp_lookup_dist ds src = Some 0"

lemma bmssp_source_zero_initial:
  "bmssp_source_zero src [(src, 0)]"
  unfolding bmssp_source_zero_def by simp

lemma bmssp_source_zero_step:
  assumes zero: "bmssp_source_zero src ds"
    and distinct: "distinct (map fst ds)"
    and relaxed: "bmssp_relax_vertices G settled pulled ds = (updates, ds')"
  shows "bmssp_source_zero src ds'"
proof -
  have lookup0: "bmssp_lookup_dist ds src = Some 0"
    using zero unfolding bmssp_source_zero_def .
  obtain d' where lookup':
    "bmssp_lookup_dist
      (snd (bmssp_relax_vertices G settled pulled ds)) src = Some d'"
    using bmssp_relax_vertices_lookup_Some_preserved[OF distinct lookup0]
    by blast
  have "d' \<le> 0"
    by (rule bmssp_relax_vertices_lookup_le[OF distinct lookup0 lookup'])
  then have "d' = 0"
    by simp
  then show ?thesis
    using lookup' relaxed unfolding bmssp_source_zero_def by simp
qed

definition bmssp_settled_have_lookups ::
  "nat list \<Rightarrow> nat_dist \<Rightarrow> bool" where
  "bmssp_settled_have_lookups settled ds \<longleftrightarrow>
     (\<forall>v\<in>set settled. \<exists>d. bmssp_lookup_dist ds v = Some d)"

lemma bmssp_settled_have_lookups_initial:
  "bmssp_settled_have_lookups [] ds"
  unfolding bmssp_settled_have_lookups_def by simp

lemma bmssp_settled_have_lookups_step:
  assumes have_old: "bmssp_settled_have_lookups old_settled ds"
    and match: "bmssp_partition_state_match vertices old_settled ds P"
    and pull: "pull_separates (bp_view P) bmssp_block_size B S beta D'"
    and pulled_def:
      "pulled = filter (\<lambda>x. x \<in> S \<and> x \<notin> set old_settled) vertices"
    and settled_def: "settled = pulled @ old_settled"
    and relaxed: "bmssp_relax_vertices G settled pulled ds = (updates, ds')"
  shows "bmssp_settled_have_lookups settled ds'"
  unfolding bmssp_settled_have_lookups_def
proof
  fix v
  assume v_settled: "v \<in> set settled"
  have v_cases: "v \<in> set pulled \<or> v \<in> set old_settled"
    using v_settled settled_def by auto
  then obtain d where lookup: "bmssp_lookup_dist ds v = Some d"
  proof
    assume v_pulled: "v \<in> set pulled"
    obtain d where "bmssp_lookup_dist ds v = Some d"
      by (rule bmssp_partition_state_pulled_list_lookup
          [OF match pull pulled_def v_pulled])
    then show ?thesis ..
  next
    assume "v \<in> set old_settled"
    then obtain d where "bmssp_lookup_dist ds v = Some d"
      using have_old unfolding bmssp_settled_have_lookups_def by blast
    then show ?thesis ..
  qed
  have lookup':
    "bmssp_lookup_dist
      (snd (bmssp_relax_vertices G settled pulled ds)) v =
      bmssp_lookup_dist ds v"
    by (rule bmssp_relax_vertices_lookup_settled[OF v_settled])
  show "\<exists>d. bmssp_lookup_dist ds' v = Some d"
    using lookup lookup' relaxed by simp
qed

lemma finite_card_le_one_member_eq:
  assumes finite: "finite A"
    and card: "card A \<le> 1"
    and x: "x \<in> A"
    and y: "y \<in> A"
  shows "x = y"
proof (rule ccontr)
  assume "x \<noteq> y"
  then have "card {x, y} = 2"
    by simp
  moreover have "{x, y} \<subseteq> A"
    using x y by blast
  ultimately have "2 \<le> card A"
    using card_mono[OF finite, of "{x, y}"] by simp
  then show False
    using card by simp
qed

definition bmssp_dijkstra_state ::
  "nat_graph \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat_dist \<Rightarrow> nat bucketed_partition \<Rightarrow> bool" where
  "bmssp_dijkstra_state G src vertices settled ds P \<longleftrightarrow>
     bmssp_partition_state_match vertices settled ds P \<and>
     bmssp_source_zero src ds \<and>
     bmssp_settled_have_lookups settled ds \<and>
     bmssp_label_witnesses G src settled ds \<and>
     bmssp_settled_exact G src settled ds \<and>
     bmssp_frontier_relaxed G src settled ds"

lemma bmssp_dijkstra_state_initial:
  assumes src_vertices: "src \<in> set vertices"
  shows "bmssp_dijkstra_state G src vertices [] [(src, 0)]
    (bp_result_of
      (c_bp_regularized_local_insert src (bmssp_partition_key src 0)
        (bp_empty bmssp_block_size bmssp_bound)))"
proof -
  have match:
    "bmssp_partition_state_match vertices [] [(src, 0)]
      (bp_result_of
        (c_bp_regularized_local_insert src (bmssp_partition_key src 0)
          (bp_empty bmssp_block_size bmssp_bound)))"
    by (rule bmssp_partition_state_match_initial[OF src_vertices])
  show ?thesis
    unfolding bmssp_dijkstra_state_def
    using match bmssp_source_zero_initial
      bmssp_settled_have_lookups_initial bmssp_label_witnesses_initial
      bmssp_settled_exact_initial bmssp_frontier_relaxed_initial
    by simp
qed

lemma bmssp_relax_edges_preserves_label_witnesses_aux:
  assumes wf: "nat_graph_well_formed Gfull"
    and edge_subset: "set Erel \<subseteq> set Gfull"
    and witnesses: "bmssp_label_witnesses Gfull src settled ds"
    and u_settled: "u \<in> set settled"
    and lookup_u: "bmssp_lookup_dist ds u = Some du"
  shows "bmssp_label_witnesses Gfull src settled
    (snd (bmssp_relax_edges Erel settled u du ds))"
  using edge_subset witnesses lookup_u
proof (induction Erel arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons e es)
  obtain a b w where e_def: "e = (a, b, w)"
    by (cases e)
  obtain updates ds1 where rec:
    "bmssp_relax_edges es settled u du ds = (updates, ds1)"
    by force
  have es_subset: "set es \<subseteq> set Gfull"
    using Cons.prems(1) by simp
  have tail_witnesses: "bmssp_label_witnesses Gfull src settled ds1"
    using Cons.IH[OF es_subset Cons.prems(2) Cons.prems(3)] rec by simp
  have lookup_u_ds1: "bmssp_lookup_dist ds1 u = Some du"
    using bmssp_relax_edges_lookup_settled[OF u_settled, of es u du ds]
      Cons.prems(3) rec by simp
  show ?case
  proof (cases "a = u \<and> b \<notin> set settled")
    case False
    then show ?thesis
      using rec tail_witnesses unfolding e_def
      by (auto simp: Let_def split: option.splits if_splits)
  next
    case True
    note active = True
    let ?nd = "du + w"
    have edge_rel: "(u, b, w) \<in> set (e # es)"
      using active unfolding e_def by simp
    have edge_mem: "(u, b, w) \<in> set Gfull"
      using Cons.prems(1) edge_rel by blast
    have edge_pair: "(u, b) \<in> set (nat_graph_edge_list Gfull)"
      unfolding nat_graph_edge_list_def using edge_mem by force
    have b_vertex: "b \<in> set (bmssp_vertices Gfull src)"
      by (rule bmssp_edge_target_in_vertices[OF edge_mem])
    have weight_b: "nat_graph_weight Gfull u b = real w"
      by (rule nat_graph_weight_of_edge[OF wf edge_mem])
    have u_mem: "(u, du) \<in> set ds1"
      by (rule bmssp_lookup_dist_Some_mem[OF lookup_u_ds1])
    obtain p where p:
      "p \<noteq> []" "hd p = src" "last p = u" "distinct p"
      "exec_walk (bmssp_vertices Gfull src)
        (nat_graph_edge_list Gfull) p"
      "exec_walk_weight (nat_graph_weight Gfull) p = real du"
      "set (butlast p) \<subseteq> set settled"
      using tail_witnesses u_mem unfolding bmssp_label_witnesses_def by blast
    have set_p: "set p \<subseteq> set settled"
    proof
      fix x
      assume x: "x \<in> set p"
      have "p = butlast p @ [last p]"
        using p(1) by simp
      then have "x \<in> set (butlast p @ [last p])"
        using x by simp
      then have "x \<in> set (butlast p) \<union> {last p}"
        by (simp only: set_append set_simps)
      then have "x \<in> set (butlast p) \<or> x = last p"
        by blast
      then show "x \<in> set settled"
      proof
        assume "x \<in> set (butlast p)"
        then show ?thesis
          using p(7) by blast
      next
        assume "x = last p"
        then show ?thesis
          using p(3) u_settled by simp
      qed
    qed
    have b_not_p: "b \<notin> set p"
      using active set_p by auto
    have walk_pb:
      "exec_walk (bmssp_vertices Gfull src)
        (nat_graph_edge_list Gfull) (p @ [b])"
      by (rule exec_walk_append_edge[OF p(5) p(1) p(3) b_vertex edge_pair])
    have distinct_pb: "distinct (p @ [b])"
      using p(4) b_not_p by simp
    have weight_pb:
      "exec_walk_weight (nat_graph_weight Gfull) (p @ [b]) = real ?nd"
      using exec_walk_weight_append_edge[OF p(1), of "nat_graph_weight Gfull" b]
        p(3,6) weight_b by simp
    have butlast_pb: "set (butlast (p @ [b])) \<subseteq> set settled"
      using p(1) set_p by simp
    have new_witnesses:
      "bmssp_label_witnesses Gfull src settled
        (bmssp_set_dist b ?nd ds1)"
      by (rule bmssp_label_witnesses_set_dist
          [OF tail_witnesses, of "p @ [b]" b ?nd])
        (use p(1,2) active walk_pb distinct_pb weight_pb butlast_pb in auto)
    show ?thesis
    proof (cases "bmssp_lookup_dist ds1 b")
      case None
      then show ?thesis
        using active rec new_witnesses unfolding e_def by (simp add: Let_def)
    next
      case (Some old)
      show ?thesis
      proof (cases "?nd < old")
        case True
        then show ?thesis
          using active rec Some new_witnesses unfolding e_def
          by (simp add: Let_def)
      next
        case False
        then show ?thesis
          using active rec Some tail_witnesses unfolding e_def
          by (simp add: Let_def)
      qed
    qed
  qed
qed

lemma bmssp_relax_edges_preserves_label_witnesses:
  assumes wf: "nat_graph_well_formed G"
    and witnesses: "bmssp_label_witnesses G src settled ds"
    and u_settled: "u \<in> set settled"
    and lookup_u: "bmssp_lookup_dist ds u = Some du"
  shows "bmssp_label_witnesses G src settled
    (snd (bmssp_relax_edges G settled u du ds))"
  by (rule bmssp_relax_edges_preserves_label_witnesses_aux
      [OF wf _ witnesses u_settled lookup_u]) simp

lemma bmssp_relax_vertices_preserves_label_witnesses:
  assumes wf: "nat_graph_well_formed G"
    and witnesses: "bmssp_label_witnesses G src settled ds"
    and xs_subset: "set xs \<subseteq> set settled"
  shows "bmssp_label_witnesses G src settled
    (snd (bmssp_relax_vertices G settled xs ds))"
  using witnesses xs_subset
proof (induction xs arbitrary: ds)
  case Nil
  then show ?case
    by simp
next
  case (Cons u us)
  show ?case
  proof (cases "bmssp_lookup_dist ds u")
    case None
    have us_subset: "set us \<subseteq> set settled"
      using Cons.prems(2) by simp
    show ?thesis
      using None Cons.IH[OF Cons.prems(1) us_subset] by simp
  next
    case (Some du)
    have u_settled: "u \<in> set settled"
      using Cons.prems(2) by simp
    obtain updates_u ds1 where edge_rec:
      "bmssp_relax_edges G settled u du ds = (updates_u, ds1)"
      by force
    have witnesses1: "bmssp_label_witnesses G src settled ds1"
      using bmssp_relax_edges_preserves_label_witnesses
        [OF wf Cons.prems(1) u_settled Some] edge_rec by simp
    obtain updates_us ds2 where vertices_rec:
      "bmssp_relax_vertices G settled us ds1 = (updates_us, ds2)"
      by force
    have us_subset: "set us \<subseteq> set settled"
      using Cons.prems(2) by simp
    have witnesses2: "bmssp_label_witnesses G src settled ds2"
      using Cons.IH[OF witnesses1 us_subset] vertices_rec by simp
    show ?thesis
      using Some edge_rec vertices_rec witnesses2 by simp
  qed
qed

lemma bmssp_label_witnesses_lookup_lt_infinity:
  assumes wf: "nat_graph_well_formed G"
    and witnesses: "bmssp_label_witnesses G src settled ds"
    and lookup: "bmssp_lookup_dist ds v = Some d"
  shows "d < bmssp_infinity"
proof -
  have mem: "(v, d) \<in> set ds"
    by (rule bmssp_lookup_dist_Some_mem[OF lookup])
  then obtain p where p:
    "distinct p"
    "exec_walk (bmssp_vertices G src) (nat_graph_edge_list G) p"
    "exec_walk_weight (nat_graph_weight G) p = real d"
    using witnesses unfolding bmssp_label_witnesses_def by blast
  have d_le_total:
    "real d \<le> real (nat_graph_total_weight G)"
    using exec_walk_weight_nat_graph_le_total[OF wf p(2) p(1)] p(3)
    by simp
  have total_lt: "nat_graph_total_weight G < bmssp_infinity"
    using wf unfolding nat_graph_well_formed_def by simp
  show ?thesis
    using d_le_total total_lt by linarith
qed

lemma bmssp_relax_vertices_update_lt_bound:
  assumes wf: "nat_graph_well_formed G"
    and witnesses: "bmssp_label_witnesses G src settled ds"
    and xs_subset: "set xs \<subseteq> set settled"
    and distinct_updates:
      "distinct (map fst (fst (bmssp_relax_vertices G settled xs ds)))"
    and update: "(v, b) \<in> set (fst (bmssp_relax_vertices G settled xs ds))"
  shows "b < bmssp_bound"
proof -
  have witnesses':
    "bmssp_label_witnesses G src settled
      (snd (bmssp_relax_vertices G settled xs ds))"
    by (rule bmssp_relax_vertices_preserves_label_witnesses
        [OF wf witnesses xs_subset])
  have lookup:
    "bmssp_lookup_dist (snd (bmssp_relax_vertices G settled xs ds)) v =
      Some (nat (floor b))"
    by (rule bmssp_relax_vertices_update_lookup_floor
        [OF distinct_updates update])
  have d_lt: "nat (floor b) < bmssp_infinity"
    by (rule bmssp_label_witnesses_lookup_lt_infinity
        [OF wf witnesses' lookup])
  obtain d where b_key: "b = bmssp_partition_key v d"
    and d_floor: "nat (floor b) = d"
    using bmssp_relax_vertices_update_floor[OF update] by blast
  have key_lt: "bmssp_partition_key v d < bmssp_bound"
    by (rule bmssp_partition_key_lt_bound_if_distance_lt)
      (use d_lt d_floor in simp)
  show ?thesis
    using b_key key_lt by simp
qed

lemma bmssp_loop_lookup_settled:
  assumes distinct: "distinct (map fst ds)"
    and v_settled: "v \<in> set settled"
  shows "bmssp_lookup_dist (bmssp_loop fuel G vertices settled ds P) v =
    bmssp_lookup_dist ds v"
  using distinct v_settled
proof (induction fuel arbitrary: settled ds P)
  case 0
  then show ?case
    by (simp add: bmssp_lookup_dist_normalize_dist)
next
  case (Suc fuel)
  obtain S beta P1 where pull:
    "bp_pull bmssp_block_size bmssp_bound P = (S, beta, P1)"
    by (cases "bp_pull bmssp_block_size bmssp_bound P") auto
  let ?pulled = "filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices"
  show ?case
  proof (cases "?pulled = []")
    case True
    then show ?thesis
      using pull Suc.prems by (simp add: bmssp_lookup_dist_normalize_dist)
  next
    case False
    let ?settled' = "?pulled @ settled"
    have v_settled': "v \<in> set ?settled'"
      using Suc.prems by simp
    obtain updates ds' where relaxed:
      "bmssp_relax_vertices G ?settled' ?pulled ds = (updates, ds')"
      by force
    have lookup_ds':
      "bmssp_lookup_dist ds' v = bmssp_lookup_dist ds v"
      using bmssp_relax_vertices_lookup_settled[OF v_settled', of G ?pulled ds]
        relaxed by simp
    have distinct_ds':
      "distinct (map fst ds')"
      using bmssp_relax_vertices_preserves_distinct_dist[OF Suc.prems(1),
          of G ?settled' ?pulled] relaxed by simp
    have rec:
      "bmssp_lookup_dist
        (bmssp_loop fuel G vertices ?settled' ds'
          (bmssp_apply_updates updates P1)) v =
        bmssp_lookup_dist ds' v"
      by (rule Suc.IH[OF distinct_ds' v_settled'])
    have loop_eq:
      "bmssp_loop (Suc fuel) G vertices settled ds P =
        bmssp_loop fuel G vertices ?settled' ds'
          (bmssp_apply_updates updates P1)"
      using pull False relaxed by (simp add: Let_def)
    show ?thesis
      using loop_eq rec lookup_ds' by simp
  qed
qed

lemma bmssp_loop_preserves_label_witnesses:
  assumes wf: "nat_graph_well_formed G"
    and witnesses: "bmssp_label_witnesses G src settled ds"
  shows "\<exists>settled'. set settled \<subseteq> set settled' \<and>
    bmssp_label_witnesses G src settled'
      (bmssp_loop fuel G vertices settled ds P)"
  using witnesses
proof (induction fuel arbitrary: settled ds P)
  case 0
  have set_norm: "set (bmssp_normalize_dist ds) = set ds"
    unfolding bmssp_normalize_dist_def by simp
  have witnesses_norm:
    "bmssp_label_witnesses G src settled (bmssp_normalize_dist ds)"
    using "0.prems" set_norm unfolding bmssp_label_witnesses_def by auto
  show ?case
  proof (intro exI conjI)
    show "set settled \<subseteq> set settled"
      by simp
    show "bmssp_label_witnesses G src settled
        (bmssp_loop 0 G vertices settled ds P)"
      using witnesses_norm by simp
  qed
next
  case (Suc fuel)
  obtain S beta P1 where pull:
    "bp_pull bmssp_block_size bmssp_bound P = (S, beta, P1)"
    by (cases "bp_pull bmssp_block_size bmssp_bound P") auto
  let ?pulled = "filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices"
  show ?case
  proof (cases "?pulled = []")
    case True
    have set_norm: "set (bmssp_normalize_dist ds) = set ds"
      unfolding bmssp_normalize_dist_def by simp
    have witnesses_norm:
      "bmssp_label_witnesses G src settled (bmssp_normalize_dist ds)"
      using Suc.prems set_norm unfolding bmssp_label_witnesses_def by auto
    have loop_eq:
      "bmssp_loop (Suc fuel) G vertices settled ds P =
        bmssp_normalize_dist ds"
      using pull True by simp
    show ?thesis
    proof (intro exI conjI)
      show "set settled \<subseteq> set settled"
        by simp
      show "bmssp_label_witnesses G src settled
          (bmssp_loop (Suc fuel) G vertices settled ds P)"
        using witnesses_norm loop_eq by simp
    qed
  next
    case False
    let ?settled' = "?pulled @ settled"
    have settled_subset: "set settled \<subseteq> set ?settled'"
      by auto
    have witnesses_settled':
      "bmssp_label_witnesses G src ?settled' ds"
      by (rule bmssp_label_witnesses_mono_settled
          [OF Suc.prems settled_subset])
    have pulled_subset: "set ?pulled \<subseteq> set ?settled'"
      by simp
    obtain updates ds' where relaxed:
      "bmssp_relax_vertices G ?settled' ?pulled ds = (updates, ds')"
      by force
    have witnesses_ds':
      "bmssp_label_witnesses G src ?settled' ds'"
      using bmssp_relax_vertices_preserves_label_witnesses
        [OF wf witnesses_settled' pulled_subset] relaxed by simp
    obtain settled'' where settled'':
      "set ?settled' \<subseteq> set settled''"
      "bmssp_label_witnesses G src settled''
        (bmssp_loop fuel G vertices ?settled' ds'
          (bmssp_apply_updates updates P1))"
      using Suc.IH[OF witnesses_ds'] by blast
    have loop_eq:
      "bmssp_loop (Suc fuel) G vertices settled ds P =
        bmssp_loop fuel G vertices ?settled' ds'
          (bmssp_apply_updates updates P1)"
      using pull False relaxed by (simp add: Let_def)
    have settled_to_final: "set settled \<subseteq> set settled''"
      using settled_subset settled''(1) by blast
    show ?thesis
    proof (intro exI conjI)
      show "set settled \<subseteq> set settled''"
        by (rule settled_to_final)
      show "bmssp_label_witnesses G src settled''
          (bmssp_loop (Suc fuel) G vertices settled ds P)"
        using settled''(2) loop_eq by simp
    qed
  qed
qed

lemma bmssp_distances_label_witnesses:
  assumes wf: "nat_graph_well_formed G"
  shows "\<exists>settled. bmssp_label_witnesses G src settled
    (bmssp_distances G src)"
proof -
  let ?vertices = "bmssp_vertices G src"
  let ?P0 = "bp_empty bmssp_block_size bmssp_bound"
  let ?P1 =
    "bp_regularized_local_insert src (bmssp_partition_key src 0) ?P0"
  let ?fuel = "Suc (length ?vertices * Suc (length G))"
  have initial: "bmssp_label_witnesses G src [] [(src, 0)]"
    by (rule bmssp_label_witnesses_initial)
  obtain settled where loop:
    "bmssp_label_witnesses G src settled
      (bmssp_loop ?fuel G ?vertices [] [(src, 0)] ?P1)"
    using bmssp_loop_preserves_label_witnesses[OF wf initial] by blast
  have unfold:
    "bmssp_distances G src =
      bmssp_loop ?fuel G ?vertices [] [(src, 0)] ?P1"
    unfolding bmssp_distances_def by (simp add: Let_def)
  show ?thesis
  proof
    show "bmssp_label_witnesses G src settled (bmssp_distances G src)"
      using loop unfold by simp
  qed
qed

lemma bmssp_distances_output_simple_walk:
  assumes wf: "nat_graph_well_formed G"
    and mem: "(v, d) \<in> set (bmssp_distances G src)"
  obtains p where
    "p \<noteq> []"
    "hd p = src"
    "last p = v"
    "distinct p"
    "exec_walk (bmssp_vertices G src) (nat_graph_edge_list G) p"
    "exec_walk_weight (nat_graph_weight G) p = real d"
proof -
  obtain settled where witnesses:
    "bmssp_label_witnesses G src settled (bmssp_distances G src)"
    using bmssp_distances_label_witnesses[OF wf] by blast
  then obtain p where
    "p \<noteq> []"
    "hd p = src"
    "last p = v"
    "distinct p"
    "exec_walk (bmssp_vertices G src) (nat_graph_edge_list G) p"
    "exec_walk_weight (nat_graph_weight G) p = real d"
    using mem unfolding bmssp_label_witnesses_def by blast
  then show ?thesis
    using that by blast
qed

lemma bmssp_distances_distinct_keys:
  "distinct (map fst (bmssp_distances G src))"
proof -
  let ?vertices = "bmssp_vertices G src"
  let ?P0 = "bp_empty bmssp_block_size bmssp_bound"
  let ?P1 =
    "bp_result_of
      (c_bp_regularized_local_insert src (bmssp_partition_key src 0) ?P0)"
  let ?fuel = "Suc (length ?vertices * Suc (length G))"
  have unfold:
    "bmssp_distances G src =
      bmssp_loop ?fuel G ?vertices [] [(src, 0)] ?P1"
    unfolding bmssp_distances_def by (simp add: Let_def)
  have distinct_loop:
    "distinct
      (map fst (bmssp_loop ?fuel G ?vertices [] [(src, 0)] ?P1))"
    by (rule bmssp_loop_preserves_distinct_output) simp
  show ?thesis
    using unfold distinct_loop by simp
qed

lemma bmssp_distances_keys_subset_bmssp_vertices:
  "set (map fst (bmssp_distances G src)) \<subseteq> set (bmssp_vertices G src)"
proof -
  let ?vertices = "bmssp_vertices G src"
  let ?P0 = "bp_empty bmssp_block_size bmssp_bound"
  let ?P1 =
    "bp_result_of
      (c_bp_regularized_local_insert src (bmssp_partition_key src 0) ?P0)"
  let ?fuel = "Suc (length ?vertices * Suc (length G))"
  have initial: "set (map fst [(src, 0)]) \<subseteq> set ?vertices"
    unfolding bmssp_vertices_def by simp
  have targets:
    "\<And>a b w. (a, b, w) \<in> set G \<Longrightarrow> b \<in> set ?vertices"
    by (rule bmssp_edge_target_in_vertices)
  have "set (map fst
      (bmssp_loop ?fuel G ?vertices [] [(src, 0)] ?P1))
      \<subseteq> set ?vertices"
    by (rule bmssp_loop_output_keys_subset_vertices[OF initial targets])
  then show ?thesis
    unfolding bmssp_distances_def by (simp add: Let_def)
qed

lemma bmssp_distances_encode_own_keys:
  "bmssp_distances G src =
    encode_dist_assoc_list (map fst (bmssp_distances G src))
      (executable_label_of (bmssp_distances G src))"
proof -
  let ?vertices = "bmssp_vertices G src"
  let ?P0 = "bp_empty bmssp_block_size bmssp_bound"
  let ?P1 =
    "bp_result_of
      (c_bp_regularized_local_insert src (bmssp_partition_key src 0) ?P0)"
  let ?fuel = "Suc (length ?vertices * Suc (length G))"
  have loop:
    "bmssp_loop ?fuel G ?vertices [] [(src, 0)] ?P1 =
      encode_dist_assoc_list
        (map fst (bmssp_loop ?fuel G ?vertices [] [(src, 0)] ?P1))
        (executable_label_of
          (bmssp_loop ?fuel G ?vertices [] [(src, 0)] ?P1))"
    by (rule bmssp_loop_output_encode) simp
  show ?thesis
    using loop unfolding bmssp_distances_def by (simp add: Let_def)
qed

lemma nat_graph_finite_weighted_digraph:
  assumes wf: "nat_graph_well_formed G"
    and src: "src \<in> nat_graph_vertices G"
  shows "finite_weighted_digraph
    (nat_graph_vertices G) (nat_graph_edges G) (nat_graph_weight G) src"
proof
  show "finite (nat_graph_vertices G)"
    unfolding nat_graph_vertices_def by simp
  show "src \<in> nat_graph_vertices G"
    by (rule src)
  show "\<And>u v. (u, v) \<in> nat_graph_edges G \<Longrightarrow>
    u \<in> nat_graph_vertices G \<and> v \<in> nat_graph_vertices G"
    using nat_graph_edge_in_vertices by blast
  show "\<And>u v. (u, v) \<in> nat_graph_edges G \<Longrightarrow>
    0 \<le> nat_graph_weight G u v"
    by simp
qed

lemma nat_graph_reachable_iff_exec_reachable:
  assumes wf: "nat_graph_well_formed G"
    and src: "src \<in> nat_graph_vertices G"
  shows "exec_reachable (nat_graph_vertex_list G) (nat_graph_edge_list G) a b
    \<longleftrightarrow> nat_graph_reachable G a b"
proof -
  interpret concrete: finite_weighted_digraph
    "nat_graph_vertices G" "nat_graph_edges G" "nat_graph_weight G" src
    by (rule nat_graph_finite_weighted_digraph[OF wf src])
  have exec:
      "exec_reachable (nat_graph_vertex_list G) (nat_graph_edge_list G) a b
        \<longleftrightarrow> concrete.reachable a b"
    by (rule concrete.exec_reachable_iff_reachable
        [OF nat_graph_vertex_list_set nat_graph_edge_list_set])
  show ?thesis
    using exec unfolding nat_graph_reachable_def .
qed

lemma nat_graph_exec_dist_eq_dist:
  assumes wf: "nat_graph_well_formed G"
    and src: "src \<in> nat_graph_vertices G"
    and reach: "nat_graph_reachable G a b"
  shows "exec_dist (nat_graph_vertex_list G) (nat_graph_edge_list G)
      (nat_graph_weight G) a b =
    nat_graph_dist G a b"
proof -
  interpret concrete: finite_weighted_digraph
    "nat_graph_vertices G" "nat_graph_edges G" "nat_graph_weight G" src
    by (rule nat_graph_finite_weighted_digraph[OF wf src])
  have reach': "concrete.reachable a b"
    using reach unfolding nat_graph_reachable_def .
  show ?thesis
    unfolding nat_graph_dist_def
    by (rule concrete.exec_dist_eq_dist[OF nat_graph_vertex_list_set
          nat_graph_edge_list_set reach'])
qed

lemma nat_graph_weight_integral:
  "\<exists>n. nat_graph_weight G u v = real n"
proof (cases "map_of
    (map (\<lambda>e. ((nat_edge_source e, nat_edge_target e),
             real (nat_edge_weight e))) G) (u, v)")
  case None
  then show ?thesis
    unfolding nat_graph_weight_def by simp
next
  case (Some c)
  then have "((u, v), c) \<in> set
      (map (\<lambda>e. ((nat_edge_source e, nat_edge_target e),
             real (nat_edge_weight e))) G)"
    by (rule map_of_SomeD)
  then obtain e where "e \<in> set G"
    and c: "c = real (nat_edge_weight e)"
    by auto
  then show ?thesis
    unfolding nat_graph_weight_def using Some by auto
qed

lemma exec_walk_weight_nat_graph_integral:
  "\<exists>n. exec_walk_weight (nat_graph_weight G) p = real n"
proof (induction p)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      by simp
  next
    case (Cons y ys)
    obtain n where w: "nat_graph_weight G x y = real n"
      using nat_graph_weight_integral[of G x y] by blast
    obtain m where tail:
        "exec_walk_weight (nat_graph_weight G) (y # ys) = real m"
      using Cons.IH Cons by blast
    have "exec_walk_weight (nat_graph_weight G) (x # y # ys) =
        real (n + m)"
      using w tail by simp
    then show ?thesis
      using Cons by blast
  qed
qed

lemma min_list_integral_nonempty:
  assumes "xs \<noteq> []"
    and "\<And>x. x \<in> set xs \<Longrightarrow> \<exists>n. x = real n"
  shows "\<exists>n. min_list xs = real n"
  using assms
proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  obtain n where x: "x = real n"
    using Cons.prems(2) by auto
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      using x by simp
  next
    case (Cons y ys)
    have tail_nonempty: "xs \<noteq> []"
      using Cons by simp
    have tail_integral: "\<And>z. z \<in> set xs \<Longrightarrow> \<exists>m. z = real m"
      using Cons.prems by simp
    obtain m where tail: "min_list xs = real m"
      using Cons.IH[OF tail_nonempty tail_integral] by blast
    have "min_list (x # xs) = min x (min_list xs)"
      using Cons by simp
    also have "\<dots> = real (min n m)"
      using x tail by simp
    finally have "min_list (x # xs) = real (min n m)" .
    then show ?thesis
      by blast
  qed
qed

lemma exec_dist_nat_graph_integral:
  "\<exists>n. exec_dist vs es (nat_graph_weight G) a b = real n"
proof (cases "exec_walk_weights vs es (nat_graph_weight G) a b")
  case Nil
  then show ?thesis
    unfolding exec_dist_def by simp
next
  case (Cons w ws)
  have integral:
    "\<And>x. x \<in> set (w # ws) \<Longrightarrow> \<exists>n. x = real n"
  proof -
    fix x
    assume "x \<in> set (w # ws)"
    then obtain p where
      "p \<in> set (exec_simple_walks_betw vs es a b)"
      and x: "x = exec_walk_weight (nat_graph_weight G) p"
      unfolding Cons[symmetric] exec_walk_weights_def by auto
    then show "\<exists>n. x = real n"
      using exec_walk_weight_nat_graph_integral[of G p] by blast
  qed
  have nonempty: "w # ws \<noteq> []"
    by simp
  obtain n where "min_list (w # ws) = real n"
    using min_list_integral_nonempty[OF nonempty integral] by blast
  then show ?thesis
    unfolding exec_dist_def Cons by simp
qed

lemma nat_graph_dist_integral:
  assumes wf: "nat_graph_well_formed G"
    and src: "src \<in> nat_graph_vertices G"
    and reach: "nat_graph_reachable G a b"
  shows "\<exists>n. nat_graph_dist G a b = real n"
proof -
  have exec_eq:
    "exec_dist (nat_graph_vertex_list G) (nat_graph_edge_list G)
        (nat_graph_weight G) a b =
      nat_graph_dist G a b"
    by (rule nat_graph_exec_dist_eq_dist[OF wf src reach])
  obtain n where "exec_dist (nat_graph_vertex_list G) (nat_graph_edge_list G)
      (nat_graph_weight G) a b = real n"
    using exec_dist_nat_graph_integral by blast
  then have "nat_graph_dist G a b = real n"
    using exec_eq by simp
  then show ?thesis
    by blast
qed

lemma real_nat_floor_integral:
  assumes "\<exists>n::nat. x = real n"
  shows "real (nat (floor x)) = x"
  using assms by auto

locale nat_graph_instance =
  fixes G :: nat_graph
    and src :: nat
  assumes wf: "nat_graph_well_formed G"
    and src_in: "src \<in> nat_graph_vertices G"
begin

interpretation concrete: finite_weighted_digraph
  "nat_graph_vertices G" "nat_graph_edges G" "nat_graph_weight G" src
  by (rule nat_graph_finite_weighted_digraph[OF wf src_in])

lemma exec_reachable_iff_reachable:
  "exec_reachable (nat_graph_vertex_list G) (nat_graph_edge_list G) a b
    \<longleftrightarrow> concrete.reachable a b"
  by (rule concrete.exec_reachable_iff_reachable
      [OF nat_graph_vertex_list_set nat_graph_edge_list_set])

lemma exec_dist_eq_dist:
  assumes "concrete.reachable a b"
  shows "exec_dist (nat_graph_vertex_list G) (nat_graph_edge_list G)
      (nat_graph_weight G) a b =
    concrete.dist a b"
  by (rule concrete.exec_dist_eq_dist[OF nat_graph_vertex_list_set
        nat_graph_edge_list_set assms])

lemma bmssp_vertices_carrier:
  "set (bmssp_vertices G src) = nat_graph_vertices G"
  using bmssp_vertices_set_if_source[OF src_in] .

lemma bmssp_distances_keys_subset_carrier:
  "set (map fst (bmssp_distances G src)) \<subseteq> nat_graph_vertices G"
  using bmssp_distances_keys_subset_bmssp_vertices[of G src]
    bmssp_vertices_carrier by simp

lemma bmssp_distances_encode_filtered_vertex_list:
  "bmssp_distances G src =
    encode_dist_assoc_list
      (filter (\<lambda>v. v \<in> set (map fst (bmssp_distances G src)))
        (nat_graph_vertex_list G))
      (executable_label_of (bmssp_distances G src))"
proof -
  let ?U = "set (map fst (bmssp_distances G src))"
  have filter_set:
    "set (filter (\<lambda>v. v \<in> ?U) (nat_graph_vertex_list G)) =
      set (map fst (bmssp_distances G src))"
    using bmssp_distances_keys_subset_carrier by auto
  have own:
    "bmssp_distances G src =
      encode_dist_assoc_list (map fst (bmssp_distances G src))
        (executable_label_of (bmssp_distances G src))"
    by (rule bmssp_distances_encode_own_keys)
  have encode_eq:
    "encode_dist_assoc_list
      (filter (\<lambda>v. v \<in> ?U) (nat_graph_vertex_list G))
      (executable_label_of (bmssp_distances G src)) =
      encode_dist_assoc_list (map fst (bmssp_distances G src))
        (executable_label_of (bmssp_distances G src))"
    by (rule encode_dist_assoc_list_cong_set[OF filter_set])
  show ?thesis
    using own encode_eq by simp
qed

lemma bmssp_distances_output_abstract_simple_walk:
  assumes mem: "(v, d) \<in> set (bmssp_distances G src)"
  obtains p where
    "concrete.simple_walk_betw src p v"
    "concrete.walk_weight p = real d"
proof -
  obtain p where p:
    "p \<noteq> []"
    "hd p = src"
    "last p = v"
    "distinct p"
    "exec_walk (bmssp_vertices G src) (nat_graph_edge_list G) p"
    "exec_walk_weight (nat_graph_weight G) p = real d"
    by (rule bmssp_distances_output_simple_walk[OF wf mem])
  have walk_p: "concrete.walk p"
    using p(5)
    by (simp add: concrete.exec_walk_iff_walk
        [OF bmssp_vertices_carrier nat_graph_edge_list_set])
  have simple: "concrete.simple_walk_betw src p v"
    using p(1-4) walk_p
    unfolding concrete.simple_walk_betw_def concrete.walk_betw_def by blast
  have weight: "concrete.walk_weight p = real d"
    using p(6) by simp
  show ?thesis
    by (rule that[OF simple weight])
qed

lemma bmssp_distances_output_reachable:
  assumes "(v, d) \<in> set (bmssp_distances G src)"
  shows "nat_graph_reachable G src v"
proof -
  obtain p where "concrete.simple_walk_betw src p v"
    by (rule bmssp_distances_output_abstract_simple_walk[OF assms])
  then have "concrete.reachable src v"
    unfolding concrete.reachable_def by blast
  then show ?thesis
    unfolding nat_graph_reachable_def .
qed

lemma bmssp_distances_output_dist_le:
  assumes mem: "(v, d) \<in> set (bmssp_distances G src)"
  shows "nat_graph_dist G src v \<le> real d"
proof -
  obtain p where simple: "concrete.simple_walk_betw src p v"
    and weight: "concrete.walk_weight p = real d"
    by (rule bmssp_distances_output_abstract_simple_walk[OF mem])
  have weight_mem:
    "real d \<in> concrete.simple_walk_weights src v"
  proof -
    have "concrete.walk_weight p \<in> concrete.walk_weight `
        {p. concrete.simple_walk_betw src p v}"
      using simple by blast
    then show ?thesis
      using weight unfolding concrete.simple_walk_weights_def by simp
  qed
  have "concrete.dist src v \<le> real d"
    unfolding concrete.dist_def
    by (rule Min_le[OF concrete.finite_simple_walk_weights weight_mem])
  then show ?thesis
    unfolding nat_graph_dist_def by simp
qed

lemma bmssp_label_witnesses_lookup_abstract_simple_walk:
  assumes witnesses: "bmssp_label_witnesses G src settled ds"
    and lookup: "bmssp_lookup_dist ds v = Some d"
  obtains p where
    "concrete.simple_walk_betw src p v"
    "concrete.walk_weight p = real d"
proof -
  have mem: "(v, d) \<in> set ds"
    by (rule bmssp_lookup_dist_Some_mem[OF lookup])
  then obtain p where p:
    "p \<noteq> []"
    "hd p = src"
    "last p = v"
    "distinct p"
    "exec_walk (bmssp_vertices G src) (nat_graph_edge_list G) p"
    "exec_walk_weight (nat_graph_weight G) p = real d"
    using witnesses unfolding bmssp_label_witnesses_def by blast
  have walk_p: "concrete.walk p"
    using p(5)
    by (simp add: concrete.exec_walk_iff_walk
        [OF bmssp_vertices_carrier nat_graph_edge_list_set])
  have simple: "concrete.simple_walk_betw src p v"
    using p(1-4) walk_p
    unfolding concrete.simple_walk_betw_def concrete.walk_betw_def by blast
  have weight: "concrete.walk_weight p = real d"
    using p(6) by simp
  show ?thesis
    by (rule that[OF simple weight])
qed

lemma bmssp_label_witnesses_lookup_reachable:
  assumes witnesses: "bmssp_label_witnesses G src settled ds"
    and lookup: "bmssp_lookup_dist ds v = Some d"
  shows "nat_graph_reachable G src v"
proof -
  obtain p where "concrete.simple_walk_betw src p v"
    by (rule bmssp_label_witnesses_lookup_abstract_simple_walk
        [OF witnesses lookup])
  then have "concrete.reachable src v"
    unfolding concrete.reachable_def by blast
  then show ?thesis
    unfolding nat_graph_reachable_def .
qed

lemma bmssp_label_witnesses_lookup_dist_le:
  assumes witnesses: "bmssp_label_witnesses G src settled ds"
    and lookup: "bmssp_lookup_dist ds v = Some d"
  shows "nat_graph_dist G src v \<le> real d"
proof -
  obtain p where simple: "concrete.simple_walk_betw src p v"
    and weight: "concrete.walk_weight p = real d"
    by (rule bmssp_label_witnesses_lookup_abstract_simple_walk
        [OF witnesses lookup])
  have weight_mem:
    "real d \<in> concrete.simple_walk_weights src v"
  proof -
    have "concrete.walk_weight p \<in> concrete.walk_weight `
        {p. concrete.simple_walk_betw src p v}"
      using simple by blast
    then show ?thesis
      using weight unfolding concrete.simple_walk_weights_def by simp
  qed
  have "concrete.dist src v \<le> real d"
    unfolding concrete.dist_def
    by (rule Min_le[OF concrete.finite_simple_walk_weights weight_mem])
  then show ?thesis
    unfolding nat_graph_dist_def by simp
qed

lemma bmssp_shortest_walk_first_unsettled_lookup_le_dist:
  assumes sp: "concrete.shortest_walk src p u"
    and u_unsettled: "u \<notin> set settled"
    and source_zero: "bmssp_source_zero src ds"
    and settled_lookup: "bmssp_settled_have_lookups settled ds"
    and exact: "bmssp_settled_exact G src settled ds"
    and frontier: "bmssp_frontier_relaxed G src settled ds"
  obtains y dy where
    "y \<in> set p"
    "y \<notin> set settled"
    "bmssp_lookup_dist ds y = Some dy"
    "real dy \<le> nat_graph_dist G src y"
    "nat_graph_dist G src y \<le> nat_graph_dist G src u"
proof -
  have p_ne: "p \<noteq> []" and hd_p: "hd p = src" and last_p: "last p = u"
    using concrete.shortest_walk_hd[OF sp] by blast+
  have last_idx: "length p - 1 < length p"
    using p_ne by simp
  have last_nth: "p ! (length p - 1) = u"
    using last_conv_nth[OF p_ne] last_p by simp
  let ?P = "\<lambda>i. i < length p \<and> p ! i \<notin> set settled"
  have ex_unsettled: "\<exists>i. ?P i"
    using last_idx last_nth u_unsettled by blast
  define i where "i = (LEAST i. ?P i)"
  have i_props: "i < length p" "p ! i \<notin> set settled"
    using LeastI_ex[OF ex_unsettled] unfolding i_def by blast+
  have before_settled:
    "\<And>j. j < i \<Longrightarrow> p ! j \<in> set settled"
  proof -
    fix j
    assume j_lt: "j < i"
    then have j_len: "j < length p"
      using i_props by simp
    show "p ! j \<in> set settled"
    proof (rule ccontr)
      assume "p ! j \<notin> set settled"
      then have "?P j"
        using j_len by blast
      then have "i \<le> j"
        unfolding i_def by (rule Least_le)
      then show False
        using j_lt by simp
    qed
  qed
  let ?y = "p ! i"
  have y_mem: "?y \<in> set p"
    using nth_mem[OF i_props(1)] .
  have y_dist_u: "nat_graph_dist G src ?y \<le> nat_graph_dist G src u"
  proof -
    have "concrete.dist src ?y \<le> concrete.dist src u"
      using concrete.shortest_walk_prefix_dist_le[OF sp y_mem] .
    then show ?thesis
      unfolding nat_graph_dist_def by simp
  qed
  have y_lookup_le: "\<exists>dy. bmssp_lookup_dist ds ?y = Some dy \<and>
      real dy \<le> nat_graph_dist G src ?y"
  proof (cases i)
    case 0
    then have y_src: "?y = src"
      using hd_p p_ne by (cases p) auto
    have lookup: "bmssp_lookup_dist ds ?y = Some 0"
      using source_zero y_src unfolding bmssp_source_zero_def by simp
    have "real 0 \<le> nat_graph_dist G src ?y"
      using concrete.dist_refl_zero[OF src_in] y_src
      unfolding nat_graph_dist_def by simp
    then show ?thesis
      using lookup by blast
  next
    case (Suc j)
    let ?x = "p ! j"
    have j_lt_i: "j < i"
      using Suc by simp
    have j_len: "j < length p"
      using j_lt_i i_props by simp
    have x_settled: "?x \<in> set settled"
      by (rule before_settled[OF j_lt_i])
    obtain dx where lookup_x: "bmssp_lookup_dist ds ?x = Some dx"
      using settled_lookup x_settled
      unfolding bmssp_settled_have_lookups_def by blast
    have exact_x: "real dx = nat_graph_dist G src ?x"
      using exact x_settled lookup_x
      unfolding bmssp_settled_exact_def by blast
    have suc_i: "Suc j = i"
      using Suc by simp
    have edge_idx: "Suc j < length p"
      using i_props suc_i by simp
    have tight: "concrete.tight_edge_step ?x ?y"
      using concrete.shortest_walk_successively_tight[OF sp]
      unfolding successively_conv_nth
      using edge_idx suc_i by blast
    have edge: "(?x, ?y) \<in> nat_graph_edges G"
      using tight unfolding concrete.tight_edge_step_def by blast
    obtain w where edge_w: "(?x, ?y, w) \<in> set G"
      using edge unfolding nat_graph_edges_def nat_graph_edge_list_def by auto
    obtain dy where lookup_y: "bmssp_lookup_dist ds ?y = Some dy"
      and dy_le: "real dy \<le> real dx + real w"
      using frontier edge_w x_settled i_props(2) lookup_x exact_x
      unfolding bmssp_frontier_relaxed_def by blast
    have weight_eq: "nat_graph_weight G ?x ?y = real w"
      by (rule nat_graph_weight_of_edge[OF wf edge_w])
    have dist_y_eq:
      "nat_graph_dist G src ?y =
        nat_graph_dist G src ?x + real w"
      using tight weight_eq
      unfolding concrete.tight_edge_step_def nat_graph_dist_def by simp
    have "real dy \<le> nat_graph_dist G src ?y"
      using dy_le exact_x dist_y_eq by simp
    then show ?thesis
      using lookup_y by blast
  qed
  obtain dy where lookup_y: "bmssp_lookup_dist ds ?y = Some dy"
    and dy_le: "real dy \<le> nat_graph_dist G src ?y"
    using y_lookup_le by blast
  show thesis
    by (rule that[OF y_mem i_props(2) lookup_y dy_le y_dist_u])
qed

lemma bmssp_partition_state_pulled_label_le_dist:
  assumes match: "bmssp_partition_state_match vertices settled ds P"
    and source_zero: "bmssp_source_zero src ds"
    and settled_lookup: "bmssp_settled_have_lookups settled ds"
    and witnesses: "bmssp_label_witnesses G src settled ds"
    and exact: "bmssp_settled_exact G src settled ds"
    and frontier: "bmssp_frontier_relaxed G src settled ds"
    and pull: "pull_separates (bp_view P) bmssp_block_size B S beta
      (bp_view P1)"
    and uS: "u \<in> S"
    and lookup_u: "bmssp_lookup_dist ds u = Some du"
  shows "real du \<le> nat_graph_dist G src u"
proof -
  have u_unsettled: "u \<notin> set settled"
    by (rule bmssp_partition_state_pulled_not_settled[OF match pull uS])
  have reach_u: "concrete.reachable src u"
    using bmssp_label_witnesses_lookup_reachable[OF witnesses lookup_u]
    unfolding nat_graph_reachable_def .
  obtain p where sp: "concrete.shortest_walk src p u"
    using concrete.shortest_walk_exists[OF reach_u] by blast
  obtain y dy where y_mem: "y \<in> set p"
    and y_unsettled: "y \<notin> set settled"
    and lookup_y: "bmssp_lookup_dist ds y = Some dy"
    and dy_le_dist: "real dy \<le> nat_graph_dist G src y"
    and dist_y_le_u: "nat_graph_dist G src y \<le> nat_graph_dist G src u"
    by (rule bmssp_shortest_walk_first_unsettled_lookup_le_dist
        [OF sp u_unsettled source_zero settled_lookup exact frontier])
  have du_le_dy: "du \<le> dy"
  proof (cases "y \<in> S")
    case True
    have S_subset: "S \<subseteq> keys_of (bp_view P)"
      by (rule pull_separates_subset[OF pull])
    have finite_S: "finite S"
      by (rule finite_subset[OF S_subset]) simp
    have card_S: "card S \<le> 1"
      using pull_separates_card[OF pull] unfolding bmssp_block_size_def .
    have "u = y"
      by (rule finite_card_le_one_member_eq[OF finite_S card_S uS True])
    then show ?thesis
      using lookup_u lookup_y by simp
  next
    case False
    show ?thesis
      by (rule bmssp_partition_state_pull_residual_label_le
          [OF match pull uS lookup_u lookup_y y_unsettled False])
  qed
  have "real du \<le> real dy"
    using du_le_dy by simp
  also have "\<dots> \<le> nat_graph_dist G src y"
    by (rule dy_le_dist)
  also have "\<dots> \<le> nat_graph_dist G src u"
    by (rule dist_y_le_u)
  finally show ?thesis .
qed

lemma bmssp_partition_state_pulled_label_exact:
  assumes match: "bmssp_partition_state_match vertices settled ds P"
    and source_zero: "bmssp_source_zero src ds"
    and settled_lookup: "bmssp_settled_have_lookups settled ds"
    and witnesses: "bmssp_label_witnesses G src settled ds"
    and exact: "bmssp_settled_exact G src settled ds"
    and frontier: "bmssp_frontier_relaxed G src settled ds"
    and pull: "pull_separates (bp_view P) bmssp_block_size B S beta
      (bp_view P1)"
    and uS: "u \<in> S"
    and lookup_u: "bmssp_lookup_dist ds u = Some du"
  shows "real du = nat_graph_dist G src u"
proof -
  have lower: "nat_graph_dist G src u \<le> real du"
    by (rule bmssp_label_witnesses_lookup_dist_le
        [OF witnesses lookup_u])
  have upper: "real du \<le> nat_graph_dist G src u"
    by (rule bmssp_partition_state_pulled_label_le_dist
        [OF match source_zero settled_lookup witnesses exact frontier
          pull uS lookup_u])
  show ?thesis
    using lower upper by simp
qed

lemma bmssp_settled_exact_partition_step:
  assumes match: "bmssp_partition_state_match vertices old_settled ds P"
    and source_zero: "bmssp_source_zero src ds"
    and settled_lookup: "bmssp_settled_have_lookups old_settled ds"
    and witnesses: "bmssp_label_witnesses G src old_settled ds"
    and exact: "bmssp_settled_exact G src old_settled ds"
    and frontier: "bmssp_frontier_relaxed G src old_settled ds"
    and pull: "pull_separates (bp_view P) bmssp_block_size B S beta
      (bp_view P1)"
    and pulled_def:
      "pulled = filter (\<lambda>x. x \<in> S \<and> x \<notin> set old_settled)
        vertices"
    and settled_def: "settled = pulled @ old_settled"
    and relaxed: "bmssp_relax_vertices G settled pulled ds = (updates, ds')"
  shows "bmssp_settled_exact G src settled ds'"
proof -
  have pulled_exact:
    "\<And>v d. \<lbrakk>v \<in> set pulled; bmssp_lookup_dist ds v = Some d\<rbrakk>
      \<Longrightarrow> real d = nat_graph_dist G src v"
  proof -
    fix v d
    assume v_pulled: "v \<in> set pulled"
      and lookup_v: "bmssp_lookup_dist ds v = Some d"
    have vS: "v \<in> S"
      using v_pulled unfolding pulled_def by simp
    show "real d = nat_graph_dist G src v"
      by (rule bmssp_partition_state_pulled_label_exact
          [OF match source_zero settled_lookup witnesses exact frontier
            pull vS lookup_v])
  qed
  show ?thesis
    by (rule bmssp_settled_exact_step
        [OF exact pulled_exact settled_def relaxed])
qed

lemma bmssp_dijkstra_state_step_bridge:
  fixes old_settled settled vertices :: "nat list"
    and pulled :: "nat list"
    and updates :: "(nat \<times> real) list"
  assumes state: "bmssp_dijkstra_state G src vertices old_settled ds P"
    and edge_targets:
      "\<And>a b w. (a, b, w) \<in> set G \<Longrightarrow> b \<in> set vertices"
    and pulled_def:
      "pulled = filter (\<lambda>x. x \<in> S \<and> x \<notin> set old_settled)
        vertices"
    and settled_def: "settled = pulled @ old_settled"
    and relaxed: "bmssp_relax_vertices G settled pulled ds = (updates, ds')"
    and P2_def: "P2 = bmssp_apply_updates updates P1"
    and distinct_vertices: "distinct vertices"
    and ord: "bp_ordered_invariant P"
    and upper: "partition_upper_bound (bp_view P) B"
    and pull: "bp_pull bmssp_block_size B P = (S, beta, P1)"
  shows "bmssp_dijkstra_state G src vertices settled ds' P2"
proof -
  have match: "bmssp_partition_state_match vertices old_settled ds P"
    and zero: "bmssp_source_zero src ds"
    and settled_lookup: "bmssp_settled_have_lookups old_settled ds"
    and witnesses: "bmssp_label_witnesses G src old_settled ds"
    and exact: "bmssp_settled_exact G src old_settled ds"
    and frontier: "bmssp_frontier_relaxed G src old_settled ds"
    using state unfolding bmssp_dijkstra_state_def by auto
  have distinct_ds: "distinct (map fst ds)"
    using match unfolding bmssp_partition_state_match_def by simp
  have updates_def: "updates = fst (bmssp_relax_vertices G settled pulled ds)"
    using relaxed by simp
  have sep:
    "pull_separates (bp_view P) bmssp_block_size B S beta (bp_view P1)"
    by (rule bmssp_loop_partition_step_bridge(1)
        [OF pulled_def updates_def P2_def wf distinct_vertices ord upper
          pull])
  have match':
    "bmssp_partition_state_match vertices settled ds' P2"
    by (rule bmssp_partition_state_match_step_bridge
        [OF match edge_targets pulled_def settled_def relaxed P2_def wf
          distinct_vertices ord upper pull])
  have zero': "bmssp_source_zero src ds'"
    by (rule bmssp_source_zero_step[OF zero distinct_ds relaxed])
  have settled_lookup':
    "bmssp_settled_have_lookups settled ds'"
    by (rule bmssp_settled_have_lookups_step
        [OF settled_lookup match sep pulled_def settled_def relaxed])
  have settled_subset: "set old_settled \<subseteq> set settled"
    using settled_def by auto
  have witnesses_settled:
    "bmssp_label_witnesses G src settled ds"
    by (rule bmssp_label_witnesses_mono_settled
        [OF witnesses settled_subset])
  have pulled_subset: "set pulled \<subseteq> set settled"
    using settled_def by simp
  have witnesses':
    "bmssp_label_witnesses G src settled ds'"
  proof -
    have "bmssp_label_witnesses G src settled
        (snd (bmssp_relax_vertices G settled pulled ds))"
      by (rule bmssp_relax_vertices_preserves_label_witnesses
          [OF wf witnesses_settled pulled_subset])
    then show ?thesis
      using relaxed by simp
  qed
  have exact': "bmssp_settled_exact G src settled ds'"
    by (rule bmssp_settled_exact_partition_step
        [OF match zero settled_lookup witnesses exact frontier sep
          pulled_def settled_def relaxed])
  have frontier': "bmssp_frontier_relaxed G src settled ds'"
    by (rule bmssp_frontier_relaxed_step
        [OF frontier distinct_ds settled_def relaxed])
  show ?thesis
    unfolding bmssp_dijkstra_state_def
    using match' zero' settled_lookup' witnesses' exact' frontier' by simp
qed

lemma bmssp_dijkstra_state_step_upper_bound:
  fixes old_settled settled vertices :: "nat list"
    and pulled :: "nat list"
    and updates :: "(nat \<times> real) list"
  assumes state: "bmssp_dijkstra_state G src vertices old_settled ds P"
    and wf: "nat_graph_well_formed G"
    and pulled_def:
      "pulled =
        filter (\<lambda>x. x \<in> S \<and> x \<notin> set old_settled)
          vertices"
    and settled_def: "settled = pulled @ old_settled"
    and relaxed: "bmssp_relax_vertices G settled pulled ds = (updates, ds')"
    and P2_def: "P2 = bmssp_apply_updates updates P1"
    and distinct_vertices: "distinct vertices"
    and ord: "bp_ordered_invariant P"
    and upper: "partition_upper_bound (bp_view P) bmssp_bound"
    and pull: "bp_pull bmssp_block_size bmssp_bound P = (S, beta, P1)"
  shows "partition_upper_bound (bp_view P2) bmssp_bound"
proof -
  have witnesses_old: "bmssp_label_witnesses G src old_settled ds"
    using state unfolding bmssp_dijkstra_state_def by simp
  have updates_def: "updates = fst (bmssp_relax_vertices G settled pulled ds)"
    using relaxed by simp
  have distinct_updates: "distinct (map fst updates)"
    by (rule bmssp_loop_partition_step_bridge(5)
        [OF pulled_def updates_def P2_def wf distinct_vertices ord upper pull])
  have settled_subset: "set old_settled \<subseteq> set settled"
    using settled_def by auto
  have witnesses:
    "bmssp_label_witnesses G src settled ds"
    by (rule bmssp_label_witnesses_mono_settled
        [OF witnesses_old settled_subset])
  have pulled_subset: "set pulled \<subseteq> set settled"
    using settled_def by simp
  have update_lt:
    "\<And>x b. (x, b) \<in> set updates \<Longrightarrow> b < bmssp_bound"
  proof -
    fix x b
    assume "(x, b) \<in> set updates"
    then have update_rel:
      "(x, b) \<in> set
        (fst (bmssp_relax_vertices G settled pulled ds))"
      using relaxed by simp
    have distinct_rel:
      "distinct
        (map fst (fst (bmssp_relax_vertices G settled pulled ds)))"
      using distinct_updates relaxed by simp
    show "b < bmssp_bound"
      by (rule bmssp_relax_vertices_update_lt_bound
          [OF wf witnesses pulled_subset distinct_rel update_rel])
  qed
  show ?thesis
    by (rule bmssp_loop_partition_step_bridge(9)
        [OF pulled_def updates_def P2_def wf distinct_vertices ord upper
          pull update_lt])
qed

definition bmssp_singleton_bucket_shape ::
  "nat bucketed_partition \<Rightarrow> bool" where
  "bmssp_singleton_bucket_shape P \<longleftrightarrow>
     bp_block_size P = bmssp_block_size \<and>
     (\<forall>b\<in>set (bp_buckets P).
       \<exists>p. bp_bucket_entries b = [p] \<and> bp_marker b = snd p)"

lemma bmssp_bucketize_sorted_entries_aux_singleton_shape:
  "\<forall>b\<in>set (bp_bucketize_sorted_entries_aux fuel 1 xs).
    \<exists>p. bp_bucket_entries b = [p] \<and> bp_marker b = snd p"
proof (induction fuel arbitrary: xs)
  case 0
  then show ?case
    by simp
next
  case (Suc fuel)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      by simp
  next
    case (Cons p ps)
    have tail:
      "\<forall>b\<in>set (bp_bucketize_sorted_entries_aux fuel 1 (drop 1 xs)).
        \<exists>p. bp_bucket_entries b = [p] \<and> bp_marker b = snd p"
      by (rule Suc.IH)
    show ?thesis
    proof
      fix b
      assume b:
        "b \<in> set (bp_bucketize_sorted_entries_aux (Suc fuel) 1 xs)"
      have b_cases:
        "b = bp_make_bucket [p] \<or>
         b \<in> set (bp_bucketize_sorted_entries_aux fuel 1 ps)"
        using b Cons by auto
      then show "\<exists>p. bp_bucket_entries b = [p] \<and> bp_marker b = snd p"
      proof
        assume b_def: "b = bp_make_bucket [p]"
        show ?thesis
          unfolding b_def bp_make_bucket_def
          by (rule exI[of _ p]) simp
      next
        assume "b \<in> set (bp_bucketize_sorted_entries_aux fuel 1 ps)"
        then show ?thesis
          using tail Cons by simp
      qed
    qed
  qed
qed

lemma bmssp_bucketize_entries_singleton_shape:
  "\<forall>b\<in>set (bp_bucketize_entries bmssp_block_size xs).
    \<exists>p. bp_bucket_entries b = [p] \<and> bp_marker b = snd p"
  unfolding bp_bucketize_entries_def bp_bucketize_sorted_entries_def
    bmssp_block_size_def
  by (rule bmssp_bucketize_sorted_entries_aux_singleton_shape)

lemma bmssp_rebucket_singleton_shape:
  assumes block: "bp_block_size P = bmssp_block_size"
  shows "bmssp_singleton_bucket_shape (bp_rebucket P)"
  unfolding bmssp_singleton_bucket_shape_def bp_rebucket_def
  using block bmssp_bucketize_entries_singleton_shape[of "bp_entries P"]
  by simp

lemma bmssp_singleton_bucket_shape_drop_empty_prefix_id:
  assumes shape:
    "\<forall>b\<in>set bs. \<exists>p. bp_bucket_entries b = [p] \<and> bp_marker b = snd p"
  shows "bp_drop_empty_prefix bs = bs"
  using shape
  by (induction bs) auto

lemma bmssp_singleton_bucket_shape_flat_length:
  assumes shape:
    "\<forall>b\<in>set bs. \<exists>p. bp_bucket_entries b = [p] \<and> bp_marker b = snd p"
  shows "length (bp_bucket_entries_flat bs) = length bs"
  using shape
proof (induction bs)
  case Nil
  then show ?case
    unfolding bp_bucket_entries_flat_def by simp
next
  case (Cons b bs)
  obtain p where b_entries: "bp_bucket_entries b = [p]"
    and b_marker: "bp_marker b = snd p"
  proof -
    have "\<exists>p. bp_bucket_entries b = [p] \<and> bp_marker b = snd p"
      using Cons.prems by simp
    then show ?thesis
      by (elim exE conjE) (rule that)
  qed
  have tail:
    "\<forall>b\<in>set bs. \<exists>p. bp_bucket_entries b = [p] \<and>
      bp_marker b = snd p"
    using Cons.prems by simp
  have "length (bp_bucket_entries_flat bs) = length bs"
    by (rule Cons.IH[OF tail])
  then show ?case
    using b_entries unfolding bp_bucket_entries_flat_def by simp
qed

lemma bmssp_singleton_bucket_shape_entries_empty_buckets:
  assumes shape: "bmssp_singleton_bucket_shape P"
    and empty: "bp_entries P = []"
  shows "bp_buckets P = []"
proof (cases "bp_buckets P")
  case Nil
  then show ?thesis .
next
  case (Cons b bs)
  obtain p where b_entries: "bp_bucket_entries b = [p]"
    using shape Cons unfolding bmssp_singleton_bucket_shape_def by auto
  then have "bp_entries P \<noteq> []"
    using Cons unfolding bp_entries_def bp_bucket_entries_flat_def by simp
  then show ?thesis
    using empty by simp
qed

lemma bmssp_singleton_bucket_shape_trim:
  assumes shape: "bmssp_singleton_bucket_shape P"
  shows "bmssp_trim_empty_prefix P = P"
proof -
  have buckets:
    "\<forall>b\<in>set (bp_buckets P).
      \<exists>p. bp_bucket_entries b = [p] \<and> bp_marker b = snd p"
    using shape unfolding bmssp_singleton_bucket_shape_def by simp
  have "bp_drop_empty_prefix (bp_buckets P) = bp_buckets P"
    by (rule bmssp_singleton_bucket_shape_drop_empty_prefix_id[OF buckets])
  then show ?thesis
    unfolding bmssp_trim_empty_prefix_def by simp
qed

lemma bmssp_singleton_bucket_shape_delete_first_bucket:
  assumes buckets: "bp_buckets P = b # bs"
    and shape: "bmssp_singleton_bucket_shape P"
    and distinct: "distinct (map fst (bp_entries P))"
  shows "bmssp_singleton_bucket_shape
    (bmssp_trim_empty_prefix (bp_delete_keys (bp_bucket_keys b) P))"
proof -
  obtain p where b_entries: "bp_bucket_entries b = [p]"
    and b_marker: "bp_marker b = snd p"
    using buckets shape unfolding bmssp_singleton_bucket_shape_def by auto
  have tail_shape:
    "\<forall>c\<in>set bs. \<exists>q. bp_bucket_entries c = [q] \<and> bp_marker c = snd q"
    using buckets shape unfolding bmssp_singleton_bucket_shape_def by auto
  have tail_unchanged:
    "map (bp_delete_keys_from_bucket (bp_bucket_keys b)) bs = bs"
  proof (rule map_idI)
    fix c
    assume c: "c \<in> set bs"
    obtain q where c_entries: "bp_bucket_entries c = [q]"
      and c_marker: "bp_marker c = snd q"
    proof -
      have "\<exists>q. bp_bucket_entries c = [q] \<and> bp_marker c = snd q"
        using tail_shape c by simp
      then show ?thesis
        by (elim exE conjE) (rule that)
    qed
    have fst_ne: "fst q \<noteq> fst p"
    proof
      assume eq: "fst q = fst p"
      have entries:
        "bp_entries P = p # bp_bucket_entries_flat bs"
        using buckets b_entries unfolding bp_entries_def
          bp_bucket_entries_flat_def by simp
      have q_flat: "q \<in> set (bp_bucket_entries_flat bs)"
        using c c_entries
        unfolding bp_bucket_entries_flat_def
        by (induction bs) auto
      then have "fst q \<in> set (map fst (bp_bucket_entries_flat bs))"
        by simp
      then show False
        using distinct eq entries by simp
    qed
    have "fst q \<notin> bp_bucket_keys b"
      using fst_ne b_entries unfolding bp_bucket_keys_def bp_entry_keys_def
      by simp
    then have keep_c:
      "filter (\<lambda>r. fst r \<notin> bp_bucket_keys b)
        (bp_bucket_entries c) = bp_bucket_entries c"
      using c_entries by simp
    then show "bp_delete_keys_from_bucket (bp_bucket_keys b) c = c"
      unfolding bp_delete_keys_from_bucket_def by simp
  qed
  have deleted_head:
    "bp_delete_keys_from_bucket (bp_bucket_keys b) b =
      b\<lparr>bp_bucket_entries := []\<rparr>"
    unfolding bp_delete_keys_from_bucket_def b_entries
      bp_bucket_keys_def bp_entry_keys_def by simp
  have buckets_deleted:
    "bp_buckets (bp_delete_keys (bp_bucket_keys b) P) =
      b\<lparr>bp_bucket_entries := []\<rparr> # bs"
    using buckets tail_unchanged deleted_head
    unfolding bp_delete_keys_def by simp
  have trimmed_buckets:
    "bp_buckets
      (bmssp_trim_empty_prefix (bp_delete_keys (bp_bucket_keys b) P)) =
      bs"
  proof -
    have tail_drop: "bp_drop_empty_prefix bs = bs"
      by (rule bmssp_singleton_bucket_shape_drop_empty_prefix_id[OF tail_shape])
    show ?thesis
      using buckets_deleted tail_drop
      unfolding bmssp_trim_empty_prefix_def by simp
  qed
  have block:
    "bp_block_size
      (bmssp_trim_empty_prefix (bp_delete_keys (bp_bucket_keys b) P)) =
      bmssp_block_size"
    using shape unfolding bmssp_singleton_bucket_shape_def
      bmssp_trim_empty_prefix_def bp_delete_keys_def by simp
  show ?thesis
    unfolding bmssp_singleton_bucket_shape_def
    using block trimmed_buckets tail_shape by simp
qed

lemma bmssp_singleton_bucket_shape_delete_all_small:
  assumes shape: "bmssp_singleton_bucket_shape P"
    and small: "length (bp_entries P) \<le> bmssp_block_size"
  shows "bmssp_singleton_bucket_shape
    (bmssp_trim_empty_prefix
      (bp_delete_keys (bp_entry_keys (bp_entries P)) P))"
proof -
  have block: "bp_block_size P = bmssp_block_size"
    using shape unfolding bmssp_singleton_bucket_shape_def by simp
  have singleton:
    "\<forall>b\<in>set (bp_buckets P).
      \<exists>p. bp_bucket_entries b = [p] \<and> bp_marker b = snd p"
    using shape unfolding bmssp_singleton_bucket_shape_def by simp
  have entries_len:
    "length (bp_entries P) = length (bp_buckets P)"
  proof -
    have "length (bp_bucket_entries_flat (bp_buckets P)) =
        length (bp_buckets P)"
      by (rule bmssp_singleton_bucket_shape_flat_length[OF singleton])
    then show ?thesis
      unfolding bp_entries_def .
  qed
  have buckets_len: "length (bp_buckets P) \<le> 1"
    using small entries_len unfolding bmssp_block_size_def by simp
  have trimmed_empty:
    "bp_drop_empty_prefix
      (bp_buckets (bp_delete_keys (bp_entry_keys (bp_entries P)) P)) = []"
  proof (cases "bp_buckets P")
    case Nil
    then show ?thesis
      unfolding bp_delete_keys_def by simp
  next
    case (Cons b bs)
    then have bs_empty: "bs = []"
      using buckets_len by (cases bs) simp_all
    obtain p where b_entries: "bp_bucket_entries b = [p]"
    proof -
      have "\<exists>p. bp_bucket_entries b = [p] \<and> bp_marker b = snd p"
        using singleton Cons by simp
      then show ?thesis
        by (elim exE conjE) (rule that)
    qed
    have key_in:
      "fst p \<in> bp_entry_keys (bp_entries P)"
      using Cons b_entries
      unfolding bp_entries_def bp_bucket_entries_flat_def bp_entry_keys_def
      by simp
    have deleted:
      "bp_delete_keys_from_bucket (bp_entry_keys (bp_entries P)) b =
        b\<lparr>bp_bucket_entries := []\<rparr>"
      unfolding bp_delete_keys_from_bucket_def b_entries
      using key_in by simp
    show ?thesis
      using Cons bs_empty deleted unfolding bp_delete_keys_def by simp
  qed
  have block_deleted:
    "bp_block_size (bp_delete_keys (bp_entry_keys (bp_entries P)) P) =
      bmssp_block_size"
    using block unfolding bp_delete_keys_def by simp
  show ?thesis
    unfolding bmssp_singleton_bucket_shape_def bmssp_trim_empty_prefix_def
    using block_deleted trimmed_empty by simp
qed

lemma bmssp_singleton_bucket_shape_pull_trim:
  assumes shape: "bmssp_singleton_bucket_shape P"
    and ord: "bp_ordered_invariant P"
    and pull: "bp_pull bmssp_block_size B P = (S, beta, P1)"
  shows "bmssp_singleton_bucket_shape (bmssp_trim_empty_prefix P1)"
proof (cases "bp_can_first_bucket_pull bmssp_block_size P")
  case True
  then obtain b c bs where buckets: "bp_buckets P = b # c # bs"
    by (rule bp_can_first_bucket_pullE) blast
  have first:
    "bp_first_bucket_pull bmssp_block_size B P = (S, beta, P1)"
    using True pull unfolding bp_pull_def by simp
  have P1_def: "P1 = bp_delete_keys (bp_bucket_keys b) P"
    using first buckets unfolding bp_first_bucket_pull_def
    by (auto simp: Let_def)
  have distinct: "distinct (map fst (bp_entries P))"
    using ord unfolding bp_ordered_invariant_def bp_invariant_def
      bp_distinct_keys_def by blast
  show ?thesis
    unfolding P1_def
    by (rule bmssp_singleton_bucket_shape_delete_first_bucket
        [OF _ shape distinct])
      (use buckets in simp)
next
  case False
  have conservative:
    "bp_conservative_pull bmssp_block_size B P = (S, beta, P1)"
    using False pull unfolding bp_pull_def by simp
  have S_def: "S = bp_pull_set bmssp_block_size P"
    and P1_def: "P1 = bp_delete_keys S P"
    using conservative unfolding bp_conservative_pull_def
    by (auto simp: Let_def)
  show ?thesis
  proof (cases "length (bp_entries P) \<le> bmssp_block_size")
    case True
    have S_all: "S = bp_entry_keys (bp_entries P)"
      using S_def True unfolding bp_pull_set_def by simp
    show ?thesis
      unfolding P1_def S_all
      by (rule bmssp_singleton_bucket_shape_delete_all_small
          [OF shape True])
  next
    case False
    have S_empty: "S = {}"
      using S_def False unfolding bp_pull_set_def by simp
    have P1_eq: "P1 = P"
      unfolding P1_def S_empty bp_delete_keys_def
        bp_delete_keys_from_bucket_def by simp
    show ?thesis
      using shape
      unfolding P1_eq
      by (simp add: bmssp_singleton_bucket_shape_trim[OF shape])
  qed
qed

lemma bmssp_singleton_bucket_shape_regularized_insert:
  assumes shape: "bmssp_singleton_bucket_shape P"
  shows "bmssp_singleton_bucket_shape
    (bp_result_of (c_bp_regularized_local_insert x b P))"
proof -
  have block: "bp_block_size P = bmssp_block_size"
    using shape unfolding bmssp_singleton_bucket_shape_def by simp
  have local_block:
    "bp_block_size (bp_local_insert_state x b P) = bmssp_block_size"
    using block
    by (simp add: bp_local_insert_state_def bp_delete_key_def Let_def)
  show ?thesis
    unfolding c_bp_regularized_local_insert_result
      bp_regularized_local_insert_def
    by (rule bmssp_rebucket_singleton_shape[OF local_block])
qed

lemma bmssp_insert_updates_singleton_shape:
  assumes shape: "bmssp_singleton_bucket_shape P"
  shows "bmssp_singleton_bucket_shape (bmssp_insert_updates xs P)"
  using shape
proof (induction xs arbitrary: P)
  case Nil
  then show ?case
    by simp
next
  case (Cons xb xs)
  obtain x b where xb: "xb = (x, b)"
    by force
  have step_shape:
    "bmssp_singleton_bucket_shape
      (bp_result_of (c_bp_regularized_local_insert x b P))"
    by (rule bmssp_singleton_bucket_shape_regularized_insert[OF Cons.prems])
  show ?case
    unfolding xb bmssp_insert_updates.simps
    by (rule Cons.IH[OF step_shape])
qed

lemma bmssp_bucketed_batch_prepend_empty_singleton_shape:
  assumes shape: "bmssp_singleton_bucket_shape P"
    and empty: "bp_entries P = []"
  shows "bmssp_singleton_bucket_shape
    (bp_result_of (c_bp_paper_batch_prepend xs P))"
proof (cases xs)
  case Nil
  then show ?thesis
    using shape empty
    unfolding c_bp_paper_batch_prepend_result
      bp_bucketed_batch_prepend_state_def
    by simp
next
  case (Cons p ps)
  have buckets_empty: "bp_buckets P = []"
    by (rule bmssp_singleton_bucket_shape_entries_empty_buckets
        [OF shape empty])
  have block: "bp_block_size P = bmssp_block_size"
    using shape unfolding bmssp_singleton_bucket_shape_def by simp
  have bucket_shape:
    "\<forall>b\<in>set (bp_bucketize_entries (bp_block_size P) xs).
      \<exists>p. bp_bucket_entries b = [p] \<and> bp_marker b = snd p"
    using block bmssp_bucketize_entries_singleton_shape[of xs] by simp
  show ?thesis
    using block buckets_empty bucket_shape Cons
    unfolding c_bp_paper_batch_prepend_result
      bp_bucketed_batch_prepend_state_def
      bmssp_singleton_bucket_shape_def
    by (simp add: Let_def)
qed

lemma bmssp_apply_updates_singleton_shape:
  assumes shape: "bmssp_singleton_bucket_shape (bmssp_trim_empty_prefix P)"
  shows "bmssp_singleton_bucket_shape (bmssp_apply_updates xs P)"
proof -
  let ?P0 = "bmssp_trim_empty_prefix P"
  show ?thesis
  proof (cases "bp_entries ?P0 = []")
    case True
    have result:
      "bmssp_apply_updates xs P =
        bp_result_of (c_bp_paper_batch_prepend xs ?P0)"
      using True unfolding bmssp_apply_updates_def by simp
    have shape':
      "bmssp_singleton_bucket_shape
        (bp_result_of (c_bp_paper_batch_prepend xs ?P0))"
      by (rule bmssp_bucketed_batch_prepend_empty_singleton_shape
          [OF shape True])
    show ?thesis
      using result shape' by simp
  next
    case False
    have result:
      "bmssp_apply_updates xs P = bmssp_insert_updates xs ?P0"
      using False unfolding bmssp_apply_updates_def by simp
    have shape':
      "bmssp_singleton_bucket_shape (bmssp_insert_updates xs ?P0)"
      by (rule bmssp_insert_updates_singleton_shape[OF shape])
    show ?thesis
      using result shape' by simp
  qed
qed

lemma bmssp_partition_key_inject:
  assumes eq: "bmssp_partition_key v d = bmssp_partition_key w e"
  shows "v = w \<and> d = e"
proof -
  have d_eq: "d = e"
    using eq bmssp_partition_key_floor[of v d]
      bmssp_partition_key_floor[of w e]
    by simp
  have frac_eq:
    "real v / real (Suc v) = real w / real (Suc w)"
    using eq d_eq unfolding bmssp_partition_key_def by simp
  have frac_v:
    "real v / real (Suc v) = 1 - inverse (real (Suc v))"
    by (simp add: field_simps)
  have frac_w:
    "real w / real (Suc w) = 1 - inverse (real (Suc w))"
    by (simp add: field_simps)
  have inv_eq:
    "inverse (real (Suc v)) = inverse (real (Suc w))"
    using frac_eq frac_v frac_w by linarith
  then have "real (Suc v) = real (Suc w)"
    by simp
  then have "v = w"
    by simp
  then show ?thesis
    using d_eq by simp
qed

lemma distinct_map_fst_mem_eq:
  assumes distinct: "distinct (map fst xs)"
    and p: "p \<in> set xs"
    and q: "q \<in> set xs"
    and fst_eq: "fst p = fst q"
  shows "p = q"
  using assms
proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons r xs)
  show ?case
  proof (cases "p = r")
    case True
    have "q = r"
    proof (rule ccontr)
      assume "q \<noteq> r"
      then have "q \<in> set xs"
        using Cons.prems(3) by simp
      then have "fst q \<in> set (map fst xs)"
        by force
      moreover have "fst r \<notin> set (map fst xs)"
        using Cons.prems(1) by simp
      ultimately show False
        using Cons.prems(4) True by simp
    qed
    then show ?thesis
      using True by simp
  next
    case False
    then have p_tail: "p \<in> set xs"
      using Cons.prems(2) by simp
    show ?thesis
    proof (cases "q = r")
      case True
      have "fst p \<in> set (map fst xs)"
        using p_tail by force
      moreover have "fst r \<notin> set (map fst xs)"
        using Cons.prems(1) by simp
      ultimately show ?thesis
        using Cons.prems(4) True by simp
    next
      case False
      have q_tail: "q \<in> set xs"
        using False Cons.prems(3) by simp
      have distinct_tail: "distinct (map fst xs)"
        using Cons.prems(1) by simp
      show ?thesis
        by (rule Cons.IH[OF distinct_tail p_tail q_tail Cons.prems(4)])
    qed
  qed
qed

lemma bmssp_partition_entries_value_inj:
  assumes match: "bmssp_partition_state_match vertices settled ds P"
    and ord: "bp_ordered_invariant P"
  shows "inj_on snd (set (bp_entries P))"
proof (rule inj_onI)
  fix p q
  assume p: "p \<in> set (bp_entries P)"
    and q: "q \<in> set (bp_entries P)"
    and snd_eq: "snd p = snd q"
  have distinct_ds: "distinct (map fst ds)"
    and keys: "bmssp_partition_keys_match settled ds P"
    and vals: "bmssp_partition_values_match settled ds (bp_view P)"
    using match unfolding bmssp_partition_state_match_def by auto
  have values_consistent:
    "\<And>r. r \<in> set (bp_entries P) \<Longrightarrow>
      value_of (bp_view P) (fst r) = snd r"
    using ord
    unfolding bp_ordered_invariant_def bp_invariant_def
      bp_values_consistent_def bp_view_def
    by simp
  have p_key: "fst p \<in> keys_of (bp_view P)"
    using p unfolding bp_view_def bp_entry_keys_def by auto
  have q_key: "fst q \<in> keys_of (bp_view P)"
    using q unfolding bp_view_def bp_entry_keys_def by auto
  obtain dp where p_lookup: "bmssp_lookup_dist ds (fst p) = Some dp"
    and p_unsettled: "fst p \<notin> set settled"
  proof -
    have key: "fst p \<in> set (map fst ds) - set settled"
      using keys p_key unfolding bmssp_partition_keys_match_def by simp
    then obtain dp where mem: "(fst p, dp) \<in> set ds"
      by force
    have lookup: "bmssp_lookup_dist ds (fst p) = Some dp"
      by (rule bmssp_lookup_dist_Some_if_distinct_mem
          [OF distinct_ds mem])
    show ?thesis
      using that lookup key by blast
  qed
  obtain dq where q_lookup: "bmssp_lookup_dist ds (fst q) = Some dq"
    and q_unsettled: "fst q \<notin> set settled"
  proof -
    have key: "fst q \<in> set (map fst ds) - set settled"
      using keys q_key unfolding bmssp_partition_keys_match_def by simp
    then obtain dq where mem: "(fst q, dq) \<in> set ds"
      by force
    have lookup: "bmssp_lookup_dist ds (fst q) = Some dq"
      by (rule bmssp_lookup_dist_Some_if_distinct_mem
          [OF distinct_ds mem])
    show ?thesis
      using that lookup key by blast
  qed
  have p_value:
    "snd p = bmssp_partition_key (fst p) dp"
    using vals p_lookup p_unsettled values_consistent[OF p]
    unfolding bmssp_partition_values_match_def by simp
  have q_value:
    "snd q = bmssp_partition_key (fst q) dq"
    using vals q_lookup q_unsettled values_consistent[OF q]
    unfolding bmssp_partition_values_match_def by simp
  have fst_eq: "fst p = fst q"
    using bmssp_partition_key_inject[of "fst p" dp "fst q" dq]
      snd_eq p_value q_value by auto
  have distinct_entries: "distinct (map fst (bp_entries P))"
    using ord unfolding bp_ordered_invariant_def bp_invariant_def
      bp_distinct_keys_def by blast
  show "p = q"
    by (rule distinct_map_fst_mem_eq
        [OF distinct_entries p q fst_eq])
qed

lemma bmssp_can_first_bucket_pull_if_singleton_shape:
  assumes shape: "bmssp_singleton_bucket_shape P"
    and ord: "bp_ordered_invariant P"
    and values_inj: "inj_on snd (set (bp_entries P))"
    and many: "length (bp_entries P) > bmssp_block_size"
  shows "bp_can_first_bucket_pull bmssp_block_size P"
proof -
  have singleton:
    "\<forall>b\<in>set (bp_buckets P).
      \<exists>p. bp_bucket_entries b = [p] \<and> bp_marker b = snd p"
    using shape unfolding bmssp_singleton_bucket_shape_def by simp
  have distinct_entries: "distinct (map fst (bp_entries P))"
    using ord unfolding bp_ordered_invariant_def bp_invariant_def
      bp_distinct_keys_def by blast
  obtain b rest where buckets_outer: "bp_buckets P = b # rest"
  proof (cases "bp_buckets P")
    case Nil
    then have "bp_entries P = []"
      unfolding bp_entries_def bp_bucket_entries_flat_def by simp
    then show ?thesis
      using many unfolding bmssp_block_size_def by simp
  next
    case (Cons b rest)
    then show ?thesis
      by (rule that)
  qed
  obtain p where b_entries: "bp_bucket_entries b = [p]"
    and b_marker: "bp_marker b = snd p"
    using singleton buckets_outer by auto
  obtain c bs where rest: "rest = c # bs"
  proof (cases rest)
    case Nil
    then have "bp_entries P = [p]"
      using buckets_outer b_entries
      unfolding bp_entries_def bp_bucket_entries_flat_def by simp
    then show ?thesis
      using many unfolding bmssp_block_size_def by simp
  next
    case (Cons c bs)
    then show ?thesis
      by (rule that)
  qed
  have buckets: "bp_buckets P = b # c # bs"
    using buckets_outer rest by simp
  obtain q where c_entries: "bp_bucket_entries c = [q]"
    and c_marker: "bp_marker c = snd q"
    using singleton buckets by auto
  have p_entry: "p \<in> set (bp_entries P)"
    using buckets b_entries
    unfolding bp_entries_def bp_bucket_entries_flat_def by simp
  have q_entry: "q \<in> set (bp_entries P)"
    using buckets c_entries
    unfolding bp_entries_def bp_bucket_entries_flat_def by simp
  have p_neq_q: "p \<noteq> q"
  proof
    assume "p = q"
    then have "fst p = fst q"
      by simp
    moreover have "map fst (bp_entries P) =
      fst p # fst q # map fst (bp_bucket_entries_flat bs)"
      using buckets b_entries c_entries
      unfolding bp_entries_def bp_bucket_entries_flat_def by simp
    ultimately show False
      using distinct_entries by simp
  qed
  have snd_ne: "snd p \<noteq> snd q"
    using values_inj p_entry q_entry p_neq_q unfolding inj_on_def by blast
  have boundary:
    "\<forall>r\<in>set (bp_bucket_entries b). snd r \<le> bp_marker c"
    using ord buckets
    unfolding bp_ordered_invariant_def
      bp_bucket_boundaries_state_ok_def
    by simp
  have below: "bp_bucket_below_bound b (bp_marker c)"
  proof -
    have "snd p < snd q"
      using boundary snd_ne unfolding b_entries c_marker by auto
    then show ?thesis
      unfolding bp_bucket_below_bound_def b_entries c_marker by simp
  qed
  have len_b: "length (bp_bucket_entries b) \<le> bmssp_block_size"
    unfolding b_entries bmssp_block_size_def by simp
  have tail_nonempty: "bp_bucket_entries_flat (c # bs) \<noteq> []"
    using c_entries unfolding bp_bucket_entries_flat_def by simp
  show ?thesis
    unfolding bp_can_first_bucket_pull_def buckets
    using many len_b below tail_nonempty by simp
qed

lemma bmssp_pull_nonempty_if_keys_nonempty:
  assumes shape: "bmssp_singleton_bucket_shape P"
    and ord: "bp_ordered_invariant P"
    and values_inj: "inj_on snd (set (bp_entries P))"
    and pull: "bp_pull bmssp_block_size B P = (S, beta, P1)"
    and keys_nonempty: "keys_of (bp_view P) \<noteq> {}"
  shows "S \<noteq> {}"
proof (cases "bp_can_first_bucket_pull bmssp_block_size P")
  case True
  obtain b c bs where buckets: "bp_buckets P = b # c # bs"
    by (rule bp_can_first_bucket_pullE[OF True])
  obtain p where b_entries: "bp_bucket_entries b = [p]"
    using shape buckets unfolding bmssp_singleton_bucket_shape_def by auto
  have first:
    "bp_first_bucket_pull bmssp_block_size B P = (S, beta, P1)"
    using True pull unfolding bp_pull_def by simp
  have "S = bp_bucket_keys b"
    using first buckets unfolding bp_first_bucket_pull_def
    by (simp add: Let_def)
  then show ?thesis
    using b_entries unfolding bp_bucket_keys_def bp_entry_keys_def by simp
next
  case False
  note not_can = False
  have conservative:
    "bp_conservative_pull bmssp_block_size B P = (S, beta, P1)"
    using False pull unfolding bp_pull_def by simp
  have S_def: "S = bp_pull_set bmssp_block_size P"
    using conservative unfolding bp_conservative_pull_def
    by (simp add: Let_def)
  show ?thesis
  proof (cases "length (bp_entries P) \<le> bmssp_block_size")
    case True
    have "bp_entry_keys (bp_entries P) \<noteq> {}"
      using keys_nonempty unfolding bp_view_def by simp
    then show ?thesis
      using S_def True unfolding bp_pull_set_def by simp
  next
    case False
    have can: "bp_can_first_bucket_pull bmssp_block_size P"
      by (rule bmssp_can_first_bucket_pull_if_singleton_shape
          [OF shape ord values_inj])
        (use False in simp)
    then show ?thesis
      using not_can by simp
  qed
qed

definition bmssp_dijkstra_loop_state ::
  "nat list \<Rightarrow> nat list \<Rightarrow>
    nat_dist \<Rightarrow> nat bucketed_partition \<Rightarrow> bool" where
  "bmssp_dijkstra_loop_state vertices settled ds P \<longleftrightarrow>
     bmssp_dijkstra_state G src vertices settled ds P \<and>
     bp_ordered_invariant P \<and>
     partition_upper_bound (bp_view P) bmssp_bound"


lemma bmssp_dijkstra_loop_state_initial:
  assumes src_vertices: "src \<in> set vertices"
  shows "bmssp_dijkstra_loop_state vertices [] [(src, 0)]
    (bp_result_of
      (c_bp_regularized_local_insert src (bmssp_partition_key src 0)
        (bp_empty bmssp_block_size bmssp_bound)))"
proof -
  have dijkstra:
    "bmssp_dijkstra_state G src vertices [] [(src, 0)]
      (bp_result_of
        (c_bp_regularized_local_insert src (bmssp_partition_key src 0)
          (bp_empty bmssp_block_size bmssp_bound)))"
    by (rule bmssp_dijkstra_state_initial[OF src_vertices])
  have ord:
    "bp_ordered_invariant
      (bp_result_of
        (c_bp_regularized_local_insert src (bmssp_partition_key src 0)
          (bp_empty bmssp_block_size bmssp_bound)))"
    by (rule bmssp_initial_partition_bridge(1))
  have upper:
    "partition_upper_bound
      (bp_view
        (bp_result_of
          (c_bp_regularized_local_insert src (bmssp_partition_key src 0)
            (bp_empty bmssp_block_size bmssp_bound))))
      bmssp_bound"
    by (rule bmssp_initial_partition_bridge(2))
  show ?thesis
    unfolding bmssp_dijkstra_loop_state_def
    using dijkstra ord upper by simp
qed

lemma bmssp_dijkstra_loop_state_step_bridge:
  fixes old_settled settled vertices :: "nat list"
    and pulled :: "nat list"
    and updates :: "(nat \<times> real) list"
  assumes loop_state:
      "bmssp_dijkstra_loop_state vertices old_settled ds P"
    and edge_targets:
      "\<And>a b w. (a, b, w) \<in> set G \<Longrightarrow> b \<in> set vertices"
    and pulled_def:
      "pulled =
        filter (\<lambda>x. x \<in> S \<and> x \<notin> set old_settled)
          vertices"
    and settled_def: "settled = pulled @ old_settled"
    and relaxed: "bmssp_relax_vertices G settled pulled ds = (updates, ds')"
    and P2_def: "P2 = bmssp_apply_updates updates P1"
    and wf: "nat_graph_well_formed G"
    and distinct_vertices: "distinct vertices"
    and pull: "bp_pull bmssp_block_size bmssp_bound P = (S, beta, P1)"
  shows "bmssp_dijkstra_loop_state vertices settled ds' P2"
proof -
  have state: "bmssp_dijkstra_state G src vertices old_settled ds P"
    and ord: "bp_ordered_invariant P"
    and upper: "partition_upper_bound (bp_view P) bmssp_bound"
    using loop_state unfolding bmssp_dijkstra_loop_state_def by auto
  have state':
    "bmssp_dijkstra_state G src vertices settled ds' P2"
    by (rule bmssp_dijkstra_state_step_bridge
        [OF state edge_targets pulled_def settled_def relaxed P2_def
          distinct_vertices ord upper pull])
  have updates_def: "updates = fst (bmssp_relax_vertices G settled pulled ds)"
    using relaxed by simp
  have ord':
    "bp_ordered_invariant P2"
    by (rule bmssp_loop_partition_step_bridge(8)
        [OF pulled_def updates_def P2_def wf distinct_vertices ord upper
          pull])
  have upper':
    "partition_upper_bound (bp_view P2) bmssp_bound"
    by (rule bmssp_dijkstra_state_step_upper_bound
        [OF state wf pulled_def settled_def relaxed P2_def distinct_vertices
          ord upper pull])
  show ?thesis
    unfolding bmssp_dijkstra_loop_state_def
    using state' ord' upper' by simp
qed

lemma distinct_subset_length_le:
  assumes xs: "distinct xs"
    and ys: "distinct ys"
    and subset: "set xs \<subseteq> set ys"
  shows "length xs \<le> length ys"
proof -
  have "length xs = card (set xs)"
    using xs by (simp add: distinct_card)
  also have "\<dots> \<le> card (set ys)"
    by (rule card_mono) (use subset in simp_all)
  also have "\<dots> = length ys"
    using ys by (simp add: distinct_card)
  finally show ?thesis .
qed

lemma bmssp_dijkstra_loop_state_settled_subset_vertices:
  assumes loop_state: "bmssp_dijkstra_loop_state vertices settled ds P"
  shows "set settled \<subseteq> set vertices"
proof
  fix v
  assume v_settled: "v \<in> set settled"
  have state: "bmssp_dijkstra_state G src vertices settled ds P"
    using loop_state unfolding bmssp_dijkstra_loop_state_def by simp
  have match: "bmssp_partition_state_match vertices settled ds P"
    and have_lookups: "bmssp_settled_have_lookups settled ds"
    using state unfolding bmssp_dijkstra_state_def by auto
  obtain d where lookup: "bmssp_lookup_dist ds v = Some d"
    using have_lookups v_settled
    unfolding bmssp_settled_have_lookups_def by blast
  have "v \<in> set (map fst ds)"
    by (rule bmssp_lookup_dist_mem_key[OF lookup])
  then show "v \<in> set vertices"
    using match unfolding bmssp_partition_state_match_def by blast
qed

lemma bmssp_loop_quiescent_state:
  assumes loop_state: "bmssp_dijkstra_loop_state vertices settled ds P"
    and shape: "bmssp_singleton_bucket_shape P"
    and edge_targets:
      "\<And>a b w. (a, b, w) \<in> set G \<Longrightarrow> b \<in> set vertices"
    and distinct_vertices: "distinct vertices"
    and distinct_settled: "distinct settled"
    and fuel: "fuel > length vertices - length settled"
  shows "\<exists>settled' ds' P' S beta P1.
    bmssp_loop fuel G vertices settled ds P = bmssp_normalize_dist ds' \<and>
    bmssp_dijkstra_loop_state vertices settled' ds' P' \<and>
    bmssp_singleton_bucket_shape P' \<and>
    distinct settled' \<and>
    set settled \<subseteq> set settled' \<and>
    bp_pull bmssp_block_size bmssp_bound P' = (S, beta, P1) \<and>
    filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled') vertices = []"
  using loop_state shape distinct_settled fuel
proof (induction fuel arbitrary: settled ds P)
  case 0
  then show ?case
    by simp
next
  case (Suc fuel)
  obtain S beta P1 where pull:
    "bp_pull bmssp_block_size bmssp_bound P = (S, beta, P1)"
    by (cases "bp_pull bmssp_block_size bmssp_bound P") auto
  let ?pulled =
    "filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices"
  show ?case
  proof (cases "?pulled = []")
    case True
    have loop_eq:
      "bmssp_loop (Suc fuel) G vertices settled ds P =
        bmssp_normalize_dist ds"
      using pull True by simp
    show ?thesis
    proof (intro exI conjI)
      show "bmssp_loop (Suc fuel) G vertices settled ds P =
          bmssp_normalize_dist ds"
        by (rule loop_eq)
      show "bmssp_dijkstra_loop_state vertices settled ds P"
        by (rule Suc.prems(1))
      show "bmssp_singleton_bucket_shape P"
        by (rule Suc.prems(2))
      show "distinct settled"
        by (rule Suc.prems(3))
      show "set settled \<subseteq> set settled"
        by simp
      show "bp_pull bmssp_block_size bmssp_bound P = (S, beta, P1)"
        by (rule pull)
      show "filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices = []"
        by (rule True)
    qed
  next
    case False
    let ?settled = "?pulled @ settled"
    obtain updates ds' where relaxed:
      "bmssp_relax_vertices G ?settled ?pulled ds = (updates, ds')"
      by force
    let ?P2 = "bmssp_apply_updates updates P1"
    have pulled_def:
      "?pulled =
        filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices"
      by simp
    have settled_def: "?settled = ?pulled @ settled"
      by simp
    have P2_def: "?P2 = bmssp_apply_updates updates P1"
      by simp
    have loop_state':
      "bmssp_dijkstra_loop_state vertices ?settled ds' ?P2"
      by (rule bmssp_dijkstra_loop_state_step_bridge
          [OF Suc.prems(1) edge_targets pulled_def settled_def relaxed
            P2_def wf distinct_vertices pull])
    have state: "bmssp_dijkstra_state G src vertices settled ds P"
      and ord: "bp_ordered_invariant P"
      and upper: "partition_upper_bound (bp_view P) bmssp_bound"
      using Suc.prems(1) unfolding bmssp_dijkstra_loop_state_def by auto
    have trim_shape:
      "bmssp_singleton_bucket_shape (bmssp_trim_empty_prefix P1)"
      by (rule bmssp_singleton_bucket_shape_pull_trim
          [OF Suc.prems(2) ord pull])
    have shape':
      "bmssp_singleton_bucket_shape ?P2"
      by (rule bmssp_apply_updates_singleton_shape[OF trim_shape])
    have updates_def:
      "updates = fst (bmssp_relax_vertices G ?settled ?pulled ds)"
      using relaxed by simp
    have pulled_len: "length ?pulled \<le> 1"
      by (rule bmssp_loop_partition_step_bridge(4)
          [OF pulled_def updates_def P2_def wf distinct_vertices ord upper
            pull])
    have pulled_one: "length ?pulled = 1"
      using False pulled_len by (cases ?pulled) auto
    have pulled_distinct: "distinct ?pulled"
      using pulled_len by (cases ?pulled) auto
    have pulled_disjoint: "set ?pulled \<inter> set settled = {}"
      by auto
    have distinct_settled': "distinct ?settled"
      using pulled_distinct pulled_disjoint Suc.prems(3) by simp
    have settled_subset_vertices:
      "set settled \<subseteq> set vertices"
      by (rule bmssp_dijkstra_loop_state_settled_subset_vertices
          [OF Suc.prems(1)])
    have old_lt_vertices: "length settled < length vertices"
    proof -
      obtain x where x_pulled: "x \<in> set ?pulled"
        using False by (cases ?pulled) auto
      have x_vertices: "x \<in> set vertices"
        using x_pulled by simp
      have x_not_settled: "x \<notin> set settled"
        using x_pulled by simp
      have proper: "set settled < set vertices"
        using settled_subset_vertices x_vertices x_not_settled
        unfolding psubset_eq by blast
      have "card (set settled) < card (set vertices)"
        by (rule psubset_card_mono) (use proper in simp_all)
      then show ?thesis
      using Suc.prems(3) distinct_vertices
      by (simp add: distinct_card)
    qed
    have diff_step:
      "Suc (length vertices - Suc (length settled)) =
        length vertices - length settled"
      by (rule Suc_diff_Suc[OF old_lt_vertices])
    have fuel':
      "fuel > length vertices - length ?settled"
    proof -
      have "fuel > length vertices - Suc (length settled)"
        using Suc.prems(4) diff_step by simp
      then show ?thesis
        using pulled_one by simp
    qed
    obtain settled'' ds'' P'' S' beta' P1' where final:
      "bmssp_loop fuel G vertices ?settled ds' ?P2 =
        bmssp_normalize_dist ds''"
      "bmssp_dijkstra_loop_state vertices settled'' ds'' P''"
      "bmssp_singleton_bucket_shape P''"
      "distinct settled''"
      "set ?settled \<subseteq> set settled''"
      "bp_pull bmssp_block_size bmssp_bound P'' = (S', beta', P1')"
      "filter (\<lambda>x. x \<in> S' \<and> x \<notin> set settled'') vertices = []"
    proof -
      have "\<exists>settled_out ds_out P_out S_out beta_out P1_out.
        bmssp_loop fuel G vertices ?settled ds' ?P2 =
          bmssp_normalize_dist ds_out \<and>
        bmssp_dijkstra_loop_state vertices settled_out ds_out P_out \<and>
        bmssp_singleton_bucket_shape P_out \<and>
        distinct settled_out \<and>
        set ?settled \<subseteq> set settled_out \<and>
        bp_pull bmssp_block_size bmssp_bound P_out =
          (S_out, beta_out, P1_out) \<and>
        filter (\<lambda>x. x \<in> S_out \<and> x \<notin> set settled_out) vertices = []"
        by (rule Suc.IH[OF loop_state' shape' distinct_settled' fuel'])
      then show ?thesis
        by (elim exE conjE) (rule that)
    qed
    have loop_eq:
      "bmssp_loop (Suc fuel) G vertices settled ds P =
        bmssp_loop fuel G vertices ?settled ds' ?P2"
      using pull False relaxed by (simp add: Let_def)
    show ?thesis
    proof (intro exI conjI)
      show "bmssp_loop (Suc fuel) G vertices settled ds P =
          bmssp_normalize_dist ds''"
        using loop_eq final(1) by simp
      show "bmssp_dijkstra_loop_state vertices settled'' ds'' P''"
        by (rule final(2))
      show "bmssp_singleton_bucket_shape P''"
        by (rule final(3))
      show "distinct settled''"
        by (rule final(4))
      show "set settled \<subseteq> set settled''"
        using final(5) by auto
      show "bp_pull bmssp_block_size bmssp_bound P'' = (S', beta', P1')"
        by (rule final(6))
      show "filter (\<lambda>x. x \<in> S' \<and> x \<notin> set settled'') vertices = []"
        by (rule final(7))
    qed
  qed
qed

lemma bmssp_dijkstra_loop_state_lookup_exact_if_queue_empty:
  assumes loop_state: "bmssp_dijkstra_loop_state vertices settled ds P"
    and empty: "keys_of (bp_view P) = {}"
    and lookup: "bmssp_lookup_dist ds v = Some d"
  shows "real d = nat_graph_dist G src v"
proof -
  have state: "bmssp_dijkstra_state G src vertices settled ds P"
    using loop_state unfolding bmssp_dijkstra_loop_state_def by simp
  have match: "bmssp_partition_state_match vertices settled ds P"
    and exact: "bmssp_settled_exact G src settled ds"
    using state unfolding bmssp_dijkstra_state_def by auto
  have keys: "bmssp_partition_keys_match settled ds P"
    using match unfolding bmssp_partition_state_match_def by blast
  have v_key: "v \<in> set (map fst ds)"
    by (rule bmssp_lookup_dist_mem_key[OF lookup])
  have v_settled: "v \<in> set settled"
    using keys empty v_key unfolding bmssp_partition_keys_match_def by blast
  show ?thesis
    using exact v_settled lookup unfolding bmssp_settled_exact_def by blast
qed

lemma bmssp_dijkstra_loop_state_normalize_exact_if_queue_empty:
  assumes loop_state: "bmssp_dijkstra_loop_state vertices settled ds P"
    and empty: "keys_of (bp_view P) = {}"
    and mem: "(v, d) \<in> set (bmssp_normalize_dist ds)"
  shows "real d = nat_graph_dist G src v"
proof -
  have state: "bmssp_dijkstra_state G src vertices settled ds P"
    using loop_state unfolding bmssp_dijkstra_loop_state_def by simp
  have match: "bmssp_partition_state_match vertices settled ds P"
    using state unfolding bmssp_dijkstra_state_def by auto
  have distinct_ds: "distinct (map fst ds)"
    using match unfolding bmssp_partition_state_match_def by simp
  have mem_ds: "(v, d) \<in> set ds"
    using mem unfolding bmssp_normalize_dist_def by simp
  have lookup: "bmssp_lookup_dist ds v = Some d"
    by (rule bmssp_lookup_dist_Some_if_distinct_mem[OF distinct_ds mem_ds])
  show ?thesis
    by (rule bmssp_dijkstra_loop_state_lookup_exact_if_queue_empty
        [OF loop_state empty lookup])
qed

lemma bmssp_dijkstra_loop_state_normalize_reachable:
  assumes loop_state: "bmssp_dijkstra_loop_state vertices settled ds P"
    and mem: "(v, d) \<in> set (bmssp_normalize_dist ds)"
  shows "nat_graph_reachable G src v"
proof -
  have state: "bmssp_dijkstra_state G src vertices settled ds P"
    using loop_state unfolding bmssp_dijkstra_loop_state_def by simp
  have match: "bmssp_partition_state_match vertices settled ds P"
    and witnesses: "bmssp_label_witnesses G src settled ds"
    using state unfolding bmssp_dijkstra_state_def by auto
  have distinct_ds: "distinct (map fst ds)"
    using match unfolding bmssp_partition_state_match_def by simp
  have mem_ds: "(v, d) \<in> set ds"
    using mem unfolding bmssp_normalize_dist_def by simp
  have lookup: "bmssp_lookup_dist ds v = Some d"
    by (rule bmssp_lookup_dist_Some_if_distinct_mem[OF distinct_ds mem_ds])
  show ?thesis
    by (rule bmssp_label_witnesses_lookup_reachable[OF witnesses lookup])
qed

lemma bmssp_dijkstra_loop_state_reachable_lookup_if_queue_empty:
  assumes loop_state: "bmssp_dijkstra_loop_state vertices settled ds P"
    and empty: "keys_of (bp_view P) = {}"
    and reach: "nat_graph_reachable G src v"
  shows "\<exists>d. bmssp_lookup_dist ds v = Some d"
proof (rule ccontr)
  assume no_lookup: "\<not> (\<exists>d. bmssp_lookup_dist ds v = Some d)"
  have v_unsettled: "v \<notin> set settled"
  proof
    assume v_settled: "v \<in> set settled"
    have state: "bmssp_dijkstra_state G src vertices settled ds P"
      using loop_state unfolding bmssp_dijkstra_loop_state_def by simp
    have settled_lookup: "bmssp_settled_have_lookups settled ds"
      using state unfolding bmssp_dijkstra_state_def by simp
    then obtain d where "bmssp_lookup_dist ds v = Some d"
      using v_settled unfolding bmssp_settled_have_lookups_def by blast
    then show False
      using no_lookup by blast
  qed
  have state: "bmssp_dijkstra_state G src vertices settled ds P"
    using loop_state unfolding bmssp_dijkstra_loop_state_def by simp
  have match: "bmssp_partition_state_match vertices settled ds P"
    and source_zero: "bmssp_source_zero src ds"
    and settled_lookup: "bmssp_settled_have_lookups settled ds"
    and exact: "bmssp_settled_exact G src settled ds"
    and frontier: "bmssp_frontier_relaxed G src settled ds"
    using state unfolding bmssp_dijkstra_state_def by auto
  have reach': "concrete.reachable src v"
    using reach unfolding nat_graph_reachable_def .
  obtain p where sp: "concrete.shortest_walk src p v"
    using concrete.shortest_walk_exists[OF reach'] by blast
  obtain y dy where y_unsettled: "y \<notin> set settled"
    and lookup_y: "bmssp_lookup_dist ds y = Some dy"
    by (rule bmssp_shortest_walk_first_unsettled_lookup_le_dist
        [OF sp v_unsettled source_zero settled_lookup exact frontier])
      blast
  have keys: "bmssp_partition_keys_match settled ds P"
    using match unfolding bmssp_partition_state_match_def by blast
  have y_key: "y \<in> set (map fst ds)"
    by (rule bmssp_lookup_dist_mem_key[OF lookup_y])
  have "y \<in> keys_of (bp_view P)"
    using keys y_key y_unsettled
    unfolding bmssp_partition_keys_match_def by blast
  then show False
    using empty by simp
qed

lemma bmssp_dijkstra_loop_state_normalize_complete_if_queue_empty:
  assumes loop_state: "bmssp_dijkstra_loop_state vertices settled ds P"
    and empty: "keys_of (bp_view P) = {}"
    and reach: "nat_graph_reachable G src v"
  shows "\<exists>d. (v, d) \<in> set (bmssp_normalize_dist ds)"
proof -
  obtain d where lookup: "bmssp_lookup_dist ds v = Some d"
    using bmssp_dijkstra_loop_state_reachable_lookup_if_queue_empty
        [OF loop_state empty reach]
    by blast
  have mem_ds: "(v, d) \<in> set ds"
    by (rule bmssp_lookup_dist_Some_mem[OF lookup])
  have "(v, d) \<in> set (bmssp_normalize_dist ds)"
    using mem_ds unfolding bmssp_normalize_dist_def by simp
  then show ?thesis
    by blast
qed

lemma bmssp_dijkstra_loop_state_quiescent_pull_empty:
  assumes loop_state: "bmssp_dijkstra_loop_state vertices settled ds P"
    and pull: "bp_pull bmssp_block_size bmssp_bound P = (S, beta, P1)"
    and stopped:
      "filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices = []"
  shows "S = {}"
proof
  show "S \<subseteq> {}"
  proof
    fix x
    assume xS: "x \<in> S"
    have state: "bmssp_dijkstra_state G src vertices settled ds P"
      and ord: "bp_ordered_invariant P"
      and upper: "partition_upper_bound (bp_view P) bmssp_bound"
      using loop_state unfolding bmssp_dijkstra_loop_state_def by auto
    have match: "bmssp_partition_state_match vertices settled ds P"
      using state unfolding bmssp_dijkstra_state_def by simp
    have sep:
      "pull_separates (bp_view P) bmssp_block_size bmssp_bound S beta
        (bp_view P1)"
      by (rule bmssp_pull_refines_pull_separates[OF ord upper pull])
    have S_keys: "S \<subseteq> keys_of (bp_view P)"
      by (rule pull_separates_subset[OF sep])
    have keys_vertices: "keys_of (bp_view P) \<subseteq> set vertices"
      by (rule bmssp_partition_state_match_keys_subset[OF match])
    have keys: "bmssp_partition_keys_match settled ds P"
      using match unfolding bmssp_partition_state_match_def by blast
    have x_vertices: "x \<in> set vertices"
      using S_keys keys_vertices xS by blast
    have x_unsettled: "x \<notin> set settled"
      using keys S_keys xS unfolding bmssp_partition_keys_match_def by blast
    have "x \<in> set
        (filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices)"
      using xS x_vertices x_unsettled by simp
    then show "x \<in> {}"
      using stopped by simp
  qed
next
  show "{} \<subseteq> S"
    by simp
qed

lemma bmssp_dijkstra_loop_state_keys_empty_if_pull_empty:
  assumes loop_state: "bmssp_dijkstra_loop_state vertices settled ds P"
    and shape: "bmssp_singleton_bucket_shape P"
    and pull: "bp_pull bmssp_block_size bmssp_bound P = (S, beta, P1)"
    and S_empty: "S = {}"
  shows "keys_of (bp_view P) = {}"
proof (rule ccontr)
  assume nonempty: "keys_of (bp_view P) \<noteq> {}"
  have state: "bmssp_dijkstra_state G src vertices settled ds P"
    and ord: "bp_ordered_invariant P"
    using loop_state unfolding bmssp_dijkstra_loop_state_def by auto
  have match: "bmssp_partition_state_match vertices settled ds P"
    using state unfolding bmssp_dijkstra_state_def by simp
  have values_inj: "inj_on snd (set (bp_entries P))"
    by (rule bmssp_partition_entries_value_inj[OF match ord])
  have "S \<noteq> {}"
    by (rule bmssp_pull_nonempty_if_keys_nonempty
        [OF shape ord values_inj pull nonempty])
  then show False
    using S_empty by simp
qed

lemma bmssp_dijkstra_loop_state_quiescent_queue_empty:
  assumes loop_state: "bmssp_dijkstra_loop_state vertices settled ds P"
    and shape: "bmssp_singleton_bucket_shape P"
    and pull: "bp_pull bmssp_block_size bmssp_bound P = (S, beta, P1)"
    and stopped:
      "filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) vertices = []"
  shows "keys_of (bp_view P) = {}"
proof -
  have S_empty: "S = {}"
    by (rule bmssp_dijkstra_loop_state_quiescent_pull_empty
        [OF loop_state pull stopped])
  show ?thesis
    by (rule bmssp_dijkstra_loop_state_keys_empty_if_pull_empty
        [OF loop_state shape pull S_empty])
qed

definition bmssp_executable_distances_fuel :: nat where
  "bmssp_executable_distances_fuel =
     Suc (length (bmssp_vertices G src) * Suc (length G))"

definition bmssp_executable_initial_partition :: "nat bucketed_partition" where
  "bmssp_executable_initial_partition =
     bp_result_of
       (c_bp_regularized_local_insert src (bmssp_partition_key src 0)
         (bp_empty bmssp_block_size bmssp_bound))"

lemma bmssp_distances_unfold_executable:
  "bmssp_distances G src =
    bmssp_loop bmssp_executable_distances_fuel G (bmssp_vertices G src) []
      [(src, 0)] bmssp_executable_initial_partition"
  unfolding bmssp_distances_def bmssp_executable_distances_fuel_def
    bmssp_executable_initial_partition_def
  by (simp add: Let_def)

lemma bmssp_executable_initial_partition_singleton_shape:
  "bmssp_singleton_bucket_shape bmssp_executable_initial_partition"
proof -
  have empty_shape:
    "bmssp_singleton_bucket_shape (bp_empty bmssp_block_size bmssp_bound)"
    unfolding bmssp_singleton_bucket_shape_def bp_empty_def by simp
  show ?thesis
    unfolding bmssp_executable_initial_partition_def
    by (rule bmssp_singleton_bucket_shape_regularized_insert
        [OF empty_shape])
qed

lemma bmssp_dijkstra_loop_state_initial_executable:
  "bmssp_dijkstra_loop_state (bmssp_vertices G src) [] [(src, 0)]
    bmssp_executable_initial_partition"
proof -
  have src_vertices: "src \<in> set (bmssp_vertices G src)"
    using bmssp_vertices_set[of G src] by simp
  show ?thesis
    unfolding bmssp_executable_initial_partition_def
    by (rule bmssp_dijkstra_loop_state_initial[OF src_vertices])
qed

lemma bmssp_distances_quiescent_state_executable:
  obtains settled ds P S beta P1 where
    "bmssp_distances G src = bmssp_normalize_dist ds"
    "bmssp_dijkstra_loop_state (bmssp_vertices G src) settled ds P"
    "bmssp_singleton_bucket_shape P"
    "bp_pull bmssp_block_size bmssp_bound P = (S, beta, P1)"
    "filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled)
      (bmssp_vertices G src) = []"
proof -
  let ?vertices = "bmssp_vertices G src"
  have fuel_gt:
    "bmssp_executable_distances_fuel > length ?vertices - length ([] :: nat list)"
  proof (cases ?vertices)
    case Nil
    then show ?thesis
      unfolding bmssp_executable_distances_fuel_def by simp
  next
    case (Cons v vs)
    then show ?thesis
      unfolding bmssp_executable_distances_fuel_def by simp
  qed
  have distinct_empty: "distinct ([] :: nat list)"
    by simp
  have quiescent:
    "\<exists>settled ds P S beta P1.
      bmssp_loop bmssp_executable_distances_fuel G ?vertices []
        [(src, 0)] bmssp_executable_initial_partition =
          bmssp_normalize_dist ds \<and>
      bmssp_dijkstra_loop_state ?vertices settled ds P \<and>
      bmssp_singleton_bucket_shape P \<and>
      distinct settled \<and>
      set [] \<subseteq> set settled \<and>
      bp_pull bmssp_block_size bmssp_bound P = (S, beta, P1) \<and>
      filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) ?vertices = []"
    by (rule bmssp_loop_quiescent_state
        [OF bmssp_dijkstra_loop_state_initial_executable
          bmssp_executable_initial_partition_singleton_shape
          bmssp_edge_target_in_vertices bmssp_vertices_distinct
          distinct_empty fuel_gt])
  obtain settled ds P S beta P1 where final:
    "bmssp_loop bmssp_executable_distances_fuel G ?vertices []
        [(src, 0)] bmssp_executable_initial_partition =
          bmssp_normalize_dist ds"
    "bmssp_dijkstra_loop_state ?vertices settled ds P"
    "bmssp_singleton_bucket_shape P"
    "bp_pull bmssp_block_size bmssp_bound P = (S, beta, P1)"
    "filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled) ?vertices = []"
    using quiescent by blast
  have distances_eq: "bmssp_distances G src = bmssp_normalize_dist ds"
    using final(1) unfolding bmssp_distances_unfold_executable .
  show ?thesis
    by (rule that[OF distances_eq final(2) final(3) final(4) final(5)])
qed

theorem bmssp_correct_instance:
  shows
    "\<forall>(v, d)\<in>set (bmssp_distances G src).
       real d = nat_graph_dist G src v"
    "\<forall>v\<in>nat_graph_vertices G. nat_graph_reachable G src v \<longrightarrow>
       (\<exists>d. (v, d) \<in> set (bmssp_distances G src))"
proof -
  obtain settled ds P S beta P1 where final:
    "bmssp_distances G src = bmssp_normalize_dist ds"
    "bmssp_dijkstra_loop_state (bmssp_vertices G src) settled ds P"
    "bmssp_singleton_bucket_shape P"
    "bp_pull bmssp_block_size bmssp_bound P = (S, beta, P1)"
    "filter (\<lambda>x. x \<in> S \<and> x \<notin> set settled)
      (bmssp_vertices G src) = []"
    by (rule bmssp_distances_quiescent_state_executable)
  have empty: "keys_of (bp_view P) = {}"
    by (rule bmssp_dijkstra_loop_state_quiescent_queue_empty
        [OF final(2) final(3) final(4) final(5)])
  show "\<forall>(v, d)\<in>set (bmssp_distances G src).
       real d = nat_graph_dist G src v"
  proof
    fix p
    assume p_mem: "p \<in> set (bmssp_distances G src)"
    obtain v d where p_eq: "p = (v, d)"
      by force
    have norm_mem: "(v, d) \<in> set (bmssp_normalize_dist ds)"
      using p_mem p_eq final(1) by simp
    have exact: "real d = nat_graph_dist G src v"
      by (rule bmssp_dijkstra_loop_state_normalize_exact_if_queue_empty
          [OF final(2) empty norm_mem])
    show "case p of (v, d) \<Rightarrow> real d = nat_graph_dist G src v"
      using p_eq exact by simp
  qed
  show "\<forall>v\<in>nat_graph_vertices G. nat_graph_reachable G src v \<longrightarrow>
       (\<exists>d. (v, d) \<in> set (bmssp_distances G src))"
  proof
    fix v
    assume vV: "v \<in> nat_graph_vertices G"
    show "nat_graph_reachable G src v \<longrightarrow>
       (\<exists>d. (v, d) \<in> set (bmssp_distances G src))"
    proof
      assume reach: "nat_graph_reachable G src v"
      obtain d where norm_mem: "(v, d) \<in> set (bmssp_normalize_dist ds)"
        using bmssp_dijkstra_loop_state_normalize_complete_if_queue_empty
          [OF final(2) empty reach] by blast
      have "(v, d) \<in> set (bmssp_distances G src)"
        using norm_mem final(1) by simp
      then show "\<exists>d. (v, d) \<in> set (bmssp_distances G src)"
        by blast
    qed
  qed
qed

lemma bmssp_distances_executable_integral_on_keys:
  "real_label_integral_on (set (map fst (bmssp_distances G src)))
    (executable_label_of (bmssp_distances G src))"
  by (rule executable_label_integral_on_keys)
    (rule bmssp_distances_distinct_keys)

end

theorem bmssp_correct_executable:
  assumes "nat_graph_well_formed G"
    and "src \<in> nat_graph_vertices G"
  shows
    "\<forall>(v, d) \<in> set (bmssp_distances G src).
       real d = nat_graph_dist G src v"
    "\<forall>v \<in> nat_graph_vertices G. nat_graph_reachable G src v \<longrightarrow>
       (\<exists>d. (v, d) \<in> set (bmssp_distances G src))"
proof -
  interpret inst: nat_graph_instance G src
    by standard (rule assms(1), rule assms(2))
  have sound:
    "\<forall>(v, d) \<in> set (bmssp_distances G src).
       real d = nat_graph_dist G src v"
    by (rule inst.bmssp_correct_instance(1))
  have complete:
    "\<forall>v \<in> nat_graph_vertices G. nat_graph_reachable G src v \<longrightarrow>
       (\<exists>d. (v, d) \<in> set (bmssp_distances G src))"
    by (rule inst.bmssp_correct_instance(2))
  show "\<forall>(v, d) \<in> set (bmssp_distances G src).
       real d = nat_graph_dist G src v"
    by (rule sound)
  show "\<forall>v \<in> nat_graph_vertices G. nat_graph_reachable G src v \<longrightarrow>
       (\<exists>d. (v, d) \<in> set (bmssp_distances G src))"
    by (rule complete)
qed

end
