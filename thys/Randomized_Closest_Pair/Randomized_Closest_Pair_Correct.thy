section \<open>Correctness\<close>

text \<open>This section verifies that the algorithm always returns the correct result.

Because the algorithm checks every pair of points in the same or in neighboring cells. It is
enough to establish that the grid distance is at least the distance of the closest pair.

The latter is true by construction, because the grid distance is chosen as a minimum of actually
occurring point distances.\<close>

theory Randomized_Closest_Pair_Correct
  imports Randomized_Closest_Pair
begin

definition min_dist :: "('a::metric_space) list \<Rightarrow> real"
  where "min_dist xs = Min {dist x y|x y. {# x, y#} \<subseteq># mset xs}"

text \<open>For a list with length at least two, the result is the minimum distance between the points
of any two elements of the list. This means that @{term "min_dist xs = 0"}, if and only if the same
point occurs twice in the list.

Note that this means, we won't assume the distinctness of the input list, and show the correctness
of the algorithm in the above sense.\<close>

lemma image_conv_2: "{f x y|x y. p x y} = (case_prod f) ` {(x,y). p x y}" by auto

lemma min_dist_set_fin: "finite {dist x y|x y. {#x, y#} \<subseteq># mset xs}"
proof -
  have a:"finite (set xs \<times> set xs)" by simp
  have "x \<in># mset xs \<and> y \<in># mset xs" if "{#x, y#} \<subseteq># mset xs" for x y
    using that by (meson insert_union_subset_iff mset_subset_eq_insertD)
  thus ?thesis unfolding image_conv_2 by (intro finite_imageI finite_subset[OF _ a]) auto
qed

lemma min_dist_ne:  "length xs \<ge> 2 \<longleftrightarrow> {dist x y|x y. {# x,y#} \<subseteq># mset xs} \<noteq> {}" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then obtain xh1 xh2 xt where xs:"xs=xh1#xh2#xt" by (metis Suc_le_length_iff numerals(2))
  hence "{#xh1,xh2#} \<subseteq># mset xs" unfolding xs by simp
  thus ?R by auto
next
  assume ?R
  then obtain x y where xy: "{#x,y#} \<subseteq># mset xs" by auto
  have "2 \<le>  size {#x, y#}" by simp
  also have "... \<le> size (mset xs)" by (intro size_mset_mono xy)
  finally have "2 \<le> size (mset xs)" by simp
  thus ?L by simp
qed
lemmas min_dist_neI = iffD1[OF min_dist_ne]

lemma min_dist_nonneg:
  assumes "length xs \<ge> 2"
  shows "min_dist xs \<ge> 0"
  unfolding min_dist_def by (intro Min.boundedI min_dist_set_fin assms iffD1[OF min_dist_ne]) auto

lemma min_dist_pos_iff:
  assumes "length xs \<ge> 2"
  shows "distinct xs \<longleftrightarrow> 0 < min_dist xs"
proof -
  have "\<not>(distinct xs) \<longleftrightarrow> (\<exists>x. count (mset xs) x \<noteq> of_bool (x \<in> set xs))"
    unfolding of_bool_def distinct_count_atmost_1 by fastforce
  also have "... \<longleftrightarrow> (\<exists>x. count (mset xs) x \<notin> {0,1})"
    using count_mset_0_iff by (intro ex_cong1) simp
  also have "... \<longleftrightarrow> (\<exists>x. count (mset xs) x \<ge> count {#x, x#} x)"
    by (intro ex_cong1) (simp add:numeral_eq_Suc Suc_le_eq dual_order.strict_iff_order)
  also have "... \<longleftrightarrow> (\<exists>x. {#x, x#} \<subseteq># mset xs)" by (intro ex_cong1) (simp add: subseteq_mset_def)
  also have "... \<longleftrightarrow> 0 \<in> {dist x y |x y. {#x, y#} \<subseteq># mset xs}" by auto
  also have "... \<longleftrightarrow> min_dist xs = 0" (is "?L \<longleftrightarrow> ?R")
  proof
    assume "?L"
    hence "min_dist xs \<le> 0" unfolding min_dist_def by (intro Min_le min_dist_set_fin)
    thus "min_dist xs = 0" using min_dist_nonneg[OF assms] by auto
  next
    assume "?R"
    thus "0 \<in> {dist x y |x y. {#x, y#} \<subseteq># mset xs}"
      unfolding min_dist_def using Min_in[OF min_dist_set_fin min_dist_neI[OF assms]] by simp
  qed
  finally  have "\<not>(distinct xs) \<longleftrightarrow> min_dist xs = 0" by simp
  thus ?thesis using min_dist_nonneg[OF assms] by auto
qed

lemma multiset_filter_mono_2:
  assumes "\<And>x. x \<in> set_mset xs \<Longrightarrow> P x \<Longrightarrow> Q x"
  shows "filter_mset P xs \<subseteq># filter_mset Q xs" (is "?L \<subseteq># ?R")
proof -
  have "?L = filter_mset (\<lambda>x. Q x \<and> P x) xs" using assms by (intro filter_mset_cong) auto
  also have "... = filter_mset P (filter_mset Q xs)" by (simp add:filter_filter_mset)
  also have "... \<subseteq># ?R" by simp
  finally show ?thesis by simp
qed

lemma filter_mset_disj:
  "filter_mset (\<lambda>x. p x \<or> q x) xs = filter_mset (\<lambda>x. p x \<and> \<not> q x) xs + filter_mset q xs"
  by (induction xs) auto

lemma size_filter_mset_decompose:
  assumes "finite T"
  shows "size (filter_mset (\<lambda>x. f x \<in> T) xs) = (\<Sum>t \<in> T. size (filter_mset (\<lambda>x. f x = t) xs))"
  using assms
proof (induction T)
  case empty thus ?case by simp
next
  case (insert x F) thus ?case by (simp add:filter_mset_disj) metis
qed

lemma size_filter_mset_decompose':
  "size (filter_mset (\<lambda>x. f x \<in> T) xs) = sum' (\<lambda>t. size (filter_mset (\<lambda>x. f x = t) xs)) T"
  (is "?L = ?R")
proof -
  let ?T = "f ` set_mset xs \<inter> T"
  have "?L = size (filter_mset (\<lambda>x. f x \<in> ?T) xs)"
    by (intro arg_cong[where f="size"] filter_mset_cong) auto
  also have "... = (\<Sum>t \<in> ?T. size (filter_mset (\<lambda>x. f x = t) xs))"
    by (intro size_filter_mset_decompose) auto
  also have "... = sum' (\<lambda>t. size (filter_mset (\<lambda>x. f x = t) xs)) ?T"
    by (intro sum.eq_sum[symmetric]) auto
  also have "... = ?R" by (intro sum.mono_neutral_left') auto
  finally show ?thesis by simp
qed


lemma filter_product:
  "filter (\<lambda>x. P (fst x)\<and>Q (snd x)) (List.product xs ys) = List.product (filter P xs) (filter Q ys)"
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons xh xt) thus ?case by (simp add:filter_map comp_def)
qed

lemma floor_diff_bound: "\<bar>\<lfloor>x\<rfloor>-\<lfloor>y\<rfloor>\<bar> \<le> \<lceil>\<bar>x - (y::real)\<bar>\<rceil>" by linarith

lemma power2_strict_mono:
  fixes x y :: "'a :: linordered_idom"
  assumes "\<bar>x\<bar> < \<bar>y\<bar>"
  shows "x^2 < y^2"
  using assms unfolding power2_eq_square
  by (metis abs_mult_less abs_mult_self_eq)

definition "grid ps d = \<lparr> g_dist = d, g_lookup = (\<lambda>q. map_tm return (filter (\<lambda>x. to_grid d x = q) ps)) \<rparr>"

lemma build_grid_val: "val (build_grid ps d) = grid ps d"
  unfolding build_grid_def grid_def by simp

lemma lookup_neighborhood:
  "mset (val (lookup_neighborhood (grid ps d) p)) =
  filter_mset (\<lambda>x. to_grid d x - to_grid d p \<in> {(0,0),(0,1),(1,-1),(1,0),(1,1)}) (mset ps) - {#p#}"
proof -
  define ls where  "ls = [(0::int,0::int),(0,1),(1,-1),(1,0),(1,1)]"
  define g where "g = grid ps d"
  define cs where "cs = map ((+) (to_grid (g_dist g) p)) ([(0,0),(0,1),(1,-1),(1,0),(1,1)])"

  have distinct_ls: "distinct ls" unfolding ls_def by (simp add: upto.simps)

  have "mset (concat (map (\<lambda>x. val (g_lookup g (x + to_grid (g_dist g) p))) ls)) =
    mset (concat (map (\<lambda>x. filter (\<lambda>q. to_grid d q - to_grid d p = x) ps) ls))"
    by (simp add:grid_def filter_eq_val_filter_tm cs_def comp_def algebra_simps ls_def g_def)
  also have "... = {# q \<in># mset ps. to_grid d q - to_grid d p \<in> set ls #}"
    using distinct_ls by (induction ls) (simp_all add:filter_mset_disj, metis)
  also have "... = {#x \<in># mset ps. to_grid d x - to_grid d p \<in> {(0,0),(0,1),(1,-1),(1,0),(1,1)}#}"
    unfolding ls_def by simp
  finally have a:
    "mset (concat (map (\<lambda>x. val (g_lookup g (x + to_grid (g_dist g) p))) ls)) =
    {#x \<in># mset ps. to_grid d x - to_grid d p \<in> {(0,0),(0,1),(1,-1),(1,0),(1,1)}#}" by simp

  thus ?thesis
    unfolding g_def[symmetric] lookup_neighborhood_def ls_def[symmetric]
    by (simp add:val_remove1 comp_def)
qed

lemma fin_nat_pairs: "finite {(i, j). i < j \<and> j < (n::nat)}"
  by (rule finite_subset[where B="{..<n }\<times>{..<n}"]) auto

lemma mset_list_subset:
  assumes "distinct ys" "set ys \<subseteq> {..<length xs}"
  shows  "mset (map ((!) xs) ys) \<subseteq># mset xs" (is "?L \<subseteq># ?R")
proof -
  have "mset ys \<subseteq># mset [0..<length xs]" using assms
    by (metis finite_lessThan mset_set_set mset_set_upto_eq_mset_upto subset_imp_msubset_mset_set)
  hence "image_mset ((!) xs) (mset ys) \<subseteq># image_mset ((!) xs) (mset ([0..<length xs]))"
    by (intro image_mset_subseteq_mono)
  moreover have "image_mset ((!) xs) (mset ([0..<length xs])) = mset xs" by (metis map_nth mset_map)
  ultimately show ?thesis by simp
qed

lemma sample_distance:
  assumes "length ps \<ge> 2"
  shows "AE d in map_pmf val (sample_distance ps). min_dist ps \<le> d"
proof -
  let ?S = "{i. fst i < snd i \<and> snd i < length ps}"
  let ?p = "pmf_of_set ?S"

  have "(0,1) \<in> ?S" using assms by auto
  hence a:"finite ?S" "?S \<noteq> {}"
    using fin_nat_pairs[where n="length ps"] by (auto simp:case_prod_beta')

  have "min_dist ps \<le> dist (ps ! (fst x)) (ps ! (snd x))" if "x \<in> ?S" for x
  proof -
    have "mset (map ((!) ps) [fst x, snd x]) \<subseteq># mset ps"
      using that by (intro mset_list_subset) auto
    hence "{#ps ! fst x, ps ! snd x#} \<subseteq># mset ps" by simp
    hence "(\<lambda>(x, y). dist x y) (ps ! (fst x), ps ! (snd x)) \<in> {dist x y |x y. {#x, y#} \<subseteq># mset ps}"
      unfolding image_conv_2 by (intro imageI) simp
    thus ?thesis unfolding min_dist_def by (intro Min_le min_dist_set_fin) simp
  qed
  thus ?thesis
    using a unfolding sample_distance_def map_pmf_def[symmetric] val_tpmf_simps
    by (intro AE_pmfI) (auto)
qed

lemma first_phase:
  assumes "length ps \<ge> 2"
  shows "AE d in map_pmf val (first_phase ps). min_dist ps \<le> d"
proof -
  have "min_dist ps \<le> val (min_list_tm ds)"
    if ds_range:"set ds\<subseteq>set_pmf(map_pmf val (sample_distance ps))" and "length ds=length ps" for ds
  proof -
    have ds_ne: "ds \<noteq> []" using assms that(2) by auto

    have "min_dist ps \<le> a" if "a \<in> set ds" for a
    proof -
      have "a \<in> set_pmf (map_pmf val (sample_distance ps))" using ds_range that by auto
      thus ?thesis using sample_distance[OF assms] by (auto simp add: AE_measure_pmf_iff)
    qed
    hence "min_dist ps \<le> Min (set ds)" using ds_ne by (intro Min.boundedI) auto
    also have "... = min_list ds" unfolding min_list_Min[OF ds_ne] by simp
    also have "... = val (min_list_tm ds)" by (intro val_min_list[symmetric] ds_ne)
    finally show ?thesis by simp
  qed

  thus ?thesis
    unfolding first_phase_def val_tpmf_simps val_replicate_tpmf
    by (intro AE_pmfI) (auto simp:set_replicate_pmf)
qed

definition grid_lex_ord :: "int * int \<Rightarrow> int * int \<Rightarrow> bool"
  where "grid_lex_ord x y = (fst x < fst y \<or> (fst x = fst y \<and> snd x \<le> snd y))"

lemma grid_lex_order_antisym: "grid_lex_ord x y \<or> grid_lex_ord y x"
  unfolding grid_lex_ord_def by auto

lemma grid_dist:
  fixes p q :: point
  assumes "d > 0"
  shows  "\<bar>\<lfloor>p $ k/d\<rfloor> - \<lfloor>q $ k/d\<rfloor>\<bar> \<le> \<lceil>dist p q/d\<rceil>"
proof -
  have "\<bar>p$k - q$k\<bar> = sqrt ((p$k - q$k)^2)" by simp
  also have "... = sqrt (\<Sum>j\<in>UNIV. of_bool(j=k)*(p$j - q$j)^2)" by simp
  also have "... \<le> dist p q" unfolding dist_vec_def L2_set_def
    by (intro real_sqrt_le_mono sum_mono) (auto simp:dist_real_def)
  finally have "\<bar>p$k - q$k\<bar> \<le> dist p q" by simp
  hence 0:"\<bar>p$k /d - q$k /d\<bar>\<le> dist p q /d" using assms by (simp add:field_simps)
  have "\<bar>\<lfloor>p$k/d\<rfloor> - \<lfloor>q$k/d\<rfloor>\<bar> \<le> \<lceil>\<bar>p$k /d - q$k /d\<bar>\<rceil>" by (intro floor_diff_bound)
  also have "... \<le> \<lceil>dist p q/d\<rceil>" by (intro ceiling_mono 0)
  finally show ?thesis by simp
qed

lemma grid_dist_2:
  fixes p q :: point
  assumes "d > 0"
  assumes "\<lceil>dist p q/d\<rceil> \<le> s"
  shows  "to_grid d p - to_grid d q \<in> {-s..s}\<times>{-s..s}"
proof -
  have "f (to_grid d p) - f (to_grid d q) \<in> {-s..s}" if "f = fst \<or> f = snd" for f
  proof -
    have "\<bar>f (to_grid d p) - f (to_grid d q)\<bar> \<le> \<lceil>dist p q/d\<rceil>"
      using that grid_dist[OF assms(1)] unfolding to_grid_def by auto
    also have "... \<le> s" by (intro assms(2))
    finally have "\<bar>f (to_grid d p) - f (to_grid d q)\<bar> \<le> s" by simp
    thus ?thesis by auto
  qed
  thus ?thesis by (simp add:mem_Times_iff)
qed

lemma grid_dist_3:
  fixes p q :: point
  assumes "d > 0"
  assumes "\<lceil>dist q p/d\<rceil> \<le> 1" "grid_lex_ord (to_grid d p) (to_grid d q)"
  shows  "to_grid d q - to_grid d p \<in> {(0,0),(0,1),(1,-1),(1,0),(1,1)}"
proof -
  have a:"{-1..1} = {-1,0,1::int}" by auto
  let ?r = "to_grid d q - to_grid d p"
  have "?r \<in> {-1..1}\<times>{-1..1}" by (intro grid_dist_2 assms(1-2))
  moreover have "?r \<notin> {(-1,0),(-1,-1),(-1,1),(0,-1)}" using assms(3)
    unfolding grid_lex_ord_def insert_iff de_Morgan_disj
    by (intro conjI notI) (simp_all add:algebra_simps)
  ultimately show ?thesis unfolding a by simp
qed

lemma second_phase_aux:
  assumes "d > 0" "min_dist ps \<le> d" "length ps \<ge> 2"
  obtains u v where
    "min_dist ps = dist u v"
    "{#u, v#} \<subseteq># mset ps"
    "grid_lex_ord (to_grid d u) (to_grid d v)"
    "u \<in> set ps" "v \<in> set (val (lookup_neighborhood (grid ps d) u))"
proof -
  have "\<exists>u v. min_dist ps = dist u v \<and> {#u, v#} \<subseteq># mset ps"
    unfolding min_dist_def using Min_in[OF min_dist_set_fin min_dist_neI[OF assms(3)]] by auto

  then obtain u v where uv:
    "min_dist ps = dist u v" "{#u, v#} \<subseteq># mset ps"
    "grid_lex_ord (to_grid d u) (to_grid d v)"
    using add_mset_commute dist_commute grid_lex_order_antisym by (metis (no_types, lifting))

  have u_range: "u \<in> set ps" using uv(2) set_mset_mono by fastforce

  have "to_grid d v - to_grid d u \<in> {(0,0),(0,1),(1,-1),(1,0),(1,1)}"
    using assms(1,2) uv(1,3) by (intro grid_dist_3) (simp_all add:dist_commute)

  hence "v \<in># mset (val (lookup_neighborhood (grid ps d) u))"
    using uv(2) unfolding lookup_neighborhood by (simp add: in_diff_count insert_subset_eq_iff)

  thus ?thesis using that u_range uv by simp
qed

lemma second_phase:
  assumes "d > 0" "min_dist ps \<le> d" "length ps \<ge> 2"
  shows "val (second_phase d ps) = min_dist ps" (is "?L = ?R")
proof -
  let ?g = "grid ps d"

  have "\<exists>u v. min_dist ps = dist u v \<and> {#u, v#} \<subseteq># mset ps"
    unfolding min_dist_def using Min_in[OF min_dist_set_fin min_dist_neI[OF assms(3)]] by auto

  then obtain u v where uv:
    "min_dist ps = dist u v" "{#u, v#} \<subseteq># mset ps"
    "grid_lex_ord (to_grid d u) (to_grid d v)"
    and u_range: "u \<in> set ps"
    and v_range: "v \<in> set (val (lookup_neighborhood (grid ps d) u))"
    using second_phase_aux[OF assms] by auto

  hence a: "val (lookup_neighborhood (grid ps d) u) \<noteq> []" by auto

  have "\<exists>x\<in>set ps. min_dist ps \<in> dist x ` set (val (lookup_neighborhood (grid ps d) x))"
    using v_range uv(1) by (intro bexI[where x="u"] u_range) simp

  hence b: "Min (\<Union>x\<in>set ps. dist x ` set (val (lookup_neighborhood (grid ps d) x))) \<le> min_dist ps"
    by (intro Min.coboundedI finite_UN_I) simp_all

  have "{# x, y#} \<subseteq># mset ps"
    if "x \<in> set ps" "y \<in> set (val (lookup_neighborhood (grid ps d) x))" for x y
  proof -
    have "y \<in># mset (val (lookup_neighborhood (grid ps d) x))" using that by simp
    moreover have "mset (val (lookup_neighborhood (grid ps d) x)) \<subseteq>#  mset ps - {#x#}"
      using that(1) unfolding lookup_neighborhood subset_eq_diff_conv by simp
    ultimately have "y \<in># mset ps - {#x#}" by (metis mset_subset_eqD)
    moreover have "x \<in># mset ps" using that(1) by simp
    ultimately show "{#x, y#} \<subseteq># mset ps" by (simp add: insert_subset_eq_iff)
  qed
  hence c: "min_dist ps \<le> Min (\<Union>x\<in>set ps. dist x ` set (val (lookup_neighborhood (grid ps d) x)))"
    unfolding min_dist_def using a u_range by (intro Min_antimono min_dist_set_fin) auto

  have "?L = val (min_list_tm (concat (map (\<lambda>x. map (dist x) (val (lookup_neighborhood ?g x))) ps)))"
    unfolding second_phase_def by (simp add:calc_dists_neighborhood_def build_grid_val)
  also have "... = min_list (concat (map (\<lambda>x. map (dist x) (val (lookup_neighborhood ?g x))) ps))"
    using assms(3) a u_range by (intro val_min_list) auto
  also have "... = Min (\<Union>x\<in>set ps. dist x ` set (val (lookup_neighborhood ?g x)))"
    using a u_range by (subst min_list_Min) auto
  also have "... = min_dist ps" using b c by simp
  finally show ?thesis by simp
qed

text \<open>Main result of this section:\<close>

theorem closest_pair_correct:
  assumes "length ps \<ge> 2"
  shows "AE r in map_pmf val (closest_pair ps). r = min_dist ps"
proof -
  define fp where "fp = map_pmf val (first_phase ps)"

  have "r = min_dist ps" if
    "d \<in> fp"
    "r = (if d = 0 then 0 else val (second_phase d ps))" for r d
  proof -
    have d_ge: "d \<ge> min_dist ps"
      using that(1) first_phase[OF assms] unfolding AE_measure_pmf_iff fp_def[symmetric] by simp
    show ?thesis
    proof (cases "d > 0")
      case True
      thus ?thesis using second_phase[OF True d_ge assms] that(2)
        by (simp add: AE_measure_pmf_iff)
    next
      case False
      hence "d = 0" "min_dist ps = 0" using d_ge min_dist_nonneg[OF assms] by auto
      then show ?thesis using that(2) by auto
    qed
  qed
  thus ?thesis unfolding closest_pair_def val_tpmf_simps fp_def[symmetric] if_distrib
    by (intro AE_pmfI) (auto simp:if_distrib)
qed

end