theory Polygon_Convex_Lemmas
imports
  Polygon_Lemmas
  Linepath_Collinearity

begin

section "Misc. Convex Polygon Properties"

lemma polygon_path_image_subset_convex:
  assumes "length vts > 0"
  shows "path_image (make_polygonal_path vts) \<subseteq> convex hull (set vts)" (is "path_image ?p \<subseteq> ?S")
  using assms
proof(induct vts rule: make_polygonal_path.induct)
  case 1
  then show ?case by simp
next
  case (2 a)
  then show ?case by auto
next
  case (3 a b)
  show ?case (is "path_image ?p \<subseteq> ?S")
  proof(rule subsetI)
    fix x
    assume x_in_path_image: "x \<in> path_image ?p"
    then have "x \<in> path_image (linepath a b)" by auto
    thus "x \<in> ?S"
      unfolding path_image_def linepath_def
      by (smt (verit, ccfv_SIG) \<open>x \<in> path_image (linepath a b)\<close> convex_alt convex_convex_hull hull_subset in_mono in_segment(1) linepath_image_01 list.set_intros(1) path_image_def set_subset_Cons)
  qed
next
  case (4 a b c tl)
  let ?vts = "a # b # c # tl"
  show ?case (is "path_image ?p \<subseteq> ?S")
  proof(rule subsetI)
    fix x
    assume x_in_path_image: "x \<in> path_image ?p"
    show "x \<in> ?S"
    proof cases
      assume "x \<in> set ?vts"
      thus ?thesis by (simp add: hull_inc)
    next
      assume x_notin: "x \<notin> set ?vts"
      obtain u where p_u: "u \<in> {0..1} \<and> ?p u = x"
        using x_in_path_image unfolding path_image_def by auto
      then have p_head_tail: "?p = (linepath a b) +++ make_polygonal_path (b # c # tl)"
        by auto
      have abc_in_S: "set ?vts \<subseteq> convex hull (set ?vts)" by (simp add: hull_subset)
      { assume u_assm: "u \<le> 1/2"
        then have "?p u = (1 - 2 * u) *\<^sub>R a + (2 * u) *\<^sub>R b"
          using p_head_tail unfolding linepath_def joinpaths_def
          by presburger
        hence "x \<in> ?S"
          using abc_in_S convexD_alt[of ?S a b "2 * u"] u_assm p_u by simp
      } moreover
      { assume u_assm: "u > 1/2"
        then have "x = (make_polygonal_path (b # c # tl) (2 * u - 1))" (is "x = (?p' (2 * u - 1))")
          using p_head_tail p_u unfolding linepath_def joinpaths_def by auto
        moreover have "0 < (2 * u - 1)" using u_assm by linarith
        ultimately have "x \<in> path_image ?p'"
          using p_u by (simp add: path_image_def)
        moreover have "path_image ?p' \<subseteq> convex hull (set (b # c # tl))" using 4(1) by auto
        moreover have "... \<subseteq> convex hull (set (a # b # c # tl))"
          by (meson hull_mono set_subset_Cons)
        ultimately have "x \<in> ?S" by auto
      }
      ultimately show ?thesis by linarith
    qed
  qed
qed
  
lemma convex_contains_simple_closed_path_imp_contains_path_inside:
  assumes "convex S"
  assumes "simple_path p \<and> closed_path p"
  assumes "path_image p \<subseteq> S"
  shows "path_inside p \<subseteq> S"
  by (metis (no_types, opaque_lifting) Compl_subset_Compl_iff Un_subset_iff assms(1) assms(3) boolean_algebra_class.boolean_algebra.double_compl outside_subset_convex path_inside_def union_with_inside)

lemma convex_polygon_is_convex_hull:
  assumes "polygon p"
  assumes "convex (path_inside p \<union> path_image p)"
  assumes "p = make_polygonal_path vts"
  shows "convex hull (set vts) = path_inside p \<union> path_image p" (is "?hull = ?poly")
proof-
  have "?hull \<subseteq> ?poly"
  proof(rule subsetI)
    fix x
    assume "x \<in> ?hull"
    moreover have "\<forall>H. (convex H \<and> (set vts) \<subseteq> H) \<longrightarrow> ?hull \<subseteq> H" by (simp add: hull_minimal)
    moreover have "convex (?poly) \<and> (set vts) \<subseteq> ?poly"
      using assms(2) assms(3) vertices_on_path_image by auto
    ultimately show "x \<in> ?poly" by auto
  qed
  moreover have "?hull \<supseteq> ?poly"
  proof(rule subsetI)
    fix x
    assume "x \<in> ?poly"
    moreover have "path_image p \<subseteq> ?hull"
      using polygon_path_image_subset_convex[of vts] polygon_at_least_3_vertices assms
      by force
    moreover from calculation have "path_inside p \<subseteq> ?hull"
      using convex_contains_simple_closed_path_imp_contains_path_inside polygon_def assms(1)
      by auto
    ultimately show "x \<in> ?hull" by auto
  qed
  ultimately show ?thesis by auto
qed

lemma convex_polygon_inside_is_convex_hull_interior:
  assumes "polygon p"
  assumes "convex (path_inside p)"
  assumes "p = make_polygonal_path vts"
  shows "interior (convex hull (set vts)) = path_inside p"
  by (metis (no_types, lifting) assms closure_Un_frontier convex_closure convex_interior_closure convex_polygon_is_convex_hull inside_outside_def inside_outside_polygon interior_eq)

lemma convex_polygon_inside_is_convex_hull_interior2:
  assumes "polygon p"
  assumes "convex (path_inside p \<union> path_image p)"
  assumes "p = make_polygonal_path vts"
  shows "interior (convex hull (set vts)) = path_inside p"
  using assms closure_Un_frontier convex_closure convex_interior_closure convex_polygon_is_convex_hull inside_outside_def inside_outside_polygon interior_eq
  by (smt (verit, best) List.finite_set compact_eq_bounded_closed finite_imp_compact_convex_hull frontier_complement inside_frontier_eq_interior outside_inside path_inside_def path_outside_def sup_commute) 

lemma polygon_convex_iff:
  assumes "polygon p"
  shows "convex (path_inside p) \<longleftrightarrow> convex (path_inside p \<union> path_image p)"
  using convex_polygon_inside_is_convex_hull_interior
  using convex_polygon_inside_is_convex_hull_interior2
  by (metis Jordan_inside_outside_real2 closed_path_def assms closure_Un_frontier convex_closure convex_interior convex_polygon_is_convex_hull path_inside_def polygon_def polygon_to_polygonal_path)

lemma convex_polygon_frontier_is_path_image:
  assumes "polygon_of p vts"
  assumes "convex (path_inside p)"
  shows "frontier (convex hull (set vts)) = path_image p"
  using assms
  unfolding frontier_def polygon_of_def
  by (metis (no_types, lifting) Jordan_inside_outside_real2 closed_path_def convex_closure_interior convex_convex_hull convex_polygon_inside_is_convex_hull_interior frontier_def interior_interior path_inside_def polygon_def)

lemma convex_polygon_frontier_is_path_image2:
  assumes "polygon p"
  assumes "convex (path_inside p)"
  shows "frontier (path_image p \<union> path_inside p) = path_image p"
  using assms
  by (simp add: Jordan_inside_outside_real2 closed_path_def path_inside_def polygon_def union_with_inside)

lemma convex_polygon_frontier_is_path_image3:
  assumes "polygon p"
  assumes "convex (path_image p \<union> path_inside p)"
  shows "frontier (path_image p \<union> path_inside p) = path_image p"
  using assms polygon_convex_iff
  by (simp add: convex_polygon_frontier_is_path_image2 sup_commute)

lemma polygon_frontier_is_path_image:
  assumes "polygon p"
  shows "frontier (path_inside p) = path_image p"
  using inside_outside_polygon unfolding inside_outside_def
  using assms by presburger

lemma convex_path_inside_means_convex_polygon:
  assumes "polygon p"
  assumes "frontier (convex hull (set vts)) = path_image p"
  shows "convex (path_inside p)"
  by (metis List.finite_set assms(2) convex_convex_hull convex_interior finite_imp_bounded_convex_hull inside_frontier_eq_interior path_inside_def)

lemma convex_hull_of_polygon_is_convex_hull_of_vts:
 assumes "polygon_of p vts"
 shows "convex hull (path_image p \<union> path_inside p) = convex hull (set vts)"
proof - 
  have len_vts: "length vts > 0"
    by (metis assms card.empty empty_set length_greater_0_conv not_numeral_le_zero polygon_at_least_3_vertices polygon_of_def)
  have "path_image p \<union> path_inside p \<subseteq> convex hull (set vts)"
    using polygon_path_image_subset_convex[OF len_vts] 
    using assms convex_contains_simple_closed_path_imp_contains_path_inside polygon_def polygon_of_def by auto
  then have subset1: "convex hull (path_image p \<union> path_inside p) \<subseteq> convex hull (set vts)"
    by (simp add: convex_hull_subset)
  have "set vts \<subseteq> path_image p \<union> path_inside p" using assms vertices_on_path_image 
    by (simp add: polygon_of_def sup.coboundedI1)
  then have subset2: "convex hull (set vts) \<subseteq> convex hull (path_image p \<union> path_inside p)"
    by (simp add: hull_mono)
  show ?thesis using subset1 subset2 
    by auto
  qed

lemma convex_hull_frontier_polygon:
  assumes "polygon_of p vts"
  assumes "\<not> set vts \<subseteq> frontier (convex hull (set vts))"
  shows "\<not> convex (path_inside p)"
  by (metis assms(1) assms(2) convex_polygon_frontier_is_path_image polygon_of_def vertices_on_path_image)

lemma frontier_int_subset:
  assumes "A \<subseteq> B"
  shows "(frontier B) \<inter> A \<subseteq> frontier A"
  by (metis assms closure_Un_frontier frontier_Int inf.absorb_iff2 inf_sup_aci(1) subset_Un_eq sup_inf_distrib2)

lemma in_frontier_in_subset:
  assumes "A \<subseteq> B"
  assumes "x \<in> frontier B"
  assumes "x \<in> A"
  shows "x \<in> frontier A"
  by (metis assms frontier_int_subset IntI in_mono)

lemma in_frontier_in_subset_convex_hull:
  assumes "A \<subseteq> B"
  assumes "x \<in> frontier (convex hull B)"
  assumes "x \<in> convex hull A"
  shows "x \<in> frontier (convex hull A)"
  by (metis in_frontier_in_subset assms hull_mono)

lemma convex_hull_two_extreme_points:
  fixes S :: "'a::euclidean_space set"
  assumes "finite S"
  assumes "convex hull S \<noteq> {}"
  assumes "\<forall>x. convex hull S \<noteq> {x}"
  shows "card {x. x extreme_point_of (convex hull S)} \<ge> 2" (is "card ?ep \<ge> 2")
proof-
  have "compact (convex hull S)" by (simp add: assms(1) finite_imp_compact_convex_hull)
  then have "convex hull S = convex hull ?ep"
    using Krein_Milman_Minkowski[OF _ convex_convex_hull] by blast
  moreover then obtain x where "x \<in> ?ep" using assms(2) by fastforce
  moreover have "?ep \<noteq> {x}" using assms(3) calculation(1) by force
  ultimately obtain y where "x \<in> ?ep \<and> y \<in> ?ep \<and> x \<noteq> y" by blast
  moreover have "finite ?ep" using assms(1) extreme_points_of_convex_hull finite_subset by blast
  ultimately show ?thesis 
    by (metis (no_types, lifting) One_nat_def Orderings.order_eq_iff Suc_1 Suc_leI card_1_singletonE card_gt_0_iff empty_iff insert_Diff not_less_eq_eq singleton_insert_inj_eq)
qed

lemma convex_hull_two_vts_on_frontier:
  fixes S :: "'a::euclidean_space set"
  assumes "card S \<ge> 2"
  shows "card (S \<inter> frontier (convex hull S)) \<ge> 2"
proof-
  have "S \<subseteq> convex hull S" by (simp add: hull_subset)
  then have "convex hull S \<noteq> {} \<and> card (convex hull S) \<noteq> 1"
    by (metis Suc_1 add_leD2 assms card.empty card_1_singletonE convex_hull_eq_empty not_one_le_zero numeral_le_one_iff plus_1_eq_Suc semiring_norm(69) subset_singletonD)
  moreover have "finite S" using assms by (metis Suc_1 Suc_leD card_eq_0_iff not_one_le_zero)
  ultimately have "card {x. x extreme_point_of (convex hull S)} \<ge> 2"
    using convex_hull_two_extreme_points by fastforce
  moreover have "{x. x extreme_point_of (convex hull S)} \<subseteq> S \<inter> frontier (convex hull S)"
  proof-
    have "{x. x extreme_point_of (convex hull S)} \<subseteq> S" by (simp add: extreme_points_of_convex_hull)
    moreover have "{x. x extreme_point_of (convex hull S)} \<inter> interior (convex hull S) = {}"
      using extreme_point_not_in_interior by blast
    moreover have "{x. x extreme_point_of (convex hull S)} \<subseteq> convex hull S"
      using \<open>S \<subseteq> convex hull S\<close> calculation(1) by blast
    moreover have "convex hull S = interior (convex hull S) \<union> frontier (convex hull S)"
      by (metis (no_types, lifting) Diff_empty Suc_1 assms card.infinite closure_Un_frontier closure_convex_hull convex_closure_interior convex_convex_hull empty_subsetI finite_imp_compact frontier_def interior_interior not_less_eq_eq sup_absorb2 zero_less_one_class.zero_le_one)
    ultimately show ?thesis by blast
  qed
  ultimately show ?thesis
    by (smt (verit, del_insts) assms extreme_points_of_convex_hull card_gt_0_iff finite_Int linorder_not_less not_numeral_le_zero order_less_le order_less_le_trans psubset_card_mono)
qed

section "Vertices on Convex Frontier Implies Polygon is Convex"

lemma convex_cut_aux:
  assumes "\<forall>v \<in> S. z \<bullet> v \<le> 0"
  shows "convex hull S \<subseteq> {x. z \<bullet> x \<le> 0}"
  by (simp add: assms convex_halfspace_le hull_minimal subsetI)

lemma convex_cut_aux':
  assumes "\<forall>v \<in> S. z \<bullet> v \<ge> 0"
  shows "convex hull S \<subseteq> {x. z \<bullet> x \<ge> 0}"
  using convex_cut_aux[of S "-z"] assms by auto

lemma convex_cut:
  assumes "z \<noteq> 0"
  assumes "{x. z \<bullet> x = 0} \<inter> interior (convex hull S) \<noteq> {}"
  obtains v1 v2 where "v1 \<noteq> v2 \<and> {v1, v2} \<subseteq> S \<and> v1 \<in> {x. z \<bullet> x < 0} \<and> v2 \<in> {x. z \<bullet> x > 0}"
proof-
  let ?P1 = "{x. z \<bullet> x \<le> 0}"
  let ?P2 = "{x. z \<bullet> x \<ge> 0}"
  have "frontier ?P1 = {x. z \<bullet> x = 0}"
    by (simp add: assms(1) frontier_halfspace_le)
  moreover have "frontier ?P2 = {x. z \<bullet> x = 0}"
    by (simp add: assms(1) frontier_halfspace_ge)
  ultimately have "\<not> convex hull S \<subseteq> ?P1 \<and> \<not> convex hull S \<subseteq> ?P2"
    by (smt (verit, ccfv_SIG) DiffE IntE assms(2) disjoint_iff frontier_def inf.absorb_iff2 interior_Int)
  moreover have "(\<forall>v \<in> S. z \<bullet> v \<le> 0) \<Longrightarrow> convex hull S \<subseteq> ?P1" using convex_cut_aux by blast
  moreover have "(\<forall>v \<in> S. z \<bullet> v \<ge> 0) \<Longrightarrow> convex hull S \<subseteq> ?P2" using convex_cut_aux' by blast
  ultimately obtain v1 v2 where "{v1, v2} \<subseteq> S \<and> z \<bullet> v1 < 0 \<and> z \<bullet> v2 > 0"
    using linorder_not_le by auto
  thus ?thesis using that by fastforce
qed

lemma affine_2_int_convex:
  fixes S :: "'a::euclidean_space set"
  assumes "{a, b} \<subseteq> S"
  assumes "{a, b} \<subseteq> frontier (convex hull S)"
  assumes "affine hull {a, b} \<inter> interior (convex hull S) \<noteq> {}"
  shows "affine hull {a, b} \<inter> convex hull S = convex hull {a, b}"
proof-
  let ?H = "convex hull S"
  let ?L = "affine hull {a, b} \<inter> ?H"
  have 1: "?L \<supseteq> convex hull {a, b}"
    by (meson Int_greatest assms(1) convex_hull_subset_affine_hull hull_mono)
  moreover have "?L \<subseteq> convex hull {a, b}"
  proof(rule subsetI)
    fix x
    assume *: "x \<in> ?L"
    then obtain u v where uv: "x = u *\<^sub>R a + v *\<^sub>R b \<and> u + v = 1" using affine_hull_2 by blast
    
    have "rel_interior ?L \<subseteq> rel_interior ?H"
      using subset_rel_interior_convex[of ?L ?H]
      by (metis assms(3) convex_affine_hull convex_convex_hull convex_rel_interior_inter_two inf_bot_right inf_le2 rel_interior_affine_hull rel_interior_nonempty_interior)
    moreover have ab_frontier: "a \<in> frontier ?H \<and> b \<in> frontier ?H" using assms by blast
    ultimately have ab_rel_frontier: "a \<in> rel_frontier ?L \<and> b \<in> rel_frontier ?L"
      by (metis IntI affine_affine_hull assms(3) convex_affine_rel_frontier_Int convex_convex_hull hull_subset inf_commute insert_subset)

    { assume **: "u < 0"
      then have "b \<in> open_segment a x"
      proof-
        from uv have "b = (1/v) *\<^sub>R x - (u/v) *\<^sub>R a"
          by (smt (verit, ccfv_threshold) ** divide_inverse_commute inverse_eq_divide real_vector_affinity_eq vector_space_assms(3) Groups.add_ac(2))
        moreover from uv have "1/v - u/v = 1"
          by (metis "**" add.commute add_cancel_right_left diff_divide_distrib divide_self_if eq_diff_eq' not_one_less_zero)
        ultimately have "b = (1 - 1/v) *\<^sub>R a + (1/v) *\<^sub>R x" by (simp add: diff_eq_eq)
        moreover from uv ** have "0 < 1/v \<and> 1/v < 1" by simp
        ultimately show ?thesis
          by (metis "1" ab_rel_frontier affine_hull_sing convex_hull_singleton empty_iff equalityI in_segment(2) inf_le1 insert_absorb rel_frontier_sing scaleR_collapse singletonI)
      qed
      then have "b \<in> rel_interior (convex hull {a, x})"
        by (metis empty_iff open_segment_idem rel_interior_closed_segment segment_convex_hull)
      moreover have "x \<in> ?H" using * by blast
      ultimately have "b \<in> interior ?H"
        by (smt (verit, ccfv_threshold) "*" IntD2 Int_empty_right 1 affine_affine_hull affine_hull_affine_Int_nonempty_interior affine_hull_convex_hull assms(3) convex_Int convex_affine_hull convex_convex_hull convex_rel_interior_inter_two hull_hull hull_redundant_eq insert_commute insert_subsetI rel_interior_affine_hull rel_interior_mono rel_interior_nonempty_interior rel_interior_subset subset_hull subset_iff)
      then have False by (metis DiffD2 ab_frontier frontier_def)
    } moreover
    { assume **: "v < 0"
      then have "a \<in> open_segment b x"
      proof-
        from uv have "a = (1/u) *\<^sub>R x - (v/u) *\<^sub>R b"
          by (smt (verit, ccfv_threshold) ** divide_inverse_commute inverse_eq_divide real_vector_affinity_eq vector_space_assms(3) Groups.add_ac(2))
        moreover from uv have "1/u - v/u = 1"
          by (metis "**" add_cancel_right_left diff_divide_distrib divide_self_if eq_diff_eq' not_one_less_zero)
        ultimately have "a = (1 - 1/u) *\<^sub>R b + (1/u) *\<^sub>R x" by (simp add: diff_eq_eq)
        moreover from uv ** have "0 < 1/u \<and> 1/u < 1" by simp
        ultimately show ?thesis
          by (metis "1" ab_rel_frontier affine_hull_sing convex_hull_singleton empty_iff equalityI in_segment(2) inf_le1 insert_absorb rel_frontier_sing scaleR_collapse singletonI)
      qed
      then have "a \<in> rel_interior (convex hull {b, x})"
        by (metis empty_iff open_segment_idem rel_interior_closed_segment segment_convex_hull)
      moreover have "x \<in> ?H" using * by blast
      ultimately have "a \<in> interior ?H"
        by (smt (verit, ccfv_threshold) "*" IntD2 Int_empty_right 1 affine_affine_hull affine_hull_affine_Int_nonempty_interior affine_hull_convex_hull assms(3) convex_Int convex_affine_hull convex_convex_hull convex_rel_interior_inter_two hull_hull hull_redundant_eq insert_commute insert_subsetI rel_interior_affine_hull rel_interior_mono rel_interior_nonempty_interior rel_interior_subset subset_hull subset_iff)
      then have False by (metis DiffD2 ab_frontier frontier_def)
    }
    ultimately have "0 \<le> u \<and> u \<le> 1 \<and> 0 \<le> v \<and> v \<le> 1" using uv by argo
    thus "x \<in> convex hull {a, b}" by (simp add: convexD hull_inc uv)
  qed
  ultimately show ?thesis by blast
qed

lemma halfplane_frontier_affine_hull:
  fixes b v :: "real^2"
  assumes "b \<noteq> 0"
  assumes "v \<noteq> 0"
  assumes "b \<in> {x. v \<bullet> x = 0}"
  shows "{x. v \<bullet> x = 0} = affine hull {0, b}"
proof-
  let ?F = "{x. v \<bullet> x = 0}"
  let ?A = "affine hull {0, b}"
  have "?F \<subseteq> ?A"
  proof(rule subsetI)
    fix y
    assume *: "y \<in> ?F"
    have "y \<in> ?A" if "y = 0" by (simp add: assms(2) hull_inc that)
    moreover have "y \<in> ?A" if "b$1 \<noteq> 0"
    proof-
      have "v \<bullet> y = 0" using * by fast
      moreover have "v \<bullet> b = 0" using assms by force
      moreover have "v \<bullet> y = v$1 * y$1 + v$2 * y$2" by (simp add: inner_vec_def sum_2 real_2_inner)
      moreover have "v \<bullet> b = v$1 * b$1 + v$2 * b$2" by (simp add: inner_vec_def sum_2 real_2_inner)
      ultimately have 0: "v$1 * y$1 + v$2 * y$2 = 0 \<and> 0 = v$1 * b$1 + v$2 * b$2" by auto
      moreover obtain c where c: "y$1 = c * b$1" using \<open>b$1 \<noteq> 0\<close>
        by (metis hyperplane_eq_Ex inner_real_def mult.commute)
      ultimately have "v$1 * y$1 + v$2 * y$2 = 0 \<and> 0 = c * v$1 * b$1 + c * v$2 * b$2" by algebra
      then have "v$1 * y$1 + v$2 * y$2 = v$1 * y$1 + c * v$2 * b$2" using c by algebra
      then have "v$2 * y$2 = c * v$2 * b$2" by argo
      then have "y$2 = c * b$2"
        by (smt (verit, ccfv_threshold) 0 exhaust_2 mult.commute mult.left_commute mult_cancel_left that assms vec_eq_iff zero_index)
      then have "y = c *\<^sub>R b" using c
        by (smt (verit) exhaust_2 real_scaleR_def vec_eq_iff vector_scaleR_component)
      then have "y \<in> span {0, b}" by (meson insert_subset span_mul span_superset)
      thus "y \<in> ?A"
        by (simp add: affine_hull_span_0 assms(2) hull_inc)
    qed
    moreover have "y \<in> ?A" if "b$2 \<noteq> 0"
    proof-
      have "v \<bullet> y = 0" using * by fast
      moreover have "v \<bullet> b = 0" using assms by force
      moreover have "v \<bullet> y = v$1 * y$1 + v$2 * y$2" by (simp add: inner_vec_def sum_2 real_2_inner)
      moreover have "v \<bullet> b = v$1 * b$1 + v$2 * b$2" by (simp add: inner_vec_def sum_2 real_2_inner)
      ultimately have 0: "v$1 * y$1 + v$2 * y$2 = 0 \<and> 0 = v$1 * b$1 + v$2 * b$2" by auto
      moreover obtain c where c: "y$2 = c * b$2" using \<open>b$2 \<noteq> 0\<close>
        by (metis hyperplane_eq_Ex inner_real_def mult.commute)
      ultimately have "v$1 * y$1 + v$2 * y$2 = 0 \<and> 0 = c * v$1 * b$1 + c * v$2 * b$2" by algebra
      then have "v$1 * y$1 + v$2 * y$2 = 0 \<and> 0 = c * v$1 * b$1 + v$2 * y$2" using c by algebra
      then have "v$1 * y$1 = c * v$1 * b$1" by argo
      then have "y$1 = c * b$1"
        by (smt (verit, ccfv_threshold) 0 exhaust_2 mult.commute mult.left_commute mult_cancel_left that assms vec_eq_iff zero_index)
      then have "y = c *\<^sub>R b" using c
        by (smt (verit) exhaust_2 real_scaleR_def vec_eq_iff vector_scaleR_component)
      then have "y \<in> span {0, b}" by (meson insert_subset span_mul span_superset)
      thus "y \<in> ?A"
        by (simp add: affine_hull_span_0 assms(2) hull_inc)
    qed
    ultimately show "y \<in> ?A"
      by (metis (mono_tags, opaque_lifting) assms(1) exhaust_2 vec_eq_iff zero_index)
  qed
  moreover have "?A \<subseteq> ?F"
  proof(rule subsetI)
    fix x
    assume "x \<in> ?A"
    then obtain \<alpha> \<beta> where "x = \<alpha> *\<^sub>R 0 + \<beta> *\<^sub>R b \<and> \<alpha> + \<beta> = 1" using affine_hull_2 by blast
    then have "v \<bullet> x = \<alpha> * (v \<bullet> 0) + \<beta> * (v \<bullet> b)" by (simp add: assms(1))
    then have "v \<bullet> x = 0" using assms(3) by auto
    thus "x \<in> ?F" by fast
  qed
  ultimately show ?thesis by blast
qed

lemma vts_on_convex_frontier_aux:
  assumes "polygon_of p vts"
  assumes "vts!0 = 0"
  assumes "set vts \<subseteq> frontier (convex hull (set vts))"
  shows "path_image (linepath (vts!0) (vts!1)) \<subseteq> frontier (convex hull (set vts))"
proof-
  let ?H = "convex hull (set vts)"
  let ?a = "vts!0"
  let ?b = "vts!1"
  let ?l = "linepath ?a ?b"
  let ?L = "path_image ?l"
  let ?A = "affine hull {?a, ?b}"
  let ?x = "?b - ?a"

  obtain v where v: "v \<bullet> ?x = 0 \<and> v \<noteq> 0"
  proof-
    let ?v = "(vector [?x$2, -?x$1])::(real^2)"
    have "?a \<noteq> ?b"
      by (smt (verit, best) Cons_nth_drop_Suc One_nat_def Suc_le_eq arc_distinct_ends assms(1) assms(2) card.empty drop0 empty_set length_greater_0_conv list.sel(1) list.sel(3) make_polygonal_path.elims make_polygonal_path.simps(1) make_polygonal_path.simps(2) nth_drop pathfinish_linepath pathstart_linepath plus_1_eq_Suc polygon_at_least_3_vertices polygon_def polygon_of_def polygon_pathstart rel_simps(28) simple_path_joinE)
    then have "?x \<noteq> 0" by simp
    then have "?v \<bullet> ?x = 0 \<and> ?v \<noteq> 0"
    proof-
      have "?v \<bullet> ?x = (?x$2 * ?x$1) + (-?x$1 * ?x$2)"
        by (simp add: inner_vec_def sum_2 real_2_inner)
      then have "?v \<bullet> ?x = 0" by argo
      moreover have "?v \<noteq> 0"
        by (smt (verit, best) \<open>?x \<noteq> 0\<close> exhaust_2 vec_eq_iff vector_2(1) vector_2(2) zero_index)
      ultimately show ?thesis by blast
    qed
    thus ?thesis using that by blast
  qed

  let ?P1 = "{x. v \<bullet> x \<le> 0}"
  let ?P2 = "{x. v \<bullet> x \<ge> 0}"
  let ?P1_int = "{x. v \<bullet> x < 0}"
  let ?P2_int = "{x. v \<bullet> x > 0}"
  let ?F = "{x. v \<bullet> x = 0}"

  have "?b \<noteq> 0"
    by (smt (verit) Cons_nth_drop_Suc One_nat_def Suc_le_eq Suc_le_length_iff arc_distinct_ends assms(1) assms(2) card.empty drop0 drop_eq_Nil empty_set le_numeral_extra(4) length_greater_0_conv list.inject make_polygonal_path.elims make_polygonal_path.simps(2) nat_less_le pathfinish_linepath pathstart_linepath polygon_at_least_3_vertices polygon_def polygon_of_def polygon_pathstart rel_simps(28) simple_path_joinE)
  moreover have "?b \<in> ?F" using assms(2) v by auto
  ultimately have F: "?F = ?A"
    using halfplane_frontier_affine_hull[of ?b v] v assms(2) by presburger
  moreover have "?L \<subseteq> ?A" by (simp add: convex_hull_subset_affine_hull segment_convex_hull)
  ultimately have L_subset_F: "?L \<subseteq> ?F" by blast
  have L_subset_H: "?L \<subseteq> ?H"
    by (metis (no_types, lifting) add_gr_0 assms(1) card.empty convex_contains_segment convex_convex_hull diff_less empty_set hull_subset leD length_greater_0_conv less_numeral_extra(1) nth_mem numeral_3_eq_3 path_image_linepath plus_1_eq_Suc polygon_at_least_3_vertices polygon_of_def rotate_polygon_vertices_same_set rotated_polygon_vertices_helper(2) subset_code(1))

  have frontier_P1: "frontier ?P1 = ?F" by (simp add: v frontier_halfspace_le)
  have frontier_P2: "frontier ?P2 = ?F" by (simp add: v frontier_halfspace_ge)
  have interior_P1: "interior ?P1 = ?P1_int" by (simp add: v)
  have interior_P2: "interior ?P2 = ?P2_int" by (simp add: v)
  have convex_P1: "convex ?P1" by (simp add: convex_halfspace_le)
  have convex_P2: "convex ?P2" by (simp add: convex_halfspace_ge)
  have P1_int_P2: "?P1 \<inter> ?P2 = ?F" by (simp add: halfspace_Int_eq(1))
  
  let ?H1 = "?H \<inter> ?P1"  
  let ?H2 = "?H \<inter> ?P2"

  have "\<not> collinear (set vts)" using polygon_vts_not_collinear assms(1) by simp
  then have nonempty_interior_H: "interior ?H \<noteq> {}"
    by (smt (verit, ccfv_SIG) Jordan_inside_outside_real2 closed_path_def Un_Int_eq(4) assms(1) convex_hull_of_polygon_is_convex_hull_of_vts disjoint_iff hull_subset inf.orderE interior_Int interior_eq interior_subset path_inside_def polygon_def polygon_of_def)

  have convex_H1: "convex ?H1" by (simp add: convex_Int convex_P1)
  have convex_H2: "convex ?H2" by (simp add: convex_Int convex_P2)

  have "?H \<subseteq> ?P1 \<or> ?H \<subseteq> ?P2"
  proof(rule ccontr)
    assume *: "\<not> (?H \<subseteq> ?P1 \<or> ?H \<subseteq> ?P2)"
    moreover have "interior ?H \<subseteq> ?P1 \<Longrightarrow> ?H \<subseteq> ?P1"
      by (metis (no_types, lifting) Int_Un_eq(3) Krein_Milman_frontier List.finite_set P1_int_P2 closure_Un_frontier closure_convex_hull closure_mono compact_frontier convex_closure_interior convex_convex_hull finite_imp_compact_convex_hull frontier_P1 nonempty_interior_H)
    moreover have "interior ?H \<subseteq> ?P2 \<Longrightarrow> ?H \<subseteq> ?P2"
      by (metis (no_types, lifting) Int_Un_eq(3) Krein_Milman_frontier List.finite_set P1_int_P2 calculation(1) calculation(2) closure_Un_frontier closure_convex_hull closure_mono compact_frontier convex_closure_interior convex_convex_hull emptyE finite_imp_compact_convex_hull frontier_P2 inf_commute subsetI)
    ultimately have "interior ?H \<inter> ?P1 \<noteq> {} \<and> interior ?H \<inter> -?P1 \<noteq> {}" by force
    moreover have "path_connected (interior ?H)" by (simp add: convex_imp_path_connected)
    ultimately have F_int_interior_H: "?F \<inter> interior ?H \<noteq> {}"
      by (metis (no_types, lifting) path_connected_frontier ComplD disjoint_eq_subset_Compl frontier_P1 subset_eq)
    then obtain v1 v2 where v1v2: "v1 \<noteq> v2 \<and> {v1, v2} \<subseteq> set vts
        \<and> v1 \<in> interior ?P1 \<and> v2 \<in> interior ?P2"
      using convex_cut frontier_P1 interior_P1 interior_P2 v by metis
    then obtain i j where ij: "vts!i = v1 \<and> vts!j = v2
        \<and> 2 \<le> i \<and> 2 \<le> j \<and> i \<noteq> j \<and> i < length vts - 1 \<and> j < length vts - 1"
    proof-
      obtain i j where "vts!i = v1 \<and> vts!j = v2 \<and> i \<noteq> j \<and> i < length vts \<and> j < length vts"
        by (metis in_set_conv_nth insert_subset v1v2)
      moreover have "2 \<le> i"
      proof-
        { assume "i = 0 \<or> i = 1"
          then have "vts!i = ?a \<or> vts!i = ?b" by blast
          then have "vts!i \<in> ?F" by (simp add: F hull_inc)
          then have False using calculation(1) interior_P1 v1v2 by auto
        }
        thus ?thesis by presburger
      qed
      moreover have "2 \<le> j"
      proof-
        { assume "j = 0 \<or> j = 1"
          then have "vts!j = ?a \<or> vts!j = ?b" by blast
          then have "vts!j \<in> ?F" by (simp add: F hull_inc)
          then have False using calculation(1) interior_P2 v1v2 by auto
        }
        thus ?thesis by presburger
      qed
      moreover have False if "i = length vts - 1"
        by (metis (no_types, lifting) F assms(1) calculation(1) frontier_P1 frontier_def have_wraparound_vertex hull_subset insertCI insert_Diff last_conv_nth last_snoc less_nat_zero_code list.size(3) polygon_of_def subset_Diff_insert that v1v2)
      moreover have False if "j = length vts - 1"
        by (metis (no_types, lifting) F assms(1) calculation(1) frontier_P2 frontier_def have_wraparound_vertex hull_subset insertCI insert_Diff last_conv_nth last_snoc less_nat_zero_code list.size(3) polygon_of_def subset_Diff_insert that v1v2)
      ultimately show ?thesis using that by fastforce
    qed

    let ?i' = "min i j"
    let ?j' = "max i j"
    let ?vts' = "take (?j' - ?i' + 1) (drop ?i' vts)"
    let ?p' = "make_polygonal_path ?vts'"
    have vts'_sublist: "sublist ?vts' vts" using sublist_order.order.trans by blast
    then have vts'_sublist_tl: "sublist ?vts' (tl vts)"
      by (metis Suc_1 Suc_eq_plus1 drop_Suc ij max_def min_def nat_minus_add_max not_less_eq_eq sublist_drop sublist_order.dual_order.trans sublist_take)

    have p'_start_finish: "{pathstart ?p', pathfinish ?p'} = {v1, v2}"
    proof-
      have "?vts'!0 = vts!?i'" using ij by force
      moreover have "?vts'!(?j' - ?i') = vts!?j'"
        using diff_is_0_eq diff_zero ij less_numeral_extra(1) max.cobounded1 min_absorb2 min_def nth_drop nth_take order_less_imp_le
        by fastforce
      moreover have "(vts!?i' = v1 \<and> vts!?j' = v2) \<or> (vts!?i' = v2 \<and> vts!?j' = v1)"
        using ij by linarith
      moreover have "pathstart ?p' = ?vts'!0 \<and> pathfinish ?p' = ?vts'!(?j' - ?i')"
        using ij min_diff polygon_pathfinish polygon_pathstart
        by (smt (verit, ccfv_SIG) add_diff_cancel_right' add_diff_inverse_nat length_drop length_take less_diff_conv max.commute max_min_same(1) min.absorb4 nat_minus_add_max not_add_less2 plus_1_eq_Suc plus_nat.simps(2) take_eq_Nil zero_less_one)
      ultimately show ?thesis by auto
    qed
    then have "path_image ?p' \<inter> interior ?P2 \<noteq> {} \<and> path_image ?p' \<inter> interior ?P1 \<noteq> {}"
      by (metis v1v2 IntI doubleton_eq_iff empty_iff pathfinish_in_path_image pathstart_in_path_image)
    then have "path_image ?p' \<inter> -?P1 \<noteq> {} \<and> path_image ?p' \<inter> ?P1 \<noteq> {}"
      using interior_P2
      by (smt (verit, best) disjoint_iff_not_equal in_mono inf_shunt interior_P1 mem_Collect_eq)
    moreover have "path_connected (path_image ?p')"
      using make_polygonal_path_gives_path path_connected_path_image by blast
    ultimately obtain z where z: "z \<in> path_image ?p' \<inter> ?F"
      by (smt (verit, del_insts) path_connected_frontier DiffE Diff_triv all_not_in_conv frontier_P1)
    moreover have "path_image ?p' \<subseteq> ?H"
    proof-
      have "path_image p \<subseteq> ?H"
        by (metis assms(1) insert_subset length_pos_if_in_set polygon_of_def polygon_path_image_subset_convex v1v2)
      moreover have "path_image ?p' \<subseteq> path_image p"
        by (metis (no_types, lifting) vts'_sublist sublist_path_image_subset One_nat_def Suc_leI p'_start_finish assms(1) doubleton_eq_iff length_greater_0_conv make_polygonal_path.simps(1) pathfinish_linepath pathstart_linepath polygon_of_def v1v2)
      ultimately show ?thesis by blast
    qed
    ultimately have "z \<in> path_image ?p' \<inter> (?H \<inter> ?F)" by blast
    moreover have "?H \<inter> ?F = ?L" 
      using affine_2_int_convex[of ?a ?b "set vts"]
      by (smt (verit, best) assms(3) F F_int_interior_H inf_commute segment_convex_hull path_image_linepath Suc_1 add_leD2 assms(1) empty_subsetI insert_subset length_greater_0_conv lessI nat_neq_iff nth_mem numeral_Bit0 order.strict_iff_not plus_1_eq_Suc polygon_of_def polygon_vertices_length_at_least_4 take_all_iff take_eq_Nil IntE inf.orderE)
    ultimately have "z \<in> ?L \<inter> path_image ?p'" by blast
    moreover have "?L \<inter> path_image ?p' \<subseteq> {?a, ?b}"
    proof-
      let ?p_tl = "make_polygonal_path (tl vts)"
      have "p = make_polygonal_path vts \<and> loop_free p"
        using assms unfolding polygon_of_def polygon_def simple_path_def by blast
      moreover have "[?a, ?b] = take 2 vts"
        by (metis Cons_nth_drop_Suc One_nat_def Suc_1 append_Cons append_Nil calculation constant_linepath_is_not_loop_free drop0 drop_eq_Nil insert_subset length_pos_if_in_set linorder_not_le make_polygonal_path.simps(2) take0 take_Suc_conv_app_nth v1v2)
      moreover have "tl vts = drop (2 - 1) vts" by (simp add: drop_Suc)
      moreover have "?l = make_polygonal_path [?a, ?b]" using make_polygonal_path.simps by simp
      moreover have "length vts > 2" using ij by linarith
      moreover have "pathstart ?l = ?a \<and> pathstart ?p_tl = ?b"
        using calculation(3) calculation(5) polygon_pathstart by auto
      ultimately have "?L \<inter> path_image ?p_tl \<subseteq> {?a, ?b}"
        using loop_free_split_int[of p vts "[?a, ?b]" 2 "tl vts" ?l ?p_tl "length vts"] by auto
      moreover have "path_image ?p' \<subseteq> path_image ?p_tl"
        using sublist_path_image_subset
        by (metis add.commute ij le_add2 length_drop length_take less_diff_conv min.absorb4 min.cobounded1 min_def vts'_sublist_tl)
      ultimately show ?thesis by blast
    qed
    ultimately have *: "z = ?a \<or> z = ?b" by blast

    let ?\<ii> = "?i'"
    let ?\<jj> = "?j' - ?i' + 1"
    let ?\<kk> = "?\<ii> + ?\<jj>"
    let ?x1 = "(2^?\<ii> - 1)/(2^?\<ii>)::real"
    let ?x2 = "(2^(?\<kk>-1) - 1)/(2^(?\<kk>-1))::real"

    have "?vts' = take ?\<jj> (drop ?\<ii> vts)" by blast
    moreover have "?\<kk> \<le> length vts - 1 \<and> 2 \<le> ?\<jj>" using ij by linarith
    ultimately have "path_image ?p' = p`{?x1..?x2}"
      using vts_sublist_path_image assms(1) unfolding polygon_of_def by metis
    moreover have x1x2: "?x1 > 1/2 \<and> ?x2 < 1"
    proof-
      have "?i' \<ge> 2" using ij by linarith
      then have "(1::real) < 2^?i' - 1"
        by (smt (z3) dual_order.strict_trans1 linorder_le_less_linear numeral_le_one_iff power_one_right power_strict_increasing semiring_norm(69))
      thus ?thesis by simp
    qed
    moreover have "p 0 \<notin> p`{?x1..?x2} \<and> p (1/2) \<notin> p`{?x1..?x2}"
    proof-
      have False if *: "p 0 \<in> p`{?x1..?x2}"
      proof-
        obtain t where t: "t \<in> {?x1..?x2} \<and> p t = p 0" using * by auto
        then have "t \<ge> ?x1 \<and> t \<le> ?x2" by presburger
        then have "1/2 < t \<and> t < 1" using x1x2 by argo
        thus False
          using t assms(1) unfolding polygon_of_def polygon_def simple_path_def loop_free_def
          by force
      qed
      moreover have False if *: "p (1/2) \<in> p`{?x1..?x2}"
      proof-
        obtain t where t: "t \<in> {?x1..?x2} \<and> p t = p (1/2)" using * by auto
        then have "t \<ge> ?x1 \<and> t \<le> ?x2" by presburger
        then have "1/2 < t \<and> t < 1" using x1x2 by argo
        thus False
          using t assms(1) unfolding polygon_of_def polygon_def simple_path_def loop_free_def
          by fastforce
      qed
      ultimately show ?thesis by fast
    qed
    moreover have "?a = p 0"
      by (metis assms(1) card.empty empty_set not_numeral_le_zero pathstart_def polygon_at_least_3_vertices polygon_of_def polygon_pathstart)
    moreover have "?b = p (1/2)"
    proof-
      have "p = ?l +++ (make_polygonal_path (tl vts))"
        by (smt (verit, best) One_nat_def Suc_1 assms(1) ij length_Cons length_greater_0_conv length_tl less_imp_le_nat list.sel(3) list.size(3) make_polygonal_path.elims nth_Cons_0 nth_tl order_less_le_trans polygon_of_def pos2 zero_less_diff)
      then have "p (1/2) = ?l 1"
        unfolding joinpaths_def by simp
      thus ?thesis by (simp add: linepath_1')
    qed
    ultimately have "?a \<notin> path_image ?p' \<and> ?b \<notin> path_image ?p'" by presburger
    thus False using z * by blast
  qed
  then have "frontier ?P1 \<inter> ?H \<subseteq> frontier ?H \<or> frontier ?P2 \<inter> ?H \<subseteq> frontier ?H"
    using frontier_int_subset by auto
  moreover have "?L \<subseteq> frontier ?P1 \<and> ?L \<subseteq> frontier ?P2"
    using frontier_P1 frontier_P2 L_subset_F by presburger
  ultimately show ?thesis using L_subset_H by fast
qed

lemma vts_on_convex_frontier_aux':
  assumes "polygon_of p vts"
  assumes "set vts \<subseteq> frontier (convex hull (set vts))"
  shows "path_image (linepath (vts!0) (vts!1)) \<subseteq> frontier (convex hull (set vts))"
proof-
  let ?a = "vts!0"
  let ?f = "\<lambda>v. v + (-?a)"
  let ?vts' = "map ?f vts"
  let ?p' = "make_polygonal_path ?vts'"

  have len_vts: "length vts \<ge> 2"
    using assms(1) polygon_of_def polygon_vertices_length_at_least_4 by fastforce
  then have p': "?p' = ?f \<circ> p"
    using make_polygonal_path_translate[of vts "-?a"] assms unfolding polygon_of_def by presburger
  then have 0: "?vts'!0 = 0"
    by (metis len_vts neg_eq_iff_add_eq_0 nth_map order_less_le_trans pos2)
  moreover have vts': "set ?vts' = ?f ` (set vts)" by simp
  ultimately have "convex hull (set ?vts') = ?f ` (convex hull (set vts))"
    using convex_hull_translation[of "-?a" "set vts"] by force
  then have "frontier (convex hull (set ?vts')) = frontier (?f ` (convex hull (set vts)))"
    by auto
  then have frontier_translation: 
      "frontier (convex hull (set ?vts')) = ?f ` (frontier ((convex hull (set vts))))"
    using frontier_translation[of "-?a" "convex hull (set vts)"] by simp

  have "?f (vts!0) = ?vts'!0 \<and> ?f (vts!1) = ?vts'!1" using 0 len_vts by auto
  then have linepath_translation:
      "?f ` path_image (linepath (vts!0) (vts!1)) = path_image (linepath (?vts'!0) (?vts'!1))"
    using linepath_translation[of ?a "-?a" "vts!1"] by (simp add: path_image_compose)

  have "polygon_of ?p' ?vts'" using translation_is_polygon assms(1) p' by presburger 
  moreover have "set ?vts' \<subseteq> frontier (convex hull (set ?vts'))"
  proof-
    have "frontier (convex hull (set ?vts')) = frontier (convex hull (?f ` (set vts)))"
      using vts' by presburger
    then have "frontier (convex hull (set ?vts')) = ?f ` (frontier (convex hull (set vts)))"
      using frontier_translation by presburger
    thus ?thesis using vts' assms(2) by auto
  qed
  ultimately have "path_image (linepath (?vts'!0) (?vts'!1)) \<subseteq> frontier (convex hull (set ?vts'))"
    using vts_on_convex_frontier_aux assms 0 by blast
  then have "?f ` path_image (linepath (vts!0) (vts!1)) \<subseteq> ?f ` (frontier ((convex hull (set vts))))"
    using linepath_translation frontier_translation by argo
  thus ?thesis by force
qed

lemma vts_on_convex_frontier:
  assumes "polygon_of p vts"
  assumes "set vts \<subseteq> frontier (convex hull (set vts))"
  assumes "i < length vts - 1"
  shows "path_image (linepath (vts!i) (vts!(i+1))) \<subseteq> frontier (convex hull (set vts))"
proof-
  let ?vts' = "rotate_polygon_vertices vts i"
  let ?p' = "make_polygonal_path ?vts'"
  have "polygon_of ?p' ?vts'"
    using assms(1) polygon_of_def rotation_is_polygon by blast
  moreover have "set ?vts' \<subseteq> frontier (convex hull (set ?vts'))"
    using assms(1) assms(2) polygon_of_def rotate_polygon_vertices_same_set by auto
  ultimately have "path_image (linepath (?vts'!0) (?vts'!1)) \<subseteq> frontier (convex hull (set ?vts'))"
    using vts_on_convex_frontier_aux' by presburger
  moreover have "?vts'!0 = vts!i \<and> ?vts'!1 = vts!(i+1)"
    using assms(3)
    using rotated_polygon_vertices[of ?vts' vts i "i+1"]
    using rotated_polygon_vertices[of ?vts' vts i "i"]
    by (smt (verit, best) Suc_leI add.commute add.right_neutral add_2_eq_Suc' add_diff_cancel_left' add_lessD1 assms(1) have_wraparound_vertex hd_Nil_eq_last hd_conv_nth last_snoc le_add1 less_diff_conv plus_1_eq_Suc polygon_of_def)
  moreover have "frontier (convex hull (set ?vts')) = frontier (convex hull (set vts))"
    by (metis assms(1) polygon_of_def rotate_polygon_vertices_same_set)
  ultimately show ?thesis by argo
qed

lemma vts_on_frontier_means_path_image_on_frontier:
  assumes "polygon_of p vts"
  assumes "set vts \<subseteq> frontier (convex hull (set vts))"
  shows "path_image p \<subseteq> frontier (convex hull (set vts))"
proof(rule subsetI)
  let ?H = "convex hull (set vts)"
  fix x assume "x \<in> path_image p"
  moreover have "path_image p = (\<Union> {path_image (linepath (vts!i) (vts!(i+1))) | i. i \<le> (length vts) - 2})"
    using polygonal_path_image_linepath_union assms unfolding polygon_of_def
    by (metis (no_types, lifting) add_leD2 numeral_Bit0 polygon_vertices_length_at_least_4)
  ultimately obtain i where "i \<le> (length vts) - 2 \<and> x \<in> path_image (linepath (vts!i) (vts!(i+1)))"
    by blast
  thus "x \<in> frontier ?H"
    by (smt (verit, ccfv_SIG) One_nat_def Suc_diff_Suc add.commute add_2_eq_Suc' assms(1) assms(2) in_mono le_add1 le_zero_eq less_Suc_eq_le less_diff_conv linorder_not_less plus_1_eq_Suc vts_on_convex_frontier vts_on_convex_frontier_aux')
qed

lemma vts_on_convex_frontier_interior:
  assumes "polygon_of p vts"
  assumes "set vts \<subseteq> frontier (convex hull (set vts))"
  shows "path_inside p = interior (convex hull (set vts))"
proof-
  let ?H = "convex hull (set vts)"

  have "path_inside p \<subseteq> interior (convex hull (set vts))"
    by (metis (no_types, lifting) Un_empty assms(1) convex_contains_simple_closed_path_imp_contains_path_inside convex_convex_hull convex_hull_eq_empty convex_hull_of_polygon_is_convex_hull_of_vts empty_set inside_outside_def inside_outside_polygon interior_maximal length_greater_0_conv polygon_def polygon_of_def polygon_path_image_subset_convex)
  moreover have "interior (convex hull (set vts)) \<subseteq> path_inside p"
  proof(rule ccontr)
    assume *: "\<not> interior (convex hull (set vts)) \<subseteq> path_inside p"
    then obtain x where x: "x \<in> interior (convex hull (set vts)) - path_inside p" by blast
    obtain y where y: "y \<in> path_inside p"
      using inside_outside_polygon assms unfolding inside_outside_def polygon_of_def by fastforce

    let ?l = "linepath x y"
    have 1: "path_image ?l \<subseteq> interior ?H"
      by (metis (no_types, lifting) DiffE calculation convex_contains_segment convex_convex_hull convex_interior in_mono linepath_image_01 path_defs(4) x y)
    have "path_image ?l \<inter> frontier (path_inside p) \<noteq> {}"
      using inside_outside_polygon assms unfolding inside_outside_def polygon_of_def
      by (smt (verit) "*" Diff_disjoint Diff_eq_empty_iff Int_Un_eq(2) Int_assoc Un_Int_eq(3) assms(1) calculation connected_Int_frontier convex_connected convex_convex_hull convex_interior frontier_def inf.absorb_iff2 vts_on_frontier_means_path_image_on_frontier)
    then have 2: "path_image ?l \<inter> path_image p \<noteq> {}"
      using inside_outside_polygon assms unfolding inside_outside_def polygon_of_def by blast

    show False
      using 1 2 vts_on_frontier_means_path_image_on_frontier
      using Diff_disjoint Int_lower2 Int_subset_iff assms(1) assms(2) frontier_def inf_le1
      by fastforce
  qed
  ultimately show ?thesis by blast
qed

lemma vts_subset_frontier:
  assumes "polygon_of p vts"
  assumes "set vts \<subseteq> frontier (convex hull (set vts))"
  shows "convex (path_image p \<union> path_inside p)"
  by (metis assms(1) assms(2) vts_on_convex_frontier_interior convex_convex_hull convex_interior polygon_convex_iff polygon_of_def sup_commute)

lemma convex_hull_of_nonconvex_polygon_strict_subset_ep:
  assumes "polygon_of p vts"
  assumes "\<not> (convex (path_image p \<union> path_inside p))"
  shows "{v. v extreme_point_of (convex hull (set vts))} \<subset> set vts"
proof-
  let ?ep = "{v. v extreme_point_of (convex hull (set vts))}"
  let ?H = "convex hull (set vts)"
  have "?ep \<subseteq> frontier ?H"
    by (metis Krein_Milman_frontier List.finite_set convex_convex_hull extreme_point_of_convex_hull finite_imp_compact_convex_hull mem_Collect_eq subsetI)
  thus ?thesis using assms vts_subset_frontier extreme_points_of_convex_hull by force
qed

lemma convex_hull_of_nonconvex_polygon_strict_subset:
  assumes "polygon_of p vts"
  assumes "\<not> (convex (path_image p \<union> path_inside p))"
  shows "\<exists>v \<in> set vts. v \<in> interior (convex hull (set vts))"
  using assms vts_subset_frontier
  by (smt (verit) Diff_iff UnCI closure_Un_frontier frontier_def hull_inc subsetI)

lemma convex_polygon_means_linepaths_inside:
  fixes p :: "R_to_R2"
  assumes "polygon_of p vts"
  assumes convex_is: "convex hull (set vts) = (path_inside p \<union> path_image p)"
  assumes a_in: "a \<in> (path_inside p \<union> path_image p)"
  assumes b_in: "b \<in> (path_inside p \<union> path_image p)"
  shows "path_image (linepath a b) \<subseteq> (path_inside p \<union> path_image p)"
proof - 
  let ?conv = "path_inside p \<union> path_image p"
  have "\<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R a + v *\<^sub>R b \<in> ?conv"
    using convex_is a_in b_in unfolding convex_def 
    by (metis (no_types, lifting) convexD convex_convex_hull convex_is)
  then have "(1 - x) *\<^sub>R a + x *\<^sub>R b \<in> ?conv" if x_in: "x \<in> {0..1}" for x
    using x_in by auto
  then show ?thesis unfolding linepath_def path_image_def 
    by fast
qed

end