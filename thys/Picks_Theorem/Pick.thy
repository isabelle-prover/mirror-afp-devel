theory Pick
imports
  Polygon_Splitting
  Elementary_Triangle_Area
begin

section "Setup"

subsection "Integral Points Cardinality Properties"
lemma bounded_finite:
  fixes A:: "(real^2) set"
  assumes "bounded A"
  shows "finite {x::(real^2). integral_vec x \<and> x \<in> A}" (is "finite ?A_int")
proof-
  obtain M where M: "\<forall>x \<in> A. norm x \<le> M" using assms bounded_def by (meson bounded_iff)
  
  let ?M_bounded_ints = "{n. n \<in> {-M..M} \<and> is_int n}"
  let ?M_bounded_int_vecs = "{v::(real^2). v$1 \<in> ?M_bounded_ints \<and> v$2 \<in> ?M_bounded_ints}"

  have "\<forall>x::(real^2). norm (x$1) \<le> norm x \<and> (x$2) \<le> norm x"
    by (smt (verit, ccfv_threshold) Finite_Cartesian_Product.norm_nth_le real_norm_def)
  then have "\<forall>x \<in> ?A_int. norm (x$1) \<le> M \<and> norm (x$2) \<le> M"
    using M dual_order.trans Finite_Cartesian_Product.norm_nth_le by blast
  then have "\<forall>x \<in> ?A_int. x$1 \<in> ?M_bounded_ints \<and> x$2 \<in> ?M_bounded_ints"
    using integral_vec_def intervalE by auto
  then have "\<forall>x \<in> ?A_int. x \<in> ?M_bounded_int_vecs" by blast
  moreover have "finite ?M_bounded_int_vecs"
  proof-
    obtain S :: "int set" where S: "S = {n. \<exists>m \<in> ?M_bounded_ints. n = m} \<and> (\<forall>n \<in> S. norm n \<le> M)"
      by (simp add: abs_le_iff)
    then have finite_S: "finite S"
      by (metis infinite_int_iff_unbounded le_floor_iff linorder_not_less norm_of_int of_int_abs)

    (* Construct injection f : ?M_bounded_ints \<rightarrow> S *)
    have finite_M_bounded_ints: "finite ?M_bounded_ints"
    proof-
      let ?f = "\<lambda>n::real. THE m::int. n = m"
      have "\<forall>n \<in> ?M_bounded_ints. \<exists>!m::int. n = m" using is_int_def by force
      moreover have "inj_on ?f ?M_bounded_ints" using inj_on_def is_int_def by force
      moreover have "?f ` ?M_bounded_ints \<subseteq> S" using calculation S subsetI by auto
      ultimately show ?thesis using finite_imageD finite_S by (simp add: inj_on_finite)
    qed
    show ?thesis (* Construct injection f : ?M_bounded_int_vecs \<rightarrow> S \<times> S *)
    proof-
      let ?f = "\<lambda>x::(real^2). (THE m::int. m = x$1, THE n::int. n = x$2)"
      have "inj_on ?f ?M_bounded_int_vecs"
        unfolding inj_on_def
      proof clarify
        fix x y :: "real^2"
        assume x1_int: "is_int (x$1)"
        assume x2_int: "is_int (x$2)"
        assume y1_int: "is_int (y$1)"
        assume y2_int: "is_int (y$2)"
        assume x1y1_int_eq: "(THE m. real_of_int m = x$1) = (THE m. real_of_int m = y$1)"
        assume x2y2_int_eq: "(THE n. real_of_int n = x$2) = (THE n. real_of_int n = y$2)"

        have "\<exists>!m. m = x$1"
          by blast
        moreover have "\<exists>!n. n = y$1"
          by blast
        moreover have "(THE m. real_of_int m = x$1) = (THE m. real_of_int m = y$1)"
          using x1y1_int_eq by auto
        ultimately have x1y1: "x$1 = y$1"
          using x1_int y1_int is_int_def by auto

        have "\<exists>!m. m = x$2"
          by blast
        moreover have "\<exists>!n. n = y$2"
          by blast
        moreover have "(THE m. real_of_int m = x$2) = (THE m. real_of_int m = y$2)" 
          using x2y2_int_eq by auto
        ultimately have x2y2: "x$2 = y$2"
          using x2_int y2_int is_int_def by auto

        show "x = y" using x1y1 x2y2
          by (metis (no_types, lifting) exhaust_2 vec_eq_iff) 
      qed
      moreover have "?f ` ?M_bounded_int_vecs \<subseteq> S \<times> S"
      proof(rule subsetI)
        fix mn
        assume "mn \<in> ?f ` ?M_bounded_int_vecs"
        then obtain v where v:
          "v \<in> ?M_bounded_int_vecs \<and> ?f v = mn \<and> (\<exists>!m. v$1 = m) \<and> (\<exists>!n. v$2 = n)"
          using is_int_def by auto
        let ?m = "fst mn"
        let ?n = "snd mn"

        have "?m = (THE m::int. m = v$1)" using v
          by (meson fstI)
        moreover have "\<exists>! m::int. m = v$1" using v is_int_def
          by (metis (no_types, lifting) mem_Collect_eq of_int_eq_iff)
        ultimately have m_in_S: "?m \<in> S"
          by (metis (mono_tags, lifting) S mem_Collect_eq theI' v)

        have "?n = (THE n::int. n = v$2)" using v
          by (meson sndI)
        moreover have "\<exists>! n::int. n = v$2" using v is_int_def
          by (metis (no_types, lifting) mem_Collect_eq of_int_eq_iff)
        ultimately have n_in_S: "?n \<in> S"
          by (metis (mono_tags, lifting) S mem_Collect_eq theI' v)        

        show "mn \<in> S \<times> S" using m_in_S n_in_S v by auto
      qed
      ultimately show ?thesis
        by (meson finite_S finite_SigmaI finite_imageD finite_subset)
    qed
  qed
  ultimately show ?thesis
    by (smt (verit) finite_subset subsetI)
qed

lemma finite_path_image:
  assumes "polygon p"
  shows "finite {x. integral_vec x \<and> x \<in> path_image p}"
  using bounded_finite inside_outside_polygon
  unfolding inside_outside_def 
  by (meson assms bounded_simple_path_image polygon_def)

lemma finite_path_inside:
  assumes "polygon p"
  shows "finite {x. integral_vec x \<and> x \<in> path_inside p}"
  using bounded_finite inside_outside_polygon
  unfolding inside_outside_def 
  using assms by presburger

lemma bounded_finite_inside:
  fixes B:: "(real^2) set"
  assumes "simple_path p"
  shows "bounded (path_inside p)"
  using assms 
  by (simp add: bounded_inside bounded_simple_path_image path_inside_def)

lemma finite_integral_points_path_image:
  assumes "simple_path p"
  shows "finite {x. integral_vec x \<and> x \<in> path_image p}"
  using bounded_finite bounded_simple_path_image assms by blast

lemma finite_integral_points_path_inside:
  assumes "simple_path p"
  shows "finite {x. integral_vec x \<and> x \<in> path_inside p}"
  using bounded_finite bounded_finite_inside assms by blast

section "Pick splitting"

lemma pick_split_path_union_main:
  assumes is_split: "is_polygon_split_path vts i j cutvts"
  assumes "vts1 = (take i vts)" 
  assumes "vts2 = (take (j - i - 1) (drop (Suc i) vts))"
  assumes "vts3 = drop (j - i) (drop (Suc i) vts)"
  assumes "x = vts!i"
  assumes "y = vts!j"
  assumes "cutpath = make_polygonal_path (x # cutvts @ [y])"
  assumes p: "p = make_polygonal_path (vts@[vts!0])" (is "p = make_polygonal_path ?p_vts")
  assumes p1: "p1 = make_polygonal_path (x#(vts2 @ [y] @ (rev cutvts) @ [x]))" (is "p1 = make_polygonal_path ?p1_vts")
  assumes p2: "p2 = make_polygonal_path (vts1 @ ([x] @ cutvts @ [y]) @ vts3 @ [vts ! 0])" (is "p2 = make_polygonal_path ?p2_vts")
  assumes I1: "I1 = card {x. integral_vec x \<and> x \<in> path_inside p1}" 
  assumes B1: "B1 = card {x. integral_vec x \<and> x \<in> path_image p1}"
  assumes I2: "I2 = card {x. integral_vec x \<and> x \<in> path_inside p2}" 
  assumes B2: "B2 = card {x. integral_vec x \<and> x \<in> path_image p2}"
  assumes I: "I = card {x. integral_vec x \<and> x \<in> path_inside p}" 
  assumes B: "B = card {x. integral_vec x \<and> x \<in> path_image p}"
  assumes all_integral_vts: "all_integral vts"
  shows "measure lebesgue (path_inside p1) = I1 + B1/2 - 1
          \<Longrightarrow> measure lebesgue (path_inside p2) = I2 + B2/2 - 1
          \<Longrightarrow> measure lebesgue (path_inside p) = I + B/2 - 1"
        "measure lebesgue (path_inside p) = I + B/2 - 1
          \<Longrightarrow> measure lebesgue (path_inside p2) = I2 + B2/2 - 1
          \<Longrightarrow> measure lebesgue (path_inside p1) = I1 + B1/2 - 1"
        "measure lebesgue (path_inside p) = I + B/2 - 1
          \<Longrightarrow> measure lebesgue (path_inside p1) = I1 + B1/2 - 1
          \<Longrightarrow> measure lebesgue (path_inside p2) = I2 + B2/2 - 1"
proof -
  let ?p_im = "{x. integral_vec x \<and> x \<in> path_image p}"
  let ?p1_im = "{x. integral_vec x \<and> x \<in> path_image p1}"
  let ?p2_im = "{x. integral_vec x \<and> x \<in> path_image p2}"
  let ?p_int = "{x. integral_vec x \<and> x \<in> path_inside p}"
  let ?p1_int = "{x. integral_vec x \<and> x \<in> path_inside p1}"
  let ?p2_int = "{x. integral_vec x \<and> x \<in> path_inside p2}"

  have vts: "vts = vts1 @ (x # (vts2 @ y # vts3))"
    using assms split_up_a_list_into_3_parts
    using is_polygon_split_path_def by blast
  have "polygon p"
    using finite_path_image assms(1) p unfolding is_polygon_split_path_def 
    by (smt (verit, best))
  then have B_finite: "finite ?p_im"
    using finite_path_image by auto
  have polygon_p1: "polygon p1"
    using finite_path_image assms(1) p1 unfolding is_polygon_split_path_def 
    by (smt (z3) assms(3) assms(5) assms(6))
  then have B1_finite: "finite ?p1_im"
    using finite_path_image by auto
   have polygon_p2: "polygon p2"
     using finite_path_image assms(1) p1 unfolding is_polygon_split_path_def 
     by (smt (z3) assms(2) assms(4) assms(5) assms(6) p2)
  then have B2_finite: "finite ?p2_im"
    using finite_path_image by auto

  have vts_distinct: "distinct vts"
    using simple_polygonal_path_vts_distinct
    by (metis \<open>polygon p\<close> butlast_snoc p polygon_def)
  then have x_neq_y: "x \<noteq> y"
    by (metis assms(1) assms(5) assms(6) index_first index_nth_id is_polygon_split_path_def)
  then have card_2: "card {x, y} = 2"
    by auto
  have polygon_split_props: "(is_polygon_cut_path (vts@[vts!0]) cutpath \<and>
    polygon p \<and> polygon p1 \<and> polygon p2 \<and>
    path_inside p1 \<inter> path_inside p2 = {} \<and>
    path_inside p1 \<union> path_inside p2 \<union> (path_image cutpath - {x, y}) = path_inside p 
    \<and> ((path_image p1) - (path_image cutpath)) \<inter> ((path_image p2) - (path_image cutpath)) = {}
    \<and> path_image p = ((path_image p1) - (path_image cutpath)) \<union> ((path_image p2) - (path_image cutpath)) \<union> {x, y})"
    using assms 
    by (meson is_polygon_split_path_def)
  have measure_sum: "measure lebesgue (path_inside p) = measure lebesgue (path_inside p1) + measure lebesgue (path_inside p2)"
    using polygon_split_path_add_measure assms
    by (smt (verit, del_insts)) 


  let ?yx_int = "{k. integral_vec k \<and> k \<in> path_image (make_polygonal_path (y#rev cutvts@[x]))}"
  let ?xy_int = "{k. integral_vec k \<and> k \<in> path_image cutpath}"
  have yx_int_is_xy_int: "?yx_int = ?xy_int"
    using rev_vts_path_image[of "x # cutvts @ [y]"] assms(7) by simp
  have "x # vts2 @ [y] @ rev cutvts @ [x] = (x#vts2) @ ([y] @ rev cutvts @ [x]) @ []"
    by simp
  then have "sublist ([y]@rev cutvts@[x]) ?p1_vts" 
    unfolding sublist_def by blast
  then have subset1:
    "?xy_int \<subseteq> ?p1_im"
    using sublist_integral_subset_integral_on_path p1 yx_int_is_xy_int  
    by force
  have len_gteq: "length (x # cutvts @ [y]) \<ge> 2"
    by auto
  have sublist_p2: "sublist (x # cutvts @ [y]) ?p2_vts"
    unfolding sublist_def by auto
  then have subset2:
    "?xy_int \<subseteq> ?p2_im"
    using sublist_integral_subset_integral_on_path[OF len_gteq p2 sublist_p2]
    assms(7) by blast

  let ?S1 = "?p1_im - ?xy_int"
  let ?S2 = "?p2_im - ?xy_int"
  have disjoint_1: "?S1 \<inter> ?S2 = {}"
    using polygon_split_props by blast

  have integral_xy: "integral_vec x \<and> integral_vec y"
    using all_integral_vts vts 
    using all_integral_def by auto
  have nonempty: "y # rev cutvts @ [x] \<noteq> []"
    by simp
  have trivial: " make_polygonal_path (y # rev cutvts @ [x]) = make_polygonal_path (y # rev cutvts @ [x])"
    by auto
  have "pathstart (make_polygonal_path (y#rev cutvts@[x])) = y \<and> pathfinish (make_polygonal_path (y#rev cutvts@[x])) = x"
    using polygon_pathstart[OF nonempty trivial] polygon_pathfinish[OF nonempty trivial] 
    by (metis last.simps last_conv_nth nonempty nth_Cons_0 snoc_eq_iff_butlast)
  then have x_in_y_in: "x \<in> path_image (make_polygonal_path (y#rev cutvts@[x])) \<and> y \<in> path_image (make_polygonal_path (y#rev cutvts@[x]))"
    unfolding pathstart_def pathfinish_def path_image_def 
    by (metis \<open>pathstart (make_polygonal_path (y # rev cutvts @ [x])) = y \<and> pathfinish (make_polygonal_path (y # rev cutvts @ [x])) = x\<close> path_image_def pathfinish_in_path_image pathstart_in_path_image)
  then have "{x, y} \<subseteq> ?yx_int"
    using integral_xy
    by simp
  then have disjoint_2: "(?S1 \<union> ?S2) \<inter> {x, y} = {}"
    by (simp add: yx_int_is_xy_int)
  have "path_image p =
      path_image p1 - path_image cutpath \<union>
      (path_image p2 - path_image cutpath) \<union>
      {x, y}"
    using polygon_split_props by auto
  then have set_union: "?p_im = (?S1 \<union> ?S2) \<union> {x, y}"
    using polygon_split_props integral_xy by auto
  then have add_card: "B = card (?p1_im - ?xy_int) + card (?p2_im - ?xy_int) + card {x, y}"
    using B_finite using disjoint_1 disjoint_2 
    by (metis (no_types, lifting) B card_Un_disjoint finite_Un)
  have sub1: "card (?p1_im - ?xy_int) = B1 - card ?xy_int"
    using B1_finite B1 subset1
    by (meson card_Diff_subset finite_subset)
  have sub2: "card (?p2_im - ?xy_int) = B2 - card ?xy_int"
    using B2_finite B2 subset2 
    by (meson card_Diff_subset finite_subset)
  have B: "B = (B1 - card ?xy_int) + (B2 - card ?xy_int) + card {x, y}"
    using add_card sub1 sub2
    by auto
  then have B_sum_h: "B = B1 + B2 - 2*card ?xy_int + 2"
    using card_2
    by (smt (verit, best) B1 B1_finite B2 B2_finite Nat.add_diff_assoc add.commute card_mono diff_diff_left mult_2 subset1 subset2) 
  then have "B1 + B2 = B + 2*card ?xy_int - 2"
    by (metis (no_types, lifting) B1 B1_finite B2 B2_finite add_mono_thms_linordered_semiring(1) card_mono diff_add_inverse2 le_add2 mult_2 ordered_cancel_comm_monoid_diff_class.add_diff_assoc2 subset1 subset2)
  then have B_sum: "(B1 + B2)/2 = B/2 + card ?xy_int - 1" 
    by (smt (verit) B_sum_h field_sum_of_halves le_add2 mult_2 nat_1_add_1 of_nat_1 of_nat_add of_nat_diff ordered_cancel_comm_monoid_diff_class.add_diff_assoc2)
  have casting_h: "\<And> A B:: nat. A \<ge> B \<Longrightarrow> real (A - B) = real A - real B"
    by auto
  have " path_inside p1 \<union> path_inside p2 \<union> (path_image cutpath - {x, y}) = path_inside p"
    using polygon_split_props by auto
  then have interior_union: "?p_int = (?xy_int - {x, y}) \<union> ?p1_int \<union> ?p2_int"
    by blast  

  have finite_inside_p: "finite ?p_int"
    using bounded_finite inside_outside_polygon 
    by (simp add: polygon_split_props inside_outside_def)
  have finite_pathimage: "finite (?xy_int - {x, y})"
    using B1_finite finite_subset subset1 by auto
  have finite_inside_p1: "finite ?p1_int"
     using polygon_split_props bounded_finite inside_outside_polygon 
     using finite_Un finite_inside_p interior_union by auto
  have finite_inside_p2: "finite ?p2_int"
    using polygon_split_props bounded_finite inside_outside_polygon 
    using finite_Un finite_inside_p interior_union by auto
  have path_image_inside_disjoint1: "(?xy_int - {x, y}) \<inter> (?p1_int) = {}"
    using subset1 inside_outside_polygon[OF polygon_p1]
    unfolding inside_outside_def by auto
  have path_image_inside_disjoint2: "(?xy_int - {x, y}) \<inter> (?p2_int) = {}"
    using subset2  inside_outside_polygon[OF polygon_p2]
    unfolding inside_outside_def by auto
  (* The union of these interiors is disjoint from their path image *)
  have "(?xy_int - {x, y}) \<inter> (?p1_int \<union> ?p2_int) = {}" 
    using  subset2 path_image_inside_disjoint1 path_image_inside_disjoint2
    by auto
  then have I_is: "I = card (?xy_int - {x, y}) + 
    card (?p1_int \<union> ?p2_int)"
    using interior_union I finite_inside_p1 finite_inside_p2
    by (metis (no_types, lifting) card_Un_disjoint finite_Un finite_pathimage sup_assoc) 
  have disjoint_4: "?p1_int \<inter> ?p2_int = {}"
    using polygon_split_props by auto
  then have "I = card (?xy_int - {x, y}) + 
    I1 + I2"
    using I_is finite_inside_p1 finite_inside_p2 
    by (simp add: I1 I2 card_Un_disjoint)
  have interior_subset: "(?xy_int - {x, y}) \<subseteq> ?p_int"
    using interior_union by auto 
  have x_y_subset: "{x, y} \<subseteq> ?xy_int"
    using x_in_y_in rev_vts_path_image[of "x # cutvts @ [y]"] assms(7)
    integral_xy 
    using yx_int_is_xy_int by blast
  have " real (card (?xy_int - {x, y})) =
  real (card (?xy_int )) - real (card {x, y})"
    using x_y_subset
    by (metis (no_types, lifting) B2_finite card_Diff_subset card_mono finite_subset of_nat_diff subset2)
  then have card_diff: "real (card (?xy_int - {x, y})) =
  real (card (?xy_int )) - 2"
    using card_2 by auto
  then have "I = I1 + I2 + (card (?xy_int - {x, y}))"
    using I I1 I2 interior_union finite_inside_p1 finite_inside_p2 
    by (simp add: I_is disjoint_4 card_Un_disjoint)
  then have "I = I1 + I2 + real (card (?xy_int)) - 2"
    using card_diff 
    by linarith
  then have I_sum: "I1 + I2 = I - real (card ?xy_int) + 2"
    by fastforce

  {assume pick1: "measure lebesgue (path_inside p1) = I1 + B1/2 - 1"
    assume pick2: "measure lebesgue (path_inside p2) = I2 + B2/2 - 1"
  have "measure lebesgue (path_inside p) = I1 + I2 + (B1+B2)/2 -2"
    using pick1 pick2 measure_sum by auto
  then have "measure lebesgue (path_inside p) = I - real (card ?xy_int) + 2 + 
   B/2 + card ?xy_int - 1 - 2"
    using I_sum B_sum 
    by linarith
  then have "measure lebesgue (path_inside p) = I + B/2 - 1" by auto
  }
  then show "measure lebesgue (path_inside p1) = I1 + B1/2 - 1 \<Longrightarrow> measure lebesgue (path_inside p2) = I2 + B2/2 - 1 \<Longrightarrow> measure lebesgue (path_inside p) = I + B/2 - 1"
    by blast

  {assume pick1: "measure lebesgue (path_inside p) = I + B/2 - 1"
    assume pick2: "measure lebesgue (path_inside p2) = I2 + B2/2 - 1"
    then have "real I + real B / 2 - 1 = (measure lebesgue (path_inside p1)) + I2 + B2/2 -1"
    using measure_sum pick1 pick2 by auto
  then have "measure lebesgue (path_inside p) = I - real (card ?xy_int) + 2 + 
   B/2 + card ?xy_int - 1 - 2"
    using I_sum B_sum pick1 
    by linarith
  then have "measure lebesgue (path_inside p1) = I1 + B1/2 - 1" 
    using B_sum \<open>real I = real (I1 + I2) + real (card {k. integral_vec k \<and> k \<in> path_image cutpath}) - 2\<close> field_sum_of_halves measure_sum of_nat_add 
    pick1 pick2 by auto
  }
  then show  "measure lebesgue (path_inside p) = I + B/2 - 1 \<Longrightarrow> measure lebesgue (path_inside p2) = I2 + B2/2 - 1 \<Longrightarrow> measure lebesgue (path_inside p1) = I1 + B1/2 - 1"
    by blast

  {assume pick1: "measure lebesgue (path_inside p) = I + B/2 - 1"
    assume pick2: "measure lebesgue (path_inside p1) = I1 + B1/2 - 1"
    then have "real I + real B / 2 - 1 = (measure lebesgue (path_inside p2)) + I1 + B1/2 -1"
    using measure_sum pick1 pick2 by auto
  then have "measure lebesgue (path_inside p) = I - real (card ?xy_int) + 2 + 
   B/2 + card ?xy_int - 1 - 2"
    using I_sum B_sum pick1 
    by linarith
  then have "measure lebesgue (path_inside p2) = I2 + B2/2 - 1" 
    using B_sum \<open>real I = real (I1 + I2) + real (card {k. integral_vec k \<and> k \<in> path_image cutpath}) - 2\<close> field_sum_of_halves measure_sum of_nat_add 
    using pick2 by auto
  }
  then show "measure lebesgue (path_inside p) = I + B/2 - 1 \<Longrightarrow> measure lebesgue (path_inside p1) = I1 + B1/2 - 1 \<Longrightarrow> measure lebesgue (path_inside p2) = I2 + B2/2 - 1"
    by blast
qed

lemma pick_split_union:
  assumes is_split: "is_polygon_split vts i j"
  assumes "vts1 = (take i vts)" 
  assumes "vts2 = (take (j - i - 1) (drop (Suc i) vts)) "
  assumes "vts3 = drop (j - i) (drop (Suc i) vts) "
  assumes "x = vts ! i "
  assumes "y = vts ! j "
  assumes p: "p = make_polygonal_path (vts@[vts!0])" (is "p = make_polygonal_path ?p_vts")
  assumes p1: "p1 = make_polygonal_path (x#(vts2@[y, x]))" (is "p1 = make_polygonal_path ?p1_vts")
  assumes p2: "p2 = make_polygonal_path (vts1 @ [x, y] @ vts3 @ [vts ! 0])" (is "p2 = make_polygonal_path ?p2_vts")
  assumes I1: "I1 = card {x. integral_vec x \<and> x \<in> path_inside p1}" 
  assumes B1: "B1 = card {x. integral_vec x \<and> x \<in> path_image p1}"
  assumes pick1: "measure lebesgue (path_inside p1) = I1 + B1/2 - 1"
  assumes I2: "I2 = card {x. integral_vec x \<and> x \<in> path_inside p2}" 
  assumes B2: "B2 = card {x. integral_vec x \<and> x \<in> path_image p2}"
  assumes pick2: "measure lebesgue (path_inside p2) = I2 + B2/2 - 1"
  assumes I: "I = card {x. integral_vec x \<and> x \<in> path_inside p}" 
  assumes B: "B = card {x. integral_vec x \<and> x \<in> path_image p}"
  assumes all_integral_vts: "all_integral vts"
  shows "measure lebesgue (path_inside p) = I + B/2 - 1"
        "measure lebesgue (path_inside p) = measure lebesgue (path_inside p1) + measure lebesgue (path_inside p2)"
proof -
  let ?p_im = "{x. integral_vec x \<and> x \<in> path_image p}"
  let ?p1_im = "{x. integral_vec x \<and> x \<in> path_image p1}"
  let ?p2_im = "{x. integral_vec x \<and> x \<in> path_image p2}"
  let ?p_int = "{x. integral_vec x \<and> x \<in> path_inside p}"
  let ?p1_int = "{x. integral_vec x \<and> x \<in> path_inside p1}"
  let ?p2_int = "{x. integral_vec x \<and> x \<in> path_inside p2}"

  have vts: "vts = vts1 @ (x # (vts2 @ y # vts3))"
    using assms split_up_a_list_into_3_parts
    using is_polygon_split_def by blast
  have "polygon p"
    using finite_path_image assms(1) p unfolding is_polygon_split_def 
    by (smt (verit, best))
  then have B_finite: "finite ?p_im"
    using finite_path_image by auto
  have polygon_p1: "polygon p1"
    using finite_path_image assms(1) p1 unfolding is_polygon_split_def 
    by (smt (z3) assms(3) assms(5) assms(6))
  then have B1_finite: "finite ?p1_im"
    using finite_path_image by auto
   have polygon_p2: "polygon p2"
     using finite_path_image assms(1) p1 unfolding is_polygon_split_def 
     by (smt (z3) assms(2) assms(4) assms(5) assms(6) p2)
  then have B2_finite: "finite ?p2_im"
    using finite_path_image by auto

  have vts_distinct: "distinct vts"
    using simple_polygonal_path_vts_distinct
    by (metis \<open>polygon p\<close> butlast_snoc p polygon_def)
  then have x_neq_y: "x \<noteq> y"
    by (metis assms(1) assms(5) assms(6) index_first index_nth_id is_polygon_split_def)
  then have card_2: "card {x, y} = 2"
    by auto
  have polygon_split_props: "is_polygon_cut ?p_vts x y \<and>
      polygon p \<and> polygon p1 \<and> polygon p2 \<and>
      path_inside p1 \<inter> path_inside p2 = {} \<and>
      path_inside p1 \<union> path_inside p2 \<union> (path_image (linepath x y) - {x, y})
         = path_inside p \<and> ((path_image p1) - (path_image (linepath x y))) \<inter> ((path_image p2) - (path_image (linepath x y))) = {}
     \<and> path_image p = ((path_image p1) - (path_image (linepath x y))) \<union> ((path_image p2) - (path_image (linepath x y))) \<union> {x, y} "
    using assms 
    by (meson is_polygon_split_def)
  have "measure lebesgue (path_inside p) = measure lebesgue (path_inside p1) + measure lebesgue (path_inside p2)"
    using polygon_split_add_measure assms
    by (smt (verit, del_insts)) 
  then have measure_sum: "measure lebesgue (path_inside p) = I1 + I2 + (B1+B2)/2 -2"
    using pick1 pick2 by auto

  let ?yx_int = "{k. integral_vec k \<and> k \<in> path_image (linepath y x)}"
  let ?xy_int = "{k. integral_vec k \<and> k \<in> path_image (linepath x y)}"
  have yx_int_is_xy_int: "?yx_int = ?xy_int"
    by (simp add: closed_segment_commute)

  have "sublist [y, x] ?p1_vts" by (simp add: sublist_Cons_right)
  then have subset1:
    "?xy_int \<subseteq> ?p1_im"
    using sublist_pair_integral_subset_integral_on_path p1 yx_int_is_xy_int by blast
  have subset2:
    "?xy_int \<subseteq> ?p2_im"
    using sublist_pair_integral_subset_integral_on_path p2 by blast

  let ?S1 = "?p1_im - ?xy_int"
  let ?S2 = "?p2_im - ?xy_int"
  have disjoint_1: "?S1 \<inter> ?S2 = {}"
    using polygon_split_props by blast

  have integral_xy: "integral_vec x \<and> integral_vec y"
    using all_integral_vts vts 
    using all_integral_def by auto
  then have "{x, y} \<subseteq> ?yx_int"
    by simp
  then have disjoint_2: "(?S1 \<union> ?S2) \<inter> {x, y} = {}"
    by simp
  have "path_image p =
  path_image p1 - path_image (linepath x y) \<union>
  (path_image p2 - path_image (linepath x y)) \<union>
  {x, y}"
    using polygon_split_props by auto
  then have set_union: "?p_im = (?S1 \<union> ?S2) \<union> {x, y}"
    using polygon_split_props integral_xy by auto
  then have add_card: "B = card (?p1_im - ?xy_int) + card (?p2_im - ?xy_int) + card {x, y}"
    using B_finite using disjoint_1 disjoint_2 
    by (metis (no_types, lifting) B card_Un_disjoint finite_Un)
  have sub1: "card (?p1_im - ?xy_int) = B1 - card ?xy_int"
    using B1_finite B1 subset1
    by (meson card_Diff_subset finite_subset)
  have sub2: "card (?p2_im - ?xy_int) = B2 - card ?xy_int"
    using B2_finite B2 subset2 
    by (meson card_Diff_subset finite_subset)
  have B: "B = (B1 - card ?xy_int) + (B2 - card ?xy_int) + card {x, y}"
    using add_card sub1 sub2
    by auto
  then have B_sum_h: "B = B1 + B2 - 2*card ?xy_int + 2"
    using card_2
    by (smt (verit, best) B1 B1_finite B2 B2_finite Nat.add_diff_assoc add.commute card_mono diff_diff_left mult_2 subset1 subset2) 
  then have "B1 + B2 = B + 2*card ?xy_int - 2"
    by (metis (no_types, lifting) B1 B1_finite B2 B2_finite add_mono_thms_linordered_semiring(1) card_mono diff_add_inverse2 le_add2 mult_2 ordered_cancel_comm_monoid_diff_class.add_diff_assoc2 subset1 subset2)
  then have B_sum: "(B1 + B2)/2 = B/2 + card ?xy_int - 1" 
    by (smt (verit) B_sum_h field_sum_of_halves le_add2 mult_2 nat_1_add_1 of_nat_1 of_nat_add of_nat_diff ordered_cancel_comm_monoid_diff_class.add_diff_assoc2)
  have casting_h: "\<And> A B:: nat. A \<ge> B \<Longrightarrow> real (A - B) = real A - real B"
    by auto
  have " path_inside p1 \<union> path_inside p2 \<union> (path_image (linepath x y) - {x, y}) = path_inside p"
    using polygon_split_props by auto
  then have interior_union: "?p_int = (?xy_int - {x, y}) \<union> ?p1_int \<union> ?p2_int"
    by blast  

  have finite_inside_p: "finite ?p_int"
    using bounded_finite inside_outside_polygon 
    by (simp add: polygon_split_props inside_outside_def)
  have finite_pathimage: "finite (?xy_int - {x, y})"
    using B1_finite finite_subset subset1 by auto
  have finite_inside_p1: "finite ?p1_int"
     using polygon_split_props bounded_finite inside_outside_polygon 
     using finite_Un finite_inside_p interior_union by auto
  have finite_inside_p2: "finite ?p2_int"
    using polygon_split_props bounded_finite inside_outside_polygon 
    using finite_Un finite_inside_p interior_union by auto
  have path_image_inside_disjoint1: "(?xy_int - {x, y}) \<inter> (?p1_int) = {}"
    using subset1 inside_outside_polygon[OF polygon_p1]
    unfolding inside_outside_def by auto
  have path_image_inside_disjoint2: "(?xy_int - {x, y}) \<inter> (?p2_int) = {}"
    using subset2  inside_outside_polygon[OF polygon_p2]
    unfolding inside_outside_def by auto
  have "(?xy_int - {x, y}) \<inter> (?p1_int \<union> ?p2_int) = {}" 
    using  subset2 path_image_inside_disjoint1 path_image_inside_disjoint2
    by auto
  then have I_is: "I = card (?xy_int - {x, y}) + 
    card (?p1_int \<union> ?p2_int)"
    using interior_union I finite_inside_p1 finite_inside_p2
    by (metis (no_types, lifting) card_Un_disjoint finite_Un finite_pathimage sup_assoc) 
  have disjoint_4: "?p1_int \<inter> ?p2_int = {}"
    using polygon_split_props by auto
  then have "I = card (?xy_int - {x, y}) + 
    I1 + I2"
    using I_is finite_inside_p1 finite_inside_p2 
    by (simp add: I1 I2 card_Un_disjoint)
  have interior_subset: "(?xy_int - {x, y}) \<subseteq> ?p_int"
    using interior_union by auto 
  have x_y_subset: "{x, y} \<subseteq> ?xy_int"
    using local.set_union by auto
  have " real (card (?xy_int - {x, y})) =
  real (card (?xy_int )) - real (card {x, y})"
    using x_y_subset
    by (metis (no_types, lifting) B2_finite card_Diff_subset card_mono finite_subset of_nat_diff subset2)
  then have card_diff: "real (card (?xy_int - {x, y})) =
  real (card (?xy_int )) - 2"
    using card_2 by auto
  then have "I = I1 + I2 + (card (?xy_int - {x, y}))"
    using I I1 I2 interior_union finite_inside_p1 finite_inside_p2 
    by (simp add: I_is disjoint_4 card_Un_disjoint)
  then have "I = I1 + I2 + real (card (?xy_int)) - 2"
    using card_diff 
    by linarith
  then have I_sum: "I1 + I2 = I - real (card ?xy_int) + 2"
    by fastforce
  have "measure lebesgue (path_inside p) = I - real (card ?xy_int) + 2 + 
   B/2 + card ?xy_int - 1 - 2"
    using measure_sum I_sum B_sum 
    by linarith
  then show "measure lebesgue (path_inside p) = I + B/2 - 1" by auto

  show "measure lebesgue (path_inside p) = measure lebesgue (path_inside p1) + measure lebesgue (path_inside p2)"
    using \<open>Sigma_Algebra.measure lebesgue (path_inside p) = Sigma_Algebra.measure lebesgue (path_inside p1) + Sigma_Algebra.measure lebesgue (path_inside p2)\<close> by blast
qed

lemma pick_split_path_union:
  assumes is_split: "is_polygon_split_path vts i j cutvts"
  assumes "vts1 = (take i vts)" 
  assumes "vts2 = (take (j - i - 1) (drop (Suc i) vts))"
  assumes "vts3 = drop (j - i) (drop (Suc i) vts)"
  assumes "x = vts!i"
  assumes "y = vts!j"
  assumes "cutpath = make_polygonal_path (x # cutvts @ [y])"
  assumes p: "p = make_polygonal_path (vts@[vts!0])" (is "p = make_polygonal_path ?p_vts")
  assumes p1: "p1 = make_polygonal_path (x#(vts2 @ [y] @ (rev cutvts) @ [x]))" (is "p1 = make_polygonal_path ?p1_vts")
  assumes p2: "p2 = make_polygonal_path (vts1 @ ([x] @ cutvts @ [y]) @ vts3 @ [vts ! 0])" (is "p2 = make_polygonal_path ?p2_vts")
  assumes I1: "I1 = card {x. integral_vec x \<and> x \<in> path_inside p1}" 
  assumes B1: "B1 = card {x. integral_vec x \<and> x \<in> path_image p1}"
  assumes pick1: "measure lebesgue (path_inside p1) = I1 + B1/2 - 1"
  assumes I2: "I2 = card {x. integral_vec x \<and> x \<in> path_inside p2}" 
  assumes B2: "B2 = card {x. integral_vec x \<and> x \<in> path_image p2}"
  assumes pick2: "measure lebesgue (path_inside p2) = I2 + B2/2 - 1"
  assumes I: "I = card {x. integral_vec x \<and> x \<in> path_inside p}" 
  assumes B: "B = card {x. integral_vec x \<and> x \<in> path_image p}"
  assumes all_integral_vts: "all_integral vts"
  shows "measure lebesgue (path_inside p) = I + B/2 - 1"
  using pick_split_path_union_main pick1 pick2(1) assms by blast

lemma pick_triangle_basic_split:
  assumes "p = make_triangle a b c" and "distinct [a, b, c]" and "\<not> collinear {a, b, c}" and
          d_prop: "d \<in> path_image (linepath a b) \<and> d \<notin> {a, b, c}"
  shows "good_linepath c d [a, d, b, c, a]
          \<and> path_image (make_polygonal_path [a, d, b, c, a]) = path_image p"
proof-
  let ?l = "linepath c d"
  let ?L = "path_image ?l"
  let ?P = "path_image p"
  let ?vts' = "[a, d, b, c, a]"
  let ?p' = "make_polygonal_path ?vts'"
  let ?P' = "path_image ?p'"

  have h1: "path_image (make_polygonal_path [a, b, c, a]) = path_image (linepath a b) \<union> path_image (linepath b c) \<union> path_image (linepath c a)"
    using polygonal_path_image_linepath_union by (simp add: path_image_join sup.assoc)
  have h2: "path_image (make_polygonal_path [a, d, b, c, a]) = path_image (linepath a d) \<union> path_image (linepath d b) \<union>  path_image (linepath b c) \<union>  path_image (linepath c a)"
    using polygonal_path_image_linepath_union by (simp add: path_image_join sup.assoc)
  have h3: "path_image (linepath a b) = path_image (linepath a d) \<union> path_image (linepath d b)"
    using path_image_linepath_union d_prop by auto 

  have 1: "?P' = ?P"
    using h1 h2 h3
    using assms(1) make_triangle_def by force

  have "{c, d} = ?L \<inter> ?P"
  proof(rule ccontr)
    have subs: "{c, d} \<subseteq> ?L \<inter> ?P"
      using assms(1) vertices_on_path_image unfolding make_triangle_def
      by (metis IntD2 IntI assms(4) empty_subsetI inf_sup_absorb insert_subset list.discI list.simps(15) nth_Cons_0 path_image_cons_union pathfinish_in_path_image pathfinish_linepath pathstart_in_path_image pathstart_linepath)  

    assume *: "{c, d} \<noteq> ?L \<inter> ?P"
    then obtain z where z: "z \<noteq> c \<and> z \<noteq> d \<and> z \<in> ?L \<inter> ?P" using subs by blast
    then have cases:
        "z \<in> path_image (linepath a b) \<or> z \<in> path_image (linepath b c) \<or> z \<in> path_image (linepath c a)"
      using "1" h2 h3 by blast
    { assume **: "z \<in> path_image (linepath a b)"
      moreover have "z \<in> ?L \<and> d \<in> ?L \<and> d \<in> path_image (linepath a b)" using assms z by force
      ultimately have "{z, d} \<subseteq> ?L \<inter> path_image (linepath a b) \<and> z \<noteq> d" using z by blast
      then have "collinear {a, b, c, d}" using two_linepath_colinearity_property by fastforce
      then have False using assms(2) assms(3) collinear_4_3 by auto
    } moreover
    { assume **: "z \<in> path_image (linepath b c)"
       then have "collinear {a, b, c, d}" using two_linepath_colinearity_property[of z _ b c c d]
        by (smt (verit) "**" IntE assms(3) collinear_3_trans d_prop in_path_image_imp_collinear insertCI insert_commute z)
      then have False using assms(2) assms(3) collinear_4_3 by auto
    } moreover
    { assume **: "z \<in> path_image (linepath c a)"
      then have "collinear {a, b, c, d}" using two_linepath_colinearity_property[of z _ c a c d]
        by (smt (verit) IntD1 assms(3) collinear_3_trans d_prop in_path_image_imp_collinear insert_commute insert_iff z)
      then have False using assms(2) assms(3) collinear_4_3 by auto
    }
    ultimately show False using cases by argo
  qed
  moreover have "?L \<subseteq> path_inside p \<union> ?P"
  proof-
    have "convex hull {a, b, c} = path_inside p \<union> ?P"
      by (simp add: Un_commute assms(1) assms(3) triangle_convex_hull)
    moreover have "?L \<subseteq> convex hull {a, b, c}"
      by (smt (verit, ccfv_threshold) assms empty_subsetI hull_insert hull_mono insert_commute insert_mono insert_subset path_image_linepath segment_convex_hull)
    ultimately show ?thesis by blast
  qed
  ultimately have "?L \<subseteq> path_inside p \<union> {c, d}" by blast
  then have "?L \<subseteq> path_inside ?p' \<union> {c, d}" using 1 unfolding path_inside_def by presburger
  then have 2: "good_linepath c d ?vts'" using assms unfolding good_linepath_def by auto

  thus ?thesis using 1 by blast
qed

section "Convex Hull Has Good Linepath"

lemma leq_2_extreme_points_means_collinear:
  fixes vts :: "'a::euclidean_space set"
  assumes "finite vts"
  assumes "card {v. v extreme_point_of (convex hull vts)} \<le> 2"
  shows "collinear vts"
  using assms
  by (metis Krein_Milman_polytope affine_hull_convex_hull collinear_affine_hull_collinear collinear_small extreme_points_of_convex_hull finite_subset)

lemma convex_hull_non_extreme_point_in_open_seg:
  assumes "H = convex hull vts"
  assumes "x \<in> H - {v. v extreme_point_of H}"
  shows "\<exists>a b. a \<in> H \<and> b \<in> H \<and> x \<in> open_segment a b"
  using assms unfolding extreme_point_of_def by blast

lemma convex_hull_extreme_points_vertex_split:
  fixes vts :: "(real^2) set"
  assumes "H = convex hull vts"
  assumes "finite vts"
  assumes "card {v. v extreme_point_of H} \<ge> 4"
  assumes "{a, b, c} \<subseteq> {v. v extreme_point_of H} \<and> distinct [a, b, c]"
  shows "path_image (linepath a b) \<inter> interior H \<noteq> {}
      \<or> path_image (linepath b c) \<inter> interior H \<noteq> {}
      \<or> path_image (linepath c a) \<inter> interior H \<noteq> {}"
proof-
  let ?ep = "{v. v extreme_point_of H}"

  have H: "H = convex hull ?ep" using Krein_Milman_polytope assms(1) assms(2) by blast
  let ?H' = "convex hull {a, b, c}"

  have not_collinear: "\<not> collinear {a, b, c}"
  proof(rule ccontr)
    assume "\<not> \<not> collinear {a, b, c}"
    then have "collinear {a, b, c}" by blast
    then have "a \<in> path_image (linepath b c)
        \<or> b \<in> path_image (linepath a c)
        \<or> c \<in> path_image (linepath a b)"
      using collinear_between_cases unfolding between_def
      by (smt (verit, del_insts) between_mem_segment closed_segment_eq collinear_between_cases doubleton_eq_iff path_image_linepath)
    moreover have "a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c" using assms by simp
    ultimately have "a \<in> open_segment b c \<or> b \<in> open_segment a c \<or> c \<in> open_segment a b"
      using closed_segment_eq_open by auto
    moreover have "a extreme_point_of H \<and> b extreme_point_of H \<and> c extreme_point_of H"
      using assms by blast
    ultimately show False unfolding extreme_point_of_def by blast
  qed

  have strict_subset: "interior ?H' \<subset> interior H"
  proof-
    have "interior ?H' \<subseteq> interior H"
      by (metis H assms(4) hull_mono interior_mono)
    moreover have "?H' \<subset> H"
    proof-
      have "card {a, b, c} \<le> 3"
        by (metis card.empty card_insert_disjoint collinear_2 finite.emptyI finite_insert insert_absorb nat_le_linear not_collinear numeral_3_eq_3)
      then have "card (?ep - {a, b, c}) \<ge> 1"
        using assms(3) assms(4) by auto
      then obtain d where "d \<in> ?ep - {a, b, c}"
        by (metis One_nat_def all_not_in_conv card.empty not_less_eq_eq zero_le)
      thus ?thesis
        by (metis DiffE H assms(4) extreme_point_of_convex_hull hull_mono mem_Collect_eq order_less_le)
    qed
    ultimately show ?thesis
      by (metis (no_types, lifting) assms(1) assms(2) closure_convex_hull convex_closure_rel_interior convex_convex_hull convex_hull_eq_empty convex_polygon_frontier_is_path_image2 dual_order.strict_iff_order finite.emptyI finite.insertI finite_imp_bounded_convex_hull finite_imp_compact frontier_empty insert_not_empty inside_frontier_eq_interior not_collinear path_inside_def polygon_frontier_is_path_image rel_interior_nonempty_interior sup_bot.right_neutral triangle_convex_hull triangle_is_convex triangle_is_polygon)
  qed
  moreover have "interior ?H' \<noteq> {}"
    by (metis not_collinear convex_convex_hull convex_hull_eq_empty convex_polygon_frontier_is_path_image2 finite.emptyI finite.insertI finite_imp_bounded_convex_hull frontier_empty insert_not_empty inside_frontier_eq_interior path_inside_def polygon_frontier_is_path_image sup_bot.right_neutral triangle_convex_hull triangle_is_convex triangle_is_polygon)
  ultimately obtain x y where xy: "x \<in> interior ?H' \<and> y \<in> interior H - interior ?H'" by blast

  let ?l = "linepath x y"

  have "x \<in> interior ?H' \<and> y \<in> -(interior ?H')" using xy by blast
  then have "path_image ?l \<inter> interior ?H' \<noteq> {} \<and> path_image ?l \<inter> -(interior ?H') \<noteq> {}" by auto
  moreover have "path_connected (interior ?H')" by (simp add: convex_imp_path_connected)
  ultimately obtain z where z: "z \<in> path_image ?l \<inter> frontier (interior ?H')"
    by (metis Diff_eq Diff_eq_empty_iff all_not_in_conv convex_convex_hull convex_imp_path_connected path_connected_not_frontier_subset path_image_linepath segment_convex_hull)
  moreover have "path_image ?l \<subseteq> interior H" using xy convex_interior[of H]
    by (metis DiffD1 IntD2 strict_subset assms(1) closed_segment_subset convex_convex_hull inf.strict_order_iff path_image_linepath)
  ultimately have z_interior: "z \<in> interior H" by blast

  have "z \<in> frontier (interior ?H')" using z by blast
  moreover have "frontier (interior ?H')
      = path_image (linepath a b) \<union> path_image (linepath b c) \<union> path_image (linepath c a)"
  proof-
    let ?p = "make_triangle a b c"
    have "path_inside ?p = interior ?H'"
      by (metis not_collinear bounded_convex_hull bounded_empty bounded_insert convex_convex_hull convex_polygon_frontier_is_path_image2 inside_frontier_eq_interior path_inside_def triangle_convex_hull triangle_is_convex triangle_is_polygon)
    then have "path_image ?p = frontier (interior ?H')"
      by (metis not_collinear polygon_frontier_is_path_image triangle_is_polygon)
    moreover have "path_image ?p
        = path_image (linepath a b) \<union> path_image (linepath b c) \<union> path_image (linepath c a)"
      by (metis Un_assoc list.discI make_polygonal_path.simps(3) make_triangle_def nth_Cons_0 path_image_cons_union)
    ultimately show ?thesis by presburger
  qed
  ultimately show ?thesis using z_interior by blast
qed

lemma convex_hull_has_vertex_split_helper_wlog:
  assumes "p = make_triangle a b c" and "distinct [a, b, c]" and "\<not> collinear {a, b, c}" and
    d_prop: "d \<in> path_image (linepath a b) \<and> d \<notin> {a, b, c}"
  shows "path_image (linepath c d) \<inter> path_inside p \<noteq> {}"
proof-
  have "good_linepath c d [a, d, b, c, a]
      \<and> path_image (make_polygonal_path [a, d, b, c, a]) = path_image p"
    using pick_triangle_basic_split[of p a b c d] assms by fast
  thus ?thesis
    unfolding good_linepath_def
    by (smt (verit, del_insts) Int_Un_eq(4) Int_insert_right_if1 Un_insert_right diff_points_path_image_set_property le_iff_inf path_inside_def pathfinish_in_path_image pathfinish_linepath pathstart_in_path_image pathstart_linepath)
qed

lemma convex_hull_has_vertex_split_helper:
  assumes "p = make_triangle a b c" and "distinct [a, b, c]" and "\<not> collinear {a, b, c}" and
    d_prop: "d \<in> path_image p \<and> d \<notin> {a, b, c}"
  shows "\<exists>x y. {x, y} \<subseteq> {a, b, c, d} \<and> x \<noteq> y \<and> path_image (linepath x y) \<inter> path_inside p \<noteq> {}"
proof-
  { assume "d \<in> path_image (linepath a b)"
    then have ?thesis
      using convex_hull_has_vertex_split_helper_wlog[of p a b c d] assms(1) assms(2) assms(3) d_prop
      by fastforce
  } moreover
  { assume *: "d \<in> path_image (linepath b c)"
    let ?p' = "make_triangle b c a"
    have "path_image (linepath a d) \<inter> path_inside ?p' \<noteq> {}"
      using convex_hull_has_vertex_split_helper_wlog[of ?p' b c a d]
      by (metis (no_types, opaque_lifting) "*" assms(3) collinear_2 d_prop distinct_length_2_or_more distinct_singleton insert_absorb2 insert_commute)
    moreover have "path_inside ?p' = path_inside p"
      unfolding make_triangle_def
      by (smt (verit, best) assms(1) assms(3) convex_polygon_frontier_is_path_image2 insert_commute make_triangle_def path_inside_def triangle_convex_hull triangle_is_convex triangle_is_polygon)
    ultimately have ?thesis using assms by auto
  } moreover
  { assume *: "d \<in> path_image (linepath c a)"
    let ?p' = "make_triangle c a b"
    have "path_image (linepath b d) \<inter> path_inside ?p' \<noteq> {}"
      using convex_hull_has_vertex_split_helper_wlog[of ?p' c a b d]
      by (metis (no_types, opaque_lifting) "*" assms(3) collinear_2 d_prop distinct_length_2_or_more distinct_singleton insert_absorb2 insert_commute)
    moreover have "path_inside ?p' = path_inside p"
      unfolding make_triangle_def
      by (smt (verit, ccfv_SIG) assms(1) assms(3) convex_polygon_frontier_is_path_image2 insert_commute make_triangle_def path_inside_def triangle_convex_hull triangle_is_convex triangle_is_polygon)
    ultimately have ?thesis using assms by auto
  }
  ultimately show ?thesis using on_triangle_path_image_cases assms(1) d_prop by fast
qed

lemma convex_hull_has_vertex_split:
  fixes vts :: "(real^2) set"
  assumes "H = convex hull vts"
  assumes "\<not> collinear vts"
  assumes "card vts > 3"
  assumes "finite vts"
  shows "\<exists>a b. {a, b} \<subseteq> vts \<and> a \<noteq> b \<and> path_image (linepath a b) \<inter> interior H \<noteq> {}"
proof-
  let ?ep = "{v. v extreme_point_of H}"
  have ep: "?ep \<subseteq> vts" by (simp add: assms(1) extreme_points_of_convex_hull)
  have card_ep: "card ?ep \<ge> 3"
    by (metis One_nat_def Suc_1 assms(1) assms(2) assms(3) card.infinite leq_2_extreme_points_means_collinear not_less_eq_eq not_less_zero numeral_3_eq_3)
  obtain a b c where abc: "{a, b, c} \<subseteq> ?ep \<and> a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c"
  proof-
    obtain a A where "a \<in> ?ep \<and> A = ?ep - {a} \<and> card A \<ge> 2" using card_ep by force
    moreover then obtain b B where "b \<in> A \<and> B = A - {b} \<and> card B \<ge> 1"
      by (metis Suc_1 Suc_diff_le bot.extremum_uniqueI bot_nat_0.extremum card_Diff_singleton card_eq_0_iff diff_Suc_1 less_Suc_eq_le less_one linorder_not_le subset_emptyI)
    moreover then obtain c C where "c \<in> B \<and> C = B - {c} \<and> card C \<ge> 0"
      by (metis One_nat_def bot_nat_0.extremum card.empty equals0I not_less_eq_eq)
    ultimately have "{a, b, c} \<subseteq> ?ep \<and> a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c" by blast
    thus ?thesis using that by auto
  qed
  { assume *: "card ?ep = 3"
    then have abc: "?ep = {a, b, c}"
      by (metis abc card_3_iff card_gt_0_iff numeral_3_eq_3 order_less_le psubset_card_mono zero_less_Suc)
    obtain d where d: "d \<in> vts \<and> d \<noteq> a \<and> d \<noteq> b \<and> d \<noteq> c"
      by (metis "*" assms(3) abc ep insertCI nat_less_le subsetI subset_antisym)
    { assume "d \<in> interior H"
      then have "d \<in> path_image (linepath a d) \<inter> interior H" by simp
      then have ?thesis using ep abc d by auto
    } moreover
    { assume ***: "d \<notin> interior H"
      let ?p = "make_triangle a b c"
      have H: "H = convex hull ?ep"
      proof-
        have "compact H"
          by (metis assms(1) assms(3) card_eq_0_iff finite_imp_compact_convex_hull gr_implies_not0)
        moreover have "convex H" using convex_convex_hull[of vts] assms by blast
        ultimately have "H = closure (convex hull ?ep)" using Krein_Milman[of H] by fast
        thus ?thesis using abc by auto
      qed
      then have interior: "path_inside ?p = interior H"
        using abc
        by (metis assms(1,2) affine_hull_convex_hull collinear_affine_hull_collinear convex_convex_hull convex_polygon_frontier_is_path_image2 finite.intros(1) finite_imp_bounded_convex_hull finite_insert inside_frontier_eq_interior path_inside_def triangle_convex_hull triangle_is_convex triangle_is_polygon)
      then have d_frontier: "d \<in> frontier H"
        by (metis *** Diff_iff assms(1) UnCI d closure_Un_frontier frontier_def hull_subset in_mono)
      moreover have "path_image ?p = frontier H"
        using convex_polygon_frontier_is_path_image
        by (metis assms(1,2) H abc affine_hull_convex_hull collinear_affine_hull_collinear convex_polygon_frontier_is_path_image2 triangle_convex_hull triangle_is_convex triangle_is_polygon)
      ultimately have "d \<in> path_image ?p" by blast
      moreover have "\<not> collinear {a, b, c}"
        by (metis H assms(1,2) abc affine_hull_convex_hull collinear_affine_hull_collinear)
      moreover then have "distinct [a, b, c]"
        by (metis collinear_2 distinct.simps(2) distinct_singleton empty_set insert_absorb list.simps(15))
      moreover have "d \<notin> {a, b, c}" using d by blast
      ultimately have ?thesis
        using abc d convex_hull_has_vertex_split_helper[of ?p a b c d]
        by (metis (no_types, lifting) insert_subset interior subset_trans ep)
    }
    ultimately have ?thesis by fast
  } moreover
  { assume *: "card ?ep \<ge> 4"
    moreover have "{a, b, c} \<subseteq> ?ep \<and> distinct [a, b, c]" using abc by fastforce
    ultimately have "path_image (linepath a b) \<inter> interior H \<noteq> {}
      \<or> path_image (linepath b c) \<inter> interior H \<noteq> {}
      \<or> path_image (linepath c a) \<inter> interior H \<noteq> {}"
      using convex_hull_extreme_points_vertex_split[OF assms(1) assms(4) *] by presburger
    then have ?thesis
      by (metis (no_types, lifting) ep abc insert_subset subset_trans)
  }
  ultimately show ?thesis using card_ep by fastforce
qed

lemma convex_polygon_has_good_linepath_helper:
  assumes "polygon_of p vts"
  assumes "convex (path_inside p \<union> path_image p)"
  assumes "card (set vts) > 3"
  obtains a b where "{a, b} \<subseteq> set vts \<and> a \<noteq> b \<and> \<not> path_image (linepath a b) \<subseteq> path_image p"
proof-
  let ?H = "convex hull (set vts)"
  obtain a b where ab: "{a, b} \<subseteq> set vts \<and> a \<noteq> b \<and> path_image (linepath a b) \<inter> interior ?H \<noteq> {}"
    using convex_hull_has_vertex_split assms polygon_vts_not_collinear unfolding polygon_of_def
    by fastforce
  moreover have "interior ?H = path_inside p"
    using assms(1) assms(2) convex_polygon_inside_is_convex_hull_interior polygon_convex_iff polygon_of_def
    by blast
  ultimately have "path_image (linepath a b) \<inter> path_inside p \<noteq> {}" by simp
  moreover have "path_inside p \<inter> path_image p = {}" using path_inside_def by auto
  moreover have "path_image (linepath a b) \<subseteq> path_image p \<union> path_inside p"
    by (metis ab assms(1) assms(2) convex_polygon_is_convex_hull hull_mono path_image_linepath polygon_of_def segment_convex_hull sup_commute)
  ultimately have "\<not> path_image (linepath a b) \<subseteq> path_image p" by fast
  thus ?thesis using ab that by meson
qed

lemma convex_polygon_has_good_linepath:
  assumes "convex (path_inside p \<union> path_image p)"
  assumes "polygon p"
  assumes "p = make_polygonal_path vts"
  assumes "card (set vts) > 3"
  shows "\<exists>a b. good_linepath a b vts"
proof-
  let ?T = "convex hull (set vts)"
  have T: "path_image p \<union> path_inside p = ?T"
    by (metis Un_commute assms(1) assms(2) assms(3) convex_polygon_is_convex_hull)
  obtain a b where ab: "a \<noteq> b \<and> {a, b} \<subseteq> set vts \<and> \<not> path_image (linepath a b) \<subseteq> path_image p"
    using convex_polygon_has_good_linepath_helper assms unfolding polygon_of_def by metis

  let ?S = "path_image (linepath a b)"

  have p_is_frontier: "frontier ?T = path_image p"
    using convex_polygon_frontier_is_path_image assms polygon_of_def polygon_convex_iff by blast

  have "closure ?T = ?T" by (simp add: finite_imp_compact)
  then have "?S \<subseteq> closure ?T" using ab by (simp add: hull_mono segment_convex_hull)
  moreover have "convex ?T" using convex_convex_hull by auto
  moreover have "convex ?S" by simp
  moreover have "rel_interior ?S = open_segment a b"
    by (metis ab path_image_linepath rel_interior_closed_segment)
  moreover have "rel_interior ?T = interior ?T"
    by (metis p_is_frontier Diff_empty ab calculation(1) frontier_def rel_interior_nonempty_interior)
  ultimately have "open_segment a b \<subseteq> interior ?T"
    using subset_rel_interior_convex by (metis ab p_is_frontier frontier_def rel_frontier_def)
  then have "(open_segment a b) \<inter> path_image p = {}"
    using p_is_frontier frontier_def by auto
  then have "closed_segment a b \<inter> path_image p = {a, b}"
    by (metis (no_types, lifting) Int_Un_distrib2 Int_absorb2 Un_commute ab assms(3) closed_segment_eq_open subset_trans sup_bot.right_neutral vertices_on_path_image)
  then have "path_image (linepath a b) \<inter> path_image p = {a, b}" by simp
  thus ?thesis
    using ab unfolding good_linepath_def
    by (smt (verit, ccfv_threshold) IntI UnCI UnE T assms(3) hull_mono path_image_linepath segment_convex_hull subset_iff)
qed

section "Pick's Theorem"

definition integral_inside:
  "integral_inside p = {x. integral_vec x \<and> x \<in> path_inside p}"

definition integral_boundary:
  "integral_boundary p = {x. integral_vec x \<and> x \<in> path_image p}"

subsection "Pick's Theorem Triangle Case"

definition pick_triangle:
  "pick_triangle p a b c \<longleftrightarrow>
      p = make_triangle a b c
      \<and> all_integral [a, b, c]
      \<and> distinct [a, b, c]
      \<and> \<not> collinear {a, b, c}"

definition pick_holds:
  "pick_holds p \<longleftrightarrow>
    (let I = card {x. integral_vec x \<and> x \<in> path_inside p} in
    let B = card {x. integral_vec x \<and> x \<in> path_image p} in
      measure lebesgue (path_inside p) = I + B/2 - 1)"

lemma pick_triangle_wlog_helper:
  assumes "pick_triangle p a b c" and
          "I = card (integral_inside p)" and
          "B = card (integral_boundary p)" and
          "integral_inside p = {}" and
          "integral_vec d \<and> d \<in> path_image (linepath a b) \<and> d \<notin> {a, b, c}" and "d \<notin> {a, b, c}" and
          ih: "\<And>p' a' b' c'. (card (integral_inside p') + card (integral_boundary p') < I + B) \<Longrightarrow> pick_triangle p' a' b' c' \<Longrightarrow> pick_holds p'"
  shows "measure lebesgue (path_inside p) = I + B/2 - 1"
proof-
  have polygon_p: "polygon p" using triangle_is_polygon assms unfolding pick_triangle by presburger
  then have polygon_of: "polygon_of p [a, b, c, a]"
    unfolding polygon_of_def using assms unfolding make_triangle_def pick_triangle by auto

  let ?p' = "make_polygonal_path [a, d, b, c, a]"

  have "good_linepath c d [a, d, b, c, a] \<and> path_image (make_polygonal_path [a, d, b, c, a]) = path_image p"
    using pick_triangle_basic_split assms unfolding pick_triangle by presburger
  then have *: "good_linepath d c [a, d, b, c, a] \<and> path_image (make_polygonal_path [a, d, b, c, a]) = path_image p"
    using good_linepath_comm by blast
  have polygon_new: "polygon (make_polygonal_path [a, d, b, c, a])"
    using polygon_linepath_split_is_polygon[OF polygon_of, of 0 a b d "[a, d, b, c, a]"] assms
    by force
  have h1: "make_polygonal_path [a, d, b, c, a] = make_polygonal_path ([a, d, b, c] @ [[a, d, b, c] ! 0])"
    by auto
  have h2: "good_linepath d c ([a, d, b, c] @ [[a, d, b, c] ! 0])"
    using *   by auto
  have h3: " (1::nat) < length [a, d, b, c] \<and> (3::nat) < length [a, d, b, c]"
    by auto
  then have polygon_split: "is_polygon_split [a, d, b, c] 1 3"
    using good_linepath_implies_polygon_split[OF polygon_new h1 h2 h3] by auto
  let ?p1 = "make_polygonal_path (d # [b] @ [c, d])"
  let ?p2 = "make_polygonal_path ([a] @ [d, c] @ [] @ [[a, d, b, c] ! 0])"
  let ?I1 = "card {x. integral_vec x \<and> x \<in> path_inside ?p1}"
  let ?B1 = "card {x. integral_vec x \<and> x \<in> path_image ?p1}"
  let ?I2 = "card {x. integral_vec x \<and> x \<in> path_inside ?p2}"
  let ?B2 = "card {x. integral_vec x \<and> x \<in> path_image ?p2}"
  have p1_triangle: "?p1 = make_triangle d b c"
    unfolding make_triangle_def by auto
  have p2_triangle: "?p2 = make_triangle a d c"
    unfolding make_triangle_def by auto
  have I_is: "I = card {x. integral_vec x \<and> x \<in> path_inside (make_polygonal_path [a, d, b, c, a])}"
    using path_image_linepath_split[of 0 "[a, b, c, a]" d] "*" assms path_inside_def integral_inside by presburger
  have B_is: "B = card {x. integral_vec x \<and> x \<in> path_image (make_polygonal_path [a, d, b, c, a])}"
    using path_image_linepath_split[of 0 "[a, b, c, a]" d]
    using "*" assms path_inside_def integral_boundary by presburger
  have all_integral_assump: "all_integral [a, d, b, c]"
    using assms unfolding all_integral_def pick_triangle by force
  
  (* First inductive hypothesis *)
  have dist_indh1: "distinct [d, b, c]"
    using assms unfolding pick_triangle by auto
  have coll_indh1: "\<not> collinear {d, b, c}"
    using assms pick_triangle
    by (smt (verit) collinear_3_trans dist_indh1 distinct_length_2_or_more in_path_image_imp_collinear insert_commute)
  have path_inside_inside: "path_inside (make_polygonal_path (d # [b] @ [c, d])) \<subseteq> path_inside p"
    using polygon_split unfolding is_polygon_split_def
    by (smt (z3) "*" One_nat_def Un_iff append_Cons append_Nil diff_Suc_1 drop0 drop_Suc_Cons nth_Cons_0 nth_Cons_Suc numeral_3_eq_3 path_inside_def subsetI take_Suc_Cons take_eq_Nil2) 
  then have indh1_card1: "card {x. integral_vec x \<and> x \<in> path_inside (make_polygonal_path (d # [b] @ [c, d]))}\<le> card {x. integral_vec x \<and> x \<in> path_inside p}"
    by (metis (no_types, lifting) assms(4) integral_inside Collect_empty_eq card.empty le_zero_eq subsetD)
  have indh1_card2: "card {x. integral_vec x \<and> x \<in> path_image (make_polygonal_path (d # [b] @ [c, d]))} < card {x. integral_vec x \<and> x \<in> path_image p}"
    (* Use polygon split and also that a isn't in the first set *)
  proof-
    have path_image_union: "path_image (make_polygonal_path (d # [b] @ [c, d])) = path_image (linepath d b) \<union> path_image (linepath b c) \<union> path_image (linepath c d)"
      using path_image_cons_union p1_triangle make_triangle_def
      by (metis (no_types, lifting) inf_sup_aci(6) list.discI make_polygonal_path.simps(3) nth_Cons_0) 
    have path_image_db:  "path_image (linepath d b) \<subseteq> path_image p"
      by (metis assms(5) list.discI nth_Cons_0 path_image_cons_union path_image_linepath_union polygon_of polygon_of_def sup.cobounded2 sup.coboundedI1)
    have path_image_bc:  "path_image (linepath b c) \<subseteq> path_image p"
      using assms(1) linepaths_subset_make_polygonal_path_image[of "[a, b, c, a]" 1] unfolding pick_triangle make_triangle_def 
      by simp
    have path_image_cd1: "path_image (linepath c d) - {c, d} \<subseteq> path_inside p"
      using polygon_split unfolding is_polygon_split_def 
      by (smt (z3) One_nat_def \<open>good_linepath c d [a, d, b, c, a] \<and> path_image (make_polygonal_path [a, d, b, c, a]) = path_image p\<close> append_Cons append_Nil insert_commute nth_Cons_0 nth_Cons_Suc numeral_3_eq_3 path_image_linepath path_inside_def segment_convex_hull sup.cobounded2)
    have path_image_cd2: "{c, d} \<subseteq> path_image p"
      using linepaths_subset_make_polygonal_path_image assms(1) unfolding pick_triangle make_triangle_def 
      by (metis (no_types, lifting) \<open>good_linepath c d [a, d, b, c, a] \<and> path_image (make_polygonal_path [a, d, b, c, a]) = path_image p\<close> good_linepath_def subset_trans vertices_on_path_image)
    have "path_image (linepath c d) \<subseteq> path_image p \<union> path_inside p"
      using path_image_cd1 path_image_cd2 by auto 
    moreover have "integral_inside p = {}" using assms by force
    ultimately have path_image_cd:  "integral_boundary (linepath c d) \<subseteq> integral_boundary p" unfolding integral_inside integral_boundary by blast
    have a_neq_d: "a \<noteq> d"
      using assms(5) by auto
    have a_neq_c: "a \<noteq> c"
      using assms(1) unfolding pick_triangle by simp
    have a_in_image: "a \<in> path_image p"
      using assms(1) unfolding pick_triangle make_triangle_def using vertices_on_path_image
      by fastforce
    have "path_image (linepath c d) \<inter> path_image p = {c, d}"
      using * unfolding good_linepath_def 
      by (smt (verit, ccfv_SIG) One_nat_def h1 insert_commute is_polygon_cut_def is_polygon_split_def nth_Cons_0 nth_Cons_Suc numeral_3_eq_3 path_image_linepath polygon_split segment_convex_hull)
    then have a_not_in1: "a \<notin> path_image (linepath c d)"
      using a_neq_c a_neq_d  a_in_image by blast
    have a_not_in2: "a \<notin> path_image (linepath d b)"
      using Int_closed_segment assms(5) by auto
    have a_not_in3: "a \<notin> path_image (linepath b c)"
      by (metis (no_types, lifting) assms(1) in_path_image_imp_collinear insert_commute pick_triangle)
    then have "a \<notin> path_image (linepath d b) \<union> path_image (linepath b c) \<union> path_image (linepath c d)"
      using a_not_in1 a_not_in2 a_not_in3 by simp
    then have "a \<in> integral_boundary p \<and> a \<notin> integral_boundary (make_polygonal_path [d, b, c, d])"
      using path_image_union using integral_boundary a_in_image all_integral_assump all_integral_def by auto
    then have strict_subset: "integral_boundary (make_polygonal_path [d, b, c, d]) \<subset> integral_boundary p"
      using path_image_union path_image_db path_image_bc path_image_cd 
      unfolding integral_boundary by auto
    have "integral_inside (make_polygonal_path [d, b, c, d]) = {}"
      using path_inside_inside assms unfolding integral_inside by auto
    then show ?thesis using assms(2-3) strict_subset bounded_finite  
      using finite_path_inside finite_path_image 
      by (simp add: integral_boundary polygon_p psubset_card_mono)
  qed
  have fewer_points_p1: " card {x. integral_vec x \<and> x \<in> path_inside (make_polygonal_path (d # [b] @ [c, d]))} +
      card {x. integral_vec x \<and> x \<in> path_image (make_polygonal_path (d # [b] @ [c, d]))}
      < card {x. integral_vec x \<and> x \<in> path_inside p} +
      card {x. integral_vec x \<and> x \<in> path_image p}" 
    using indh1_card1 indh1_card2 by linarith
  have indh_1: "Sigma_Algebra.measure lebesgue (path_inside ?p1) = real ?I1 + real ?B1 / 2 - 1"
    using assms fewer_points_p1 p1_triangle all_integral_assump dist_indh1 coll_indh1 all_integral_def
    unfolding pick_holds pick_triangle integral_inside integral_boundary by simp

  (* Second inductive hypothesis *)
  have dist_indh2: "distinct [a, d, c]"
    using assms unfolding pick_triangle by auto
  have coll_indh2: "\<not> collinear {a, d, c}"
    using assms pick_triangle
    by (smt (verit) collinear_3_trans dist_indh2 distinct_length_2_or_more in_path_image_imp_collinear insert_commute)
  have path_inside_inside: "path_inside (make_polygonal_path (a # [d] @ [c, a])) \<subseteq> path_inside p"
    using polygon_split unfolding is_polygon_split_def
    by (smt (z3) "*" One_nat_def Un_iff append_Cons append_Nil diff_Suc_1 drop0 drop_Suc_Cons nth_Cons_0 nth_Cons_Suc numeral_3_eq_3 path_inside_def subsetI take_Suc_Cons take_eq_Nil2) 
  then have indh2_card1: "card {x. integral_vec x \<and> x \<in> path_inside (make_polygonal_path (a # [d] @ [c, a]))}\<le> card {x. integral_vec x \<and> x \<in> path_inside p}"
    by (metis (no_types, lifting) assms(4) integral_inside Collect_empty_eq card.empty le_zero_eq subsetD)
  have indh2_card2: "card {x. integral_vec x \<and> x \<in> path_image (make_polygonal_path (a # [d] @ [c, a]))} < card {x. integral_vec x \<and> x \<in> path_image p}"
    (* Use polygon split and also that a isn't in the first set *)
  proof-
    have path_image_union: "path_image (make_polygonal_path (a # [d] @ [c, a])) = path_image (linepath a d) \<union> path_image (linepath d c) \<union> path_image (linepath c a)"
      using path_image_cons_union p2_triangle make_triangle_def 
      by (metis Un_assoc append.left_neutral append_Cons list.discI make_polygonal_path.simps(3) nth_Cons_0)
    have path_image_ad:  "path_image (linepath a d) \<subseteq> path_image p"
      by (metis \<open>good_linepath c d [a, d, b, c, a] \<and> path_image (make_polygonal_path [a, d, b, c, a]) = path_image p\<close> inf_sup_absorb le_iff_inf list.discI nth_Cons_0 path_image_cons_union)
    have path_image_ca:  "path_image (linepath c a) \<subseteq> path_image p"
      using assms(1) linepaths_subset_make_polygonal_path_image[of "[a, b, c, a]" 2] unfolding pick_triangle make_triangle_def 
      by simp
    have path_image_cd1: "path_image (linepath d c) - {c, d} \<subseteq> path_inside p"
      using polygon_split unfolding is_polygon_split_def 
      by (smt (z3) One_nat_def \<open>good_linepath c d [a, d, b, c, a] \<and> path_image (make_polygonal_path [a, d, b, c, a]) = path_image p\<close> append_Cons append_Nil insert_commute nth_Cons_0 nth_Cons_Suc numeral_3_eq_3 path_image_linepath path_inside_def segment_convex_hull sup.cobounded2)
    have path_image_cd2: "{c, d} \<subseteq> path_image p"
      using linepaths_subset_make_polygonal_path_image assms(1) unfolding pick_triangle make_triangle_def 
      by (metis (no_types, lifting) \<open>good_linepath c d [a, d, b, c, a] \<and> path_image (make_polygonal_path [a, d, b, c, a]) = path_image p\<close> good_linepath_def subset_trans vertices_on_path_image)
    have "path_image (linepath d c) \<subseteq> path_image p \<union> path_inside p"
      using path_image_cd1 path_image_cd2 by auto 
    moreover have "integral_inside p = {}" using assms by force
    ultimately have path_image_cd:  "integral_boundary (linepath d c) \<subseteq> integral_boundary p" unfolding integral_inside integral_boundary by blast
    have b_neq_d: "b \<noteq> d"
      using assms(5) by auto
    have b_neq_c: "b \<noteq> c"
      using assms(1) unfolding pick_triangle by simp
    have b_in_image: "b \<in> path_image p"
      using assms(1) unfolding pick_triangle make_triangle_def using vertices_on_path_image
      by fastforce
    have "path_image (linepath d c) \<inter> path_image p = {d, c}"
      using * unfolding good_linepath_def 
      by (smt (verit, ccfv_SIG) One_nat_def h1 insert_commute is_polygon_cut_def is_polygon_split_def nth_Cons_0 nth_Cons_Suc numeral_3_eq_3 path_image_linepath polygon_split segment_convex_hull)
    then have b_not_in1: "b \<notin> path_image (linepath d c)"
      using b_neq_c b_neq_d  b_in_image by blast
    have b_not_in2: "b \<notin> path_image (linepath a d)"
      using Int_closed_segment assms(5) by auto
    have b_not_in3: "b \<notin> path_image (linepath c a)"
      by (metis (no_types, lifting) assms(1) in_path_image_imp_collinear insert_commute pick_triangle)
    then have "b \<notin> path_image (linepath a d) \<union> path_image (linepath d c) \<union> path_image (linepath c a)"
      using b_not_in1 b_not_in2 b_not_in3 by simp
    then have "b \<in> integral_boundary p \<and> b \<notin> integral_boundary (make_polygonal_path [a, d, c, a])"
      using path_image_union using integral_boundary b_in_image all_integral_assump all_integral_def by auto
    then have strict_subset: "integral_boundary (make_polygonal_path [a, d, c, a]) \<subset> integral_boundary p"
      using path_image_union path_image_ad path_image_ca path_image_cd 
      unfolding integral_boundary by auto
    have "integral_inside (make_polygonal_path [a, d, c, a]) = {}"
      using path_inside_inside assms unfolding integral_inside by auto
    then show ?thesis using assms(2-3) strict_subset bounded_finite  
      using finite_path_inside finite_path_image 
      by (simp add: integral_boundary polygon_p psubset_card_mono)
  qed
  have fewer_points_p2: " card {x. integral_vec x \<and> x \<in> path_inside (make_polygonal_path ([a, d, c, a]))} +
      card {x. integral_vec x \<and> x \<in> path_image (make_polygonal_path ([a, d, c, a]))}
      < card {x. integral_vec x \<and> x \<in> path_inside p} +
      card {x. integral_vec x \<and> x \<in> path_image p}" 
    using indh2_card1 indh2_card2 by simp
  have indh_2: "Sigma_Algebra.measure lebesgue (path_inside ?p2) = real ?I2 + real ?B2 / 2 - 1"
    using fewer_points_p2 using assms fewer_points_p2 p2_triangle all_integral_assump dist_indh2 coll_indh2 all_integral_def
    unfolding pick_holds pick_triangle integral_inside integral_boundary by simp

  (* Use the induction *)
  have "Sigma_Algebra.measure lebesgue (path_inside ?p1) = real ?I1 + real ?B1 / 2 - 1 \<Longrightarrow>
      Sigma_Algebra.measure lebesgue (path_inside ?p2) = real ?I2 + real ?B2 / 2 - 1 \<Longrightarrow>
      I = card {x. integral_vec x \<and> x \<in> path_inside (make_polygonal_path [a, d, b, c, a])} \<Longrightarrow>
      B = card {x. integral_vec x \<and> x \<in> path_image (make_polygonal_path [a, d, b, c, a])} \<Longrightarrow>
      all_integral [a, d, b, c] \<Longrightarrow>
      Sigma_Algebra.measure lebesgue (path_inside (make_polygonal_path [a, d, b, c, a])) =
      real I + real B / 2 - 1"
    using pick_split_union[OF polygon_split, of "[a]" "[b]" "[]" d c ?p'] by auto
  then have "Sigma_Algebra.measure lebesgue (path_inside (make_polygonal_path [a, d, b, c, a])) =
      real I + real B / 2 - 1"
    using I_is B_is all_integral_assump indh_1 indh_2 by auto
  thus "measure lebesgue (path_inside p) = I + B/2 - 1"
    using path_image_linepath_split[of 0 "[a, b, c, a]" d] by (metis path_inside_def *)
qed

lemma pick_triangle_helper:
  assumes "pick_triangle p a b c" and
          "I = card (integral_inside p)" and
          "B = card (integral_boundary p)" and
          "integral_inside p = {}" and
          "integral_vec d \<and> d \<notin> {a, b, c}" and "d \<notin> {a, b, c}" and
          "d \<in> path_image (linepath a b)
            \<or> d \<in> path_image (linepath b c)
            \<or> d \<in> path_image (linepath c a)" and
          ih: "\<And>p' a' b' c'. (card (integral_inside p') + card (integral_boundary p') < I + B) \<Longrightarrow> pick_triangle p' a' b' c' \<Longrightarrow> pick_holds p'"
  shows "measure lebesgue (path_inside p) = I + B/2 - 1"
proof-
  { assume "d \<in> path_image (linepath a b)"
    then have ?thesis using pick_triangle_wlog_helper assms by blast
  } moreover
  { assume *: "d \<in> path_image (linepath b c)"
    let ?p' = "make_polygonal_path (rotate_polygon_vertices [a, b, c, a] 1)"
    let ?I' = "card (integral_inside ?p')"
    let ?B' = "card (integral_boundary ?p')"

    have p'_p: "path_image ?p' = path_image p \<and> path_inside ?p' = path_inside p"
      unfolding path_inside_def
      using assms(1) make_triangle_def pick_triangle polygon_vts_arb_rotation triangle_is_polygon
      by auto

    have "rotate_polygon_vertices [a, b, c, a] 1 = [b, c, a, b]"
      unfolding rotate_polygon_vertices_def by simp
    then have pick_triangle_p': "pick_triangle ?p' b c a"
      using assms unfolding pick_triangle
      by (smt (verit, best) all_integral_def distinct_length_2_or_more insert_commute list.simps(15) make_triangle_def)
    then have "measure lebesgue (path_inside ?p') = ?I' + ?B'/2 - 1"
      using pick_triangle_wlog_helper[of ?p' b c a ?I' ?B' d] assms
      using integral_boundary integral_inside * insert_commute pick_triangle_p' p'_p
      by auto
    moreover have "?I' = I \<and> ?B' = B" using p'_p integral_boundary integral_inside assms(2) assms(3) by presburger
    ultimately have ?thesis using p'_p by auto
  } moreover
  { assume *: "d \<in> path_image (linepath c a)"
    let ?p' = "make_polygonal_path (rotate_polygon_vertices [a, b, c, a] 2)"
    let ?I' = "card (integral_inside ?p')"
    let ?B' = "card (integral_boundary ?p')"

    have p'_p: "path_image ?p' = path_image p \<and> path_inside ?p' = path_inside p"
      unfolding path_inside_def
      using assms(1) make_triangle_def pick_triangle polygon_vts_arb_rotation triangle_is_polygon
      by auto

    have "rotate_polygon_vertices [a, b, c, a] 1 = [b, c, a, b]"
      unfolding rotate_polygon_vertices_def by simp
    also have "rotate_polygon_vertices ... 1 = [c, a, b, c]"
      unfolding rotate_polygon_vertices_def by simp
    ultimately have "rotate_polygon_vertices [a, b, c, a] 2 = [c, a, b, c]"
      by (metis Suc_1 arb_rotation_as_single_rotation)
    then have pick_triangle_p': "pick_triangle ?p' c a b"
      using assms unfolding pick_triangle
      by (smt (verit, best) all_integral_def distinct_length_2_or_more insert_commute list.simps(15) make_triangle_def)
    then have "measure lebesgue (path_inside ?p') = ?I' + ?B'/2 - 1"
      using pick_triangle_wlog_helper[of ?p' c a b ?I' ?B' d] assms
      using integral_boundary integral_inside * insert_commute pick_triangle_p' p'_p
      by auto
    moreover have "?I' = I \<and> ?B' = B" using p'_p integral_boundary integral_inside assms(2) assms(3) by presburger
    ultimately have ?thesis using p'_p by auto
  }
  ultimately show ?thesis using assms by blast
qed

lemma triangle_3_split_helper:
  fixes a b :: "'a::euclidean_space"
  assumes "a \<in> frontier S"
  assumes "b \<in> interior S"
  assumes "convex S"
  assumes "closed S"
  shows "path_image (linepath a b) \<inter> frontier S = {a}"
proof-
  let ?L = "path_image (linepath a b)"
  have "a \<in> S \<and> b \<in> S" using assms frontier_subset_closed interior_subset by auto
  then have "?L \<subseteq> S"
    using assms hull_minimal segment_convex_hull by (simp add: closed_segment_subset)
  then have "?L \<subseteq> closure S" using assms(4) by auto
  moreover have "convex ?L" by simp
  moreover have "?L \<inter> interior S \<noteq> {}" using assms(2) by auto
  moreover then have "\<not> ?L \<subseteq> rel_frontier S"
    by (metis DiffE assms(2) interior_subset_rel_interior pathfinish_in_path_image pathfinish_linepath rel_frontier_def subsetD)
  ultimately have "rel_interior ?L \<subseteq> rel_interior S"
    using subset_rel_interior_convex[of ?L S] assms by fastforce
  then have "open_segment a b \<subseteq> interior S"
    by (metis all_not_in_conv assms(2) empty_subsetI open_segment_eq_empty' path_image_linepath rel_interior_closed_segment rel_interior_nonempty_interior)
  moreover have "?L = closed_segment a b" by auto
  moreover have "interior S \<inter> frontier S = {}" by (simp add: frontier_def)
  ultimately have "?L \<inter> frontier S \<subseteq> {a, b}"
    by (smt (verit) Diff_iff disjoint_iff inf_commute inf_le1 open_segment_def subsetD subsetI)
  moreover have "b \<notin> frontier S" by (simp add: assms(2) frontier_def)
  ultimately show ?thesis using assms(1) by auto
qed

lemma unit_triangle_interior_point_not_collinear_e1_e2:
  assumes "p = make_triangle (vector [0, 0]) (vector [1, 0]) (vector [0, 1])"
    (is "p = make_triangle ?O ?e1 ?e2")
  assumes "z \<in> path_inside p"
  shows "\<not> collinear {?O, ?e1, z}"
proof-
  have "path_inside p = interior (convex hull {?O, ?e1, ?e2})"
    by (metis assms(1) bounded_convex_hull bounded_empty bounded_insert convex_convex_hull convex_polygon_frontier_is_path_image2 inside_frontier_eq_interior path_inside_def triangle_convex_hull triangle_is_convex triangle_is_polygon unit_triangle_vts_not_collinear)
  then have "z \<in> interior (convex hull {?O, ?e1, ?e2})" using assms by simp
  then have z: "z$1 > 0 \<and> z$2 > 0"
    using assms(1) assms(2) unit_triangle_interior_char make_triangle_def by blast
  have abc: "?O$1 = 0 \<and> ?O$2 = 0 \<and> ?e1$2 = 0 \<and> ?e2$1 = 0" by simp

  show "\<not> collinear {?O, ?e1, z}"
  proof(rule ccontr)
    assume "\<not> \<not> collinear {?O, ?e1, z}"
    then have *: "collinear {?O, ?e1, z}" by blast
    then obtain u c1 c2 where u: "?O - ?e1 = c1 *\<^sub>R u \<and> ?e1 - z = c2 *\<^sub>R u"
      unfolding collinear_def by blast
    moreover have "c1 \<noteq> 0"
    proof-
      have "(?O - ?e1)$1 = -1" by simp
      moreover have "(?O - ?e1)$1 = (c1 *\<^sub>R u)$1" using u by presburger
      ultimately show ?thesis by force
    qed
    moreover have "(?O - ?e1)$2 = 0" by simp
    moreover have "(?O - ?e1)$2 = (c1 *\<^sub>R u)$2" by (simp add: calculation(1))
    ultimately have "u$2 = 0" by auto
    thus False
      by (smt (verit, ccfv_threshold) u abc scaleR_eq_0_iff vector_minus_component vector_scaleR_component z)
  qed
qed

lemma triangle_interior_point_not_collinear_vertices_wlog_helper:
  assumes "p = make_triangle a b c"
  assumes "polygon p"
  assumes "z \<in> path_inside p"
  shows "\<not> collinear {a, b, z}"
proof-
  let ?O = "(vector [0, 0])::(real^2)"
  let ?e1 = "(vector [1, 0])::(real^2)"
  let ?e2 = "(vector [0, 1])::(real^2)"
  let ?M = "triangle_affine a b c"
  have a: "?M ?O = a"
    using triangle_affine_e1_e2 by blast
  have b: "?M ?e1 = b" using triangle_affine_e1_e2 by simp
  have c: "?M ?e2 = c" using triangle_affine_e1_e2 by simp

  have abc_not_collinear: "\<not> collinear {a, b, c}"
    using assms polygon_vts_not_collinear unfolding make_triangle_def polygon_of_def
    by (metis (no_types, lifting) empty_set insertCI insert_absorb insert_commute list.simps(15))

  have "convex hull {a, b, c} = convex hull {?M ?O, ?M ?e1, ?M ?e2}"
    using a b c by simp
  also have "... = ?M ` (convex hull {?O, ?e1, ?e2})"
    using calculation triangle_affine_img by blast
  also have interior_preserve: "interior ... = ?M ` (interior (convex hull {?O, ?e1, ?e2}))"
    using triangle_affine_preserves_interior[of ?M a b c _ "convex hull {?O, ?e1, ?e2}"]
    using abc_not_collinear
    by presburger
  finally have z: "z \<in> ?M ` (interior (convex hull {?O, ?e1, ?e2}))"
    using assms(1) assms(2) assms(3) make_triangle_def polygon_of_def triangle_inside_is_convex_hull_interior
    by auto
  then obtain z' where z': "z' \<in> interior (convex hull {?O, ?e1, ?e2}) \<and> ?M z' = z" by fast
  then have "\<not> collinear {?O, ?e1, z'}"
    by (metis convex_convex_hull convex_polygon_frontier_is_path_image2 finite.intros(1) finite_imp_bounded_convex_hull finite_insert inside_frontier_eq_interior path_inside_def triangle_convex_hull triangle_is_convex triangle_is_polygon unit_triangle_interior_point_not_collinear_e1_e2 unit_triangle_vts_not_collinear)
  then have z'_notin: "z' \<notin> affine hull {?O, ?e1}" using affine_hull_3_imp_collinear by blast
  then have "?M z' \<notin> affine hull {?M ?O, ?M ?e1}"
  proof-
    have "inj ?M" using triangle_affine_inj abc_not_collinear by blast
    then have "?M z' \<notin> ?M ` (affine hull {?O, ?e1})" using z'_notin by (simp add: inj_image_mem_iff)
    moreover have "?M ` (affine hull {?O, ?e1}) = affine hull {?M ?O, ?M ?e1}"
      using triangle_affine_preserves_affine_hull[of _ a b c] abc_not_collinear by simp
    ultimately show ?thesis by blast
  qed
  then have "z \<notin> affine hull {a, b}" using a b z' by argo
  thus ?thesis
    by (metis interior_preserve z affine_hull_convex_hull affine_hull_nonempty_interior collinear_2 collinear_3_affine_hull collinear_affine_hull_collinear empty_iff insert_absorb2 triangle_affine_img unit_triangle_vts_not_collinear z')
qed

lemma triangle_interior_point_not_collinear_vertices:
  assumes "p = make_triangle a b c"
  assumes "polygon p"
  assumes "z \<in> path_inside p"
  shows "\<not> collinear {a, b, z} \<and> \<not> collinear {a, c, z} \<and> \<not> collinear {b, c, z}"
proof-
  let ?p1 = "make_triangle b c a"
  let ?p2 = "make_triangle c a b"
  have p1: "?p1 = make_polygonal_path (rotate_polygon_vertices [a, b, c, a] 1)"
    using assms unfolding make_triangle_def rotate_polygon_vertices_def by fastforce
  have p2: "?p2 = make_polygonal_path (rotate_polygon_vertices [a, b, c, a] 2)"
    using assms unfolding make_triangle_def rotate_polygon_vertices_def by (simp add: numeral_Bit0)

  have "path_inside ?p1 = path_inside p \<and> path_inside ?p2 = path_inside p"
    using p1 p2 unfolding path_inside_def
    using assms(1) assms(2) make_triangle_def polygon_vts_arb_rotation by force
  then have "z \<in> path_inside ?p1 \<and> z \<in> path_inside ?p2" using assms by force
  moreover have "polygon ?p1 \<and> polygon ?p2"
    using assms make_triangle_def p1 p2 rotation_is_polygon by presburger
  ultimately show ?thesis
    using assms triangle_interior_point_not_collinear_vertices_wlog_helper
    by (smt (verit, best) insert_commute)
qed


lemma triangle_3_split:
  assumes "p = make_triangle a b c"
  assumes "polygon p"
  assumes "z \<in> path_inside p"
  shows "is_polygon_split_path [a, b, c] 0 1 [z]"
        "is_polygon_split [a, z, b, c] 1 3"
        "a \<notin> path_image (make_triangle z b c) \<union> path_inside (make_triangle z b c)"
        "b \<notin> path_image (make_triangle a z c) \<union> path_inside (make_triangle a z c)"
        "c \<notin> path_image (make_triangle a b z) \<union> path_inside (make_triangle a b z)"
proof-
  let ?q = "make_polygonal_path [a, z, b, c, a]"
  let ?cutpath = "make_polygonal_path [a, z, b]"
  let ?vts = "[a, b, c, a]"

  let ?l1 = "linepath a z"
  let ?l2 = "linepath z b"
  let ?S = "path_inside p \<union> path_image p"
  have "convex (path_inside p)"
    using triangle_is_convex assms(1,2) polygon_vts_not_collinear unfolding make_triangle_def
    by (simp add: polygon_of_def triangle_inside_is_convex_hull_interior)
  then have convex: "convex (path_inside p \<union> path_image p)"
    using polygon_convex_iff assms(2) by simp
  then have frontier: "frontier ?S = path_image p"
    using convex_polygon_frontier_is_path_image3 by (simp add: assms(2) sup_commute)
  have interior: "interior ?S = path_inside p"
    by (metis Jordan_inside_outside_real2 closed_path_def \<open>convex (path_inside p)\<close> assms(2) closure_Un_frontier convex_interior_closure interior_open path_inside_def polygon_def)

  have not_collinear: "\<not> collinear {a, b, z} \<and> \<not> collinear {a, c, z} \<and> \<not> collinear {b, c, z}"
    using triangle_interior_point_not_collinear_vertices assms(1) assms(2) assms(3) by blast

  have "a = pathstart ?cutpath \<and> b = pathfinish ?cutpath" by simp
  moreover have "a \<noteq> b"
    by (metis assms(1) assms(2) constant_linepath_is_not_loop_free make_polygonal_path.simps(4) make_triangle_def not_loop_free_first_component polygon_def simple_path_def)
  moreover have "polygon p" by (simp add: assms(2))
  moreover have "{a, b} \<subseteq> set ?vts" by force
  moreover have "simple_path ?cutpath"
    by (simp add: insert_commute not_collinear not_collinear_loopfree_path simple_path_def)
  moreover have "path_image ?cutpath \<inter> path_image p = {a, b}"
  proof-
    have "{a, b} \<subseteq> path_image ?cutpath \<inter> path_image p"
      by (metis (no_types, lifting) Int_subset_iff Un_subset_iff assms(1) insert_is_Un list.simps(15) make_triangle_def vertices_on_path_image)
    moreover have "path_image ?cutpath \<inter> path_image p \<subseteq> {a, b}"
    proof-
      have "z \<in> interior ?S" using assms interior by fast      
      moreover then have "a \<in> frontier ?S \<and> b \<in> frontier ?S"
        using vertices_on_path_image
        using \<open>{a, b} \<subseteq> path_image (make_polygonal_path [a, z, b]) \<inter> path_image p\<close> frontier by force
      moreover have "closed ?S" using frontier frontier_subset_eq by auto
      ultimately have "path_image ?l1 \<inter> path_image p = {a} \<and> path_image ?l2 \<inter> path_image p = {b}"
        using triangle_3_split_helper convex frontier
        by (metis (no_types, lifting) insert_commute path_image_linepath segment_convex_hull)
      moreover have "path_image ?cutpath = path_image ?l1 \<union> path_image ?l2"
        by (metis list.discI make_polygonal_path.simps(3) nth_Cons_0 path_image_cons_union)
      ultimately show ?thesis by blast
    qed
    ultimately show ?thesis by blast
  qed
  moreover have "path_image ?cutpath \<inter> path_inside p \<noteq> {}"
    by (metis (no_types, opaque_lifting) Int_Un_distrib2 Un_absorb2 Un_empty assms(3) insert_disjoint(2) list.simps(15) vertices_on_path_image)
  ultimately have cutpath: "is_polygon_cut_path ?vts ?cutpath"
    using assms unfolding make_triangle_def is_polygon_cut_path_def by simp
  thus 1: "is_polygon_split_path [a, b, c] 0 1 [z]"
    using polygon_cut_path_to_split_path assms(2) by (simp add: assms(1,2) make_triangle_def)

  let ?l = "linepath z c"
  let ?vts = "[a, z, b, c, a]"

  have c_noton_cutpath: "c \<notin> path_image ?cutpath"
    by (smt (verit) UnE assms(1) assms(2) assms(3) in_path_image_imp_collinear insert_commute make_polygonal_path.simps(3) neq_Nil_conv nth_Cons_0 path_image_cons_union triangle_interior_point_not_collinear_vertices)

  have "z \<noteq> c"
  proof-
    have "c \<in> path_image p"
      by (metis assms(1) insert_subset list.simps(15) make_triangle_def vertices_on_path_image)
    moreover have "path_image p \<inter> path_inside p = {}"
      by (simp add: disjoint_iff inside_def path_inside_def)
    ultimately show ?thesis using assms(3) by blast
  qed
  moreover have polygon_q: "polygon ?q"
    using 1 unfolding is_polygon_split_path_def
      (* may take a while to load *)
    by (smt (z3) One_nat_def append_Cons append_Nil diff_self_eq_0 drop0 drop_append length_Cons length_drop length_greater_0_conv list.size(3) nth_Cons_0 nth_Cons_Suc take_0)
  moreover have "{z, c} \<subseteq> set ?vts" by force
  moreover have l_q_int: "path_image ?l \<inter> path_image ?q = {z, c}"
  proof-
    have "{z, c} \<subseteq> path_image ?l \<inter> path_image ?q"
      by (metis (no_types, lifting) Int_subset_iff calculation(3) dual_order.trans hull_subset path_image_linepath segment_convex_hull vertices_on_path_image)
    moreover 
    { fix x
      assume *: "x \<in> path_image ?l \<inter> path_image ?q \<and> x \<noteq> z \<and> x \<noteq> c"
      then have "x \<in> path_image ?q" by blast
      then have "x \<in> path_image (linepath a z)
          \<or> x \<in> path_image (linepath z b)
          \<or> x \<in> path_image (linepath b c)
          \<or> x \<in> path_image (linepath c a)"
        by (metis UnE list.discI make_polygonal_path.simps(3) nth_Cons_0 path_image_cons_union)
      moreover
      { assume "x \<in> path_image (linepath a z)"
        then have "x \<in> path_image (linepath a z) \<and> x \<in> path_image (linepath z c)" using * by blast
        moreover have "z \<in> path_image (linepath a z) \<and> z \<in> path_image (linepath z c)" by simp
        moreover have "x \<noteq> z" using * by blast
        ultimately have "collinear {a, z, c}"
          by (smt (verit, best) collinear_3_trans in_path_image_imp_collinear insert_commute)
        then have False using not_collinear by (simp add: insert_commute)
      } moreover
      { assume "x \<in> path_image (linepath z b)"
        then have "x \<in> path_image (linepath z b) \<and> x \<in> path_image (linepath z c)" using * by blast
        moreover have "z \<in> path_image (linepath z b) \<and> z \<in> path_image (linepath z c)" by simp
        moreover have "x \<noteq> z" using * by blast
        ultimately have "collinear {z, b, c}"
          by (smt (verit, best) collinear_3_trans in_path_image_imp_collinear insert_commute)
        then have False using not_collinear by (simp add: insert_commute)
      } moreover
      { assume "x \<in> path_image (linepath b c)"
        then have "x \<in> path_image (linepath b c) \<and> x \<in> path_image (linepath z c)" using * by blast
        moreover have "c \<in> path_image (linepath b c) \<and> z \<in> path_image (linepath z c)" by simp
        moreover have "x \<noteq> c" using * by blast
        ultimately have "collinear {b, z, c}"
          by (smt (verit, best) collinear_3_trans in_path_image_imp_collinear insert_commute)
        then have False using not_collinear by (simp add: insert_commute)
      } moreover
      { assume "x \<in> path_image (linepath c a)"
        then have "x \<in> path_image (linepath c a) \<and> x \<in> path_image (linepath z c)" using * by blast
        moreover have "c \<in> path_image (linepath c a) \<and> z \<in> path_image (linepath z c)" by simp
        moreover have "x \<noteq> c" using * by blast
        ultimately have "collinear {a, z, c}"
          by (smt (verit, best) collinear_3_trans in_path_image_imp_collinear insert_commute)
        then have False using not_collinear by (simp add: insert_commute)
      }
      ultimately have False by blast
    }
    ultimately show ?thesis by blast
  qed
  moreover have "path_image ?l \<inter> path_inside ?q \<noteq> {}"
  proof(rule ccontr)
    let ?p' = "make_triangle a b z"

    assume "\<not> path_image ?l \<inter> path_inside ?q \<noteq> {}"
    then have "path_image ?l \<inter> path_inside ?q = {}" by blast
    then have *: "rel_interior (path_image ?l) \<inter> path_inside ?q = {}"
      by (meson disjoint_iff rel_interior_subset subset_eq)

    have "path_image ?l \<subseteq> path_image p \<union> path_inside p"
      by (metis UnCI assms(1) assms(3) empty_subsetI hull_minimal insert_subset list.simps(15) local.convex make_triangle_def path_image_linepath segment_convex_hull sup_commute vertices_on_path_image)
    then have "path_image ?l \<subseteq> convex hull {a, b, c}"
      by (smt (verit, best) assms(1) convex_polygon_is_convex_hull cutpath empty_set insertCI insert_absorb insert_commute is_polygon_cut_path_def list.simps(15) local.convex make_triangle_def sup_commute)
    then have "rel_interior (path_image ?l) \<subseteq> interior (convex hull {a, b, c})"
      by (smt (verit, ccfv_threshold) Diff_disjoint IntE IntI Un_upper1 assms(1) assms(2) assms(3) calculation(4) closure_Un_frontier convex_polygon_is_convex_hull convex_segment(1) dual_order.trans empty_iff empty_set insertCI insert_absorb2 insert_commute interior list.simps(15) local.convex make_triangle_def path_image_linepath rel_frontier_def rel_interior_nonempty_interior subsetD subset_rel_interior_convex)
    then have rel_interior: "rel_interior (path_image ?l) \<subseteq> path_inside p"
      by (smt (verit, best) assms(1) convex_polygon_is_convex_hull cutpath empty_set insertCI insert_absorb insert_commute interior is_polygon_cut_path_def list.simps(15) local.convex make_triangle_def)

    have "(let vts1 = []; vts2 = [];
           vts3 = [c]; x = a; y = b;
           cutpath = ?cutpath; p = make_polygonal_path ([a, b, c] @ [[a, b, c] ! 0]);
           p1 = make_polygonal_path (x # vts2 @ [y] @ rev [z] @ [x]);
           p2 = make_polygonal_path (vts1 @ ([x] @ [z] @ [y]) @ vts3 @ [[a, b, c] ! 0]);
           c1 = make_polygonal_path (x # vts2 @ [y]); c2 = make_polygonal_path (vts1 @ ([x] @ [z] @ [y]) @ vts3)
       in is_polygon_cut_path ([a, b, c] @ [[a, b, c] ! 0]) ?cutpath \<and>
          polygon p \<and>
          polygon p1 \<and>
          polygon p2 \<and>
          path_inside p1 \<inter> path_inside p2 = {} \<and>
          path_inside p1 \<union> path_inside p2 \<union> (path_image cutpath - {x, y}) = path_inside p \<and>
          (path_image p1 - path_image cutpath) \<inter> (path_image p2 - path_image ?cutpath) = {} \<and>
          path_image p = path_image p1 - path_image ?cutpath \<union> (path_image p2 - path_image ?cutpath) \<union> {x, y})"
      using 1 unfolding is_polygon_split_path_def by fastforce
    then have "(let
           p = make_polygonal_path ([a, b, c] @ [[a, b, c] ! 0]);
           p1 = make_polygonal_path (a # [] @ [b] @ rev [z] @ [a]);
           p2 = make_polygonal_path ([] @ ([a] @ [z] @ [b]) @ [c] @ [[a, b, c] ! 0])
       in path_inside p1 \<union> path_inside p2 \<union> (path_image ?cutpath - {a, b}) = path_inside p
          \<and> (path_image p1 - path_image ?cutpath) \<inter> (path_image p2 - path_image ?cutpath) = {})"
      by meson
    moreover have "?q = make_polygonal_path ([] @ ([a] @ [z] @ [b]) @ [c] @ [[a, b, c] ! 0])"
      by simp
    moreover have "?p' = make_polygonal_path (a # [] @ [b] @ rev [z] @ [a])"
      unfolding make_triangle_def by simp
    moreover have "p = make_polygonal_path ([a, b, c] @ [[a, b, c] ! 0])"
      unfolding assms make_triangle_def by auto
    ultimately have path_inside_p: "path_inside ?p'
        \<union> path_inside ?q
        \<union> (path_image ?cutpath - {a, b}) = path_inside p
        \<and> (path_image ?p' - path_image ?cutpath) \<inter> (path_image ?q - path_image ?cutpath) = {}"
      using 1 unfolding make_triangle_def is_polygon_split_path_def by metis
    moreover have "a \<in> path_image ?cutpath \<and> a \<notin> path_inside ?p' \<union> path_inside ?q"
      by (metis (no_types, lifting) UnI1 \<open>a = pathstart (make_polygonal_path [a, z, b]) \<and> b = pathfinish (make_polygonal_path [a, z, b])\<close> assms(1) assms(2) collinear_2 insert_absorb2 insert_commute path_inside_p pathstart_in_path_image triangle_interior_point_not_collinear_vertices_wlog_helper)
    moreover have "b \<in> path_image ?cutpath \<and> b \<notin> path_inside ?p' \<union> path_inside ?q"
      by (metis UnI1 \<open>a = pathstart (make_polygonal_path [a, z, b]) \<and> b = pathfinish (make_polygonal_path [a, z, b])\<close> assms(1) assms(2) collinear_2 insert_absorb2 path_inside_p pathfinish_in_path_image triangle_interior_point_not_collinear_vertices_wlog_helper)
    ultimately have "rel_interior (path_image ?l) \<subseteq>
        (path_inside ?p' - path_image ?cutpath)
        \<union> (path_image ?cutpath - {a, b})"
      using rel_interior * by blast
    then have "rel_interior (path_image ?l) \<subseteq> path_inside ?p' \<union> path_image ?cutpath" by blast
    moreover have "path_image ?cutpath \<subseteq> path_image ?p'"
    proof-
      have "path_image ?cutpath = path_image (linepath a z) \<union> path_image (linepath z b)"
        by (metis list.discI make_polygonal_path.simps(3) nth_Cons_0 path_image_cons_union)
      moreover have "path_image (linepath a z) = path_image (linepath z a)
          \<and> path_image (linepath z b) = path_image (linepath b z)"
        by (simp add: insert_commute)
      moreover have "path_image (linepath z a) \<subseteq> path_image ?p'
          \<and> path_image (linepath b z) \<subseteq> path_image ?p'"
        unfolding make_triangle_def
        by (metis Un_commute Un_upper2 list.discI nth_Cons_0 path_image_cons_union sup.coboundedI2)
      ultimately show ?thesis by blast
    qed
    ultimately have "rel_interior (path_image ?l) \<subseteq> path_inside ?p' \<union> path_image ?p'" by fast
    then have "rel_interior (path_image ?l) \<subseteq> convex hull {a, z, b}"
      unfolding make_triangle_def
      by (simp add: insert_commute make_triangle_def not_collinear sup_commute triangle_convex_hull)
    then have "closure (rel_interior (path_image ?l)) \<subseteq> closure (convex hull {a, z, b})"
      using closure_mono by blast
    then have "path_image ?l \<subseteq> convex hull {a, z, b}" by (simp add: convex_closure_rel_interior)
    then have c: "c \<in> path_image ?p' \<union> path_inside ?p'"
      unfolding make_triangle_def
      by (metis (no_types, lifting) IntE insertCI insert_commute l_q_int make_triangle_def not_collinear subsetD triangle_convex_hull)

    moreover have "c \<notin> path_image ?p'"
    proof-
      have "c \<in> path_image ?q - path_image ?cutpath" using c_noton_cutpath l_q_int by auto
      moreover have "(path_image ?p' - path_image ?cutpath) \<inter> (path_image ?q - path_image ?cutpath) = {}"
        using path_inside_p by fastforce
      ultimately show ?thesis by blast
    qed
    moreover have "c \<notin> path_inside ?p'"
      by (smt (verit, ccfv_threshold) DiffI IntD1 UnI1 UnI2 \<open>path_image (make_polygonal_path [a, z, b]) \<inter> path_image p = {a, b}\<close> \<open>path_image (make_polygonal_path [a, z, b]) \<subseteq> path_image (make_triangle a b z)\<close> assms(1) assms(2) calculation(2) collinear_2 in_mono insert_absorb2 path_inside_p triangle_interior_point_not_collinear_vertices)
    ultimately show False by blast
  qed
  ultimately have cutpath: "is_polygon_cut ?vts z c"
    using assms unfolding make_triangle_def is_polygon_cut_def by blast
  thus 2: "is_polygon_split [a, z, b, c] 1 3"
    using polygon_cut_to_split
    by (metis One_nat_def append_Cons append_Nil diff_Suc_1 length_Cons length_greater_0_conv lessI list.discI list.size(3) nth_Cons_0 nth_Cons_Suc numeral_3_eq_3 polygon_cut_to_split zero_less_diff)

  let ?p1 = "make_triangle a z c"
  let ?p2 = "make_triangle z b c"
  let ?p3 = "make_triangle a b z"
  
  have "(path_image ?p1 - path_image (linepath z c)) \<inter> (path_image ?p2 - path_image (linepath z c)) = {}"
    using 2 unfolding make_triangle_def is_polygon_split_def
    by (smt (z3) Int_commute One_nat_def Suc_1 append_Cons append_Nil diff_numeral_Suc diff_zero drop0 drop_Suc_Cons nth_Cons_0 nth_Cons_Suc nth_Cons_numeral pred_numeral_simps(3) take0 take_Cons_numeral take_Suc_Cons)
  moreover have "a \<notin> path_image (linepath z c) \<and> b \<notin> path_image (linepath z c)"
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) in_path_image_imp_collinear insert_commute triangle_interior_point_not_collinear_vertices)
  moreover have "a \<in> path_image ?p1 \<and> b \<in> path_image ?p2"
    by (metis insert_subset list.simps(15) make_triangle_def vertices_on_path_image)
  ultimately have "a \<notin> path_image ?p2 \<and> b \<notin> path_image ?p1" by auto
  moreover have "a \<notin> path_inside ?p2 \<and> b \<notin> path_inside ?p1"
  proof-
    have "a \<notin> path_inside p"
      by (metis (no_types, lifting) assms(1) assms(2) collinear_2 insertCI insert_absorb triangle_interior_point_not_collinear_vertices)
    moreover have "b \<notin> path_inside p"
      using assms(1) assms(2) triangle_interior_point_not_collinear_vertices_wlog_helper by fastforce
    moreover have "path_inside ?p2 \<subseteq> path_inside ?q"
      using 2 unfolding is_polygon_split_def
      by (smt (z3) One_nat_def UnCI append_Cons diff_Suc_1 drop0 drop_Suc_Cons make_triangle_def nth_Cons_0 nth_Cons_Suc numeral_3_eq_3 self_append_conv2 subsetI take0 take_Suc_Cons)
    moreover have "path_inside ?p1 \<subseteq> path_inside ?q"
      using 2 unfolding is_polygon_split_def
      by (smt (z3) One_nat_def Un_assoc append_Cons diff_Suc_1 drop0 drop_Suc_Cons inf_sup_absorb le_iff_inf make_triangle_def nth_Cons_0 nth_Cons_Suc numeral_3_eq_3 self_append_conv2 sup_commute take0 take_Suc_Cons)
    moreover have "path_inside ?q \<subseteq> path_inside p"
      using 1 unfolding is_polygon_split_path_def
      by (smt (z3) One_nat_def Un_subset_iff Un_upper1 append_Cons append_Nil assms(1) diff_zero drop0 drop_Suc_Cons make_triangle_def nth_Cons_0 nth_Cons_Suc take0)
    ultimately show ?thesis by blast
  qed
  moreover show "a \<notin> path_image ?p2 \<union> path_inside ?p2" using calculation by simp
  ultimately show "b \<notin> path_image ?p1 \<union> path_inside ?p1" by simp

  have "(path_image ?p3 - path_image ?cutpath) \<inter> (path_image ?q - path_image ?cutpath) = {}"
    using 1 unfolding make_triangle_def is_polygon_split_path_def
    by (smt (z3) One_nat_def append_Cons append_Nil diff_self_eq_0 diff_zero drop0 drop_Suc_Cons nth_Cons_0 nth_Cons_Suc rev_singleton_conv take_0)
  moreover have "c \<in> path_image ?q" using l_q_int by auto
  ultimately have "c \<notin> path_image ?p3" using c_noton_cutpath by blast
  moreover have "c \<notin> path_inside ?p3"
  proof-
    have "c \<notin> path_inside p"
      using assms(1) assms(2) triangle_interior_point_not_collinear_vertices by fastforce
    moreover have "path_inside ?p3 \<subseteq> path_inside p"
      using 1 unfolding is_polygon_split_path_def
      by (smt (z3) One_nat_def Un_assoc Un_upper1 append_Cons append_Nil assms(1) diff_Suc_Suc diff_zero make_triangle_def nth_Cons_0 nth_Cons_Suc rev_singleton_conv take0)
    ultimately show ?thesis by blast
  qed
  ultimately show "c \<notin> path_image ?p3 \<union> path_inside ?p3" by blast
qed

lemma smaller_triangle:
  assumes "\<not> collinear {a, b, c} \<and> \<not> collinear {a', b', c'}"
  assumes "p = make_triangle a b c"
  assumes "p' = make_triangle a' b' c'"
  assumes "path_inside p \<subseteq> path_inside p'"
  assumes "\<exists>d. integral_vec d \<and> d \<in> path_image p' \<union> path_inside p' \<and> d \<notin> path_image p \<union> path_inside p"
  shows "card (integral_inside p) + card (integral_boundary p) < card (integral_inside p') + card (integral_boundary p')"
proof-
  have "simple_path p" using assms unfolding make_triangle_def
    using assms(2) polygon_def triangle_is_polygon by presburger
  then have finite_p: "finite (integral_inside p) \<and> finite (integral_boundary p)" using assms unfolding make_triangle_def
    using integral_boundary integral_inside finite_integral_points_path_image finite_integral_points_path_inside by metis
  have "simple_path p'" using assms unfolding make_triangle_def
    using assms(3) polygon_def triangle_is_polygon by presburger
  then have finite_p': "finite (integral_inside p') \<and> finite (integral_boundary p')" using assms unfolding make_triangle_def
    using integral_boundary integral_inside finite_integral_points_path_image finite_integral_points_path_inside by metis

  have "polygon p" using assms(1,2) triangle_is_polygon by blast
  then have 1: "(integral_inside p) \<inter> (integral_boundary p) = {}"
    unfolding integral_inside integral_boundary using inside_outside_polygon unfolding inside_outside_def by blast

  have "polygon p'" using assms(1,3) triangle_is_polygon by blast
  then have 2: "(integral_inside p') \<inter> (integral_boundary p') = {}"
    unfolding integral_inside integral_boundary using inside_outside_polygon unfolding inside_outside_def by blast

  have path_image_subset: "path_image p \<subseteq> path_image p' \<union> path_inside p'"
  proof-
    have p_frontier: "path_image p = frontier (convex hull {a, b, c})"
      by (simp add: assms(1) assms(2) convex_polygon_frontier_is_path_image2 triangle_convex_hull triangle_is_convex triangle_is_polygon)
    have p'_frontier: "path_image p' = frontier (convex hull {a', b', c'})"
      by (simp add: assms(1) assms(3) convex_polygon_frontier_is_path_image2 triangle_convex_hull triangle_is_convex triangle_is_polygon)

    have p_interior: "path_inside p = interior (convex hull {a, b, c})"
      by (simp add: bounded_convex_hull p_frontier inside_frontier_eq_interior path_inside_def)
    have p'_interior: "path_inside p' = interior (convex hull {a', b', c'})"
      by (simp add: bounded_convex_hull p'_frontier inside_frontier_eq_interior path_inside_def)

    have "interior (convex hull {a, b, c}) \<subseteq> interior (convex hull {a', b', c'})"
      using assms p_interior p'_interior by argo
    moreover have "compact (convex hull {a, b, c}) \<and> compact (convex hull {a', b', c'})"
      by (simp add: compact_convex_hull)
    ultimately have "frontier (convex hull {a, b, c})
        \<subseteq> interior (convex hull {a', b', c'}) \<union> frontier (convex hull {a', b', c'})"
      by (smt (verit, ccfv_threshold) Jordan_inside_outside_real2 closed_path_def \<open>polygon p'\<close> \<open>polygon p\<close> assms(1) assms(2) closure_Un closure_Un_frontier closure_convex_hull finite.emptyI finite_imp_compact finite_insert p'_frontier p'_interior p_interior path_inside_def polygon_def subset_trans sup.absorb_iff1 sup_commute triangle_convex_hull)
    then show ?thesis using p'_frontier p'_interior p_frontier by blast
  qed

  have "card ((integral_inside p) \<union> (integral_boundary p)) = card (integral_inside p) + card (integral_boundary p)"
    using 1 finite_p by (simp add: card_Un_disjoint)
  moreover have "card ((integral_inside p') \<union> (integral_boundary p')) = card (integral_inside p') + card (integral_boundary p')"
    using 2 finite_p' by (simp add: card_Un_disjoint)
  moreover have "(integral_inside p) \<union> (integral_boundary p) \<subseteq> (integral_inside p') \<union> (integral_boundary p')"
    using assms path_image_subset unfolding integral_inside integral_boundary by blast
  moreover then have "(integral_inside p) \<union> (integral_boundary p) \<subset> (integral_inside p') \<union> (integral_boundary p')" using assms unfolding integral_inside integral_boundary by blast
  ultimately show ?thesis by (metis finite_Un finite_p' psubset_card_mono)
qed

lemma pick_elem_triangle:
  fixes p :: "R_to_R2"
  assumes p_triangle: "p = make_triangle a b c"
  assumes elem_triangle: "elem_triangle a b c" 
  assumes "I = card {x. integral_vec x \<and> x \<in> path_inside p}" and
          "B = card {x. integral_vec x \<and> x \<in> path_image p}"
  shows "measure lebesgue (path_inside p) = I + B/2 - 1"
proof - 
  have polygon_p: "polygon p"
    using p_triangle triangle_is_polygon elem_triangle
    unfolding elem_triangle_def by auto
  then have "path_inside p \<inter> path_image p = {}"
    using inside_outside_polygon[of p] unfolding inside_outside_def 
    by auto

  let ?p = "polygon (make_polygonal_path [a, b, c, a])"
  have a_neq_b:"a \<noteq> b"
    using elem_triangle unfolding elem_triangle_def
    by auto 
  have b_neq_c: "b \<noteq> c"
    using elem_triangle unfolding elem_triangle_def
    by auto
  have a_neq_c: "c \<noteq> a"
    using elem_triangle unfolding elem_triangle_def
    using collinear_3_eq_affine_dependent by blast 

  have "path_image p \<subseteq> convex hull {a, b, c}"
    using triangle_path_image_subset_convex p_triangle by auto
  then have
    "{x. integral_vec x \<and> x \<in> path_image p} \<subseteq> {x. integral_vec x \<and> x \<in> convex hull {a, b, c}}"
    by auto
  also have "... = {a, b, c}"
    using elem_triangle unfolding elem_triangle_def by auto
  finally have "{x. integral_vec x \<and> x \<in> path_image p} \<subseteq> {a, b, c}" .
  moreover have "{x. integral_vec x \<and> x \<in> path_image p} \<supseteq> {a, b, c}"
    
    by (smt (verit) Collect_mono_iff make_triangle_def \<open>{x. integral_vec x \<and> x \<in> convex hull {a, b, c}} = {a, b, c}\<close> empty_set insert_subset list.simps(15) mem_Collect_eq p_triangle subsetD vertices_on_path_image)
  ultimately have "{x. integral_vec x \<and> x \<in> path_image p} = {a, b, c}" by auto
  then have card_2: "B = 3"
    using a_neq_b b_neq_c a_neq_c assms(4)
    by simp

  have "{x. integral_vec x \<and> x \<in> path_inside p} = {}"
  proof-
    have "path_inside p \<subseteq> convex hull {a, b, c}"
      by (smt (verit, best) Diff_insert_absorb make_triangle_def convex_polygon_inside_is_convex_hull_interior empty_iff empty_set insert_Diff_single insert_commute interior_subset list.simps(15) p_triangle polygon_p elem_triangle elem_triangle_def triangle_is_convex)
    then have
      "{x. integral_vec x \<and> x \<in> path_inside p} \<subseteq> {x. integral_vec x \<and> x \<in> convex hull {a, b, c}}"
      by auto
    also have "... = {a, b, c}"
      using \<open>{x. integral_vec x \<and> x \<in> convex hull {a, b, c}} = {a, b, c}\<close> by auto
    finally have "{x. integral_vec x \<and> x \<in> path_inside p} \<subseteq> {a, b, c}" .
    moreover have
      "{x. integral_vec x \<and> x \<in> path_inside p} \<inter> {x. integral_vec x \<and> x \<in> path_image p} = {}"
      using \<open>path_inside p \<inter> path_image p = {}\<close> by auto
    ultimately show ?thesis
      using \<open>{x. integral_vec x \<and> x \<in> path_image p} = {a, b, c}\<close> by auto
  qed
  then have card_1: "I = 0"
    using assms(3) 
    by (metis card.empty)

  have "I + B/2 - 1 = 1/2"
    using card_1 card_2 assms
    by auto
  then show ?thesis
    using elem_triangle_area_is_half[OF assms(2)] triangle_measure_convex_hull_measure_path_inside_same[OF assms(1) assms(2)]
    by auto
qed

lemma pick_triangle_lemma:
  fixes p :: "R_to_R2"
  assumes "p = make_triangle a b c" and "all_integral [a, b, c]" and "distinct [a, b, c]" and "\<not> collinear {a, b, c}"
          "I = card {x. integral_vec x \<and> x \<in> path_inside p}" and
          "B = card {x. integral_vec x \<and> x \<in> path_image p}"
  shows "measure lebesgue (path_inside p) = I + B/2 - 1"
  using assms
proof(induction "card {x. integral_vec x \<and> x \<in> path_inside p} + card {x. integral_vec x \<and> x \<in> path_image p}" arbitrary: p a b c I B rule:less_induct)
  case less
  have polygon_p: "polygon p" using triangle_is_polygon[OF less.prems(4)] less.prems(1) by simp
  then have polygon_of: "polygon_of p [a, b, c, a]"
    unfolding polygon_of_def using less.prems(1) unfolding make_triangle_def by auto
 (* One case where I is nonempty *)
  have convex_hull_char: "convex hull {a, b, c} = path_inside p \<union> path_image p"
    using triangle_convex_hull[OF less.prems(1) less.prems(4)] by auto
  then have interior_convex_hull: "{x. integral_vec x \<and> x \<in> path_inside p} \<union> {x. integral_vec x \<and> x \<in> path_image p} = {x \<in> convex hull {a, b, c}. integral_vec x}"
    by auto
  have vts_in_path_image: "a \<in> path_image p \<and> b \<in> path_image p \<and>  c \<in> path_image p"
    using assms(1) unfolding make_triangle_def using vertices_on_path_image 
    by (metis (mono_tags, lifting) insertCI less.prems(1) list.simps(15) make_triangle_def subset_code(1))
  have integral_vts: "integral_vec a \<and> integral_vec b \<and> integral_vec c"
    using less.prems(2)
    by (simp add: all_integral_def) 
  then have subset: "{a, b, c} \<subseteq> {x. integral_vec x \<and> x \<in> path_image p}"
    using vts_in_path_image integral_vts by simp
  have finite_integral_on_path_im: "finite {x. integral_vec x \<and> x \<in> path_image p}" 
    using finite_integral_points_path_image triangle_is_polygon[OF less.prems(4)]
    unfolding make_triangle_def polygon_def 
    using less.prems(1) make_triangle_def by auto
  have B_3_if: "B > 3" if other_point_in_set: "{x. integral_vec x \<and> x \<in> path_image p} \<noteq> {a, b, c}"
  proof -
    have "\<exists>d. d \<notin> {a, b, c} \<and> d \<in> {x. integral_vec x \<and> x \<in> path_image p}"
      using other_point_in_set subset 
      by blast
    then obtain d where d_prop: "d \<notin> {a, b, c} \<and> d \<in> {x. integral_vec x \<and> x \<in> path_image p}"
      by auto
    then have subset2: "{a, b, c, d} \<subseteq>{x. integral_vec x \<and> x \<in> path_image p}"
      using d_prop subset by auto
    have "distinct [a, b, c, d]"
      using d_prop
      using less.prems(3) by auto 
    then have card_is: "card {a, b, c, d} = 4"
      by simp
    show ?thesis using subset2 card_is finite_integral_on_path_im
      by (metis (no_types, lifting) Suc_le_eq card_mono eval_nat_numeral(2) less.prems(6) semiring_norm(26) semiring_norm(27))
  qed
  { assume *: "I = 0"
    have "finite {x. integral_vec x \<and> x \<in> path_inside p}"
      using finite_integral_points_path_inside triangle_is_polygon[OF less.prems(4)]
      unfolding make_triangle_def
      by (simp add: less.prems(1) make_triangle_def polygon_def)
    then have empty_inside: "{x. integral_vec x \<and> x \<in> path_inside p} = {}"
      using * less.prems(5) by auto

    (* First, use pick_elem_triangle in the case where I is empty and B only contains the vertices *)
    { assume **: "B = 3"
      have "{x \<in> convex hull {a, b, c}. integral_vec x} = {a, b, c}"
        using * ** less.prems(5-6) B_3_if interior_convex_hull empty_inside 
        by blast
      then have "elem_triangle a b c"
        unfolding elem_triangle_def using less.prems(4) integral_vts by simp
      then have "measure lebesgue (path_inside p) = I + B/2 - 1"
        using pick_elem_triangle less.prems by auto
    } (* In the next case, there is an integral vertex on one of the line segments of the triangle *)
    moreover
    { assume *: "B > 3"
      then obtain d where d: "integral_vec d \<and> d \<in> path_image p \<and> d \<notin> {a, b, c}"
        by (smt (verit, del_insts) subset finite_integral_on_path_im less.prems(3) card_3_iff collinear_3_eq_affine_dependent less.prems(4) less.prems(6) less_not_refl mem_Collect_eq subsetI subset_antisym)
      have "path_image (make_polygonal_path [a, b, c, a]) = path_image (linepath a b) \<union>  path_image (linepath b c) \<union>  path_image (linepath c a)"
        by (metis (no_types, lifting) list.discI make_polygonal_path.simps(3) nth_Cons_0 path_image_cons_union sup_assoc)
      then have "d \<in> path_image (linepath a b)
          \<or> d \<in> path_image (linepath b c)
          \<or> d \<in> path_image (linepath c a)"
        using d less.prems(1) unfolding make_triangle_def polygon_of_def 
        by blast
      then have "measure lebesgue (path_inside p) = I + B/2 - 1"
        using pick_triangle_helper less.prems less.hyps empty_inside d
        unfolding pick_holds pick_triangle integral_inside integral_boundary
        apply simp by blast
    }
    ultimately have "measure lebesgue (path_inside p) = I + B/2 - 1"
      using B_3_if 
      by (metis (no_types, lifting) card.empty card_insert_disjoint collinear_2 finite.emptyI finite.insertI insert_absorb less.prems(4) less.prems(6) numeral_3_eq_3)
  } (* In the last case, there is an integral vertex inside the triangle *)
  moreover
  { assume *: "I > 0" 
    then obtain d where d_inside: "integral_vec d \<and> d \<in> path_inside p"
      using less.prems(5) 
      by (metis (mono_tags, lifting) Collect_empty_eq add_0 canonically_ordered_monoid_add_class.lessE card_0_eq card_ge_0_finite)
    have "a \<in> path_image p"
      using vertices_on_path_image polygon_of unfolding polygon_of_def by fastforce
    then have a_inset: "a \<in> path_inside p \<union> path_image p" 
      by fastforce
    have convex_hull_set: "convex hull set [a, b, c, a] = path_inside p \<union> path_image p"
      using convex_hull_char 
      by (simp add: insert_commute)
    then have ad_linepath_inside: "path_image (linepath a d) \<subseteq> path_inside p \<union> path_image p"
      using d_inside convex_polygon_means_linepaths_inside[OF polygon_of convex_hull_set a_inset]
      by blast
    have "b \<in> path_image p"
      using vertices_on_path_image polygon_of unfolding polygon_of_def by fastforce
    then have b_inset: "b \<in> path_inside p \<union> path_image p" 
      by fastforce
    have bd_linepath_inside: "path_image (linepath b d) \<subseteq> path_inside p \<union> path_image p"
      using d_inside convex_polygon_means_linepaths_inside[OF polygon_of convex_hull_set b_inset]
      by blast
    have "c \<in> path_image p"
      using vertices_on_path_image polygon_of unfolding polygon_of_def by fastforce
    then have c_inset: "c \<in> path_inside p \<union> path_image p" 
      by fastforce
    then have cd_linepath_inside: "path_image (linepath c d) \<subseteq> path_inside p \<union> path_image p"
      using d_inside convex_hull_char convex_polygon_means_linepaths_inside[OF polygon_of convex_hull_set c_inset]
      by blast

    let ?p1 = "make_triangle a d c"
    let ?p2 = "make_triangle d b c"
    let ?p3 = "make_triangle a b d"

    have triangle_split:
        "is_polygon_split_path [a, b, c] 0 1 [d]"
        "is_polygon_split [a, d, b, c] 1 3"
        "a \<notin> path_image ?p2 \<union> path_inside ?p2"
        "b \<notin> path_image ?p1 \<union> path_inside ?p1"
        "c \<notin> path_image ?p3 \<union> path_inside ?p3"
      using triangle_3_split[of p a b c d] less.prems d_inside polygon_p apply fastforce
      using triangle_3_split[of p a b c d] less.prems d_inside polygon_p apply fastforce
      using triangle_3_split[of p a b c d] less.prems d_inside polygon_p apply fastforce
      using triangle_3_split[of p a b c d] less.prems d_inside polygon_p apply fastforce
      using triangle_3_split[of p a b c d] less.prems d_inside polygon_p by fastforce

    let ?q = "make_polygonal_path [a, d, b, c, a]"
    let ?I1 = "card (integral_inside ?p1)"
    let ?B1 = "card (integral_boundary ?p1)"
    let ?I2 = "card (integral_inside ?p2)"
    let ?B2 = "card (integral_boundary ?p2)"
    let ?I3 = "card (integral_inside ?p3)"
    let ?B3 = "card (integral_boundary ?p3)"
    let ?Iq = "card (integral_inside ?q)"
    let ?Bq = "card (integral_boundary ?q)"
    have "measure lebesgue (path_inside ?p1) = ?I1 + ?B1/2 - 1"
    proof-
      have "path_inside ?p1 \<subseteq> path_inside ?q"
        using triangle_split(2) unfolding is_polygon_split_def
        by (smt (z3) One_nat_def Un_assoc Un_upper1 append_Cons append_Nil diff_Suc_Suc diff_zero drop0 drop_Suc_Cons make_triangle_def nth_Cons_0 nth_Cons_Suc numeral_3_eq_3 sup_commute take0 take_Suc_Cons)
      moreover have "path_inside ?q \<subseteq> path_inside p"
        using triangle_split(1) unfolding is_polygon_split_path_def
        by (smt (z3) One_nat_def Un_assoc Un_subset_iff append_Cons append_Nil diff_zero drop0 drop_Suc_Cons less.prems(1) make_triangle_def nth_Cons_0 nth_Cons_Suc sup.cobounded2 take0)
      ultimately have "path_inside ?p1 \<subseteq> path_inside p" by blast
      moreover have "\<not> collinear {a, d, c}"
        by (metis d_inside insert_commute less.prems(1) polygon_p triangle_interior_point_not_collinear_vertices)
      moreover have "\<not> collinear {a, b, c}" by (simp add: less.prems(4))
      moreover have "integral_vec b"
        using integral_vts by blast
      moreover have "b \<in> path_image p"
        using vts_in_path_image by auto
      ultimately have "card (integral_inside ?p1) + card (integral_boundary ?p1) < card (integral_inside p) + card (integral_boundary p)"
        using smaller_triangle[of a d c a b c ?p1 p] triangle_split(4) less.prems(1) less_imp_le_nat
        by blast
      thus ?thesis
        using less.hyps[of ?p1 a d c] unfolding integral_inside integral_boundary
        using \<open>\<not> collinear {a, d, c}\<close> all_integral_def d_inside integral_vts less.prems(1) less.prems(3) triangle_split(3) triangle_split(5)
        by fastforce
    qed
    moreover have "measure lebesgue (path_inside ?p2) = ?I2 + ?B2/2 - 1"
    proof-
      have "path_inside ?p2 \<subseteq> path_inside ?q"
        using triangle_split(2) unfolding is_polygon_split_def
        by (smt (z3) One_nat_def Un_assoc Un_upper1 append_Cons append_Nil diff_Suc_Suc diff_zero drop0 drop_Suc_Cons make_triangle_def nth_Cons_0 nth_Cons_Suc numeral_3_eq_3 sup_commute take0 take_Suc_Cons)
      moreover have "path_inside ?q \<subseteq> path_inside p"
        using triangle_split(1) unfolding is_polygon_split_path_def
        by (smt (z3) One_nat_def Un_assoc Un_subset_iff append_Cons append_Nil diff_zero drop0 drop_Suc_Cons less.prems(1) make_triangle_def nth_Cons_0 nth_Cons_Suc sup.cobounded2 take0)
      ultimately have "path_inside ?p2 \<subseteq> path_inside p" by blast
      moreover have "\<not> collinear {d, b, c}"
        by (metis d_inside insert_commute less.prems(1) polygon_p triangle_interior_point_not_collinear_vertices)
      moreover have "\<not> collinear {a, b, c}" by (simp add: less.prems(4))
      moreover have "integral_vec a"
        using integral_vts by blast
      moreover have "a \<in> path_image p"
        using vts_in_path_image by auto
      ultimately have "card (integral_inside ?p2) + card (integral_boundary ?p2) < card (integral_inside p) + card (integral_boundary p)"
        using smaller_triangle[of d b c a b c ?p2 p] triangle_split(3) less.prems(1) less_imp_le_nat
        by blast
      thus ?thesis
        using less.hyps[of ?p2 d b c] unfolding integral_inside integral_boundary
        using \<open>\<not> collinear {d, b, c}\<close> all_integral_def d_inside integral_vts less.prems(1) less.prems(3) triangle_split(3) triangle_split(5)
        by fastforce
    qed
    moreover have "measure lebesgue (path_inside ?p3) = ?I3 + ?B3/2 - 1"
    proof-
      have "path_inside ?p3 \<subseteq> path_inside p"
        using triangle_split(1) unfolding is_polygon_split_path_def
        by (smt (z3) One_nat_def Un_assoc Un_upper1 append_Cons append_Nil diff_Suc_Suc diff_zero less.prems(1) make_triangle_def nth_Cons_0 nth_Cons_Suc rev_singleton_conv take0)
      moreover have "\<not> collinear {a, b, d}"
        by (metis d_inside less.prems(1) polygon_p triangle_interior_point_not_collinear_vertices)
      moreover have "\<not> collinear {a, b, c}" by (simp add: less.prems(4))
      moreover have "integral_vec c"
        using integral_vts by blast
      moreover have "c \<in> path_image p"
        using vts_in_path_image by auto
      ultimately have "card (integral_inside ?p3) + card (integral_boundary ?p3) < card (integral_inside p) + card (integral_boundary p)"
        using smaller_triangle[of a b d a b c ?p3 p] triangle_split(5) less.prems(1) less_imp_le_nat
        by blast
      thus ?thesis
        using less.hyps[of ?p3 a b d] unfolding integral_inside integral_boundary
        using \<open>\<not> collinear {a, b, d}\<close> all_integral_def d_inside integral_vts less.prems(1) less.prems(3) triangle_split(3) triangle_split(5)
        by fastforce
    qed
    moreover have "measure lebesgue (path_inside ?q) = ?Iq + ?Bq/2 - 1"
      using pick_split_union[OF triangle_split(2),
          of "[a]" "[b]" "[]" d c ?q ?p2 ?p1 ?I2 ?B2 ?I1 ?B1 ?Iq ?Bq]
      using calculation
      unfolding integral_inside integral_boundary make_triangle_def
      using all_integral_def d_inside less.prems(2) by force
    ultimately have ?case
      using pick_split_path_union[OF triangle_split(1),
          of "[]" "[]" "[c]" a b "make_polygonal_path (a # [d] @ [b])" p ?p3 ?q ?I3 ?B3 ?Iq ?Bq I B]
      unfolding integral_inside integral_boundary make_triangle_def less.prems
      using less.prems(2) by force
  }
  ultimately show ?case by blast
qed

subsection "Pocket properties"

definition index_not_in_set :: "(real^2) list \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow> bool"
  where "index_not_in_set vts A i \<longleftrightarrow> i \<in> {i. i < length vts \<and> vts ! i \<notin> A}"

definition min_index_not_in_set:: "(real^2) list \<Rightarrow> (real^2) set \<Rightarrow> nat"
  where "min_index_not_in_set vts A = (LEAST i. index_not_in_set vts A i)"

definition nonzero_index_in_set :: "(real^2) list \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "nonzero_index_in_set vts A i \<longleftrightarrow> i \<in> {i. 0 < i \<and> i < length vts \<and> vts ! i \<in> A}"

definition min_nonzero_index_in_set :: "(real^2) list \<Rightarrow> (real^2) set \<Rightarrow> nat" where
  "min_nonzero_index_in_set vts A = (LEAST i. nonzero_index_in_set vts A i)"

(* NOTE: Requires rotation: enforce that vts!0 is in convex_hull_vts,
  since the pocket can "loop around" the end of the polygon vts list
*)
definition construct_pocket_0 :: "(real^2) list \<Rightarrow> (real^2) set \<Rightarrow> (real^2) list" where
  "construct_pocket_0 vts A = take ((min_nonzero_index_in_set vts A) + 1) vts"

definition is_pocket_0 :: "(real^2) list \<Rightarrow> (real^2) list \<Rightarrow> bool" where
  "is_pocket_0 vts vts' \<longleftrightarrow>
      polygon (make_polygonal_path vts)
      \<and> (\<exists>i. vts' = take i vts)
      \<and> 3 \<le> length vts' \<and> length vts' < length vts
      \<and> hd vts' \<in> frontier (convex hull (set vts)) \<and> last vts' \<in> frontier (convex hull (set vts))
      \<and> set (tl (butlast vts')) \<subseteq> interior (convex hull (set vts))"

(* i is the length of the pocket path *)
definition fill_pocket_0 :: "(real^2) list \<Rightarrow> nat \<Rightarrow> (real^2) list" where
  "fill_pocket_0 vts i = (hd vts) # (drop (i-1) vts)"

lemma min_nonzero_index_in_set_exists:
  assumes "set (tl vts) \<inter> A \<noteq> {}"
  shows "\<exists>i. nonzero_index_in_set vts A i"
proof-
  obtain v where v: "v \<in> A \<inter> set (tl vts)" using assms by blast
  then obtain i where "(tl vts)!i = v \<and> i < length (tl vts)" by (meson IntD2 in_set_conv_nth)
  then obtain j where "vts!j = v \<and> 0 < j \<and> j < length vts" using nth_tl by fastforce
  thus ?thesis unfolding nonzero_index_in_set_def using v by blast
qed

lemma min_nonzero_index_in_set_defined:
  assumes "set (tl vts) \<inter> A \<noteq> {}"
  defines "i \<equiv> min_nonzero_index_in_set vts A"
  shows "nonzero_index_in_set vts A i \<and> (\<forall>j < i. \<not> nonzero_index_in_set vts A j)"
proof-
  have "\<exists>i. nonzero_index_in_set vts A i" using assms min_nonzero_index_in_set_exists by blast
  then have "nonzero_index_in_set vts A i"
    using assms unfolding min_nonzero_index_in_set_def
    using LeastI_ex by blast
  moreover have "(\<forall>j < i. \<not> nonzero_index_in_set vts A j)"
    by (metis assms(2) wellorder_Least_lemma(2) leD min_nonzero_index_in_set_def)
  ultimately show ?thesis by blast
qed

lemma min_index_not_in_set_exists:
  assumes "set vts \<supset> A"
  shows "\<exists>i. index_not_in_set vts A i"
proof-
  obtain v where "v \<in> set vts \<and> v \<notin> A" using assms by blast
  then obtain i where "i < length vts \<and> vts ! i \<notin> A" by (metis in_set_conv_nth)
  thus ?thesis unfolding index_not_in_set_def by blast
qed

lemma min_index_not_in_set_defined:
  assumes "set vts \<supset> A"
  defines "i \<equiv> min_index_not_in_set vts A"
  shows "index_not_in_set vts A i \<and> (\<forall>j < i. \<not> index_not_in_set vts A j)"
proof-
  have "\<exists>i. index_not_in_set vts A i" using assms min_index_not_in_set_exists by simp
  then have "index_not_in_set vts A i"
    using assms unfolding min_index_not_in_set_def
    using LeastI_ex by blast
  moreover have "(\<forall>j < i. \<not> index_not_in_set vts A j)"
    by (metis assms(2) wellorder_Least_lemma(2) leD min_index_not_in_set_def)
  ultimately show ?thesis by blast
qed

lemma min_nonzero_index_in_set_bound:
  assumes "set (tl vts) \<inter> A \<noteq> {}"
  shows "min_nonzero_index_in_set vts A < length vts"
  using min_nonzero_index_in_set_defined assms unfolding nonzero_index_in_set_def by blast

lemma construct_pocket_0_subset_vts:
  assumes "set (tl vts) \<inter> A \<noteq> {}"
  shows "set (construct_pocket_0 vts A) \<subseteq> set vts"
proof-
  let ?i = "min_nonzero_index_in_set vts A"
  have "nonzero_index_in_set vts A ?i" using min_nonzero_index_in_set_defined assms by presburger
  then have "?i < length vts" unfolding nonzero_index_in_set_def by blast
  thus ?thesis unfolding construct_pocket_0_def by (simp add: set_take_subset)
qed

lemma min_index_not_in_set_0:
  assumes "set vts \<supset> A"
  assumes "vts!0 \<in> A"
  defines "i \<equiv> min_index_not_in_set vts A"
  defines "r \<equiv> i - 1"
  shows "vts!r \<in> A"
proof-
  have *: "index_not_in_set vts A i \<and> (\<forall>j<i. \<not> index_not_in_set vts A j)"
    using min_index_not_in_set_defined[of A vts, OF assms(1)] unfolding i_def by blast
  moreover then have "r < i"
    unfolding r_def i_def min_index_not_in_set_def index_not_in_set_def
    by (metis (no_types, lifting) assms(2) bot_nat_0.not_eq_extremum diff_less mem_Collect_eq zero_less_one)
  ultimately have "\<not> index_not_in_set vts A r" by blast
  thus ?thesis
    unfolding index_not_in_set_def using assms * index_not_in_set_def less_imp_diff_less by force
qed

lemma construct_pocket_0_last_in_set:
  assumes "set (tl vts) \<inter> A \<noteq> {}"
  assumes "vts!0 \<in> A"
  defines "p \<equiv> construct_pocket_0 vts A"
  shows "last p \<in> A"
proof-
  let ?i = "min_nonzero_index_in_set vts A"
  have *: "nonzero_index_in_set vts A ?i" using assms(1) min_nonzero_index_in_set_defined by blast
  then have "length p = min_nonzero_index_in_set vts A + 1"
    unfolding p_def construct_pocket_0_def nonzero_index_in_set_def by simp
  then have "last p = p!?i"
    by (metis add_diff_cancel_right' last_conv_nth length_0_conv zero_eq_add_iff_both_eq_0 zero_neq_one)
  also have "... = vts!?i"
    unfolding p_def construct_pocket_0_def by simp
  also have "... \<in> A" using * unfolding nonzero_index_in_set_def by force
  finally show ?thesis .
qed

lemma construct_pocket_0_first_last_distinct:
  assumes "card A \<ge> 2"
  assumes "A \<subseteq> set vts"
  assumes "distinct (butlast vts)"
  assumes "hd vts = last vts"
  shows "hd (construct_pocket_0 vts A) \<noteq> last (construct_pocket_0 vts A)"
proof-
  let ?n = "min_nonzero_index_in_set vts A"
  have "set (tl vts) \<inter> A \<noteq> {}"
    by (metis (no_types, lifting) Diff_cancel Int_commute Int_insert_right_if1 Nat.le_diff_conv2 Suc_1 add_leD1 assms(1) assms(2) card.empty card_Diff_singleton inf.orderE list.collapse list.sel(2) list.set(2) not_one_le_zero plus_1_eq_Suc subset_insert)
  then have n_defined: "nonzero_index_in_set vts A ?n \<and> (\<forall>j < ?n. \<not> nonzero_index_in_set vts A j)"
    using min_nonzero_index_in_set_defined by presburger
  obtain a b where ab: "a \<noteq> b \<and> {a, b} \<subseteq> A" by (metis assms(1) card_2_iff ex_card)
  then obtain i j where ij: "vts!i = a \<and> vts!j = b \<and> i < length vts \<and> j < length vts \<and> i \<noteq> j"
    by (metis (no_types, opaque_lifting) assms(2) in_set_conv_nth insert_subset subsetD)

  have ?thesis if *: "?n < length vts - 1"
  proof-
    have "?n > 0" using n_defined unfolding nonzero_index_in_set_def by blast
    then have n_bound': "?n > 0 \<and> ?n < length (butlast vts)" using * by fastforce
    then have "hd vts \<noteq> vts!?n"
      by (metis assms(3) distinct_Ex1 hd_conv_nth ij in_set_conv_nth length_0_conv length_pos_if_in_set less_nat_zero_code nth_butlast)
    moreover then have "vts!?n \<noteq> last vts" using assms(4) by simp
    moreover have "last (construct_pocket_0 vts A) = vts!?n"
      using n_defined
      unfolding construct_pocket_0_def
      by (metis Cons_nth_drop_Suc Suc_eq_plus1 n_bound' * last_snoc less_diff_conv list.sel(1) nth_butlast take_butlast take_hd_drop)
    moreover have "hd (construct_pocket_0 vts A) = hd vts"
      unfolding construct_pocket_0_def by force
    ultimately show ?thesis by presburger
  qed
  moreover have ?thesis if *: "?n = length vts - 1"
  proof-
    have "{i, j} \<subseteq> {i. i < length vts \<and> vts ! i \<in> A}" using ij ab by simp
    moreover have "i \<noteq> 0 \<or> j \<noteq> 0" using ij by argo
    ultimately have "nonzero_index_in_set vts A i \<or> nonzero_index_in_set vts A j"
      unfolding nonzero_index_in_set_def by simp
    then have "?n = i \<or> ?n = j"
      by (metis n_defined Suc_diff_1 gr_implies_not_zero ij linorder_cases not_less_eq *)
    moreover then have "last (construct_pocket_0 vts A) = vts!?n"
      by (metis Suc_eq_plus1 construct_pocket_0_def hd_drop_conv_nth ij snoc_eq_iff_butlast take_hd_drop)
    ultimately show ?thesis
      by (metis (no_types, lifting) ij ab Suc_eq_plus1 assms(4) bot_nat_0.not_eq_extremum hd_conv_nth insert_subset last_conv_nth less_diff_conv list.size(3) mem_Collect_eq n_defined nat_neq_iff nonzero_index_in_set_def not_less_eq that)
  qed
  ultimately show ?thesis using n_defined unfolding nonzero_index_in_set_def by fastforce
qed

lemma construct_pocket_is_pocket:
  assumes "polygon (make_polygonal_path vts)"
  assumes "vts!0 \<in> frontier (convex hull (set vts))"
  assumes "vts!1 \<notin> frontier (convex hull (set vts))"
  shows "is_pocket_0 vts (construct_pocket_0 vts (set vts \<inter> frontier (convex hull (set vts))))"
proof-
  let ?vts' = "construct_pocket_0 vts (set vts \<inter> frontier (convex hull (set vts)))"
  have ex_i: "\<exists>i. ?vts' = take i vts" unfolding construct_pocket_0_def by blast
  moreover have "3 \<le> length ?vts'" (* smt call may take a second or two to terminate *)
    by (smt (verit) Cons_nth_drop_Suc IntI Int_iff One_nat_def Suc_1 Suc_diff_Suc Suc_lessI add_diff_cancel_right' add_gr_0 append_Nil2 assms(1) assms(2) assms(3) butlast.simps(1) butlast.simps(2) butlast_conv_take calculation cancel_comm_monoid_add_class.diff_cancel card.empty construct_pocket_0_def construct_pocket_0_first_last_distinct construct_pocket_0_last_in_set convex_hull_two_vts_on_frontier diff_diff_cancel diff_is_0_eq diff_is_0_eq' drop0 empty_iff empty_set have_wraparound_vertex hd_conv_nth hd_drop_conv_nth hd_take id_take_nth_drop last.simps last_conv_nth last_drop last_in_set last_snoc leI le_add2 le_numeral_extra(4) le_trans length_0_conv length_greater_0_conv length_take length_tl length_upt less_2_cases less_numeral_extra(1) less_numeral_extra(3) linorder_not_less list.distinct(1) list.sel(2) list.sel(3) list.size(3) min.absorb4 not_gr_zero not_less_eq_eq not_numeral_le_zero nth_mem numeral_3_eq_3 plus_1_eq_Suc polygon_at_least_3_vertices polygon_at_least_3_vertices_wraparound polygon_def pos2 rev.simps(1) self_append_conv2 simple_polygonal_path_vts_distinct snoc_eq_iff_butlast subset_iff take_all_iff take_eq_Nil take_hd_drop)
  moreover have vts'_length: "length ?vts' < length vts"
    by (metis (no_types, lifting) One_nat_def Suc_1 assms(1) calculation(1) calculation(2) construct_pocket_0_first_last_distinct convex_hull_two_vts_on_frontier have_wraparound_vertex hd_conv_nth inf_le1 last_snoc leI le_add2 le_trans length_take min.absorb4 not_numeral_le_zero numeral_3_eq_3 plus_1_eq_Suc polygon_at_least_3_vertices polygon_def simple_polygonal_path_vts_distinct take_all_iff take_eq_Nil)
  moreover have "hd ?vts' \<in> frontier (convex hull (set vts))"
    by (metis assms(2) bot_nat_0.not_eq_extremum calculation(1) calculation(2) hd_conv_nth hd_take list.size(3) not_numeral_le_zero take_eq_Nil)
  moreover have "last ?vts' \<in> frontier (convex hull (set vts))"
    by (smt (verit, ccfv_SIG) Cons_nth_drop_Suc Int_iff assms(1) assms(2) card_length construct_pocket_0_last_in_set drop0 drop_eq_Nil empty_iff have_wraparound_vertex last_drop last_in_set le_add2 le_trans linorder_not_less list.sel(3) list.simps(15) not_less_eq_eq numeral_3_eq_3 plus_1_eq_Suc polygon_at_least_3_vertices snoc_eq_iff_butlast)
  moreover have "set (tl (butlast ?vts')) \<subseteq> interior (convex hull (set vts))"
  proof-
    let ?A = "(set vts \<inter> frontier (convex hull (set vts)))"
    let ?r = "min_nonzero_index_in_set vts ?A"
    have "nonzero_index_in_set vts ?A ?r
        \<and> (\<forall>j<min_nonzero_index_in_set vts ?A. \<not> nonzero_index_in_set vts ?A j)"
      by (metis min_nonzero_index_in_set_defined IntI Nitpick.size_list_simp(2) One_nat_def add_leD1 assms(1) assms(2) calculation(2) calculation(3) empty_iff empty_set have_wraparound_vertex last_in_set last_snoc last_tl less_one not_one_le_zero nth_mem numeral_3_eq_3 plus_1_eq_Suc)
    then have "\<forall>i. (0 < i \<and> i < ?r) \<longrightarrow> vts!i \<notin> ?A" unfolding nonzero_index_in_set_def by force
    then have "\<forall>i. (0 < i \<and> i < ?r) \<longrightarrow> vts!i \<notin> frontier (convex hull (set vts))"
      using calculation(3) construct_pocket_0_def by fastforce
    then have "\<forall>i. (0 < i \<and> i < ?r) \<longrightarrow> vts!i \<in> interior (convex hull (set vts))"
      by (smt (verit, ccfv_threshold) Cons_nth_drop_Suc DiffI IntI One_nat_def add_leD1 assms(1) assms(2) calculation(2) calculation(3) closure_subset drop0 dual_order.strict_trans2 empty_iff frontier_def have_wraparound_vertex hull_subset inf.strict_coboundedI2 inf.strict_order_iff last_drop last_in_set last_snoc length_greater_0_conv list.discI list.sel(3) min_nonzero_index_in_set_bound nth_mem numeral_3_eq_3 plus_1_eq_Suc subset_eq)
    moreover have "tl (butlast ?vts') = drop 1 (take ?r vts)"
      unfolding construct_pocket_0_def
      by (metis One_nat_def add_implies_diff antisym_conv2 butlast_take construct_pocket_0_def drop_0 drop_Suc linorder_le_cases take_all vts'_length)
    moreover have "\<forall>v \<in> set (drop 1 (take ?r vts)). \<exists>i. 0 < i \<and> i < ?r \<and> vts!i = v"
    proof
      fix v assume *: "v \<in> set (drop 1 (take ?r vts))"
      then obtain i' where i': "(drop 1 (take ?r vts))!i' = v \<and> i' < ?r - 1"
        by (smt (z3) Cons_nth_drop_Suc One_nat_def ex_i butlast_conv_take calculation(2) drop0 hd_conv_nth hd_take index_less_size_conv length_drop length_take less_imp_le_nat linorder_not_less list.collapse list.sel(2) min.absorb4 nth_index take_all_iff take_eq_Nil vts'_length)
      then have "(take ?r vts)!(i' + 1) = v"
        by (metis * add.commute drop_eq_Nil empty_iff empty_set nle_le nth_drop)
      thus "\<exists>i. 0 < i \<and> i < ?r \<and> vts!i = v"
        by (metis add_gr_0 i' less_diff_conv nth_take zero_less_one)
    qed
    ultimately show ?thesis by fastforce
  qed
  ultimately show ?thesis unfolding is_pocket_0_def using assms(1) by argo
qed


lemma exists_point_above_interior:
  fixes a :: "real^2"
  assumes "a \<in> interior (convex hull S)"
  obtains x where "x \<in> S \<and> x$2 > a$2"
proof-
  have False if "\<forall>x \<in> S. x$2 \<le> a$2"
  proof-
    have "S \<subseteq> {x. x \<bullet> (vector [0, 1]) \<le> a$2}"
    proof(rule subsetI)
      fix x
      assume "x \<in> S"
      then have "x$2 \<le> a$2" using that by blast
      moreover have "x \<bullet> (vector [0, 1]) = x$1 * 0 + x$2 * 1"
        by (simp add: cart_eq_inner_axis e1e2_basis(3))
      ultimately show "x \<in> {x. x \<bullet> (vector [0, 1]) \<le> a$2}" by simp
    qed
    then have *: "convex hull S \<subseteq> {x. x \<bullet> (vector [0, 1]) \<le> a$2}"
    proof- (* sledgehammer-generated *)
      have "S \<subseteq> {v. vector [0, 1] \<bullet> v \<le> a $ 2}"
        by (simp add: \<open>S \<subseteq> {x. x \<bullet> vector [0, 1] \<le> a $ 2}\<close> inner_commute)
      then have "convex hull S \<subseteq> {v. vector [0, 1] \<bullet> v \<le> a $ 2}"
        by (simp add: convex_halfspace_le hull_minimal)
      then show ?thesis
        by (simp add: inner_commute)
    qed
    moreover have "a \<bullet> (vector [0, 1]) = a$2" by (simp add: cart_eq_inner_axis e1e2_basis(3))
    moreover have "frontier {x. x \<bullet> ((vector [0, 1])::(real^2)) \<le> a$2}
        = {x. x \<bullet> (vector [0, 1]) = a$2}"
      using frontier_halfspace_le[of "(vector [0, 1])::(real^2)" "a$2"]
      by (smt (verit) Collect_cong inner_commute vector_2(2) zero_index)
    ultimately have "a \<in> frontier {x. x \<bullet> (vector [0, 1]) \<le> a$2}" by blast
    thus False
      by (metis (mono_tags, lifting) Diff_iff * assms frontier_def in_frontier_in_subset in_mono interior_subset)
  qed
  thus ?thesis using that by fastforce
qed

lemma exists_point_above_convex_hull_interior:
  fixes S :: "(real^2) set"
  assumes "S \<noteq> {}"
  assumes "compact S"
  obtains x where "x \<in> S - (interior (convex hull S)) \<and> (\<forall>y \<in> interior (convex hull S). x$2 > y$2)"
proof-
  let ?H = "convex hull S"
  let ?e2 = "(vector [0, 1])::(real^2)"
  let ?f = "(\<lambda>x. x$2)::(real^2 \<Rightarrow> real)"
  have "continuous_on {x. True} ?f" by (simp add: continuous_on_component)
  moreover have "compact (convex hull S)" using assms(2) compact_convex_hull by blast
  moreover from calculation have "compact (?f`?H)"
    using compact_continuous_image continuous_on_subset by blast
  ultimately obtain x max where x: "x \<in> ?H \<and> ?f x = max \<and> (\<forall>y \<in> ?H. y$2 \<le> max)"
    by (smt (verit) Collect_mono assms(1) convex_hull_eq_empty convex_hull_explicit continuous_attains_sup continuous_on_subset)

  have "?H \<inter> {x. ?e2 \<bullet> x = max} \<noteq> {}"
    by (metis (mono_tags, lifting) cart_eq_inner_axis disjoint_iff e1e2_basis(3) inner_commute mem_Collect_eq x)
  moreover have "?H \<inter> {x. ?e2 \<bullet> x = max} = {}" if "(\<forall>x \<in> S. x$2 < max)"
  proof-
    have "S \<subseteq> {x. ?e2 \<bullet> x < max}"
      using that by (simp add: cart_eq_inner_axis e1e2_basis(3) inner_commute subset_eq)
    moreover have "convex {x. ?e2 \<bullet> x < max}" by (simp add: convex_halfspace_lt)
    ultimately show ?thesis using hull_minimal by blast
  qed
  ultimately have "\<exists>x \<in> S. x$2 \<ge> max" by force
  moreover have "?H \<subseteq> {x. ?e2 \<bullet> x \<le> max}"
    using x
    by (simp add: cart_eq_inner_axis e1e2_basis(3) inner_commute subsetI)
  moreover then have "interior ?H \<subseteq> {x. ?e2 \<bullet> x < max}"
    by (metis (mono_tags) convex_empty empty_iff inner_zero_left interior_halfspace_le interior_mono real_inner_1_left separating_hyperplane_set_0 vector_2(2) zero_index)
  ultimately have "x \<notin> interior ?H \<and> (\<forall>y \<in> interior ?H. x$2 > y$2)"
    by (smt (verit) cart_eq_inner_axis e1e2_basis(3) in_mono inner_commute mem_Collect_eq x)
  thus ?thesis using that \<open>\<exists>x\<in>S. max \<le> x $ 2\<close> x by fastforce
qed

lemma flip_function:
  defines "M \<equiv> (vector [vector [1, 0], vector [0, -1]])::(real^2^2)"
  defines "f \<equiv> \<lambda>v. M *v v"
  defines "g \<equiv> (\<lambda>v. vector [v$1, -v$2])::(real^2 \<Rightarrow> real^2)"
  shows "inj f" "f = g"
proof-
  have "det M = M$1$1 * M$2$2 - M$1$2 * M$2$1" using det_2 by blast
  thus "inj f" by (simp add: inj_matrix_vector_mult invertible_det_nz f_def M_def)

  have "\<And>x. f x = g x"
  proof-
    fix x
    have "f x = vector [M$1$1 * x$1 + M$1$2 * x$2, M$2$1 * x$1 + M$2$2 * x$2]"
      by (simp add: M_def f_def mat_vec_mult_2)
    also have "... = vector [x$1, -x$2]" by (simp add: M_def)
    finally show "f x = g x" using f_def g_def by blast
  qed
  thus "f = g" by (simp add: f_def g_def)
qed

lemma exists_point_below_convex_hull_interior:
  fixes S :: "(real^2) set"
  assumes "S \<noteq> {}"
  assumes "compact S"
  obtains x where "x \<in> S - (interior (convex hull S)) \<and> (\<forall>y \<in> interior (convex hull S). x$2 < y$2)"
proof-
  let ?M = "(vector [vector [1, 0], vector [0, -1]])::(real^2^2)"
  let ?f = "\<lambda>v. ?M *v v"
  let ?g = "(\<lambda>v. vector [v$1, -v$2])::(real^2 \<Rightarrow> real^2)"

  let ?H' = "?g`(convex hull S)"
  let ?S' = "?g`S"

  have interior: "?f`(interior (convex hull S)) = interior (convex hull (?f`S))"
    by (smt (verit, best) flip_function convex_hull_linear_image interior_injective_linear_image matrix_vector_mul_linear)
  have hull: "?H' = convex hull ?S'"
  proof- (* sledgehammer-generated *)
    have "(*v) (vector [vector [1, 0], vector [0, - 1]]) ` (convex hull S) = convex hull ((*v) (vector [vector [1, 0], vector [0, - 1]]) ` S::(real, 2) vec set)"
      by (simp add: convex_hull_linear_image)
    then show ?thesis
      by (simp add: flip_function)
  qed
  moreover have "compact ?S'"
  proof-
    have "continuous_on {x. True} ?f" using matrix_vector_mult_linear_continuous_on by blast
    then have "continuous_on {x. True} ?g" using flip_function by simp
    thus ?thesis using assms(2) compact_continuous_image continuous_on_subset flip_function by blast
  qed
  moreover have "?S' \<noteq> {}" using assms(1) by blast
  ultimately obtain x' where x': "x' \<in> ?S' - (interior ?H') \<and> (\<forall>y \<in> interior ?H'. x'$2 > y$2)"
    using exists_point_above_convex_hull_interior[of ?S'] by auto
  moreover have "?S' - (interior ?H') = ?f`(S - (interior (convex hull S)))"
  proof-
    have "?f`(S - (interior (convex hull S))) = ?S' - ?f`(interior (convex hull S))"
      by (metis (no_types, lifting) flip_function(1) flip_function(2) image_cong image_set_diff)
    thus ?thesis using flip_function(2) interior hull by auto
  qed
  ultimately obtain x where "?g x = x' \<and> x \<in> S - interior (convex hull S)"
    using flip_function by auto
  moreover have "(\<forall>y\<in>interior (convex hull S). x $ 2 < y $ 2)"
  proof clarify
    fix y
    assume "y \<in> interior (convex hull S)"
    then have "(?g x)$2 > (?g y)$2"
      using x' interior hull flip_function by (metis (no_types, lifting) calculation image_eqI)
    thus "x$2 < y$2" by simp
  qed
  ultimately show ?thesis using that by fast
qed

lemma exists_point_above_all:
  fixes p q :: "R_to_R2"
  defines "H \<equiv> convex hull (path_image p \<union> path_image q)"
  assumes "path p \<and> path q"
  assumes "p`{0<..<1} \<subseteq> interior H"
  assumes "(p 0)$2 = 0 \<and> (p 1)$2 = 0"
  assumes "\<exists>x \<in> p`{0<..<1}. x$2 \<ge> 0"
  obtains x where "x \<in> path_image q \<and> (\<forall>y \<in> path_image p. x$2 > y$2)"
proof-
  let ?S = "path_image p \<union> path_image q"
  let ?H = "convex hull ?S"
  obtain x where x: "x \<in> ?S - (interior ?H) \<and> (\<forall>y \<in> interior ?H. x$2 > y$2)"
    by (metis exists_point_above_convex_hull_interior Un_empty assms(2) compact_Un compact_path_image path_image_nonempty)
  then have "x \<notin> p`{0<..<1}" using H_def assms(3) by blast
  moreover have "x \<in> ?S" using x by blast
  ultimately have "x \<in> path_image q \<or> x \<in> (path_image p) - p`{0<..<1}" by blast
  moreover have "{0..1} - {0<..<1} = {0::real, 1}" by fastforce
  ultimately have "x \<in> path_image q \<or> x \<in> p`{0, 1}"
    by (smt (verit, best) image_diff_subset path_image_def subsetD)
  moreover have "x$2 > (p 0)$2 \<and> x$2 > (p 1)$2"
    using H_def assms(3) assms(4) assms(5) x by fastforce
  ultimately have "x \<in> path_image q \<and> x$2 > (p 0)$2 \<and> x$2 > (p 1)$2 \<and> (\<forall>y \<in> p`{0<..<1}. x$2 > y$2)"
    using H_def assms(3) x by auto
  moreover have "path_image p = p`{0<..<1} \<union> {p 0, p 1}"
  proof-
    have "{0<..<1} \<union> {0::real, 1} = {0..1}" by force
    thus ?thesis unfolding path_image_def by blast
  qed
  ultimately show ?thesis by (simp add: that)
qed

lemma exists_point_below_all:
  fixes p q :: "R_to_R2"
  defines "H \<equiv> convex hull (path_image p \<union> path_image q)"
  assumes "path p \<and> path q"
  assumes "p`{0<..<1} \<subseteq> interior H"
  assumes "(p 0)$2 = 0 \<and> (p 1)$2 = 0"
  assumes "\<exists>x \<in> path_image p \<union> path_image q. x$2 < 0"
  obtains x where "x \<in> path_image q \<and> (\<forall>y \<in> path_image p. x$2 < y$2)"
proof-
  let ?thesis' = "\<exists>x. x \<in> path_image q \<and> (\<forall>y \<in> path_image p. x$2 < y$2)"
  have ?thesis' if "\<exists>x \<in> path_image p. x$2 < 0"
  proof-
    have *: "\<exists>x \<in> p`{0<..<1}. x$2 < 0"
    proof-
      have "(p 0)$2 = 0 \<and> (p 1)$2 = 0" by (simp add: assms(4))
      thus ?thesis
        using that unfolding path_image_def
        using atLeastAtMost_iff less_eq_real_def
        by fastforce
    qed
    let ?S = "path_image p \<union> path_image q"
    let ?H = "convex hull ?S"
    obtain x where x: "x \<in> ?S - (interior ?H) \<and> (\<forall>y \<in> interior ?H. x$2 < y$2)"
      by (metis exists_point_below_convex_hull_interior Un_empty assms(2) compact_Un compact_path_image path_image_nonempty)
    then have "x \<notin> p`{0<..<1}" using H_def assms(3) by blast
    moreover have "x \<in> ?S" using x by blast
    ultimately have "x \<in> path_image q \<or> x \<in> (path_image p) - p`{0<..<1}" by blast
    moreover have "{0..1} - {0<..<1} = {0::real, 1}" by fastforce
    ultimately have "x \<in> path_image q \<or> x \<in> p`{0, 1}"
      by (smt (verit, best) image_diff_subset path_image_def subsetD)
    moreover have "x$2 < (p 0)$2 \<and> x$2 < (p 1)$2"
      by (smt (verit, ccfv_SIG) "*" H_def assms(3) assms(4) subset_eq x)
    ultimately have "x$2 < (p 0)$2 \<and> x$2 < (p 1)$2 \<and> (\<forall>y \<in> p`{0<..<1}. x$2 < y$2)"
      using H_def assms(3) x by blast
    moreover have "path_image p = p`{0<..<1} \<union> {p 0, p 1}"
    proof-
      have "{0<..<1} \<union> {0::real, 1} = {0..1}" by force
      thus ?thesis unfolding path_image_def by blast
    qed
    ultimately have "\<forall>y \<in> path_image p. x$2 < y$2" by fast
    thus ?thesis using x by fast
  qed
  moreover then have ?thesis' if "\<not> (\<exists>x \<in> path_image p. x$2 < 0)" using assms(5) by fastforce
  ultimately show ?thesis using that by blast
qed

lemma pocket_fill_line_int_aux:
  fixes x y z :: "real^2"
  defines "a \<equiv> y$1"
  assumes "x = 0"
  assumes "a > 0 \<and> y$2 = 0"
  assumes "z$1 < 0 \<or> z$1 > a"
  assumes "z$2 = 0"
  assumes "convex A \<and> compact A"
  assumes "{x, y, z} \<subseteq> A"
  assumes "{x, y} \<subseteq> frontier A"
  shows "z \<in> frontier A \<and> closed_segment x y \<subseteq> frontier A"
proof(rule disjE[OF assms(4)])
  assume "z$1 > a"
  moreover have xyz: "x$1 = 0 \<and> x$2 = 0 \<and> y$1 = a \<and> y$2 = 0 \<and> z$2 = 0"
    by (simp add: a_def assms(2) assms(3) assms(5))
  ultimately have y: "y \<in> path_image (linepath x z)" (is "_ \<in> ?L")
    using segment_horizontal assms(3) by force
  moreover have y_neq: "y \<noteq> x \<and> y \<noteq> z"
    by (metis a_def assms(2) assms(3) assms(4) not_less_iff_gr_or_eq zero_index)
  ultimately have "y \<in> rel_interior ?L"
    by (metis UnE closed_segment_eq_open closed_segment_idem insert_Diff insert_iff path_image_linepath rel_interior_closed_segment singleton_insert_inj_eq)
  moreover have "?L \<subseteq> A" using assms closed_segment_subset by auto
  moreover have "z \<in> interior A \<union> frontier A"
    by (metis Diff_iff UnI1 UnI2 assms(6) calculation(2) closure_convex_hull convex_hull_eq frontier_def in_mono pathfinish_in_path_image pathfinish_linepath)
  ultimately have "z \<in> frontier A"
    by (metis (no_types, lifting) Int_iff UnE y y_neq assms(6) assms(8) compact_imp_closed insert_subset singletonD triangle_3_split_helper)
  moreover have "closed_segment x y \<subseteq> frontier A"
  proof(rule ccontr)
    assume "\<not> closed_segment x y \<subseteq> frontier A"
    then obtain v where "v \<in> closed_segment x y - frontier A" by blast
    moreover then have "v \<in> closed_segment x y \<inter> interior A"
      by (metis (no_types, lifting) DiffD1 DiffD2 DiffI Int_iff assms(6) assms(7) closed_segment_subset closure_convex_hull convex_hull_eq frontier_def insert_subset subsetD)
    moreover from calculation have "v \<noteq> x \<and> v \<noteq> y" using assms(8) by auto
    moreover from calculation have "v$1 < a"
      by (smt (z3) DiffD1 a_def assms(2) assms(3) exhaust_2 segment_horizontal vec_eq_iff zero_index)
    moreover from calculation have "y \<in> open_segment v z"
      by (smt (z3) Diff_iff xyz insert_iff open_segment_def open_segment_idem path_image_linepath segment_horizontal y y_neq)
    ultimately have "y \<in> interior A"
      by (metis (no_types, lifting) IntD2 assms(6) assms(7) closure_convex_hull convex_hull_eq in_interior_closure_convex_segment insertI2 singletonI subsetD)
    thus False using assms(8) frontier_def by auto
  qed
  ultimately show "z \<in> frontier A \<and> closed_segment x y \<subseteq> frontier A" by blast
next (* copy/paste previous case, switching the roles of x and y*)
  assume *: "z$1 < 0"
  moreover have xyz: "x$1 = 0 \<and> x$2 = 0 \<and> y$1 = a \<and> y$2 = 0 \<and> z$2 = 0"
    by (simp add: a_def assms(2) assms(3) assms(5))
  ultimately have x: "x \<in> path_image (linepath y z)" (is "_ \<in> ?L'")
    using segment_horizontal assms(3) by force
  moreover have x_neq: "y \<noteq> x \<and> x \<noteq> z"
    by (metis a_def assms(2) assms(3) assms(4) not_less_iff_gr_or_eq zero_index)
  ultimately have "x \<in> rel_interior ?L'"
    by (metis UnE closed_segment_eq_open closed_segment_idem insert_Diff insert_iff path_image_linepath rel_interior_closed_segment singleton_insert_inj_eq)
  moreover have "?L' \<subseteq> A"
  proof-
    have "y \<in> A \<and> z \<in> A" using assms by blast
    thus ?thesis by (simp add: assms(6) closed_segment_subset)
  qed
  moreover have "z \<in> interior A \<union> frontier A"
    by (metis Diff_iff UnI1 UnI2 assms(6) calculation(2) closure_convex_hull convex_hull_eq frontier_def in_mono pathfinish_in_path_image pathfinish_linepath)
  ultimately have "z \<in> frontier A"
    by (metis (no_types, lifting) Int_iff UnE x x_neq assms(6) assms(8) compact_imp_closed insert_subset singletonD triangle_3_split_helper)
  moreover have "closed_segment x y \<subseteq> frontier A"
  proof(rule ccontr)
    assume "\<not> closed_segment x y \<subseteq> frontier A"
    then obtain v where "v \<in> closed_segment x y - frontier A" by blast
    moreover then have "v \<in> closed_segment x y \<inter> interior A"
      by (metis (no_types, lifting) DiffD1 DiffD2 DiffI Int_iff assms(6) assms(7) closed_segment_subset closure_convex_hull convex_hull_eq frontier_def insert_subset subsetD)
    moreover from calculation have "v \<noteq> x \<and> v \<noteq> y" using assms(8) by auto
    moreover from calculation have "v$1 > 0"
      by (smt (z3) DiffD1 a_def assms(2) assms(3) exhaust_2 segment_horizontal vec_eq_iff zero_index)
    moreover from calculation have "x \<in> open_segment v z"
      by (smt (z3) Diff_iff xyz insert_iff open_segment_def open_segment_idem path_image_linepath segment_horizontal x x_neq)
    ultimately have "x \<in> interior A"
      by (metis (no_types, lifting) IntD2 assms(6) assms(7) closure_convex_hull convex_hull_eq in_interior_closure_convex_segment insertI2 singletonI subsetD)
    thus False using assms(8) frontier_def by auto
  qed
  ultimately show "z \<in> frontier A \<and> closed_segment x y \<subseteq> frontier A" by blast
qed

lemma axis_dist:
  fixes a b :: "real^2"
  shows "a$2 = b$2 \<Longrightarrow> dist a b = dist (a$1) (b$1)" "a$1 = b$1 \<Longrightarrow> dist a b = dist (a$2) (b$2)"
proof-
  have "dist a b = norm (b - a)" by (metis dist_commute dist_norm)
  also have "... = sqrt ((b - a) \<bullet> (b - a))" using norm_eq_sqrt_inner by blast
  also have "... = sqrt ((b - a)$1 * (b - a)$1 + (b - a)$2 * (b - a)$2)"
    by (simp add: inner_vec_def sum_2)
  finally have *: "dist a b = sqrt ((b - a)$1 * (b - a)$1 + (b - a)$2 * (b - a)$2)" .
  show "a$2 = b$2 \<Longrightarrow> dist a b = dist (a$1) (b$1)"
       "a$1 = b$1 \<Longrightarrow> dist a b = dist (a$2) (b$2)"
    apply (simp add: "*" dist_real_def)
    by (simp add: "*" dist_real_def)
qed

lemma dist_bound_1:
  fixes a b x :: "real^2"
  assumes "a$2 = x$2"
  assumes "b \<in> ball x \<epsilon>"
  assumes "\<epsilon> < dist a x"
  shows "a$1 < x$1 \<Longrightarrow> b$1 > a$1" "a$1 > x$1 \<Longrightarrow> b$1 < a$1"
proof-
  have 1: "dist a x = dist (a$1) (x$1)" using axis_dist assms(1) by blast
  have 2: "dist (b$1) (x$1) < \<epsilon>"
    by (metis  assms(2) dist_commute dist_vec_nth_le mem_ball order_le_less_trans)
  show "a$1 < x$1 \<Longrightarrow> b$1 > a$1" "a$1 > x$1 \<Longrightarrow> b$1 < a$1"
    apply (smt (verit, ccfv_threshold) assms(1) assms(3) 1 2 dist_norm real_norm_def)
    by (smt (verit, ccfv_threshold) assms(1) assms(3) 1 2 dist_norm real_norm_def)
qed

lemma dist_bound_2:
  fixes a b x :: "real^2"
  assumes "a$1 = x$1"
  assumes "b \<in> ball x \<epsilon>"
  assumes "\<epsilon> < dist a x"
  shows "a$2 < x$2 \<Longrightarrow> b$2 > a$2" "a$2 > x$2 \<Longrightarrow> b$2 < a$2"
proof-
  have 1: "dist a x = dist (a$2) (x$2)" using axis_dist assms(1) by blast
  have 2: "dist (b$2) (x$2) < \<epsilon>"
    by (metis  assms(2) dist_commute dist_vec_nth_le mem_ball order_le_less_trans)
  show "a$2 < x$2 \<Longrightarrow> b$2 > a$2" "a$2 > x$2 \<Longrightarrow> b$2 < a$2"
    apply (smt (verit, ccfv_threshold) assms(1) assms(3) 1 2 dist_norm real_norm_def)
    by (smt (verit, ccfv_threshold) assms(1) assms(3) 1 2 dist_norm real_norm_def)
qed

lemma linepath_bound_1:
  fixes x y :: "real^2"
  shows "a < x$1 \<and> a < y$1 \<Longrightarrow> \<forall>v \<in> path_image (linepath x y). a < v$1"
        "x$1 < b \<and> y$1 < b \<Longrightarrow> \<forall>v \<in> path_image (linepath x y). v$1 < b"
proof-
  have *: "\<forall>v \<in> path_image (linepath x y). \<exists>u \<in> {0..1}. v = (1 - u) *\<^sub>R x + u *\<^sub>R y"
    by (simp add: image_iff linepath_def path_image_def)
  have 1: "\<forall>u \<in> {0..1}. a < ((1 - u) *\<^sub>R x + u *\<^sub>R y)$1" if "a < x$1 \<and> a < y$1"
  proof clarify
    fix u assume "u \<in> {0..1::real}"
    then have *: "u \<ge> 0 \<and> 1 - u \<ge> 0" by simp
    then show "a < ((1 - u) *\<^sub>R x + u *\<^sub>R y)$1"
      by (smt (z3) that scaleR_collapse scaleR_left_mono vector_add_component vector_scaleR_component)
  qed
  have 2: "\<forall>u \<in> {0..1}. ((1 - u) *\<^sub>R x + u *\<^sub>R y)$1 < b" if "x$1 < b \<and> y$1 < b"
  proof clarify
    fix u assume "u \<in> {0..1::real}"
    then have *: "u \<ge> 0 \<and> 1 - u \<ge> 0" by simp
    then show "((1 - u) *\<^sub>R x + u *\<^sub>R y)$1 < b"
      by (smt (z3) that scaleR_collapse scaleR_left_mono vector_add_component vector_scaleR_component)
  qed
  show "a < x$1 \<and> a < y$1 \<Longrightarrow> \<forall>v \<in> path_image (linepath x y). a < v$1" using * 1 by fastforce
  show "x$1 < b \<and> y$1 < b \<Longrightarrow> \<forall>v \<in> path_image (linepath x y). v$1 < b" using * 2 by fastforce
qed

lemma linepath_bound_2:
  fixes x y :: "real^2"
  shows "a < x$2 \<and> a < y$2 \<Longrightarrow> \<forall>v \<in> path_image (linepath x y). a < v$2"
        "x$2 < b \<and> y$2 < b \<Longrightarrow> \<forall>v \<in> path_image (linepath x y). v$2 < b"
proof-
  have *: "\<forall>v \<in> path_image (linepath x y). \<exists>u \<in> {0..1}. v = (1 - u) *\<^sub>R x + u *\<^sub>R y"
    by (simp add: image_iff linepath_def path_image_def)
  have 1: "\<forall>u \<in> {0..1}. a < ((1 - u) *\<^sub>R x + u *\<^sub>R y)$2" if "a < x$2 \<and> a < y$2"
  proof clarify
    fix u assume "u \<in> {0..1::real}"
    then have *: "u \<ge> 0 \<and> 1 - u \<ge> 0" by simp
    then show "a < ((1 - u) *\<^sub>R x + u *\<^sub>R y)$2"
      by (smt (z3) that scaleR_collapse scaleR_left_mono vector_add_component vector_scaleR_component)
  qed
  have 2: "\<forall>u \<in> {0..1}. ((1 - u) *\<^sub>R x + u *\<^sub>R y)$2 < b" if "x$2 < b \<and> y$2 < b"
  proof clarify
    fix u assume "u \<in> {0..1::real}"
    then have *: "u \<ge> 0 \<and> 1 - u \<ge> 0" by simp
    then show "((1 - u) *\<^sub>R x + u *\<^sub>R y)$2 < b"
      by (smt (z3) that scaleR_collapse scaleR_left_mono vector_add_component vector_scaleR_component)
  qed
  show "a < x$2 \<and> a < y$2 \<Longrightarrow> \<forall>v \<in> path_image (linepath x y). a < v$2" using * 1 by fastforce
  show "x$2 < b \<and> y$2 < b \<Longrightarrow> \<forall>v \<in> path_image (linepath x y). v$2 < b" using * 2 by fastforce
qed

lemma linepath_int_corner:
  fixes x y z :: "real^2"
  assumes "x$2 \<noteq> y$2"
  assumes "y$2 = z$2"
  shows "path_image (linepath x y) \<inter> path_image (linepath y z) = {y}"
    (is "path_image ?l1 \<inter> path_image ?l2 = {y}")
proof-
  have 1: "y \<in> path_image ?l1 \<inter> path_image ?l2" by simp

  have "\<forall>t \<in> {0..1}. (?l1 t)$2 = y$2 \<longrightarrow> t = 1"
  proof clarify
    fix t :: real
    assume 1: "t \<in> {0..1}"
    assume 2: "(?l1 t)$2 = y$2"

    have "(?l1 t)$2 = ((1 - t) * (x$2) + t * (y$2))" by (simp add: linepath_def)
    thus "t = 1"
      by (smt (verit, best) assms 2 distrib_right inner_real_def mult.commute real_inner_1_right vector_space_over_itself.scale_cancel_left)
  qed
  then have "\<forall>t \<in> {0..1}. (?l1 t)$2 = y$2 \<longleftrightarrow> t = 1" by (metis linepath_1')
  moreover have "\<forall>t \<in> {0..1}. (?l2 t)$2 = y$2"
    unfolding linepath_def
    by (metis (no_types, lifting) assms(2) segment_degen_1 vector_add_component vector_scaleR_component)
  ultimately have 2: "path_image ?l1 \<inter> path_image ?l2 \<subseteq> {y}"
    by (smt (verit, best) "1" IntD1 IntD2 imageE path_defs(4) singleton_iff subsetI)

  show ?thesis using 1 2 by fastforce
qed

lemma linepath_int_vertical:
  fixes w x y z :: "real^2"
  assumes "w$1 \<noteq> y$1"
  assumes "w$1 = x$1"
  assumes "y$1 = z$1"
  shows "path_image (linepath w x) \<inter> path_image (linepath y z) = {}"
  using assms segment_vertical by fastforce

lemma linepath_int_horizontal:
  fixes w x y z :: "real^2"
  assumes "w$2 \<noteq> y$2"
  assumes "w$2 = x$2"
  assumes "y$2 = z$2"
  shows "path_image (linepath w x) \<inter> path_image (linepath y z) = {}"
  using assms segment_horizontal by fastforce

lemma linepath_int_columns:
  fixes w x y z :: "real^2"
  assumes "w$1 < y$1 \<and> w$1 < z$1"
  assumes "x$1 < y$1 \<and> x$1 < z$1"
  shows "path_image (linepath w x) \<inter> path_image (linepath y z) = {}"
    (is "path_image ?l1 \<inter> path_image ?l2 = {}")
proof-
  have "\<forall>t1 \<in> {0..1}. \<forall>t2 \<in> {0..1}. (?l2 t2)$1 > (?l1 t1)$1"
    by (smt (verit, ccfv_SIG) assms linepath_bound_1 linepath_in_path path_image_linepath)
  thus ?thesis by (smt (verit, best) disjoint_iff imageE path_image_def)
qed

lemma linepath_int_rows:
  fixes w x y z :: "real^2"
  assumes "w$2 < y$2 \<and> w$2 < z$2"
  assumes "x$2 < y$2 \<and> x$2 < z$2"
  shows "path_image (linepath w x) \<inter> path_image (linepath y z) = {}"
    (is "path_image ?l1 \<inter> path_image ?l2 = {}")
proof-
  have "\<forall>t1 \<in> {0..1}. \<forall>t2 \<in> {0..1}. (?l2 t2)$2 > (?l1 t1)$2"
    by (smt (verit, ccfv_SIG) assms linepath_bound_2 linepath_in_path path_image_linepath)
  thus ?thesis by (smt (verit, best) disjoint_iff imageE path_image_def)
qed

lemma horizontal_segment_at_0:
  assumes "a > 0"
  shows "closed_segment ((vector [0, 0])::(real^2)) (vector [a, 0]) = {x. x$2 = 0 \<and> x$1 \<in> {0..a}}"
    (is "?l = ?s")
proof-
  have "?l \<subseteq> ?s"
  proof(rule subsetI)
    fix x
    assume *: "x \<in> ?l"
    then have "x$2 = 0" using segment_horizontal by auto
    moreover have "0 \<le> x$1 \<and> x$1 \<le> a" using * assms segment_horizontal by force
    ultimately show "x \<in> ?s" by force
  qed
  moreover have "?s \<subseteq> ?l"
  proof(rule subsetI)
    fix x
    assume *: "x \<in> ?s"
    then have "x = (x$1 / a) *\<^sub>R (vector [a, 0]) + (1 - (x$1 / a)) *\<^sub>R (vector [0, 0])"
    proof-
      have "(x$1 / a) *\<^sub>R ((vector [a, 0])::(real^2)) = vector [x$1, 0]"
        using vec_scaleR_2 assms by fastforce
      moreover have "(1 - (x$1 / a)) *\<^sub>R ((vector [0, 0])::(real^2)) = vector [0, 0]"
        using vec_scaleR_2 by simp
      moreover have "x = vector [x$1, 0]"
        by (smt (verit) * exhaust_2 mem_Collect_eq vec_eq_iff vector_2(1) vector_2(2))
      ultimately show ?thesis
        by (metis add_cancel_right_right scaleR_collapse vec_scaleR_2 vector_2(2))
    qed
    moreover have "x$1 / a \<in> {0..1}" using * assms by fastforce
    ultimately show "x \<in> ?l"
      by (smt (verit, del_insts) add.commute atLeastAtMost_iff mem_Collect_eq closed_segment_def)
  qed
  ultimately show ?thesis by blast
qed

lemma horizontal_segment_at_0':
  fixes x y :: "real^2"
  assumes "a > 0"
  assumes "x$1 = 0 \<and> x$2 = 0 \<and> y$1 = a \<and> y$2 = 0"
  shows "closed_segment x y = {x. x$2 = 0 \<and> x$1 \<in> {0..a}}"
proof-
  have "x = vector [0, 0] \<and> y = vector [a, 0]"
    by (smt (verit, best) assms(2) exhaust_2 vec_eq_iff vector_2(1) vector_2(2))
  thus ?thesis using horizontal_segment_at_0 assms by presburger
qed

lemma pocket_fill_line_int_aux1:
  fixes p q :: "R_to_R2"
  defines "p0 \<equiv> pathstart p"
  defines "p1 \<equiv> pathfinish p"
  defines "q0 \<equiv> pathstart q"
  defines "q1 \<equiv> pathfinish q"
  defines "a \<equiv> p1$1"
  defines "l \<equiv> closed_segment p0 p1"
  assumes "simple_path p"
  assumes "simple_path q"
  assumes "p0$1 = 0 \<and> p0$2 = 0 \<and> p1$2 = 0"
  assumes "a > 0"
  assumes "path_image q \<inter> {x. x$2 = 0} \<subseteq> l"
  assumes "path_image p \<inter> {x. x$2 = 0} \<subseteq> l"
  assumes "\<forall>v \<in> path_image p. q0$2 \<le> v$2"
  assumes "\<forall>v \<in> path_image p. q1$2 > v$2"
  shows "path_image p \<inter> path_image q \<noteq> {}"
proof-
  have p0: "p0 = 0"
    by (metis (mono_tags, opaque_lifting) assms(9) exhaust_2 vec_eq_iff zero_index)
  moreover have p1: "p1 = vector [a, 0]"
    by (smt (verit) a_def assms(9) exhaust_2 vec_eq_iff vector_2(1) vector_2(2))

  obtain a_x where a_x: "\<forall>v \<in> path_image p \<union> path_image q. a_x < v$1"
  proof-
    let ?a_x = "Inf ((\<lambda>v. v$1)`(path_image p \<union> path_image q))"
    have "compact (path_image p \<union> path_image q)"
      by (simp add: assms(7) assms(8) compact_Un compact_simple_path_image)
    moreover have "continuous_on UNIV ((\<lambda>v. v$1)::(real^2 \<Rightarrow> real))"
      by (simp add: continuous_on_component)
    ultimately have *: "compact ((\<lambda>v. v$1)`(path_image p \<union> path_image q))"
      by (meson compact_continuous_image continuous_on_subset top_greatest)
    then have "\<forall>x \<in> ((\<lambda>v. v$1)`(path_image p \<union> path_image q)). ?a_x \<le> x"
      by (simp add: assms(7) assms(8) bounded_component_cart bounded_has_Inf(1) bounded_simple_path_image)
    thus ?thesis using that[of "?a_x - 1"] by (smt (verit, ccfv_SIG) assms(10) imageI)
  qed
  obtain b_x where b_x: "\<forall>v \<in> path_image p \<union> path_image q. b_x > v$1"
  proof-
    let ?b_x = "Sup ((\<lambda>v. v$1)`(path_image p \<union> path_image q))"
    have "compact (path_image p \<union> path_image q)"
      by (simp add: assms(7) assms(8) compact_Un compact_simple_path_image)
    moreover have "continuous_on UNIV ((\<lambda>v. v$1)::(real^2 \<Rightarrow> real))"
      by (simp add: continuous_on_component)
    ultimately have *: "compact ((\<lambda>v. v$1)`(path_image p \<union> path_image q))"
      by (meson compact_continuous_image continuous_on_subset top_greatest)
    then have "\<forall>x \<in> ((\<lambda>v. v$1)`(path_image p \<union> path_image q)). ?b_x \<ge> x"
      by (simp add: assms(7) assms(8) bounded_component_cart bounded_has_Sup(1) bounded_simple_path_image)
    thus ?thesis using that[of "?b_x + 1"] by (smt (verit, ccfv_SIG) assms(10) imageI)
  qed
  obtain b_y where b_y: "\<forall>v \<in> path_image p \<union> path_image q. b_y > v$2"
  proof-
    let ?b_y = "Sup ((\<lambda>v. v$2)`(path_image p \<union> path_image q))"
    have "compact (path_image p \<union> path_image q)"
      by (simp add: assms(7) assms(8) compact_Un compact_simple_path_image)
    moreover have "continuous_on UNIV ((\<lambda>v. v$2)::(real^2 \<Rightarrow> real))"
      by (simp add: continuous_on_component)
    ultimately have *: "compact ((\<lambda>v. v$2)`(path_image p \<union> path_image q))"
      by (meson compact_continuous_image continuous_on_subset top_greatest)
    then have "\<forall>x \<in> ((\<lambda>v. v$2)`(path_image p \<union> path_image q)). ?b_y \<ge> x"
      by (simp add: assms(7) assms(8) bounded_component_cart bounded_has_Sup(1) bounded_simple_path_image)
    thus ?thesis using that[of "?b_y + 1"] by (smt (verit, ccfv_SIG) assms(10) imageI)
  qed

  let ?l1 = "linepath p1 (vector [b_x, 0])"
  let ?l2 = "linepath (vector [b_x, 0]) ((vector [b_x, b_y])::(real^2))"
  let ?l3 = "linepath (vector [b_x, b_y]) ((vector [a_x, b_y])::(real^2))"
  let ?l4 = "linepath (vector [a_x, b_y]) ((vector [a_x, 0])::(real^2))"
  let ?l5 = "linepath (vector [a_x, 0]) p0"

  let ?R' = "?l1 +++ ?l2 +++ ?l3 +++ ?l4 +++ ?l5"
  let ?R = "p +++ ?R'"

  have R_y_b: "\<forall>v \<in> path_image ?R. v$2 \<le> b_y"
  proof-
    have "\<forall>v \<in> path_image ?l1. v$2 \<le> b_y"
      by (metis UnCI assms(9) b_y less_eq_real_def p1_def path_image_linepath pathfinish_in_path_image segment_horizontal vector_2(2))
    moreover have "\<forall>v \<in> path_image ?l2. v$2 \<le> b_y"
      by (smt (verit, ccfv_SIG) UnCI assms(9) b_y p0_def path_image_linepath pathstart_in_path_image segment_vertical vector_2(1) vector_2(2))
    moreover have "\<forall>v \<in> path_image ?l3. v$2 \<le> b_y"
      by (simp add: segment_horizontal)
    moreover have "\<forall>v \<in> path_image ?l4. v$2 \<le> b_y"
      by (smt (verit, best) UnCI assms(9) b_y p0_def path_image_linepath pathstart_in_path_image segment_vertical vector_2(1) vector_2(2))
    moreover have "\<forall>v \<in> path_image ?l5. v$2 \<le> b_y"
      by (smt (verit) UnI1 assms(9) b_y linepath_image_01 p0_def path_defs(4) pathstart_in_path_image segment_horizontal vector_2(2))
    ultimately show ?thesis by (smt (verit, best) UnCI b_y not_in_path_image_join)
  qed
  have R_y_q0: "\<forall>v \<in> path_image ?R. v$2 \<ge> q0$2"
  proof-
    have "\<forall>v \<in> path_image ?l1. v$2 \<ge> q0$2"
      using assms(13) assms(9) p1_def pathfinish_in_path_image segment_horizontal by fastforce
    moreover have "\<forall>v \<in> path_image ?l2. v$2 \<ge> q0$2"
      by (smt (z3) UnCI assms(13) assms(9) b_y p1_def path_image_linepath pathfinish_in_path_image segment_vertical vector_2(1) vector_2(2))
    moreover have "\<forall>v \<in> path_image ?l3. v$2 \<ge> q0$2"
      by (metis calculation(2) ends_in_segment(2) path_image_linepath segment_horizontal vector_2(2))
    moreover have "\<forall>v \<in> path_image ?l4. v$2 \<ge> q0$2"
      by (smt (z3) UnCI assms(13) assms(9) b_y p1_def path_image_linepath pathfinish_in_path_image segment_vertical vector_2(1) vector_2(2))
    moreover have "\<forall>v \<in> path_image ?l5. v$2 \<ge> q0$2"
      by (metis assms(13) assms(9) p0_def path_image_linepath pathstart_in_path_image segment_horizontal vector_2(2))
    ultimately show ?thesis
      by (metis assms(13) not_in_path_image_join)
  qed

  have R_x_a: "\<forall>v \<in> path_image ?R. v$1 \<ge> a_x"
  proof-
    have "\<forall>v \<in> path_image ?l1. v$2 \<ge> a_x"
      by (metis UnCI a_x assms(9) linorder_le_cases linorder_not_less p0_def path_image_linepath pathstart_in_path_image segment_horizontal vector_2(2))
    moreover have "\<forall>v \<in> path_image ?l2. v$2 \<ge> a_x"
      by (smt (z3) UnCI assms(9) b_y calculation p0_def path_image_linepath pathstart_in_path_image pathstart_linepath segment_vertical vector_2(1) vector_2(2))
    moreover have "\<forall>v \<in> path_image ?l3. v$2 \<ge> a_x"
      by (metis calculation(2) ends_in_segment(2) path_image_linepath segment_horizontal vector_2(2))
    moreover have "\<forall>v \<in> path_image ?l4. v$2 \<ge> a_x"
      by (smt (z3) assms(9) calculation(1) calculation(3) ends_in_segment(1) path_image_linepath segment_vertical vector_2(1) vector_2(2))
    moreover have "\<forall>v \<in> path_image ?l5. v$2 \<ge> a_x"
      by (smt (verit, del_insts) UnCI a_x assms(9) p0_def path_image_linepath pathstart_in_path_image segment_horizontal vector_2(2))
    ultimately show ?thesis
      by (smt (z3) UnCI a_x assms(9) b_x not_in_path_image_join p1_def path_image_linepath pathfinish_in_path_image segment_horizontal segment_vertical vector_2(1) vector_2(2))
  qed

  have closed: "closed_path ?R" using assms p0_def unfolding simple_path_def closed_path_def by simp
  have simple: "simple_path ?R"
  proof-
    have "arc ?R'"
    proof-
      let ?a = "p1"
      let ?b = "(vector [b_x, 0])::(real^2)"
      let ?c = "(vector [b_x, b_y])::(real^2)"
      let ?d = "(vector [a_x, b_y])::(real^2)"
      let ?e = "(vector [a_x, 0])::(real^2)"
      let ?f = "p0"

      have arcs: "arc ?l1 \<and> arc ?l2 \<and> arc ?l3 \<and> arc ?l4 \<and> arc ?l5"
        by (smt (verit, ccfv_SIG) UnCI a_x arc_linepath assms(9) b_x b_y p0_def p1_def pathfinish_in_path_image pathstart_in_path_image vector_2(1) vector_2(2))

      have l4l5: "path_image ?l4 \<inter> path_image ?l5 = {pathfinish ?l4}"
        using linepath_int_corner[of ?d ?e ?f] arc_simple_path arcs constant_linepath_is_not_loop_free p0 simple_path_def
        by auto
      have l3l4: "path_image ?l3 \<inter> path_image ?l4 = {pathfinish ?l3}"
        using linepath_int_corner[of ?c ?d ?e]
        by (metis Int_commute arc_simple_path arcs closed_segment_commute linepath_0' linepath_int_corner path_image_linepath pathfinish_linepath pathstart_def vector_2(2))
      have l2l3: "path_image ?l2 \<inter> path_image ?l3 = {pathfinish ?l2}"
        using linepath_int_corner[of ?b ?c ?d]
        by (metis Int_commute arc_simple_path arcs linepath_0' linepath_int_corner pathfinish_linepath pathstart_def vector_2(2))
      have l1l2: "path_image ?l1 \<inter> path_image ?l2 = {pathfinish ?l1}"
        using linepath_int_corner[of ?a ?b ?c]
        by (metis Int_commute arc_distinct_ends arcs assms(9) closed_segment_commute linepath_int_corner path_image_linepath pathfinish_linepath pathstart_linepath vector_2(2))

      have l3l5: "path_image ?l3 \<inter> path_image ?l5 = {}"
        using linepath_int_horizontal[of ?c ?d ?e ?f]
        by (metis arc_distinct_ends arcs assms(9) linepath_int_horizontal pathfinish_linepath pathstart_linepath vector_2(2))
      have l2l4: "path_image ?l2 \<inter> path_image ?l4 = {}"
        using linepath_int_vertical[of ?b ?c ?d ?e]
        by (metis arc_distinct_ends arcs linepath_int_vertical pathfinish_linepath pathstart_linepath vector_2(1))
      have l1l3: "path_image ?l1 \<inter> path_image ?l3 = {}"
        using linepath_int_vertical[of ?a ?b ?c ?d]
        by (metis arc_distinct_ends arcs assms(9) linepath_int_horizontal pathfinish_linepath pathstart_linepath vector_2(2))

      have l2l5: "path_image ?l2 \<inter> path_image ?l5 = {}"
        using linepath_int_columns[of ?b ?c ?e ?f]
        by (smt (verit, ccfv_threshold) Int_commute UnCI a_x b_x linepath_int_columns p0 p0_def pathstart_in_path_image pathstart_join vector_2(1) verit_comp_simplify1(3))
      have l1l4: "path_image ?l1 \<inter> path_image ?l4 = {}"
        using linepath_int_columns[of ?a ?b ?d ?e]
        by (smt (z3) UnCI a_x assms(9) b_x disjoint_iff p1_def path_image_linepath pathfinish_in_path_image segment_horizontal segment_vertical vector_2(1) vector_2(2))

      have l1l5: "path_image ?l1 \<inter> path_image ?l5 = {}"
        using linepath_int_columns[of ?a ?b ?e ?f]
        by (smt (z3) UnCI a_def a_x assms(10) assms(9) b_x disjoint_iff p1_def path_image_linepath pathfinish_in_path_image segment_horizontal vector_2(1) vector_2(2))

      have "path_image ?l4 \<inter> path_image ?l5 = {pathfinish ?l4}"
        using l4l5 by blast
      moreover have sf_45: "pathfinish ?l4 = pathstart ?l5" by simp
      ultimately have "arc (?l4 +++ ?l5)"
        by (metis arc_join_eq_alt arcs)
      moreover have "path_image ?l3 \<inter> path_image (?l4 +++ ?l5) = {pathfinish ?l3}"
        using l3l4 l3l5
        by (metis (no_types, lifting) Int_Un_distrib sf_45 insert_is_Un path_image_join)
      moreover have sf_345: "pathfinish ?l3 = pathstart (?l4 +++ ?l5)" by simp
      ultimately have "arc (?l3 +++ ?l4 +++ ?l5)" 
        by (metis arc_join_eq_alt arcs)
      moreover have "path_image ?l2 \<inter> path_image (?l3 +++ ?l4 +++ ?l5) = {pathfinish ?l2}"
        using l2l3 l2l4 l2l5
        by (smt (verit) Int_Un_distrib sf_45 sf_345 insert_is_Un path_image_join sup_bot_left)
      moreover have sf_2345: "pathfinish ?l2 = pathstart (?l3 +++ ?l4 +++ ?l5)" by simp
      ultimately have "arc (?l2 +++ ?l3 +++ ?l4 +++ ?l5)"
        by (metis arc_join_eq_alt arcs)
      moreover have "path_image ?l1 \<inter> path_image (?l2 +++ ?l3 +++ ?l4 +++ ?l5) = {pathfinish ?l1}"
      proof-
        have "path_image (?l2 +++ ?l3 +++ ?l4 +++ ?l5)
            = path_image ?l2 \<union> path_image ?l3 \<union> path_image ?l4 \<union> path_image ?l5"
          by (simp add: path_image_join sup_assoc)
        thus ?thesis using l1l2 l1l3 l1l4 l1l5 by blast
      qed
      moreover have "pathfinish ?l1 = pathstart (?l2 +++ ?l3 +++ ?l4 +++ ?l5)" by simp
      ultimately show "arc (?l1 +++ ?l2 +++ ?l3 +++ ?l4 +++ ?l5)"
        by (metis arc_join_eq_alt arcs)
    qed
    moreover have "loop_free p" using assms(1) assms(7) simple_path_def by blast
    moreover have "path_image ?R' \<inter> path_image p = {p0, p1}"
    proof-
      have "path_image p \<inter> path_image ?l2 = {}" using b_x segment_vertical by auto
      moreover have "path_image p \<inter> path_image ?l3 = {}" using b_y segment_horizontal by auto
      moreover have "path_image p \<inter> path_image ?l4 = {}" using a_x segment_vertical by auto
      moreover have "path_image p \<inter> path_image ?l1 = {p1}"
      proof-
        have "p1 \<in> path_image p" using p1_def by blast
        moreover have "path_image p \<inter> path_image ?l1 \<subseteq> {p1}"
        proof(rule subsetI)
          fix x assume *: "x \<in> path_image p \<inter> path_image ?l1"
          then have "x$1 \<le> a"
            using a_def assms(10) assms(12) assms(9) l_def linepath_image_01 segment_horizontal by auto
          moreover have "x$1 \<ge> a"
            by (smt (z3) "*" Int_iff Un_iff a_def assms(9) b_x linepath_image_01 path_defs(4) segment_horizontal vector_2(1) vector_2(2))
          moreover have "x$2 = 0" using * assms(9) segment_horizontal by auto
          ultimately show "x \<in> {p1}" using a_def assms(9) segment_vertical by fastforce
        qed
        ultimately show ?thesis by auto
      qed
      moreover have "path_image p \<inter> path_image ?l5 = {p0}"
      proof-
        have "p0 \<in> path_image p" using p0_def by blast
        moreover have "path_image p \<inter> path_image ?l5 \<subseteq> {p0}"
        proof(rule subsetI)
          fix x assume *: "x \<in> path_image p \<inter> path_image ?l5"
          then have "x$1 \<le> 0"
            using R_x_a assms(9) p0_def pathstart_in_path_image segment_horizontal by fastforce
          moreover have "x$1 \<ge> 0"
          proof-
            have "x \<in> {x. x$2 = 0}" using "*" assms(9) segment_horizontal by fastforce
            then have "x \<in> l" using "*" assms(12) by auto
            thus ?thesis using a_def assms(10) assms(9) l_def segment_horizontal by auto
          qed
          moreover have "x$2 = 0" using * assms(9) segment_horizontal by auto
          ultimately show "x \<in> {p0}" using a_def assms(9) segment_vertical by fastforce
        qed
        ultimately show ?thesis by auto
      qed
      moreover have "path_image ?R'
          = path_image ?l1 \<union> path_image ?l2 \<union> path_image ?l3 \<union> path_image ?l4 \<union> path_image ?l5"
        by (simp add: Un_assoc path_image_join)
      ultimately show ?thesis by fast
    qed
    moreover have "arc p"
      using a_def arc_simple_path assms(10) assms(7) p0 p0_def p1_def by fastforce
    ultimately show ?thesis
      by (metis (no_types, lifting) simple_path_join_loop_eq Int_commute dual_order.refl p0_def p1_def pathfinish_join pathfinish_linepath pathstart_join pathstart_linepath)
  qed

  have inside_outside: "inside_outside ?R (path_inside ?R) (path_outside ?R)"
    using closed simple Jordan_inside_outside_real2
    by (simp add: closed_path_def inside_outside_def path_inside_def path_outside_def)

  have interior_frontier: "path_inside ?R = interior (path_inside ?R)
      \<and> frontier (path_inside ?R) = path_image ?R"
    using inside_outside interior_open unfolding inside_outside_def by auto

  have "path_image q \<inter> path_image ?l1 \<subseteq> {p1}"
  proof(rule subsetI)
    fix x assume *: "x \<in> path_image q \<inter> path_image ?l1"
    then have "x$1 \<le> a" using a_def assms(10) assms(11) assms(9) l_def segment_horizontal by auto
    moreover have "x$1 \<ge> a"
      by (smt (z3) "*" Int_iff Un_iff a_def assms(9) b_x linepath_image_01 path_defs(4) segment_horizontal vector_2(1) vector_2(2))
    moreover have "x$2 = 0" using * assms(9) segment_horizontal by auto
    ultimately show "x \<in> {p1}" using a_def assms(9) segment_vertical by fastforce
  qed
  moreover have "path_image q \<inter> path_image ?l5 \<subseteq> {p0}"
  proof(rule subsetI)
    fix x assume *: "x \<in> path_image q \<inter> path_image ?l5"
    then have "x$1 \<le> 0"
      using R_x_a assms(9) p0_def pathstart_in_path_image segment_horizontal by fastforce
    moreover have "x$1 \<ge> 0"
      using "*" a_def assms(10) assms(11) assms(9) l_def segment_horizontal by auto
    moreover have "x$2 = 0" using * assms(9) segment_horizontal by auto
    ultimately show "x \<in> {p0}" using a_def assms(9) segment_vertical by fastforce
  qed
  moreover have ?thesis if "p1 \<in> path_image q \<inter> path_image ?l1" using p1_def that by blast
  moreover have ?thesis if "p0 \<in> path_image q \<inter> path_image ?l5" using p0_def that by blast
  moreover have ?thesis if
      q_int_l1: "path_image q \<inter> path_image ?l1 = {}" and
      q_int_l5: "path_image q \<inter> path_image ?l5 = {}"
  proof-
    have q_int_l2: "path_image q \<inter> path_image ?l2 = {}"
      using b_x segment_vertical by auto
    moreover have q_int_l3: "path_image q \<inter> path_image ?l3 = {}"
      using UnCI b_y segment_horizontal by auto
    moreover have q_int_l4: "path_image q \<inter> path_image ?l4 = {}"
      using a_x segment_vertical by auto
    moreover have ?thesis if "q0 \<in> path_image p" using q0_def that by blast
    moreover have "path_image q \<inter> path_image ?R \<noteq> {}" if "q0 \<notin> path_image p"
    proof-
      have "q0 \<in> path_outside ?R"
        (* take downward ray, show component is unbounded *)
      proof-
        let ?e2' = "(vector [0, -1])::(real^2)"
        let ?ray = "\<lambda>d. q0 + d *\<^sub>R ?e2'"
        have "\<not> (\<exists>d>0. ?ray d \<in> path_image ?R)"
        proof-
          have "\<forall>d>0. (?ray d)$2 < q0$2" by auto
          thus ?thesis using R_y_q0 by fastforce
        qed
        moreover have "bounded (path_inside ?R)" using bounded_finite_inside simple by blast
        moreover have "?e2' \<noteq> 0" by (metis vector_2(2) zero_index zero_neq_neg_one)
        ultimately have "q0 \<notin> path_inside ?R"
          using ray_to_frontier[of "path_inside ?R"] interior_frontier by metis
        moreover have "q0 \<notin> path_image ?R"
          using that q_int_l1 q_int_l2 q_int_l3 q_int_l4 q_int_l5
          by (simp add: disjoint_iff not_in_path_image_join pathstart_in_path_image q0_def)
        ultimately show ?thesis using inside_outside unfolding inside_outside_def by blast
      qed
      then have "q0 \<in> - (path_inside ?R)"
        by (metis ComplI IntI equals0D inside_Int_outside path_inside_def path_outside_def)
      moreover have "q1 \<in> path_inside ?R"
        (* take \<epsilon>-ball around the point on l3 directly above q1;
           it contains a point from the interior. Take line from this point to the q1. This line
           does not touch R, so q1 must also be in the interior of R by path-connectedness. *)
      proof-
        let ?e = "(vector [q1$1, b_y])::(real^2)"
        let ?d1 = "(vector [b_x, b_y])::(real^2)"
        let ?d2 = "(vector [a_x, b_y])::(real^2)"
        obtain \<epsilon> where \<epsilon>: "0 < \<epsilon> \<and> \<epsilon> < dist ?e q1 \<and> \<epsilon> < dist ?e ?d1 \<and> \<epsilon> < dist ?e ?d2"
        proof-
          have "?e \<noteq> q1"
            by (metis UnCI b_y order_less_irrefl pathfinish_in_path_image q1_def vector_2(2))
          moreover have "?e \<noteq> ?d1"
            by (smt (verit) UnCI b_x pathfinish_in_path_image q1_def vector_2(1))
          moreover have "?e \<noteq> ?d2"
            by (metis UnCI a_x order_less_irrefl pathfinish_in_path_image q1_def vector_2(1))
          ultimately have "0 < dist ?e q1 \<and> 0 < dist ?e ?d1 \<and> 0 < dist ?e ?d2" by simp
          then have "0 < Min {dist ?e q1, dist ?e ?d1, dist ?e ?d2}" by auto
          then obtain \<epsilon> where "0 < \<epsilon> \<and> \<epsilon> < Min {dist ?e q1, dist ?e ?d1, dist ?e ?d2}"
            by (meson field_lbound_gt_zero)
          thus ?thesis using that by auto
        qed
        then have "?e \<in> path_image ?l3"
          by (simp add: a_x b_x q1_def segment_horizontal less_eq_real_def pathfinish_in_path_image)
        then have "?e \<in> path_image ?R" by (simp add: p1_def path_image_join)
        then have "?e \<in> frontier (path_inside ?R)"
          using inside_outside unfolding inside_outside_def by blast
        then obtain int_p where int_p: "int_p \<in> ball ?e \<epsilon> \<and> int_p \<in> path_inside ?R"
          by (meson \<epsilon> inside_outside frontier_straddle mem_ball)
  
        have int_p_x: "a_x < int_p$1 \<and> int_p$1 < b_x"
          by (metis (mono_tags, lifting) dist_bound_1 UnI2 \<epsilon> a_x b_x dist_commute int_p pathfinish_in_path_image q1_def vector_2(1) vector_2(2))
        have "int_p$2 < b_y"
        proof(rule ccontr)
          have "int_p$2 \<noteq> b_y"
          proof-
            have "int_p$2 = b_y \<Longrightarrow> int_p \<in> path_image ?l3"
              using int_p_x by (simp add: segment_horizontal)
            moreover have "int_p \<in> path_image ?l3 \<Longrightarrow> int_p \<in> path_image ?R"
              by (simp add: p1_def path_image_join)
            moreover have "path_image ?R \<inter> path_inside ?R = {}"
              using inside_outside unfolding inside_outside_def by blast
            ultimately show ?thesis using int_p by fast
          qed
          moreover assume "\<not> int_p$2 < b_y"
          ultimately have *: "int_p$2 > b_y" by simp
  
          let ?e2 = "(vector [0, 1])::(real^2)"
          let ?ray = "\<lambda>d. int_p + d *\<^sub>R ?e2"
          have "\<not> (\<exists>d>0. ?ray d \<in> path_image ?R)"
          proof-
            have "\<forall>d>0. (?ray d)$2 > b_y" using * by auto
            thus ?thesis using R_y_b by fastforce
          qed
          moreover have "bounded (path_inside ?R)" using bounded_finite_inside simple by blast
          moreover have "?e2 \<noteq> 0" using e1e2_basis(4) by force
          ultimately have "int_p \<notin> path_inside ?R"
            using ray_to_frontier[of "path_inside ?R"] interior_frontier by metis
          thus False using int_p by blast
        qed
        moreover have "int_p$2 > q1$2"
        proof-
          have "dist int_p ?e < \<epsilon>" using \<epsilon> dist_commute_lessI int_p mem_ball by blast
          then have "dist (int_p$2) (?e$2) < \<epsilon>" by (smt (verit, best) dist_vec_nth_le)
          then have 1: "int_p$2 > ?e$2 - \<epsilon>" by (simp add: dist_real_def)
  
          have "q1$1 = ?e$1" by simp
          then have "dist q1 ?e = dist (q1$2) (?e$2)" using axis_dist by blast
          then have "q1$2 < ?e$2 - \<epsilon>"
            by (smt (verit) UnCI \<epsilon> b_y dist_commute dist_real_def pathfinish_in_path_image q1_def vector_2(2))
          moreover have "q1$2 < ?e$2" by (simp add: b_y pathfinish_in_path_image q1_def)
          moreover have "dist q1 ?e > \<epsilon>" by (metis \<epsilon> dist_commute)
          ultimately have "q1$2 < ?e$2 - \<epsilon>" by presburger
          thus ?thesis using 1 by force
        qed
        ultimately have int_p_y: "int_p$2 < b_y \<and> int_p$2 > q1$2" by blast
  
        let ?int_l = "linepath int_p q1"

        have "path_image ?int_l \<inter> path_image p = {}"
        proof-
          have "\<forall>x \<in> path_image p. (?int_l 0)$2 > x$2"
            by (smt (verit) int_p_y assms(14) linepath_0')
          moreover have "\<forall>x \<in> path_image p. (?int_l 1)$2 > x$2"
            by (simp add: assms(14) linepath_1')
          ultimately have "\<forall>x \<in> path_image p. \<forall>y \<in> path_image ?int_l. y$2 > x$2"
            by (metis assms(14) linepath_0' linepath_bound_2(1))
          thus ?thesis by blast
        qed
        moreover have "path_image ?int_l \<inter> path_image ?l1 = {}"
          by (smt (verit, best) assms(14) assms(9) disjoint_iff int_p_y linepath_int_rows p0_def pathstart_in_path_image vector_2(2))
        moreover have "path_image ?int_l \<inter> path_image ?l2 = {}"
          by (metis UnCI b_x int_p_x linepath_int_columns pathfinish_in_path_image q1_def vector_2(1))
        moreover have "path_image ?int_l \<inter> path_image ?l3 = {}"
          using int_p_y linepath_int_rows by auto
        moreover have "path_image ?int_l \<inter> path_image ?l4 = {}"
          by (metis UnCI a_x inf_commute int_p_x linepath_int_columns pathfinish_in_path_image q1_def vector_2(1))
        moreover have "path_image ?int_l \<inter> path_image ?l5 = {}"
          by (smt (verit, best) assms(14) assms(9) disjoint_iff int_p_y linepath_int_rows p0_def pathstart_in_path_image vector_2(2))
        ultimately have "path_image ?int_l \<inter> path_image ?R = {}"
          by (simp add: disjoint_iff not_in_path_image_join)
        then have "path_image ?int_l \<subseteq> path_inside ?R \<or> path_image ?int_l \<subseteq> path_outside ?R"
          by (smt (verit, ccfv_SIG) convex_imp_path_connected convex_segment(1) disjoint_insert(1) insert_Diff inside_outside_def int_p linepath_image_01 local.inside_outside path_connected_not_frontier_subset path_defs(4) pathstart_in_path_image pathstart_linepath)
        moreover have "?int_l 0 = int_p \<and> int_p \<in> path_inside ?R"
          using int_p by (simp add: linepath_0')
        ultimately have "path_image ?int_l \<subseteq> path_inside ?R"
          using inside_outside_def local.inside_outside by auto
        thus ?thesis by auto
      qed
      ultimately have "path_image q \<inter> - (path_inside ?R) \<noteq> {} \<and> path_image q \<inter> (path_inside ?R) \<noteq> {}"
        unfolding q0_def q1_def by fast
      moreover have "path_connected (path_image q)"
        by (simp add: assms(8) path_connected_path_image simple_path_imp_path)
      moreover have "path_image ?R = frontier (path_inside ?R)"
        using inside_outside unfolding inside_outside_def p0_def path_inside_def by auto
      ultimately show ?thesis by (metis Diff_eq Diff_eq_empty_iff path_connected_not_frontier_subset)
    qed
    ultimately show ?thesis 
      by (smt (verit, ccfv_threshold) disjoint_iff_not_equal not_in_path_image_join q_int_l1 q_int_l5)
  qed
  ultimately show ?thesis by auto
qed

lemma pocket_fill_line_int_aux2:
  fixes p q :: "R_to_R2"
  fixes A :: "(real^2) set"
  defines "p0 \<equiv> pathstart p"
  defines "p1 \<equiv> pathfinish p"
  defines "a \<equiv> p1$1"
  defines "l \<equiv> closed_segment p0 p1"
  assumes "simple_path p"
  assumes "p0$1 = 0 \<and> p0$2 = 0 \<and> p1$2 = 0"
  assumes "a > 0"
  assumes "convex A \<and> compact A"
  assumes "{p0, p1} \<subseteq> frontier A"
  assumes "p ` {0<..<1} \<subseteq> interior A"
  shows "path_image p \<inter> {x. x$2 = 0} \<subseteq> l"
proof-
  have l: "l = {x. x$2 = 0 \<and> x$1 \<in> {0..a}}"
    using horizontal_segment_at_0' a_def assms(6) assms(7) l_def by presburger
  have endpoints: "(p 0)$1 = 0 \<and> (p 0)$2 = 0 \<and> (p 1)$1 = a \<and> (p 1)$2 = 0"
    by (metis a_def assms(6) p0_def p1_def pathfinish_def pathstart_def)

  have False if *: "\<exists>t \<in> {0..1}. (p t)$2 = 0 \<and> ((p t)$1 > a \<or> (p t)$1 < 0)"
  proof-
    obtain t where "t \<in> {0<..<1} \<and> (p t)$2 = 0 \<and> ((p t)$1 > a \<or> (p t)$1 < 0)"
      by (metis * assms(7) endpoints atLeastAtMost_iff greaterThanLessThan_iff less_eq_real_def linorder_not_le)
    then obtain x where x: "x \<in> p`{0<..<1} \<and> x$2 = 0 \<and> (x$1 > a \<or> x$1 < 0)" by blast
    thus False
      using pocket_fill_line_int_aux[of p0 p1 x A]
      by (smt (verit, del_insts) Diff_iff a_def assms(10) assms(6) assms(7) assms(8) assms(9) empty_subsetI endpoints exhaust_2 frontier_def frontier_subset_compact insert_subset interior_subset p0_def pathstart_def subset_eq vec_eq_iff zero_index)
  qed
  then have "\<forall>t \<in> {0..1}. (p t)$2 = 0 \<longrightarrow> (p t)$1 \<in> {0..a}" by fastforce
  then have "\<forall>v \<in> path_image p. v$2 = 0 \<longrightarrow> v$1 \<in> {0..a}" by (simp add: imageE path_defs(4))
  thus ?thesis using l by blast
qed

lemma three_points_on_line:
  fixes a b :: "'a::real_vector"
  assumes "A = affine hull {a, b}"
  assumes "a \<noteq> b"
  assumes "{x, y, z} \<subseteq> A"
  assumes "x \<noteq> y \<and> y \<noteq> z \<and> x \<noteq> z"
  shows "x \<in> open_segment y z \<or> y \<in> open_segment x z \<or> z \<in> open_segment x y"
proof-
  let ?u = "b - a"

  have *: "\<And>\<alpha> \<beta> \<gamma>::real. \<alpha> \<in> open_segment \<beta> \<gamma>
      \<Longrightarrow> a + \<alpha> *\<^sub>R ?u \<in> open_segment (a + \<beta> *\<^sub>R ?u) (a + \<gamma> *\<^sub>R ?u)"
  proof-
    fix \<alpha> \<beta> \<gamma> :: real
    assume *: "\<alpha> \<in> open_segment \<beta> \<gamma>"

    define x where "x \<equiv> a + \<alpha> *\<^sub>R ?u"
    define y where "y \<equiv> a + \<beta> *\<^sub>R ?u"
    define z where "z \<equiv> a + \<gamma> *\<^sub>R ?u"

    obtain v where v: "\<alpha> = (1 - v) * \<beta> + v * \<gamma> \<and> v \<in> {0<..<1}"
      by (metis (no_types, lifting) "*" imageE in_segment(2) real_scaleR_def segment_image_interval(2))
    then have "x = a + ((1 - v) * \<beta> + v * \<gamma>) *\<^sub>R ?u" using x_def by blast
    also have "... = a + (((1 - v) * \<beta>) *\<^sub>R ?u) + ((v * \<gamma>) *\<^sub>R ?u)" by (simp add: scaleR_left.add)
    also have "... = a + ((1 - v) *\<^sub>R (\<beta> *\<^sub>R ?u)) + (v *\<^sub>R (\<gamma> *\<^sub>R ?u))" by simp
    also have "... = a + ((1 - v) *\<^sub>R (y - a)) + (v *\<^sub>R (z - a))" by (simp add: y_def z_def)
    also have "... = a + y - a - v *\<^sub>R (y - a) + v *\<^sub>R (z - a)" by (simp add: scaleR_left_diff_distrib)
    also have "... = y - v *\<^sub>R (y - a) + v *\<^sub>R (z - a)" by simp
    also have "... = y - (v *\<^sub>R y) + (v *\<^sub>R a) + (v *\<^sub>R z) - (v *\<^sub>R a)" by (simp add: scaleR_right_diff_distrib)
    also have "... = (1 - v) *\<^sub>R y + v *\<^sub>R z" by (metis add_diff_cancel diff_add_eq scaleR_collapse)
    finally have "x = (1 - v) *\<^sub>R y + v *\<^sub>R z" .
    moreover have "0 \<le> 1 - v \<and> 1 - v \<le> 1" using v by fastforce
    ultimately have "x \<in> closed_segment y z" using in_segment(1) by auto
    moreover have "x \<noteq> y \<and> x \<noteq> z"
      by (metis "*" add_diff_cancel_left' assms(2) eq_iff_diff_eq_0 in_open_segment_iff_line open_segment_commute open_segment_subsegment scaleR_right_imp_eq x_def y_def z_def)
    ultimately show "a + \<alpha> *\<^sub>R ?u \<in> open_segment (a + \<beta> *\<^sub>R ?u) (a + \<gamma> *\<^sub>R ?u)"
      unfolding open_segment_def using x_def y_def z_def by force
  qed

  obtain \<alpha> \<beta> \<gamma> where xyz: "x = a + \<alpha> *\<^sub>R ?u \<and> y = a + \<beta> *\<^sub>R ?u \<and> z = a + \<gamma> *\<^sub>R ?u"
    using affine_hull_2_alt[of a b] assms(1) assms(3) by auto
  then have "\<alpha> \<noteq> \<beta> \<and> \<beta> \<noteq> \<gamma> \<and> \<alpha> \<noteq> \<gamma>" using assms by blast
  moreover have "\<alpha> \<in> closed_segment \<beta> \<gamma> \<or> \<beta> \<in> closed_segment \<alpha> \<gamma> \<or> \<gamma> \<in> closed_segment \<alpha> \<beta>"
    by (metis atLeastAtMost_iff closed_segment_commute less_eq_real_def less_max_iff_disj linorder_not_less real_Icc_closed_segment)
  ultimately have "\<alpha> \<in> open_segment \<beta> \<gamma> \<or> \<beta> \<in> open_segment \<alpha> \<gamma> \<or> \<gamma> \<in> open_segment \<alpha> \<beta>"
    unfolding open_segment_def by fast
  thus ?thesis using * xyz by presburger
qed

lemma pocket_fill_line_int_aux3:
  fixes A :: "(real^2) set"
  assumes "convex A \<and> compact A"
  assumes "v \<noteq> 0"
  assumes "closed_segment 0 w \<subseteq> frontier A" (is "closed_segment ?a ?b \<subseteq> _")
  assumes "w \<bullet> v = 0"
  assumes "w \<noteq> 0"
  shows "(A \<subseteq> {x. x \<bullet> v \<le> 0} \<or> A \<subseteq> {x. x \<bullet> v \<ge> 0})" (is "A \<subseteq> ?P1 \<or> A \<subseteq> ?P2")
proof-
  have frontiers: "frontier ?P1 = frontier ?P2 \<and> frontier ?P1 \<subseteq> ?P2 \<and> frontier ?P2 \<subseteq> ?P1"
    by (smt (verit, ccfv_threshold) Collect_mono assms(2) frontier_halfspace_component_ge frontier_halfspace_le inner_commute subset_antisym)
  have frontier: "frontier ?P1 = {x. x \<bullet> v = 0}"
    by (simp add: assms(2) frontier_halfspace_component_ge frontiers)

  have ?thesis if "interior A \<noteq> {}"
  proof-
    have "interior A \<subseteq> ?P1 \<or> interior A \<subseteq> ?P2"
    proof(rule ccontr)  
      assume "\<not> (interior A \<subseteq> ?P1 \<or> interior A \<subseteq> ?P2)"
      then obtain x y where xy: "x \<in> ((interior A) \<inter> ?P1) - ?P2 \<and> y \<in> ((interior A) \<inter> ?P2) - ?P1"
        by fastforce
      moreover have "x \<in> frontier ?P1 \<union> interior ?P1 \<and> y \<in> frontier ?P2 \<union> interior ?P2"
        by (metis DiffD1 IntD2 Un_Diff_cancel2 frontiers closure_Un_frontier frontier_def interior_subset sup.orderE xy)
      ultimately have xy': "x \<in> (interior A) \<inter> interior ?P1 \<and> y \<in> (interior A) \<inter> interior ?P2"
        using frontiers by blast
      then have "closed_segment x y \<inter> frontier ?P1 \<noteq> {}"
        by (metis (no_types, lifting) DiffD1 DiffD2 Int_iff convex_closed_segment convex_imp_path_connected empty_iff ends_in_segment(1) ends_in_segment(2) in_mono path_connected_not_frontier_subset xy)
      moreover have "closed_segment x y \<subseteq> interior A"
        by (metis convex_interior Int_iff assms(1) convex_contains_segment xy')
      ultimately obtain z where z: "z \<in> interior A \<inter> frontier ?P1" by blast

      have "closed_segment ?a ?b \<subseteq> frontier ?P1"
      proof(rule subsetI)
        fix x
        assume "x \<in> closed_segment ?a ?b"
        then obtain u where "x = (1 - u) *\<^sub>R ?a + u *\<^sub>R ?b \<and> 0 \<le> u \<and> u \<le> 1"
          unfolding closed_segment_def by blast
        then have "x \<bullet> v = u *\<^sub>R (?b \<bullet> v)" by simp
        moreover have "?b \<bullet> v = 0" by (simp add: assms(4))
        ultimately have "x \<bullet> v = 0" by simp
        thus "x \<in> frontier ?P1" using frontier by blast
      qed
      moreover have "z \<notin> closed_segment ?a ?b" using assms(3) frontier_def z by fastforce
      ultimately have "z \<in> frontier ?P1 - closed_segment ?a ?b" using z by blast
      moreover have "collinear {z, ?a, ?b}"
      proof-
        have "{z, ?a, ?b} \<subseteq> {x. x \<bullet> v = 0}"
          using \<open>{0--w} \<subseteq> frontier {x. x \<bullet> v \<le> 0}\<close> frontier z by auto
        moreover have "{x. x \<bullet> v = 0} = affine hull {?a, ?b}"
          by (metis (no_types, lifting) Collect_mono assms(2) assms(5) calculation halfplane_frontier_affine_hull inner_commute insert_subset subset_antisym)
        ultimately show ?thesis using collinear_affine_hull by auto
      qed
      ultimately have "?a \<in> open_segment z ?b \<or> ?b \<in> open_segment z ?a"
        using three_points_on_line[of "{x. x \<bullet> v = 0}"]
        by (smt (z3) \<open>z \<notin> {0--w}\<close> assms(5) collinear_3_imp_in_affine_hull ends_in_segment(1) ends_in_segment(2) hull_redundant hull_subset insert_commute open_closed_segment three_points_on_line)
      moreover have "open_segment z ?b \<subseteq> interior A \<and> open_segment z ?a \<subseteq> interior A"
      proof-
        have "closed_segment z ?b \<subseteq> A \<and> closed_segment z ?a \<subseteq> A"
          by (meson IntD1 assms(1) assms(3) closed_segment_subset ends_in_segment(1) ends_in_segment(2) frontier_subset_compact in_mono interior_subset z)
        then have "rel_interior (closed_segment z ?b) \<subseteq> interior A
            \<and> rel_interior (closed_segment z ?a) \<subseteq> interior A"
          by (metis IntD1 \<open>z \<notin> {0--w}\<close> assms(1) closure_convex_hull convex_hull_eq in_interior_closure_convex_segment order_class.order_eq_iff rel_interior_closed_segment subsetD subset_closed_segment z)
        moreover have "rel_interior (closed_segment z ?b) = open_segment z ?b
            \<and> rel_interior (closed_segment z ?a) = open_segment z ?a"
          by (metis \<open>z \<notin> {0--w}\<close> closed_segment_commute ends_in_segment(1) rel_interior_closed_segment)
        ultimately show ?thesis by force
      qed
      ultimately have "?a \<in> interior A \<or> ?b \<in> interior A" by fast
      thus False using assms(3) frontier_def by auto
    qed
    then have "closure (interior A) \<subseteq> closure ?P1 \<or> closure (interior A) \<subseteq> closure ?P2"
      using closure_mono by blast
    moreover have "closed ?P1 \<and> closed ?P2"
      by (simp add: closed_halfspace_component_ge closed_halfspace_component_le)
    moreover have "closure (interior A) = A"
      using assms(1)
      by (simp add: compact_imp_closed convex_closure_interior that)
    ultimately show ?thesis using closure_closed by auto
  qed
  moreover have ?thesis if "interior A = {}"
  proof(rule ccontr)
    assume "\<not> (A \<subseteq> ?P1 \<or> A \<subseteq> ?P2)"
    then obtain x y where xy: "x \<in> (A \<inter> ?P1) - ?P2 \<and> y \<in> (A \<inter> ?P2) - ?P1" by fastforce
    moreover have "x \<in> frontier ?P1 \<union> interior ?P1 \<and> y \<in> frontier ?P2 \<union> interior ?P2"
      by (metis DiffD1 IntD2 Un_Diff_cancel2 frontiers closure_Un_frontier frontier_def interior_subset sup.orderE xy)
    ultimately have xy': "x \<in> A \<inter> interior ?P1 \<and> y \<in> A \<inter> interior ?P2" using frontiers by blast
    have "\<not> collinear {?a, ?b, x, y}"
    proof(rule ccontr)
      assume "\<not> \<not> collinear {?a, ?b, x, y}"
      then have *: "collinear {?a, ?b, x, y}" by blast
      then have "{?a, ?b, x, y} \<subseteq> affine hull {?a, ?b}"
        by (metis assms(5) collinear_3_imp_in_affine_hull collinear_4_3 hull_subset insert_subset)
      moreover have "affine hull {?a, ?b} = {x. x \<bullet> v = 0}"
        by (smt (verit) DiffE * assms(2) assms(4) assms(5) collinear_3_imp_in_affine_hull collinear_4_3 halfplane_frontier_affine_hull inner_commute mem_Collect_eq xy)
      moreover have "... = frontier ?P1 \<and> ... = frontier ?P2"
        using frontiers assms(2) frontier_halfspace_component_ge by blast
      ultimately show False using frontiers xy by auto
    qed
    then obtain c1 c2 c3 where c123: "\<not> collinear {c1, c2, c3} \<and> {c1, c2, c3} \<subseteq> {?a, ?b, x, y}"
      by (metis assms(5) collinear_4_3 insert_mono subset_insertI)
    then have "interior (convex hull {c1, c2, c3}) \<noteq> {}"
      by (metis Jordan_inside_outside_real2 closed_path_def make_triangle_def path_inside_def polygon_def polygon_of_def triangle_inside_is_convex_hull_interior triangle_is_polygon)
    moreover have "{c1, c2, c3} \<subseteq> A"
      by (smt (verit, del_insts) c123 xy' assms(1) assms(3) empty_subsetI frontier_subset_compact in_mono inf.orderE insert_absorb insert_mono le_infE subsetI subset_closed_segment)
    ultimately have "interior A \<noteq> {}"
      by (metis assms(1) interior_mono subset_empty subset_hull)
    thus False using that by blast
  qed
  ultimately show ?thesis by blast
qed

lemma pocket_fill_line_int_aux4:
  fixes p q :: "R_to_R2"
  fixes A :: "(real^2) set"
  defines "p0 \<equiv> pathstart p"
  defines "p1 \<equiv> pathfinish p"
  defines "q0 \<equiv> pathstart q"
  defines "q1 \<equiv> pathfinish q"
  defines "a \<equiv> p1$1"
  defines "l \<equiv> closed_segment p0 p1"
  assumes "simple_path p"
  assumes "simple_path q"
  assumes "path_image p \<inter> path_image q = {}"
  assumes "p0$1 = 0 \<and> p0$2 = 0 \<and> p1$2 = 0"
  assumes "a > 0"
  assumes "\<forall>v \<in> path_image p. q0$2 \<le> v$2"
  assumes "\<forall>v \<in> path_image p. q1$2 > v$2"
  assumes "convex A \<and> compact A"
  assumes "{p0, p1} \<subseteq> frontier A"
  assumes "p`{0<..<1} \<subseteq> interior A"
  assumes "path_image q \<subseteq> A"
  shows "l \<subseteq> frontier A" "\<forall>x \<in> (path_image p) \<union> (path_image q). x$2 \<ge> 0" "q0$2 = 0"
proof-
  have l: "l = {x. x$2 = 0 \<and> x$1 \<in> {0..a}}"
    using horizontal_segment_at_0' a_def assms(10) assms(11) l_def by presburger
  have endpoints: "(p 0)$1 = 0 \<and> (p 0)$2 = 0 \<and> (p 1)$1 = a \<and> (p 1)$2 = 0"
    by (metis a_def assms(10) p0_def p1_def pathfinish_def pathstart_def)

  have "l \<subseteq> frontier A" if "\<not> (path_image q \<inter> {x. x$2 = 0} \<subseteq> l)"
  proof-
    from that obtain x where "x \<in> path_image q \<inter> {x. x$2 = 0} \<and> (x$1 < 0 \<or> x$1 > a)"
      by (smt (verit) Int_Collect a_def assms(10) endpoints l_def p0_def pathstart_def segment_horizontal subsetI)
    thus ?thesis
      using pocket_fill_line_int_aux[of p0 p1 x A] unfolding l_def
      by (smt (verit, del_insts) IntD2 Int_commute a_def assms(11) assms(14) assms(15) assms(17) assms(10) endpoints exhaust_2 frontier_subset_compact insert_subset mem_Collect_eq p0_def pathstart_def subset_eq vec_eq_iff zero_index)
  qed
  moreover have False if "(path_image q \<inter> {x. x$2 = 0} \<subseteq> l)"
  proof-
    have "(path_image p \<inter> {x. x$2 = 0} \<subseteq> l)"
      using pocket_fill_line_int_aux2
      by (metis a_def assms(10) assms(11) assms(14) assms(15) assms(16) assms(7) l_def p0_def p1_def)
    then have "path_image p \<inter> path_image q \<noteq> {}"
      using pocket_fill_line_int_aux1
      by (metis (mono_tags, lifting) assms(11) assms(12) assms(13) assms(7) assms(8) endpoints l_def p0_def p1_def pathfinish_def pathstart_def q0_def q1_def that)
    thus False by (simp add: assms(9))
  qed
  ultimately show *: "l \<subseteq> frontier A" by blast

  show "\<forall>x \<in> (path_image p) \<union> (path_image q). x$2 \<ge> 0"
  proof(rule ccontr)
    assume "\<not> (\<forall>x \<in> (path_image p) \<union> (path_image q). x$2 \<ge> 0)"
    then have "\<exists>x \<in> (path_image p) \<union> (path_image q). x$2 < 0" using linorder_not_le by blast
    then obtain x where x: "x \<in> ((path_image p) \<union> (path_image q)) \<inter> A \<and> x$2 < 0"
      using assms(12) assms(17) pathstart_in_path_image q0_def by fastforce

    let ?v = "(vector [0, 1])::(real^2)"
    have 1: "?v \<noteq> 0" by (simp add: e1e2_basis(3))
    have 2: "closed_segment 0 p1 \<subseteq> frontier A"
      by (smt (verit, del_insts) * Int_closed_segment closed_segment_eq doubleton_eq_iff endpoints l_def p0_def pathstart_def segment_vertical zero_index)
    have 3: "p1 \<bullet> ?v = 0" by (metis assms(10) cart_eq_inner_axis e1e2_basis(3))
    have 4: "p1 \<noteq> 0" using a_def assms(11) by force
    have *: "(A \<subseteq> {x. x \<bullet> ?v \<le> 0} \<or> A \<subseteq> {x. x \<bullet> ?v \<ge> 0})"
      using pocket_fill_line_int_aux3[OF assms(14) 1 2 3 4] by blast
    moreover have "q1$2 > 0" using assms(10) assms(13) p0_def pathstart_in_path_image by fastforce
    ultimately show False
      by (metis (no_types, lifting) IntE x assms(17) e1e2_basis(3) inner_axis linorder_not_less mem_Collect_eq pathfinish_in_path_image q1_def real_inner_1_right subsetD)
  qed
  moreover have "q0$2 \<le> 0" using assms(10) assms(12) p1_def by force
  moreover have "q0 \<in> (path_image p) \<union> (path_image q)"
    by (simp add: pathstart_in_path_image q0_def)
  ultimately show "q0$2 = 0" by force
qed

(* slight generalization of aux4*)
lemma pocket_fill_line_int_aux5:
  fixes p q :: "R_to_R2"
  fixes A :: "(real^2) set"
  defines "p0 \<equiv> pathstart p"
  defines "p1 \<equiv> pathfinish p"
  defines "q0 \<equiv> pathstart q"
  defines "q1 \<equiv> pathfinish q"
  defines "a \<equiv> p1$1"
  defines "l \<equiv> closed_segment p0 p1"
  assumes "simple_path p"
  assumes "simple_path q"
  assumes "path_image p \<inter> path_image q = {q0, q1}"
  assumes "p0$1 = 0 \<and> p0$2 = 0 \<and> p1$2 = 0"
  assumes "a > 0"
  assumes "A = convex hull (path_image p \<union> path_image q)"
  assumes "{p0, p1} \<subseteq> frontier A"
  assumes "p`{0<..<1} \<subseteq> interior A"
  assumes "path_image q \<subseteq> A"
  assumes "\<exists>x \<in> p`{0<..<1}. x$2 \<ge> 0" (* wlog; if not the case, we flip across x axis *)
  assumes "q0 = p1 \<and> q1 = p0"
  shows "l \<subseteq> frontier A" "\<forall>x \<in> path_image p \<union> path_image q. x$2 \<ge> 0"
proof-
  have 1: "l \<subseteq> frontier A" if "\<forall>x \<in> path_image p \<union> path_image q. x$2 \<ge> 0"
  proof-
    have "\<forall>x \<in> path_image p \<union> path_image q. x \<bullet> (vector [0, 1]) \<ge> 0"
      by (simp add: e1e2_basis(3) inner_axis that)
    then have "\<forall>x \<in> A. x \<bullet> (vector [0, 1]) \<ge> 0" 
      by (smt (verit, ccfv_threshold) convex_cut_aux' assms(12) inner_commute mem_Collect_eq subset_eq)
    then have "A \<subseteq> {x. x \<bullet> (vector [0, 1]) \<ge> 0}" by blast
    moreover have "frontier {x. x \<bullet> ((vector [0, 1])::(real^2)) \<ge> 0} = {x. x \<bullet> (vector [0, 1]) = 0}"
      by (metis dual_order.refl frontier_halfspace_component_ge not_one_le_zero vector_2(2) zero_index)
    moreover have "l \<subseteq> {x. x \<bullet> (vector [0, 1]) = 0}"
    proof-
      have "\<forall>x \<in> l. x$2 = 0" using assms(10) l_def segment_horizontal by presburger
      thus ?thesis by (simp add: cart_eq_inner_axis e1e2_basis(3) subset_eq)
    qed
    ultimately show ?thesis
      by (smt (verit, best) Un_upper1 assms(12) closed_segment_subset convex_convex_hull hull_subset in_frontier_in_subset l_def p0_def p1_def pathfinish_in_path_image pathstart_in_path_image subset_eq)
  qed
  have 2: False if tht: "\<not> (\<forall>x \<in> (path_image p) \<union> (path_image q). x$2 \<ge> 0)"
  proof-
    obtain x tx where x: "tx \<in> {0..1} \<and> q tx = x \<and> (\<forall>z \<in> path_image p. x$2 < z$2)"
      using exists_point_below_all[of p q] that
      by (smt (verit, del_insts) tht assms(10) assms(12) assms(14) assms(7) assms(8) image_iff p0_def p1_def path_image_def pathfinish_def pathstart_def simple_path_imp_path)
    obtain y ty where y: "ty \<in> {0..1} \<and> q ty = y \<and> (\<forall>x \<in> path_image p. y$2 > x$2)"
      using exists_point_above_all[of p q]
      by (smt (verit, del_insts) assms(10) assms(12) assms(14) assms(16) assms(7) assms(8) image_iff p0_def p1_def path_image_def pathfinish_def pathstart_def simple_path_imp_path)

    let ?Q =
      "\<lambda>q'. simple_path q' \<and> path_image p \<inter> path_image q' = {}
        \<and> q' 0 = q tx \<and> q' 1 = q ty
        \<and> path_image q' \<subseteq> path_image q"
    have *: "\<And>q'. ?Q q' \<Longrightarrow> False"
    proof-
      fix q'
      assume *: "?Q q'"

      have 2: "simple_path q'" by (simp add: *)
      have 3: "path_image p \<inter> path_image q' = {}" by (simp add: *)
      have 6: "\<forall>v\<in>path_image p. pathstart q' $ 2 \<le> v $ 2"
        by (simp add: * less_eq_real_def pathstart_def x)
      have 7: "\<forall>v\<in>path_image p. v $ 2 < pathfinish q' $ 2" by (simp add: * pathfinish_def y)
      have 11: "path_image q' \<subseteq> A" using * assms(15) by blast
      have "\<forall>x \<in> (path_image p) \<union> (path_image q'). x$2 \<ge> 0"
        using pocket_fill_line_int_aux4(2)[of p, OF _ 2 3 _ _ 6 7 _ _ _ 11]
        by (metis a_def assms(10) assms(11) assms(12) assms(13) assms(14) assms(7) assms(8) compact_Un compact_convex_hull compact_simple_path_image convex_convex_hull p0_def p1_def)
      thus False
        by (smt (verit) "*" UnCI assms(10) p0_def pathstart_def pathstart_in_path_image x)
    qed

    have lf: "(\<forall>t \<in> {0..1}. (q t = q0 \<or> q t = q1) \<longrightarrow> (t = 0 \<or> t = 1))"
      using assms(8)
      unfolding q0_def q1_def simple_path_def loop_free_def pathstart_def pathfinish_def
      by fastforce
    have endpoints: "q tx \<noteq> q0 \<and> q ty \<noteq> q0 \<and> q tx \<noteq> q1 \<and> q ty \<noteq> q1"
      by (metis x y assms(10) assms(17) order_less_le p0_def pathstart_in_path_image)

    have tx_neq_ty: "tx \<noteq> ty" using pathstart_in_path_image x y by fastforce
    moreover have False if "tx < ty"
    proof-
      have "path_image p \<inter> path_image (subpath tx ty q) = {}"
        (is "path_image p \<inter> path_image ?q' = {}")
      proof-
        have "q0 \<notin> path_image ?q' \<and> q1 \<notin> path_image ?q'"
        proof-
          have "{tx..ty} \<subseteq> {0..1}" using x y by simp
          then have "(\<forall>t \<in> {tx..ty}. (q t = q0 \<or> q t = q1) \<longrightarrow> (t = 0 \<or> t = 1))" using lf by blast
          moreover have "0 \<notin> {tx..ty} \<and> 1 \<notin> {tx..ty}"
            by (metis atLeastAtMost_iff dual_order.eq_iff endpoints pathfinish_def pathstart_def q0_def q1_def x y)
          moreover have "path_image ?q' = q`{tx..ty}" by (simp add: path_image_subpath that)
          ultimately show ?thesis by fastforce
        qed
        thus ?thesis
          by (smt (verit, best) Int_empty_right Int_insert_right_if0 assms(9) boolean_algebra_cancel.inf2 inf.absorb_iff1 path_image_subpath_subset x y)
      qed
      thus ?thesis using *[of ?q']
        by (metis assms(8) tx_neq_ty path_image_subpath_subset pathfinish_def pathfinish_subpath pathstart_def pathstart_subpath simple_path_subpath x y)
    qed
    moreover have False if "ty < tx"
    proof-
      have "path_image p \<inter> path_image (reversepath (subpath tx ty q)) = {}"
        (is "path_image p \<inter> path_image ?q' = {}")
      proof-
        have "q0 \<notin> path_image ?q' \<and> q1 \<notin> path_image ?q'"
        proof-
          have "{ty..tx} \<subseteq> {0..1}" using x y by simp
          then have "(\<forall>t \<in> {ty..tx}. (q t = q0 \<or> q t = q1) \<longrightarrow> (t = 0 \<or> t = 1))" using lf by blast
          moreover have "0 \<notin> {ty..tx} \<and> 1 \<notin> {ty..tx}"
            by (metis atLeastAtMost_iff dual_order.eq_iff endpoints pathfinish_def pathstart_def q0_def q1_def x y)
          moreover have "path_image ?q' = q`{ty..tx}"
            by (simp add: path_image_subpath reversepath_subpath that)
          ultimately show ?thesis by fastforce
        qed
        thus ?thesis
          by (smt (verit) Int_commute assms(9) inf.absorb_iff2 inf.assoc inf_bot_right insert_disjoint(2) path_image_reversepath path_image_subpath_subset x y)
      qed
      thus ?thesis using *[of ?q']
        by (metis "*" assms(8) tx_neq_ty path_image_subpath_commute path_image_subpath_subset pathfinish_def pathfinish_subpath pathstart_def pathstart_subpath reversepath_subpath simple_path_subpath x y)
    qed
    ultimately show False by fastforce
  qed
  show "l \<subseteq> frontier A" "\<forall>x \<in> (path_image p) \<union> (path_image q). x$2 \<ge> 0"
    using 1 2 apply blast
    using 1 2 by blast
qed

lemma pocket_fill_line_int_aux6:
  fixes p q :: "R_to_R2"
  defines "p0 \<equiv> pathstart p"
  defines "p1 \<equiv> pathfinish p"
  defines "q0 \<equiv> pathstart q"
  defines "q1 \<equiv> pathfinish q"
  defines "a \<equiv> p1$1"
  assumes "simple_path p"
  assumes "simple_path q"
  assumes "p0 = 0 \<and> p1$2 = 0"
  assumes "a > 0"
  assumes "q0$1 \<in> {0..a} \<and> q0$2 = 0"
  assumes "\<forall>x \<in> path_image p. q1$2 > x$2"
  assumes "\<forall>x \<in> path_image p \<union> path_image q. x$2 \<ge> 0"
  shows "path_image p \<inter> path_image q \<noteq> {}"
proof-
  let ?l1 = "linepath p1 (vector [a, -1])"
  let ?l2 = "linepath ((vector [a, -1])::(real^2)) (vector [0, -1])"
  let ?l3 = "linepath ((vector [0, -1])::(real^2)) 0"

  let ?R' = "?l1 +++ ?l2 +++ ?l3"
  let ?R = "p +++ ?R'"

  have closed: "closed_path ?R"
  proof-
    have "path ?R" using assms(6) p1_def simple_path_imp_path by auto
    moreover have "pathstart ?R = pathstart p" by simp
    moreover have "pathfinish ?R = pathfinish ?l3" by simp
    moreover have "pathstart p = 0" using assms(8) p0_def by fastforce
    moreover have "pathfinish ?l3 = 0" by simp
    ultimately show ?thesis unfolding closed_path_def by presburger
  qed
  have simple: "simple_path ?R"
  proof-
    have "arc ?R'"
    proof-
      let ?a = "p1"
      let ?b = "(vector [a, -1])::(real^2)"
      let ?c = "(vector [0, -1])::(real^2)"
      let ?d = "0::(real^2)"

      have arcs: "arc ?l1 \<and> arc ?l2 \<and> arc ?l3"
        by (metis arc_linepath assms(8) assms(9) vector_2(1) vector_2(2) verit_comp_simplify1(1) zero_index zero_neq_neg_one)

      have l2l3: "path_image ?l2 \<inter> path_image ?l3 = {pathfinish ?l2}"
        using linepath_int_corner[of ?b ?c ?d]
        by (metis Int_commute closed_segment_commute linepath_int_corner path_image_linepath pathfinish_linepath vector_2(2) zero_index zero_neq_neg_one)
      have l1l2: "path_image ?l1 \<inter> path_image ?l2 = {pathfinish ?l1}"
        using linepath_int_corner[of ?a ?b ?c] by (simp add: assms(8))
      have l1l3: "path_image ?l1 \<inter> path_image ?l3 = {}"
        using linepath_int_vertical[of ?a ?b ?c ?d] a_def assms(9) linepath_int_vertical by auto

      have "path_image ?l2 \<inter> path_image ?l3 = {pathfinish ?l2}"
        using l2l3 by blast
      moreover have sf_23: "pathfinish ?l2 = pathstart ?l3" by simp
      ultimately have "arc (?l2 +++ ?l3)"
        by (metis arc_join_eq_alt arcs)
      moreover have "path_image ?l1 \<inter> path_image (?l2 +++ ?l3) = {pathfinish ?l1}"
        using l1l2 l1l3
        by (metis (no_types, lifting) Int_Un_distrib sf_23 insert_is_Un path_image_join)
      moreover have "pathfinish ?l1 = pathstart (?l2 +++ ?l3)" by simp
      ultimately show "arc (?l1 +++ ?l2 +++ ?l3)" 
        by (metis arc_join_eq_alt arcs)
    qed
    moreover have "loop_free p" using assms(6) simple_path_def by blast
    moreover have "path_image ?R' \<inter> path_image p = {p0, p1}"
    proof-
      have "path_image ?l1 \<inter> path_image p = {p1}"
      proof-
        have "\<forall>x \<in> path_image p. x$2 \<ge> 0" by (simp add: assms(12))
        moreover have "\<forall>x \<in> path_image ?l1. x$2 \<le> 0" using a_def assms(8) segment_vertical by force
        ultimately have "\<forall>x \<in> path_image p \<inter> path_image ?l1. x$2 = 0" by fastforce
        moreover have "\<forall>x \<in> path_image ?l1. x$2 = 0 \<longrightarrow> x = p1"
          by (metis (mono_tags, opaque_lifting) a_def assms(8) exhaust_2 path_image_linepath segment_vertical vec_eq_iff vector_2(1))
        ultimately have "\<forall>x \<in> path_image p \<inter> path_image ?l1. x = p1" by fast
        moreover have "p1 \<in> path_image ?l1 \<and> p1 \<in> path_image p" using p1_def by auto
        ultimately show ?thesis by blast
      qed
      moreover have "path_image ?l2 \<inter> path_image p = {}"
        by (smt (verit, best) segment_horizontal assms(12) UnCI disjoint_iff path_image_linepath vector_2(2))
      moreover have "path_image ?l3 \<inter> path_image p = {p0}"
      proof-
        have "\<forall>x \<in> path_image p. x$2 \<ge> 0" by (simp add: assms(12))
        moreover have "\<forall>x \<in> path_image ?l3. x$2 \<le> 0" using a_def assms(8) segment_vertical by force
        ultimately have "\<forall>x \<in> path_image p \<inter> path_image ?l3. x$2 = 0" by fastforce
        moreover have "\<forall>x \<in> path_image ?l3. x$2 = 0 \<longrightarrow> x = p0"
          by (metis (no_types, opaque_lifting) assms(8) exhaust_2 path_image_linepath segment_vertical vec_eq_iff vector_2(1) zero_index)
        ultimately have "\<forall>x \<in> path_image p \<inter> path_image ?l3. x = p0" by fast
        moreover have "p0 \<in> path_image ?l3 \<and> p0 \<in> path_image p" using assms(8) p0_def by fastforce
        ultimately show ?thesis by blast
      qed
      ultimately show ?thesis
        by (smt (verit, del_insts) Int_Un_distrib Int_commute Un_assoc Un_insert_right insert_is_Un path_image_join pathfinish_linepath pathstart_join pathstart_linepath)
    qed
    moreover have "arc p"
      using closed_path_def arc_distinct_ends assms(6) calculation(1) closed p1_def simple_path_imp_arc
      by force
    ultimately show ?thesis
      by (metis (no_types, opaque_lifting) Int_commute closed_path_def closed dual_order.refl linepath_0' p0_def p1_def pathfinish_join pathstart_def pathstart_join simple_path_join_loop_eq)
  qed

  have inside_outside: "inside_outside ?R (path_inside ?R) (path_outside ?R)"
    using closed simple Jordan_inside_outside_real2
    by (simp add: closed_path_def inside_outside_def path_inside_def path_outside_def)

  have interior_frontier: "path_inside ?R = interior (path_inside ?R)
      \<and> frontier (path_inside ?R) = path_image ?R"
    using inside_outside interior_open unfolding inside_outside_def by auto

  have R_y_q1: "\<forall>x \<in> path_image ?R. x$2 < q1$2"
  proof-
    have *: "\<forall>x \<in> path_image p. x$2 < q1$2" using assms(11) by blast
    moreover have "\<forall>x \<in> path_image ?l1. x$2 < q1$2"
      using a_def assms(8) * p1_def pathfinish_in_path_image segment_vertical by fastforce
    moreover have "\<forall>x \<in> path_image ?l2. x$2 < q1$2"
      using assms(8) * p1_def pathfinish_in_path_image segment_horizontal by fastforce
    moreover have "\<forall>x \<in> path_image ?l3. x$2 < q1$2"
      using assms(8) * p1_def pathfinish_in_path_image segment_vertical by fastforce
    ultimately show ?thesis by (metis not_in_path_image_join)
  qed
  have R_y_0: "\<forall>x \<in> path_image ?R. x$2 \<ge> -1"
  proof-
    have "\<forall>x \<in> path_image ?l1. x$2 \<ge> -1" using a_def assms(8) segment_vertical by fastforce
    moreover have "\<forall>x \<in> path_image ?l2. x$2 \<ge> -1" using segment_horizontal by auto
    moreover have "\<forall>x \<in> path_image ?l3. x$2 \<ge> -1" using segment_vertical by auto
    moreover have "\<forall>x \<in> path_image p. x$2 \<ge> -1" using assms(12) by force
    ultimately show ?thesis by (metis not_in_path_image_join)
  qed

  have ?thesis if "p0 \<in> path_image q \<or> p1 \<in> path_image q" using p0_def p1_def that by blast
  moreover have ?thesis if "p0 \<notin> path_image q \<and> p1 \<notin> path_image q \<and> q0 \<notin> path_image p"
  proof-
    have q_int_l1: "path_image q \<inter> path_image ?l1 = {}"
    proof-
      have "\<forall>x \<in> path_image q. x$2 \<ge> 0" by (simp add: assms(12))
      moreover have "\<forall>x \<in> path_image ?l1. x$2 = 0 \<longrightarrow> x = p1"
        by (metis (mono_tags, opaque_lifting) a_def assms(8) exhaust_2 path_image_linepath segment_vertical vec_eq_iff vector_2(1))
      ultimately show ?thesis using that a_def assms(8) segment_vertical by fastforce
    qed
    moreover have q_int_l2: "path_image q \<inter> path_image ?l2 = {}"
      by (smt (verit, ccfv_threshold) UnCI assms(12) disjoint_iff path_image_linepath segment_horizontal vector_2(2))
    moreover have q_int_l3: "path_image q \<inter> path_image ?l3 = {}"
    proof-
      have "\<forall>x \<in> path_image q. x$2 \<ge> 0" by (simp add: assms(12))
      moreover have "\<forall>x \<in> path_image ?l3. x$2 = 0 \<longrightarrow> x = p0"
        by (metis (no_types, opaque_lifting) assms(8) exhaust_2 path_image_linepath segment_vertical vec_eq_iff vector_2(1) zero_index)
      ultimately show ?thesis using that a_def assms(8) segment_vertical by fastforce
    qed
    ultimately have q0_notin_R: "q0 \<notin> path_image ?R"
      using that by (simp add: disjoint_iff not_in_path_image_join pathstart_in_path_image q0_def)

    have "path_image q \<inter> path_image ?R \<noteq> {}"
    proof-
      have "q0 \<in> path_inside ?R"
      proof-
        let ?e = "(vector [q0$1, -1])::(real^2)"
        let ?d1 = "(vector [a, -1])::(real^2)"
        let ?d2 = "(vector [0, -1])::(real^2)"

        have "0 < q0$1 \<and> q0$1 < a"
          by (smt (verit) a_def assms(10) assms(8) atLeastAtMost_iff exhaust_2 linorder_not_less pathstart_in_path_image q0_def that vec_eq_iff zero_index)
        then have "q0$1 > 0 \<and> a - q0$1 > 0" by simp
        then have "min (min (q0$1) (a - q0$1)) 1 > 0" (is "?\<epsilon>' > 0") by linarith
        then have "0 < ?\<epsilon>'/2 \<and> ?\<epsilon>'/2 < 1 \<and> ?\<epsilon>'/2 < q0$1 \<and> ?\<epsilon>'/2 < a - q0$1" by argo
        then obtain \<epsilon> where \<epsilon>: "0 < \<epsilon> \<and> \<epsilon> < 1 \<and> \<epsilon> < q0$1 \<and> \<epsilon> < a - q0$1" by blast
        moreover have "?e \<in> frontier (path_inside ?R)"
          by (smt (verit, del_insts) UnCI \<open>0 < q0 $ 1 \<and> 0 < a - q0 $ 1\<close> interior_frontier p1_def path_image_join path_image_linepath pathfinish_linepath pathstart_join pathstart_linepath segment_horizontal vector_2(1) vector_2(2))
        ultimately obtain int_p where int_p: "int_p \<in> ball ?e \<epsilon> \<inter> path_inside ?R"
          by (meson inside_outside frontier_straddle mem_ball IntI)

        have int_p_x: "int_p$1 > 0 \<and> int_p$1 < a"
        proof-
          have "int_p$1 > 0"
          proof(rule ccontr)
            assume "\<not> int_p$1 > 0"
            moreover have "dist (int_p$1) (q0$1) < q0$1"
              by (smt (verit) IntE \<epsilon> dist_commute dist_vec_nth_le int_p mem_ball vector_2(1))
            ultimately show False using dist_real_def by force
          qed
          moreover have "int_p$1 < a"
          proof(rule ccontr)
            assume "\<not> int_p$1 < a"
            moreover have "dist (int_p$1) (q0$1) < a - q0$1"
              by (smt (verit) IntE \<epsilon> dist_commute dist_vec_nth_le int_p mem_ball vector_2(1))
            ultimately show False using dist_real_def by force
          qed
          ultimately show ?thesis by blast
        qed
        have int_p_y: "int_p$2 > -1 \<and> int_p$2 < 0"
        proof-
          have "int_p$2 > -1"
          proof(rule ccontr)
            assume *: "\<not> int_p$2 > -1"
            then have "int_p$2 \<le> -1" by simp
            let ?e2' = "(vector [0, -1])::(real^2)"
            let ?ray = "\<lambda>d. int_p + d *\<^sub>R ?e2'"
            have "\<not> (\<exists>d>0. ?ray d \<in> path_image ?R)"
            proof-
              have "\<forall>d>0. (?ray d)$2 < -1" using * by auto
              thus ?thesis using R_y_0 by force
            qed
            moreover have "bounded (path_inside ?R)" using bounded_finite_inside simple by blast
            moreover have "?e2' \<noteq> 0" by (metis vector_2(2) zero_index zero_neq_neg_one)
            ultimately have "int_p \<notin> path_inside ?R"
              using ray_to_frontier[of "path_inside ?R"] interior_frontier by metis
            thus False using int_p by blast
          qed
          moreover have "int_p$2 < 0"
          proof(rule ccontr)
            assume "\<not> int_p$2 < 0"
            then have "dist int_p ?e \<ge> 1"
              by (smt (verit, del_insts) dist_real_def dist_vec_nth_le vector_2(2))
            thus False by (smt (verit, del_insts) IntD1 \<epsilon> dist_commute int_p mem_ball)
          qed
          ultimately show ?thesis by blast
        qed
        
        let ?int_l = "linepath int_p q0"

        have "path_image ?int_l \<inter> path_image ?l1 = {}"
          using \<open>0 < q0 $ 1 \<and> q0 $ 1 < a\<close> a_def int_p_x linepath_int_columns by auto
        moreover have "path_image ?int_l \<inter> path_image ?l2 = {}"
          by (smt (verit, best) assms(10) disjoint_iff int_p_y linepath_int_rows vector_2(2))
        moreover have "path_image ?int_l \<inter> path_image ?l3 = {}"
          by (smt (verit, del_insts) \<epsilon> disjoint_iff int_p_x linepath_int_columns vector_2(1) zero_index)
        moreover have "path_image ?int_l \<inter> path_image p = {}"
        proof-
          have "\<forall>t \<in> {0..1}. (?int_l t)$2 = 0 \<longrightarrow> t = 1"
            unfolding linepath_def using assms(10) int_p_y by force
          then have "\<forall>x \<in> path_image ?int_l. x$2 = 0 \<longrightarrow> x = q0"
            unfolding path_image_def using linepath_1' by fastforce
          moreover have "\<forall>x \<in> path_image p. x$2 \<ge> 0" by (simp add: assms(12))
          moreover have "\<forall>x \<in> path_image ?int_l. x$2 \<le> 0"
            by (smt (verit) assms(10) int_p_y linepath_bound_2(2))
          ultimately show ?thesis using that by fastforce
        qed
        ultimately have "path_image ?int_l \<inter> path_image ?R = {}"
          by (simp add: disjoint_iff not_in_path_image_join)

        then have "path_image ?int_l \<subseteq> path_inside ?R \<or> path_image ?int_l \<subseteq> path_outside ?R"
          by (metis IntD2 IntI convex_imp_path_connected convex_segment(1) empty_iff int_p interior_frontier path_connected_not_frontier_subset path_image_linepath pathstart_in_path_image pathstart_linepath)
        moreover have "?int_l 0 = int_p \<and> int_p \<in> path_inside ?R"
          using int_p by (simp add: linepath_0')
        ultimately have "path_image ?int_l \<subseteq> path_inside ?R"
          using inside_outside_def local.inside_outside by auto
        thus ?thesis by auto
      qed
      then have "q0 \<in> - (path_outside ?R)"
        by (metis ComplI IntI equals0D inside_Int_outside path_inside_def path_outside_def)
      moreover have "q1 \<in> path_outside ?R"
      proof-
        let ?e2 = "(vector [0, 1])::(real^2)"
        let ?ray = "\<lambda>d. q1 + d *\<^sub>R ?e2"
        have "\<not> (\<exists>d>0. ?ray d \<in> path_image ?R)"
        proof-
          have "\<forall>d>0. (?ray d)$2 > q1$2" by simp
          thus ?thesis using R_y_q1 by fastforce
        qed
        moreover have "bounded (path_inside ?R)" using bounded_finite_inside simple by blast
        moreover have "?e2 \<noteq> 0" using e1e2_basis(4) by force
        ultimately have "q1 \<notin> path_inside ?R"
          using ray_to_frontier[of "path_inside ?R"] interior_frontier by metis
        moreover have "q1 \<notin> path_image ?R" using R_y_q1 by blast
        ultimately show ?thesis using inside_outside unfolding inside_outside_def by blast
      qed
      ultimately have "path_image q \<inter> - (path_outside ?R) \<noteq> {}
          \<and> path_image q \<inter> (path_outside ?R) \<noteq> {}"
        using q0_def q1_def by blast
      moreover have "path_connected (path_image q)"
        using assms(7) path_connected_path_image simple_path_def by blast
      moreover have "path_image ?R = frontier (path_outside ?R)"
        using inside_outside unfolding inside_outside_def p0_def path_inside_def by blast
      ultimately show ?thesis by (metis Diff_eq Diff_eq_empty_iff path_connected_not_frontier_subset)
    qed
    thus ?thesis by (meson q_int_l1 q_int_l2 q_int_l3 disjoint_iff not_in_path_image_join)
  qed
  ultimately show ?thesis using q0_def by blast
qed

lemma pocket_fill_line_int_aux7:
  fixes p q :: "R_to_R2"
  fixes A :: "(real^2) set"
  defines "p0 \<equiv> pathstart p"
  defines "p1 \<equiv> pathfinish p"
  defines "q0 \<equiv> pathstart q"
  defines "q1 \<equiv> pathfinish q"
  defines "a \<equiv> p1$1"
  defines "l \<equiv> open_segment p0 p1"
  assumes "simple_path p"
  assumes "simple_path q"
  assumes "path_image p \<inter> path_image q = {q0, q1}"
  assumes "p0$1 = 0 \<and> p0$2 = 0 \<and> p1$2 = 0"
  assumes "a > 0"
  assumes "A = convex hull (path_image p \<union> path_image q)"
  assumes "{p0, p1} \<subseteq> frontier A"
  assumes "p`{0<..<1} \<subseteq> interior A"
  assumes "\<exists>x \<in> p`{0<..<1}. x$2 \<ge> 0" (* wlog; if not the case, we flip across x axis *)
  assumes "q0 = p1 \<and> q1 = p0"
  shows "path_image q \<inter> l = {}" "closed_segment p0 p1 \<subseteq> frontier A"
proof-
  have 1: "path_image p \<inter> path_image q = {pathstart q, pathfinish q}"
    by (simp add: assms(9) q0_def q1_def)
  have 2: "pathstart p $ 1 = 0 \<and> pathstart p $ 2 = 0 \<and> pathfinish p $ 2 = 0"
    using assms(10) p0_def p1_def by blast
  have 3: "0 < pathfinish p $ 1" using a_def assms(11) p1_def by auto
  have 4: "A = convex hull (path_image p \<union> path_image q)" by (simp add: assms(12))
  have 5: "{pathstart p, pathfinish p} \<subseteq> frontier A" using assms(13) p0_def p1_def by blast
  have 6: "p ` {0<..<1} \<subseteq> interior A" using assms(14) by blast
  have 7: "path_image q \<subseteq> A" using assms(12) hull_subset by force
  have 8: "\<exists>x \<in> p`{0<..<1}. x$2 \<ge> 0" using assms(15) by blast
  have 9: "pathstart q = pathfinish p \<and> pathfinish q = pathstart p"
    using assms(16) p0_def p1_def q0_def q1_def by fastforce
  have *: "\<forall>x \<in> (path_image p) \<union> (path_image q). x$2 \<ge> 0"
    using pocket_fill_line_int_aux5(2)[OF assms(7) assms(8) 1 2 3 4 5 6 7 8 9] by blast

  show "closed_segment p0 p1 \<subseteq> frontier A"
    using pocket_fill_line_int_aux5(1)[OF assms(7) assms(8) 1 2 3 4 5 6 7 8 9]
    unfolding l_def p0_def p1_def by blast
  show "path_image q \<inter> l = {}"
  proof(rule ccontr)
    assume "\<not> path_image q \<inter> l = {}"
    then obtain x tx where x: "tx \<in> {0..1} \<and> q tx = x \<and> x \<in> l"
      by (metis (no_types, lifting) disjoint_iff imageE path_image_def)
    obtain y ty where y: "ty \<in> {0..1} \<and> q ty = y \<and> (\<forall>x \<in> path_image p. y$2 > x$2)"
      using exists_point_above_all[of p q]
      by (smt (verit, del_insts) "4" "6" "8" assms(10) assms(7) assms(8) p0_def p1_def pathfinish_def pathstart_def simple_path_def image_iff path_image_def)

    have lf: "(\<forall>t \<in> {0..1}. (q t = q0 \<or> q t = q1) \<longrightarrow> (t = 0 \<or> t = 1))"
      using assms(8)
      unfolding q0_def q1_def simple_path_def loop_free_def pathstart_def pathfinish_def
      by fastforce
    have endpoints: "q tx \<noteq> q0 \<and> q ty \<noteq> q0 \<and> q tx \<noteq> q1 \<and> q ty \<noteq> q1 \<and> tx \<noteq> ty"
    proof-
      have "(q ty)$2 > 0" by (metis assms(10) p0_def pathstart_in_path_image y)
      moreover have "(q tx)$2 = 0"
      proof-
        have "q tx \<in> closed_segment q0 q1"
          using assms(16) l_def open_closed_segment open_segment_commute x by blast
        thus ?thesis by (simp add: assms(10) assms(16) segment_horizontal)
      qed
      moreover have "q0 \<notin> open_segment q0 q1 \<and> q1 \<notin> open_segment q0 q1"
        by (simp add: open_segment_def)
      ultimately show ?thesis
        using assms(10) assms(16) l_def open_segment_commute x by auto
    qed

    let ?Q =
      "\<lambda>q'. simple_path q' \<and> path_image p \<inter> path_image q' = {}
        \<and> q' 0 = q tx \<and> q' 1 = q ty
        \<and> path_image q' \<subseteq> path_image q"
    have **: "\<And>q'. ?Q q' \<Longrightarrow> False"
    proof-
      fix q'
      assume **: "?Q q'"
      have 1: "simple_path q'" by (simp add: **)
      have 2: "pathstart p = 0 \<and> pathfinish p $ 2 = 0"
        by (metis (mono_tags, lifting) assms(10) exhaust_2 p0_def p1_def vec_eq_iff zero_index)
      have 3: "0 < pathfinish p $ 1" using a_def assms(11) p1_def by blast
      have 4: "pathstart q' $ 1 \<in> {0..pathfinish p $ 1} \<and> pathstart q' $ 2 = 0"
      proof-
        have "q' 0 \<in> closed_segment p0 p1" using ** l_def open_closed_segment x by auto
        thus ?thesis
          by (smt (z3) 2 a_def assms(11) atLeastAtMost_iff atLeastatMost_empty p0_def p1_def pathstart_def pathstart_subpath segment_horizontal zero_index)
      qed
      have 5: "\<forall>x\<in>path_image p. x $ 2 < pathfinish q' $ 2" by (simp add: ** pathfinish_def y)
      have 6: "\<forall>x\<in>path_image p \<union> path_image q'. 0 \<le> x $ 2" using * ** by blast
      have "path_image p \<inter> path_image q' \<noteq> {}"
        using pocket_fill_line_int_aux6[OF assms(7) 1 2 3 4 5 6] by simp
      thus False using ** by blast
    qed

    have False if "tx < ty"
    proof-
      let ?q' = "subpath tx ty q"
      have "q0 \<notin> path_image ?q' \<and> q1 \<notin> path_image ?q'"
      proof-
        have "{tx..ty} \<subseteq> {0..1}" using x y by simp
        then have "(\<forall>t \<in> {tx..ty}. (q t = q0 \<or> q t = q1) \<longrightarrow> (t = 0 \<or> t = 1))" using lf by blast
        moreover have "0 \<notin> {tx..ty} \<and> 1 \<notin> {tx..ty}"
          by (metis atLeastAtMost_iff dual_order.eq_iff endpoints pathfinish_def pathstart_def q0_def q1_def x y)
        moreover have "path_image ?q' = q`{tx..ty}" by (simp add: path_image_subpath that)
        ultimately show ?thesis by fastforce
      qed
      then have "?Q ?q'"
        by (smt (verit, best) assms(8) assms(9) disjoint_insert(1) endpoints inf.absorb_iff1 inf_bot_right inf_left_commute path_image_subpath_subset pathfinish_def pathfinish_subpath pathstart_def pathstart_subpath simple_path_subpath x y)
      thus False using ** by auto
    qed
    moreover have False if "tx > ty"
    proof-
      let ?q' = "reversepath (subpath ty tx q)"
      have "q0 \<notin> path_image ?q' \<and> q1 \<notin> path_image ?q'"
      proof-
        have "{ty..tx} \<subseteq> {0..1}" using x y by simp
        then have "(\<forall>t \<in> {ty..tx}. (q t = q0 \<or> q t = q1) \<longrightarrow> (t = 0 \<or> t = 1))" using lf by blast
        moreover have "0 \<notin> {ty..tx} \<and> 1 \<notin> {ty..tx}"
          by (metis atLeastAtMost_iff dual_order.eq_iff endpoints pathfinish_def pathstart_def q0_def q1_def x y)
        moreover have "path_image ?q' = q`{ty..tx}" by (simp add: path_image_subpath that)
        ultimately show ?thesis by fastforce
      qed
      then have "?Q ?q'"
        by (smt (verit) assms(8) assms(9) endpoints inf.absorb_iff2 inf.assoc inf_bot_left insert_disjoint(2) path_image_subpath_subset pathstart_def pathstart_subpath reversepath_def reversepath_subpath simple_path_subpath x y)
      thus False using ** by blast
    qed
    ultimately show False using endpoints by linarith
  qed
qed

(* could not find in libraries, seems like it should be there *)
lemma frontier_injective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes "linear f" "inj f"
  shows "f ` (frontier S) = frontier (f ` S)"
  using interior_injective_linear_image closure_injective_linear_image frontier_def assms
  by (metis image_set_diff)

lemma pocket_fill_line_int_aux8:
  fixes p q :: "R_to_R2"
  fixes A :: "(real^2) set"
  defines "p0 \<equiv> pathstart p"
  defines "p1 \<equiv> pathfinish p"
  defines "q0 \<equiv> pathstart q"
  defines "q1 \<equiv> pathfinish q"
  defines "a \<equiv> p1$1"
  defines "l \<equiv> open_segment p0 p1"
  assumes "simple_path p"
  assumes "simple_path q"
  assumes "path_image p \<inter> path_image q = {q0, q1}"
  assumes "p0$1 = 0 \<and> p0$2 = 0 \<and> p1$2 = 0"
  assumes "a > 0"
  assumes "A = convex hull (path_image p \<union> path_image q)"
  assumes "{p0, p1} \<subseteq> frontier A"
  assumes "p`{0<..<1} \<subseteq> interior A"
  assumes "q0 = p1 \<and> q1 = p0"
  shows "path_image q \<inter> l = {} \<and> l \<subseteq> frontier A"
proof-
  have ?thesis if ex: "\<exists>x \<in> p`{0<..<1}. x$2 \<ge> 0" 
    using ex a_def assms dual_order.trans l_def p0_def p1_def pocket_fill_line_int_aux7(1) pocket_fill_line_int_aux7(2) q0_def q1_def segment_open_subset_closed that
    
    by (smt (verit) a_def assms dual_order.trans l_def p0_def p1_def pocket_fill_line_int_aux7(1) pocket_fill_line_int_aux7(2) q0_def q1_def segment_open_subset_closed that)
  moreover have ?thesis if "\<not> (\<exists>x \<in> p`{0<..<1}. x$2 \<ge> 0)"
  proof- (* flip across x axis *)
    let ?M = "(vector [vector [1, 0], vector [0, -1]])::(real^2^2)"
    let ?f = "\<lambda>v. ?M *v v"
    let ?g = "(\<lambda>v. vector [v$1, -v$2])::(real^2 \<Rightarrow> real^2)"
    define p' where "p' \<equiv> ?f \<circ> p"
    define q' where "q' \<equiv> ?f \<circ> q"
    define A' where "A' \<equiv> ?f`A"

    have inj: "inj ?f" and f_eq_g: "?f = ?g"
      using flip_function(1) apply blast
      using flip_function(2) by blast

    have 4: "pathstart p' $ 1 = 0 \<and> pathstart p' $ 2 = 0 \<and> pathfinish p' $ 2 = 0"
      by (smt (verit, best) assms(10) f_eq_g o_apply p'_def p0_def p1_def pathfinish_def pathstart_def vector_2(1) vector_2(2))
    have startfinish: "pathstart p' = pathstart p \<and> pathfinish p' = pathfinish p"
      by (metis (mono_tags, opaque_lifting) "4" assms(10) exhaust_2 f_eq_g o_apply p'_def p0_def p1_def pathfinish_def vec_eq_iff vector_2(1))

    have 1: "simple_path p'" using inj by (simp add: assms(7) simple_path_linear_image_eq p'_def)
    have 2: "simple_path q'" using inj by (simp add: assms(8) simple_path_linear_image_eq q'_def)
    have 3: "path_image p' \<inter> path_image q' = {pathstart q', pathfinish q'}"
    proof-
      have "path_image p' \<inter> path_image q' = ?f`(path_image p \<inter> path_image q)"
        unfolding p'_def q'_def by (simp add: image_Int inj path_image_compose)
      also have "... = ?f`{q0, q1}" using assms(9) by presburger
      finally show ?thesis
        by (simp add: startfinish pathfinish_compose pathstart_compose q'_def q0_def q1_def)
    qed
    have 5: "0 < pathfinish p' $ 1"
      by (metis (mono_tags, lifting) a_def assms(11) f_eq_g o_apply p'_def p1_def pathfinish_def vector_2(1))
    have 6: "A' = convex hull (path_image p' \<union> path_image q')"
    proof-
      have "path_image (?f \<circ> p) = ?f`(path_image p)" using path_image_compose by blast
      moreover have "path_image (?f \<circ> q) = ?f`(path_image q)" using path_image_compose by blast
      moreover have "?f`(path_image p \<union> path_image q) = ?f`(path_image p) \<union> ?f`(path_image q)"
        by blast
      moreover have "A' = convex hull (?f`(path_image p \<union> path_image q))"
        by (simp add: assms(12) convex_hull_linear_image A'_def)
      ultimately show ?thesis using p'_def q'_def A'_def by argo
    qed
    have 7: "{pathstart p', pathfinish p'} \<subseteq> frontier A'"
      using frontier_injective_linear_image
      by (smt (verit, best) "3" A'_def assms(13) assms(15) assms(9) doubleton_eq_iff image_Int inj inj_image_subset_iff matrix_vector_mul_linear p'_def p0_def p1_def path_image_linear_image pathfinish_compose pathstart_compose q'_def q0_def q1_def)
    have 8: "p'`{0<..<1} \<subseteq> interior A'"
    proof-
      have "?f`(interior A) = interior A'" by (simp add: A'_def inj interior_injective_linear_image)
      thus ?thesis using assms(14) p'_def by auto
    qed
    have 9: "\<exists>x \<in> p'`{0<..<1}. x$2 \<ge> 0"
    proof-
      have "\<exists>x \<in> p`{0<..<1}. x$2 < 0"
        by (metis that all_not_in_conv bot.extremum greaterThanLessThan_subseteq_greaterThanLessThan image_is_empty verit_comp_simplify1(3) zero_less_one)
      then obtain x where "x \<in> p`{0<..<1} \<and> x$2 < 0" by presburger
      moreover then have "(?g x)$2 > 0" by fastforce
      ultimately show ?thesis by (smt (verit, ccfv_threshold) f_eq_g image_iff o_apply p'_def)
    qed
    have 10: "pathstart q' = pathfinish p' \<and> pathfinish q' = pathstart p'"
      by (metis (mono_tags, lifting) assms(15) o_apply p'_def p0_def p1_def pathfinish_def pathstart_def q'_def q0_def q1_def)

    have "path_image q' \<inter> open_segment (pathstart p') (pathfinish p') = {}"
      using pocket_fill_line_int_aux7(1)[OF 1 2 3 4 5 6 7 8 9 10] by blast
    then have "path_image q' \<inter> l = {}" using startfinish unfolding l_def p0_def p1_def by simp
    moreover have on_l: "\<And>x. x \<in> l \<Longrightarrow> ?g x \<in> l"
    proof-
      fix x :: "real^2"
      assume "x \<in> l"
      moreover then have "x$2 = 0" by (metis assms(6,10) segment_horizontal open_closed_segment)
      moreover then have "(?g x)$2 = 0" by simp
      moreover have "(?g x)$1 = x$1" by simp
      ultimately show "?g x \<in> l" by (smt (verit, ccfv_SIG) exhaust_2 vec_eq_iff)
    qed
    ultimately have "path_image q \<inter> l = {}"
      by (metis (no_types, lifting) disjoint_iff f_eq_g image_eqI path_image_compose q'_def)
    moreover have "l \<subseteq> frontier A"
    proof-
      have "pathstart p' = pathstart p \<and> pathfinish p' = pathfinish p"
        using startfinish by auto
      then have "?f`l \<subseteq> frontier A'"
        using pocket_fill_line_int_aux7(2)[OF 1 2 3 4 5 6 7 8 9 10] on_l f_eq_g l_def p0_def p1_def segment_open_subset_closed
        by force
      thus ?thesis
        by (metis (no_types, lifting) A'_def frontier_injective_linear_image inj inj_image_subset_iff matrix_vector_mul_linear)
    qed
    ultimately show ?thesis by fast
  qed
  ultimately show ?thesis by argo
qed

lemma simple_path_linear_image:
  assumes "simple_path p"
  assumes "inj f \<and> bounded_linear f"
  shows "simple_path (f \<circ> p)" 
proof-
  have "continuous_on {x. True} f" using assms(2) linear_continuous_on by blast
  then have 1: "path (f \<circ> p)"
    by (metis Collect_cong UNIV_I assms(1) continuous_on_subset path_continuous_image simple_path_imp_path top_empty_eq top_greatest top_set_def)

  have "inj_on p {0<..<1}" by (simp add: assms(1) simple_path_inj_on)                  
  then have "inj_on (f \<circ> p) {0<..<1}" by (meson assms(2) comp_inj_on inj_on_subset top_greatest)
  then have "loop_free (f \<circ> p)"
    by (metis (mono_tags, lifting) assms(1) assms(2) comp_apply inj_eq loop_free_def simple_path_def)  
  thus ?thesis using 1 unfolding simple_path_def by blast
qed

lemma vts_interior:
  fixes vts
  defines "p \<equiv> make_polygonal_path vts"
  assumes "convex H"
  assumes "\<forall>j \<in> {0<..<length vts - 1}. vts!j \<notin> frontier H"
  assumes "loop_free p"
  assumes "path_image p \<subseteq> H"
  assumes "length vts \<ge> 3"
  shows "p`{0<..<1} \<subseteq> interior H"
proof(rule subsetI)
  fix x assume *: "x \<in> p`{0<..<1}"
  then obtain t where t: "x = p t \<and> t \<in> {0<..<1}" by blast
  then have "x \<noteq> p 0 \<and> x \<noteq> p 1" using assms(4) unfolding loop_free_def by fastforce
  then have x_neq: "x \<noteq> hd vts \<and> x \<noteq> last vts"
    by (metis assms(4) constant_linepath_is_not_loop_free hd_conv_nth last_conv_nth make_polygonal_path.simps(1) p_def pathfinish_def pathstart_def polygon_pathfinish polygon_pathstart)

  have "x \<in> interior H" if **: "\<exists>i<length vts. x = vts!i"
  proof-
    obtain i where i:  "i < length vts \<and> x = vts!i" using ** by blast
    then have "i \<noteq> 0 \<and> i \<noteq> length vts - 1"
      by (metis x_neq gr_implies_not0 hd_conv_nth last_conv_nth list.size(3))
    then have "i \<in> {0<..<length vts - 1}" using i by fastforce
    then have "vts!i \<notin> frontier H" using assms(3) by blast
    then have "vts!i \<in> interior H"
      by (metis DiffI assms(5) closure_subset frontier_def i nth_mem p_def subsetD vertices_on_path_image)
    thus ?thesis using assms(3) i by blast
  qed
  moreover have "x \<in> interior H" if **: "\<not> (\<exists>i<length vts. x = vts!i)"
  proof-
    have "x \<in> path_image p" using * unfolding path_image_def by force
    then obtain i where i: "x \<in> path_image (linepath (vts!i) (vts!(i+1))) \<and> i < length vts - 1"
      using make_polygonal_path_image_property[of vts x] assms(6) unfolding p_def by auto
    moreover then have "x \<noteq> vts!i \<and> x \<noteq> vts!(i+1)" using ** by force
    ultimately have "x \<in> open_segment (vts!i) (vts!(i+1))" by (simp add: open_segment_def)
    moreover then have "x \<in> rel_interior (path_image (linepath (vts!i) (vts!(i+1))))"
      by (metis empty_iff open_segment_idem path_image_linepath rel_interior_closed_segment)
    moreover have interior_nonempty: "vts!i \<in> interior H \<or> vts!(i+1) \<in> interior H"
    proof(rule ccontr)
      assume "\<not> (vts!i \<in> interior H \<or> vts!(i+1) \<in> interior H)"
      then have "vts!i \<in> frontier H \<and> vts!(i+1) \<in> frontier H"
        using assms(5) closure_subset frontier_def i p_def vertices_on_path_image by fastforce
      thus False
        by (metis assms(3) i Suc_1 Suc_eq_plus1 add.commute add.right_neutral assms(6) eval_nat_numeral(3) greaterThanLessThan_iff less_diff_conv linorder_not_le not_gr_zero not_less_eq_eq)
    qed
    ultimately have "x \<in> rel_interior H"
      by (smt (verit, ccfv_SIG) add_diff_inverse_nat assms(2) assms(5) convex_same_rel_interior_closure_straddle empty_iff i in_interior_closure_convex_segment less_diff_conv less_nat_zero_code nat_diff_split nth_mem open_segment_commute p_def rel_interior_nonempty_interior subset_eq trans_less_add2 vertices_on_path_image)
    moreover have "interior H \<noteq> {}" using interior_nonempty by blast
    ultimately show ?thesis using rel_interior_nonempty_interior by blast
  qed
  ultimately show "x \<in> interior H" by blast
qed

lemma pocket_fill_line_int_0:
  assumes "polygon_of r vts"
  defines "H \<equiv> convex hull (set vts)"
  assumes "2 \<le> i \<and> i < length vts - 1"
  defines "a \<equiv> hd vts"
  defines "b \<equiv> vts!i"
  assumes "{a, b} \<subseteq> frontier H"
  assumes "\<forall>j \<in> {0<..<i}. vts!j \<notin> frontier H"
  assumes "a = 0"
  shows "path_image (linepath a b) \<inter> path_image r = {a, b}"
        "path_image (linepath a b) \<subseteq> frontier H"
proof-
  let ?x = "(b - a)"
  let ?e = "norm (b - a) *\<^sub>R ((vector [1, 0])::(real^2))"
  have "norm ?x = norm ?e" by (simp add: e1e2_basis(1))
  then obtain f where f: "orthogonal_transformation f \<and> det(matrix f) = 1 \<and> f ?x = ?e"
    using rotation_exists by (metis two_le_card)

  have bij: "bij f \<and> linear f"
    using f orthogonal_transformation_bij orthogonal_transformation_def by blast

  let ?p_vts = "take (i + 1) vts"
  let ?q_vts = "drop i vts"
  let ?p = "make_polygonal_path ?p_vts"
  let ?q = "make_polygonal_path ?q_vts"

  let ?p' = "f \<circ> ?p"
  let ?q' = "f \<circ> ?q"
  let ?H' = "convex hull (path_image ?p' \<union> path_image ?q')"

  have vts_split: "vts = ?p_vts @ (tl ?q_vts)"
    by (metis Suc_eq_plus1 append_take_drop_id drop_Suc tl_drop)

  have "simple_path r" using assms(1) unfolding polygon_of_def polygon_def by blast
  then have a_neq_b: "a \<noteq> b"
    using simple_polygonal_path_vts_distinct[of vts]
    by (metis (mono_tags, lifting) a_def assms(1) assms(3) b_def bot_nat_0.extremum_strict butlast_conv_take constant_linepath_is_not_loop_free distinct_nth_eq_iff dual_order.strict_trans2 hd_conv_nth length_butlast make_polygonal_path.simps(1) nat_neq_iff nth_take polygon_of_def pos2 simple_path_def)

  have H_r: "H = convex hull (path_image r)"
    by (metis (no_types, lifting) H_def Un_subset_iff assms(1) convex_convex_hull convex_hull_eq convex_hull_of_polygon_is_convex_hull_of_vts hull_mono hull_subset order_antisym_conv polygon_of_def vertices_on_path_image)
  moreover have r_union: "path_image r = (path_image ?p) \<union> (path_image ?q)"
  proof-
    let ?i = "i + 1"
    let ?x = "((2::real) ^ (?i - 1) - 1) / 2 ^ (?i - 1)"
    have "?x \<in> {0..1} \<and> path_image ?p = r`{0..?x} \<and> path_image ?q = r`{?x..1}"
      using vts_split_path_image[of r vts ?p ?p_vts ?q ?q_vts ?i _ ?x]
      by (smt (verit, ccfv_SIG) add.commute add_diff_cancel_left' assms(1) assms(3) atLeastAtMost_iff atLeastatMost_empty' image_empty le_add1 less_diff_conv path_image_nonempty polygon_of_def) 
    thus ?thesis by (metis atLeastAtMost_iff image_Un ivl_disj_un_two_touch(4) path_image_def)
  qed
  moreover have "f`H = convex hull (f`(path_image r))"
    using bij by (simp add: calculation(1) convex_hull_linear_image)
  ultimately have H_image: "?H' = f`H" by (simp add: image_Un path_image_compose)

  have p_image: "path_image ?p' = f`(path_image ?p)" using path_image_compose by blast
  have q_image: "path_image ?q' = f`(path_image ?q)" using path_image_compose by blast

  have pathstart_p: "pathstart ?p = a"
    by (metis Suc_eq_plus1 a_def assms(3) gr_implies_not0 hd_conv_nth length_tl less_Suc_eq_0_disj list.sel(2) list.size(3) nth_take polygon_pathstart take_eq_Nil)
  have pathfinish_p: "pathfinish ?p = b"
    by (metis (no_types, lifting) H_def H_r add_diff_cancel_right' assms(3) b_def convex_hull_eq_empty length_take less_add_one less_diff_conv min.absorb4 nth_append one_neq_zero path_image_nonempty polygon_pathfinish set_empty take_eq_Nil vts_split zero_eq_add_iff_both_eq_0)
  then have pathstart_q: "pathstart ?q = b" using assms(3) b_def polygon_pathstart by force

  have pathstart_p': "pathstart ?p' = f a" using pathstart_compose pathstart_p by blast
  have pathfinish_p': "pathfinish ?p' = f b" using pathfinish_compose pathfinish_p by blast
  have pathstart_q': "pathstart ?q' = f b" using pathstart_compose pathstart_q by blast

  have "sublist ?p_vts vts" by auto
  then have lf_p: "loop_free ?p"
    by (metis add.commute assms(1) assms(3) less_diff_conv less_imp_le_nat polygon_def polygon_of_def simple_path_def take_i_is_loop_free trans_le_add2)
  then have simple_p: "simple_path ?p"
    using assms unfolding polygon_of_def
    by (meson make_polygonal_path_gives_path simple_path_def)

  have "sublist ?q_vts vts" by auto
  then have lf_q: "loop_free ?q"
    by (metis (no_types, lifting) Suc_1 Suc_diff_Suc assms(1) assms(3) diff_is_0_eq drop_i_is_loop_free less_Suc_eq_le less_zeroE linorder_not_less polygon_def polygon_of_def simple_path_def)
  then have simple_q: "simple_path ?q"
    using assms unfolding polygon_of_def
    by (meson make_polygonal_path_gives_path simple_path_def)

  have bounded_linear: "bounded_linear f" using bij linear_conv_bounded_linear by blast
  have 1: "simple_path ?p'"
    using simple_p simple_path_linear_image bij bij_is_inj bounded_linear
    by blast
  have 2: "simple_path ?q'" 
    using simple_q simple_path_linear_image bij bij_is_inj bounded_linear
    by blast
  have 3: "path_image ?p' \<inter> path_image ?q' = {pathstart ?q', pathfinish ?q'}"
  proof-
    have "path_image ?p \<inter> path_image ?q \<subseteq> {pathstart ?q, pathfinish ?q}"
      using loop_free_split_int[of r vts ?p_vts i ?q_vts ?p ?q]
      by (smt (verit, ccfv_threshold) a_def add_diff_cancel_right' assms(1) assms(3) constant_linepath_is_not_loop_free drop_eq_Nil have_wraparound_vertex hd_conv_nth insert_commute last_conv_nth last_drop last_snoc le_add2 less_diff_conv lf_q linorder_not_less loop_free_split_int make_polygonal_path.simps(1) pathstart_p polygon_def polygon_of_def polygon_pathfinish simple_path_def)
    moreover have "pathstart ?q \<in> path_image ?q \<and> pathfinish ?q \<in> path_image ?q" by blast
    moreover have "pathstart ?q \<in> path_image ?p \<and> pathfinish ?q \<in> path_image ?p"
      by (smt (verit, ccfv_SIG) a_def add_diff_cancel_right' assms(1) assms(3) b_def constant_linepath_is_not_loop_free drop_eq_Nil have_wraparound_vertex hd_conv_nth last_conv_nth last_drop last_snoc length_take less_add_one less_diff_conv lf_q linorder_not_less list.size(3) make_polygonal_path.simps(1) min.absorb4 nth_take pathfinish_in_path_image pathstart_in_path_image pathstart_p pathstart_q polygon_of_def polygon_pathfinish take_eq_Nil zero_eq_add_iff_both_eq_0 zero_neq_one)
    ultimately have "path_image ?p \<inter> path_image ?q = {pathstart ?q, pathfinish ?q}" by fast
    moreover have "path_image ?p' \<inter> path_image ?q' = f`(path_image ?p \<inter> path_image ?q)"
      by (metis bij bij_is_inj image_Int p_image q_image)
    ultimately show ?thesis by (simp add: pathfinish_compose pathstart_compose)
  qed
  have 4: "(pathstart ?p')$1 = 0 \<and> (pathstart ?p')$2 = 0 \<and> (pathfinish ?p')$2 = 0"
  proof-
    have "f ?x = ?e" using f by blast
    then have "f b - f a = ?e"
      by (metis assms(8) diff_zero f norm_eq_zero orthogonal_transformation_norm)
    moreover have "f a = 0" by (metis assms(8) f norm_eq_zero orthogonal_transformation_norm)
    moreover from calculation have "f b = ?e" by force
    ultimately show ?thesis using pathfinish_p' pathstart_p' by auto
  qed
  have 5: "(pathfinish ?p')$1 > 0"
  proof-
    have "pathfinish ?p' = f b" using pathfinish_p' by auto
    moreover have "f b = ?e" using assms(8) f by auto
    moreover have "?e$1 = norm ?x" by simp
    ultimately show ?thesis using a_neq_b by auto
  qed
  have 6: "?H' = convex hull (path_image ?p' \<union> path_image ?q')" by blast
  have 7: "{pathstart ?p', pathfinish ?p'} \<subseteq> frontier ?H'"
  proof-
    have "{pathstart ?p, pathfinish ?p} \<subseteq> frontier H"
      using pathstart_p pathfinish_p assms(6) by fastforce
    then have "f`{pathstart ?p, pathfinish ?p} \<subseteq> f`(frontier H)" by blast
    moreover have "f`(frontier H) = frontier (f`H)"
      by (simp add: bij bij_is_inj frontier_injective_linear_image)
    ultimately show ?thesis using H_image by (simp add: pathfinish_compose pathstart_compose)
  qed
  have 8: "?p'`{0<..<1} \<subseteq> interior ?H'"
  proof-
    have 1: "convex H" by (simp add: H_def)
    have 2: "\<forall>j\<in>{0<..<length ?p_vts - 1}. ?p_vts ! j \<notin> frontier H"
      by (simp add: add.commute assms(3) assms(7) less_diff_conv)
    have 3: "loop_free ?p" using lf_p by blast
    have 4: "path_image ?p \<subseteq> H" using H_r hull_subset r_union by fastforce
    have 5: "length ?p_vts \<ge> 3" using assms(3) by force
    have "?p`{0<..<1} \<subseteq> interior H" using vts_interior[OF 1 2 3 4 5] by argo
    moreover have "f`(?p`{0<..<1}) = ?p'`{0<..<1}" by (meson image_comp)
    moreover have "f`(interior H) = interior ?H'"
      using H_image interior_injective_linear_image[of f H] by (simp add: bij bij_is_inj)
    ultimately show ?thesis by fast
  qed
  have 9: "pathstart ?q' = pathfinish ?p' \<and> pathfinish ?q' = pathstart ?p'"
    by (metis (mono_tags, lifting) H_def H_r a_def assms(1) constant_linepath_is_not_loop_free convex_hull_eq_empty drop_eq_Nil have_wraparound_vertex hd_conv_nth last_conv_nth last_drop last_snoc lf_q linorder_not_less make_polygonal_path.simps(1) path_image_nonempty pathfinish_compose pathfinish_p pathstart_compose pathstart_p pathstart_q polygon_of_def polygon_pathfinish set_empty)

  let ?l = "open_segment a b"
  let ?l' = "open_segment (pathstart ?p') (pathfinish ?p')"

  have *: "path_image ?q' \<inter> open_segment (pathstart ?p') (pathfinish ?p') = {} \<and> ?l' \<subseteq> frontier ?H'"
    using pocket_fill_line_int_aux8[OF 1 2 3 4 5 6 7 8 9] by blast
  moreover have l_image: "?l' = f`?l"
  proof-
    have "f a = pathstart ?p' \<and> f b = pathfinish ?p'" using pathfinish_p' pathstart_p' by presburger
    moreover have "\<And>a b. f`(open_segment a b) = open_segment (f a) (f b)"
      by (simp add: bij bij_is_inj open_segment_linear_image)
    ultimately show ?thesis by presburger
  qed
  moreover have "path_image ?q' = f`(path_image ?q)" using q_image by blast
  ultimately have "path_image ?q \<inter> ?l = {}" by blast
  moreover have "path_image ?p \<inter> ?l = {}"
  proof-
    from 8 have "path_image ?p' \<inter> ?l' = {}"
    proof-
      have "?p'`{0<..<1} \<inter> ?l' = {}"
        by (smt (verit, ccfv_SIG) "*" "8" Diff_disjoint disjoint_iff frontier_def subset_iff)
      moreover have "?p' 0 \<notin> ?l'"
        by (metis "*" "9" IntI empty_iff pathfinish_in_path_image pathstart_def)
      moreover have "?p' 1 \<notin> ?l'"
        by (metis "*" "9" Int_iff emptyE pathfinish_def pathstart_in_path_image)
      ultimately show ?thesis
        by (smt (verit, ccfv_SIG) "*" "1" "3" "9" Int_Un_eq(4) Un_Diff_cancel Un_iff disjoint_iff insert_commute simple_path_endless)
    qed
    thus ?thesis using l_image bij p_image by auto
  qed
  ultimately have "path_image r \<inter> ?l = {}"
    by (simp add: r_union boolean_algebra.conj_disj_distrib inf_commute)
  moreover have "a \<in> path_image r" using pathstart_p r_union by auto
  moreover have "b \<in> path_image r" using pathfinish_p r_union by auto
  moreover have "(path_image (linepath a b)) = ?l \<union> {a, b}" by (simp add: closed_segment_eq_open)
  ultimately show "path_image (linepath a b) \<inter> path_image r = {a, b}" by auto

  have l'_frontier: "?l' \<subseteq> frontier ?H'" using * by presburger
  have "?l \<subseteq> frontier H"
  proof-
    have "?l' = f`?l" using l_image by blast
    moreover have "frontier ?H' = f`(frontier H)"
      by (metis H_image bij bij_is_inj frontier_injective_linear_image)
    ultimately have "f`?l \<subseteq> f`(frontier H)" using l'_frontier by argo
    thus ?thesis by (simp add: bij bij_is_inj inj_image_subset_iff)
  qed
  moreover have "closed_segment a b = path_image (linepath a b)" by simp
  moreover have "closed_segment a b = ?l \<union> {a, b}" by (simp add: closed_segment_eq_open)
  moreover have "a \<in> frontier H \<and> b \<in> frontier H" using assms(6) by auto
  ultimately show "path_image (linepath a b) \<subseteq> frontier H" by simp
qed

lemma linepath_translation: "(\<lambda>v. v - a) \<circ> (linepath x y) = linepath ((\<lambda>v. v - a) x) ((\<lambda>v. v - a) y)"
  by (auto simp: linepath_def algebra_simps)

lemma linepath_image_translation:
    "path_image ((\<lambda>v. v - a) \<circ> (linepath x y)) = path_image (linepath ((\<lambda>v. v - a) x) ((\<lambda>v. v - a) y))"
  using linepath_translation by metis

lemma make_polygonal_path_translate:
  assumes "length vts \<ge> 1"
  shows "(\<lambda>v. v - a) \<circ> (make_polygonal_path vts) = make_polygonal_path (map (\<lambda>v. v - a) vts)"
  using assms
proof(induct "length vts" arbitrary: vts a)
  case 0
  then show ?case by linarith
next
  case (Suc n)
  { assume *: "Suc n = 1"
    then have "make_polygonal_path vts = linepath (vts!0) (vts!0)"
      by (metis Cons_nth_drop_Suc One_nat_def Suc.hyps(2) Suc.prems drop0 drop_eq_Nil less_numeral_extra(1) make_polygonal_path.simps(2))
    then have "(\<lambda>v. v - a) \<circ> (make_polygonal_path vts) = linepath ((vts!0) - a) ((vts!0) - a)"
      by fastforce
    then have ?case
      by (metis Cons_nth_drop_Suc One_nat_def Suc.hyps(2) Suc.prems * drop0 drop_eq_Nil list.map(1) list.simps(9) make_polygonal_path.simps(2) zero_less_one)
  } moreover
  { assume *: "Suc n = 2"
    then have "make_polygonal_path vts = linepath (vts!0) (vts!1)"
      by (metis (no_types, lifting) Cons_nth_drop_Suc One_nat_def Suc.hyps(2) Suc_1 diff_Suc_1 drop0 drop_Suc drop_eq_Nil le_numeral_extra(4) length_tl less_numeral_extra(1) make_polygonal_path.simps(3) nth_tl pos2)
    then have "(\<lambda>v. v - a) \<circ> (make_polygonal_path vts) = linepath ((vts!0) - a) ((vts!1) - a)"
      using linepath_translation by auto
    then have ?case
      by (metis (no_types, lifting) "*" Cons_nth_drop_Suc One_nat_def Suc.hyps(2) Suc_1 drop0 drop_eq_Nil length_map lessI make_polygonal_path.simps(3) nat_le_linear nth_map pos2)
  } moreover
  { assume *: "Suc n \<ge> 3"
    then obtain h h' t where vts: "vts = h # h' # t"
      by (metis Suc.hyps(2) Suc_le_length_iff numeral_3_eq_3)
    then have "(\<lambda>v. v - a) \<circ> (make_polygonal_path (h' # t))
        = make_polygonal_path (map (\<lambda>v. v - a) (h' # t))"
      using Suc.hyps(1) Suc.hyps(2) * by auto
    moreover have "(\<lambda>v. v - a) \<circ> (linepath h h') = linepath (h - a) (h' - a)"
      using linepath_translation by blast
    moreover have "make_polygonal_path vts = (linepath h h') +++ (make_polygonal_path (h' # t))"
      by (metis "*" Suc.hyps(2) Suc_le_length_iff vts list.sel(3) make_polygonal_path.simps(4) numeral_3_eq_3)
    ultimately have ?case
      by (smt (verit) list.discI list.inject list.simps(9) make_polygonal_path.elims path_compose_join vts)
  }
  ultimately show ?case using Suc.prems by linarith
qed

lemma pocket_fill_line_int:
  assumes "polygon_of r vts"
  defines "H \<equiv> convex hull (set vts)"
  assumes "2 \<le> i \<and> i < length vts - 1"
  defines "a \<equiv> hd vts"
  defines "b \<equiv> vts!i"
  assumes "{a, b} \<subseteq> frontier H"
  assumes "\<forall>j \<in> {0<..<i}. vts!j \<notin> frontier H"
  shows "path_image (linepath a b) \<inter> path_image r = {a, b}"
        "path_image (linepath a b) \<subseteq> frontier H"
proof-
  let ?f = "(\<lambda>v. v - a)::(real^2 \<Rightarrow> real^2)"
  let ?r' = "?f \<circ> r"
  let ?vts' = "map ?f vts"
  let ?H' = "convex hull (set ?vts')"
  let ?a' = "?f a"
  let ?b' = "?f b"

  have 5: "hd ?vts' = 0"
    by (metis One_nat_def a_def assms(3) cancel_comm_monoid_add_class.diff_cancel lessI list.map_sel(1) list.size(3) nat_diff_split_asm not_less_zero)

  have a'b': "?a' = hd ?vts' \<and> ?b' = ?vts'!i" using 5 assms(3) b_def by force

  have frontier_H': "frontier ?H' = ?f ` (frontier H)"
    using frontier_translation[of "-a" H]
    by (metis (no_types, lifting) H_def convex_hull_translation image_cong list.set_map uminus_add_conv_diff)

  have "simple_path r" using assms(1) polygon_def polygon_of_def by blast
  then have "simple_path ?r'" using simple_path_translation_eq[of "-a" r] by simp
  moreover have "?r' = make_polygonal_path ?vts'"
    using make_polygonal_path_translate assms(1) assms(3) polygon_of_def by auto
  moreover have "closed_path ?r'"
    by (smt (verit, best) closed_path_def add_diff_inverse_nat assms(1) assms(3) calculation(1) calculation(2) dual_order.refl gr_implies_not0 hd_conv_nth length_map less_Suc_eq_le list.map_disc_iff list.map_sel(1) nat_diff_split_asm nth_map plus_1_eq_Suc polygon_def polygon_of_def polygon_pathfinish polygon_pathstart simple_path_def)
  ultimately have 1: "polygon_of ?r' ?vts'"
    unfolding polygon_of_def polygon_def polygon_def polygonal_path_def by blast
  have 2: "2 \<le> i \<and> i < length ?vts' - 1" using assms(3) by auto
  have 3: "{hd ?vts', ?vts'!i} \<subseteq> frontier ?H'"
    using a'b' frontier_H'
    by (metis (no_types, lifting) assms(6) image_empty image_insert image_mono)
  have 4: "\<forall>j \<in> {0<..<i}. ?vts'!j \<notin> frontier ?H'"
  proof
    fix j assume *: "j \<in> {0<..<i}"
    then have "vts!j \<notin> frontier H" using assms(7) by blast
    then have "?f (vts!j) \<notin> frontier ?H'" using frontier_H' by auto
    thus "?vts'!j \<notin> frontier ?H'" using Nat.le_imp_diff_is_add * assms(3) by auto
  qed

  have "path_image (linepath ?a' ?b') \<inter> path_image ?r' = {?a', ?b'}"
    using pocket_fill_line_int_0(1)[OF 1 2 3 4 5] a'b' by argo
  moreover have "{?a', ?b'} = ?f`{a, b}" by simp
  moreover have "path_image (linepath ?a' ?b') = ?f`(path_image (linepath a b))"
    using linepath_image_translation path_image_compose by blast
  moreover have "path_image ?r' = ?f`(path_image r)" using path_image_compose by blast
  ultimately have "?f`(path_image (linepath a b)) \<inter> ?f`(path_image r) = ?f`{a, b}" by argo
  then have "?f`(path_image (linepath a b) \<inter> path_image r) = ?f`{a, b}" by (simp add: image_Int)
  moreover have "bij ?f" by (simp add: bij_diff_right)
  ultimately show "path_image (linepath a b) \<inter> path_image r = {a, b}"
    by (meson bij_is_inj inj_image_eq_iff)

  have "path_image (linepath ?a' ?b') \<subseteq> frontier ?H'"
    using pocket_fill_line_int_0(2)[OF 1 2 3 4 5] a'b' by argo
  thus "path_image (linepath a b) \<subseteq> frontier H"
    by (metis \<open>bij ?f\<close> \<open>path_image (linepath ?a' ?b') = ?f`(path_image (linepath a b))\<close> bij_betw_imp_inj_on frontier_H' inj_image_subset_iff)
qed

(* not in libraries; would be nice? *)
lemma path_connected_simple_path_endless:
  assumes "simple_path p"
  shows "path_connected (path_image p - {pathstart p, pathfinish p})" (is "path_connected ?S")
proof-
  have "continuous_on {0<..<1} p"
    using assms(1) unfolding simple_path_def path_def
    by (meson continuous_on_path dual_order.refl greaterThanLessThan_subseteq_atLeastAtMost_iff path_def)
  moreover have "path_connected {0<..<1::real}" by simp
  ultimately have "path_connected (p`{0<..<1})" using path_connected_continuous_image by blast
  thus ?thesis using simple_path_endless assms by metis
qed

lemma simple_loop_split:
  assumes "simple_path p \<and> closed_path p"
  assumes "simple_path q"
  assumes "path_image q \<inter> path_image p = {q 0, q 1}"
  assumes "path_image q \<inter> path_inside p \<noteq> {}"
  shows "q`{0<..<1} \<subseteq> path_inside p"
proof-
  have inside_outside:  "inside_outside p (path_inside p) (path_outside p)"
    using Jordan_inside_outside_real2 closed_path_def assms(1) inside_outside_def path_inside_def path_outside_def
    by presburger

  obtain x where x: "x \<in> path_image q \<inter> path_inside p" using assms(4) by blast
  then obtain tx where "tx \<in> {0..1} \<and> q tx = x" unfolding path_image_def by fast
  moreover then have "tx \<noteq> 0 \<and> tx \<noteq> 1"
    using assms(3) inside_outside x unfolding inside_outside_def by auto
  ultimately have tx: "tx \<in> {0<..<1} \<and> q tx = x" by simp

  have "connected (q`{0<..<1})"
    using connected_simple_path_endless simple_path_endless assms(2) by metis
  then have "path_connected (q`{0<..<1})"
    using path_connected_simple_path_endless assms(2) simple_path_endless by metis
  moreover have "q`{0<..<1} \<inter> path_inside p \<noteq> {}" using tx x by blast
  moreover have "q`{0<..<1} \<inter> frontier (path_inside p) = {}"
    using inside_outside unfolding inside_outside_def
    by (smt (verit, del_insts) Diff_Int_distrib2 assms(2,3) diff_eq inf_compl_bot_right inf_idem inf_sup_aci(1) pathfinish_def pathstart_def simple_path_endless)
  ultimately show ?thesis
    using path_connected_not_frontier_subset[of "q`{0<..<1}" "path_inside p"] by fast
qed

lemma pocket_path_interior_aux:
  assumes "simple_path p \<and> simple_path q"
  assumes "arc p \<and> arc q"
  assumes "q 0 = p 1 \<and> q 1 = p 0"
  assumes "path_image p \<inter> path_image q = {p 0, q 0}"
  defines "A \<equiv> convex hull (path_image p \<union> path_image q)"
  defines "l \<equiv> linepath (p 0) (p 1)"
  assumes "p`{0<..<1} \<subseteq> interior A"
  assumes "path_image l \<subseteq> frontier A"
  assumes "path_image q \<inter> path_image l = {l 0, q 0}"
  shows "p`{0<..<1} \<inter> path_inside (l +++ q) \<noteq> {}"
        "simple_path (l +++ q) \<and> closed_path (l +++ q)"
        "path_image p \<inter> path_image (l +++ q) = {p 0, p 1}"
proof-
  let ?r = "l +++ q"
  let ?Ir = "path_inside ?r"
  let ?Or = "path_outside ?r"
  show closed_simple_r: "simple_path ?r \<and> closed_path ?r"
    using simple_path_join_loop[of l q] assms unfolding pathstart_def pathfinish_def
    by (metis (no_types, opaque_lifting) closed_path_def arc_linepath arc_simple_path dual_order.refl inf_commute linepath_0' linepath_1' pathfinish_def pathfinish_join pathstart_def pathstart_join simple_path_def)
  then have inside_outside_r: "inside_outside ?r ?Ir ?Or"
    by (simp add: Jordan_inside_outside_real2 closed_path_def inside_outside_def path_inside_def path_outside_def)

  have l_p_endpoints: "l 0 = p 0 \<and> l 1 = p 1" by (simp add: l_def linepath_0' linepath_1')
  have l_q_endpoints: "l 0 = q 1 \<and> l 1 = q 0" by (simp add: assms(3) l_p_endpoints)
  have p_int_l: "p`{0<..<1} \<inter> path_image l = {}" using assms(7,8) unfolding frontier_def by blast
  have q_int_l: "q`{0<..<1} \<inter> path_image l = {}"
    by (metis (no_types, opaque_lifting) assms(9) Diff_iff Int_Diff all_not_in_conv assms(1) assms(3) inf_sup_aci(1) insert_commute l_def linepath_0' pathfinish_def pathstart_def simple_path_endless)
  have interval: "{0..1::real} = {0<..<1} \<union> {0, 1}" by fastforce
  have lf_l: "loop_free l"
    using closed_simple_r not_loop_free_first_component simple_path_def by blast

  let ?p' = "reversepath p"
  let ?s = "l +++ ?p'"
  let ?Is = "path_inside ?s"
  let ?Os = "path_outside ?s"
  have "arc ?p' \<and> arc l"
    by (metis assms(2) arc_linepath arc_reversepath arc_simple_path l_def pathfinish_def pathstart_def)
  moreover have p'_int_l: "path_image ?p' \<inter> path_image l = {?p' 0, l 0}"
  proof-
    have "path_image p \<inter> path_image l = {l 0, l 1}"
    proof-
      have "{l 0, l 1} \<subseteq> path_image p \<inter> path_image l"
        using assms(3) assms(4) l_def linepath_0' linepath_1' by fastforce
      moreover have "path_image p = p`{0<..<1} \<union> {p 0, p 1}"
        using interval unfolding path_image_def by blast
      ultimately show ?thesis using p_int_l l_p_endpoints by simp
    qed
    moreover have "?p' 0 = l 1" by (simp add: l_def linepath_1' reversepath_def)
    moreover have "path_image p = path_image ?p'" by simp
    ultimately show ?thesis by (metis doubleton_eq_iff)
  qed
  ultimately have closed_simple_s: "closed_path ?s \<and> simple_path ?s"
    using simple_path_join_loop[of l ?p'] assms unfolding pathstart_def pathfinish_def
    by (metis (no_types, opaque_lifting) closed_path_def dual_order.refl inf_commute insert_commute linepath_0' linepath_1' pathfinish_def pathfinish_join pathfinish_reversepath pathstart_def pathstart_join pathstart_reversepath simple_path_def)
  then have inside_outside_s: "inside_outside ?s ?Is ?Os"
    by (simp add: Jordan_inside_outside_real2 closed_path_def inside_outside_def path_inside_def path_outside_def)

  have r_inside_subset: "path_inside ?r \<subseteq> interior A"
  proof-
    have "path_image l \<subseteq> A \<and> path_image q \<subseteq> A"
      by (metis A_def Un_upper2 assms(1) assms(8) compact_Un compact_convex_hull compact_simple_path_image frontier_subset_compact hull_subset subset_trans)
    thus ?thesis
      by (metis (no_types, lifting) A_def closed_simple_r convex_contains_simple_closed_path_imp_contains_path_inside convex_convex_hull inside_outside_def inside_outside_r interior_eq interior_mono subset_path_image_join)
  qed
  have s_inside_subset: "path_inside ?s \<subseteq> interior A"
  proof-
    have "path_image l \<subseteq> A \<and> path_image p \<subseteq> A"
      by (metis A_def Un_upper1 assms(1) assms(8) compact_Un compact_convex_hull compact_simple_path_image frontier_subset_compact hull_subset subset_trans)
    thus ?thesis
      by (metis A_def Jordan_inside_outside_real2 closed_path_def closed_simple_s convex_contains_simple_closed_path_imp_contains_path_inside convex_convex_hull interior_maximal path_image_reversepath path_inside_def subset_path_image_join)
  qed

  have q_outside: "q`{0<..<1} \<subseteq> path_outside ?s"
  proof(rule ccontr)
    let ?ep = "{v. v extreme_point_of A}"
    assume "\<not> q`{0<..<1} \<subseteq> path_outside ?s"
    then have "\<exists>x \<in> q`{0<..<1}. x \<in> path_inside ?s \<union> path_image ?s"
      using inside_outside_s unfolding inside_outside_def by auto
    then have "q`{0<..<1} \<subseteq> path_inside ?s"
      using simple_loop_split[of p q]
      by (smt (verit) DiffE IntI Int_Un_distrib2 closed_path_def UnE \<open>arc (reversepath p) \<and> arc l\<close> arc_imp_path assms(1) assms(2) assms(3) assms(4) closed_simple_r closed_simple_s doubleton_eq_iff emptyE inf.commute l_def path_image_join path_image_reversepath path_join_eq pathfinish_join pathfinish_linepath pathstart_join pathstart_linepath simple_loop_split simple_path_endless simple_path_joinE sup_absorb2)
    then have "q`{0<..<1} \<inter> frontier A = {}" using frontier_def s_inside_subset by fastforce
    then have "(path_image p \<union> path_image q) \<inter> frontier A = {p 0, p 1}"
      by (smt (z3) Diff_disjoint Int_Un_distrib Un_Diff_Int Un_Int_eq(3) assms(1) assms(3) assms(4) assms(7) assms(8) assms(9) frontier_def inf.commute inf.orderE inf_idem inf_left_commute insert_commute l_p_endpoints pathfinish_def pathstart_def simple_path_endless)
    moreover have "?ep\<subseteq> path_image p \<union> path_image q"
      by (simp add: extreme_points_of_convex_hull A_def)
    moreover have "?ep \<subseteq> frontier A"
      using extreme_point_not_in_interior
    proof-
      have "?ep \<inter> interior A = {}"
        using extreme_point_not_in_interior by blast
      thus ?thesis
        by (smt (verit, ccfv_SIG) A_def Int_Un_distrib2 Un_Diff_cancel assms(1) calculation(2) closure_convex_hull compact_Un compact_simple_path_image dual_order.trans frontier_def hull_subset inf.absorb_iff2 inf_commute sup_bot_left)
    qed
    ultimately have *: "?ep \<subseteq> {p 0, p 1}" by auto
    have "A = path_image l"
    proof-
      have "convex A \<and> compact A"
        by (simp add: A_def arc_imp_path assms(2) compact_Un compact_convex_hull compact_path_image)
      then have A_ep: "A = convex hull ?ep" using Krein_Milman_Minkowski by blast
      moreover have "finite ?ep" using "*" infinite_super by auto
      moreover have "A \<noteq> {}" by (simp add: A_def)
      moreover have "\<forall>x. A \<noteq> {x}" using assms(7) by fastforce
      ultimately have "card ?ep \<ge> 2" using convex_hull_two_extreme_points by metis
      then have "?ep = {p 0, p 1}"
        by (metis * One_nat_def Suc_1 add_leD2 card.empty card_insert_disjoint card_seteq finite.emptyI finite.insertI insert_absorb plus_1_eq_Suc)
      then have "A = closed_segment (p 0) (p 1)" by (metis A_ep segment_convex_hull)
      thus ?thesis by (simp add: l_def)
    qed
    then have "interior A = {}"
      by (metis A_def Diff_eq_empty_iff assms(1) assms(8) closure_convex_hull compact_Un compact_simple_path_image double_diff dual_order.refl frontier_def interior_subset)
    thus False using inside_outside_def inside_outside_r r_inside_subset by auto
  qed

  let ?e = "l (1/2)"
  have l_on_r_frontier: "path_image l \<subseteq> frontier (path_inside ?r)"
    using inside_outside_r unfolding inside_outside_def
    by (metis Un_upper1 closed_simple_r \<open>arc (reversepath p) \<and> arc l\<close> arc_def assms(2) path_image_join path_join_eq simple_path_def)
  moreover have "path_image l \<subseteq> frontier (path_inside ?s)"
    using inside_outside_s unfolding inside_outside_def
    by (simp add: l_def path_image_join pathstart_def reversepath_def)
  ultimately have e_frontier: "?e \<in> frontier (path_inside ?r) \<and> ?e \<in> frontier (path_inside ?s)"
    by (simp add: path_defs(4) subsetD)

  have e_notin: "?e \<notin> path_image p \<union> path_image q"
  proof-
    have "?e \<notin> path_image p"
    proof-
      have "?e \<noteq> l 0 \<and> ?e \<noteq> l 1" using lf_l unfolding loop_free_def by fastforce
      then have "?e \<noteq> p 0 \<and> ?e \<noteq> p 1" using l_p_endpoints by simp
      moreover have "?e \<notin> p`{0<..<1}" using p_int_l unfolding path_image_def by fastforce
      ultimately show ?thesis using p_int_l unfolding path_image_def by fastforce
    qed
    moreover have "?e \<notin> path_image q"
    proof-
      have "?e \<noteq> l 0 \<and> ?e \<noteq> l 1" using lf_l unfolding loop_free_def by fastforce
      then have "?e \<noteq> q 0 \<and> ?e \<noteq> q 1" using l_q_endpoints by simp
      moreover have "?e \<notin> q`{0<..<1}" using q_int_l unfolding path_image_def by fastforce
      ultimately show ?thesis using q_int_l unfolding path_image_def by fastforce
    qed
    ultimately show ?thesis by blast
  qed
  obtain \<epsilon> where \<epsilon>: "\<epsilon> > 0 \<and> ball ?e \<epsilon> \<inter> path_image p = {} \<and> ball ?e \<epsilon> \<inter> path_image q = {}"
  proof-
    have "?e \<notin> path_image p" using e_notin by simp
    moreover have "compact (path_image p)" by (simp add: assms(2) compact_arc_image)
    moreover have "?e \<notin> path_image q" using e_notin by simp
    moreover have "compact (path_image q)" by (simp add: assms(2) compact_arc_image)
    ultimately obtain \<epsilon>1 \<epsilon>2 where
        "\<epsilon>1 > 0 \<and> ball ?e \<epsilon>1 \<inter> path_image p = {} \<and> \<epsilon>2 > 0 \<and> ball ?e \<epsilon>2 \<inter> path_image q = {}"
      by (meson assms(1) not_on_path_ball simple_path_imp_path)
    thus ?thesis using that[of "min \<epsilon>1 \<epsilon>2"] by (simp add: disjoint_iff)
  qed
  
  obtain z_r where z_r: "z_r \<in> ball ?e \<epsilon> \<inter> path_inside ?r"
    by (metis e_frontier \<epsilon> all_not_in_conv disjoint_iff frontier_straddle mem_ball)
  obtain z_s where z_s: "z_s \<in> ball ?e \<epsilon> \<inter> path_inside ?s"
    by (metis e_frontier \<epsilon> all_not_in_conv disjoint_iff frontier_straddle mem_ball)

  have z_s_in_r: "z_s \<in> path_inside ?r"
  proof-
    let ?l_z = "linepath z_r z_s"
    have "z_r \<in> interior A \<and> z_s \<in> interior A"
      using r_inside_subset s_inside_subset z_r z_s by blast
    then have "path_image ?l_z \<subseteq> interior A" by (simp add: A_def closed_segment_subset)
    then have 1: "path_image ?l_z \<inter> path_image l = {}"
      by (smt (verit) Diff_iff assms(8) disjoint_iff frontier_def subsetD)

    have "convex (ball ?e \<epsilon>)" by simp
    then have "path_image ?l_z \<subseteq> ball ?e \<epsilon>"
      by (metis IntD1 closed_segment_subset path_image_linepath z_r z_s)
    then have 2: "path_image ?l_z \<inter> path_image q = {}" using \<epsilon> by blast

    show ?thesis
      by (smt (verit, best) 1 2 IntI Int_Un_distrib Int_Un_distrib2 Jordan_inside_outside_real2 closed_path_def \<epsilon> \<open>path_image (linepath z_r z_s) \<subseteq> ball (l (1 / 2)) \<epsilon>\<close> arc_def assms(2) closed_simple_r emptyE in_mono inf.assoc le_iff_inf path_connected_not_frontier_subset path_connected_path_image path_image_join path_inside_def path_join_path_ends path_linepath pathfinish_in_path_image pathfinish_linepath pathstart_in_path_image pathstart_linepath sup.order_iff z_r)
  qed

  let ?xq = "q (1/2)"
  let ?z = "z_s"

  let ?v = "?xq - ?z"
  let ?ray = "\<lambda>d. ?z + d *\<^sub>R ?v"
  let ?rayline = "linepath ?z ?xq"
  have z_ray: "?z = ?ray 0" by simp
  have xq_ray: "?xq = ?ray 1" by simp
  have xq_rayline: "?xq = ?rayline 1" unfolding linepath_def by simp
  have "?xq \<in> path_image ?r"
    by (metis (mono_tags, opaque_lifting) Un_iff atLeastAtMost_iff imageI l_q_endpoints less_eq_real_def path_defs(4) path_image_join pathfinish_def pathstart_def pos_half_less zero_less_divide_1_iff zero_less_numeral zero_less_one)
  then have xq_frontier: "?xq \<in> frontier (path_inside ?r)"
    using inside_outside_r unfolding inside_outside_def by auto
  have xq_neq_z: "?xq \<noteq> ?z"
  proof-
    have "?xq \<in> path_image ?r"
    proof- (* sledgehammer-generated *)
      have "q (1 / 2) \<in> path_image q"
        by (simp add: path_defs(4))
      thus ?thesis
        by (simp add: l_q_endpoints path_image_join pathfinish_def pathstart_def)
    qed
    thus ?thesis using z_s_in_r inside_outside_r unfolding inside_outside_def by blast
  qed
  then have v_neq_0: "?v \<noteq> 0" by simp

  have "bounded (path_inside ?r)" using inside_outside_r unfolding inside_outside_def by blast
  moreover have "?z \<in> interior (path_inside ?r)"
    by (metis inside_outside_def inside_outside_r interior_eq z_s_in_r)
  ultimately obtain d where d: "0 < d \<and> ?ray d \<in> frontier (path_inside ?r)
      \<and> (\<forall>e \<in> {0..<d}. ?ray e \<in> interior (path_inside ?r))"
    using ray_to_frontier[of "path_inside ?r" ?z ?v] by (metis atLeastLessThan_iff v_neq_0)

  have interior_inside_r: "interior (path_inside ?r) = path_inside ?r"
    by (meson inside_outside_def inside_outside_r interior_eq)
  have d_leq_1: "d \<le> 1"
  proof(rule ccontr)
    assume "\<not> d \<le> 1"
    then have "d > 1" by simp
    moreover have "?ray 1 \<in> frontier (path_inside ?r)" using xq_ray xq_frontier by argo
    ultimately show False using d unfolding frontier_def by fastforce
  qed

  have z_inside: "?z \<in> path_inside ?s" using z_s by blast
  moreover have "?rayline d \<in> path_outside ?s"
  proof-
    have "?rayline d \<notin> path_image l" if "d < 1"
    proof-
      have "?rayline 0 \<in> interior A"
        using r_inside_subset by (simp add: linepath_0' subsetD z_s_in_r)
      moreover have "path_image ?rayline \<subseteq> closure A"
      proof-
        have "closure A = A"
          using A_def assms(1) closure_convex_hull compact_Un compact_simple_path_image by blast
        moreover have "?rayline 0 \<in> A" using \<open>?rayline 0 \<in> interior A\<close> interior_subset by blast
        moreover have "?rayline 1 \<in> A"
          using path_image_def A_def hull_subset xq_rayline by fastforce
        ultimately show ?thesis
          by (metis A_def closed_segment_subset convex_convex_hull linepath_0' linepath_1' path_image_linepath)
      qed
      moreover have "\<not> path_image ?rayline \<subseteq> rel_frontier A"
      proof-
        have "path_image ?rayline \<inter> interior A \<noteq> {}"
          using \<open>?rayline 0 \<in> interior A\<close> unfolding path_image_def by fastforce
        moreover have "interior A \<inter> rel_frontier A = {}"
          using rel_frontier_def rel_interior_nonempty_interior by auto
        ultimately show ?thesis by blast
      qed
      ultimately have "rel_interior (path_image ?rayline) \<subseteq> rel_interior A"
        using subset_rel_interior_convex[of "path_image ?rayline" A] by (simp add: A_def)
      moreover have "interior A = rel_interior A"
        using \<open>?rayline 0 \<in> interior A\<close> rel_interior_nonempty_interior by auto
      moreover have "?rayline d \<in> ?rayline`{0<..<1}" using that d by simp
      ultimately show ?thesis
        by (smt (verit, del_insts) DiffD1 DiffD2 Un_iff xq_neq_z arc_linepath arc_simple_path assms(8) closed_segment_eq_open frontier_def path_image_linepath pathfinish_linepath pathstart_linepath rel_interior_closed_segment simple_path_endless subset_eq)
    qed
    moreover have "?rayline d \<notin> path_image l" if "d = 1"
      using that q_int_l unfolding linepath_def by (simp add: disjoint_iff)
    moreover have "?rayline d \<in> path_image ?r"
      by (metis (no_types, lifting) add_diff_eq d diff_add_eq inside_outside_def inside_outside_r linepath_def scale_left_diff_distrib scale_one scale_right_diff_distrib)
    ultimately show ?thesis
      by (smt (verit, ccfv_SIG) d_leq_1 Diff_iff Int_iff closed_path_def \<open>arc (reversepath p) \<and> arc l\<close> arc_def assms(1) assms(3) assms(9) closed_simple_r insert_commute l_def l_p_endpoints not_in_path_image_join path_join_eq pathfinish_join pathfinish_linepath pathstart_join pathstart_linepath q_outside simple_path_def simple_path_endless subsetD)
  qed
  moreover have "?z \<in> ?rayline`{0..d}"
    using z_ray unfolding linepath_def
    by (smt (verit, del_insts) add.commute atLeastAtMost_iff cancel_comm_monoid_add_class.diff_cancel d diff_zero image_iff less_eq_real_def segment_degen_1)
  moreover have "?rayline d \<in> ?rayline`{0..d}" by (simp add: d less_eq_real_def)
  ultimately have "?rayline`{0..d} \<inter> path_inside ?s \<noteq> {} \<and> ?rayline`{0..d} \<inter> path_outside ?s \<noteq> {}"
    by blast
  then have "?rayline`{0..d} \<inter> path_inside ?s \<noteq> {} \<and> ?rayline`{0..d} \<inter> - path_inside ?s \<noteq> {}"
    using inside_outside_s unfolding inside_outside_def by (meson ComplI disjoint_iff)
  moreover have "path_connected (?rayline`{0..d})"
  proof-
    have "?rayline`{0..d} = path_image (subpath 0 d ?rayline)" by (simp add: d path_image_subpath)
    moreover have "path (subpath 0 d ?rayline)" using d d_leq_1 by auto
    ultimately show ?thesis by (metis path_connected_path_image)
  qed
  ultimately have "?rayline`{0..d} \<inter> frontier (path_inside ?s) \<noteq> {}"
    using path_connected_frontier[of "?rayline`{0..d}" "path_inside ?s"] by (metis disjoint_iff)
  then have "?rayline`{0..d} \<inter> path_image ?s \<noteq> {}" using inside_outside_s unfolding inside_outside_def by argo
  moreover have "?rayline 0 \<notin> path_image ?s"
  proof-
    have "?xq \<noteq> p 0"
      by (metis (full_types) disjoint_iff greaterThanLessThan_iff imageI l_p_endpoints pathstart_def pathstart_in_path_image pos_half_less q_int_l zero_less_divide_1_iff zero_less_numeral zero_less_one)
    moreover have "?xq \<noteq> p 1"
      by (metis (full_types) disjoint_iff greaterThanLessThan_iff imageI l_p_endpoints pathfinish_def pathfinish_in_path_image pos_half_less q_int_l zero_less_divide_1_iff zero_less_numeral zero_less_one)
    moreover have "?xq \<notin> p`{0<..<1}"
    proof-
      have "?xq \<in> q`{0<..<1}" by fastforce
      thus ?thesis by (metis assms(1,3,4) Diff_iff Int_iff pathfinish_def pathstart_def simple_path_endless)
    qed
    moreover have "?xq \<notin> path_image l"
      by (metis disjoint_iff greaterThanLessThan_iff imageI pos_half_less q_int_l zero_less_divide_1_iff zero_less_numeral zero_less_one)
    ultimately show ?thesis
      by (metis (no_types, lifting) ComplD UnI1 z_inside inside_outside_def inside_outside_s linepath_0')
  qed
  moreover have "?rayline d \<notin> path_image ?s"
    using \<open>?rayline d \<in> path_outside ?s\<close> inside_outside_def inside_outside_s by auto
  moreover have "{0..d} = {0<..<d} \<union> {0, d}" using d by fastforce
  ultimately have "?rayline`{0<..<d} \<inter> path_image ?s \<noteq> {}" unfolding path_image_def by blast
  moreover have "?rayline`{0<..<d} = ?ray`{0<..<d}"
    unfolding linepath_def by (auto simp: algebra_simps)
  moreover have "?ray`{0<..<d} \<subseteq> path_inside ?r" using d interior_inside_r by fastforce
  ultimately have "path_image ?s \<inter> path_inside ?r \<noteq> {}" by blast
  moreover have "path_image l \<inter> path_inside ?r = {}"
    by (metis (no_types, opaque_lifting) Diff_disjoint Int_assoc l_on_r_frontier frontier_def inf.orderE inf_bot_left inf_sup_aci(1) interior_inside_r)
  moreover have "p`{0<..<1} = path_image ?s - path_image l"
  proof-
    have "path_image ?s = path_image p \<union> path_image l"
      by (simp add: l_p_endpoints path_image_join pathfinish_def sup_commute)
    moreover have "p`{0<..<1} = path_image p - {p 0, p 1}"
      by (metis assms(1) pathfinish_def pathstart_def simple_path_endless)
    ultimately have "path_image ?s = p`{0<..<1} \<union> {p 0, p 1} \<union> path_image l"
      using assms(3) assms(9) l_p_endpoints by auto
    moreover have "p 1 \<in> path_image l \<and> p 0 \<in> path_image l" by (simp add: l_def)
    ultimately show ?thesis using p_int_l by blast
  qed
  ultimately show "p`{0<..<1} \<inter> path_inside (l +++ q) \<noteq> {}" by auto

  show "path_image p \<inter> path_image (l +++ q) = {p 0, p 1}"
    by (smt (verit, best) Int_Un_distrib Un_absorb assms(1) assms(3) assms(4) closed_simple_r insert_commute l_p_endpoints p'_int_l path_image_join path_image_reversepath path_join_path_ends reversepath_def simple_path_imp_path)
qed

lemma pocket_path_interior:
  assumes "simple_path p \<and> simple_path q"
  assumes "arc p \<and> arc q"
  assumes "q 0 = p 1 \<and> q 1 = p 0"
  assumes "path_image p \<inter> path_image q = {p 0, q 0}"
  defines "A \<equiv> convex hull (path_image p \<union> path_image q)"
  defines "l \<equiv> linepath (p 0) (p 1)"
  assumes "p`{0<..<1} \<subseteq> interior A"
  assumes "path_image l \<subseteq> frontier A"
  assumes "path_image q \<inter> path_image l = {l 0, q 0}"
  shows "p`{0<..<1} \<subseteq> path_inside (l +++ q)"
  using pocket_path_interior_aux[of p q] simple_loop_split[of "l +++ q" p] assms
  by (metis (no_types, lifting) DiffE disjoint_iff simple_path_endless)

lemma pocket_path_good:
  assumes "polygon (make_polygonal_path vts)"
  assumes "vts!0 \<in> frontier (convex hull (set vts))"
  assumes "vts!1 \<notin> frontier (convex hull (set vts))"
  assumes "\<not> convex (path_image (make_polygonal_path vts) \<union> path_inside (make_polygonal_path vts))"
  defines "pocket_path_vts \<equiv> construct_pocket_0 vts (set vts \<inter> frontier (convex hull (set vts)))"
  defines "pocket \<equiv> make_polygonal_path (pocket_path_vts @ [pocket_path_vts!0])"
  defines "filled_vts \<equiv> fill_pocket_0 vts (length pocket_path_vts)"
  defines "filled_p \<equiv> make_polygonal_path filled_vts"
  defines "a \<equiv> hd pocket_path_vts"
  defines "b \<equiv> last pocket_path_vts"
  defines "good_pocket_path_vts \<equiv> tl (butlast pocket_path_vts)"
  shows "polygon filled_p"
        "is_polygon_split_path (butlast filled_vts) 0 1 good_pocket_path_vts"
        "polygon pocket"
        "card (set pocket_path_vts) < card (set vts)"
        "card (set filled_vts) < card (set vts)"
proof-
  let ?p = "make_polygonal_path vts"
  let ?A = "set vts \<inter> frontier (convex hull (set vts))"
  let ?filled_vts_tl = "tl filled_vts"
  let ?filled_p_tl = "make_polygonal_path ?filled_vts_tl"
  let ?pocket_vts = "pocket_path_vts @ [pocket_path_vts!0]"
  let ?pocket_path = "make_polygonal_path pocket_path_vts"
  let ?l = "linepath a b"

  (* min_nonzero_index_in_set is defined *)
  let ?r = "min_nonzero_index_in_set vts ?A"
  have int_A_nonempty: "set (tl vts) \<inter> ?A \<noteq> {}"
    by (metis (mono_tags, lifting) IntI Nitpick.size_list_simp(2) Suc_eq_plus1 assms(1) assms(2) card_length empty_iff have_wraparound_vertex last_in_set last_tl le_add1 le_trans not_less_eq_eq numeral_3_eq_3 polygon_at_least_3_vertices snoc_eq_iff_butlast)
  then have r_defined: "nonzero_index_in_set vts ?A ?r \<and> (\<forall>i < ?r. \<not> nonzero_index_in_set vts ?A i)"
    using min_nonzero_index_in_set_defined[of vts ?A] by fast

  (* first and second vts in filled_vts are a and b *)
  have two_vts_on_frontier: "2 \<le> card ?A"
    by (metis convex_hull_two_vts_on_frontier One_nat_def Suc_1 add_leD2 assms(1) numeral_3_eq_3 plus_1_eq_Suc polygon_at_least_3_vertices)
  moreover have frontier_vts_subset: "?A \<subseteq> set vts" by force
  moreover have distinct_vts: "distinct (butlast vts)"
    using assms(1) polygon_def simple_polygonal_path_vts_distinct by blast
  moreover have hd_last_vts: "hd vts = last vts"
    by (metis assms(1) have_wraparound_vertex hd_conv_nth snoc_eq_iff_butlast)
  ultimately have a_neq_b: "a \<noteq> b"
    using a_def b_def construct_pocket_0_first_last_distinct pocket_path_vts_def by presburger
  have "length filled_vts \<ge> 2"
    unfolding filled_vts_def fill_pocket_0_def
    by (smt (verit, best) One_nat_def Suc_1 Suc_diff_Suc a_def a_neq_b b_def construct_pocket_0_def diff_is_0_eq diff_zero hd_Nil_eq_last length_drop length_greater_0_conv length_tl list.sel(3) not_less_eq_eq pocket_path_vts_def sublist_length_le sublist_take)
  moreover have filled_vts_0: "a = filled_vts!0"
    unfolding filled_vts_def fill_pocket_0_def a_def pocket_path_vts_def construct_pocket_0_def
    by auto
  moreover have filled_vts_1: "b = filled_vts!1"
    by (smt (verit, del_insts) filled_vts_def fill_pocket_0_def b_def pocket_path_vts_def construct_pocket_0_def Cons_nth_drop_Suc Nitpick.size_list_simp(2) a_def a_neq_b add.right_neutral drop0 drop_eq_Nil hd_Nil_eq_last last_conv_nth length_take length_tl linorder_not_less list.sel(3) min.absorb4 nat_le_linear not_less_eq_eq nth_drop nth_take plus_1_eq_Suc take_all_iff zero_less_diff)
  ultimately have filled_vts: "filled_vts = [a, b] @ tl ?filled_vts_tl"
    by (metis (no_types, lifting) Nitpick.size_list_simp(2) One_nat_def Suc_1 append_Nil append_eq_Cons_conv length_greater_0_conv list.collapse not_less_eq_eq nth_Cons_0 nth_tl order_less_le_trans pos2)

  have 1: "polygon_of ?p vts" unfolding polygon_of_def using assms(1) by blast
  have 2: "2 \<le> ?r \<and> ?r < length vts - 1"
  proof-
    have "?r \<noteq> 0 \<and> ?r \<noteq> 1"
      using assms(2,3) min_nonzero_index_in_set_def nonzero_index_in_set_def r_defined
      by fastforce
    then have 1: "?r \<ge> 2" by simp

    have "\<exists>i \<in> {0<..<length vts - 1}. vts!i \<in> frontier (convex hull (set vts))"
    proof-
      have "card ((set vts) \<inter> frontier (convex hull (set vts))) \<ge> 2"
        using two_vts_on_frontier by blast
      then obtain v where "v \<in> set vts \<and> v \<in> frontier (convex hull set vts) \<and> v \<noteq> hd vts"
        by (metis hd_last_vts Int_iff a_neq_b assms(2) b_def construct_pocket_0_last_in_set convex_hull_empty empty_set fill_pocket_0_def filled_vts_0 filled_vts_def frontier_empty hd_conv_nth int_A_nonempty last_in_set nth_Cons_0 pocket_path_vts_def)
      thus ?thesis
        by (metis hd_last_vts assms(1) in_set_conv_nth diff_Suc_1 gr0_implies_Suc greaterThanLessThan_iff have_wraparound_vertex last_conv_nth le_eq_less_or_eq less_Suc_eq_le less_one nat.simps(3) nat_le_linear snoc_eq_iff_butlast)
    qed
    then have 2: "?r < length vts - 1"
      using r_defined
      unfolding min_nonzero_index_in_set_def nonzero_index_in_set_def
      by (smt (verit, del_insts) Int_iff add.commute add_diff_cancel_left' add_diff_inverse_nat greaterThanLessThan_iff less_imp_diff_less mem_Collect_eq nat_less_le nth_mem)
    show ?thesis using 1 2 by blast
  qed
  have ab: "a = hd vts \<and> b = vts!?r"
    by (metis (no_types, lifting) "2" Suc_1 int_A_nonempty ab_semigroup_add_class.add_ac(1) add_Suc_right b_def construct_pocket_0_def fill_pocket_0_def filled_vts_0 filled_vts_def hd_drop_conv_nth last_snoc le_add_diff_inverse2 min_nonzero_index_in_set_bound nth_Cons_0 plus_1_eq_Suc pocket_path_vts_def take_hd_drop)
  have 3: "{hd vts, vts ! ?r} \<subseteq> frontier (convex hull set vts)"
    using ab assms(1) assms(2) assms(3) b_def construct_pocket_is_pocket is_pocket_0_def pocket_path_vts_def
    by fastforce
  have 4: "\<forall>j\<in>{0<..<?r}. vts ! j \<notin> frontier (convex hull set vts)"
    using r_defined unfolding nonzero_index_in_set_def by fastforce

  have l_int_p: "path_image (linepath (hd vts) (vts ! ?r)) \<inter> path_image ?p = {hd vts, vts ! ?r}"
    using pocket_fill_line_int[OF 1 2 3 4] by blast
  have l_frontier: "path_image (linepath (hd vts) (vts ! ?r)) \<subseteq> frontier (convex hull (set vts))"
    using pocket_fill_line_int[OF 1 2 3 4] by blast

  (* filled_p is a polygon *)
  have "path_image ?filled_p_tl \<inter> path_image ?l = {a, b}"
  proof-
    have "path_image (linepath (hd vts) (vts ! ?r)) \<inter> path_image ?p = {hd vts, vts ! ?r}"
      using pocket_fill_line_int[OF 1 2 3 4] by blast
    moreover have "path_image ?filled_p_tl \<subseteq> path_image ?p"
    proof-
      have "sublist ?filled_vts_tl vts" by (simp add: fill_pocket_0_def filled_vts_def)
      thus ?thesis using \<open>2 \<le> length filled_vts\<close> sublist_path_image_subset by auto
    qed
    moreover have "a \<in> path_image ?filled_p_tl \<and> b \<in> path_image ?filled_p_tl"
      by (smt (verit, best) Cons_nth_drop_Suc Diff_insert_absorb One_nat_def Suc_1 \<open>2 \<le> length filled_vts\<close> drop0 drop_eq_Nil fill_pocket_0_def filled_vts_0 filled_vts_1 filled_vts_def hd_last_vts last_drop last_in_set linorder_not_le list.sel(3) not_less_eq_eq nth_Cons_0 order_less_le_trans pathstart_in_path_image polygon_pathstart pos2 subset_Diff_insert vertices_on_path_image)
    ultimately show ?thesis using ab by auto
  qed
  moreover have hd_filled: "hd ?filled_vts_tl = last [a, b]"
    unfolding filled_vts_def fill_pocket_0_def pocket_path_vts_def construct_pocket_0_def
    by (metis construct_pocket_0_def fill_pocket_0_def filled_vts filled_vts_def hd_append2 last_ConsL last_ConsR list.sel(1) list.sel(3) list.simps(3) pocket_path_vts_def tl_append2)
  moreover have last_filled: "last ?filled_vts_tl = hd [a, b]"
    unfolding filled_vts_def fill_pocket_0_def pocket_path_vts_def construct_pocket_0_def
    using r_defined a_def assms(1) assms(2) assms(3) construct_pocket_is_pocket hd_last_vts is_pocket_0_def pocket_path_vts_def
    by fastforce
  moreover have "loop_free ?filled_p_tl"
  proof-
    have "sublist ?filled_vts_tl vts"
      unfolding filled_vts_def fill_pocket_0_def pocket_path_vts_def construct_pocket_0_def
      using r_defined
      by force
    thus ?thesis
      by (smt (verit, del_insts) Nitpick.size_list_simp(2) Suc_1 \<open>2 \<le> length filled_vts\<close> \<open>b = filled_vts ! 1\<close> a_neq_b assms(1) diff_is_0_eq dual_order.strict_trans1 last_conv_nth last_filled le_antisym length_greater_0_conv length_tl list.sel(1) list.size(3) not_less_eq_eq nth_tl polygon_def pos2 simple_path_def sublist_is_loop_free sublist_length_le)
  qed
  moreover have "loop_free ?l" using a_neq_b linepath_loop_free by blast
  moreover have filled_vts: "filled_vts = [a, b] @ tl ?filled_vts_tl" using filled_vts by blast
  moreover have "arc ?l"
    by (smt (verit) arc_linepath calculation(5) constant_linepath_is_not_loop_free)
  moreover have "arc ?filled_p_tl"
    by (smt (z3) arc_simple_path calculation(2) calculation(3) calculation(4) calculation(7) hd_Nil_eq_last hd_conv_nth last.simps last_conv_nth list.discI list.sel(1) make_polygonal_path_gives_path pathfinish_linepath pathstart_linepath polygon_pathfinish polygon_pathstart simple_path_def)
  moreover have "?l = make_polygonal_path [a, b]"
    using make_polygonal_path.simps by presburger
  ultimately have lf_filled: "loop_free filled_p"
    by (smt (z3) Nat.add_diff_assoc One_nat_def Suc_pred' add_Suc_shift append_butlast_last_id arc_distinct_ends butlast.simps(2) filled_p_def hd_Nil_eq_last hd_conv_nth inf_sup_aci(1) last_ConsR less_numeral_extra(1) list.sel(1) list.simps(3) list.size(3) list.size(4) loop_free_append nth_append_length order_eq_refl plus_1_eq_Suc polygon_pathfinish polygon_pathstart)
  show polygon_filled_p: "polygon filled_p"
    unfolding polygon_def
    by (metis closed_path_def UNIV_def append_is_Nil_conv filled_p_def filled_vts hd_append2 last.simps last_conv_nth last_filled lf_filled list.discI list.exhaust_sel make_polygonal_path_gives_path nth_Cons_0 polygon_pathfinish polygon_pathstart polygonal_path_def rangeI simple_path_def)

  (* good_pocket_path_vts forms a good_polygonal_path of filled_vts from a to b*)
  have "{a, b} \<subseteq> set filled_vts"
    using filled_vts by (smt (z3) UnCI empty_set list.simps(15) set_append subset_iff)
  moreover have pocket_path: "?pocket_path = make_polygonal_path ([a] @ good_pocket_path_vts @ [b])"
    by (metis (no_types, lifting) a_def a_neq_b append_Cons append_Nil append_butlast_last_id b_def good_pocket_path_vts_def hd_Nil_eq_last hd_conv_nth last_conv_nth length_butlast list.collapse list.size(3) tl_append2)
  moreover have "path_image ?pocket_path \<subseteq> path_inside filled_p \<union> {a, b}"
  proof-
    let ?\<p> = ?pocket_path
    let ?\<q> = ?filled_p_tl
    let ?H = "convex hull (path_image ?\<p> \<union> path_image ?\<q>)"
    have b: "pocket_path_vts = take (?r + 1) vts"
      unfolding pocket_path_vts_def construct_pocket_0_def by blast
    moreover then have c': "?filled_vts_tl = drop ?r vts" unfolding filled_vts_def fill_pocket_0_def
      using "2" by fastforce
    ultimately have "vts = pocket_path_vts @ tl ?filled_vts_tl"
      by (metis Suc_eq_plus1 append_take_drop_id drop_Suc tl_drop)
    then have "path_image ?p = path_image ?\<p> \<union> path_image ?\<q>"
      by (metis Suc_1 a_def a_neq_b b_def diff_is_0_eq hd_Nil_eq_last hd_conv_nth hd_filled last.simps last_conv_nth last_filled list.discI list.sel(1) make_polygonal_path_image_append_alt not_less_eq_eq path_image_join polygon_pathfinish polygon_pathstart)
    moreover have "convex hull (path_image ?p) = convex hull (set vts)"                                                                                                        
      by (metis (no_types, lifting) "1" Un_subset_iff convex_hull_of_polygon_is_convex_hull_of_vts hull_Un_subset hull_mono subset_antisym vertices_on_path_image)
    ultimately have H_eq: "?H = convex hull (set vts)" by presburger

    have a: "?p = make_polygonal_path vts \<and> loop_free ?p"
      using assms(1) polygon_def simple_path_def by blast
    have c: "?filled_vts_tl = drop ((?r + 1) - 1) vts" using c' by simp
    have h: "1 \<le> ?r + 1 \<and> ?r + 1 < length vts" using "2" by linarith
    have "path_image ?\<p> \<inter> path_image ?\<q> \<subseteq> {?\<p> 0, ?\<q> 0}"
      using loop_free_split_int[OF a b c _ _ _ h] by (simp add: pathstart_def)
    moreover have "?\<p> 0 \<in> path_image ?\<p> \<and> ?\<p> 0 \<in> path_image ?\<q>"
      by (metis a_def a_neq_b b_def hd_Nil_eq_last hd_conv_nth hd_filled last.simps last_conv_nth last_filled list.sel(1) pathfinish_in_path_image pathstart_def pathstart_in_path_image polygon_pathfinish polygon_pathstart)
    moreover have "?\<q> 0 \<in> path_image ?\<p> \<and> ?\<q> 0 \<in> path_image ?\<q>"
      by (metis a_def a_neq_b b_def hd_Nil_eq_last hd_conv_nth hd_filled last.simps last_conv_nth last_filled list.sel(1) pathfinish_in_path_image pathstart_def pathstart_in_path_image polygon_pathfinish polygon_pathstart)
    ultimately have 4: "path_image ?\<p> \<inter> path_image ?\<q> = {?\<p> 0, ?\<q> 0}" by fastforce

    have 1: "simple_path ?\<p> \<and> simple_path ?\<q>"
      by (metis (no_types, lifting) One_nat_def Suc_1 Suc_le_eq \<open>arc ?filled_p_tl\<close> arc_simple_path assms(1) assms(2) assms(3) construct_pocket_is_pocket is_pocket_0_def le_add2 make_polygonal_path_gives_path numeral_3_eq_3 order_le_less_trans plus_1_eq_Suc pocket_path_vts_def polygon_def simple_path_def sublist_is_loop_free sublist_take)
    have 2: "arc ?\<p> \<and> arc ?\<q>"
      by (metis "1" \<open>arc ?filled_p_tl\<close> a_def a_neq_b b_def hd_Nil_eq_last hd_conv_nth last_conv_nth polygon_pathfinish polygon_pathstart simple_path_cases)
    have 3: "?\<q> 0 = ?\<p> 1 \<and> ?\<q> 1 = ?\<p> 0"
      by (metis "1" a_def append_Cons b_def constant_linepath_is_not_loop_free filled_vts hd_conv_nth last_conv_nth last_filled list.sel(1) list.sel(3) make_polygonal_path.simps(1) pathfinish_def pathstart_def polygon_pathfinish polygon_pathstart simple_path_def)
    have 5: "?\<p> ` {0<..<1} \<subseteq> interior ?H"
    proof-
      have "\<forall>j \<in> {0<..<?r}. vts!j \<notin> frontier (convex hull (set vts))" 
        by (smt (verit, del_insts) Int_iff dual_order.strict_trans greaterThanLessThan_iff int_A_nonempty mem_Collect_eq min_nonzero_index_in_set_defined nonzero_index_in_set_def nth_mem)
      moreover have "?r = length pocket_path_vts - 1" using b h by auto
      moreover have "\<forall>j < ?r. vts!j = pocket_path_vts!j" using b by auto
      ultimately have "\<forall>j \<in> {0<..<length pocket_path_vts - 1}. pocket_path_vts!j \<notin> frontier ?H"
        using H_eq by simp
      moreover have "loop_free ?pocket_path" using "1" simple_path_def by auto
      ultimately show ?thesis
        by (metis vts_interior Un_subset_iff assms(1) assms(2) assms(3) construct_pocket_is_pocket convex_convex_hull hull_subset is_pocket_0_def pocket_path_vts_def)
    qed
    have 6: "path_image (linepath (?\<p> 0) (?\<p> 1)) \<subseteq> frontier ?H"
      by (metis l_frontier H_eq "3" a_def a_neq_b ab b_def hd_Nil_eq_last hd_conv_nth hd_filled last.simps last_filled list.discI list.sel(1) pathstart_def polygon_pathstart)
    have 7: "path_image ?\<q> \<inter> path_image (linepath (?\<p> 0) (?\<p> 1)) = {linepath (?\<p> 0) (?\<p> 1) 0, ?\<q> 0}"
      by (metis "3" \<open>path_image (make_polygonal_path (tl filled_vts)) \<inter> path_image (linepath a b) = {a, b}\<close> a_def a_neq_b b_def hd_Nil_eq_last hd_filled last.simps last_conv_nth last_filled linepath_0' list.sel(1) pathfinish_def polygon_pathfinish)
    have "?\<p> ` {0<..<1} \<subseteq> path_inside (linepath (?\<p> 0) (?\<p> 1) +++ ?\<q>)"
      using pocket_path_interior[OF 1 2 3 4 5 6 7] by blast
    then have "?\<p>`{0<..<1} \<subseteq> path_inside filled_p"
      by (smt (verit) "3" \<open>2 \<le> length filled_vts\<close> a_def a_neq_b b_def filled_p_def filled_vts_0 hd_Nil_eq_last hd_filled last.simps last_filled length_greater_0_conv list.discI list.sel(1) list.sel(3) make_polygonal_path.elims nth_Cons_0 order_less_le_trans pathstart_def polygon_pathstart pos2)
    moreover have "?\<p> 0 = a \<and> ?\<p> 1 = b"
      by (metis "3" a_def a_neq_b b_def hd_Nil_eq_last hd_conv_nth hd_filled last.simps last_filled list.discI list.sel(1) pathstart_def polygon_pathstart)
    ultimately show ?thesis
      by (metis "1" Diff_subset_conv a_def a_neq_b b_def hd_Nil_eq_last hd_conv_nth last_conv_nth polygon_pathfinish polygon_pathstart simple_path_endless sup_commute)
  qed
  moreover have loop_free_pocket_path: "loop_free ?pocket_path"
  proof-
    have "sublist pocket_path_vts vts"
      by (simp add: construct_pocket_0_def pocket_path_vts_def)
    moreover have "loop_free ?p"
      using assms(1) polygon_def simple_path_def by blast
    moreover have "length pocket_path_vts \<ge> 2"
      by (metis Suc_1 a_def a_neq_b b_def diff_is_0_eq' hd_Nil_eq_last hd_conv_nth last_conv_nth not_less_eq_eq)
    moreover have "length vts \<ge> 2"
      by (meson calculation(1) calculation(3) le_trans sublist_length_le)
    ultimately show ?thesis using sublist_is_loop_free by blast
  qed
  ultimately have good_polygonal_path: "good_polygonal_path a good_pocket_path_vts b filled_vts"
    by (metis a_neq_b filled_p_def good_polygonal_path_def)

  (* good_pocket_path_vts forms polygon split path of filled_vts *)
  have filled_vts_as_butlast: "filled_vts = (butlast filled_vts) @ [(butlast filled_vts)!0]"
    by (metis Nitpick.size_list_simp(2) append.right_neutral butlast_conv_take filled_p_def filled_vts have_wraparound_vertex length_butlast length_tl less_Suc_eq_0_disj list.discI list.sel(2) list.sel(3) nth_butlast polygon_filled_p)
  then have filled_p_as_butlast:
      "filled_p = make_polygonal_path ((butlast filled_vts) @ [(butlast filled_vts)!0])"
    unfolding filled_p_def filled_vts_def by argo
  have le: "0 < (1::nat)" by simp

  have filled_0_a: "(butlast filled_vts) ! 0 = a"
    by (metis append_Cons append_Nil butlast.simps(2) filled_vts nth_Cons_0 filled_vts_0)
  have filled_1_b: "(butlast filled_vts) ! 1 = b"
    by (metis (no_types, opaque_lifting) filled_vts_1 filled_vts_as_butlast a_neq_b append_Cons append_Nil butlast_conv_take filled_0_a filled_vts length_butlast less_one linorder_not_le nat_less_le nth_append_length nth_butlast take0)

  have 01: "0 < length (butlast filled_vts) \<and> 1 < length (butlast filled_vts)"
    by (metis One_nat_def Suc_lessI filled_vts_1 filled_vts_as_butlast a_neq_b append_eq_Cons_conv filled_0_a length_greater_0_conv nth_Cons_Suc nth_append_length)
  show is_split_path:
      "is_polygon_split_path (butlast filled_vts) 0 1 good_pocket_path_vts"
    using good_polygonal_path_implies_polygon_split_path
            [OF polygon_filled_p filled_p_as_butlast _ 01 filled_0_a filled_1_b le]
    using good_polygonal_path filled_vts_as_butlast
    by presburger

  (* pocket is a polygon *)
  have polygon_pocket_rev: "polygon (make_polygonal_path (a#([] @ [b] @ (rev good_pocket_path_vts) @ [a])))"
    unfolding is_polygon_split_path_def
    by (smt (z3) "01" One_nat_def add_diff_cancel_left' add_diff_cancel_right' filled_0_a filled_1_b is_polygon_split_path_def is_split_path nth_butlast plus_1_eq_Suc take0)
  moreover have rev_pocket_vts: "rev ?pocket_vts = a#([] @ [b] @ (rev good_pocket_path_vts) @ [a])"
    by (smt (verit) a_def a_neq_b append.left_neutral append_Cons append_butlast_last_id b_def good_pocket_path_vts_def hd_Nil_eq_last hd_append2 hd_conv_nth last_conv_nth length_butlast list.collapse list.size(3) rev.simps(1) rev.simps(2) rev_append)
  ultimately show "polygon pocket"
    by (metis polygon_pocket_rev rev_vts_is_polygon polygon_of_def pocket_def rev_rev_ident)

  (* pocket_path_vts is missing at least one vertex from vts *)
  have "card (set vts) = length (butlast vts)"
    using distinct_vts
    by (smt (verit, ccfv_threshold) Suc_n_not_le_n Un_insert_right append_Nil2 assms(1) butlast_conv_take distinct_card dual_order.strict_trans have_wraparound_vertex hd_conv_nth hd_in_set hd_take insert_absorb length_0_conv length_butlast less_eq_Suc_le linorder_linear list.set(2) not_numeral_le_zero numeral_3_eq_3 polygon_at_least_3_vertices_wraparound polygon_vertices_length_at_least_4 set_append)
  then have "set pocket_path_vts \<subset> set vts"
    unfolding pocket_path_vts_def construct_pocket_0_def
    using r_defined
    by (smt (verit, ccfv_threshold) Cons_nth_drop_Suc One_nat_def Suc_diff_Suc Suc_le_lessD add_diff_cancel_right' assms(1) assms(2) assms(3) butlast_conv_take butlast_snoc card_length construct_pocket_0_def construct_pocket_is_pocket drop0 fill_pocket_0_def filled_vts_def is_pocket_0_def is_polygon_split_path_def is_split_path leD le_less_Suc_eq length_butlast length_drop length_greater_0_conv list.inject numeral_3_eq_3 plus_1_eq_Suc pocket_path_vts_def polygon_at_least_3_vertices_wraparound psubsetI set_take_subset take_eq_Nil add_eq_0_iff_both_eq_0 add_gr_0 cancel_comm_monoid_add_class.diff_cancel diff_zero dual_order.strict_trans filled_p_def length_Cons length_tl less_imp_diff_less list.sel(3) list.size(3) not_less_eq_eq polygon_filled_p zero_less_one zero_neq_one)
  thus "card (set pocket_path_vts) < card (set vts)" by (simp add: psubset_card_mono)

  (* filled_vts is missing at least one vertex from vts *)
  have "card (set vts) = card (set (butlast vts))"
    by (smt (z3) Cons_nth_drop_Suc List.finite_set One_nat_def Suc_1 Suc_le_lessD two_vts_on_frontier distinct_vts hd_last_vts frontier_vts_subset butlast.simps(1) butlast_conv_take card_insert_if card_length card_mono distinct_card drop0 drop_eq_Nil dual_order.trans last_in_set last_tl length_butlast length_greater_0_conv length_tl list.collapse list.sel(3) list.simps(15) set_take_subset verit_la_disequality)
  moreover have "length good_pocket_path_vts \<ge> 1"
    unfolding good_pocket_path_vts_def pocket_path_vts_def construct_pocket_0_def
    using convex_hull_of_nonconvex_polygon_strict_subset[OF _ assms(4), of vts]
    using Suc_le_eq assms(1) assms(2) assms(3) construct_pocket_0_def construct_pocket_is_pocket is_pocket_0_def numeral_3_eq_3
    by auto
  ultimately show "card (set filled_vts) < card (set vts)"
      (* smt call may take 5+ seconds to terminate *)
    unfolding filled_vts_def fill_pocket_0_def good_pocket_path_vts_def pocket_path_vts_def
    by (smt (verit) Nitpick.size_list_simp(2) Suc_1 Suc_diff_Suc Suc_n_not_le_n \<open>2 \<le> length filled_vts\<close> distinct_vts hd_last_vts card_length diff_is_0_eq diff_less distinct_card drop_eq_Nil fill_pocket_0_def filled_vts_def insert_absorb last_drop last_in_set le leI le_less_Suc_eq length_Cons length_butlast length_drop length_tl less_imp_diff_less list.simps(15) order_less_le_trans pocket_path_vts_def)
qed

subsection "Arbitrary Polygon Case"

lemma pick_rotate:
  assumes "polygon_of p vts"
  assumes "all_integral vts"
  obtains p' vts' where "polygon_of p' vts'
    \<and> vts'!0 \<in> frontier (convex hull (set vts'))
    \<and> path_image p' = path_image p
    \<and> all_integral vts'
    \<and> set vts' = set vts"
proof-
  obtain v where v: "v \<in> set vts \<inter> frontier (convex hull (set vts))"
  proof-
    obtain v where "v \<in> set vts \<and> v extreme_point_of (convex hull (set vts))"
      using assms unfolding polygon_of_def
      by (metis List.finite_set card.empty convex_convex_hull convex_hull_eq_empty extreme_point_exists_convex extreme_point_of_convex_hull finite_imp_compact_convex_hull not_numeral_le_zero polygon_at_least_3_vertices)
    then have "v \<in> set vts \<and> v \<in> frontier (convex hull (set vts))"
      by (metis Krein_Milman_frontier List.finite_set convex_convex_hull extreme_point_of_convex_hull finite_imp_compact_convex_hull)
    thus ?thesis using that by blast
  qed
  obtain i where i: "vts!i = v \<and> i < length vts" by (meson IntE in_set_conv_nth v)
  let ?vts_rotated = "rotate_polygon_vertices vts i"
  let ?p_rotated = "make_polygonal_path ?vts_rotated"
  have same_set: "set vts = set ?vts_rotated"
      using assms unfolding polygon_of_def
      using rotate_polygon_vertices_same_set
      by force
  moreover have *: "?vts_rotated!0 \<in> frontier (convex hull (set ?vts_rotated))"
  proof-
    have "?vts_rotated!0 = vts!i"
      using assms unfolding polygon_of_def
      by (metis add_leD2 diff_self_eq_0 have_wraparound_vertex hd_conv_nth i last_snoc less_nat_zero_code list.size(3) nat_le_linear numeral_Bit0 polygon_vertices_length_at_least_4 rotated_polygon_vertices)
    moreover have "vts!i \<in> frontier (convex hull (set vts))" using v i by blast
    ultimately show ?thesis using same_set by argo
  qed
  moreover have "polygon ?p_rotated"
    using rotation_is_polygon assms unfolding polygon_of_def by blast
  moreover have "all_integral ?vts_rotated"
    using rotate_polygon_vertices_same_set assms
    unfolding all_integral_def polygon_of_def by blast
  moreover have "path_image ?p_rotated = path_image p"
    using assms unfolding polygon_of_def using polygon_vts_arb_rotation by force
  moreover then have "path_inside ?p_rotated = path_inside p" unfolding path_inside_def by simp
  ultimately show ?thesis using polygon_of_def that by blast
qed

lemma pick_unrotated:
  fixes p :: "R_to_R2"
  assumes polygon: "polygon p"
  assumes polygonal_path: "p = make_polygonal_path vts"
  assumes int_vertices: "all_integral vts"
  assumes I_is: "I = card {x. integral_vec x \<and> x \<in> path_inside p}" 
  assumes B_is: "B = card {x. integral_vec x \<and> x \<in> path_image p}"
  assumes "vts!0 \<in> frontier (convex hull (set vts))"
  shows "measure lebesgue (path_inside p) = I + B/2 - 1"
  using assms
proof (induct "card (set vts)" arbitrary: vts p I B rule: less_induct)
  case less
  have B_finite: "finite {x. integral_vec x \<and> x \<in> path_image p}"
    using finite_path_image less(2) by auto
  have "set vts \<subseteq> {x. integral_vec x \<and> x \<in> path_image p}"
    using less(3) vertices_on_path_image[of vts] less(4)
    unfolding all_integral_def 
    by auto
  then have card_vts: "card (set vts) \<ge> 3"
    using polygon_at_least_3_vertices[OF less(2) less(3)] card_mono order_trans
    by blast
  have vts_wraparound: "vts ! 0 = vts ! (length vts - 1)"
    using less(2-3) polygon_pathstart polygon_pathfinish
    unfolding polygon_def closed_path_def
    by (metis diff_0_eq_0 length_0_conv)
  then have vts_is: "vts = (butlast vts) @ [vts ! 0]"
    by (metis butlast_conv_take have_wraparound_vertex less.prems(1) less.prems(2))
  have same_set: "set vts = set (butlast (vts))"
    by (metis ListMem_iff Un_insert_right append.right_neutral butlast.simps(2) constant_linepath_is_not_loop_free elem hd_conv_nth insert_absorb less.prems(1) less.prems(2) list.collapse list.simps(15) make_polygonal_path.simps(2) polygon_def set_append simple_path_def vts_is)
  have distinct_butlast_vts: "distinct (butlast vts)"
    using simple_polygonal_path_vts_distinct less(2-3)
    unfolding polygon_def
    by auto
  have card_butlast_vts: "card (set vts) = card (set (butlast vts))"
    using vts_wraparound 
    by (smt (verit, best) List.finite_set butlast_conv_take card_distinct card_length card_mono card_vts diff_is_0_eq diff_less distinct_butlast_vts distinct_card drop_rev dual_order.strict_trans1 le_SucE length_append_singleton length_greater_0_conv less_numeral_extra(1) less_numeral_extra(4) nth_eq_iff_index_eq one_less_numeral_iff order_class.order_eq_iff semiring_norm(77) set_drop_subset set_rev vts_is)
  then have card_set_len_butlast: "card (set vts) = length (butlast vts)"
    using distinct_butlast_vts 
    by (metis distinct_card)
  { assume triangle: "card (set vts) = 3"
    then have "length (butlast vts) = 3"
      using card_set_len_butlast
      by auto
    then have "butlast vts = [vts ! 0, vts ! 1, vts ! 2]"
      by (metis (no_types, lifting) Cons_nth_drop_Suc One_nat_def Suc_1 card_set_len_butlast card_vts drop0 drop_eq_Nil lessI nth_append numeral_3_eq_3 one_less_numeral_iff semiring_norm(77) vts_is zero_less_numeral)
    then have vts_is: "vts = [vts ! 0, vts ! 1, vts ! 2, vts ! 0]"
      using vts_is by auto
    then have p_make_triangle: "p = make_triangle (vts ! 0) (vts ! 1) (vts ! 2)"
      using less(3) unfolding make_triangle_def by simp
    then have not_collinear: "\<not> collinear {vts ! 0, vts ! 1, vts ! 2}"
      using vts_is less(2) polygon_vts_not_collinear[of p vts] unfolding polygon_of_def make_triangle_def
      by (smt (verit, ccfv_threshold) insert_absorb2 insert_commute list.set(1) list.simps(15))
    have  all_integral: "all_integral [vts ! 0, vts ! 1, vts ! 2]"
      using less.prems(3) vts_is unfolding all_integral_def 
      by (simp add: \<open>butlast vts = [vts ! 0, vts ! 1, vts ! 2]\<close> in_set_butlastD)
    have distinct: "distinct [vts ! 0, vts ! 1, vts ! 2]"
      using \<open>butlast vts = [vts ! 0, vts ! 1, vts ! 2]\<close> distinct_butlast_vts by presburger
    have pick_triangle: "pick_triangle p (vts ! 0) (vts ! 1) (vts ! 2)"
      using pick_triangle p_make_triangle less(2) not_collinear all_integral distinct
      by simp
    then have ?case
      using pick_triangle_lemma[OF p_make_triangle all_integral distinct not_collinear] less.prems(4-5)
      by blast
  } moreover
  { assume non_triangle: "card (set vts) > 3"
    { assume convex: "convex (path_image p \<union> path_inside p)"
      then obtain a b where "good_linepath a b vts"
        using convex_polygon_has_good_linepath non_triangle
        by (metis inf_sup_aci(5) less.prems(1) less.prems(2))
      then have ab_prop: "a \<noteq> b \<and> {a, b} \<subseteq> set vts \<and> path_image (linepath a b) \<subseteq> path_inside p \<union> {a, b}"
        unfolding good_linepath_def less.prems(2) by presburger
      then have ab_prop_restate: "a \<noteq> b \<and> a \<in> set (butlast vts) \<and> b \<in> set (butlast vts)"
        using same_set
        by simp
      have good_linepath_ab: "good_linepath a b ((butlast vts) @ [(butlast vts) ! 0])"
        using ab_prop vts_is unfolding good_linepath_def 
        using ab_prop_restate empty_set hd_append2 hd_conv_nth insert_absorb insert_not_empty less.prems(2) same_set
        by (smt (z3))
      then have good_linepath_ba: "good_linepath b a ((butlast vts) @ [(butlast vts) ! 0])"
        using good_linepath_comm good_linepath_def by blast
      obtain i1 j1 where ij_prop: "i1 < length (butlast vts) \<and> j1 < length (butlast vts) \<and>
          butlast vts ! i1 = a \<and>
          butlast vts ! j1 = b \<and> i1 \<noteq> j1"
        using ab_prop_restate 
        by (metis distinct_Ex1 distinct_butlast_vts)
      have i_lt_then: "i1 < j1 \<Longrightarrow> is_polygon_split (butlast vts) i1 j1"
        using good_linepath_implies_polygon_split[OF less(2), of "butlast vts"] vts_is same_set
        using ij_prop good_linepath_ab good_linepath_ba
        by (metis ab_prop_restate length_pos_if_in_set less.prems(2) nth_butlast)
      have j_lt_then: "j1 < i1 \<Longrightarrow> is_polygon_split (butlast vts) j1 i1"
        using good_linepath_implies_polygon_split[OF less(2), of "butlast vts"] vts_is same_set
        using ij_prop good_linepath_ab good_linepath_ba
        by (metis ab_prop_restate length_pos_if_in_set less.prems(2) nth_butlast)
      obtain i j where polygon_split: "is_polygon_split (butlast vts) i j"
        using i_lt_then j_lt_then ij_prop 
        by (meson nat_neq_iff)
      then have ij_prop: "i < length (butlast vts) \<and> j < length (butlast vts) \<and> i < j"
        unfolding is_polygon_split_def 
        by blast
  
      (* Now can cut, IH applies relatively immediately *)
      have p_is: "p = make_polygonal_path (butlast vts @ [butlast vts ! 0])"
        using less(3) vts_is  
        by (metis length_greater_0_conv nth_butlast same_set set_empty)
  
      let ?vts1 = "take i (butlast vts)"
      let ?vts2 = "take (j - i - 1) (drop (Suc i) (butlast vts))"
      let ?vts3 = "drop (j - i) (drop (Suc i) (butlast vts))"
  
      let ?vtsp1 = "(butlast vts ! i # ?vts2 @ [butlast vts ! j, butlast vts ! i])"
      have finite_butlast: "finite (set (butlast vts))"
        by blast
      have vtsp1_subset: "set ?vtsp1 \<subseteq> set (butlast vts)"
        using ij_prop 
        by (smt (verit, del_insts) Un_commute append_Cons append_Nil dual_order.trans insert_subset list.simps(15) nth_mem set_append set_drop_subset set_take_subset)

      let ?p1 = "make_polygonal_path ?vtsp1"
      let ?I1 = "card {x. integral_vec x \<and> x \<in> path_inside ?p1}"
      let ?B1 = "card {x. integral_vec x \<and> x \<in> path_image ?p1}"
      have polygon_p1: "polygon ?p1"
        using polygon_split unfolding is_polygon_split_def by metis

      let ?vtsp2 = "?vts1 @ [butlast vts ! i, butlast vts ! j] @ ?vts3 @ [butlast vts ! 0]"
      let ?p2 = "make_polygonal_path ?vtsp2"
      have polygon_p2: "polygon ?p2"
        using polygon_split unfolding is_polygon_split_def by metis

      (* The linepath between vts !i and vts ! (i+1) can't cut the polygon *)
      have j_neq: "j \<noteq> i + 1"
        by (smt (verit, ccfv_SIG) One_nat_def Suc_n_not_le_n Suc_numeral add_Suc_shift add_implies_diff cancel_ab_semigroup_add_class.diff_right_commute length_Cons length_append list.size(3) numeral_3_eq_3 plus_1_eq_Suc polygon_p1 polygon_vertices_length_at_least_4 semiring_norm(2) semiring_norm(8) take_eq_Nil)
      have subset1: "set (take i (butlast vts)) \<subseteq> set (butlast vts)"
        using ij_prop by (meson set_take_subset)
      have subset2: "set ([butlast vts ! i, butlast vts ! j]) \<subseteq> set (butlast vts)"
        using ij_prop by simp
      have subset3: "set (take i (butlast vts) @
          [butlast vts ! i, butlast vts ! j]) \<subseteq> set (butlast vts)"
        using subset1 subset2 by auto
      have subset4: "set (drop (j - i) (drop (Suc i) (butlast vts)) @ [butlast vts ! 0])  \<subseteq> set (butlast vts)"
        using ij_prop set_drop_subset 
        by (metis (no_types, opaque_lifting) Un_commute append_Cons append_Nil card_set_len_butlast drop0 drop_drop drop_eq_Nil2 hd_append2 hd_conv_nth in_set_conv_decomp insert_subset linorder_not_less list.simps(15) non_triangle not_less_eq not_less_iff_gr_or_eq numeral_3_eq_3 same_set set_append snoc_eq_iff_butlast vts_is)
      then have main_subset: "set ?vtsp2 \<subseteq> set (butlast vts)"
        using subset3 subset4 by simp

      have subset_p1: "set ?vtsp1 \<subset> set (butlast vts)"
        using ij_prop distinct_butlast_vts
      proof-
        have "card (set ?vtsp2) \<ge> 3"
          using polygon_p2 polygon_at_least_3_vertices by blast
        moreover have "set ?vtsp1 \<inter> set ?vtsp2 = {vts!i, vts!j}"
        proof-
          have "set ?vts2 \<inter> set ?vts3 = {}"
            by (metis append_take_drop_id diff_le_self distinct_append distinct_butlast_vts set_take_disj_set_drop_if_distinct)
          moreover have "set ?vts2 \<inter> set ?vts1 = {}"
          proof-
            have "set ?vts2 \<subseteq> set (drop (i + 1) vts)"
              by (metis add.commute drop_butlast in_set_butlastD in_set_takeD plus_1_eq_Suc subset_code(1))
            moreover have "set (drop (i + 1) vts) \<inter> set ?vts1 \<subseteq> {last vts}"
            proof-
              have "set (drop (i + 1) (butlast vts)) \<inter> set ?vts1 = {}"
                by (simp add: Int_commute set_take_disj_set_drop_if_distinct distinct_butlast_vts)
              moreover have "set (drop (i + 1) vts) = set (drop (i + 1) (butlast vts)) \<union> {last vts}"
              proof-
                have "drop (i + 1) vts = (drop (i + 1) ((butlast vts) @ [last vts]))"
                  by (metis last_snoc vts_is)
                thus ?thesis using ij_prop by force
              qed
              ultimately show ?thesis by blast
            qed
            moreover have "last vts \<notin> set ?vts2"
              by (metis card_set_len_butlast card_vts distinct_butlast_vts dual_order.strict_trans1 in_set_takeD index_nth_id last_snoc nth_butlast numeral_3_eq_3 set_drop_if_index vts_is zero_less_Suc)
            ultimately show ?thesis by force
          qed
          moreover have "vts!i \<in> set ?vtsp1" by (metis ij_prop list.set_intros(1) nth_butlast)
          moreover have "vts!j \<in> set ?vtsp1" using ij_prop nth_butlast by fastforce
          moreover have "vts!i \<in> set ?vtsp2"
            by (metis UnCI ij_prop list.set_intros(1) nth_butlast set_append)
          moreover have "vts!j \<in> set ?vtsp2" using ij_prop nth_butlast by force
          moreover have "set ?vtsp1 = set ?vts2 \<union> {vts!i, vts!j}"
            by (smt (verit, ccfv_SIG) Un_insert_right empty_set ij_prop insert_absorb2 insert_commute list.simps(15) nth_butlast set_append)
          moreover have "set ?vtsp2 = set ?vts1 \<union> set ?vts3 \<union> {vts!i, vts!j, vts!0}"
          proof-
            have "vts!i = (butlast vts)!i" by (metis ij_prop nth_butlast)
            moreover have "vts!j = (butlast vts)!j" by (metis ij_prop nth_butlast)
            moreover have "vts!0 = (butlast vts)!0"
              by (metis ij_prop leD length_greater_0_conv nth_butlast take_all_iff take_eq_Nil)
            ultimately show ?thesis by force
          qed
          moreover have "vts!0 \<notin> set ?vts2"
            by (metis distinct_butlast_vts in_set_conv_decomp in_set_takeD index_nth_id length_pos_if_in_set nth_butlast same_set set_drop_if_index vts_is zero_less_Suc)
          ultimately show ?thesis by blast
        qed
        ultimately have "card (set ?vtsp2) > card (set ?vtsp1 \<inter> set ?vtsp2)"
          by (smt (verit, del_insts) card_length empty_set leI le_trans length_Cons list.simps(15) list.size(3) not_less_eq_eq numeral_3_eq_3)
        then have "\<exists>v. v \<in> set ?vtsp2 \<and> v \<notin> (set ?vtsp1 \<inter> set ?vtsp2)"
          by (smt (verit) Int_lower2 Orderings.order_eq_iff less_not_refl subset_code(1))
        then obtain v where "v \<in> set ?vtsp2 - set ?vtsp1" by blast
        thus ?thesis
          by (metis main_subset Diff_eq_empty_iff length_pos_if_in_set less_numeral_extra(3) list.set(1) list.size(3) psubsetI vtsp1_subset)
      qed
      then have "card (set ?vtsp1) < card (set (butlast vts))"
        using card_subset_eq[OF finite_butlast]  
        by (meson finite_butlast psubset_card_mono)
      then have card_lt_p1: "card (set ?vtsp1) < card (set vts)"
        using same_set by argo
      have "set ?vtsp1 \<subseteq> set vts"
        using ij_prop 
        using same_set subset_p1 by blast
      then have all_integral_p1: "all_integral ?vtsp1"
        using less(4) unfolding all_integral_def 
        by blast
  
      obtain p1' vtsp1' where p1_rot: "polygon_of p1' vtsp1'
          \<and> vtsp1'!0 \<in> frontier (convex hull (set vtsp1'))
          \<and> path_image p1' = path_image ?p1
          \<and> all_integral vtsp1'
          \<and> set vtsp1' = set ?vtsp1"
        using pick_rotate less polygon_p1 unfolding polygon_of_def
        using all_integral_p1
        by blast
  
      let ?I1' = "card {x. integral_vec x \<and> x \<in> path_inside p1'}"
      let ?B1' = "card {x. integral_vec x \<and> x \<in> path_image p1'}"
  
      have "measure lebesgue (path_inside p1') = real ?I1' + real ?B1' / 2 - 1"
        using less(1) polygon_split card_lt_p1 p1_rot unfolding polygon_of_def by force
      then have indh1: "Sigma_Algebra.measure lebesgue (path_inside ?p1) = real ?I1 + real ?B1 / 2 - 1"
        using p1_rot unfolding path_inside_def by metis
  
      have "vts ! (i+1) \<notin> set (take i (butlast vts))"
        using distinct_butlast_vts j_neq ij_prop
      proof-
        have "i + 1 < length vts - 2" using distinct_butlast_vts j_neq ij_prop by fastforce
        then have "vts ! (i+1) = (butlast vts) ! (i+1)" by (simp add: nth_butlast)
        moreover then have "\<forall>j < i + 1. (butlast vts) ! j \<noteq> (butlast vts) ! (i+1)"
          using distinct_butlast_vts distinct_nth_eq_iff ij_prop by fastforce
        moreover have "set (take i (butlast vts)) = {vts!j | j. j < i}"
        proof-
          have "set (take i (butlast vts)) \<subseteq> {vts!j | j. j < i}"
            by (smt (verit, ccfv_SIG) dual_order.strict_trans ij_prop in_set_conv_nth length_take mem_Collect_eq min.absorb4 nth_butlast nth_take subsetI)
          moreover have "{vts!j | j. j < i} \<subseteq> set (take i (butlast vts))"
            by (smt (verit, del_insts) dual_order.strict_trans ij_prop in_set_conv_nth length_take mem_Collect_eq min.absorb4 nth_butlast nth_take subsetI)
          ultimately show ?thesis by blast
        qed
        ultimately show ?thesis
          by (metis (no_types, lifting) add.commute ij_prop in_set_conv_nth length_take min.absorb4 nth_take trans_less_add2)
      qed
      moreover have "vts ! (i+1) \<noteq> butlast vts ! i"
        by (metis (no_types, lifting) ij_prop add.commute add_cancel_right_right distinct_butlast_vts distinct_nth_eq_iff less_trans_Suc nth_append plus_1_eq_Suc vts_is zero_neq_one)
      moreover have "vts ! (i+1) \<noteq> butlast vts ! j"
        by (metis (no_types, lifting) add.commute distinct_butlast_vts distinct_nth_eq_iff ij_prop j_neq less_trans_Suc nth_append plus_1_eq_Suc vts_is)
      ultimately have "vts ! (i+1) \<notin> set (take i (butlast vts) @
          [butlast vts ! i, butlast vts ! j])" by force
      moreover have "vts ! (i+1) \<notin> set (drop (j - i) (drop (Suc i) (butlast vts)) @ [butlast vts ! 0])"
      proof-
        have "vts ! (i+1) \<notin> set (drop (j - i + Suc i) (butlast vts))"
          by (metis (no_types, lifting) add.commute distinct_butlast_vts ij_prop index_nth_id less_add_same_cancel2 less_trans_Suc nth_append plus_1_eq_Suc set_drop_if_index vts_is zero_less_diff)
        moreover have "vts ! (i+1) \<noteq> butlast vts ! 0"
          by (metis (no_types, lifting) ij_prop Nil_is_append_conv add.commute distinct_butlast_vts distinct_nth_eq_iff length_greater_0_conv less_trans_Suc list.discI nat.distinct(1) nth_append plus_1_eq_Suc same_set set_empty vts_is)
        ultimately show ?thesis by simp
      qed
      ultimately have "vts ! (i+1) \<notin> set (take i (butlast vts) @
           [butlast vts ! i, butlast vts ! j] @
           drop (j - i) (drop (Suc i) (butlast vts)) @ [butlast vts ! 0])"
        by auto
      then have subset_butlast_p2: "set ?vtsp2 \<subset> set (butlast vts)"
        using main_subset ij_prop
        by (metis (no_types, lifting) antisym_conv2 length_butlast less_diff_conv nth_mem same_set) 
      then have card_lt_p2: "card (set ?vtsp2) < card (set vts)"
        using card_subset_eq[OF finite_butlast]  
        by (metis finite_butlast psubset_card_mono same_set)
      have subset_p2: "set ?vtsp2 \<subset> set vts"
        using subset_butlast_p2 same_set
        by presburger
      then have all_integral_p2: "all_integral ?vtsp2"
        using less(4) unfolding all_integral_def 
        by blast
    
      let ?p2 = "make_polygonal_path (take i (butlast vts) @ [butlast vts ! i, butlast vts ! j] @
          drop (j - i) (drop (Suc i) (butlast vts)) @ [butlast vts ! 0])"
      let ?I2 = "card {x. integral_vec x \<and> x \<in> path_inside ?p2}"
      let ?B2 = "card {x. integral_vec x \<and> x \<in> path_image ?p2}"
      have polygon_p2: "polygon ?p2"
        using polygon_split unfolding is_polygon_split_def by metis
  
      have vtsp2_0: "?vtsp2!0 \<in> frontier (convex hull (set ?vtsp2))"
      proof-
        have "?vtsp2!0 = vts!0"
          by (metis (no_types, lifting) append_Cons ij_prop length_greater_0_conv less_nat_zero_code nat_neq_iff nth_append nth_append_length nth_butlast nth_take take_eq_Nil)
        then have "?vtsp2!0 \<in> frontier (convex hull (set vts))" using less by argo
        moreover have "?vtsp2!0 \<in> (convex hull (set ?vtsp2))"
          by (meson append_is_Nil_conv hull_inc length_greater_0_conv neq_Nil_conv nth_mem)
        moreover have "convex hull (set ?vtsp2) \<subseteq> convex hull (set vts)"
          by (metis hull_mono main_subset same_set)
        ultimately show ?thesis using in_frontier_in_subset by blast
      qed
  
      have indh2: "Sigma_Algebra.measure lebesgue (path_inside ?p2) = real ?I2 + real ?B2 / 2 - 1"
        using less(1)[OF card_lt_p2 polygon_p2 _ all_integral_p2 _ _ vtsp2_0] polygon_split
        by blast
        
      have "all_integral (butlast vts) \<Longrightarrow>
          Sigma_Algebra.measure lebesgue (path_inside p) = real (card {x. integral_vec x \<and> x \<in> path_inside p}) + real (card {x. integral_vec x \<and> x \<in> path_image p}) / 2 - 1"
        using pick_split_union
          [OF polygon_split, of ?vts1 ?vts2 ?vts3 "butlast vts ! i" "butlast vts ! j" p ?p1 ?p2 ?I1 ?B1 ?I2 ?B2]
        using indh1 indh2 p_is 
        by blast
      then have ?case
        using less(4-6) unfolding all_integral_def
        using same_set by presburger
    } moreover
    { assume non_convex: "\<not> (convex (path_image p \<union> path_inside p))"
      let ?vts_ch = "set vts \<inter> frontier (convex hull (set vts))"
      have finite_vts: "finite (set vts)"
        using less 
        by force
      have subset_ch: "?vts_ch \<subset> set vts"
        using vts_subset_frontier
        using less.prems(1) less.prems(2) non_convex polygon_of_def by blast
      then have card_ch: "card (?vts_ch) < card (set vts)" 
        using finite_vts 
        by (simp add: psubset_card_mono)
  
      let ?vts_ch_list = "filter (\<lambda>v. v \<in> ?vts_ch) vts"
      (* don't need to know that this is a polygon, but we do need to know that
        filling in one (i.e. the first) pocket is a polygon *)
  
      let ?r_idx = "min_index_not_in_set vts ?vts_ch"
      let ?r = "?r_idx - 1"
      let ?rotated_vts = "rotate_polygon_vertices vts ?r"
      let ?pr = "make_polygonal_path ?rotated_vts"
  
      have subset_ch_list: "set ?vts_ch_list \<subset> set vts" using subset_ch by auto
      then have r_defined: "index_not_in_set vts ?vts_ch ?r_idx
          \<and> (\<forall>j < ?r_idx. \<not> index_not_in_set vts ?vts_ch j)"
        using min_index_not_in_set_defined[of ?vts_ch vts] by fastforce
  
      have pr_image: "path_image p = path_image ?pr"
        using polygon_vts_arb_rotation less by blast
      then have "measure lebesgue (path_inside ?pr) = measure lebesgue (path_inside p)"
        unfolding path_inside_def by presburger
      have rotated_vts_set: "set ?rotated_vts = set vts"
        using less.prems(1) less.prems(2) rotate_polygon_vertices_same_set by auto
      then have "card (set ?rotated_vts) = card (set vts)" by argo
      have polygon_rotation: "polygon ?pr" using rotation_is_polygon less by blast
  
      (* vts of linepath which makes up pocket, not including the "closing" linepath which lies
        on the frontier of the convex hull *)
      let ?pocket_path_vts = "construct_pocket_0 ?rotated_vts ?vts_ch" 
  
      let ?a = "hd ?pocket_path_vts"
      let ?b = "last ?pocket_path_vts"
      let ?l = "linepath ?a ?b"
  
      have "vts!0 \<in> ?vts_ch"
        by (metis IntI length_greater_0_conv less.prems(6) nth_mem snoc_eq_iff_butlast vts_is)
      then have vts_r: "vts!?r \<in> ?vts_ch"
        using min_index_not_in_set_0 subset_ch by presburger
      moreover have rotated_0: "?rotated_vts!0 = vts!?r"
        using rotated_polygon_vertices[of ?rotated_vts vts ?r ?r]
        by (metis (no_types, lifting) Suc_1 Suc_leI card_gt_0_iff card_set_len_butlast diff_is_0_eq' finite_vts hd_conv_nth index_not_in_set_def le_refl length_butlast less_imp_diff_less mem_Collect_eq r_defined set_empty snoc_eq_iff_butlast vts_is zero_less_diff)
      ultimately have rotated_0_in: "?rotated_vts!0 \<in> ?vts_ch" by presburger
      then have b_in: "?b \<in> set vts"
        using construct_pocket_0_last_in_set[of ?rotated_vts ?vts_ch]
        by (smt (verit, ccfv_threshold) Int_iff One_nat_def closed_path_def Suc_leI card_0_eq card_set_len_butlast empty_iff finite_vts last_conv_nth last_in_set last_tl length_butlast length_greater_0_conv length_tl list.size(3) polygon_def polygon_pathfinish polygon_pathstart polygon_rotation rotate_polygon_vertices_same_length set_empty)
  
      have "2 \<le> card ?vts_ch"
        using convex_hull_two_vts_on_frontier
        by (metis One_nat_def Suc_1 add_leD2 card_vts numeral_3_eq_3 plus_1_eq_Suc)
      moreover have "?vts_ch \<subseteq> set ?rotated_vts"
        using less.prems(1) less.prems(2) rotate_polygon_vertices_same_set by force
      moreover have "distinct (butlast ?rotated_vts)"
        using polygon_def polygon_rotation simple_polygonal_path_vts_distinct by blast
      moreover have hd_last_rotated: "hd ?rotated_vts = last ?rotated_vts"
        by (metis have_wraparound_vertex hd_conv_nth polygon_rotation snoc_eq_iff_butlast)
      ultimately have a_neq_b: "?a \<noteq> ?b"
        using construct_pocket_0_first_last_distinct
        by (smt (verit) Collect_cong Int_def mem_Collect_eq set_filter)
  
      (* we rotate, so we assume the pocket starts at 0 *)
  
      (* construct vertices for the pocket polygon *)
      let ?pocket_vts = "?pocket_path_vts @ [?rotated_vts!0]"
      (* the interior of the polygon pocket --- this should be the good linepath of the filled in polygon*)
      let ?pocket_good_path_vts = "tl (butlast ?pocket_path_vts)"
      (*let ?filled_vts = "filter (\<lambda>v. v \<notin> set ?pocket_good_path_vts) ?rotated_vts"*)
      let ?filled_vts = "fill_pocket_0 ?rotated_vts (length ?pocket_path_vts)"
      let ?filled_vts_tl = "tl ?filled_vts"
      let ?filled_p_tl = "make_polygonal_path ?filled_vts_tl"
      let ?filled_p = "make_polygonal_path ?filled_vts"
      let ?pocket_path = "make_polygonal_path ?pocket_path_vts"
      let ?pocket = "make_polygonal_path ?pocket_vts"

      have non_convex_rot: "\<not> convex (path_image ?pr \<union> path_inside ?pr)"
        using non_convex by (simp add: path_inside_def pr_image)

      have 0: "?rotated_vts!0 \<in> frontier (convex hull (set ?rotated_vts))"
        using less.prems(1) less.prems(2) rotate_polygon_vertices_same_set rotated_0_in by fastforce
      have 1: "?rotated_vts!1 \<notin> frontier (convex hull (set ?rotated_vts))"
      proof-
        have "?rotated_vts!1 = vts!(?r + 1)"
          using rotated_polygon_vertices[of ?rotated_vts vts ?r "?r + 1"]
          by (smt (verit, ccfv_threshold) Suc_1 Suc_leI card_gt_0_iff card_set_len_butlast diff_is_0_eq' finite_vts hd_conv_nth index_not_in_set_def le_refl length_butlast less_imp_diff_less mem_Collect_eq r_defined set_empty snoc_eq_iff_butlast vts_is zero_less_diff Suc_diff_Suc add.commute add_diff_cancel_left' bot_nat_0.not_eq_extremum less_imp_le_nat plus_1_eq_Suc)
        also have "... \<notin> frontier (convex hull (set ?rotated_vts))"
          using r_defined unfolding index_not_in_set_def
          by (smt (verit, best) Int_iff Suc_leI add.commute add_diff_inverse_nat bot_nat_0.not_eq_extremum diff_is_0_eq' mem_Collect_eq nat_less_le nth_mem plus_1_eq_Suc rotated_vts_set vts_r zero_less_diff)
        finally show ?thesis .
      qed
      then have split:
          "is_polygon_split_path (butlast ?filled_vts) 0 1 ?pocket_good_path_vts"
          and polygon_filled_p: "polygon ?filled_p"
          and polygon_pocket: "polygon ?pocket"
          and pocket_path_vts_card: "card (set ?pocket_path_vts) < card (set vts)"
          and filled_vts_card: "card (set ?filled_vts) < card (set vts)"
        using pocket_path_good[OF _ 0 1 non_convex_rot] polygon_rotation rotated_vts_set apply argo
        using pocket_path_good[OF _ 0 1 non_convex_rot] polygon_rotation rotated_vts_set apply argo
        using pocket_path_good[OF _ 0 1 non_convex_rot] polygon_rotation rotated_vts_set
          apply (metis add_gr_0 construct_pocket_0_def nth_take zero_less_one)
        using pocket_path_good[OF _ 0 1 non_convex_rot] polygon_rotation rotated_vts_set apply argo
        using pocket_path_good[OF _ 0 1 non_convex_rot] polygon_rotation rotated_vts_set by argo
  
      have vts_0_frontier: "?rotated_vts!0 \<in> frontier (convex hull (set vts))"
        using rotated_0_in by simp 
      have filled_0: "?filled_vts!0 = ?rotated_vts!0"
        by (metis convex_hull_empty empty_set fill_pocket_0_def frontier_empty hd_conv_nth length_pos_if_in_set less.prems(6) less_numeral_extra(3) list.size(3) nth_Cons_0 rotated_vts_set)
      have pocket_0: "?pocket_vts!0 = ?rotated_vts!0" 
        unfolding construct_pocket_0_def 
        by (simp add: less_numeral_extra(1) nth_append trans_less_add2) 

      have subset_pocket_path_vts: "set ?pocket_path_vts \<subseteq> set vts" 
        using construct_pocket_0_subset_vts 
        by (metis construct_pocket_0_def less.prems(1) less.prems(2) rotate_polygon_vertices_same_set set_take_subset) 
      moreover have "set ?pocket_good_path_vts \<subseteq> set ?pocket_path_vts" 
        by (smt (verit, best) butlast_conv_take list.exhaust_sel list.sel(2) set_subset_Cons set_take_subset subset_trans) 
      ultimately have subset_pocket_good_path: "set ?pocket_good_path_vts \<subseteq> set vts" by blast 
      then have subset_pocket: "set ?pocket_vts \<subseteq> set vts" 
        by (metis (mono_tags, lifting) have_wraparound_vertex less.prems(1) less.prems(2) polygon_rotation rotate_polygon_vertices_same_set set_append subset_code(1) subset_pocket_path_vts sup.bounded_iff) 
      have "set ?filled_vts \<subseteq> set ?rotated_vts"
        unfolding fill_pocket_0_def
        by (metis b_in hd_in_set insert_subset length_pos_if_in_set less_numeral_extra(3) list.simps(15) list.size(3) rotated_vts_set set_drop_subset)
      then have subset_filled: "set ?filled_vts \<subseteq> set vts"
        using rotated_vts_set by blast
  
      have taut1: "?filled_p = make_polygonal_path ?filled_vts" by blast
      have all_integral_filled_vts: "all_integral ?filled_vts"
        using subset_filled less by (meson all_integral_def subset_iff)
      have taut2: "card (integral_inside ?filled_p) = card {x. integral_vec x \<and> x \<in> path_inside ?filled_p}"
        unfolding integral_inside by blast
      have taut3: "card (integral_boundary ?filled_p) = card {x. integral_vec x \<and> x \<in> path_image ?filled_p}"
        unfolding integral_boundary by blast
      have filled_vts_0_frontier: "?filled_vts!0 \<in> frontier (convex hull (set ?filled_vts))"
      proof-
        have "?filled_vts!0 \<in> frontier (convex hull set vts)"
          using filled_0 vts_0_frontier by presburger
        moreover have "?filled_vts!0 \<in> convex hull (set ?filled_vts)"
          by (metis have_wraparound_vertex hull_inc in_set_conv_decomp polygon_filled_p)
        moreover have "set ?filled_vts \<subseteq> set vts" using subset_filled by force
        ultimately show ?thesis using in_frontier_in_subset_convex_hull by blast
      qed
  
      have ih_filled: "measure lebesgue (path_inside ?filled_p)
          = card (integral_inside ?filled_p) + ((card (integral_boundary ?filled_p)) / 2) - 1"
        using less(1)[OF filled_vts_card polygon_filled_p taut1 all_integral_filled_vts taut2 taut3 filled_vts_0_frontier]
        by blast
  
      (* pocket is not entire polygon; last vertex of pocket linepath is not last vertex of polygon *)
      have "set ?pocket_path_vts \<subset> set vts"
        using pocket_path_vts_card subset_pocket_path_vts by force
      moreover have pocket_path_set: "set ?pocket_path_vts = set ?pocket_vts"
        by (smt (verit) Nil_is_append_conv rotated_0 a_neq_b append_Cons append_Nil hd_Nil_eq_last hd_append2 hd_conv_nth hd_in_set insert_absorb list.simps(15) pocket_0 rev_append set_append set_rev)
      ultimately have "set ?pocket_vts \<subset> set vts" by blast
      then have pocket_vts_card: "card (set ?pocket_vts) < card (set vts)"
        by (meson finite_vts psubset_card_mono)
      have all_integral_pocket_vts: "all_integral ?pocket_vts"
        using subset_pocket less unfolding all_integral_def by blast
      have taut1: "?pocket = make_polygonal_path ?pocket_vts" by blast
      have taut2: "card (integral_inside ?pocket) = card {x. integral_vec x \<and> x \<in> path_inside ?pocket}"
        unfolding integral_inside by blast
      have taut3: "card (integral_boundary ?pocket) = card {x. integral_vec x \<and> x \<in> path_image ?pocket}"
        unfolding integral_boundary by blast
      have pocket_vts_0_frontier: "?pocket_vts!0 \<in> frontier (convex hull (set ?pocket_vts))"
      proof-
        have "?pocket_vts!0 \<in> frontier (convex hull set vts)"
          using pocket_0 vts_0_frontier by presburger
        moreover have "?pocket_vts!0 \<in> convex hull (set ?pocket_vts)"
          by (smt (verit, del_insts) hull_inc in_set_conv_decomp pocket_0)
        moreover have "set ?pocket_vts \<subseteq> set vts" using subset_pocket by force
        ultimately show ?thesis using in_frontier_in_subset_convex_hull by blast
      qed
  
      have ih_pocket: "measure lebesgue (path_inside ?pocket) = card (integral_inside ?pocket) + ((card (integral_boundary ?pocket)) / 2) - 1"
        using less(1)[OF pocket_vts_card polygon_pocket taut1 all_integral_pocket_vts taut2 taut3 pocket_vts_0_frontier]
        by blast
  
      let ?i = "0::nat"
      let ?j = "1::nat"
      let ?vts = "butlast ?filled_vts"
      let ?vts1 = "[]"
      let ?vts2 = "[]"
      let ?vts3 = "butlast (drop 2 ?filled_vts)"
      let ?cutvts = "?pocket_good_path_vts"
      let ?p = "?filled_p"
      let ?p1 = "make_polygonal_path (?a # ?vts2 @ [?b] @ rev ?cutvts @ [?a])"
      let ?p2 = "?pr"
      let ?I1 = "card {x. integral_vec x \<and> x \<in> path_inside ?p1}"
      let ?B1 = "card {x. integral_vec x \<and> x \<in> path_image ?p1}"
      let ?I2 = "card {x. integral_vec x \<and> x \<in> path_inside ?p2}"
      let ?B2 = "card {x. integral_vec x \<and> x \<in> path_image ?p2}"
      let ?I = "card {x. integral_vec x \<and> x \<in> path_inside ?p}"
      let ?B = "card {x. integral_vec x \<and> x \<in> path_image ?p}"
  
      have "rev ?pocket_vts = (?a # ?vts2 @ [?b] @ rev ?cutvts @ [?a])"
        by (smt (verit) a_neq_b append_Nil append_butlast_last_id hd_Nil_eq_last hd_append2 hd_conv_nth last_conv_nth length_butlast list.collapse list.size(3) pocket_0 rev.simps(2) rev_append rev_rev_ident snoc_eq_iff_butlast)
      then have pocket_rev_image: "path_image ?pocket = path_image ?p1"
        using polygon_at_least_3_vertices polygon_pocket card_length
        by (smt (verit, best) One_nat_def Suc_1 le_add2 le_trans numeral_3_eq_3 plus_1_eq_Suc rev_vts_path_image polygon_at_least_3_vertices polygon_pocket card_length)
      then have pocket_rev_inside: "path_inside ?pocket = path_inside ?p1"
        unfolding path_inside_def by argo
  
      have split': "is_polygon_split_path ?vts ?i ?j ?cutvts" using split by blast
      have 0: "?vts1 = take ?i ?vts" by auto
      have 1: "?vts2 = take (?j - ?i - 1) (drop (Suc ?i) ?vts)" by simp
      have 2: "?vts3 = drop (?j - ?i) (drop (Suc ?i) ?vts)"
        by (metis (no_types, lifting) One_nat_def Suc_1 diff_zero drop_butlast drop_drop plus_1_eq_Suc)
      have 3: "?a = ?vts ! ?i"
        by (smt (z3) Nil_is_append_conv pocket_path_set filled_0 hd_conv_nth is_polygon_split_path_def length_greater_0_conv list.distinct(1) nth_append nth_butlast pocket_0 set_empty split')
      have 4: "?b = ?vts ! ?j"
      proof-
        have "?b = ?filled_vts!1"
          unfolding construct_pocket_0_def fill_pocket_0_def
          by (smt (z3) Suc_eq_plus1 a_neq_b construct_pocket_0_def diff_Suc_1 diff_is_0_eq' drop_eq_Nil hd_conv_nth hd_drop_conv_nth hd_last_rotated last_conv_nth length_take linorder_not_less min.absorb4 nat_le_linear not_less_eq_eq nth_Cons' nth_take one_neq_zero take_all_iff take_eq_Nil)
        thus ?thesis by (metis is_polygon_split_path_def nth_butlast split')
      qed
      have 5: "?pocket_path = make_polygonal_path (?a # ?cutvts @ [?b])"
        by (smt (verit, ccfv_SIG) a_neq_b butlast.simps(2) butlast_tl hd_Cons_tl hd_Nil_eq_last last.simps snoc_eq_iff_butlast)
      have 6: "?p = make_polygonal_path (?vts @ [?vts!0])"
        by (metis (no_types, lifting) butlast_conv_take have_wraparound_vertex is_polygon_split_path_def nth_butlast polygon_filled_p split')
      have 7: "?p1 = make_polygonal_path (?a # ?vts2 @ [?b] @ rev ?cutvts @ [?a])" by blast
      have 8: "?p2 = make_polygonal_path (?vts1 @ ([?a] @ ?cutvts @ [?b]) @ ?vts3 @ [?vts!0])"
      proof-
        have "?rotated_vts = ?vts1 @ ([?a] @ ?cutvts @ [?b]) @ ?vts3 @ [?vts!0]"
          unfolding construct_pocket_0_def fill_pocket_0_def
          by (smt (verit) "3" Suc_1 hd_last_rotated a_neq_b append_Cons append_Nil append_butlast_last_id append_take_drop_id construct_pocket_0_def drop_Suc drop_drop drop_eq_Nil fill_pocket_0_def hd_Nil_eq_last hd_append2 hd_conv_nth last_conv_nth last_drop length_Cons length_take length_tl linorder_not_less list.collapse list.sel(3) list.size(3) min.absorb4 plus_1_eq_Suc take_all_iff)
        thus ?thesis by argo
      qed
      have 9: "?I1 = card {x. integral_vec x \<and> x \<in> path_inside ?p1}" by blast
      have 10: "?B1 = card {x. integral_vec x \<and> x \<in> path_image ?p1}" by blast
      have 11: "?I2 = card {x. integral_vec x \<and> x \<in> path_inside ?p2}" by blast
      have 12: "?B2 = card {x. integral_vec x \<and> x \<in> path_image ?p2}" by blast
      have 13: "?I = card {x. integral_vec x \<and> x \<in> path_inside ?p}" by blast
      have 14: "?B = card {x. integral_vec x \<and> x \<in> path_image ?p}" by blast
      have 15: "all_integral ?vts"
        using subset_filled less
        unfolding all_integral_def
        by (metis (no_types, lifting) all_integral_def all_integral_filled_vts in_set_butlastD)
      have 16: "measure lebesgue (path_inside ?p) = ?I + ?B/2 - 1"
        using ih_filled unfolding integral_inside integral_boundary by blast
      have 17: "measure lebesgue (path_inside ?p1) = ?I1 + ?B1/2 - 1"
        using ih_pocket unfolding integral_inside integral_boundary using pocket_rev_image pocket_rev_inside by force
      have "measure lebesgue (path_inside ?p2) = ?I2 + ?B2/2 - 1"
        using pick_split_path_union_main(3)
          [OF split' 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17] less(5-6) by blast
      moreover have "?I2 = I" using less(5) pr_image path_inside_def by presburger
      moreover have "?B2 = B" using less(6) pr_image path_image_def by presburger
      ultimately have ?case by (simp add: path_inside_def pocket_rev_inside pr_image)
    }
    ultimately have ?case by blast
  }
  ultimately show ?case using card_vts by linarith
qed

theorem pick:
  fixes p :: "R_to_R2"
  assumes "polygon p"
  assumes "p = make_polygonal_path vts"
  assumes "all_integral vts"
  assumes "I = card {x. integral_vec x \<and> x \<in> path_inside p}" 
  assumes "B = card {x. integral_vec x \<and> x \<in> path_image p}"
  shows "measure lebesgue (path_inside p) = I + B/2 - 1"
proof-
  obtain p' vts' where "polygon_of p' vts'
      \<and> vts'!0 \<in> frontier (convex hull (set vts'))
      \<and> path_image p' = path_image p
      \<and> all_integral vts'
      \<and> set vts' = set vts"
    using pick_rotate assms unfolding polygon_of_def by blast
  thus ?thesis using assms pick_unrotated unfolding path_inside_def polygon_of_def by fastforce
qed

end
