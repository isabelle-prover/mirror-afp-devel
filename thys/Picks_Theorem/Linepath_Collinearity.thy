theory Linepath_Collinearity
  imports Polygon_Lemmas

begin

section "Collinearity Properties"

lemma points_on_linepath_collinear:
  assumes exists_c: "(\<exists>c. a - b = c *\<^sub>R u)"
  assumes x_in_linepath: "x \<in> path_image (linepath a b) "
  shows "(\<exists>c. x - a = c *\<^sub>R u)" "(\<exists>c. b - x = c *\<^sub>R u)"
proof - 
  obtain k :: real where k_prop: "0 \<le> k \<and> k \<le> 1 \<and> x = (1 - k) *\<^sub>R a + k *\<^sub>R b"
    using x_in_linepath unfolding linepath_def path_image_def by fastforce
  then have "x =  a - k *\<^sub>R a + k *\<^sub>R b"
    by (simp add: eq_diff_eq)
  then have "x - a=  - k *\<^sub>R a + k *\<^sub>R b"
    by auto
  then have xminusa: "x - a = -k*\<^sub>R(a - b)"
    by (simp add: scaleR_right_diff_distrib)
  obtain c where c_prop: " a - b = c *\<^sub>R u" using exists_c by blast
  show "(\<exists>c. x - a = c *\<^sub>R u)" using xminusa c_prop 
    by (metis scaleR_scaleR)
  then show "(\<exists>c. b - x = c *\<^sub>R u)"
    using exists_c 
    by (metis (no_types, opaque_lifting) add_diff_eq diff_add_cancel minus_diff_eq scaleR_left_distrib)
qed

lemma three_points_collinear_property:
  fixes a b:: "real^2"
  assumes exists_c1: "(\<exists>c. a - x1 = c *\<^sub>R u)"
  assumes exists_c2: "(\<exists>c. a - x2 = c *\<^sub>R u)"
  shows "\<exists>c. x1 - x2 = c*\<^sub>R u"
proof - 
  obtain c1 where c1_prop: "a - x1 = c1 *\<^sub>R u"
    using exists_c1 by auto
  obtain c2 where c2_prop: "a - x2 = c2 *\<^sub>R u"
    using exists_c2 by auto 
  then have "a - x2 - (a - x1) = c2 *\<^sub>R u - c1 *\<^sub>R u"
    using c1_prop c2_prop by simp
  then have "a - x2 - (a - x1) = (c2 - c1) *\<^sub>R u"
    by (simp add: scaleR_left_diff_distrib)
  then show ?thesis 
    by auto
qed

lemma in_path_image_imp_collinear:
  fixes a b:: "real^2"
  assumes "k \<in> path_image (linepath a b)"
  shows "collinear {a, b, k}"
proof - 
  obtain w where w_prop: "w \<in> {0..1} \<and> k = (1 - w) *\<^sub>R a + w *\<^sub>R b"
    using assms unfolding path_image_def linepath_def by fast
  have "collinear {0, a-b, (1 - w) *\<^sub>R a + (w-1) *\<^sub>R b}"
    using collinear 
    by (smt (verit) collinear_lemma diff_minus_eq_add scaleR_minus_left scaleR_right_diff_distrib)
  then have "collinear {0, a - b, k - b}"
    using w_prop 
    by (metis (no_types, lifting) add.commute add_diff_cancel_left collinear_lemma scaleR_collapse scaleR_right_diff_distrib)
  then show ?thesis using assms collinear_alt collinear_3[of a b k] 
    by auto
qed

lemma two_linepath_colinearity_property:
  fixes a b c d:: "real^2"
  assumes "y \<noteq> z \<and> {y, z} \<subseteq> (path_image (linepath a b)) \<inter> (path_image (linepath c d))"
  shows "collinear {a, b, c, d}"
proof - 
  have "collinear {a, b, y, z}"
    using in_path_image_imp_collinear assms 
    by (metis (no_types, lifting) Int_closed_segment collinear_4_3 inf.boundedE inf_idem insert_absorb2 insert_subset path_image_linepath pathstart_in_path_image pathstart_linepath)
  moreover have "collinear {c, d, y, z}"
    using in_path_image_imp_collinear assms 
    by (metis (no_types, lifting) Int_closed_segment collinear_4_3 inf.boundedE inf_idem insert_absorb2 insert_subset path_image_linepath pathstart_in_path_image pathstart_linepath)
  ultimately show ?thesis
    using assms collinear_3_eq_affine_dependent collinear_4_3 insert_absorb2 insert_commute
    by (smt (z3) collinear_3_trans)
qed

lemma polygon_vts_not_collinear:
  assumes "polygon_of p vts"
  shows "\<not> collinear (set vts)"
proof -
  have len_vts: "length vts \<ge> 3"
    using polygon_at_least_3_vertices assms unfolding polygon_of_def 
    using card_length dual_order.trans by blast
  have compact_and_connected: "compact (path_image p) \<and> connected (path_image p)"
    using inside_outside_polygon assms unfolding polygon_of_def
    using compact_simple_path_image connected_simple_path_image polygon_def
    by auto
  have nonempty_path_image: "path_image p \<noteq> {}"
    using assms unfolding polygon_of_def
    using vertices_on_path_image by simp
  have collinear_imp: "collinear (set vts) \<Longrightarrow> (collinear (path_image p))"
  proof - 
    assume "collinear (set vts)"
    then obtain u where u_prop: "\<forall>x\<in>set vts. \<forall>y\<in>set vts. \<exists>c. x - y = c *\<^sub>R u"
      unfolding collinear_def by blast
    then have "\<exists>c. x - y = c *\<^sub>R u" if xy_in_pathimage: "y\<in>path_image p \<and> x\<in>path_image p" for x y
    proof - 
      obtain k1 where k1_prop: "k1<length vts - 1 \<and> x \<in> path_image (linepath (vts ! k1) (vts ! (k1 + 1)))"
        using make_polygonal_path_image_property xy_in_pathimage len_vts 
        by (metis One_nat_def Suc_1 Suc_leD assms numeral_3_eq_3 polygon_of_def)
      then have "\<exists>c. (vts ! k1) - (vts ! (k1 + 1)) = c *\<^sub>R u"
        by (meson add_lessD1 in_set_conv_nth less_diff_conv u_prop)
      obtain k2 where k2_prop: "k2<length vts - 1 \<and> y \<in> path_image (linepath (vts ! k2) (vts ! (k2 + 1)))"
        using make_polygonal_path_image_property xy_in_pathimage len_vts 
        by (metis One_nat_def Suc_1 Suc_leD assms numeral_3_eq_3 polygon_of_def)
      have "\<exists>c. vts ! (k2 + 1) -  (vts ! k1) = c *\<^sub>R u"
        using u_prop k1_prop k2_prop 
        by (meson add_lessD1 less_diff_conv nth_mem)
      have k2_vts_prop: "\<exists>c. vts ! (k2 + 1) -  (vts ! k2) = c *\<^sub>R u"
        using u_prop k2_prop by fastforce
      have ex_c_k2: "\<exists>c. vts ! (k2 + 1) - y = c *\<^sub>R u"
        using points_on_linepath_collinear[of "vts ! (k2 + 1)" "vts ! k2" u y] k2_prop k2_vts_prop
        by (meson add_lessD1 points_on_linepath_collinear(2) less_diff_conv nth_mem u_prop)
      have k1_vts_prop: "\<exists>c. vts ! (k1 + 1) -  (vts ! k1) = c *\<^sub>R u"
        using u_prop k1_prop by fastforce
      have ex_c_k1_y: "\<exists>c. vts ! (k1 + 1) - y = c *\<^sub>R u"
        using points_on_linepath_collinear[of "vts ! (k1 + 1)" "vts ! k1" u y] k1_prop k1_vts_prop
        by (meson \<open>\<exists>c. vts ! (k2 + 1) - vts ! k1 = c *\<^sub>R u\<close> \<open>\<exists>c. vts ! k1 - vts ! (k1 + 1) = c *\<^sub>R u\<close> three_points_collinear_property ex_c_k2)
      have ex_c_k1_x: "\<exists>c. vts ! (k1 + 1) - x = c *\<^sub>R u"
        using points_on_linepath_collinear[of "vts ! (k1 + 1)" "vts ! k1" u x] k1_prop k1_vts_prop
        by (meson add_lessD1 points_on_linepath_collinear(2) less_diff_conv nth_mem u_prop)
      show ?thesis
        using ex_c_k1_y ex_c_k1_y three_points_collinear_property ex_c_k1_x by blast
    qed
    then show "(collinear (path_image p))" unfolding collinear_def by auto
  qed
  { assume *: "collinear (set vts)"
    then obtain a b::"real^2" where im_closed: "path_image p = closed_segment a b"
      using collinear_imp compact_convex_collinear_segment_alt[of "path_image p"] compact_and_connected nonempty_path_image
      by blast
    have "inside (closed_segment a b) = {}"
      by (simp add: inside_convex)
    then have "path_inside p = {}"
      unfolding path_inside_def using im_closed by auto
    then have "False"
      using inside_outside_polygon assms unfolding polygon_of_def inside_outside_def
      by blast
  }
  then show ?thesis by blast
qed

lemma not_collinear_with_subset:
  assumes "collinear A"
  assumes "\<not> collinear (A \<union> {x})"
  assumes "card A > 2"
  assumes "a \<in> A"
  shows "\<not> collinear ((A - {a}) \<union> {x})"
proof-
  obtain u v where uv: "u \<in> A \<and> v \<in> A \<and> u \<noteq> v \<and> u \<noteq> a \<and> v \<noteq> a"
  proof-
    have "card (A - {a}) \<ge> 2" using assms by auto
    then obtain u B where "u \<in> (A - {a}) \<and> B = (A - {a} - {u})" 
      by (metis bot_nat_0.extremum_unique card.empty ex_in_conv zero_neq_numeral)
    moreover then obtain v where "v \<in> B"
      by (metis Diff_iff One_nat_def Suc_1 assms(3) assms(4) card.empty card.insert equals0I finite.intros(1) finite_insert insert_Diff insert_commute less_irrefl)
    ultimately show ?thesis using that by blast
  qed
  then have "x \<notin> affine hull {u, v}"
    using assms
    by (smt (verit, ccfv_threshold) Un_commute Un_upper1 collinear_affine_hull_collinear hull_insert hull_mono insert_absorb insert_is_Un insert_subset)
  moreover have "u \<in> A - {a} \<and> v \<in> A - {a}" using uv by blast
  ultimately show ?thesis
    by (metis UnCI collinear_3_imp_in_affine_hull collinear_triples insert_absorb singletonD uv)
qed

lemma vec_diff_scale_collinear:
  fixes a b c :: "real^2"
  assumes "b - a = m *\<^sub>R (c - a)"
  shows "collinear {a, b, c}"
proof-
  { assume "m = 0"
    then have "b = a" using assms by simp
    then have "collinear {a, b, c}" by auto
  } moreover
  { assume m_nz: "m \<noteq> 0"
    then have c_eq: "c = (1/m) *\<^sub>R (b - a) + a" using assms by simp
    then have "c - b = (1/m - 1) *\<^sub>R (b - a)" using m_nz by (simp add: scaleR_left.diff)
    then obtain m' where "c - b = m' *\<^sub>R (b - a)" by fast

    (* show that "\<forall>v \<in> {a, b, c}. \<forall>w \<in> {a, b, c}. v - w \<in> span({b - a})" by exhaustion *)
    then have "c - b \<in> span({b - a})" by (simp add: span_breakdown_eq)
    moreover from this have "b - c \<in> span({b - a})" using span_0 span_add_eq2 by fastforce
    moreover have "c - a \<in> span({b - a})" using assms by (simp add: span_breakdown_eq c_eq)
    moreover from this have "a - c \<in> span({b - a})" using span_0 span_add_eq2 by fastforce
    moreover have "b - a \<in> span({b - a})" by (simp add: span_base)
    moreover from this have "a - b \<in> span({b - a})" using span_0 span_add_eq2 by fastforce
    moreover have "\<forall>v \<in> {a, b, c}. v - v \<in> span({b - a})" by (simp add: span_0)
    ultimately have "\<forall>v \<in> {a, b, c}. \<forall>w \<in> {a, b, c}. v - w \<in> span({b - a})" by blast
    then have "\<forall>v \<in> {a, b, c}. \<forall>w \<in> {a, b, c}. \<exists>k. v - w = k *\<^sub>R (b - a)"
      by (simp add: span_breakdown_eq)
    then have "collinear {a, b, c}" using collinear_def by blast
  }
  ultimately show ?thesis using assms by auto
qed

section "Linepath Properties"

lemma good_linepath_comm: "good_linepath a b vts \<Longrightarrow> good_linepath b a vts"
  unfolding good_linepath_def
  by (metis (no_types, opaque_lifting) insert_commute path_image_linepath segment_convex_hull)

lemma finite_set_linepaths:
  assumes polygon: "polygon p"
  assumes polygonal_path: "p = make_polygonal_path vts"
  shows "finite {(a, b). (a, b) \<in> set vts \<times> set vts}"
proof -
  have "finite (set vts)"
    using polygonal_path by auto
  then have "finite (set vts \<times> set vts)"
    by blast
  then show ?thesis
    by auto
qed

lemma linepaths_intersect_once_or_collinear:
  fixes a b c d :: "real^2"
  assumes "path_image (linepath a b) \<inter> path_image (linepath c d) \<noteq> {}"
  shows "collinear {a, b, c, d} \<or> (\<exists>x. path_image (linepath a b) \<inter> path_image (linepath c d) = {x})"
proof safe
  assume "\<not> (\<exists>x. path_image (linepath a b) \<inter> path_image (linepath c d) = {x})"
  then obtain x y where "x \<noteq> y \<and> {x, y} \<subseteq> path_image (linepath a b) \<inter> path_image (linepath c d)"
    using assms by blast
  then show "collinear {a, b, c, d}" using two_linepath_colinearity_property by meson
qed

lemma linepaths_intersect_once_or_collinear_alt:
  fixes a b c d :: "real^2"
  assumes "path_image (linepath a b) \<inter> path_image (linepath c d) \<noteq> {}"
  shows "collinear {a, b, c, d} \<or> card (path_image (linepath a b) \<inter> path_image (linepath c d)) = 1"
proof-
  have "card (path_image (linepath a b) \<inter> path_image (linepath c d)) = 1
      \<longleftrightarrow> (\<exists>x. path_image (linepath a b) \<inter> path_image (linepath c d) = {x})"
    using is_singleton_altdef is_singleton_def by blast
  thus ?thesis using linepaths_intersect_once_or_collinear assms by presburger
qed

lemma path_image_linepath_union:
  fixes a b :: "'a::euclidean_space"
  assumes "d \<in> path_image (linepath a b)"
  shows "path_image (linepath a b) = path_image (linepath a d) \<union> path_image (linepath d b)"
proof- 
  have "path_image (linepath a b) = closed_segment a b" using path_image_linepath by simp
  also then have "... = closed_segment a d \<union> closed_segment d b"
    using Un_closed_segment assms by blast
  also have "... = path_image (linepath a d) \<union> path_image (linepath d b)"
    using path_image_linepath by simp
  ultimately show ?thesis by order
qed

lemma path_image_linepath_split:
  assumes "i < (length vts) - 1"
  assumes "x \<in> path_image (linepath (vts!i) (vts!(i+1)))"
  assumes x_notin: "x \<notin> set vts"
  shows "path_image (make_polygonal_path vts) = path_image (make_polygonal_path ((take (i+1) vts) @ [x] @ (drop (i+1) vts)))"
  using assms
proof(induct "length vts" arbitrary: vts i x)
  case 0
  then show ?case by linarith
next
  case (Suc n)
  let ?vts' = "(take (i+1) vts) @ [x] @ (drop (i+1) vts)"
  let ?p = "make_polygonal_path vts"
  let ?p' = "make_polygonal_path ?vts'"
  have "Suc n \<ge> 2" using Suc by linarith
  then obtain v1 v2 vts_tail where vts_is: "vts = v1#v2#vts_tail"
    by (metis Suc(2) Cons_nth_drop_Suc One_nat_def Suc_1 Suc_le_eq drop0 zero_less_Suc) 
  { assume *: "i = 0"
    then have vts'_is: "?vts' = [v1, x, v2] @ vts_tail"
      using vts_is  by simp
    then have x_in: "x \<in> path_image (linepath v1 v2)"
      using * Suc.prems vts_is by simp
    { assume *: "vts_tail = []"
      then have p_is: "path_image ?p = path_image (linepath v1 v2)"
        using vts_is  make_polygonal_path.simps(3)[of v1 v2]
        by simp
      have "path_image ?p' = path_image (linepath v1 x) \<union> path_image (linepath x v2)"
        using vts'_is * make_polygonal_path.simps(4)[of v1 x v2 "[]"]
        using make_polygonal_path.simps(3)[of x v2]
        by (metis append.right_neutral list.discI nth_Cons_0 path_image_cons_union)
      then have ?case
        using p_is path_image_linepath_union[of x v1 v2] assms(3) vts_is x_in by blast
    } moreover
    { assume *: "vts_tail \<noteq> []"
      then have "path_image ?p = path_image (linepath v1 v2) \<union> path_image (make_polygonal_path (v2#vts_tail))"
        using path_image_cons_union vts_is by (metis list.discI nth_Cons_0)
      moreover have "path_image (linepath v1 x) \<union> path_image (linepath x v2) = path_image (linepath v1 v2)"
        using path_image_linepath_union x_in by blast
      ultimately have ?case
        by (metis (no_types, lifting) append_Cons append_Nil inf_sup_aci(6) list.discI nth_Cons_0 path_image_cons_union vts'_is)
    }                                                                      
    ultimately have ?case by blast
  } moreover
  { assume * :"i > 0"
    then have "Suc n > 2" using Suc by linarith

    let ?vts_tl = "tl vts"
    let ?vts_tl' = "(take i ?vts_tl) @ [x] @ (drop i ?vts_tl)"
    let ?p_tl = "make_polygonal_path ?vts_tl"
    let ?p_tl' = "make_polygonal_path ?vts_tl'"

    have "?vts_tl!(i-1) = vts!i \<and> ?vts_tl!i = vts!(i+1)" using Suc * by (simp add: vts_is)
    moreover then have "x \<in> path_image (linepath (?vts_tl!(i-1)) (?vts_tl!i))"
      using Suc by presburger
    ultimately have "path_image ?p_tl = path_image ?p_tl'"
      using Suc
      by (smt (verit) "*" One_nat_def Suc_leI diff_Suc_1 le_add_diff_inverse2 length_tl less_diff_conv list.sel(3) list.set_intros(2) vts_is)
    moreover have "path_image ?p = path_image (linepath v1 v2) \<union> path_image ?p_tl"
      using path_image_cons_union vts_is by auto
    ultimately have ?case
      by (smt (verit, ccfv_threshold) Nil_is_append_conv Suc_eq_plus1 \<open>i = 0 \<Longrightarrow> path_image (make_polygonal_path vts) = path_image (make_polygonal_path (take (i + 1) vts @ [x] @ drop (i + 1) vts))\<close> append_Cons append_same_eq append_take_drop_id drop_Suc hd_append2 hd_conv_nth list.sel(1) list.sel(3) path_image_cons_union take_eq_Nil vts_is)
  }
  ultimately show ?case by linarith
qed

lemma linepath_split_is_loop_free:
  assumes "d \<in> path_image (linepath a b)"
  assumes "d \<notin> {a, b}"
  shows "loop_free (make_polygonal_path [a, d, b])" (is "loop_free ?p")
proof-
  let ?l1 = "linepath a d"
  let ?l2 = "linepath d b"
  have "path_image ?l1 \<inter> path_image ?l2 = {d}" using Int_closed_segment assms(1) by auto
  moreover have "arc ?l1 \<and> arc ?l2" using assms(2) by fastforce
  ultimately show ?thesis
    by (metis arc_imp_simple_path arc_join_eq_alt make_polygonal_path.simps(3) make_polygonal_path.simps(4) pathfinish_linepath pathstart_linepath simple_path_def)
qed

lemma loop_free_linepath_split_is_loop_free:
  assumes "p = make_polygonal_path vts"
  assumes "loop_free p"
  assumes "n = length vts"
  assumes "i < n - 1"
  assumes "x \<in> path_image (linepath (vts!i) (vts!(i+1))) \<and> x \<notin> set vts"
  assumes "vts' = (take (i+1) vts) @ [x] @ (drop (i+1) vts)"
  assumes "p' = make_polygonal_path vts'"
  shows "loop_free p' \<and> path_image p' = path_image p"
  using assms
proof(induct i arbitrary: p vts p' vts' n)
  case 0
  let ?vts_tl = "tl vts"
  let ?p_tl = "make_polygonal_path ?vts_tl"
  let ?vts'_tl = "tl vts'"
  let ?p'_tl = "make_polygonal_path ?vts'_tl"
  let ?a = "vts!0"
  let ?b = "vts!1"
  let ?l = "linepath ?a ?b"
  let ?l' = "make_polygonal_path [?a, x, ?b]"

  have vts': "vts' = [?a, x] @ ?vts_tl"
    using 0
    by (metis (no_types, lifting) Suc_eq_plus1 append_Cons append_eq_append_conv2 append_self_conv bot_nat_0.not_eq_extremum diff_is_0_eq drop0 drop_Suc list.collapse nth_Cons_0 take_Suc take_all_iff take_eq_Nil)

  have "x \<notin> {?a, ?b}"
    by (metis 0(3-5) One_nat_def Suc_eq_plus1 bot_nat_0.not_eq_extremum diff_is_0_eq insert_iff less_diff_conv nth_mem singletonD take_Suc_eq take_all_iff)
  then have lf_l': "loop_free ?l'" using linepath_split_is_loop_free[of x ?a ?b] 0 by simp

  { assume "length ?vts_tl = 1"
    then have "vts' = [?a, x, ?b]"
      by (metis Cons_nth_drop_Suc One_nat_def append_eq_Cons_conv drop0 drop_eq_Nil le_numeral_extra(4) nth_tl vts' zero_less_one)
    then have ?case using linepath_split_is_loop_free path_image_linepath_split
      by (metis "0.prems"(1) "0.prems"(3) "0.prems"(4) "0.prems"(5) "0.prems"(6) "0.prems"(7) lf_l')
  } moreover
  { assume *: "length ?vts_tl \<ge> 2"
    then have p: "p = ?l +++ ?p_tl"
      using make_polygonal_path.simps(4)[of ?a ?b]
      by (metis (no_types, opaque_lifting) "0"(1) "0"(3) "0"(4) Cons_nth_drop_Suc One_nat_def Suc_1 Suc_le_eq diff_is_0_eq drop_0 drop_Suc length_tl less_nat_zero_code nat_le_linear nth_tl)

    have "loop_free ?p_tl"
      using tail_of_loop_free_polygonal_path_is_loop_free 0 *
      by (metis list.exhaust_sel list.sel(2))
    moreover have l_l': "path_image ?l = path_image ?l'"
      using path_image_linepath_split 0
      by (metis One_nat_def Suc_eq_plus1 list.discI make_polygonal_path.simps(3) nth_Cons_0 path_image_cons_union path_image_linepath_union)
    moreover have "path_image ?l' \<inter> path_image ?p_tl \<subseteq> {?a, ?b}"
      by (metis (mono_tags, opaque_lifting) p l_l' "0.prems"(1) "0.prems"(2) make_polygonal_path_gives_path path_join_path_ends pathfinish_linepath pathstart_linepath simple_path_def simple_path_joinE)
    moreover have "arc p \<longrightarrow> path_image ?l' \<inter> path_image ?p_tl \<subseteq> {?b}"
      using p l_l'
      by (metis arc_def arc_join_eq make_polygonal_path_gives_path path_join_eq path_linepath pathfinish_linepath)
    moreover have "arc p \<longleftrightarrow> hd [?a, x, ?b] \<noteq> last (tl vts)"
      by (metis "*" "0.prems"(1) "0.prems"(2) arc_def arc_simple_path last_conv_nth last_tl list.sel(1) list.sel(2) list.size(3) loop_free_cases make_polygonal_path_gives_path not_numeral_le_zero polygon_pathfinish polygon_pathstart)
    moreover have "vts' = [?a, x, ?b] @ tl ?vts_tl"
      by (metis drop_Suc "0.prems"(3) "0.prems"(4) One_nat_def append_Cons append_Nil append_take_drop_id length_tl nth_tl take_Suc_conv_app_nth take_eq_Nil vts')
    moreover have "last [?a, x, ?b] = hd ?vts_tl"
      by (metis "0.prems"(3) "0.prems"(4) One_nat_def hd_conv_nth last.simps length_greater_0_conv length_tl list.discI nth_tl)
    moreover have "pathfinish ?l = pathstart ?p_tl"
      by (metis (no_types) "0.prems"(1) make_polygonal_path.simps(3) make_polygonal_path_gives_path p path_join_eq)
    moreover have "\<And>v va vb vs. pathfinish (linepath v va) = pathstart (make_polygonal_path (va # vb # vs))"
        (* generated by sledgehammer *)
      by (metis (no_types) make_polygonal_path.simps(3) make_polygonal_path.simps(4) make_polygonal_path_gives_path path_join_eq)
    ultimately have "loop_free p'"
      using loop_free_append[of p' vts' ?l' "[?a, x, ?b]" ?p_tl ?vts_tl]
      by (metis (no_types) "0.prems"(1) "0.prems"(2) "0.prems"(7) arc_simple_path lf_l' make_polygonal_path.simps(3) make_polygonal_path.simps(4) make_polygonal_path_gives_path p pathfinish_join pathstart_linepath simple_path_def simple_path_joinE)
    then have ?case
      using "0"(1) "0"(3) "0"(4) "0"(5) "0"(6) "0"(7) path_image_linepath_split by blast
  }
  ultimately show ?case
    by (metis 0(3,4) One_nat_def Suc_lessI length_tl less_eq_Suc_le nat_1_add_1 plus_1_eq_Suc)
next
  case (Suc i)
  let ?vts_tl = "tl vts"
  let ?p_tl = "make_polygonal_path ?vts_tl"
  let ?vts'_tl = "tl vts'"
  let ?p'_tl = "make_polygonal_path ?vts'_tl"
  let ?a = "vts!0"
  let ?b = "vts!1"
  let ?l = "linepath ?a ?b"

  have "?vts_tl!i = vts!(Suc i) \<and> ?vts_tl!(i+1) = vts!((Suc i) + 1)"
    by (metis Suc.prems(3) Suc.prems(4) add_Suc_right add_Suc_shift diff_is_0_eq linorder_not_le list.exhaust_sel list.size(3) not_less_zero nth_Cons_Suc)
  moreover have "set ?vts_tl \<subseteq> set vts"
    by (metis list.sel(2) list.set_sel(2) subsetI)
  ultimately have "x \<in> path_image (linepath (?vts_tl!i) (?vts_tl!(i+1))) \<and> x \<notin> set ?vts_tl"
    using Suc.prems(5) by auto
  moreover have vts'_tl: "?vts'_tl = (take (i+1) ?vts_tl) @ [x] @ (drop (i+1) ?vts_tl)"
    by (metis Suc.prems(3) Suc.prems(4) Suc.prems(6) Suc_eq_plus1 drop_Suc leD length_tl take_all_iff take_eq_Nil take_tl tl_append2 zero_eq_add_iff_both_eq_0 zero_neq_one)
  moreover have "loop_free ?p_tl"
    using tail_of_loop_free_polygonal_path_is_loop_free Suc.prems
    by (metis Nitpick.size_list_simp(2) Suc_1 Suc_leI Suc_neq_Zero diff_0_eq_0 diff_Suc_1 less_one linorder_neqE_nat list.collapse not_less_zero)
  ultimately have ih: "loop_free ?p'_tl \<and> path_image ?p'_tl = path_image ?p_tl"
    using Suc.prems Suc.hyps[of ?p_tl ?vts_tl _ ?vts'_tl ?p'_tl] by simp

  have p: "p = ?l +++ ?p_tl"
  proof -
    have f1: "\<forall>vs. (hd (tl vs)::(real, 2) vec) = vs ! 1 \<or> [] = vs \<or> [] = tl vs"
      by (metis (no_types) One_nat_def hd_conv_nth list.collapse nth_Cons_Suc)
    have "[] \<noteq> tl vts \<and> vts \<noteq> [] \<and> tl vts \<noteq> [hd (tl vts)]"
      by (metis Suc.prems(1) Suc.prems(2) \<open>loop_free (make_polygonal_path (tl vts))\<close> constant_linepath_is_not_loop_free make_polygonal_path.simps(1) make_polygonal_path.simps(2))
    then have "p = make_polygonal_path [hd vts, vts ! 1] +++ make_polygonal_path (tl vts) \<and> vts \<noteq> []"
      using f1 by (metis (full_types) Suc.prems(1) list.collapse make_polygonal_path.simps(3) make_polygonal_path.simps(4))
    then show ?thesis
      by (simp add: hd_conv_nth)
  qed

  have "length vts' \<ge> 3" using Suc.prems by force
  moreover have ab: "?a = vts'!0 \<and> ?b = vts'!1"
    using Suc.prems
    by (smt (verit, ccfv_SIG) One_nat_def Suc_eq_plus1 add_Suc_right append_Cons drop0 drop_Suc length_tl less_nat_zero_code list.exhaust_sel list.size(3) nat_diff_split nth_Cons_0 nth_Cons_Suc take_Suc zero_less_Suc)
  ultimately have p': "p' = ?l +++ ?p'_tl"
    using Suc.prems(7) make_polygonal_path.simps(4)[of ?a ?b]
    by (metis (no_types, opaque_lifting) Cons_nth_drop_Suc One_nat_def Suc_leD Suc_le_eq drop0 drop_Suc numeral_3_eq_3)

  have nonarc: "path_image ?l \<inter> path_image ?p_tl \<subseteq> {?a, ?b}"
    using simple_path_join_loop_eq Suc.prems
    by (smt (verit, ccfv_threshold) p One_nat_def length_tl less_zeroE make_polygonal_path_gives_path nth_tl order.strict_iff_not order_le_less_trans path_join_eq path_linepath pathfinish_linepath pathstart_linepath polygon_pathstart simple_path_def simple_path_joinE take_Nil take_all_iff)
  have arc: "arc p \<longrightarrow> path_image ?l \<inter> path_image ?p_tl \<subseteq> {?b}"
    using arc_join_eq
    by (metis Suc.prems(1) p make_polygonal_path_gives_path path_join_eq path_linepath pathfinish_linepath)

  { assume "arc p"
    moreover then have "path_image ?l \<inter> path_image ?p'_tl \<subseteq> {?b}" using arc ih by presburger
    moreover have "pathfinish ?l = pathstart ?p'_tl"
      by (metis Suc.prems(7) make_polygonal_path_gives_path p' path_join_path_ends)
    ultimately have ?case using p' arc_join_eq[of ?l ?p'_tl]
      by (smt (verit, ccfv_SIG) Nil_is_append_conv Suc.prems(3) Suc.prems(4) Suc_eq_plus1 vts'_tl arc_simple_path drop_eq_Nil ih last_appendR last_conv_nth last_drop leD length_tl make_polygonal_path_gives_path p path_image_join path_join_eq path_linepath pathfinish_linepath polygon_pathfinish simple_path_def simple_path_joinE take_all_iff take_eq_Nil)
  } moreover
  { assume "\<not> arc p"
    then have "pathstart ?l = pathfinish ?p'_tl \<and> pathfinish ?l = pathstart ?p'_tl"
      by (smt (verit, del_insts) Nil_is_append_conv Nil_tl One_nat_def Suc.prems(2) Suc.prems(3) Suc.prems(4) Suc_eq_plus1 vts'_tl ab arc_def drop_eq_Nil last_appendR last_conv_nth last_drop leD length_tl list.collapse loop_free_cases make_polygonal_path_gives_path nth_Cons_Suc p path_join_eq path_linepath pathfinish_join pathfinish_linepath pathstart_join polygon_pathfinish polygon_pathstart take_all_iff take_eq_Nil)
    then have ?case using simple_path_join_loop_eq[of ?l ?p'_tl] p' nonarc
      by (smt (verit, ccfv_threshold) One_nat_def Suc.prems(2) Suc.prems(3) Suc.prems(4) arc_def constant_linepath_is_not_loop_free dual_order.strict_trans ih leD length_tl loop_free_cases make_polygonal_path_gives_path not_loop_free_first_component nth_tl p path_image_join path_linepath pathfinish_linepath pathstart_linepath polygon_pathstart simple_path_def simple_path_join_loop_eq take_all_iff take_eq_Nil zero_less_Suc)
  }
  ultimately show ?case by argo
qed


lemma polygon_linepath_split_is_polygon:
  assumes "polygon_of p vts"
  assumes "i < (length vts) - 1"
  assumes "a = vts!i \<and> b = vts!(i+1)"
  assumes "x \<in> path_image (linepath a b) \<and> x \<notin> set vts"
  assumes "vts' = (take (i+1) vts) @ [x] @ (drop (i+1) vts)"
  shows "polygon (make_polygonal_path vts')"
proof-
  let ?p' = "make_polygonal_path vts'"
  have "path ?p'" using assms make_polygonal_path_gives_path by presburger
  moreover have "loop_free ?p'" using assms loop_free_linepath_split_is_loop_free
    by (metis polygon_def polygon_of_def simple_path_def)
  moreover have "closed_path ?p'"
  proof-
    have "hd vts' = hd vts"
      using assms
      by (metis hd_append2 hd_take le_diff_conv linorder_not_less take_all_iff take_eq_Nil2 trans_less_add2 zero_less_one)
    moreover have "last vts' = last vts"
      using assms linordered_semidom_class.add_diff_inverse by auto
    ultimately show ?thesis
      by (metis closed_path_def \<open>path ?p'\<close> append_butlast_last_id append_eq_conv_conj append_is_Nil_conv assms(1) assms(5) have_wraparound_vertex hd_conv_nth length_butlast not_Cons_self nth_append_length polygon_of_def polygon_pathfinish polygon_pathstart)
  qed
  ultimately show ?thesis unfolding polygon_def polygonal_path_def simple_path_def assms(5) by blast
qed

section "Measure of linepaths"

lemma linepath_is_negligible_vertical:
  fixes a b :: "real^2"
  assumes "a$1 = b$1"
  defines "p \<equiv> linepath a b"
  shows "negligible (path_image p)"
proof-
  have p_t: "\<forall>t \<in> {0..1}. (p t)$1 = a$1"
    using linepath_in_path p_def segment_vertical assms by blast

  let ?x = "a$1"
  let ?e1 = "(vector [1, 0])::real^2"

  have "(1::real) \<in> Basis" by simp
  then have "axis 1 (1::real) \<in> (\<Union>i. \<Union>u\<in>(Basis::(real set)). {axis i u})" by blast
  moreover have "?e1 = axis 1 (1::real)"
    unfolding axis_def vector_def by auto
  ultimately have e1_basis: "?e1 \<in> (Basis::((real^2) set))" by simp
  then have "negligible {v. v \<bullet> ?e1 = ?x}" (is "negligible ?S")
    using negligible_standard_hyperplane by auto
  moreover have "\<forall>t \<in> {0..1}. (p t) \<bullet> ?e1 = ?x"
  proof clarify
    fix t :: "real"
    assume t: "t \<in> {0..1}"
    have "(p t) \<bullet> ?e1 = (p t)$1"
      by (smt (verit, best) e1_basis cart_eq_inner_axis vec_nth_Basis vector_2(1))
    also have "... = ?x" using p_t t by blast
    finally show "(p t) \<bullet> ?e1 = ?x" .
  qed
  moreover from this have "path_image p \<subseteq> ?S" unfolding path_image_def by blast
  ultimately show ?thesis using negligible_subset by blast
qed

lemma linepath_is_negligible_non_vertical:
  fixes a b :: "real^2"
  assumes "a$1 < b$1"
  defines "p \<equiv> linepath a b"
  shows "negligible (path_image p)"
proof-
  let ?A = "(vector [vector [1, b$1 - a$1], vector [0, b$2 - a$2]])::(real^2^2)"
  let ?f1 = "\<lambda>v::real^2. (?A *v v)"
  let ?id = "\<lambda>v::real^2. v"
  let ?f_a = "\<lambda>v::real^2. a"
  let ?f2 = "\<lambda>v. ?id v + ?f_a v"
  let ?f = "?f2 \<circ> ?f1"

  let ?O = "(vector [0, 0])::real^2"
  let ?e2 = "(vector [0, 1])::real^2"
  let ?y_unit_seg_path = "linepath ?O ?e2"
  let ?y_unit_seg = "path_image ?y_unit_seg_path"

  have "\<forall>t \<in> {0..1}. ?f (?y_unit_seg_path t) = p t"
  proof clarify
    fix t :: real
    assume t: "t \<in> {0..1}"
    then obtain v where v: "?y_unit_seg_path t = v" by auto
    then have "v = (1 - t) *\<^sub>R ?O + t *\<^sub>R ?e2" unfolding linepath_def by auto
    then have "v = t *\<^sub>R ?e2"
      by (smt (verit, best) t v exhaust_2 linepath_0 scaleR_zero_left vec_eq_iff vector_2(1) vector_2(2) vector_scaleR_component)
    then have "?f v = p t"
    proof-
      assume "v = t *\<^sub>R vector [0, 1]"
      then have "v = vector [t * 0, t * 1]"
        by (smt (verit, del_insts) exhaust_2 mult_cancel_left1 real_scaleR_def scaleR_zero_right vec_eq_iff vector_2(1) vector_2(2) vector_scaleR_component)
      then have v: "v = vector [0, t]" by auto
      
      have f1: "?f1 v = vector [t * (b$1 - a$1), t * (b$2 - a$2)]" (is "?f1 v = ?f1_v")
        by (simp add: mat_vec_mult_2 v)
      
      have "?f2 ?f1_v = vector [t * (b$1 - a$1), t * (b$2 - a$2)] + vector [a$1, a$2]"
        by (smt (verit) exhaust_2 vec_eq_iff vector_2(1) vector_2(2))
      also have "... = vector [t * (b$1 - a$1) + a$1, t * (b$2 - a$2) + a$2]"
        by (smt (verit, del_insts) vector_add_component exhaust_2 vec_eq_iff vector_2(1) vector_2(2))
      also have "... = vector [t * b$1 + (1 - t) * a$1, t * b$2 + (1 - t) * a$2]" by argo
      also have "... = t *\<^sub>R b + (1 - t) *\<^sub>R a"
        by (smt (verit, del_insts) exhaust_2 real_scaleR_def vec_eq_iff vector_2(1) vector_2(2) vector_add_component vector_scaleR_component)
      finally have "?f2 ?f1_v = t *\<^sub>R b + (1 - t) *\<^sub>R a" .
      thus ?thesis using p_def f1 unfolding linepath_def by simp
    qed
    thus "?f (?y_unit_seg_path t) = p t" using v by simp
  qed

  then have "?f ` ?y_unit_seg = path_image p" unfolding path_image_def by force
  moreover have "?f differentiable_on ?y_unit_seg"
  proof-
    have "linear ?f1" by auto
    then have "?f1 differentiable_on ?y_unit_seg"
      using linear_imp_differentiable by (simp add: linear_imp_differentiable_on)
    moreover have "?f2 differentiable_on (?f1 ` ?y_unit_seg)"
    proof-
      have "?id differentiable_on ?f1 ` ?y_unit_seg"
        using differentiable_const by simp
      moreover have "?f_a differentiable_on ?f1 ` ?y_unit_seg"
        using differentiable_ident by simp
      ultimately show "?f2 differentiable_on ?f1 ` ?y_unit_seg"
        using differentiable_compose by simp
    qed
    ultimately show ?thesis using differentiable_compose
      by (simp add: differentiable_chain_within differentiable_on_def)
  qed
  moreover have "negligible ?y_unit_seg"
    using linepath_is_negligible_vertical[of ?O ?e2] by simp
  ultimately show ?thesis
    using negligible_differentiable_image_negligible by fastforce
qed

lemma linepath_is_negligible:
  fixes a b :: "real^2"
  defines "p \<equiv> linepath a b"
  shows "negligible (path_image p)"
proof-
  { assume "a$1 = b$1"
    then have ?thesis using linepath_is_negligible_vertical p_def by blast
  } moreover
  { assume "a$1 < b$1"
    then have ?thesis using linepath_is_negligible_non_vertical p_def by blast
  } moreover
  { assume a: "a$1 > b$1"
    let ?p_rev = "reversepath p"
    have "path_image p = path_image ?p_rev" by simp
    moreover have "?p_rev = linepath b a" using p_def by simp
    ultimately have ?thesis using a linepath_is_negligible_non_vertical[of b a] by simp
  }
  ultimately show ?thesis by linarith
qed

lemma linepath_has_emeasure_0:
  "emeasure lebesgue (path_image (linepath (a::(real^2)) (b::(real^2)))) = 0"
  using linepath_is_negligible emeasure_notin_sets negligible_iff_emeasure0 by blast

lemma linepath_has_measure_0:
  "measure lebesgue (path_image (linepath (a::(real^2)) (b::(real^2)))) = 0"
  using linepath_has_emeasure_0 linepath_is_negligible negligible_imp_measure0 by blast

end 