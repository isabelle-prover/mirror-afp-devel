theory Triangle_Lemmas
imports
  Polygon_Convex_Lemmas
  Integral_Matrix
  "Affine_Arithmetic.Floatarith_Expression"
  "HOL-Analysis.Topology_Euclidean_Space"
  "HOL-Analysis.Equivalence_Lebesgue_Henstock_Integration"
  "HOL-Analysis.Inner_Product"
  "HOL-Analysis.Line_Segment"
  "HOL-Analysis.Convex_Euclidean_Space"
  "HOL-Analysis.Change_Of_Vars"

begin

section "Triangles"

definition elem_triangle :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "elem_triangle a b c \<longleftrightarrow>
    \<not> collinear {a, b, c}
    \<and> integral_vec a \<and> integral_vec b \<and> integral_vec c
    \<and> {x. x \<in> convex hull {a, b, c} \<and> integral_vec x} = {a, b, c}"

definition triangle_mat :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2^2" where
  "triangle_mat a b c = transpose (vector [b - a, c - a])"

definition triangle_linear :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2 \<Rightarrow> real^2)" where
  "triangle_linear a b c = (\<lambda>x. (triangle_mat a b c) *v x)"

definition triangle_affine :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2 \<Rightarrow> real^2)" where
  "triangle_affine a b c = (\<lambda>x. a + (triangle_mat a b c) *v x)"

abbreviation "unit_square \<equiv>
  (convex hull {vector [0, 0], vector [0, 1], vector [1, 1], vector [1, 0]})::((real^2) set)"

abbreviation "unit_triangle \<equiv>
  (convex hull {vector [0, 0], vector [1, 0], vector [0, 1]})::((real^2) set)"

abbreviation "unit_triangle' \<equiv>
  (convex hull {vector [1, 1], vector [1, 0], vector [0, 1]})::((real^2) set)"

lemma triangle_inside_is_convex_hull_interior:
  assumes "polygon_of p [a, b, c, a]"
  shows "path_inside p = interior (convex hull {a, b, c})"
proof-
  have "path_image p = closed_segment a b \<union> closed_segment b c \<union> closed_segment c a"
  proof-
    have "path_image (linepath a b) = closed_segment a b" by simp
    moreover have "path_image (linepath b c) = closed_segment b c" by simp
    moreover have "path_image (linepath c a) = closed_segment c a" by simp
    moreover have "path_image p = path_image (linepath a b) \<union> path_image (linepath b c) \<union> path_image (linepath c a)"
      using calculation assms(1) unfolding polygon_of_def make_polygonal_path.simps
      by (simp add: path_image_join sup_assoc)
    ultimately show ?thesis by simp
  qed
  moreover have "DIM((real, 2) vec) = 2" by simp
  ultimately show ?thesis using inside_of_triangle[of a b c] unfolding path_inside_def by presburger
qed

lemma triangle_is_convex:
  assumes "p = make_triangle a b c" and "\<not> collinear {a, b, c}"
  shows "convex (path_inside p)" (is "convex ?s")
  using triangle_inside_is_convex_hull_interior assms(1) assms(2)
  using make_triangle_def polygon_of_def triangle_is_polygon
  by auto

lemma affine_comp_linear_trans: "triangle_affine a b c = (\<lambda>x. x + a) \<circ> (triangle_linear a b c)"
  apply (simp add: triangle_affine_def triangle_linear_def)
  by auto

lemma triangle_linear_der:
  fixes a b c :: "real^2"
  defines "T \<equiv> triangle_linear a b c"
  shows "(T has_derivative T) (at x)"
proof-
  have "linear T" using T_def by (simp add: triangle_linear_def)
  then have "bounded_linear T" by (simp add: linear_linear)
  thus ?thesis using bounded_linear_imp_has_derivative by blast
qed

lemma triangle_affine_der:
  fixes a b c :: "real^2"
  assumes "S \<in> sets lebesgue" and "x \<in> S"
  defines "A \<equiv> triangle_affine a b c" and "T \<equiv> triangle_linear a b c"
  shows "x \<in> S \<Longrightarrow> (A has_derivative T) (at x within S)"
proof-
  assume xin: "x \<in> S"
  let ?trans = "\<lambda>x::real^2. x + a"
  have comp: "(?trans \<circ> T) = (\<lambda>x. (T x) + a)"
    by auto
  have "\<forall>x. A x = (?trans \<circ> T) x" unfolding A_def T_def using affine_comp_linear_trans by auto
  moreover then have Ax_is: "(\<And>x. x \<in> S \<Longrightarrow> A x = ((\<lambda>x. x + a) \<circ> T) x)"
    by auto
  moreover have trans_der: "(?trans has_derivative id) (at x within S)"
    by (metis (full_types) add.commute assms(2) eq_id_iff has_derivative_transform shift_has_derivative_id)
  moreover have Tder: "(T has_derivative T) (at x within S)" using triangle_linear_der
    by (simp add: T_def bounded_linear_imp_has_derivative triangle_linear_def)
  moreover have comp_der: "((?trans \<circ> T) has_derivative T) (at x within S)"
    using  has_derivative_add_const[OF Tder] comp
    by simp
  ultimately show "(A has_derivative T) (at x within S)"
    using triangle_affine_def triangle_linear_def affine_comp_linear_trans o_apply add.commute vector_derivative_chain_within assms(2) has_derivative_add_const has_derivative_transform A_def T_def
    by force
qed

lemma triangle_linear_inj:
  fixes a b c :: "real^2"
  assumes "\<not> collinear {a, b, c}"
  defines "L \<equiv> triangle_linear a b c"
  shows "inj L"
proof-
  let ?M = "triangle_mat a b c"
  let ?m_11 = "(b - a)$1"
  let ?m_12 = "(c - a)$1"
  let ?m_21 = "(b - a)$2"
  let ?m_22 = "(c - a)$2"
  have "det ?M = ?m_11*?m_22 - ?m_12*?m_21"
    unfolding triangle_mat_def
    by (metis det_2 det_transpose mult.commute vector_2(1) vector_2(2))
  moreover have "?m_11*?m_22 \<noteq> ?m_12*?m_21"
  proof(rule ccontr)
    assume "\<not> ?m_11*?m_22 \<noteq> ?m_12*?m_21"
    then have eq: "?m_11*?m_22 = ?m_12*?m_21" by simp
    { assume *: "?m_21 = 0 \<and> ?m_22 \<noteq> 0"
      then have "?m_11 = 0" using eq by simp
      then have "?m_11 = 0 \<and> ?m_21 = 0" using * by auto
      then have "b - a = 0" by (metis (no_types, opaque_lifting) exhaust_2 vec_eq_iff zero_index)
      then have "collinear {a, b, c}" by simp
      then have False using assms by fastforce
    } moreover
    { assume *: "?m_21 \<noteq> 0 \<and> ?m_22 = 0"
      then have "?m_12 = 0" using eq by simp
      then have "?m_12 = 0 \<and> ?m_22 = 0" using * by auto
      then have "c - a = 0" by (metis (no_types, opaque_lifting) exhaust_2 vec_eq_iff zero_index)
      then have "collinear {a, b, c}" by (simp add: collinear_3_eq_affine_dependent)
      then have False using assms by fastforce
    } moreover 
    { assume *: "?m_21 = 0 \<and> ?m_22 = 0"
      { assume "?m_11 = 0"
        then have "b - a = 0" using *
          by (metis (no_types, opaque_lifting) exhaust_2 vec_eq_iff zero_index)
        then have False using assms(1) by auto
      } moreover
      { assume "?m_11 \<noteq> 0"
        then obtain k where "?m_12 = k * ?m_11" using nonzero_divide_eq_eq by blast
        moreover have "?m_22 = k * ?m_21" using * by auto
        ultimately have "c - a = k *\<^sub>R (b - a)"
          by (smt (verit, del_insts) exhaust_2 real_scaleR_def vec_eq_iff vector_scaleR_component)
        then have "collinear {a, b, c}"
          using vec_diff_scale_collinear[of c a k b] by (simp add: insert_commute)
        then have False using assms(1) by fastforce
      }
      ultimately have False using assms by fastforce
    } moreover
    { assume *: "?m_21 \<noteq> 0 \<and> ?m_22 \<noteq> 0"
      then have "?m_11/?m_21 = ?m_12/?m_22" using eq frac_eq_eq by blast
      then obtain m where "?m_11 = m*?m_12 \<and> ?m_21 = m*?m_22"
        using nonzero_divide_eq_eq *
        by (metis (no_types, lifting) mult.commute times_divide_eq_left)
      then have "b - a = m *s (c - a)" 
        by (smt (verit, del_insts) exhaust_2 vec_eq_iff vector_smult_component)
      then have "b - a = m *\<^sub>R (c - a)" by (simp add: scalar_mult_eq_scaleR)
      then have "collinear {a, b, c}" using vec_diff_scale_collinear by auto
      then have False using assms by auto
    }
    ultimately show False by fastforce
  qed
  ultimately have "det ?M \<noteq> 0" by linarith
  thus ?thesis by (simp add: L_def inj_matrix_vector_mult invertible_det_nz triangle_linear_def)
qed

lemma triangle_affine_inj:
  fixes a b c :: "real^2"
  assumes "\<not> collinear {a, b, c}"
  defines "A \<equiv> triangle_affine a b c"
  shows "inj A"
proof-
  have "inj (triangle_linear a b c)" using triangle_linear_inj[of a b c] assms by auto
  moreover have "inj (\<lambda>x. x + a)" by simp
  moreover have "A = (\<lambda>x. x + a) \<circ> (triangle_linear a b c)"
    by (simp add: A_def affine_comp_linear_trans)
  ultimately show ?thesis using inj_compose by blast
qed

lemma triangle_linear_integrable:
  fixes a b c :: "real^2"
  assumes "S \<in> lmeasurable"
  defines "T \<equiv> triangle_linear a b c"
  shows "(\<lambda>x. abs (det (matrix (T)))) integrable_on S" (is "(\<lambda>x. ?c) integrable_on S")
  using integrable_on_const[of S ?c] assms(1) by blast

lemma measure_differentiable_image_eq_affine:
  fixes a b c :: "real^2"
  defines "A \<equiv> triangle_affine a b c" and "T \<equiv> triangle_linear a b c"
  assumes "S \<in> lmeasurable" and "\<not> collinear {a, b, c}"
  shows "measure lebesgue (A ` S) = integral S (\<lambda>x. abs (det (matrix T)))"
proof-
  have "\<And>x. x \<in> S \<Longrightarrow> (A has_derivative T) (at x within S)"
    using triangle_affine_der A_def T_def assms(3) by blast
  moreover have "inj_on A S"
    using A_def assms(3) assms(4) triangle_affine_inj inj_on_subset by blast
  moreover have "(\<lambda>x. abs (det (matrix (T)))) integrable_on S"
    by (simp add: T_def assms(3) triangle_linear_integrable)
  ultimately show ?thesis
    using measure_differentiable_image_eq[of _ _ "\<lambda>x. T"] assms(3) by blast 
qed

lemma triangle_affine_img:
  fixes a b c :: "real^2"
  defines "A \<equiv> triangle_affine a b c"
  shows "convex hull {a, b, c} = A ` unit_triangle"
proof-
  let ?O = "(vector [0, 0])::real^2"
  let ?e1 = "(vector [1, 0])::real^2"
  let ?e2 = "(vector [0, 1])::real^2"

  let ?translate_a = "\<lambda>x. x + a"

  let ?T = "triangle_linear a b c"

  define al where "al = ?T ?O"
  define bl where "bl = ?T ?e1"
  define cl where "cl = ?T ?e2"

  have a: "a = ?translate_a al"
  proof-
    have "al = ?O"
      by (simp add: al_def mat_vec_mult_2 triangle_linear_def)
    then show ?thesis
      by (metis (no_types, opaque_lifting) add_0 mat_vec_mult_2 matrix_vector_mult_0 mult_zero_right zero_index)
  qed
  have b: "b = ?translate_a bl"
  proof-
    have col1: "column 1 (triangle_mat a b c) = b - a"
      by (metis column_transpose row_def triangle_mat_def vec_lambda_eta vector_2(1))
    then have "bl = b - a"
      using bl_def unfolding triangle_linear_def triangle_mat_def matrix_vector_mult_def
      using matrix_vector_mult_basis[of "triangle_mat a b c" 1]
      by (simp add: col1 axis_def bl_def mat_vec_mult_2 triangle_linear_def)
    then show ?thesis by simp
  qed
  have c: "c = ?translate_a cl"
  proof-
    have col2: "column 2 (triangle_mat a b c) = c - a"
      by (metis column_transpose row_def triangle_mat_def vec_lambda_eta vector_2(2))
    then have "cl = c - a"
      using cl_def unfolding triangle_linear_def triangle_mat_def matrix_vector_mult_def
      using matrix_vector_mult_basis[of "triangle_mat a b c" 2]
      by (simp add: col2 axis_def cl_def mat_vec_mult_2 triangle_linear_def)
    then show ?thesis by simp
  qed

  have "linear ?T" using triangle_linear_def by force
  then have "?T ` unit_triangle = convex hull {al, bl, cl}"
    using convex_hull_linear_image al_def bl_def cl_def by force
  also have "?translate_a ` ... = convex hull {a, b, c}"
    using a b c convex_hull_translation[of a "{al, bl, cl}"]
    by (metis (no_types, lifting) add.commute image_cong image_empty image_insert)
  finally have "?translate_a ` (?T ` unit_triangle) = convex hull {a, b, c}" .
  moreover have "?translate_a \<circ> ?T = A" unfolding A_def using affine_comp_linear_trans by auto
  ultimately show ?thesis by fastforce  
qed

lemma triangle_affine_e1_e2:
  fixes a b c :: "real^2"
  defines "A \<equiv> triangle_affine a b c"
  shows "(triangle_affine a b c) (vector [0, 0]) = a"
        "(triangle_affine a b c) (vector [1, 0]) = b"
        "(triangle_affine a b c) (vector [0, 1]) = c"
proof-
  let ?M = "triangle_mat a b c"
  let ?L = "triangle_linear a b c"
  let ?A = "triangle_affine a b c"
  let ?O = "(vector [0, 0])::(real^2)"
  let ?e1 = "(vector [1, 0])::(real^2)"
  let ?e2 = "(vector [0, 1])::(real^2)"

  show "?A ?O = a"
    unfolding triangle_affine_def triangle_mat_def
    by (metis (no_types, opaque_lifting) add.right_neutral diff_self mult_zero_right scaleR_left_diff_distrib transpose_matrix_vector vec_scaleR_2 vector_matrix_mult_0)
  show "?A ?e1 = b"
  proof-
    have "?L ?e1 = ?M *v ?e1" unfolding triangle_linear_def by blast
    also have "... = vector [1*(?M$1$1) + 0*(?M$1$2), 1*(?M$2$1) + 0*(?M$2$2)]"
      unfolding triangle_linear_def triangle_mat_def
      using mat_vec_mult_2 by force
    also have "... = vector [1*(b - a)$1 + 0*(?M$1$2), 1*(b - a)$2 + 0*(?M$2$2)]"
      unfolding triangle_mat_def transpose_def by simp
    also have "... = vector [(b - a)$1, (b - a)$2]" by argo
    also have "... = b - a"
      by (smt (verit) exhaust_2 vec_eq_iff vector_2(1) vector_2(2))
    finally show ?thesis unfolding triangle_affine_def triangle_linear_def by simp
  qed
  show "?A ?e2 = c"
  proof-
    have "?L ?e2 = ?M *v ?e2" unfolding triangle_linear_def by blast
    also have "... = vector [0*(?M$1$1) + 1*(?M$1$2), 0*(?M$2$1) + 1*(?M$2$2)]"
      unfolding triangle_linear_def triangle_mat_def
      using mat_vec_mult_2 by force
    also have "... = vector [0*(?M$1$1) + 1*(c - a)$1, 0*(?M$2$1) + 1*(c - a)$2]"
      unfolding triangle_mat_def transpose_def by simp
    also have "... = vector [(c - a)$1, (c - a)$2]" by argo
    also have "... = c - a"
      by (smt (verit) exhaust_2 vec_eq_iff vector_2(1) vector_2(2))
    finally show ?thesis unfolding triangle_affine_def triangle_linear_def by simp
  qed
qed

lemma triangle_measure_integral_of_det:
  fixes a b c :: "real^2"
  defines "S \<equiv> convex hull {a, b, c}"
  assumes "\<not> collinear {a, b, c}"
  shows "measure lebesgue S =
          integral unit_triangle (\<lambda>(x::real^2). abs (det (matrix (triangle_linear a b c))))"
proof-
  let ?A = "triangle_affine a b c"
  let ?T = "triangle_linear a b c"

  have "bounded unit_triangle" by (simp add: finite_imp_bounded_convex_hull)
  then have lmeasurable_S: "unit_triangle \<in> lmeasurable"
    using bounded_set_imp_lmeasurable measurable_convex by blast

  have "S = ?A ` unit_triangle" using S_def triangle_affine_img by blast
  then have "measure lebesgue S = measure lebesgue (?A ` unit_triangle)" by blast
  moreover have
    "measure lebesgue (?A ` unit_triangle)
      = integral unit_triangle (\<lambda>(x::real^2). abs (det (matrix ?T)))"
    using measure_differentiable_image_eq_affine[OF lmeasurable_S assms(2)] by auto
  ultimately show ?thesis by auto
qed

lemma triangle_affine_preserves_interior:
  assumes "A = triangle_affine a b c" and "L = triangle_linear a b c"
  assumes "\<not> collinear {a, b, c}"
  shows "A ` (interior S) = interior (A ` S)"
proof-
  let ?trans = "\<lambda>x::real^2. x + a"
  have "linear L" by (simp add: assms(2) triangle_linear_def)
  moreover have "surj L"
    using triangle_linear_inj[of a b c] linear_injective_imp_surjective[of L] assms calculation
    by blast
  ultimately have L: "interior(L ` S) = L ` (interior S)"
    using interior_surjective_linear_image by blast
  moreover have "interior(?trans ` S) = ?trans ` (interior S)"
    using interior_translation
    by (metis (no_types, lifting) add.commute image_cong)
  moreover have "A = ?trans \<circ> L" using assms triangle_affine_def triangle_linear_def by fastforce
  ultimately show ?thesis
    by (smt (verit, del_insts) add.commute image_comp image_cong interior_translation)
qed

lemma triangle_affine_preserves_affine_hull:
  assumes "A = triangle_affine a b c"
  assumes "\<not> collinear {a, b, c}"
  shows "A ` (affine hull S) =  affine hull (A ` S)"
proof-
  let ?L = "triangle_linear a b c"
  have "linear ?L" by (simp add: triangle_linear_def)
  then have "?L ` (affine hull S) = affine hull (?L ` S)"
    by (simp add: affine_hull_linear_image linear_linear)
  then show ?thesis
    unfolding assms(1) triangle_affine_def
    by (metis affine_hull_translation image_image triangle_linear_def)
qed

lemma triangle_measure_convex_hull_measure_path_inside_same:
  assumes p_triangle: "p = make_triangle a b c"
  assumes elem_triangle: "elem_triangle a b c" 
  shows "measure lebesgue (convex hull {a, b, c}) = measure lebesgue (path_inside p)" 
    (is "measure lebesgue ?S = measure lebesgue ?I")
proof-
  have "bounded ?S" by (simp add: finite_imp_bounded_convex_hull)
  then have "measure lebesgue (frontier ?S) = measure lebesgue ?S - measure lebesgue (interior ?S)"
    using measure_frontier[of ?S] by auto
  then have "... = 0"
    by (metis convex_convex_hull negligible_convex_frontier negligible_imp_measure0)
  moreover have "?I = interior ?S"
    using assms triangle_is_convex
    by (metis (no_types, lifting) make_triangle_def convex_polygon_inside_is_convex_hull_interior empty_set insert_absorb2 insert_commute list.simps(15) elem_triangle_def triangle_is_polygon)
  ultimately show ?thesis by auto
qed

lemma on_triangle_path_image_cases:
  assumes "p = make_triangle a b c"
  assumes "d \<in> path_image p"
  shows "d \<in> path_image (linepath a b) \<or> d \<in> path_image (linepath b c) \<or> d \<in> path_image (linepath c a)"
  using assms unfolding make_triangle_def
  by (metis make_polygonal_path.simps(3) make_polygonal_path.simps(4) not_in_path_image_join)

lemma on_triangle_frontier_cases:
  fixes a b c :: "real^2"
  assumes "\<not> collinear {a, b, c}"
  assumes "d \<in> frontier (convex hull {a, b, c})"
  shows "d \<in> path_image (linepath a b) \<or> d \<in> path_image (linepath b c) \<or> d \<in> path_image (linepath c a)"
proof-
  let ?p = "make_triangle a b c"
  have "polygon ?p" by (simp add: assms(1) triangle_is_polygon)
  then have "path_image ?p = frontier (convex hull {a, b, c})"
    unfolding make_triangle_def
    by (smt (verit, ccfv_threshold) assms(1) convex_polygon_frontier_is_path_image2 convex_polygon_is_convex_hull empty_set insert_absorb2 insert_commute list.simps(15) make_triangle_def polygon_convex_iff sup_commute triangle_is_convex)
  thus ?thesis using on_triangle_path_image_cases assms(2) by blast
qed

lemma triangle_path_image_subset_convex:
  assumes "p = make_triangle a b c"
  shows "path_image p \<subseteq> convex hull {a, b, c}"
  using polygon_path_image_subset_convex polygon_at_least_3_vertices make_triangle_def
  by (metis (no_types, lifting) assms empty_set insert_absorb2 insert_commute insert_iff length_pos_if_in_set list.simps(15))


lemma triangle_convex_hull:
 assumes "p = make_triangle a b c" and "\<not> collinear {a, b, c}"
 shows "convex hull {a, b, c} = (path_image p) \<union> (path_inside p)"
  using triangle_is_convex[OF assms(1) assms(2)] 
  by (smt (z3) Un_commute assms(1) assms(2) closure_Un_frontier convex_closure convex_polygon_is_convex_hull insert_absorb2 insert_commute inside_outside_def inside_outside_polygon list.set(1) list.set(2) make_triangle_def triangle_is_polygon)

end