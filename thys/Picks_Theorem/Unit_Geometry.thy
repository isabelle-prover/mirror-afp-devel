theory Unit_Geometry
imports
  "HOL-Analysis.Polytope"
  Polygon_Jordan_Curve
  Triangle_Lemmas

begin

section "Measure Setup"

lemma finite_convex_is_measurable:
  fixes p :: "(real^2) set"
  assumes "p = convex hull l" and "finite l"
  shows "p \<in> sets lebesgue"
proof-
  have "polytope p"
    unfolding polytope_def using assms by force
  hence "compact p" using polytope_imp_compact by auto
  thus ?thesis using lmeasurable_compact by blast
qed

lemma unit_square_lebesgue: "unit_square \<in> sets lebesgue"
  using finite_convex_is_measurable by auto

lemma unit_triangle_lebesgue: "unit_triangle \<in> sets lebesgue"
  using finite_convex_is_measurable by auto

lemma unit_triangle_lmeasurable: "unit_triangle \<in> lmeasurable"
  by (simp add: bounded_convex_hull bounded_set_imp_lmeasurable unit_triangle_lebesgue)

section "Unit Triangle"

lemma unit_triangle_vts_not_collinear:
  "\<not> collinear {(vector [0, 0])::real^2, vector [1, 0], vector [0, 1]}"
  (is "\<not> collinear {?a, ?b, ?c}")
proof(rule ccontr)
  assume "\<not> \<not> collinear {?a, ?b, ?c}"
  then have "collinear {?a, ?b, ?c}" by auto
  then obtain u :: "real^2" where u: "u \<noteq> 0 \<and>
      (\<forall>x\<in>{?a, ?b, ?c}. \<forall>y\<in>{?a, ?b, ?c}. \<exists>c. x - y = c *\<^sub>R u)"
    by (meson collinear)
  then obtain c1 c2 where c1: "?b - ?a = c1 *\<^sub>R u" and c2: "?c - ?a = c2 *\<^sub>R u" by blast
  then have "c1 *\<^sub>R u = ?b"
    by (metis (no_types, opaque_lifting) diff_zero scaleR_eq_0_iff vector_2(1) vector_2(2) vector_minus_component vector_scaleR_component zero_neq_one) 
  moreover have "c2 *\<^sub>R u = ?c" using c1 c2 calculation by force
  ultimately have "u$1 = 0 \<and> u$2 = 0"
    by (metis scaleR_eq_0_iff vector_2(1) vector_2(2) vector_scaleR_component zero_neq_one)
  then have "u = 0"
    by (metis (mono_tags, opaque_lifting) exhaust_2 vec_eq_iff zero_index)
  moreover have "u \<noteq> 0" using u by auto
  ultimately show False by auto
qed

lemma unit_triangle_convex:
  assumes "p = (make_polygonal_path [vector [0, 0], vector [1, 0], vector [0, 1], vector[0, 0]])"
    (is "p = make_polygonal_path [?O, ?e1, ?e2, ?O]")
  shows "convex (path_inside p)"
proof-
  have "\<not> collinear {?O, ?e1, ?e2}" by (simp add: unit_triangle_vts_not_collinear)
  thus ?thesis using triangle_is_convex make_triangle_def assms by force
qed

lemma unit_triangle_char:
  shows "unit_triangle = {x. 0 \<le> x $ 1 \<and> 0 \<le> x $ 2 \<and> x $ 1 + x $ 2 \<le> 1}"
    (is "unit_triangle = ?S")
proof-
  have "unit_triangle \<subseteq> ?S"
  proof(rule subsetI)
    fix x assume "x \<in> unit_triangle"
    then obtain a b c where
        "x =  a *\<^sub>R (vector [0, 0]) + b *\<^sub>R (vector [1, 0]) + c *\<^sub>R (vector [0, 1])
          \<and> a \<ge> 0 \<and> b \<ge> 0 \<and> c \<ge> 0 \<and> a + b + c = 1"
      using convex_hull_3 by blast
    thus "x \<in> {x. 0 \<le> x $ 1 \<and> 0 \<le> x $ 2 \<and> x $ 1 + x $ 2 \<le> 1}" by simp
  qed
  moreover have "?S \<subseteq> unit_triangle"
  proof(rule subsetI)
    fix x assume "x \<in> ?S"
    then obtain b c where bc: "x$1 = b \<and> x$2 = c \<and> 0 \<le> b \<and> 0 \<le> c \<and> b + c \<le> 1" by blast
    moreover then obtain a where "a \<ge> 0 \<and> a + b + c = 1" using that[of "1 - b - c"] by argo
    moreover have "a *\<^sub>R ((vector [0, 0])::(real^2)) = vector [0, 0]" by (simp add: vec_scaleR_2)
    moreover have "x = (a *\<^sub>R vector [0, 0]) + (b *\<^sub>R vector [1, 0]) + (c *\<^sub>R vector [0, 1])"
      using segment_horizontal bc by fastforce
    ultimately show "x \<in> unit_triangle" using convex_hull_3 by blast
  qed
  ultimately show ?thesis by blast
qed

lemma unit_triangle_interior_char:
  shows "interior unit_triangle = {x. 0 < x $ 1 \<and> 0 < x $ 2 \<and> x $ 1 + x $ 2 < 1}"
    (is "interior unit_triangle = ?S")
proof-
  have "interior unit_triangle \<subseteq> ?S"
  proof(rule subsetI)
    fix x assume "x \<in> interior unit_triangle"
    moreover have "DIM(real^2) = 2" by simp
    ultimately obtain a b c where
        "x =  a *\<^sub>R (vector [0, 0]) + b *\<^sub>R (vector [1, 0]) + c *\<^sub>R (vector [0, 1])
          \<and> a > 0 \<and> b > 0 \<and> c > 0 \<and> a + b + c = 1"
      using interior_convex_hull_3_minimal[of "(vector [0, 0])::(real^2)" "(vector [1, 0])::(real^2)" "(vector [0, 1])::(real^2)"]
      using unit_triangle_vts_not_collinear
      by auto
    thus "x \<in> {x. 0 < x $ 1 \<and> 0 < x $ 2 \<and> x $ 1 + x $ 2 < 1}" by simp
  qed
  moreover have "?S \<subseteq> interior unit_triangle"
  proof(rule subsetI)
    fix x assume "x \<in> ?S"
    then obtain b c where bc: "x$1 = b \<and> x$2 = c \<and> 0 < b \<and> 0 < c \<and> b + c < 1" by blast
    moreover then obtain a where "a > 0 \<and> a + b + c = 1" using that[of "1 - b - c"] by argo
    moreover have "a *\<^sub>R ((vector [0, 0])::(real^2)) = vector [0, 0]" by (simp add: vec_scaleR_2)
    moreover have "x = (a *\<^sub>R vector [0, 0]) + (b *\<^sub>R vector [1, 0]) + (c *\<^sub>R vector [0, 1])"
      using segment_horizontal bc by fastforce
    moreover have "DIM(real^2) = 2" by simp
    ultimately show "x \<in> interior unit_triangle"
      using interior_convex_hull_3_minimal[of "(vector [0, 0])::(real^2)" "(vector [1, 0])::(real^2)" "(vector [0, 1])::(real^2)"]
      using unit_triangle_vts_not_collinear
      by fast
  qed
  ultimately show ?thesis by blast
qed

lemma unit_triangle_is_elementary: "elem_triangle (vector [0, 0]) (vector [1, 0]) (vector [0, 1])"
  (is "elem_triangle ?a ?b ?c")
proof-
  let ?UT = "unit_triangle"
  have "\<not> collinear {?a, ?b, ?c}" using unit_triangle_vts_not_collinear by auto
  moreover have "integral_vec ?a \<and> integral_vec ?b \<and> integral_vec ?c"
    by (simp add: integral_vec_def is_int_def)
  moreover have "{x \<in> ?UT. integral_vec x} = {?a, ?b, ?c}" (is "?UT_integral = ?abc")
  proof-
    have "?UT_integral \<supseteq> ?abc" using calculation(2) hull_subset by fastforce
    moreover have "?UT_integral \<subseteq> ?abc"
    proof - 
      have "\<And>x. x \<in> unit_triangle \<Longrightarrow> integral_vec x \<Longrightarrow> x \<noteq> vector [0, 0] \<Longrightarrow> x \<noteq> vector [1, 0] \<Longrightarrow> x \<noteq> vector [0, 1] \<Longrightarrow> False"
      proof-
        fix x
        assume *: "x \<in> unit_triangle"
               "integral_vec x"
               " x \<noteq> vector [0, 0]" 
               "x \<noteq> vector [1, 0]" 
               "x \<noteq> vector [0, 1]" 
        then have x_inset: "x \<in>{x. 0 \<le> x $ 1 \<and> 0 \<le> x $ 2 \<and> x $ 1 + x $ 2 \<le> 1}"
          using unit_triangle_char by auto
        have "x $ 1 = 1 \<Longrightarrow> x $ 2 \<noteq> 0"
          using *           
          by (smt (verit, del_insts) exhaust_2 vec_eq_iff vector_2(1) vector_2(2))
        then have "x $ 1 = 1 \<Longrightarrow> x $ 1 + x $ 2 > 1 \<or> x $ 2 < 0"
          using *(2) unfolding integral_vec_def is_int_def 
          by linarith
        then have x1_not_1: "x$1 = 1 \<Longrightarrow> False"
          using x_inset by simp
        have "x $ 1 = 0 \<Longrightarrow> x $ 2 \<noteq> 0 \<and> x $ 2 \<noteq> 1"
          using * 
          by (smt (verit, del_insts) exhaust_2 vec_eq_iff vector_2(1) vector_2(2))
        then have "x $ 1 = 0 \<Longrightarrow> x $ 1 + x $ 2 > 1 \<or> x $ 1 + x $ 2 < 0"
          using *(2) unfolding integral_vec_def is_int_def 
          by auto
        then have x1_not_0: "x $ 1 = 0 \<Longrightarrow> False"
          using x_inset by simp
        have x1_not_lt0: "x $ 1 < 0 \<Longrightarrow> False"
          using x_inset by auto
        have x1_not_gt1: "x $ 1 > 1 \<Longrightarrow> False"
          using x_inset by auto 
        then show "False" using x1_not_0 x1_not_1 x1_not_lt0 x1_not_gt1
          using *(2) unfolding integral_vec_def is_int_def 
          by force
      qed
      then have "\<exists>x \<in> ?UT_integral. x \<notin> ?abc \<and> integral_vec x \<Longrightarrow> False"
        by blast
      then show ?thesis by blast
    qed
    ultimately show ?thesis by blast 
  qed
  ultimately show ?thesis unfolding elem_triangle_def by auto
qed

lemma unit_triangles_same_area:
  "measure lebesgue unit_triangle' = measure lebesgue unit_triangle"
proof-
  let ?a = "(vector [1, 1])::real^2"
  let ?b = "(vector [0, 1])::real^2"
  let ?c = "(vector [1, 0])::real^2"
  let ?A = "triangle_affine ?a ?b ?c"
  let ?L = "triangle_linear ?a ?b ?c"
  have collinear_second_component: "\<And>c::real^2. collinear {?a, ?b, c} \<Longrightarrow> c $ 2 = 1"
  proof - 
    fix p
    assume "collinear {?a, ?b, p} "
    then obtain u where u_prop: "\<forall>x\<in>{vector [1, 1], vector [0, 1], p}.
           \<forall>y\<in>{vector [1, 1], vector [0, 1], p}. \<exists>c. x - y = c *\<^sub>R u"
      unfolding collinear_def by auto
    then have c_ab: "\<exists>c. ?a - ?b = c *\<^sub>R u"
      by blast
    then have u_2: "u $ 2 = 0"
      using vector_2 
      by (metis cancel_comm_monoid_add_class.diff_cancel diff_zero scaleR_eq_0_iff vector_minus_component vector_scaleR_component zero_neq_one)
    have u_1: "u$1 \<noteq> 0"
      using c_ab vector_2 
      by (smt (z3) scaleR_right_diff_distrib vector_minus_component vector_scaleR_component)
    then have "(\<exists>c. ?a - p = c *\<^sub>R u) \<and> (\<exists>c. ?b - p = c *\<^sub>R u)"
      using u_prop by blast
    then show "p $ 2 = 1"
      using u_1 u_2 
      by (metis eq_iff_diff_eq_0 scaleR_zero_right vector_2(2) vector_minus_component vector_scaleR_component)
  qed
  have "unit_triangle' = convex hull {?a, ?b, ?c}" by (simp add: insert_commute)
  then have "?A ` unit_triangle = unit_triangle'" using triangle_affine_img[of ?a ?b ?c] by argo
  moreover have "abs (det (matrix ?L)) = 1"
  proof-
    have "matrix ?L = transpose (vector [?b - ?a, ?c - ?a])"
      unfolding triangle_linear_def
      by (simp add: triangle_mat_def)
    also have "det ... = det (vector [?b - ?a, ?c - ?a])" using det_transpose by blast
    also have "... = (?b - ?a)$1 * (?c - ?a)$2 - (?c - ?a)$1 * (?b - ?a)$2"
      using det_2 by (metis mult.commute vector_2(1) vector_2(2))
    finally show ?thesis by simp
  qed
  moreover have "\<not> collinear {?a, ?b, ?c}" using collinear_second_component vector_2 by force
  ultimately have "measure lebesgue unit_triangle' = integral unit_triangle (\<lambda>(x::real^2). 1)"
    using triangle_measure_integral_of_det[of ?a ?b ?c]
    by (smt (verit, ccfv_SIG) Henstock_Kurzweil_Integration.integral_cong insert_commute)
  also have "... = measure lebesgue unit_triangle"
    by (simp add: lmeasure_integral unit_triangle_lmeasurable)
  finally show ?thesis .
qed

section "Unit Square"

(* based on existing convex_hull_3 lemma *)
lemma convex_hull_4:
  "convex hull {a,b,c,d} = { u *\<^sub>R a + v *\<^sub>R b + w *\<^sub>R c + t *\<^sub>R d | u v w t. 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> 0 \<le> t \<and> u + v + w + t = 1}"
proof -
  have fin: "finite {a,b,c,d}" "finite {b,c,d}" "finite {c,d}" "finite {d}"
    by auto
  have *: "\<And>x y z w ::real. x + y + z + w = 1 \<longleftrightarrow> x = 1 - y - z - w"
    by (auto simp: field_simps)
  show ?thesis
    unfolding convex_hull_finite[OF fin(1)]
    unfolding convex_hull_finite_step[OF fin(2)]
    unfolding convex_hull_finite_step[OF fin(3)]
    unfolding convex_hull_finite_step[OF fin(4)]
    unfolding *
    apply auto
     apply (smt (verit, ccfv_threshold) add.commute diff_add_cancel diff_diff_eq)
    subgoal for v w t
      apply (rule exI [where x="1 - v - w - t"], simp)
      apply (rule exI [where x=v], simp)
      apply (rule exI [where x=w], simp)
      apply (rule exI [where x="\<lambda>x. t"], simp)
      done
    done
qed

lemma unit_square_characterization_helper:
  fixes a b :: real
  assumes "0 \<le> a \<and> a \<le> 1 \<and> 0 \<le> b \<and> b \<le> 1" and
          "a \<le> b"
  obtains u v w t where
      "vector [a, b] = u *\<^sub>R ((vector [0, 0])::real^2)
        + v *\<^sub>R (vector [0, 1])
        + w *\<^sub>R (vector [1, 1])
        + t *\<^sub>R (vector [1, 0])
      \<and> 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> 0 \<le> t \<and> u + v + w + t = 1"
proof-
  let ?a = "(vector [0, 0])::(real^2)"
  let ?b = "(vector [0, 1])::(real^2)"
  let ?c = "(vector [1, 1])::(real^2)"
  let ?d = "(vector [1, 0])::(real^2)"
  let ?w = "a"
  let ?v = "b - a"
  let ?u = "(1 - ?w - ?v)::real"
  let ?t = "0::real"
  let ?T = "{u *\<^sub>R ?a + v *\<^sub>R ?b + w *\<^sub>R ?c + t *\<^sub>R ?d | u v w t. 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> 0 \<le> t \<and> u + v + w + t = 1}"
  have "?u *\<^sub>R ?a = 0"
    by (smt (verit, del_insts) exhaust_2 scaleR_zero_right vec_eq_iff vector_2(1) vector_2(2) zero_index)
  moreover have "?w *\<^sub>R ?c = vector [a, a]"
  proof-
    have "(?w *\<^sub>R ?c)$1 = a" by simp
    moreover have "(?w *\<^sub>R ?c)$2 = a" by simp
    ultimately show ?thesis by (smt (verit) vec_eq_iff exhaust_2 vector_2(1) vector_2(2))
  qed
  moreover have "?v *\<^sub>R ?b = vector [0, b - a]"
  proof-
    have "(?v *\<^sub>R ?b)$1 = 0" by fastforce
    moreover have "(?v *\<^sub>R ?b)$2 = b - a" by simp
    ultimately show ?thesis by (smt (verit) vec_eq_iff exhaust_2 vector_2(1) vector_2(2))
  qed
  ultimately have "?u *\<^sub>R ?a + ?v *\<^sub>R ?b + ?w *\<^sub>R ?c + ?t *\<^sub>R ?d = vector [0, b - a] + vector [a, a]"
    by fastforce
  also have "... = vector [a, b]"
    by (smt (verit, del_insts) diff_add_cancel exhaust_2 vec_eq_iff vector_2(1) vector_2(2) vector_add_component)
  finally have "vector [a, b] = ?u *\<^sub>R ?a + ?v *\<^sub>R ?b + ?w *\<^sub>R ?c + ?t *\<^sub>R ?d" by presburger
  moreover have "0 \<le> ?u \<and> ?u \<le> 1  \<and> 0 \<le> ?v \<and> ?v \<le> 1" using assms by simp
  moreover have "0 \<le> ?w \<and> ?w \<le> 1 \<and> 0 \<le> ?t \<and> ?t \<le> 1" using assms  by simp
  moreover have "?u + ?v + ?w + ?t = 1" by argo
  ultimately show ?thesis using that[of ?u ?v ?w ?t] by blast
qed

lemma unit_square_characterization:
  "unit_square = {x. 0 \<le> x$1 \<and> x$1 \<le> 1 \<and> 0 \<le> x$2 \<and> x$2 \<le> 1}" (is "unit_square = ?S")
proof-
  let ?a = "(vector [0, 0])::(real^2)"
  let ?b = "(vector [0, 1])::(real^2)"
  let ?c = "(vector [1, 1])::(real^2)"
  let ?d = "(vector [1, 0])::(real^2)"
  let ?T = "{u *\<^sub>R ?a + v *\<^sub>R ?b + w *\<^sub>R ?c + t *\<^sub>R ?d | u v w t. 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> 0 \<le> t \<and> u + v + w + t = 1}"
  have "unit_square = ?T" using convex_hull_4 by blast
  moreover have "?T \<subseteq> ?S"
  proof(rule subsetI)
    fix x
    assume "x \<in> ?T"
    then obtain u v w t where "x = u *\<^sub>R ?a + v *\<^sub>R ?b + w *\<^sub>R ?c + t *\<^sub>R ?d" and
        "0 \<le> u" and "0 \<le> v" and "0 \<le> w" and "0 \<le> t" and "u + v + w + t = 1" by auto
    moreover from this have
        "x$1 = u * 0 + v * 0 + w * 1 + t * 1 \<and> x$2 = u * 0 + v * 1 + w * 1 + t * 0" by simp
    ultimately have "0 \<le> x$1 \<and> x$1 \<le> 1 \<and> 0 \<le> x$2 \<and> x$2 \<le> 1" by linarith
    thus "x \<in> ?S" by blast
  qed
  moreover have "?S \<subseteq> ?T"
  proof(rule subsetI)
    fix x :: "real^2"
    assume *: "x \<in> ?S"
    { assume "x$1 < x$2"
      then have "x$1 \<le> x$2" by fastforce
      then obtain u v w t where "vector [x$1, x$2] = u *\<^sub>R ?a + v *\<^sub>R ?b + w *\<^sub>R ?c + t *\<^sub>R ?d \<and> 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> 0 \<le> t \<and> u + v + w + t = 1"
        using * unit_square_characterization_helper[of "x$1" "x$2"] by blast
      moreover have "x = vector [x$1, x$2]"
        by (smt (verit, ccfv_threshold) exhaust_2 vec_eq_iff vector_2(1) vector_2(2))
      ultimately have "x \<in> ?T" by force
    } moreover
    { assume "x$1 \<ge> x$2"
      then obtain u v w t where **: "vector [x$2, x$1] = u *\<^sub>R ?a + v *\<^sub>R ?b + w *\<^sub>R ?c + t *\<^sub>R ?d \<and> 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> 0 \<le> t \<and> u + v + w + t = 1"
        using * unit_square_characterization_helper[of "x$2" "x$1"] by blast
      have x1: "x$1 = v + w" using **
        by (smt (verit, ccfv_threshold) mult_cancel_left1 real_scaleR_def scaleR_zero_right vector_2(2) vector_add_component vector_scaleR_component)
      have x2: "x$2 = w + t" using **
        by (smt (verit) mult_cancel_left1 real_scaleR_def scaleR_zero_right vector_2(1) vector_add_component vector_scaleR_component)
      have "(u *\<^sub>R ?a + t *\<^sub>R ?b + w *\<^sub>R ?c + v *\<^sub>R ?d)$1 = w + v" by auto
      moreover have "(u *\<^sub>R ?a + t *\<^sub>R ?b + w *\<^sub>R ?c + v *\<^sub>R ?d)$2 = t + w" by fastforce
      ultimately have "u *\<^sub>R ?a + t *\<^sub>R ?b + w *\<^sub>R ?c + v *\<^sub>R ?d = vector [w + v, t + w]"
        by (smt (verit) vec_eq_iff exhaust_2 vector_2(1) vector_2(2))
      also have "... = x" using x1 x2
        by (smt (verit, del_insts) add.commute exhaust_2 vec_eq_iff vector_2(1) vector_2(2))
      ultimately have "x \<in> ?T"
        by (smt (verit, ccfv_SIG) ** mem_Collect_eq)
    }
    ultimately show "x \<in> ?T" by argo
  qed
  ultimately show ?thesis by auto
qed            

lemma e1e2_basis:
  defines "e1 \<equiv> (vector [1, 0])::(real^2)" and
          "e2 \<equiv> (vector [0, 1])::(real^2)"
  shows "e1 = axis 1 (1::real)" and "e1 \<in> (Basis::((real^2) set))" and
        "e2 = axis 2 (1::real)" and "e2 \<in> (Basis::((real^2) set))"
proof-
  have "(1::real) \<in> Basis" by simp
  then have "axis 1 (1::real) \<in> (\<Union>i. \<Union>u\<in>(Basis::(real set)). {axis i u})" by blast
  moreover show e1_axis: "e1 = axis 1 (1::real)"
    unfolding axis_def vector_def e1_def by auto
  ultimately show e1_basis: "e1 \<in> (Basis::((real^2) set))" by simp

  have "(1::real) \<in> Basis" by simp
  then have "axis 1 (1::real) \<in> (\<Union>i. \<Union>u\<in>(Basis::(real set)). {axis i u})" by blast
  moreover show e2_axis: "e2 = axis 2 (1::real)"
    unfolding axis_def vector_def e2_def by auto
  ultimately show e2_basis: "e2 \<in> (Basis::((real^2) set))" by simp
qed

lemma unit_square_cbox: "unit_square = cbox (vector [0, 0]) (vector [1, 1])"
proof-
  let ?O = "(vector [0, 0])::(real^2)"
  let ?e1 = "(vector [1, 0])::(real^2)"
  let ?e2 = "(vector [0, 1])::(real^2)"
  let ?I = "(vector [1, 1])::(real^2)"
  let ?cbox = "{x. \<forall>i\<in>Basis. ?O \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> ?I \<bullet> i}"

  have "unit_square = {x. 0 \<le> x$1 \<and> x$1 \<le> 1 \<and> 0 \<le> x$2 \<and> x$2 \<le> 1}" (is "unit_square = ?S")
    using unit_square_characterization by auto
  moreover have "?S \<subseteq> ?cbox"
  proof(rule subsetI)
    fix x
    assume *: "x \<in> ?S"
    have "?O \<bullet> ?e1 \<le> x \<bullet> ?e1 \<and> x \<bullet> ?e1 \<le> ?I \<bullet> ?e1"
      using e1e2_basis
      by (smt (verit, del_insts) * cart_eq_inner_axis mem_Collect_eq vector_2(1))
    moreover have "?O \<bullet> ?e2 \<le> x \<bullet> ?e2 \<and> x \<bullet> ?e2 \<le> ?I \<bullet> ?e2"
      using e1e2_basis
      by (smt (verit, del_insts) * cart_eq_inner_axis mem_Collect_eq vector_2(2))
    ultimately show "x \<in> ?cbox"
      by (smt (verit, best) * axis_index cart_eq_inner_axis exhaust_2 mem_Collect_eq vector_2(1) vector_2(2))
  qed
  moreover have "?cbox \<subseteq> ?S"
  proof(rule subsetI)
    fix x :: "real^2"
    assume *: "x \<in> ?cbox"
    then have "0 \<le> ?e1 \<bullet> x" using e1e2_basis
      by (metis (no_types, lifting) cart_eq_inner_axis inner_commute mem_Collect_eq vector_2(1))
    moreover have "?e1 \<bullet> x \<le> 1" using e1e2_basis
      by (smt (verit, ccfv_SIG) * inner_axis inner_commute mem_Collect_eq real_inner_1_right vector_2(1))
    moreover have "0 \<le> ?e2 \<bullet> x"
      by (metis (no_types, lifting) * cart_eq_inner_axis e1e2_basis(3) e1e2_basis(4) inner_commute mem_Collect_eq vector_2(2))
    moreover have "?e2 \<bullet> x \<le> 1"
      by (metis (no_types, lifting) * cart_eq_inner_axis e1e2_basis(3) e1e2_basis(4) inner_commute mem_Collect_eq vector_2(2))
    moreover have "?e1 \<bullet> x = x$1"
      by (simp add: cart_eq_inner_axis e1e2_basis inner_commute)
    moreover have "?e2 \<bullet> x = x$2"
      by (simp add: cart_eq_inner_axis e1e2_basis inner_commute)
    ultimately show "x \<in> ?S" by force
  qed
  ultimately show ?thesis unfolding cbox_def by order
qed

lemma unit_square_area: "measure lebesgue unit_square = 1"
proof-
  let ?e1 = "(vector [1, 0])::(real^2)"
  let ?e2 = "(vector [0, 1])::(real^2)"
  have "unit_square = cbox (vector [0, 0]) (vector [1, 1])" (is "unit_square = cbox ?O ?I")
    using unit_square_cbox by blast
  also have "emeasure lborel ... = 1" using emeasure_lborel_cbox_eq
  proof-
    have "?I \<bullet> ?e1 = (1::real)"
      by (simp add: e1e2_basis(1) inner_axis' inner_commute)
    moreover have "?I \<bullet> ?e2 = (1::real)" by (simp add: e1e2_basis(3) inner_axis' inner_commute)
    ultimately have basis_dot: "\<forall>b \<in> Basis. ?I \<bullet> b = 1"
      by (metis (full_types) axis_inverse e1e2_basis(1) e1e2_basis(3) exhaust_2)

    have "?O \<bullet> ?e1 \<le> ?I \<bullet> ?e1" by (simp add: e1e2_basis(1) inner_axis)
    moreover have "?O \<bullet> ?e2 \<le> ?I \<bullet> ?e2" by (simp add: e1e2_basis(3) inner_axis)
    ultimately have "\<forall>b \<in> Basis. ?O \<bullet> b \<le> ?I \<bullet> b"
      by (smt (verit, ccfv_threshold) axis_index cart_eq_inner_axis exhaust_2 insert_iff vector_2(1) vector_2(2))
    then have "emeasure lborel (cbox ?O ?I) = (\<Prod>b\<in>Basis. (?I - ?O) \<bullet> b)"
      using emeasure_lborel_cbox_eq by auto
    also have "... = (\<Prod>b\<in>Basis. ?I \<bullet> b)"
      by (smt (verit, del_insts) axis_index diff_zero euclidean_all_zero_iff exhaust_2 inner_axis real_inner_1_right vector_2(1) vector_2(2))
    also have "... = (\<Prod>b\<in>Basis. (1::real))" using basis_dot by fastforce
    finally show ?thesis by simp
  qed
  finally have "emeasure lborel unit_square = 1" .
  moreover have "emeasure lborel unit_square = measure lebesgue unit_square"
    by (simp add: emeasure_eq_measure2 unit_square_cbox)
  ultimately show ?thesis by fastforce
qed

section "Unit Triangle Area is 1/2"

lemma unit_triangle'_char:
  shows "unit_triangle' = {x.  x $ 1 \<le> 1 \<and> x $ 2 \<le> 1 \<and> x $ 1 + x $ 2 \<ge> 1}"
proof - 
  let ?I = "(vector [1, 1])::real^2"
  let ?e1 = "(vector [1, 0])::real^2"
  let ?e2 = "(vector [0, 1])::real^2"
  have "unit_triangle' = {u *\<^sub>R ?I + v *\<^sub>R ?e1 + w *\<^sub>R ?e2 | u v w. 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> u + v + w = 1}"
    using convex_hull_3[of ?I ?e1 ?e2] by auto
  moreover have "\<And>u v w. u *\<^sub>R ?I + v *\<^sub>R ?e1 + w *\<^sub>R ?e2 = ((vector [u + v, u + w])::real^2)"
  proof-
    fix u v w :: real

    let ?v_e1 = "((vector [v, 0])::real^2)"
    let ?w_e2 = "((vector [0, w])::real^2)"
    let ?u_I = "((vector [u, u])::real^2)"

    have "u *\<^sub>R ?I = ?u_I" using vec_scaleR_2 by simp
    moreover have "v *\<^sub>R ?e1 = ?v_e1" using vec_scaleR_2 by simp
    moreover have "w *\<^sub>R ?e2 = ?w_e2" using vec_scaleR_2 by simp
    ultimately have 1: "u *\<^sub>R ?I + v *\<^sub>R ?e1 + w *\<^sub>R ?e2 = ?u_I + ?v_e1 + ?w_e2" by argo
    moreover have "(?u_I  + ?v_e1 + ?w_e2)$1 = u + v"
      using vector_add_component by simp
    moreover have "(?u_I  + ?v_e1 + ?w_e2)$2 = u + w"
      using vector_add_component by simp
    ultimately have "?u_I  + ?v_e1 + ?w_e2 = ((vector [u + v, u + w])::real^2)"
      using vector_2 exhaust_2 by (smt (verit, del_insts) vec_eq_iff)
    thus "u *\<^sub>R ?I + v *\<^sub>R ?e1 + w *\<^sub>R ?e2 = ((vector [u + v, u + w])::real^2)" using 1 by argo
  qed
  ultimately have 1: "unit_triangle' = {(vector[u + v, u + w])::real^2 | u v w. 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> u + v + w = 1}"
    (is "unit_triangle' = ?S")
    by presburger
  have "unit_triangle' = {(vector[x, y])::real^2 | x y. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<and> x + y \<ge> 1}"
    (is "unit_triangle' = ?T")
  proof- (* can probably be cleaner *)
    have "\<And>x y::real. \<exists>u v w. 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> u + v + w = 1 \<and> x = u + v \<and> y = u + w
        \<Longrightarrow> 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<and> x + y \<ge> 1" by force
    moreover have *: "\<And>x y::real. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<and> x + y \<ge> 1
        \<Longrightarrow> \<exists>u v w. 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> u + v + w = 1 \<and> x = u + v \<and> y = u + w"
    proof-
      fix x y :: real
      let ?u = "y + x - 1"
      let ?v = "1 - y"
      let ?w = "1 - x"
      assume "0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<and> 1 \<le> x + y"
      then have "0 \<le> ?u \<and> 0 \<le> ?v \<and> 0 \<le> ?w \<and> ?u + ?v + ?w = 1 \<and> x = ?u + ?v \<and> y = ?u + ?w" by argo 
      thus "\<exists>u v w. 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> u + v + w = 1 \<and> x = u + v \<and> y = u + w" by blast
    qed
    ultimately have "\<forall>x y::real. ((\<exists>u v w. 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> u + v + w = 1 \<and> x = u + v \<and> y = u + w)
        \<longleftrightarrow> (0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<and> x + y \<ge> 1))"
      by metis
    then have "\<forall>z::real^2. ((\<exists>u v w. 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> u + v + w = 1 \<and> z$1 = u + v \<and> z$2 = u + w)
        \<longleftrightarrow> (0 \<le> z$1 \<and> z$1 \<le> 1 \<and> 0 \<le> z$2 \<and> z$2 \<le> 1 \<and> z$1 + z$2 \<ge> 1))" by presburger
    then have "\<forall>z::real^2. ((\<exists>u v w. 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> u + v + w = 1 \<and> z = vector [u + v, u + w])
        \<longleftrightarrow> (\<exists>x y. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<and> x + y \<ge> 1 \<and> z = vector [x, y]))"
      by (smt (verit) *)
    moreover have "\<forall>z::real^2. z \<in> ?S \<longleftrightarrow> (\<exists>u v w. 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> u + v + w = 1 \<and> z = vector [u + v, u + w])"
      by blast
    moreover have "\<forall>z::real^2. z \<in> ?T \<longleftrightarrow> (\<exists>x y. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<and> x + y \<ge> 1 \<and> z = vector [x, y])"
      by blast
    ultimately have "?S = ?T" by auto
    then show ?thesis using 1 by auto
  qed
  moreover have "{x. 0 \<le> x$1 \<and> x$1 \<le> 1 \<and> 0 \<le> x$2 \<and> x$2 \<le> 1 \<and> x$1 + x$2 \<ge> 1} \<subseteq> ?T"
  proof(rule subsetI)
    fix z :: "real^2"
    assume *: "z \<in> {x. 0 \<le> x$1 \<and> x$1 \<le> 1 \<and> 0 \<le> x$2 \<and> x$2 \<le> 1 \<and> x$1 + x$2 \<ge> 1}"
    then obtain x y :: real where "z = vector[x, y] \<and> 0 \<le> x" using forall_vector_2 by fastforce
    moreover from this have "x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<and> x + y \<ge> 1" using * vector_2[of x y] by simp
    ultimately show "z \<in> ?T" by blast
  qed
  moreover have "?T \<subseteq> {x. 0 \<le> x$1 \<and> x$1 \<le> 1 \<and> 0 \<le> x$2 \<and> x$2 \<le> 1 \<and> x$1 + x$2 \<ge> 1}"
    using vector_2 by force
  ultimately show ?thesis
    by (smt (verit, best) Collect_cong subset_antisym)
qed

lemma unit_square_split_diag:
  shows "unit_square = unit_triangle \<union> unit_triangle'"
proof-
  let ?S = "({vector [0, 0], vector [0, 1], vector [1, 0]})::((real^2) set)"
  let ?S' = "({vector [1, 1], vector [0, 1], vector [1, 0]})::((real^2) set)"
  have "unit_triangle \<union> unit_triangle' \<subseteq> convex hull (?S \<union> ?S')" by (simp add: hull_mono)
  moreover have "convex hull (?S \<union> ?S') \<subseteq> unit_triangle \<union> unit_triangle'"
    by (smt (z3) Un_commute Un_left_commute Un_upper1 in_mono insert_is_Un mem_Collect_eq subsetI sup.idem unit_square_characterization unit_triangle_char unit_triangle'_char)
  moreover have "unit_square = convex hull (?S \<union> ?S')" by (simp add: insert_commute)
  ultimately show ?thesis by blast
qed

lemma unit_triangle_INT_unit_triangle'_measure:
  "measure lebesgue (unit_triangle \<inter> unit_triangle') = 0"
proof - 
  let ?e1 = "(vector [1, 0])::real^2"
  let ?e2 = "(vector [0, 1])::real^2"
  have "unit_triangle \<inter> unit_triangle' = {x::(real^2).  0 \<le> x $ 1 \<and> x $ 1 \<le> 1 \<and> 0 \<le> x $ 2 \<and> x $ 2 \<le> 1 \<and> x $ 1 + x $ 2 = 1}"
    (is "unit_triangle \<inter> unit_triangle' = ?S")
    using unit_triangle_char unit_triangle'_char 
    by auto
  also have "... = path_image (linepath ?e2 ?e1)"
    (is "... = ?p")
  proof-
    have "?S \<subseteq> ?p"
    proof(rule subsetI)
      fix x :: "real^2"
      assume "x \<in> ?S"
      then have *: "0 \<le> 1 - x$2 \<and> x$2 = 1 - x$1 \<and> 0 \<le> x$2 \<and> x$2 \<le> 1" by simp

      have "x$2 *\<^sub>R ?e2 + x$1 *\<^sub>R ?e1 = vector[x$1, x$2]"
      proof-
        have "(x$1 *\<^sub>R ?e1)$1 = x$1" by simp
        moreover have "(x$1 *\<^sub>R ?e1)$2 = 0" by auto
        moreover have "(x$2 *\<^sub>R ?e2)$1 = 0" by auto
        moreover have "(x$2 *\<^sub>R ?e2)$2 = x$2" by fastforce
        ultimately have "x$1 *\<^sub>R ?e1 = vector [x$1, 0] \<and> x$2 *\<^sub>R ?e2 = vector [0, x$2]"
          by (smt (verit, ccfv_SIG) exhaust_2 vec_eq_iff vector_2(1) vector_2(2))
        then have "x$1 *\<^sub>R ?e1 + x$2 *\<^sub>R ?e2 = vector [x$1, 0] + vector [0, x$2]" by auto
        moreover from this have "(x$1 *\<^sub>R ?e1 + x$2 *\<^sub>R ?e2)$1 = x$1" by auto
        moreover from calculation have "(x$1 *\<^sub>R ?e1 + x$2 *\<^sub>R ?e2)$2 = x$2" by auto
        ultimately show ?thesis
          by (smt (verit) add.commute exhaust_2 vec_eq_iff vector_2(1) vector_2(2))
      qed
      also have "... = x"
        by (smt (verit, best) exhaust_2 vec_eq_iff vector_2(1) vector_2(2))
      finally have "x$2 *\<^sub>R ?e2 + x$1 *\<^sub>R ?e1 = x" .
      then have "x = (\<lambda>x. (1 - x) *\<^sub>R ?e2 + x *\<^sub>R ?e1) (x$1) \<and> x$1 \<in> {0..1}" using * by auto
      thus "x \<in> ?p" unfolding path_image_def linepath_def by fast
    qed
    moreover have "?p \<subseteq> ?S"
    proof(rule subsetI)
      fix x
      assume *: "x \<in> ?p"
      then obtain t where *: "x = (1 - t) *\<^sub>R ?e2 + t *\<^sub>R ?e1 \<and> t \<in> {0..1}"
        unfolding path_image_def linepath_def by blast
      moreover from this have "x$1 = t" by simp
      moreover from calculation have "x$2 = 1 - t" by simp
      moreover from calculation have "0 \<le> t \<and> t \<le> 1 \<and> 0 \<le> 1 - t \<and> 1 - t \<le> 1" by simp
      ultimately show "x \<in> ?S" by simp
    qed
    ultimately show ?thesis by blast
  qed 
  also have "measure lebesgue ?p = 0" using linepath_has_measure_0 by blast
  finally show ?thesis .
qed

lemma unit_triangle_area: "measure lebesgue unit_triangle = 1/2" 
proof-
  let ?\<mu> = "measure lebesgue"
  have "?\<mu> unit_square = ?\<mu> unit_triangle + ?\<mu> unit_triangle'"
    using unit_square_split_diag unit_triangle_INT_unit_triangle'_measure
    by (simp add: finite_imp_bounded_convex_hull measurable_convex measure_Un3)
  thus ?thesis using unit_triangles_same_area unit_square_area by simp
qed

end