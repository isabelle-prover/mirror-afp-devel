theory Elementary_Triangle_Area
imports
  Unit_Geometry

begin

section "Area of Elementary Triangle is 1/2"

lemma nonint_in_square_img_IMP_nonint_triangle_img:
  assumes "A = triangle_affine a b c"
  assumes "x \<in> unit_square"
  assumes "\<not> integral_vec x"
  assumes "integral_vec (A x)"
  assumes "elem_triangle a b c"
  obtains x' where "x' \<in> unit_triangle \<and> \<not> integral_vec x' \<and> integral_vec (A x')"
proof-
  { assume "x \<in> unit_triangle"
    then have ?thesis using assms that by blast
  } moreover
  { assume *: "x \<notin> unit_triangle"
    then have "x \<notin> {x. 0 \<le> x $ 1 \<and> 0 \<le> x $ 2 \<and> x $ 1 + x $ 2 \<le> 1}"
      using unit_triangle_char by argo
    then have x2x1_ge_1: "x$1 + x$2 > 1" using assms(2) unit_square_characterization by force
    let ?x'1 = "1 - x$1"
    let ?x'2 = "1 - x$2"
    let ?x' = "vector [?x'1, ?x'2]"
    have "?x'1 + ?x'2 \<le> 1" using x2x1_ge_1 by argo
    then have "?x' \<in> unit_triangle"
      using unit_triangle_char assms(2) unit_square_characterization by auto
    moreover have "\<not> integral_vec ?x'"
    proof-
      have "\<not> is_int (x$1) \<or> \<not> is_int (x$2)" using assms(3) unfolding integral_vec_def by blast
      then have "\<not> is_int (?x'1) \<or> \<not> is_int (?x'2)"
        using is_int_minus
        by (metis diff_add_cancel is_int_def minus_diff_eq of_int_1 uminus_add_conv_diff)
      thus ?thesis unfolding integral_vec_def by auto
    qed
    moreover have "integral_vec (A ?x')"
    proof-
      let ?L = "triangle_linear a b c"
      have A_comp: "A = (\<lambda>x. x + a) \<circ> ?L" by (simp add: affine_comp_linear_trans assms(1))
      then have Lx_int: "integral_vec (?L x)"
        by (smt (verit, del_insts) assms(4) assms(5) comp_apply diff_add_cancel diff_minus_eq_add integral_vec_minus integral_vec_sum elem_triangle_def)

      have "linear ?L" by (simp add: triangle_linear_def)
      moreover have "?L ?x' = ?L (vector [1, 1] - x)"
        by (simp add: mat_vec_mult_2 triangle_linear_def)
      ultimately have "?L ?x' = ?L (vector [1, 1]) - ?L x" by (simp add: linear_diff)
      moreover have "integral_vec (?L (vector [1, 1]))"
      proof-
        have "?L (vector [1, 1]) = vector [(b - a)$1 + (c - a)$1, (b - a)$2 + (c - a)$2]"
          unfolding triangle_linear_def triangle_mat_def transpose_def using mat_vec_mult_2 by simp
        also have "... = (b - a) + (c - a)"
          by (smt (verit, del_insts) exhaust_2 vec_eq_iff vector_2(1) vector_2(2) vector_add_component)
        finally show ?thesis using assms(5) unfolding elem_triangle_def
          by (metis ab_group_add_class.ab_diff_conv_add_uminus integral_vec_minus integral_vec_sum)
      qed
      ultimately have "integral_vec (?L ?x')"
        using Lx_int integral_vec_sum integral_vec_minus by force
      then show ?thesis using A_comp assms(5) integral_vec_sum elem_triangle_def by auto
    qed
    ultimately have ?thesis using that by blast
  }
  ultimately show ?thesis by blast
qed

lemma elem_triangle_integral_mat_bij:
  fixes a b c :: "real^2"
  assumes "elem_triangle a b c"
  defines "L \<equiv> triangle_mat a b c"
  shows "integral_mat_bij L"
proof-
  let ?A = "triangle_affine a b c"

  have L: "L = transpose (vector [b - a, c - a])" (is "L = transpose (vector [?w1, ?w2])")
    unfolding triangle_mat_def L_def by auto

  have "integral_vec ?w1 \<and> integral_vec ?w2"
    by (metis ab_group_add_class.ab_diff_conv_add_uminus assms(1) integral_vec_minus integral_vec_sum elem_triangle_def) 
  then have L_int_entries: "\<forall>i\<in>{1, 2}. \<forall>j\<in>{1, 2}. is_int (L$i$j)"
    by (simp add: L_def triangle_mat_def Finite_Cartesian_Product.transpose_def integral_vec_def)

  have L_integral: "integral_mat L" unfolding integral_mat_def
  proof(rule allI)
    fix v :: "real^2"
    show "integral_vec v \<longrightarrow> integral_vec (L *v v)"
    proof(rule impI)
      assume v_int_assm: "integral_vec v"
      let ?Lv = "L *v v"
  
      have "?Lv$1 = L$1$1 * v$1 + L$1$2 * v$2" by (simp add: mat_vec_mult_2)
      then have Lv1_int: "is_int (?Lv$1)"
        using L_int_entries v_int_assm is_int_sum is_int_mult by (simp add: integral_vec_def)
  
      have "?Lv$2 = L$2$1 * v$1 + L$2$2 * v$2" by (simp add: mat_vec_mult_2)
      then have Lv2_int: "is_int (?Lv$2)"
        using L_int_entries v_int_assm is_int_sum is_int_mult by (simp add: integral_vec_def)

      show "integral_vec (L *v v)"
        by (simp add: Lv1_int Lv2_int integral_vec_def) 
    qed
  qed
  moreover have "integral_mat_surj L"
    unfolding integral_mat_surj_def
  proof(rule allI)
    fix v :: "real^2"
    show "integral_vec v \<longrightarrow> (\<exists>w. integral_vec w \<and> L *v w = v)"
    proof(rule impI)
      assume *: "integral_vec v"
      obtain w :: "real^2" where w: "L *v w = v"
        using triangle_linear_inj assms(1) full_rank_injective full_rank_surjective
        unfolding elem_triangle_def L_def triangle_linear_def surj_def
        by (smt (verit, best) iso_tuple_UNIV_I)
      moreover have "integral_vec w"
      proof(rule ccontr)
        assume **: "\<not> integral_vec w"
        let ?w1 = "w$1"
        let ?w2 = "w$2"
        let ?w1' = "w$1 - (floor (w$1))"
        let ?w2' = "w$2 - (floor (w$2))"
        let ?w' = "(vector [?w1', ?w2'])::(real^2)"
        have "?w1' \<in> {0..1} \<and> ?w2' \<in> {0..1}"
          by (metis add.commute add.right_neutral atLeastAtMost_iff floor_correct floor_frac frac_def of_int_0 real_of_int_floor_add_one_ge)
        then have "?w' \<in> unit_square" using unit_square_characterization by auto
        moreover have "\<not> integral_vec ?w'"
          by (metis ** eq_iff_diff_eq_0 floor_frac floor_of_int frac_def integral_vec_def is_int_def of_int_0 vector_2(1) vector_2(2))
        moreover have "integral_vec (?A ?w')"
        proof-
          have "?w' = vector [w$1, w$2] - vector [floor (w$1), floor (w$2)]"
              (is "?w' = vector [w$1, w$2] - ?floor_w")
            by (smt (verit, del_insts) exhaust_2 list.simps(8) list.simps(9) vec_eq_iff vector_2(1) vector_2(2) vector_minus_component)
          then have "?w' = w - vector [floor (w$1), floor (w$2)]"
            by (smt (verit, del_insts) exhaust_2 vec_eq_iff vector_2(1) vector_2(2) vector_minus_component)
          moreover have "?A ?w' = (L *v ?w') + a" unfolding triangle_affine_def L_def by simp
          ultimately have "?A ?w' = v - (L *v ?floor_w) + a"
            by (simp add: matrix_vector_mult_diff_distrib w)
          moreover have "integral_vec v \<and> integral_vec a \<and> integral_vec (L *v ?floor_w)"
            using * assms(1) L_integral integral_mat_integral_vec integral_vec_2
            unfolding elem_triangle_def
            by blast
          ultimately show ?thesis
            by (metis ab_group_add_class.ab_diff_conv_add_uminus integral_vec_minus integral_vec_sum)
        qed
        ultimately obtain w'' where w'': "w'' \<in> unit_triangle \<and> \<not> integral_vec w'' \<and> integral_vec (?A w'')"
          using nonint_in_square_img_IMP_nonint_triangle_img[of ?A a b c ?w'] assms(1) by blast
        moreover have "?A w'' \<notin> {a, b, c}"
        proof-
          have "inj ?A" using assms(1) elem_triangle_def triangle_affine_inj by auto
          moreover have "?A (vector [0, 0]) = a"
            by (metis (no_types, opaque_lifting) add.commute add_0 mat_vec_mult_2 matrix_vector_mult_0_right real_scaleR_def scaleR_zero_right triangle_affine_def zero_index)
          moreover have "?A (vector [1, 0]) = b"
            unfolding triangle_affine_def triangle_mat_def transpose_def
            by (metis (no_types) Finite_Cartesian_Product.transpose_def add.commute column_transpose diff_add_cancel e1e2_basis(1) matrix_vector_mult_basis row_def vec_lambda_eta vector_2(1))
          moreover have "?A (vector [0, 1]) = c"
          proof-
            have "(?A (vector [0, 1]))$1 = c$1"
              by (metis L_def L add.commute column_transpose diff_add_cancel e1e2_basis(3) matrix_vector_mult_basis row_def triangle_affine_def vec_lambda_eta vector_2(2))
            moreover have "(?A (vector [0, 1]))$2 = c$2"
              by (metis add.commute column_transpose diff_add_cancel e1e2_basis(3) matrix_vector_mult_basis row_def triangle_affine_def triangle_mat_def vec_lambda_eta vector_2(2))
            ultimately show ?thesis by (smt (verit, ccfv_SIG) exhaust_2 vec_eq_iff)
          qed
          moreover have "w'' \<noteq> vector [0, 0] \<and> w'' \<noteq> vector [0, 1] \<and> w'' \<noteq> vector [1, 0]"
            using w'' elem_triangle_def unit_triangle_is_elementary by blast
          ultimately show ?thesis by (metis inj_eq insertE singletonD)
        qed
        moreover have "?A ` unit_triangle = convex hull {a, b, c}"
          using triangle_affine_img by blast
        ultimately show False using assms unfolding elem_triangle_def by blast
      qed
      ultimately show "\<exists>w. integral_vec w \<and> L *v w = v" by auto
    qed
  qed
  ultimately show ?thesis unfolding integral_mat_bij_def by auto
qed

lemma elem_triangle_measure_integral_of_1:
  fixes a b c :: "real^2"
  defines "S \<equiv> convex hull {a, b, c}"
  assumes "elem_triangle a b c"
  shows "measure lebesgue S = integral unit_triangle (\<lambda>(x::real^2). 1)"
proof-
  let ?T = "triangle_linear a b c"
  have "integral_mat_bij (matrix ?T)" (is "integral_mat_bij ?T_mat")
    by (simp add: assms(2) elem_triangle_integral_mat_bij triangle_linear_def)
  then have "abs (det ?T_mat) = 1"
    using integral_mat_bij_det_pm1 by fastforce
  thus ?thesis
    using S_def assms(2) triangle_measure_integral_of_det elem_triangle_def by force
qed

lemma elem_triangle_area_is_half:
  fixes a b c :: "real^2"
  assumes "elem_triangle a b c"
  defines "S \<equiv> convex hull {a, b, c}"
  shows "measure lebesgue S = 1/2" (is "?S_area = 1/2")
proof-
  have  "\<not> collinear {a, b, c}" using elem_triangle_def assms(1) by blast 
  then have "measure lebesgue S = integral unit_triangle (\<lambda>x::real^2. 1)"
    using S_def assms(1) elem_triangle_measure_integral_of_1 by blast 
  also have "... = measure lebesgue unit_triangle"
    using unit_triangle_is_elementary elem_triangle_measure_integral_of_1 unit_triangle_area
    by metis
  finally show ?thesis by (simp add: unit_triangle_area) 
qed

end