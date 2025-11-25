theory Sylvester_Criterion
  imports
    Cauchy_Eigenvalue_Interlacing
    "Jordan_Normal_Form.Determinant_Impl"

begin

section "Sylvester's Criterion Setup"

definition sylvester_criterion :: "('a::{comm_ring_1,ord}) mat \<Rightarrow> bool" where
  "sylvester_criterion A \<longleftrightarrow> (\<forall>k \<le> dim_row A.  Determinant.det (lps A k) > 0)"

lemma leading_principle_submatrix_sylvester:
  assumes "A \<in> carrier_mat n n"
  assumes "m \<le> n"
  assumes "sylvester_criterion A"
  shows "sylvester_criterion (lps A m)"
  using assms nested_leading_principle_submatrices
  by (smt (verit, del_insts) atLeastAtMost_iff carrier_matD(1) order.trans leading_principal_submatrix_carrier sylvester_criterion_def)

lemma sylvester_criterion_positive_det:
  assumes "A \<in> carrier_mat n n"
  assumes "sylvester_criterion A"
  shows "det A > 0"
proof-
  have "A = lps A n"
    unfolding leading_principal_submatrix_def submatrix_def
    using assms(1) pick_n_le
    by auto
  thus ?thesis using assms unfolding sylvester_criterion_def by force
qed

section "Sylvester's Criterion"

subsection "Forward Implication"

lemma (in cmplx_herm_mat) sylvester_criterion_forward:
  assumes "x \<in> carrier_vec n"
  assumes "sylvester_criterion A"
  assumes "x \<noteq> 0\<^sub>v n"
  shows "Re (QF A x) > 0"
  using assms A_dim A_herm
proof(induction n arbitrary: A x)
  case 0
  then show ?case by (metis carrier_vecD eq_vecI not_less_zero zero_carrier_vec)
next
  case (Suc n)

  have *: "\<And>k. k \<le> dim_row A \<Longrightarrow> det (leading_principal_submatrix A k) > 0"
    using Suc(3) unfolding sylvester_criterion_def by blast

  define A\<^sub>n where "A\<^sub>n \<equiv> (leading_principal_submatrix A n)"
  define v\<^sub>n where "v\<^sub>n \<equiv> vec_first (col A n) n"
  define v\<^sub>nc where "v\<^sub>nc \<equiv> conjugate v\<^sub>n"
  define w\<^sub>n where "w\<^sub>n \<equiv> vec_first (row A n) n"
  define a where "a \<equiv> A $$ (n, n)"
  define x\<^sub>n where "x\<^sub>n \<equiv> vec_first x n"
  define x\<^sub>nc where "x\<^sub>nc = conjugate x\<^sub>n"
  define b where "b \<equiv> x$n"
  define b_conj where "b_conj \<equiv> conjugate b"

  have carrier_A\<^sub>n: "A\<^sub>n \<in> carrier_mat n n"
    by (metis A\<^sub>n_def Suc(5) le_add2 leading_principal_submatrix_carrier plus_1_eq_Suc)
  have herm_A\<^sub>n: "hermitian A\<^sub>n"
    using principal_submatrix_hermitian[of "{..n}"] A\<^sub>n_def Suc A\<^sub>n_def
    using cmplx_herm_mat.leading_principal_submatrix_hermitian cmplx_herm_mat_def lessI less_or_eq_imp_le
    by presburger

  have "(col A n) = conjugate (row A n)"
    using Suc(5,6) by (metis adjoint_col carrier_matD(1) hermitian_def lessI)
  hence wn_vn_conj: "w\<^sub>n = v\<^sub>nc"
    using Suc(5) v\<^sub>n_def v\<^sub>nc_def w\<^sub>n_def
    by (metis conjugate_vec_first col_carrier_vec conjugate_id le_add2 lessI plus_1_eq_Suc)

  have "invertible_mat A\<^sub>n"
    using Suc(5) * A\<^sub>n_def carrier_A\<^sub>n 
    by (metis carrier_matD(1) invertible_det le_add2 less_irrefl plus_1_eq_Suc)
  then obtain A\<^sub>n' where An': "inverts_mat A\<^sub>n' A\<^sub>n \<and> A\<^sub>n' \<in> carrier_mat n n"
    using A\<^sub>n_def Suc(5)
    by (metis (no_types, lifting) invertible_mat_def carrier_matD(1) carrier_matI index_mult_mat(3) index_one_mat(3) inverts_mat_def le_add2 leading_principal_submatrix_carrier plus_1_eq_Suc square_mat.simps)

  have xn: "x\<^sub>n \<in> carrier_vec n" by (simp add: x\<^sub>n_def)
  moreover have An: "A\<^sub>n \<in> carrier_mat n n"
    using leading_principal_submatrix_carrier Suc(5) A\<^sub>n_def by (metis Suc_n_not_le_n linorder_linear)
  ultimately have An_xn: "A\<^sub>n *\<^sub>v x\<^sub>n \<in> carrier_vec n" by fastforce
  have vn: "v\<^sub>n \<in> carrier_vec n" by (simp add: v\<^sub>n_def)
  hence b_vn: "b \<cdot>\<^sub>v v\<^sub>n \<in> carrier_vec n" by simp

  have "(A\<^sub>n *\<^sub>v x\<^sub>n + b \<cdot>\<^sub>v v\<^sub>n) \<in> carrier_vec n" using An_xn b_vn by auto

  from herm_A\<^sub>n have hermitian: "hermitian A\<^sub>n'"
    by (meson An An' cmplx_herm_mat.hermitian_mat_inv cmplx_herm_mat.intro inverts_mat_symm)
  hence A\<^sub>n_inv_conj: "conjugate A\<^sub>n' = A\<^sub>n'\<^sup>T"
    by (metis conjugate_id hermitian_def adjoint_is_conjugate_transpose)

  have **: "(A\<^sub>n *\<^sub>v (x\<^sub>n + b \<cdot>\<^sub>v (A\<^sub>n' *\<^sub>v v\<^sub>n))) \<bullet> (x\<^sub>nc + b_conj \<cdot>\<^sub>v (A\<^sub>n'\<^sup>T *\<^sub>v v\<^sub>nc))
      = (QF A\<^sub>n x\<^sub>n) + b * (x\<^sub>nc \<bullet> v\<^sub>n) + b_conj * (x\<^sub>n \<bullet> v\<^sub>nc) + (cmod b)^2 * ((A\<^sub>n' *\<^sub>v v\<^sub>n) \<bullet> v\<^sub>nc)"
    (is "?lhs = ?rhs")
  proof-
    define E where "E \<equiv> ((A\<^sub>n *\<^sub>v x\<^sub>n) \<bullet> (x\<^sub>nc + b_conj \<cdot>\<^sub>v (A\<^sub>n'\<^sup>T *\<^sub>v v\<^sub>nc)))"
    define F where "F \<equiv> ((b \<cdot>\<^sub>v v\<^sub>n) \<bullet> (x\<^sub>nc + b_conj \<cdot>\<^sub>v (A\<^sub>n'\<^sup>T *\<^sub>v v\<^sub>nc)))"

    have "A\<^sub>n *\<^sub>v (x\<^sub>n + b \<cdot>\<^sub>v (A\<^sub>n' *\<^sub>v v\<^sub>n)) = (A\<^sub>n *\<^sub>v x\<^sub>n) + b \<cdot>\<^sub>v v\<^sub>n"
      (is "?lhs' = _")
    proof-
      have "?lhs' = A\<^sub>n *\<^sub>v x\<^sub>n + A\<^sub>n *\<^sub>v (b \<cdot>\<^sub>v (A\<^sub>n' *\<^sub>v v\<^sub>n))"
        by (meson An' carrier_A\<^sub>n mult_add_distrib_mat_vec mult_mat_vec_carrier smult_carrier_vec vn xn)
      also have "\<dots> = A\<^sub>n *\<^sub>v x\<^sub>n + (b \<cdot>\<^sub>v ((A\<^sub>n * A\<^sub>n') *\<^sub>v v\<^sub>n))"
        by (metis An' assoc_mult_mat_vec carrier_A\<^sub>n mult_mat_vec mult_mat_vec_carrier vn)
      also have "\<dots> = (A\<^sub>n *\<^sub>v x\<^sub>n) + b \<cdot>\<^sub>v v\<^sub>n"
        by (metis An' carrier_A\<^sub>n carrier_matD(1) inverts_mat_def inverts_mat_symm one_mult_mat_vec vn)
      finally show ?thesis .
    qed
    hence "?lhs = ((A\<^sub>n *\<^sub>v x\<^sub>n) + b \<cdot>\<^sub>v v\<^sub>n) \<bullet> (x\<^sub>nc + b_conj \<cdot>\<^sub>v (A\<^sub>n'\<^sup>T *\<^sub>v v\<^sub>nc))" by argo
    moreover have "\<dots> = E + F"
      unfolding E_def F_def
      by (metis An' An_xn Matrix.carrier_vec_conjugate add_carrier_vec add_scalar_prod_distrib mult_mat_vec_carrier smult_carrier_vec transpose_carrier_mat v\<^sub>nc_def vn x\<^sub>nc_def xn)
    moreover have "E = QF A\<^sub>n x\<^sub>n + b_conj * (x\<^sub>n \<bullet> v\<^sub>nc)"
    proof-
      have "E = ((A\<^sub>n *\<^sub>v x\<^sub>n) \<bullet> x\<^sub>nc) + ((A\<^sub>n *\<^sub>v x\<^sub>n) \<bullet> (b_conj \<cdot>\<^sub>v (A\<^sub>n'\<^sup>T *\<^sub>v v\<^sub>nc)))"
        unfolding E_def
        by (metis An' An_xn Matrix.carrier_vec_conjugate mult_mat_vec_carrier scalar_prod_add_distrib smult_carrier_vec transpose_carrier_mat v\<^sub>nc_def vn x\<^sub>nc_def xn)
      moreover have "((A\<^sub>n *\<^sub>v x\<^sub>n) \<bullet> x\<^sub>nc) = QF A\<^sub>n x\<^sub>n" by (simp add: x\<^sub>nc_def)
      moreover have "((A\<^sub>n *\<^sub>v x\<^sub>n) \<bullet> (b_conj \<cdot>\<^sub>v (A\<^sub>n'\<^sup>T *\<^sub>v v\<^sub>nc))) = b_conj * (x\<^sub>n \<bullet> v\<^sub>nc)"
        (is "?lhs = _")
      proof-
        have "?lhs = b_conj * ((A\<^sub>n *\<^sub>v x\<^sub>n) \<bullet> (A\<^sub>n'\<^sup>T *\<^sub>v v\<^sub>nc))" using An An' by auto
        also have "\<dots> = b_conj * ((A\<^sub>n *\<^sub>v x\<^sub>n) \<bullet> (conjugate A\<^sub>n' *\<^sub>v v\<^sub>nc))"
          using A\<^sub>n_inv_conj by presburger
        also have "\<dots> = b_conj * (((A\<^sub>n' * A\<^sub>n) *\<^sub>v x\<^sub>n) \<bullet> v\<^sub>nc)"
          by (smt (verit) An An' conj_mat_vec_mult hermitian hermitian_def inner_prod_mult_mat_vec_right v\<^sub>nc_def vn xn)
        also have "\<dots> = b_conj * (x\<^sub>n \<bullet> v\<^sub>nc)"
          by (metis An' carrier_matD(1) inverts_mat_def one_mult_mat_vec xn)
        finally show ?thesis .
      qed
      ultimately show ?thesis by argo
    qed
    moreover have "F = b * (x\<^sub>nc \<bullet> v\<^sub>n) + (cmod b)^2 * ((A\<^sub>n' *\<^sub>v v\<^sub>n) \<bullet> v\<^sub>nc)"
    proof-
      have "F = (b \<cdot>\<^sub>v v\<^sub>n) \<bullet> (x\<^sub>nc) + (b \<cdot>\<^sub>v v\<^sub>n) \<bullet> (b_conj \<cdot>\<^sub>v (A\<^sub>n'\<^sup>T *\<^sub>v v\<^sub>nc))"
        unfolding F_def
        by (metis An' Matrix.carrier_vec_conjugate b_vn carrier_matD(2) carrier_vec_dim_vec dim_mult_mat_vec index_smult_vec(2) index_transpose_mat(2) scalar_prod_add_distrib x\<^sub>nc_def xn)
      moreover have "(b \<cdot>\<^sub>v v\<^sub>n) \<bullet> (x\<^sub>nc) = b * (v\<^sub>n \<bullet> x\<^sub>nc)" using vn x\<^sub>nc_def xn by auto
      moreover have "(b \<cdot>\<^sub>v v\<^sub>n) \<bullet> (b_conj \<cdot>\<^sub>v (A\<^sub>n'\<^sup>T *\<^sub>v v\<^sub>nc)) = (cmod b)^2 * ((A\<^sub>n' *\<^sub>v v\<^sub>n) \<bullet> v\<^sub>nc)"
        (is "?lhs = _")
      proof-
        have "?lhs = (cmod b)^2 * (v\<^sub>n \<bullet> (A\<^sub>n'\<^sup>T *\<^sub>v v\<^sub>nc))"
          using An' vn b_conj_def complex_norm_square by force
        also have "\<dots> = (cmod b)^2 * ((A\<^sub>n' *\<^sub>v v\<^sub>n) \<bullet> v\<^sub>nc)"
          by (metis A\<^sub>n_inv_conj An' adjoint_def_alter conj_mat_vec_mult hermitian hermitian_def v\<^sub>nc_def vn)
        finally show ?thesis .
      qed
      ultimately show ?thesis by (metis conjugate_vec_sprod_comm vn x\<^sub>nc_def xn)
    qed
    ultimately show ?thesis by fastforce
  qed

  let ?c\<^sub>n = "b \<cdot>\<^sub>v (A\<^sub>n' *\<^sub>v v\<^sub>n)"
  have cn: "?c\<^sub>n \<in> carrier_vec n"
    by (metis An' An_xn \<open>invertible_mat A\<^sub>n\<close> carrier_vecD carrier_vec_dim_vec dim_mult_mat_vec index_mult_mat(3) index_one_mat(3) invertible_mat_def inverts_mat_def smult_carrier_vec square_mat.simps)

  have "A \<in> carrier_mat (Suc n) (Suc n)"
    by (simp add: Suc(5))
  moreover have "x \<in> carrier_vec (Suc n)"
    by (simp add: Suc(2))
  ultimately have Ax: "A *\<^sub>v x = (A\<^sub>n *\<^sub>v x\<^sub>n + b \<cdot>\<^sub>v v\<^sub>n) @\<^sub>v (vec 1 (\<lambda>i. (w\<^sub>n \<bullet> x\<^sub>n) + a * b))"
      (is "_ = _ @\<^sub>v ?Ax_last")
    using mat_vec_prod_leading_principal_submatrix
    unfolding A\<^sub>n_def a_def b_def v\<^sub>n_def w\<^sub>n_def x\<^sub>n_def by blast

  hence "QF A x = \<dots> \<bullet>c x" by force
  also have "\<dots> = ((A\<^sub>n *\<^sub>v x\<^sub>n + b \<cdot>\<^sub>v v\<^sub>n) \<bullet>c x\<^sub>n) + ((w\<^sub>n \<bullet> x\<^sub>n) + a * b) * b_conj"
  proof-
    have "x \<in> carrier_vec (dim_vec ((A\<^sub>n *\<^sub>v x\<^sub>n + b \<cdot>\<^sub>v v\<^sub>n) @\<^sub>v ?Ax_last))"
      using Suc(2) vn by force
    moreover have "(A\<^sub>n *\<^sub>v x\<^sub>n + b \<cdot>\<^sub>v v\<^sub>n) \<bullet>c (vec_first x (dim_vec (A\<^sub>n *\<^sub>v x\<^sub>n + b \<cdot>\<^sub>v v\<^sub>n)))
        = (A\<^sub>n *\<^sub>v x\<^sub>n + b \<cdot>\<^sub>v v\<^sub>n) \<bullet>c x\<^sub>n"
      by (simp add: v\<^sub>n_def x\<^sub>n_def)
    moreover have "dim_vec ?Ax_last = 1" by simp
    moreover have "?Ax_last \<bullet>c (vec_last x 1)  = (w\<^sub>n \<bullet> x\<^sub>n + a * b) * b_conj"
    proof-
      have "dim_vec ?Ax_last = 1" by simp
      moreover have "(vec_last x 1)$0 = b"
        using Suc(2) b_def
        by (smt (verit) add.commute add.right_neutral add_diff_cancel_right' carrier_vecD index_vec plus_1_eq_Suc vec_last_def zero_less_one_class.zero_less_one)
      moreover have "?Ax_last$0 = (w\<^sub>n \<bullet> x\<^sub>n + a * b)" by simp
      moreover have "?Ax_last \<bullet>c (vec_last x 1) = ?Ax_last$0 * conjugate ((vec_last x 1)$0)"
        unfolding scalar_prod_def by force
      ultimately show ?thesis using b_conj_def by presburger
    qed
    ultimately show ?thesis by (simp add: inner_prod_append(2))
  qed
  also have "\<dots> = QF A\<^sub>n x\<^sub>n + ((b \<cdot>\<^sub>v v\<^sub>n) \<bullet>c x\<^sub>n) + ((w\<^sub>n \<bullet> x\<^sub>n) * b_conj) + (a * b * b_conj)"
    using inner_prod_distrib_right[of x\<^sub>n n "A\<^sub>n *\<^sub>v x\<^sub>n" "b \<cdot>\<^sub>v v\<^sub>n"] b_vn An_xn
    by (simp add: ring_class.ring_distribs(2) xn)
  also have "\<dots> = QF A\<^sub>n x\<^sub>n + ((b \<cdot>\<^sub>v v\<^sub>n) \<bullet>c x\<^sub>n) + ((w\<^sub>n \<bullet> x\<^sub>n) * b_conj) + (a * (cmod b)^2)"
    using b_conj_def complex_norm_square by auto
  also have "\<dots> = QF A\<^sub>n x\<^sub>n + b * (x\<^sub>nc \<bullet> v\<^sub>n) + b_conj * (x\<^sub>n \<bullet> v\<^sub>nc) + (a * (cmod b)^2)"
    by (metis conjugate_vec_sprod_comm inner_prod_smult_left mult.commute v\<^sub>nc_def vn wn_vn_conj x\<^sub>nc_def xn)
  also have "\<dots> = (A\<^sub>n *\<^sub>v (x\<^sub>n + b \<cdot>\<^sub>v (A\<^sub>n' *\<^sub>v v\<^sub>n))) \<bullet> (x\<^sub>nc + b_conj \<cdot>\<^sub>v (A\<^sub>n'\<^sup>T *\<^sub>v v\<^sub>nc))
      - (cmod b)^2 * ((A\<^sub>n' *\<^sub>v v\<^sub>n) \<bullet> v\<^sub>nc) + (a * (cmod b)^2)"
    using ** by fastforce
  also have "\<dots> = (A\<^sub>n *\<^sub>v (x\<^sub>n + b \<cdot>\<^sub>v (A\<^sub>n' *\<^sub>v v\<^sub>n))) \<bullet> (x\<^sub>nc + b_conj \<cdot>\<^sub>v (A\<^sub>n'\<^sup>T *\<^sub>v v\<^sub>nc))
      + (cmod b)^2 * (a - QF A\<^sub>n' v\<^sub>n)"
    by (simp add: right_diff_distrib v\<^sub>nc_def)
  also have "\<dots> = QF A\<^sub>n (x\<^sub>n + ?c\<^sub>n) + (cmod b)^2 * (a - QF A\<^sub>n' v\<^sub>n)"
  proof-
    have "conjugate (A\<^sub>n' *\<^sub>v v\<^sub>n) = (conjugate A\<^sub>n' *\<^sub>v v\<^sub>nc)"
      by (metis conj_mat_vec_mult adjoint_dim_col carrier_mat_triv carrier_vecD cn dim_mult_mat_vec hermitian hermitian_def index_smult_vec(2) v\<^sub>nc_def vn)
    thus ?thesis
      by (smt (verit, ccfv_threshold) A\<^sub>n_inv_conj b_conj_def cn conjugate_add_vec conjugate_smult_vec x\<^sub>nc_def xn quadratic_form_def)
  qed
  finally have eq: "QF A x = QF A\<^sub>n (x\<^sub>n + ?c\<^sub>n) + (cmod b)^2 * (a - QF A\<^sub>n' v\<^sub>n)" .

  have x\<^sub>n_c\<^sub>n: "(x\<^sub>n + ?c\<^sub>n) \<in> carrier_vec n" using add_carrier_vec cn xn by blast
  have "sylvester_criterion A\<^sub>n"
    using leading_principle_submatrix_sylvester A\<^sub>n_def Suc(3,5)
    by (metis Suc_n_not_le_n linorder_linear) 
  hence 1: "Re (QF A\<^sub>n (x\<^sub>n + ?c\<^sub>n)) > 0" if "x\<^sub>n + ?c\<^sub>n \<noteq> 0\<^sub>v n"
    using Suc.IH[OF x\<^sub>n_c\<^sub>n _ that carrier_A\<^sub>n herm_A\<^sub>n] by blast
  have 2: "x\<^sub>n + ?c\<^sub>n \<noteq> 0\<^sub>v n" if "b = 0"
  proof-
    have "?c\<^sub>n = 0\<^sub>v n"
      by (metis that cn conjugate_square_eq_0_vec inner_prod_smult_left mult_eq_0_iff smult_smult_assoc)
    hence *: "x\<^sub>n + ?c\<^sub>n = x\<^sub>n" by (simp add: xn)
    show ?thesis
    proof(rule ccontr)
      assume "\<not> x\<^sub>n + ?c\<^sub>n \<noteq> 0\<^sub>v n"
      hence "x\<^sub>n = 0\<^sub>v n" using * by argo
      hence "\<forall>i < n. x\<^sub>n$i = 0" by fastforce
      moreover have "\<forall>i < n. x\<^sub>n$i = x$i" by (simp add: vec_first_def x\<^sub>n_def)
      moreover have "x$n = 0" using that unfolding b_def .
      ultimately have "\<forall>i < Suc n. x$i = 0" using less_Suc_eq by presburger
      thus False using Suc by auto
    qed
  qed
  have 3: "a - QF A\<^sub>n' v\<^sub>n > 0"
  proof-
    have "det A = det A\<^sub>n * (a - QF A\<^sub>n' v\<^sub>n)"
    proof-
      let ?B = "mat_of_cols n [v\<^sub>n]"
      let ?C = "mat_of_rows n [conjugate v\<^sub>n]"
      let ?D = "mat 1 1 (\<lambda>_. a)"

      have "(A\<^sub>n, ?B, ?C, ?D) = split_block A n n"
      proof-
        have "A\<^sub>n = mat n n (($$) A)"
          using A\<^sub>n_def An An_xn Suc(5)
          by (metis carrier_matD(2) carrier_vecD dim_col_mat(1) dim_mult_mat_vec dim_row_mat(1) index_mat(1) le_add2 leading_principal_submatrix_index mat_eq_iff plus_1_eq_Suc)
        moreover have "?B = mat n (dim_col A - n) (\<lambda>(i, j). A $$ (i, j + n))"
          (is "?lhs = ?rhs")
        proof
          show "dim_row ?lhs = dim_row ?rhs" by simp
          show "dim_col ?lhs = dim_col ?rhs" using Suc(5) by force
          show "\<And>i j. i < dim_row ?rhs \<Longrightarrow> j < dim_col ?rhs \<Longrightarrow> ?lhs$$(i,j) = ?rhs$$(i,j)"
          proof-
            fix i j assume *: "i < dim_row ?rhs" "j < dim_col ?rhs"
            hence "j = 0" using Suc(5) by auto
            thus "?lhs$$(i,j) = ?rhs$$(i,j)"
              apply (simp add: v\<^sub>n_def vec_first_def mat_of_cols_def)
              using *(1) Suc(5)
              by auto
          qed
        qed
        moreover have "?C = mat (dim_row A - n) n (\<lambda>(i, j). A $$ (i + n, j))"
          (is "?lhs = ?rhs")
        proof
          show "dim_row ?lhs = dim_row ?rhs" using Suc(5) by force
          show "dim_col ?lhs = dim_col ?rhs" by simp
          show "\<And>i j. i < dim_row ?rhs \<Longrightarrow> j < dim_col ?rhs \<Longrightarrow> ?lhs$$(i,j) = ?rhs$$(i,j)"
          proof-
            fix i j assume *: "i < dim_row ?rhs" "j < dim_col ?rhs"
            hence "i = 0" using Suc(5) by auto
            moreover have "conjugate (vec n (($) (col A n))) = (vec n (($) (row A n)))"
              using Suc(4)
              unfolding hermitian_def adjoint_def
              by (metis v\<^sub>n_def v\<^sub>nc_def vec_first_def w\<^sub>n_def wn_vn_conj)
            ultimately show "?lhs$$(i,j) = ?rhs$$(i,j)"
              apply (simp add: v\<^sub>n_def vec_first_def mat_of_cols_def)
              using *(2) Suc(5)
              by (simp add: mat_of_rows_def)
          qed
        qed
        moreover have "?D = mat (dim_row A - n) (dim_col A - n) (\<lambda>(i, j). A $$ (i + n, j + n))"
          (is "?lhs = ?rhs")
        proof
          show row: "dim_row ?lhs = dim_row ?rhs" and col: "dim_col ?lhs = dim_col ?rhs"
            using Suc(5) by fastforce+
          show "\<And>i j. i < dim_row ?rhs \<Longrightarrow> j < dim_col ?rhs \<Longrightarrow> ?lhs$$(i,j) = ?rhs$$(i,j)"
          proof-
            fix i j assume *: "i < dim_row ?rhs" "j < dim_col ?rhs"
            hence "i = 0 \<and> j = 0" using Suc(5) by auto
            thus "?lhs$$(i,j) = ?rhs$$(i,j)"
              apply (simp add: a_def)
              using col row
              by force
          qed
        qed
        ultimately show ?thesis unfolding split_block_def by metis
      qed
      hence "det A = det A\<^sub>n * det (?D - ?C * A\<^sub>n' * ?B)"
        using schur_formula[of A\<^sub>n ?B ?C ?D A n n A\<^sub>n'] An' Suc(5,6) herm_A\<^sub>n hermitian_is_square
        by (metis carrier_matD(1) carrier_matD(2) lessI)
      moreover have "det (?D - ?C * A\<^sub>n' * ?B) = (a - QF A\<^sub>n' v\<^sub>n)"
      proof-
        have "?C * A\<^sub>n' * ?B = mat 1 1 (\<lambda>_. QF A\<^sub>n' v\<^sub>n)" (is "?lhs = ?rhs")
        proof
          have dim: "?C * A\<^sub>n' * ?B \<in> carrier_mat 1 1" by (simp add: carrier_matI)
          thus "dim_row ?lhs = dim_row ?rhs" "dim_col ?lhs = dim_col ?rhs" by auto
          have "col (A\<^sub>n' * ?B) 0 = A\<^sub>n' *\<^sub>v v\<^sub>n"
            using An' vn
            by (metis mat_vec_as_mat_mat_mult)
          moreover have "row ?C 0 = conjugate v\<^sub>n" using v\<^sub>nc_def w\<^sub>n_def wn_vn_conj by auto
          moreover have "(?C * (A\<^sub>n' * ?B))$$(0,0) = row ?C 0 \<bullet> col (A\<^sub>n' * ?B) 0" by simp
          moreover have "?C * (A\<^sub>n' * ?B) = ?C * A\<^sub>n' * ?B"
            using An'
            by (metis assoc_mult_mat carrier_matI mat_of_cols_carrier(2) mat_of_rows_carrier(3))
          ultimately have "(?C * A\<^sub>n' * ?B)$$(0,0) = (conjugate v\<^sub>n) \<bullet> (A\<^sub>n' *\<^sub>v v\<^sub>n)" by argo
          also have "\<dots> = (A\<^sub>n' *\<^sub>v v\<^sub>n) \<bullet>c v\<^sub>n" 
            using An' vn by (metis conjugate_vec_sprod_comm mult_mat_vec_carrier)
          also have "\<dots> = QF A\<^sub>n' v\<^sub>n" by simp
          finally show "\<And>i j. i < dim_row ?rhs \<Longrightarrow> j < dim_col ?rhs \<Longrightarrow> ?lhs$$(i,j) = ?rhs$$(i,j)"
            by fastforce
        qed
        hence "?D - ?C * A\<^sub>n' * ?B = mat 1 1 (\<lambda>_. a - QF A\<^sub>n' v\<^sub>n)" by fastforce
        thus ?thesis by (simp add: det_single)
      qed
      ultimately show ?thesis by argo
    qed
    moreover have "det A > 0" using Suc.prems sylvester_criterion_positive_det by blast
    moreover have "det A\<^sub>n > 0" using Suc unfolding A\<^sub>n_def sylvester_criterion_def by simp
    ultimately show ?thesis by (simp add: less_complex_def zero_less_mult_iff)
  qed
  have 4: "(cmod b)^2 > 0" if "b \<noteq> 0" using that by force

  have ?case if "b = 0"
  proof-
    have "Re (QF A\<^sub>n (x\<^sub>n + ?c\<^sub>n)) > 0" using that 1 2 by blast
    thus ?thesis unfolding eq by (simp add: that)
  qed
  moreover have ?case if "b \<noteq> 0"
  proof-
    have "(cmod b)^2 * (a - QF A\<^sub>n' v\<^sub>n) > 0"
      using 3 4[OF that] by (simp add: less_le square_nneg_complex)
    moreover have "Re (QF A\<^sub>n (x\<^sub>n + ?c\<^sub>n)) \<ge> 0" using 1 carrier_A\<^sub>n by fastforce
    ultimately show ?thesis unfolding eq by (simp add: less_complex_def)
  qed
  ultimately show ?case by blast
qed

subsection "Reverse Implication"

lemma prod_list_gz:
  fixes l :: "real list"
  assumes "\<forall>x \<in> set l. x > 0"
  shows "prod_list l > 0"
  using assms by (induct l, auto+)

context cmplx_herm_mat
begin

lemma positive_definite_imp_positive_eigenvalues:
  assumes pd: "positive_definite A"
  shows "\<forall>\<mu> \<in> spectrum A. \<mu> > 0"
proof
  have square: "square_mat A" using pd[unfolded positive_definite_def] hermitian_is_square ..

  fix \<mu> assume \<mu>: "\<mu> \<in> spectrum A"
  moreover have "\<mu> > 0"
  proof-
    obtain x where x: "x \<in> carrier_vec (dim_row A) \<and> x \<noteq> 0\<^sub>v (dim_row A) \<and> A *\<^sub>v x = \<mu> \<cdot>\<^sub>v x"
      using \<mu> pd
      by (metis eigenvalue_def eigenvector_def hermitian_square positive_definite_def spectrum_eigenvalues)
    hence "\<mu> * (x \<bullet>c x) > 0"
      using pd x \<mu> square
      unfolding positive_definite_def
      by (metis dim_vec_conjugate quadratic_form_def scalar_prod_smult_left square_mat.simps)
    moreover have "x \<bullet>c x > 0" using conjugate_square_greater_0_vec x by blast
    ultimately show ?thesis by (simp add: less_complex_def zero_less_mult_iff)
  qed
  ultimately show "\<mu> > 0" by (simp add: less_complex_def)
qed

text "Technically, the following direction is not needed for the final result, but is useful later."

lemma positive_eigenvalues_imp_positive_definite:
  assumes pos_spectrum: "\<forall>\<mu> \<in> spectrum A. \<mu> > 0"
  shows "positive_definite A"
proof-
  have ?thesis if "n = 0"
    using A_dim that unfolding positive_definite_def hermitian_def adjoint_def by auto
  moreover have ?thesis if n_nz: "n \<noteq> 0"
  proof-
    have "(\<forall>x\<in>carrier_vec n. x \<noteq> 0\<^sub>v n \<longrightarrow> 0 < QF A x)"
    proof clarify
      fix x :: "complex vec" assume x: "x \<in> carrier_vec n" "x \<noteq> 0\<^sub>v n"
      have "Min (Re ` set eigenvalues) > 0"
      proof-
        have "\<forall>\<mu> \<in> set eigenvalues. \<mu> > 0"
          using A_dim cmplx_herm_mat.eigenvalues pos_spectrum
          by (metis eigenvalues eigvals_of_spectrum spectrum_connect)
        moreover have "set eigenvalues \<subseteq> \<real>"
          using A_herm eigenvalues_real by force
        ultimately have "\<forall>\<mu> \<in> Re ` set eigenvalues. \<mu> > 0" using less_complex_def by fastforce
        moreover have "set eigenvalues \<noteq> {} \<and> finite (set eigenvalues)"
          using cmplx_herm_mat.eigenvalues[unfolded eigvals_of] A_dim n_nz len_eigenvalues by fastforce
        ultimately show ?thesis by auto
      qed
      hence "0 < \<rho> A x" using rayleigh_bdd_below' x by fastforce
      moreover have "(vec_norm x)\<^sup>2 > 0" using x vec_norm_zero by (simp add: inner_prod_vec_norm_pow2)
      ultimately have "\<rho> A x * (vec_norm x)\<^sup>2 > 0" by (simp add: less_eq_complex_def less_le)
      thus "0 < QF A x" using rayleigh_quotient_QF[OF x(2,1)] vec_norm_zero x by auto
    qed
    thus ?thesis unfolding positive_definite_def using A_herm A_dim by blast
  qed
  ultimately show ?thesis by blast
qed

lemma positive_definite_imp_positive_eigenvalues\<^sub>0_Re:
  assumes pd: "positive_definite A"
  shows "\<forall>\<mu> \<in> set (map Re eigenvalues). \<mu> > 0"
proof
  fix \<mu> assume \<mu>: "\<mu> \<in> set (map Re eigenvalues)"
  then obtain \<mu>' where \<mu>': "\<mu>' \<in> set eigenvalues \<and> \<mu> = Re \<mu>'" by auto
  hence "\<mu>' > 0"
    using positive_definite_imp_positive_eigenvalues[OF pd]
    using eigenvalues\<^sub>0_def eigenvalues_set_eq spectrum_def
    by auto
  moreover hence "\<mu>' \<in> \<real>" using complex_is_real_iff_compare0 by fastforce
  ultimately show "\<mu> > 0" by (simp add: \<mu>' less_complex_def)
qed

lemma sylvester_criterion_reverse:
  assumes pd: "positive_definite A"
  shows "sylvester_criterion A"
  unfolding sylvester_criterion_def
proof clarify
  fix k assume k: "k \<le> dim_row A"
  let ?A' = "lps A k"
  have pd: "positive_definite ?A'"
    using A_dim pd leading_principal_submatrix_positive_definite k by auto
  hence det_nz: "det ?A' \<noteq> 0" using positive_definite_det_nz by blast
  have square: "square_mat ?A'" using pd hermitian_is_square positive_definite_def by blast
  have A'_dim: "?A' \<in> carrier_mat k k" using A_dim k leading_principal_submatrix_carrier by auto

  have "prod_list (map Re (eigvals ?A')) > 0"
    using cmplx_herm_mat.positive_definite_imp_positive_eigenvalues\<^sub>0_Re[of _ ?A'] pd prod_list_gz
    using A'_dim cmplx_herm_mat.intro positive_definite_def
    by (smt (verit, best) cmplx_herm_mat.positive_definite_imp_positive_eigenvalues imageE less_complex_def
        list.set_map spectrum_def zero_complex.sel(1))
  moreover have "prod_list (eigvals ?A') = prod_list (map Re (eigvals ?A'))"
  proof-
    have "\<forall>i < (length (eigvals ?A')). (eigvals ?A')!i = (map Re (eigvals ?A'))!i"
    proof safe
      fix i assume *: "i < length (eigvals ?A')"
      hence "(eigvals ?A')!i \<in> Reals"
        using pd A'_dim
        by (metis cmplx_herm_mat.hermitian_eigenvalues_real cmplx_herm_mat_def nth_mem
            positive_definite_def spectrum_def spectrum_eigenvalues)
      thus "(eigvals ?A')!i = (map Re (eigvals ?A'))!i" using * by auto
    qed
    thus ?thesis
      by (metis length_map map_nth_eq_conv of_real_hom.hom_prod_list)
  qed
  ultimately show "0 < det ?A'"
    using det_is_prod_of_eigenvalues[OF square] by (simp add: less_complex_def)
qed

subsection "Theorem Statement"

theorem sylvester_criterion:
  shows "sylvester_criterion A \<longleftrightarrow> positive_definite A"
proof
  show 1: "sylvester_criterion A \<Longrightarrow> positive_definite A"
    using sylvester_criterion_forward
    unfolding positive_definite_def
    using A_herm A_dim sylvester_criterion_forward
    using complex_is_Real_iff hermitian_quadratic_form_real less_complex_def
    by auto
  show 2: "positive_definite A \<Longrightarrow> sylvester_criterion A"
    by (rule sylvester_criterion_reverse)
qed

end

subsection "Theorem Statement (Outside Locale)"

theorem sylvester_criterion:
  fixes A :: "complex mat"
  assumes "hermitian A"
  shows "sylvester_criterion A \<longleftrightarrow> positive_definite A"
  using assms cmplx_herm_mat.sylvester_criterion cmplx_herm_mat.intro hermitian_square by blast

section "Code"

definition rat_of_nat_mat :: "nat mat \<Rightarrow> rat mat" where
  "rat_of_nat_mat A = mat (dim_row A) (dim_col A) (\<lambda>(i,j). rat_of_nat (A$$(i,j)))"

definition rat_of_int_mat :: "int mat \<Rightarrow> rat mat" where
  "rat_of_int_mat A = mat (dim_row A) (dim_col A) (\<lambda>(i,j). rat_of_int (A$$(i,j)))"

context comm_ring_hom
begin

lemma mat_hom_submatrix:
  assumes I: "I \<subseteq> {..<dim_row A}"
  assumes J: "J \<subseteq> {..<dim_col A}"
  shows "submatrix (mat\<^sub>h A) I J = mat\<^sub>h (submatrix A I J)"
  unfolding submatrix_inj[of A "dim_row A" "dim_col A", simplified, OF I J]
  unfolding submatrix_inj[of "(mat\<^sub>h A)" "dim_row A" "dim_col A", simplified, OF I J]
  apply (simp add: submatrix_of_inj_def map_mat_def)
  apply (rule cong_mat[of "card I" "card I" "card J" "card J", simplified])
  using I J
  by (simp add: subset_iff pick_in_set_le)

lemma mat_hom_carrier: "A \<in> carrier_mat m n \<Longrightarrow> mat\<^sub>h A \<in> carrier_mat m n"
  by simp

end

(* TODO: move? *)
lemma of_rat_less_complex: "x < y \<longleftrightarrow> complex_of_rat x < complex_of_rat y"
proof-
  have "complex_of_rat x = (of_real \<circ> of_rat) x" "complex_of_rat y = (of_real \<circ> of_rat) y"
    by (simp_all add: of_rat.rep_eq)
  moreover have "real_of_rat x < real_of_rat y \<longleftrightarrow> x < y" using of_rat_less by blast
  ultimately show ?thesis by (simp add: less_complex_def)
qed

lemma sylvester_criterion_rat:
  assumes square: "A \<in> carrier_mat n n"
  defines [simp]: "(hom\<^sub>H :: rat mat \<Rightarrow> complex mat) \<equiv> of_rat_hom.mat_hom"
  shows "sylvester_criterion A \<longleftrightarrow> sylvester_criterion (hom\<^sub>H A)"
  unfolding sylvester_criterion_def
proof-
  have "\<forall>k \<le> dim_row A. 0 < det (lps A k) \<longleftrightarrow> 0 < det (lps (hom\<^sub>H A) k)"
  proof clarify
    fix k assume k: "k \<le> dim_row A"
    have "det (lps (hom\<^sub>H A) k) = complex_of_rat (det (lps A k))"
      using of_rat_hom.hom_det[of "lps A k", where 'a = complex]
      unfolding hom\<^sub>H_def leading_principal_submatrix_def
      apply (subst of_rat_hom.mat_hom_submatrix[of "{..<k}" A "{..<k}"])
      using k square
      by simp_all
    thus "0 < det (lps A k) \<longleftrightarrow> 0 < det (lps (hom\<^sub>H A) k)"
      using of_rat_less_complex k hom\<^sub>H_def by (metis of_rat_hom.hom_zero)
  qed
  thus "(\<forall>k \<le> dim_row A. 0 < det (lps A k)) = (\<forall>k \<le> dim_row (hom\<^sub>H A). 0 < det (lps (hom\<^sub>H A) k))"
    by simp
qed

lemma rat_subset_real: "\<rat> \<subseteq> (\<real>::complex set)"
  by (metis Im_complex_of_real Rats_cases' complex_is_Real_iff of_real_divide of_real_of_int_eq
      subset_eq)

lemma conjugate_of_rat: "conjugate (of_rat x) = ((of_rat x)::complex)"
proof-
  have "((of_rat x)::complex) \<in> \<real>" using rat_subset_real by fastforce
  moreover have "\<forall>x \<in> \<real>::complex set. conjugate x = x" using Reals_cnj_iff by force
  ultimately show ?thesis by fast
qed

lemma hermitian_rat:
  fixes A :: "rat mat"
  shows "hermitian A \<longleftrightarrow> hermitian ((of_rat_hom.mat_hom A)::complex mat)"
  apply standard
  unfolding hermitian_ij_ji_iff
   apply (simp add: hermitian_ij_ji_iff conjugate_of_rat)
  subgoal using conjugate_of_rat by (metis conjugate_complex_def)
  subgoal by (metis conjugate_of_rat conjugate_rat_def index_map_mat(1,2,3) of_rat_eq_iff square_mat.simps)
  done

definition compute_lps :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  [code]: "compute_lps A k = mat k k (\<lambda>(i,j). A$$(i,j))"

definition compute_sylvester_criterion :: "rat mat \<Rightarrow> bool" where
  [code]: "compute_sylvester_criterion A \<longleftrightarrow> (\<forall>k \<in> {0..dim_row A}. det_field (compute_lps A k) > 0)"

lemma compute_lps_correct:
  assumes A: "A \<in> carrier_mat n n"
  assumes k: "k \<le> n"
  shows "compute_lps A k = lps A k"
  apply (rule eq_matI)
  unfolding compute_lps_def
  subgoal
    using k A
    apply (simp add: submatrix_def)
    by (metis Collect_conj_eq card_lessThan index_mat(1) inf.absorb_iff2 lessThan_def lessThan_subset_iff
        pick_n_le)
  subgoal using k A by (metis carrier_matD(1) dim_row_mat(1) leading_principal_submatrix_carrier)
  subgoal using k A by (metis carrier_matD(2) dim_col_mat(1) leading_principal_submatrix_carrier)
  done

lemma compute_sylvester_criterion_correct:
  fixes A :: "rat mat"
  assumes A: "hermitian A"
  shows "compute_sylvester_criterion A \<longleftrightarrow> sylvester_criterion A"
  unfolding compute_sylvester_criterion_def sylvester_criterion_def
  using compute_lps_correct[OF hermitian_square[OF A]]
  by auto

lemma compute_sylvester_criterion_correct':
  fixes A :: "rat mat"
  assumes A: "hermitian A"
  assumes square: "A \<in> carrier_mat n n"
  shows "compute_sylvester_criterion A \<longleftrightarrow> positive_definite ((of_rat_hom.mat_hom A)::complex mat)"
  apply (subst compute_sylvester_criterion_correct[OF A])
  apply (subst sylvester_criterion_rat[OF square])
  by (rule sylvester_criterion
      [ of "of_rat_hom.mat_hom A",
        unfolded hermitian_rat[of A, symmetric],
        OF A])

definition smallest_eigval_gr :: "rat mat \<Rightarrow> rat \<Rightarrow> bool" where
  [code]: "smallest_eigval_gr A r = (compute_sylvester_criterion (A - (r \<cdot>\<^sub>m 1\<^sub>m (dim_row A))))"

text
  "The function @{term smallest_eigval_gr} checks if the smallest eigenvalue of $A$ is bigger than $r$."

lemma hermitian_minus_I:
  fixes A :: "rat mat"
  assumes A: "hermitian A"
  shows "hermitian (A - r \<cdot>\<^sub>m 1\<^sub>m (dim_row A))"
  unfolding hermitian_def adjoint_def
  apply (rule eq_matI)
  apply simp_all
  using A[unfolded hermitian_def adjoint_def, simplified]
  by (metis index_transpose_mat(1,3) transpose_mat_def)

context comm_ring_hom
begin

lemma mat_hom_add:
  assumes "A \<in> carrier_mat m n"
  assumes "B \<in> carrier_mat m n"
  shows "mat\<^sub>h (A + B) = mat\<^sub>h A + mat\<^sub>h B"
  using assms hom_add by auto

lemma mat_hom_uminus:
  shows "mat\<^sub>h (-A) = - mat\<^sub>h A"
  using hom_uminus by auto

lemma mat_hom_sub:
  assumes "A \<in> carrier_mat m n"
  assumes "B \<in> carrier_mat m n"
  shows "mat\<^sub>h (A - B) = mat\<^sub>h A - mat\<^sub>h B"
  using assms mat_hom_add mat_hom_uminus
  by (smt (verit, ccfv_threshold) add_uminus_minus_mat comm_ring_hom.mat_hom_add
      comm_ring_hom_axioms map_carrier_mat uminus_carrier_mat)

end

lemma smallest_eigval_gr_correct_aux:
  fixes A :: "rat mat"
  assumes A: "hermitian A"
  shows "smallest_eigval_gr A r \<longleftrightarrow> positive_definite ((of_rat_hom.mat_hom (A - r \<cdot>\<^sub>m 1\<^sub>m (dim_row A)))::complex mat)"
  unfolding smallest_eigval_gr_def
  by (rule compute_sylvester_criterion_correct'[OF hermitian_minus_I[OF A]], fastforce)

lemma smallest_eigval_gr_correct:
  fixes A :: "rat mat"
  assumes A: "hermitian A"
  shows "smallest_eigval_gr A r \<longleftrightarrow> (\<forall>\<mu>::complex \<in> spectrum (of_rat_hom.mat_hom A). r < \<mu>)"
proof-
  let ?A' = "A - r \<cdot>\<^sub>m 1\<^sub>m (dim_row A)"
  let ?cA' = "(of_rat_hom.mat_hom ?A')::complex mat"
  let ?cA = "(of_rat_hom.mat_hom A)::complex mat"
  have A'_square: "square_mat ?A'" using hermitian_is_square[OF A] hermitian_minus_I by auto
  have "smallest_eigval_gr A r \<longleftrightarrow> positive_definite ?cA'"
    by (rule smallest_eigval_gr_correct_aux[OF A, of r])
  also have "\<dots> \<longleftrightarrow> (\<forall>\<mu> \<in> spectrum ?cA'. \<mu> > 0)"
    using cmplx_herm_mat.positive_definite_imp_positive_eigenvalues[OF cmplx_herm_mat.intro, of ?cA']
    using cmplx_herm_mat.positive_eigenvalues_imp_positive_definite[OF cmplx_herm_mat.intro, of ?cA']
    using A
    by (meson hermitian_minus_I hermitian_rat hermitian_square)
  also have "\<dots> \<longleftrightarrow> (\<forall>\<mu> \<in> spectrum ?cA. r < \<mu>)"
  proof-
    obtain n where n: "?cA \<in> carrier_mat n n"
      using A hermitian_rat hermitian_square by blast
    have "?cA' = of_rat_hom.mat_hom A - of_rat_hom.mat_hom (r \<cdot>\<^sub>m 1\<^sub>m (dim_row A))"
      using A of_rat_hom.mat_hom_sub[of A "dim_row A" "dim_row A" "r \<cdot>\<^sub>m 1\<^sub>m (dim_row A)"]
      by (metis hermitian_square one_carrier_mat smult_carrier_mat)
    also have "\<dots> = of_rat_hom.mat_hom A - r \<cdot>\<^sub>m of_rat_hom.mat_hom (1\<^sub>m (dim_row A))"
      by fastforce
    finally have "\<mu> \<in> spectrum ?cA \<longleftrightarrow> \<mu> - r \<in> spectrum ?cA'" for \<mu>
      using spectrum_shift[OF n, of r] n by (simp add: of_rat_hom.mat_hom_one)
    thus ?thesis by (metis diff_gt_0_iff_gt add_diff_cancel_right' diff_gt_0_iff_gt)
  qed
  finally show ?thesis .
qed


(*
(* Some tests: *)

abbreviation "n \<equiv> 5"

abbreviation "A \<equiv> mat n n (\<lambda>(i,j). if (2::nat) dvd i + j then 1::rat else 0)"

abbreviation "mat_as_list_list \<equiv> \<lambda>A. map (\<lambda>i. list_of_vec (col A i)) [0..<n]"

value "mat_as_list_list A"

value "mat_as_list_list A = mat_as_list_list A\<^sup>T"

value "smallest_eigval_gr A (-1.5)"
*)


end