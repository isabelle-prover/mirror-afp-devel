theory Sylvester_Criterion
  imports Misc_Matrix_Results

begin

section "Sylvester's Criterion Setup"

definition sylvester_criterion :: "('a::{comm_ring_1,ord}) mat \<Rightarrow> bool" where
  "sylvester_criterion A \<longleftrightarrow> (\<forall>k \<in> {0..dim_row A}.  Determinant.det (lps A k) > 0)"

lemma leading_principle_submatrix_sylvester:
  assumes "A \<in> carrier_mat n n"
  assumes "m \<le> n"
  assumes "sylvester_criterion A"
  shows "sylvester_criterion (lps A m)"
  using nested_leading_principle_submatrices
  by (smt (verit, del_insts) assms atLeastAtMost_iff carrier_matD(1) order.trans leading_principal_submatrix_carrier sylvester_criterion_def)

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

lemma sylvester_criterion_forward:
  fixes A :: "complex mat"
  assumes "A \<in> carrier_mat n n"
  assumes "x \<in> carrier_vec n"
  assumes "hermitian A"
  assumes "sylvester_criterion A"
  assumes "x \<noteq> 0\<^sub>v n"
  shows "Re (QF A x) > 0"
  using assms
proof(induction n arbitrary: A x)
  case 0
  then show ?case by (metis carrier_vecD eq_vecI not_less_zero zero_carrier_vec)
next
  case (Suc n)

  have *: "\<And>k. k \<le> dim_row A \<Longrightarrow> det (leading_principal_submatrix A k) > 0"
    using Suc(5) atLeastAtMost_iff unfolding sylvester_criterion_def by blast

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
    by (metis A\<^sub>n_def Suc.prems(1) le_add2 leading_principal_submatrix_carrier plus_1_eq_Suc)
  have herm_A\<^sub>n: "hermitian A\<^sub>n"
    using principal_submatrix_hermitian[of A "Suc n" "{..n}"] A\<^sub>n_def
    unfolding leading_principal_submatrix_def
    by (metis Suc.prems(1) Suc.prems(3) dual_order.refl le_SucI lessThan_subset_iff principal_submatrix_hermitian)

  have "(col A n) = conjugate (row A n)"
    by (metis Suc.prems(1) Suc.prems(3) adjoint_col carrier_matD(1) hermitian_def lessI)
  hence wn_vn_conj: "w\<^sub>n = v\<^sub>nc"
    by (metis Suc.prems(1) conjugate_vec_first col_carrier_vec conjugate_id le_add2 lessI plus_1_eq_Suc v\<^sub>n_def v\<^sub>nc_def w\<^sub>n_def)

  have "invertible_mat A\<^sub>n"
    by (metis "*" A\<^sub>n_def Suc(2) carrier_A\<^sub>n carrier_matD(1) invertible_det le_add2 less_irrefl plus_1_eq_Suc)
  then obtain A\<^sub>n' where An': "inverts_mat A\<^sub>n' A\<^sub>n \<and> A\<^sub>n' \<in> carrier_mat n n"
    by (metis (no_types, lifting) invertible_mat_def A\<^sub>n_def Suc.prems(1) carrier_matD(1) carrier_matI index_mult_mat(3) index_one_mat(3) inverts_mat_def le_add2 leading_principal_submatrix_carrier plus_1_eq_Suc square_mat.simps)

  have xn: "x\<^sub>n \<in> carrier_vec n" by (simp add: x\<^sub>n_def)
  moreover have An: "A\<^sub>n \<in> carrier_mat n n"
    using leading_principal_submatrix_carrier
    by (metis A\<^sub>n_def Suc.prems(1) Suc_n_not_le_n linorder_linear)
  ultimately have An_xn: "A\<^sub>n *\<^sub>v x\<^sub>n \<in> carrier_vec n" by fastforce
  have vn: "v\<^sub>n \<in> carrier_vec n" by (simp add: v\<^sub>n_def)
  hence b_vn: "b \<cdot>\<^sub>v v\<^sub>n \<in> carrier_vec n" by simp

  have "(A\<^sub>n *\<^sub>v x\<^sub>n + b \<cdot>\<^sub>v v\<^sub>n) \<in> carrier_vec n" using An_xn b_vn by auto

  from herm_A\<^sub>n have hermitian: "hermitian A\<^sub>n'"
    by (metis hermitian_mat_inv An' An inverts_mat_symm)
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
      also have "... = A\<^sub>n *\<^sub>v x\<^sub>n + (b \<cdot>\<^sub>v ((A\<^sub>n * A\<^sub>n') *\<^sub>v v\<^sub>n))"
        by (metis An' assoc_mult_mat_vec carrier_A\<^sub>n mult_mat_vec mult_mat_vec_carrier vn)
      also have "... = (A\<^sub>n *\<^sub>v x\<^sub>n) + b \<cdot>\<^sub>v v\<^sub>n"
        by (metis An' carrier_A\<^sub>n carrier_matD(1) inverts_mat_def inverts_mat_symm one_mult_mat_vec vn)
      finally show ?thesis .
    qed
    hence "?lhs = ((A\<^sub>n *\<^sub>v x\<^sub>n) + b \<cdot>\<^sub>v v\<^sub>n) \<bullet> (x\<^sub>nc + b_conj \<cdot>\<^sub>v (A\<^sub>n'\<^sup>T *\<^sub>v v\<^sub>nc))" by argo
    moreover have "... = E + F"
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
        also have "... = b_conj * ((A\<^sub>n *\<^sub>v x\<^sub>n) \<bullet> (conjugate A\<^sub>n' *\<^sub>v v\<^sub>nc))"
          using A\<^sub>n_inv_conj by presburger
        also have "... = b_conj * (((A\<^sub>n' * A\<^sub>n) *\<^sub>v x\<^sub>n) \<bullet> v\<^sub>nc)"
          by (smt (verit) An An' conj_mat_vec_mult hermitian hermitian_def inner_prod_mult_mat_vec_right v\<^sub>nc_def vn xn)
        also have "... = b_conj * (x\<^sub>n \<bullet> v\<^sub>nc)"
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
        also have "... = (cmod b)^2 * ((A\<^sub>n' *\<^sub>v v\<^sub>n) \<bullet> v\<^sub>nc)"
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
    by (simp add: Suc.prems(1))
  moreover have "x \<in> carrier_vec (Suc n)"
    by (simp add: Suc.prems(2))
  ultimately have Ax: "A *\<^sub>v x = (A\<^sub>n *\<^sub>v x\<^sub>n + b \<cdot>\<^sub>v v\<^sub>n) @\<^sub>v (vec 1 (\<lambda>i. (w\<^sub>n \<bullet> x\<^sub>n) + a * b))"
      (is "_ = _ @\<^sub>v ?Ax_last")
    using mat_vec_prod_leading_principal_submatrix
    unfolding A\<^sub>n_def a_def b_def v\<^sub>n_def w\<^sub>n_def x\<^sub>n_def by blast

  hence "QF A x = ... \<bullet>c x" by force
  also have "... = ((A\<^sub>n *\<^sub>v x\<^sub>n + b \<cdot>\<^sub>v v\<^sub>n) \<bullet>c x\<^sub>n) + ((w\<^sub>n \<bullet> x\<^sub>n) + a * b) * b_conj"
  proof-
    have "x \<in> carrier_vec (dim_vec ((A\<^sub>n *\<^sub>v x\<^sub>n + b \<cdot>\<^sub>v v\<^sub>n) @\<^sub>v ?Ax_last))"
      using Suc.prems(2) vn by force
    moreover have "(A\<^sub>n *\<^sub>v x\<^sub>n + b \<cdot>\<^sub>v v\<^sub>n) \<bullet>c (vec_first x (dim_vec (A\<^sub>n *\<^sub>v x\<^sub>n + b \<cdot>\<^sub>v v\<^sub>n)))
        = (A\<^sub>n *\<^sub>v x\<^sub>n + b \<cdot>\<^sub>v v\<^sub>n) \<bullet>c x\<^sub>n"
      by (simp add: v\<^sub>n_def x\<^sub>n_def)
    moreover have "dim_vec ?Ax_last = 1" by simp
    moreover have "?Ax_last \<bullet>c (vec_last x 1)  = (w\<^sub>n \<bullet> x\<^sub>n + a * b) * b_conj"
    proof-
      have "dim_vec ?Ax_last = 1" by simp
      moreover have "(vec_last x 1)$0 = b"
        by (smt (verit) Suc.prems(2) add.commute add.right_neutral add_diff_cancel_right' b_def carrier_vecD index_vec plus_1_eq_Suc vec_last_def zero_less_one_class.zero_less_one)
      moreover have "?Ax_last$0 = (w\<^sub>n \<bullet> x\<^sub>n + a * b)" by simp
      moreover have "?Ax_last \<bullet>c (vec_last x 1) = ?Ax_last$0 * conjugate ((vec_last x 1)$0)"
        unfolding scalar_prod_def by force
      ultimately show ?thesis using b_conj_def by presburger
    qed
    ultimately show ?thesis by (simp add: inner_prod_append(2))
  qed
  also have "... = QF A\<^sub>n x\<^sub>n + ((b \<cdot>\<^sub>v v\<^sub>n) \<bullet>c x\<^sub>n) + ((w\<^sub>n \<bullet> x\<^sub>n) * b_conj) + (a * b * b_conj)"
    using inner_prod_distrib_right[of x\<^sub>n n "A\<^sub>n *\<^sub>v x\<^sub>n" "b \<cdot>\<^sub>v v\<^sub>n"] b_vn An_xn
    by (simp add: ring_class.ring_distribs(2) xn)
  also have "... = QF A\<^sub>n x\<^sub>n + ((b \<cdot>\<^sub>v v\<^sub>n) \<bullet>c x\<^sub>n) + ((w\<^sub>n \<bullet> x\<^sub>n) * b_conj) + (a * (cmod b)^2)"
    using b_conj_def complex_norm_square by auto
  also have "... = QF A\<^sub>n x\<^sub>n + b * (x\<^sub>nc \<bullet> v\<^sub>n) + b_conj * (x\<^sub>n \<bullet> v\<^sub>nc) + (a * (cmod b)^2)"
    by (metis conjugate_vec_sprod_comm inner_prod_smult_left mult.commute v\<^sub>nc_def vn wn_vn_conj x\<^sub>nc_def xn)
  also have "... = (A\<^sub>n *\<^sub>v (x\<^sub>n + b \<cdot>\<^sub>v (A\<^sub>n' *\<^sub>v v\<^sub>n))) \<bullet> (x\<^sub>nc + b_conj \<cdot>\<^sub>v (A\<^sub>n'\<^sup>T *\<^sub>v v\<^sub>nc))
      - (cmod b)^2 * ((A\<^sub>n' *\<^sub>v v\<^sub>n) \<bullet> v\<^sub>nc) + (a * (cmod b)^2)"
    using ** by fastforce
  also have "... = (A\<^sub>n *\<^sub>v (x\<^sub>n + b \<cdot>\<^sub>v (A\<^sub>n' *\<^sub>v v\<^sub>n))) \<bullet> (x\<^sub>nc + b_conj \<cdot>\<^sub>v (A\<^sub>n'\<^sup>T *\<^sub>v v\<^sub>nc))
      + (cmod b)^2 * (a - QF A\<^sub>n' v\<^sub>n)"
    by (simp add: right_diff_distrib v\<^sub>nc_def)
  also have "... = QF A\<^sub>n (x\<^sub>n + ?c\<^sub>n) + (cmod b)^2 * (a - QF A\<^sub>n' v\<^sub>n)"
  proof-
    have "conjugate (A\<^sub>n' *\<^sub>v v\<^sub>n) = (conjugate A\<^sub>n' *\<^sub>v v\<^sub>nc)"
      by (metis conj_mat_vec_mult adjoint_dim_col carrier_mat_triv carrier_vecD cn dim_mult_mat_vec hermitian hermitian_def index_smult_vec(2) v\<^sub>nc_def vn)
    thus ?thesis
      by (smt (verit, ccfv_threshold) A\<^sub>n_inv_conj b_conj_def cn conjugate_add_vec conjugate_smult_vec x\<^sub>nc_def xn quadratic_form_def)
  qed
  finally have eq: "QF A x = QF A\<^sub>n (x\<^sub>n + ?c\<^sub>n) + (cmod b)^2 * (a - QF A\<^sub>n' v\<^sub>n)" .

  have x\<^sub>n_c\<^sub>n: "(x\<^sub>n + ?c\<^sub>n) \<in> carrier_vec n" using add_carrier_vec cn xn by blast
  have "sylvester_criterion A\<^sub>n"
    using leading_principle_submatrix_sylvester
    by (metis A\<^sub>n_def Suc.prems(1) Suc.prems(4) Suc_n_not_le_n linorder_linear) 
  hence 1: "Re (QF A\<^sub>n (x\<^sub>n + ?c\<^sub>n)) > 0" if "x\<^sub>n + ?c\<^sub>n \<noteq> 0\<^sub>v n"
    using Suc.IH[OF carrier_A\<^sub>n x\<^sub>n_c\<^sub>n herm_A\<^sub>n] that by metis
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
      thus False using Suc.prems(2,4,5) by auto
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
          by (metis A\<^sub>n_def An An_xn Suc(2) carrier_matD(2) carrier_vecD dim_col_mat(1) dim_mult_mat_vec dim_row_mat(1) index_mat(1) le_add2 leading_principal_submatrix_index mat_eq_iff plus_1_eq_Suc)
        moreover have "?B = mat n (dim_col A - n) (\<lambda>(i, j). A $$ (i, j + n))"
          (is "?lhs = ?rhs")
        proof
          show "dim_row ?lhs = dim_row ?rhs" by simp
          show "dim_col ?lhs = dim_col ?rhs" using Suc(2) by force
          show "\<And>i j. i < dim_row ?rhs \<Longrightarrow> j < dim_col ?rhs \<Longrightarrow> ?lhs$$(i,j) = ?rhs$$(i,j)"
          proof-
            fix i j assume *: "i < dim_row ?rhs" "j < dim_col ?rhs"
            hence "j = 0" using Suc(2) by auto
            thus "?lhs$$(i,j) = ?rhs$$(i,j)"
              apply (simp add: v\<^sub>n_def vec_first_def mat_of_cols_def)
              using "*"(1) Suc(2) by auto
          qed
        qed
        moreover have "?C = mat (dim_row A - n) n (\<lambda>(i, j). A $$ (i + n, j))"
          (is "?lhs = ?rhs")
        proof
          show "dim_row ?lhs = dim_row ?rhs" using Suc(2) by force
          show "dim_col ?lhs = dim_col ?rhs" by simp
          show "\<And>i j. i < dim_row ?rhs \<Longrightarrow> j < dim_col ?rhs \<Longrightarrow> ?lhs$$(i,j) = ?rhs$$(i,j)"
          proof-
            fix i j assume *: "i < dim_row ?rhs" "j < dim_col ?rhs"
            hence "i = 0" using Suc(2) by auto
            moreover have "conjugate (vec n (($) (col A n))) = (vec n (($) (row A n)))"
              using Suc(4)
              unfolding hermitian_def adjoint_def
              by (metis v\<^sub>n_def v\<^sub>nc_def vec_first_def w\<^sub>n_def wn_vn_conj)
            ultimately show "?lhs$$(i,j) = ?rhs$$(i,j)"
              apply (simp add: v\<^sub>n_def vec_first_def mat_of_cols_def)
              using "*"(2) Suc(2) by (simp add: mat_of_rows_def)
          qed
        qed
        moreover have "?D = mat (dim_row A - n) (dim_col A - n) (\<lambda>(i, j). A $$ (i + n, j + n))"
          (is "?lhs = ?rhs")
        proof
          show row: "dim_row ?lhs = dim_row ?rhs" using Suc(2) by fastforce
          show col: "dim_col ?lhs = dim_col ?rhs" using Suc(2) by fastforce
          show "\<And>i j. i < dim_row ?rhs \<Longrightarrow> j < dim_col ?rhs \<Longrightarrow> ?lhs$$(i,j) = ?rhs$$(i,j)"
          proof-
            fix i j assume *: "i < dim_row ?rhs" "j < dim_col ?rhs"
            hence "i = 0 \<and> j = 0" using Suc(2) by auto
            thus "?lhs$$(i,j) = ?rhs$$(i,j)"
              apply (simp add: a_def)
              using col row by force
          qed
        qed
        ultimately show ?thesis unfolding split_block_def by metis
      qed
      hence "det A = det A\<^sub>n * det (?D - ?C * A\<^sub>n' * ?B)"
        using schur_formula[of A\<^sub>n ?B ?C ?D A n n A\<^sub>n'] An' Suc(4) herm_A\<^sub>n hermitian_is_square
        by (metis Suc(2) carrier_matD(1) carrier_matD(2) lessI)
      moreover have "det (?D - ?C * A\<^sub>n' * ?B) = (a - QF A\<^sub>n' v\<^sub>n)"
      proof-
        have "?C * A\<^sub>n' * ?B = mat 1 1 (\<lambda>_. QF A\<^sub>n' v\<^sub>n)" (is "?lhs = ?rhs")
        proof
          have dim: "?C * A\<^sub>n' * ?B \<in> carrier_mat 1 1" by (simp add: carrier_matI)
          thus "dim_row ?lhs = dim_row ?rhs" "dim_col ?lhs = dim_col ?rhs" by auto
          have "col (A\<^sub>n' * ?B) 0 = A\<^sub>n' *\<^sub>v v\<^sub>n"
            by (metis An' vn mat_vec_as_mat_mat_mult)
          moreover have "row ?C 0 = conjugate v\<^sub>n" using v\<^sub>nc_def w\<^sub>n_def wn_vn_conj by auto
          moreover have "(?C * (A\<^sub>n' * ?B))$$(0,0) = row ?C 0 \<bullet> col (A\<^sub>n' * ?B) 0" by simp
          moreover have "?C * (A\<^sub>n' * ?B) = ?C * A\<^sub>n' * ?B"
            by (metis An' assoc_mult_mat carrier_matI mat_of_cols_carrier(2) mat_of_rows_carrier(3))
          ultimately have "(?C * A\<^sub>n' * ?B)$$(0,0) = (conjugate v\<^sub>n) \<bullet> (A\<^sub>n' *\<^sub>v v\<^sub>n)" by argo
          also have "... = (A\<^sub>n' *\<^sub>v v\<^sub>n) \<bullet>c v\<^sub>n" 
            by (metis An' conjugate_vec_sprod_comm mult_mat_vec_carrier vn)
          also have "... = QF A\<^sub>n' v\<^sub>n" by simp
          finally show "\<And>i j. i < dim_row ?rhs \<Longrightarrow> j < dim_col ?rhs \<Longrightarrow> ?lhs$$(i,j) = ?rhs$$(i,j)"
            by fastforce
        qed
        hence "?D - ?C * A\<^sub>n' * ?B = mat 1 1 (\<lambda>_. a - QF A\<^sub>n' v\<^sub>n)" by fastforce
        thus ?thesis by (simp add: det_single)
      qed
      ultimately show ?thesis by argo
    qed
    moreover have "det A > 0" using Suc.prems(1,4) sylvester_criterion_positive_det by blast
    moreover have "det A\<^sub>n > 0" using Suc(2,5) unfolding A\<^sub>n_def sylvester_criterion_def by simp
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
  using assms apply (induct l)
   apply fastforce
  by auto

lemma sylvester_criterion_reverse:
  fixes A :: "complex mat"
  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "positive_definite A"
  shows "sylvester_criterion A"
  unfolding sylvester_criterion_def
proof
  fix k assume k: "k \<in> {0..dim_row A}"
  let ?A' = "lps A k"
  have pd: "positive_definite ?A'"
    using assms(1,3) leading_principal_submatrix_positive_definite k by auto
  hence det_nz: "det ?A' \<noteq> 0" using positive_definite_det_nz by blast
  have square: "square_mat ?A'" using pd hermitian_is_square positive_definite_def by blast
  have A'_dim: "?A' \<in> carrier_mat k k"
    using assms(1) k leading_principal_submatrix_carrier by auto

  have "\<forall>e \<in> set (map Re (eigvals ?A')). e > 0"
  proof
    fix e assume "e \<in> set (map Re (eigvals ?A'))"
    then obtain e' where e': "e' \<in> set (eigvals ?A') \<and> e = Re e'"
      by auto
    moreover have "e' > 0"
    proof-
      have "e' \<in> spectrum ?A'"
        by (metis e' Projective_Measurements.spectrum_def Spectral_Radius.spectrum_def hermitian_square mem_Collect_eq pd positive_definite_def spectrum_eigenvalues)
      then obtain x where x: "x \<in> carrier_vec k \<and> x \<noteq> 0\<^sub>v k \<and> ?A' *\<^sub>v x = e' \<cdot>\<^sub>v x"
        unfolding spectrum_def eigenvalue_def eigenvector_def using A'_dim by auto
      hence "e' * (x \<bullet>c x) > 0" using pd A'_dim unfolding positive_definite_def by fastforce
      moreover have "x \<bullet>c x > 0" using conjugate_square_greater_0_vec x by blast
      ultimately show ?thesis by (simp add: less_complex_def zero_less_mult_iff)
    qed
    ultimately show "e > 0" by (simp add: less_complex_def)
  qed
  hence "prod_list (map Re (eigvals ?A')) > 0"
    using prod_list_gz by blast
  moreover have "prod_list (eigvals ?A') = prod_list (map Re (eigvals ?A'))"
  proof-
    have "\<forall>i < (length (eigvals ?A')). (eigvals ?A')!i = (map Re (eigvals ?A'))!i"
    proof safe
      fix i assume *: "i < length (eigvals ?A')"
      hence "(eigvals ?A')!i \<in> Reals"
        by (metis eigenvalue_root_char_poly eigvals_poly_length hermitian_eigenvalues_real hermitian_square linear_poly_root nth_mem pd positive_definite_def)
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
  fixes A :: "complex mat"
  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  shows "sylvester_criterion A \<longleftrightarrow> positive_definite A"
proof
  show 1: "sylvester_criterion A \<Longrightarrow> positive_definite A"
    unfolding positive_definite_def
    using sylvester_criterion_forward[of A n] assms complex_is_Real_iff hermitian_quadratic_form_real less_complex_def
    by simp
  show 2: "positive_definite A \<Longrightarrow> sylvester_criterion A"
    using sylvester_criterion_reverse[OF assms(1,2)] .
qed

end