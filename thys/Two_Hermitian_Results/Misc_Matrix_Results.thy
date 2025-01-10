theory Misc_Matrix_Results
  imports "Commuting_Hermitian.Commuting_Hermitian"
          "BenOr_Kozen_Reif.More_Matrix"
          "Jordan_Normal_Form.Spectral_Radius"
          "Jordan_Normal_Form.DL_Rank_Submatrix"
          "Jordan_Normal_Form.Jordan_Normal_Form_Uniqueness"
          "Jordan_Normal_Form.VS_Connect"
          "QHLProver.Complex_Matrix"
          "Fishers_Inequality.Matrix_Vector_Extras"
          "Complex_Bounded_Operators.Extra_Jordan_Normal_Form"
          "Hermite_Lindemann.Misc_HLW"
begin

(* For some reason, importing Commuting_Hermitian includes a bunch of legacy stuff,
   which forces us to qualify any references to things from the Jordan_Normal_Form theory.
   The following hide_ commands suppress these legacy things so that we don't need
   to qualify things from Jordan_Normal_Form.
*)
hide_type (open) Matrix_Legacy.mat
hide_const (open) Matrix_Legacy.mat
hide_fact (open) Finite_Cartesian_Product.mat_def
hide_const (open) Finite_Cartesian_Product.mat
hide_fact (open) Matrix_Legacy.mat_def
hide_const (open) Finite_Cartesian_Product.row
hide_fact (open) Finite_Cartesian_Product.row_def
hide_const (open) Matrix_Legacy.row
hide_fact (open) Matrix_Legacy.row_def
hide_const (open) Matrix_Legacy.col
hide_fact (open) Matrix_Legacy.col_def
hide_const (open) Determinants.det
hide_fact (open) Determinants.det_def
hide_type (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.vec
hide_fact (open) Finite_Cartesian_Product.vec_def
hide_type (open) Matrix_Legacy.vec
hide_const (open) Matrix_Legacy.vec
hide_fact (open) Matrix_Legacy.vec_def
hide_const (open) Coset.order
hide_fact (open) Coset.order_def
hide_const (open) Linear_Algebra.adjoint
hide_fact (open) Linear_Algebra.adjoint_def
hide_const (open) Finite_Cartesian_Product.transpose
hide_fact (open) Finite_Cartesian_Product.transpose_def
unbundle no_inner_syntax
unbundle no_vec_syntax
hide_const (open) Missing_List.span
hide_const (open)
  dependent
  independent
  real_vector.representation
  real_vector.subspace
  span
  real_vector.extend_basis
  real_vector.dim
hide_const (open) orthogonal
no_notation fps_nth (infixl "$" 75)

section "Determinant, Invertible, and Eigenvalue Lemmas"

definition eigvals_of [simp]:
  "eigvals_of M es \<longleftrightarrow> char_poly M = (\<Prod>a\<leftarrow>es. [:- a, 1:]) \<and> length es = dim_row M"

lemma det_is_prod_of_eigenvalues:
  fixes A :: "complex mat"
  assumes "square_mat A"
  shows "det A = (\<Prod>e \<leftarrow> (eigvals A). e)"
proof-
  define es where "es \<equiv> eigvals A"
  define n where "n \<equiv> dim_row A"
  have 1: "A \<in> carrier_mat n n" using assms n_def by fastforce
  have 2: "char_poly A = (\<Prod>e \<leftarrow> es. [:- e, 1:])"
    unfolding es_def eigvals_def
    by (metis (mono_tags, lifting) "1" eigvals_poly_length someI_ex)
  obtain Q Q' B where *: "similar_mat_wit A B Q Q' \<and> upper_triangular B \<and> diag_mat B = es"
    using schur_decomposition[OF 1 2] by (metis surj_pair)

  then have "det A = det (Q * B * Q')" unfolding similar_mat_wit_def by metis
  also have "... = det Q * det B * det Q'"
    by (smt (verit, ccfv_SIG) "*" "1" det_mult mult_carrier_mat similar_mat_witD2(5) similar_mat_witD2(6) similar_mat_witD2(7))
  also have "... = det Q * det B * 1/(det Q)"
    by (smt (verit, ccfv_threshold) "*" "1" det_mult det_one div_by_0 helper mult_cancel_left1 n_def nonzero_mult_div_cancel_left similar_mat_witD(6) similar_mat_witD(7) similar_mat_witD2(1))
  also have "... = det Q * (\<Prod>e \<leftarrow> diag_mat B. e) * 1/(det Q)"
    by (metis "*" det_upper_triangular list.map_ident similar_mat_witD(5))
  also have "... = (\<Prod>e \<leftarrow> (eigvals A). e)"
    by (metis (no_types, lifting) * es_def "1" Groups.mult_ac(2) class_field.zero_not_one det_mult det_one mult_cancel_left2 nonzero_mult_div_cancel_left similar_mat_witD(6) similar_mat_witD(7) similar_mat_witD2(2))
  finally show ?thesis .
qed

lemma eigvals_of_spectrum:
    "(A::(complex mat)) \<in> carrier_mat n n \<Longrightarrow> eigvals_of A \<alpha> \<Longrightarrow> spectrum A = set \<alpha>"
  unfolding eigvals_of
  using eigenvalue_root_char_poly[of A n]
  by (metis Spectral_Radius.spectrum_def equalityI linear_poly_root mem_Collect_eq root_poly_linear subsetI)

lemma trivial_kernel_imp_nonzero_eigenvalues:
  fixes M :: "'a::{idom,ring_1_no_zero_divisors} mat"
  assumes "square_mat M"
  assumes "mat_kernel M \<subseteq> {0\<^sub>v (dim_row M)}"
  assumes "eigenvalue M e"
  shows "e \<noteq> 0"
  by (metis (no_types, lifting) assms carrier_matI carrier_vecD eigenvalue_def eigenvector_def empty_iff mat_kernelI singleton_iff smult_vec_zero square_mat.simps subset_singletonD)

lemma trivial_kernel_imp_invertible: 
  fixes M :: "complex mat"
  assumes "square_mat M"
  assumes "mat_kernel M \<subseteq> {0\<^sub>v (dim_row M)}"
  shows "invertible_mat M"
  by (metis assms(1) assms(2) carrier_matI det_0_iff_vec_prod_zero_field empty_iff invertible_det mat_kernelI singletonD square_mat.elims(2) subset_singletonD)

lemma trivial_kernel_imp_det_nz:
  fixes M :: "complex mat"
  assumes "square_mat M"
  assumes "mat_kernel M \<subseteq> {0\<^sub>v (dim_row M)}"
  shows "det M \<noteq> 0"
  using trivial_kernel_imp_invertible[OF assms(1) assms(2)]
  using invertible_det assms(1) square_mat.simps
  by blast

lemma similar_mats_eigvals:
  assumes "A \<in> carrier_mat n n"
  assumes "B \<in> carrier_mat n n"
  assumes "similar_mat A B"
  assumes "eigvals_of A es"
  shows "eigvals_of B es"
  using assms unfolding eigvals_of
  by (metis (no_types) char_poly_similar assms(1-3) carrier_matD(1))

lemma scale_eigvals:
  fixes A :: "complex mat"
  assumes "A \<in> carrier_mat n n"
  assumes "B = c \<cdot>\<^sub>m A"
  assumes "eigvals_of A es"
  shows "eigvals_of B (map (\<lambda>x. c * x) es)"
proof-
  obtain A' P Q where A_decomp: "schur_decomposition A es = (A', P, Q)
      \<and> similar_mat_wit A A' P Q
      \<and> upper_triangular A'
      \<and> diag_mat A' = es"
    using assms(3) unfolding eigvals_of by (metis schur_decomposition assms(1) surj_pair)
  define B' where "B' \<equiv> c \<cdot>\<^sub>m A'"

  have B'_dim: "B' \<in> carrier_mat n n"
    by (metis A_decomp B'_def assms(1) similar_mat_witD2(5) smult_carrier_mat)
  have B_decomp: "similar_mat_wit B B' P Q
      \<and> upper_triangular B'"
  proof-
    have "upper_triangular B'"
    proof-
      { fix i j assume *: "j < i" "i < dim_row B'"
        hence "B'$$(i,j) = c * A'$$(i,j)"
          by (metis B'_def B'_dim carrier_matD(1) carrier_matD(2) dual_order.strict_trans1 index_smult_mat(1) index_smult_mat(2) index_smult_mat(3) le_simps(1))
        also have "... = 0" using A_decomp * unfolding upper_triangular_def by (simp add: B'_def)
        finally have "B'$$(i,j) = 0" .
      }
      thus ?thesis by blast
    qed
    moreover have "similar_mat_wit B B' P Q"
    proof-
      have "B = c \<cdot>\<^sub>m (P * A' * Q)" using A_decomp assms(2) similar_mat_witD2(3) by blast
      also have "... = P * (c \<cdot>\<^sub>m A') * Q"
        by (metis A_decomp similar_mat_wit_def similar_mat_wit_smult)
      also have "... = P * B' * Q" using B'_def by argo
      finally have "B = P * B' * Q" .
      thus ?thesis by (smt (verit, best) A_decomp B'_def assms(2) similar_mat_wit_smult)
    qed
    ultimately show ?thesis by blast
  qed

  hence "char_poly B' = (\<Prod>a\<leftarrow>diag_mat B'. [:- a, 1:])"
    using char_poly_upper_triangular B_decomp B'_dim by blast
  moreover have "length (diag_mat B') = dim_row B'"
    by (simp add: diag_mat_length)
  ultimately have "eigvals_of B' (diag_mat B')" using eigvals_of by blast
  moreover have "diag_mat B' = map (\<lambda>x. c * x) es"
    using A_decomp B'_def
    by (metis assms(1) diag_mat_map similar_mat_witD2(5) smult_mat_def)
  ultimately show ?thesis
    using similar_mats_eigvals B_decomp assms(2) assms(3) char_poly_similar similar_mat_def
    by fastforce
qed

lemma neg_mat_eigvals:
  fixes A :: "complex mat"
  assumes "A \<in> carrier_mat n n"
  assumes "eigvals_of A es"
  shows "eigvals_of (-A) (rev (map (\<lambda>x. -x) es))"
proof-
  have "eigvals_of A (rev es)"
    using assms(2)
    unfolding eigvals_of
    by (metis length_rev prod_list.rev rev_map)
  thus ?thesis
    using scale_eigvals[of A n "-A" "-1" "rev es"]
    by (metis assms(1) ext mult_minus1 rev_map uminus_mat)
qed

section "Quadratic Form"

definition quadratic_form :: "'a mat \<Rightarrow> 'a vec \<Rightarrow> 'a::{conjugatable_ring}" where
  "quadratic_form M x \<equiv> inner_prod x (M *\<^sub>v x)"

abbreviation "QF \<equiv> quadratic_form"

lemma hermitian_quadratic_form_real:
  fixes A :: "complex mat"
  fixes v :: "complex vec"
  assumes "A \<in> carrier_mat n n"
  assumes "v \<in> carrier_vec n"
  assumes "hermitian A"
  shows "QF A v \<in> Reals"
proof-
  have "conjugate (QF A v) = inner_prod (A *\<^sub>v v) v"
    by (metis assms(1) assms(2) inner_prod_swap mult_mat_vec_carrier quadratic_form_def)
  also have "... = inner_prod v ((adjoint A) *\<^sub>v v)"
    by (metis adjoint_def_alter assms(1) assms(2) assms(3) hermitian_def)
  also have "... = inner_prod v (A *\<^sub>v v)"
    using assms(3) by (simp add: hermitian_def)
  finally have "conjugate (QF A v) = QF A v"
    by (simp add: quadratic_form_def)
  thus ?thesis by (simp add: Reals_cnj_iff)
qed

declare
  quadratic_form_def[simp]

section "Leading Principal Submatrix Lemmas"

definition leading_principal_submatrix :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  [simp]: "leading_principal_submatrix A k = submatrix A {..<k} {..<k}"

abbreviation "lps \<equiv> leading_principal_submatrix"

lemma leading_principal_submatrix_carrier:
  "m \<ge> n \<Longrightarrow> A \<in> carrier_mat m m \<Longrightarrow> lps A n \<in> carrier_mat n n"
proof-
  assume *: "m \<ge> n" "A \<in> carrier_mat m m"
  let ?B = "lps A n"
  have "(card {i. i < dim_row A \<and> i \<in> {..<n}}) = n"
    by (metis "*"(1) "*"(2) Collect_conj_eq Collect_mem_eq card_lessThan carrier_matD(1) inf.absorb_iff2 lessThan_def lessThan_subset_iff)
  hence "dim_col ?B = n \<and> dim_row ?B = n"
    unfolding leading_principal_submatrix_def submatrix_def
    using "*"(2) by auto
  thus ?thesis by blast
qed

lemma pick_n:
  assumes "i \<le> n"
  shows "pick {..n} i = i"
  using assms
proof(induct i)
  case 0
  then show ?case by force
next
  case (Suc i)
  hence "Suc i \<in> {..n}" by blast
  moreover from Suc have "Suc i > pick {..n} i" by simp
  moreover from Suc have "\<forall>i' < Suc i. \<not> (i'\<in>{..n} \<and> i' > pick {..n} i)"
    using Suc_leD not_less_eq by presburger
  ultimately have "Suc i = (LEAST a. a\<in>{..n} \<and> a > pick {..n} i)"
    by (metis (no_types, lifting) LeastI linorder_not_less not_less_Least order.strict_iff_order)
  thus ?case by (metis DL_Missing_Sublist.pick.simps(2))
qed

lemma pick_n_le:
  assumes "i < n"
  shows "pick {..<n} i = i"
  by (metis assms lessThan_Suc_atMost less_Suc_eq_le not0_implies_Suc not_less_zero pick_n)

lemma leading_principal_submatrix_index:
  assumes "A \<in> carrier_mat n n"
  assumes "k \<le> n"
  assumes "i < k"
  assumes "j < k"
  shows "(lps A k)$$(i,j) = A$$(i,j)"
proof-
  have "\<And>i. i < k \<Longrightarrow> pick {..<k} i = i" by (simp add: pick_n_le)
  moreover have "card {i. i < dim_row A \<and> i \<in> {..<k}} = k"
    by (metis Collect_conj_eq Collect_mem_eq assms(1) assms(2) card_lessThan carrier_matD(1) inf.absorb_iff2 lessThan_def lessThan_subset_iff)
  moreover then have "card {j. j < dim_col A \<and> j \<in> {..<k}} = k" using assms(1) by force
  moreover have "(mat k k (\<lambda>(i, j). A$$(i,j)))$$(i,j) = A$$(i,j)" using assms(3) assms(4) by auto
  ultimately show ?thesis by (simp add: assms(3) assms(4) submatrix_def)
qed

lemma nested_leading_principle_submatrices:
  assumes "A \<in> carrier_mat n n"
  assumes "k\<^sub>1 \<le> k\<^sub>2"
  assumes "k\<^sub>2 \<le> n"
  shows "lps A k\<^sub>1 = lps (lps A k\<^sub>2) k\<^sub>1" (is "?lhs = ?rhs")
proof-
  have "\<And>i j. i < k\<^sub>1 \<Longrightarrow> j < k\<^sub>1 \<Longrightarrow> ?lhs$$(i,j) = ?rhs$$(i,j)"
    by (smt (verit, best) assms dual_order.trans leading_principal_submatrix_carrier leading_principal_submatrix_index order.strict_trans2)
  moreover have "?lhs \<in> carrier_mat k\<^sub>1 k\<^sub>1"
    by (meson assms leading_principal_submatrix_carrier order_trans)
  moreover have "?rhs \<in> carrier_mat k\<^sub>1 k\<^sub>1"
    by (meson assms leading_principal_submatrix_carrier)
  ultimately show ?thesis by auto
qed

section "Submatrix Lemmas"

lemma submatrix_as_matrix_prod:
  fixes A :: "complex mat"
  assumes "A \<in> carrier_mat n n"
  assumes "I \<subseteq> {..<n}"
  assumes "I \<noteq> {}"
  defines "m \<equiv> card I"
  defines "B \<equiv> submatrix A I I"
  defines "u_cols_inds \<equiv> map (pick I) [0..<m]"
  defines "u_cols \<equiv> map ((!) (unit_vecs n)) u_cols_inds"
  defines "(Inm::complex mat) \<equiv> mat_of_cols n u_cols"
  defines "(Inm'::complex mat) \<equiv> Inm\<^sup>H"
  shows "B = Inm' * A * Inm"
    "Inm' * Inm = 1\<^sub>m m"
    "Inm \<in> carrier_mat n m"
    "inj_on ((*\<^sub>v) Inm) (carrier_vec m)"
proof-
  have u_cols_length: "length u_cols = m" by (simp add: assms(7) u_cols_inds_def)
  thus Inm_carr: "Inm \<in> carrier_mat n m" unfolding Inm_def mat_of_cols_def by fastforce
  have Inm'_carr: "Inm' \<in> carrier_mat m n" using Inm_carr by (simp add: assms(9))

  let ?rhs = "Inm' * A * Inm"

  have dim_A: "dim_row A = n \<and> dim_col A = n" using assms(1) by simp
  hence I: "{i. i < dim_row A \<and> i \<in> I} = I \<and> {i. i < dim_col A \<and> i \<in> I} = I" using assms(2) by auto
  hence B_carr: "B \<in> carrier_mat m m"
    using dim_submatrix[of A I I] unfolding m_def B_def by auto

  have m_leq_n: "m \<le> n"
    using assms(2,4) atLeast0LessThan subset_eq_atLeast0_lessThan_card by presburger

  have "\<And>i. i < m \<Longrightarrow> u_cols!i = unit_vec n (pick I i)"
    unfolding u_cols_def u_cols_inds_def unit_vecs_def
    by (smt (verit, ccfv_SIG) arithmetic_simps(49) assms(2,4) atLeast_upt diff_zero length_map length_upt map_eq_conv map_nth nth_map nth_map_upt pick_in_set_le subsetD)
  hence col_Inm_i: "\<And>i. i < m \<Longrightarrow> col Inm i = unit_vec n (pick I i)"
    by (simp add: assms(8) u_cols_length)

  have Inm'_is_trans: "Inm' = Inm\<^sup>T"
  proof-
    have "\<And>i j. i < n \<and> j < m \<Longrightarrow> Inm$$(i,j) \<in> \<real>"
    proof-
      fix i j assume *: "i < n \<and> j < m"
      have "Inm$$(i,j) = (col Inm j)$i" using * Inm_carr by auto
      also have "... = (unit_vec n (pick I j))$i" using col_Inm_i * by presburger
      also have "... = 0 \<or> ... = 1" unfolding unit_vec_def using * by auto
      finally show "Inm$$(i,j) \<in> \<real>" by fastforce
    qed
    hence "\<And>i j. i < n \<and> j < m \<Longrightarrow> Inm\<^sup>T$$(j,i) \<in> \<real>" using Inm_carr by auto
    hence "\<And>i j. i < n \<and> j < m \<Longrightarrow> conjugate (Inm\<^sup>T$$(j,i)) = Inm\<^sup>T$$(j,i)"
      by (simp add: Reals_cnj_iff)
    moreover have "\<And>i j. i < n \<and> j < m \<Longrightarrow> (conjugate Inm\<^sup>T)$$(j,i) = conjugate (Inm\<^sup>T$$(j,i))"
      using Inm_carr by auto
    ultimately show ?thesis using Inm_carr assms(9) by auto
  qed

  have "Inm' * A * Inm \<in> carrier_mat m m" using Inm_carr Inm'_carr by fastforce
  moreover have "\<And>i j. i < m \<and> j < m \<Longrightarrow> B$$(i,j) = ?rhs$$(i,j)"
  proof-
    fix i j assume *: "i < m \<and> j < m"
    hence 1: "B$$(i,j) = A$$(pick I i, pick I j)" unfolding B_def submatrix_def using I m_def by auto

    have "col (A * Inm) j = A *\<^sub>v (col Inm j)" using * Inm_carr by auto
    also have "... = A *\<^sub>v unit_vec n (pick I j)" using col_Inm_i * by presburger
    also have "... = col A (pick I j)"
      by (metis "*" assms(1,2,4) basic_trans_rules(31) lessThan_iff mat_unit_vec_col pick_in_set_le)
    finally have "col (A * Inm) j = col A (pick I j)" .
    moreover have "(Inm' * (A * Inm))$$(i,j) = (row Inm' i) \<bullet> (col (A * Inm) j)"
      using * Inm'_carr Inm_carr by auto
    ultimately have "?rhs$$(i,j) = (row Inm' i) \<bullet> col A (pick I j)"
      using Inm'_carr Inm_carr assms(1) by fastforce
    also have "... = (col Inm i) \<bullet> col A (pick I j)"
      using Inm'_is_trans * Inm_carr by auto
    also have "... = (unit_vec n (pick I i)) \<bullet> col A (pick I j)"
      using * col_Inm_i by presburger
    also have "... = (col A (pick I j))$(pick I i)"
      by (metis "*" dim_A assms(2) basic_trans_rules(31) col_dim lessThan_iff m_def pick_in_set_le scalar_prod_left_unit)
    also have "... = A$$(pick I i, pick I j)" using * I m_def pick_le by auto
    finally show "B$$(i,j) = ?rhs$$(i,j)" using 1 by presburger
  qed
  ultimately show "B = Inm' * A * Inm" by (metis B_carr carrier_matD(1) carrier_matD(2) eq_matI)

  show "Inm' * Inm = 1\<^sub>m m"
  proof
    show "dim_row (Inm' * Inm) = dim_row (1\<^sub>m m)" using Inm'_carr by auto
    show "dim_col (Inm' * Inm) = dim_col (1\<^sub>m m)" using Inm_carr by auto
    fix i j
    assume "i < dim_row (1\<^sub>m m)"
    hence i: "i < m" by simp
    assume "j < dim_col (1\<^sub>m m)"
    hence j: "j < m" by simp

    have "(Inm' * Inm)$$(i,j) = (row Inm' i) \<bullet> (col Inm j)"
      by (metis Inm'_carr Inm_carr j carrier_matD(1) carrier_matD(2) i index_mult_mat(1))
    also have "... = (col Inm i) \<bullet> (col Inm j)" using Inm'_is_trans Inm_carr i by auto
    also have "... = unit_vec n (pick I i) \<bullet> unit_vec n (pick I j)" using col_Inm_i i j by presburger
    also have "... = (if i = j then 1 else 0)"
      by (metis (no_types) I assms(1) assms(4) card_pick_le carrier_matD(2) i index_unit_vec(1) j pick_le scalar_prod_right_unit)
    also have "... = 1\<^sub>m m $$ (i,j)" by (simp add: i j)
    finally show "(Inm' * Inm)$$(i,j) = 1\<^sub>m m $$ (i,j)" .
  qed
  thus "inj_on ((*\<^sub>v) Inm) (carrier_vec m)"
    by (smt (verit, best) Inm'_carr Inm_carr assoc_mult_mat_vec inj_onCI one_mult_mat_vec)
qed

lemma submatrix_as_matrix_prod_obt:
  fixes A :: "complex mat"
  assumes "A \<in> carrier_mat n n"
  assumes "I \<subseteq> {..<n}"
  assumes "I \<noteq> {}"
  defines "m \<equiv> card I"
  defines "B \<equiv> submatrix A I I"
  obtains Inm where "B = Inm\<^sup>H * A * Inm"
    "Inm\<^sup>H * Inm = 1\<^sub>m m"
    "Inm \<in> carrier_mat n m"
    "inj_on ((*\<^sub>v) Inm) (carrier_vec m)"
  using submatrix_as_matrix_prod assms by presburger

section "Hermitian and Conjugate Lemmas"

lemma hermitian_is_square: "hermitian A \<Longrightarrow> square_mat A"
  by (metis adjoint_dim_col hermitian_def square_mat.simps)

lemma hermitian_eigenvalues_real:
  assumes "(A::(complex mat)) \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "eigenvalue A e"
  shows "e \<in> Reals"
  using cpx_sq_mat.hermitian_spectrum_real[OF _ assms(1,2), of n n e]
  by (metis Projective_Measurements.spectrum_def assms(1,3) cpx_sq_mat_axioms.intro cpx_sq_mat_def eigenvalue_imp_nonzero_dim eigenvalue_root_char_poly eigvals_poly_length fixed_carrier_mat.intro root_poly_linear)

lemma hermitian_spectrum_real:
    "(A::(complex mat)) \<in> carrier_mat n n \<Longrightarrow> hermitian A \<Longrightarrow> spectrum A \<subseteq> Reals"
  by (simp add: Spectral_Radius.spectrum_def hermitian_eigenvalues_real unfold_simps(2))

lemma leading_principal_submatrix_hermitian:
  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "k \<le> n"
  shows "hermitian (lps A k)" (is "hermitian ?A'")
proof-
  have "\<And>i j. i < dim_row ?A' \<Longrightarrow> j < dim_col ?A' \<Longrightarrow> ?A'$$(i,j) = conjugate (?A'$$(j,i))"
    by (metis (no_types, lifting) adjoint_eval assms carrier_matD(1) carrier_matD(2) dual_order.strict_trans1 hermitian_def leading_principal_submatrix_carrier leading_principal_submatrix_index)
  thus ?thesis
    by (metis (no_types, lifting) adjoint_dim_col adjoint_dim_row adjoint_eval assms(1) assms(3) carrier_matD(1) carrier_matD(2) eq_matI hermitian_def leading_principal_submatrix_carrier)
qed

lemma conjugate_mat_dist:
  fixes A B :: "'a::conjugatable_ring mat"
  assumes "A \<in> carrier_mat m n"
  assumes "B \<in> carrier_mat n p"
  shows "(conjugate A) * (conjugate B) = conjugate (A * B)"
  by (smt (z3) assms(1) assms(2) carrier_matD(1) carrier_matD(2) col_conjugate conjugate_scalar_prod dim_col dim_col_conjugate dim_row_conjugate eq_matI index_mult_mat(1) index_mult_mat(2) index_mult_mat(3) index_row(2) mat_index_conjugate row_conjugate)

lemma conjugate_mat_inv:
  fixes A :: "'a::{conjugatable_ring,semiring_1} mat"
  assumes "A \<in> carrier_mat n n"
  assumes "A' \<in> carrier_mat n n"
  assumes "inverts_mat A A'"
  shows "inverts_mat (conjugate A) (conjugate A')"
proof-
  have "(conjugate A) * (conjugate A') = conjugate (A * A')"
    using conjugate_mat_dist assms(1) assms(2) by blast
  also have "... = conjugate (1\<^sub>m n)"
    by (metis assms(1) assms(3) carrier_matD(1) inverts_mat_def)
  also have "... = 1\<^sub>m n"
    by (metis (no_types, lifting) carrier_matI conjugate_id conjugate_mat_dist dim_col_conjugate dim_row_conjugate index_one_mat(2) index_one_mat(3) left_mult_one_mat' right_mult_one_mat')
  finally show ?thesis
    by (metis index_mult_mat(2) index_one_mat(2) inverts_mat_def)
qed

lemma hermitian_mat_inv:
  assumes "A \<in> carrier_mat n n"
  assumes "A' \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "inverts_mat A A'"
  shows "hermitian A'"
proof-
  have "inverts_mat A\<^sup>T A'\<^sup>T"
    by (metis assms(1) assms(2) assms(4) carrier_matD(1) carrier_matD(2) index_transpose_mat(2) inverts_mat_def inverts_mat_symm transpose_mult transpose_one)
  hence "inverts_mat (conjugate A\<^sup>T) (conjugate A'\<^sup>T)"
    by (metis assms(1) assms(2) conjugate_mat_inv transpose_carrier_mat)
  thus ?thesis
    by (smt (verit, ccfv_SIG) adjoint_dim adjoint_dim_row adjoint_mult assms(1) assms(2) assms(3) assms(4) assoc_mult_mat carrier_matD(2) hermitian_def hermitian_one inverts_mat_def inverts_mat_symm right_mult_one_mat')
qed

lemma hermitian_ij_ji:
  "hermitian A
    \<longleftrightarrow> square_mat A \<and> (\<forall>i j. i < dim_row A \<and> j < dim_row A \<longrightarrow> A$$(i,j) = conjugate (A$$(j,i)))"
  by (metis (no_types, lifting) adjoint_dim_col adjoint_dim_row adjoint_eval hermitian_def mat_eq_iff square_mat.simps)

lemma negative_hermitian:
  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  shows "hermitian (-A)"
  by (metis assms hermitian_minus left_add_zero_mat minus_add_uminus_mat uminus_carrier_iff_mat zero_carrier_mat zero_hermitian)

lemma principal_submatrix_hermitian:
  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "I \<subseteq> {..<n}"
  shows "hermitian (submatrix A I I)" (is "hermitian ?B")
proof-
  have "square_mat ?B"
    by (metis (full_types) assms(1) carrier_matD(1) carrier_matD(2) dim_submatrix(1) dim_submatrix(2) square_mat.elims(1))
  moreover {
    fix i j assume *: "i < dim_row ?B \<and> j < dim_row ?B"
    then obtain i' j' where "?B$$(i,j) = A$$(i',j') \<and> i' = pick I i \<and> j' = pick I j"
      unfolding submatrix_def using assms(1) pick_le by auto
    moreover then have "?B$$(j,i) = A$$(j',i')"
      unfolding submatrix_def
      by (metis (no_types, lifting) Collect_cong * assms(1) carrier_matD(1) carrier_matD(2) case_prod_conv dim_submatrix(1) index_mat(1))
    ultimately have "?B$$(i,j) = conjugate (?B$$(j,i))"
      by (metis "*" assms(2) dim_submatrix(1) hermitian_ij_ji pick_le)
  }
  ultimately show ?thesis by (metis hermitian_ij_ji)
qed

lemma conjugate_dist_mult_mat:
  fixes A :: "'a::conjugatable_ring mat"
  assumes "A \<in> carrier_mat m n" "B \<in> carrier_mat n p"
  shows "conjugate (A * B) = conjugate A * conjugate B"
    (is "?lhs = ?rhs")
proof-
  have "\<And>i j. i < m \<Longrightarrow> j < p \<Longrightarrow> ?lhs$$(i,j) = ?rhs$$(i,j)"
    by (smt (verit, del_insts) assms carrier_matD(1) carrier_matD(2) col_conjugate conjugate_scalar_prod dim_col dim_col_conjugate dim_row_conjugate index_mult_mat(1) index_mult_mat(2) index_mult_mat(3) index_row(2) mat_index_conjugate row_conjugate)  
  moreover have "?lhs \<in> carrier_mat m p" using assms by auto
  ultimately show ?thesis using assms carrier_matD(2) by auto
qed

lemma conjugate_dist_add_mat:
  fixes A :: "'a::conjugatable_ring mat"
  assumes "A \<in> carrier_mat m n" "B \<in> carrier_mat m n"
  shows "conjugate (A + B) = conjugate A + conjugate B"
    (is "?lhs = ?rhs")
proof-
  have "\<And>i j. i < m \<Longrightarrow> j < n \<Longrightarrow> ?lhs$$(i,j) = ?rhs$$(i,j)"
    using assms assms conjugate_dist_add by fastforce
  moreover have "?lhs \<in> carrier_mat m n" using assms by auto
  ultimately show ?thesis using assms carrier_matD(2) by auto
qed

lemma mat_row_conj:
  assumes "A \<in> carrier_mat m n"
  assumes "i < m"
  shows "conjugate (row A i) = row (conjugate A) i"
  using assms
  unfolding conjugate_mat_def
  by auto

lemma conj_mat_vec_mult:
  fixes A :: "'a::{conjugate,conjugatable_ring} mat"
  fixes v :: "'a vec"
  assumes "A \<in> carrier_mat n n"
  assumes "v \<in> carrier_vec n"
  shows "conjugate (A *\<^sub>v v) = (conjugate A) *\<^sub>v (conjugate v)"
    (is "?lhs = ?rhs")
proof-                            
  have "\<And>i. i < n \<Longrightarrow> ?lhs$i = ?rhs$i"
    by (metis assms carrier_matD(1) conjugate_sprod_vec dim_mult_mat_vec dim_row_conjugate index_mult_mat_vec mat_row_conj row_carrier_vec vec_index_conjugate)
  moreover have "?lhs \<in> carrier_vec n" using assms by force
  ultimately show ?thesis using assms(1) by auto
qed

lemma hermitian_row_col:
  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "i < n"
  shows "row A i = conjugate (col A i)"
  by (metis adjoint_row assms carrier_matD(2) hermitian_def)

lemma hermitian_real_diag_decomp_eigvals:
  fixes A :: "complex mat"
  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "eigvals_of A es"
  obtains B U where
      "real_diag_decomp A B U"
      "diag_mat B = es"
      "set es \<subseteq> Reals"
      "B \<in> carrier_mat n n"
      "U \<in> carrier_mat n n"
proof-
  (* Yoinked from the existing proof of
    hermitian_real_diag_decomp in Spectral_Theory_Complements.hermitian_real_diag_decomp *)
  have es: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> es. [:- e, 1:])" 
    using assms eigvals_poly_length by auto
  obtain B U Q where us: "unitary_schur_decomposition A es = (B,U,Q)" 
    by (cases "unitary_schur_decomposition A es")
  hence *: "similar_mat_wit A B U (adjoint U) \<and> diagonal_mat B
      \<and> diag_mat B = es \<and> unitary U \<and> (\<forall>i < n. B$$(i, i) \<in> Reals)" 
    using hermitian_eigenvalue_real assms es by auto
  moreover then have "dim_row B = n" using assms similar_mat_wit_dim_row[of A] by auto
  ultimately have 1: "real_diag_decomp A B U" using unitary_diagI[of A] 
    unfolding real_diag_decomp_def by simp

  from * have 2: "diag_mat B = es" by blast
  from * have 3: "set es \<subseteq> Reals" by (metis \<open>dim_row B = n\<close> diag_elems_real diag_elems_set_diag_mat)
  from * have 4: "B \<in> carrier_mat n n" by (meson assms(1) similar_mat_witD2(5))
  from * have 5: "U \<in> carrier_mat n n" by (meson assms(1) similar_mat_witD2(6))

  from that show ?thesis using 1 2 3 4 5 by blast
qed

lemma conjugate_vec_first:
  assumes "v \<in> carrier_vec n"
  assumes "i \<le> n"
  shows "conjugate (vec_first v i) = vec_first (conjugate v) i"
  by (smt (verit, ccfv_SIG) assms carrier_vecD dim_vec_conjugate dim_vec_first eq_vecI index_vec le_less less_trans vec_first_def vec_index_conjugate)

lemma conjugate_vec_last: "i \<le> dim_vec v \<Longrightarrow> conjugate (vec_last v i) = vec_last (conjugate v) i"
  unfolding vec_last_def by auto

lemma adjoint_is_conjugate_transpose: "A\<^sup>H = adjoint A" 
  by (simp add: adjoint_def transpose_def cong_mat conjugate_mat_def)

lemma cscalar_prod_symm_conj:
  "dim_vec (x::('a::{comm_semiring_0,conjugatable_ring} vec)) = dim_vec (y::'a vec)
    \<Longrightarrow> x \<bullet>c y = conjugate (y \<bullet>c x)"
  by (simp add: conjugate_scalar_prod scalar_prod_comm)

section "Block Matrix Lemmas"

lemma block_mat_vec_mult:
  fixes x
  assumes "A \<in> carrier_mat nr1 nc1"
  assumes "B \<in> carrier_mat nr1 nc2"
  assumes "C \<in> carrier_mat nr2 nc1"
  assumes "D \<in> carrier_mat nr2 nc2"
  assumes "M = four_block_mat A B C D"
  assumes "x \<in> carrier_vec (nc1 + nc2)"
  defines "x\<^sub>1 \<equiv> vec_first x nc1"
  defines "x\<^sub>2 \<equiv> vec_last x nc2"
  shows "M *\<^sub>v x = (A *\<^sub>v x\<^sub>1 + B *\<^sub>v x\<^sub>2) @\<^sub>v (C *\<^sub>v x\<^sub>1 + D *\<^sub>v x\<^sub>2)"
  by (smt (verit, ccfv_threshold) assms four_block_mat_mult_vec vec_first_carrier vec_first_last_append vec_last_carrier)

lemma mat_vec_prod_leading_principal_submatrix:
  fixes A :: "('a :: comm_ring) mat"
  assumes "A \<in> carrier_mat (Suc n) (Suc n)"
  assumes "x \<in> carrier_vec (Suc n)"
  defines "A\<^sub>n \<equiv> lps A n"
  defines "v\<^sub>n \<equiv> vec_first (col A n) n"
  defines "w\<^sub>n \<equiv> vec_first (row A n) n"
  defines "a \<equiv> A $$ (n, n)"
  defines "x\<^sub>n \<equiv> vec_first x n"
  defines "b \<equiv> x$n"
  shows "A *\<^sub>v x = (A\<^sub>n *\<^sub>v x\<^sub>n + b \<cdot>\<^sub>v v\<^sub>n) @\<^sub>v (vec 1 (\<lambda>i. (w\<^sub>n \<bullet> x\<^sub>n) + a * b))" (is "?lhs = ?rhs")
proof
  have dim_x\<^sub>n: "dim_vec x\<^sub>n = n" by (simp add: assms(7))
  have dim_w\<^sub>n: "dim_vec w\<^sub>n = n" by (simp add: assms(5))
  have dim_row_A\<^sub>n: "dim_row A\<^sub>n = n"
    by (metis assms(1) assms(3) carrier_matD(1) le_add2 leading_principal_submatrix_carrier plus_1_eq_Suc)
  have dim_col_A\<^sub>n: "dim_col A\<^sub>n = n"
    by (metis assms(1) assms(3) carrier_matD(2) le_add2 leading_principal_submatrix_carrier plus_1_eq_Suc)


  show dims: "dim_vec ?lhs = dim_vec ?rhs" using assms(1) v\<^sub>n_def by auto
  show "\<And>i. i < dim_vec ?rhs \<Longrightarrow> ?lhs$i = ?rhs$i"
  proof-
    fix i assume *: "i < dim_vec ?rhs"
    hence i: "i < Suc n" using dims assms(1) by auto
    hence dot: "?lhs$i = row A i \<bullet> x" using * dims by fastforce
    have row_j: "\<And>j. j < Suc n \<Longrightarrow> (row A i)$j = A$$(i,j)" using assms(1) i by force

    show "?lhs$i = ?rhs$i"
    proof(cases "i < n")
      case True
      have A\<^sub>n: "\<And>j. j < n \<Longrightarrow> A$$(i,j) = A\<^sub>n$$(i,j)"
        by (metis True assms(1) assms(3) le_add2 leading_principal_submatrix_index plus_1_eq_Suc)
      have A\<^sub>n_row: "\<And>j. j < n \<Longrightarrow> A\<^sub>n$$(i,j) = (row A\<^sub>n i)$j"
        by (metis True assms(1) assms(3) carrier_matD(1) carrier_matD(2) index_row(1) le_add2 leading_principal_submatrix_carrier plus_1_eq_Suc)
      have "?lhs$i = (A\<^sub>n *\<^sub>v x\<^sub>n + b \<cdot>\<^sub>v v\<^sub>n)$i"
      proof-
        have "?lhs$i = (\<Sum>j<Suc n. A$$(i,j) * x$j)"
          unfolding dot scalar_prod_def using row_j assms(2) atLeast0LessThan by force
        moreover have "(\<Sum>j<n. A$$(i,j) * x$j) = (\<Sum>j<n. A\<^sub>n$$(i,j) * x\<^sub>n$j)"
          by (smt (verit) A\<^sub>n assms(7) index_vec lessThan_iff sum.cong vec_first_def)
        moreover have "(\<Sum>j<n. A\<^sub>n$$(i,j) * x\<^sub>n$j) = (A\<^sub>n *\<^sub>v x\<^sub>n)$i"
        proof-
          have "(A\<^sub>n *\<^sub>v x\<^sub>n)$i = (row A\<^sub>n i) \<bullet> x\<^sub>n"
            by (metis True assms(1) assms(3) carrier_matD(1) index_mult_mat_vec le_add2 leading_principal_submatrix_carrier plus_1_eq_Suc)
          moreover have "\<And>j. j < n \<Longrightarrow> A\<^sub>n$$(i,j) * x\<^sub>n$j = (row A\<^sub>n i)$j * x\<^sub>n$j"
            using A\<^sub>n_row by presburger
          ultimately show ?thesis
            unfolding scalar_prod_def using atLeast0LessThan dim_x\<^sub>n by fastforce
        qed
        moreover have "(A$$(i,n) * x$n) = (b \<cdot>\<^sub>v v\<^sub>n)$i"
        proof-
          have "x$n = b" unfolding b_def by blast
          moreover have "A$$(i,n) = v\<^sub>n$i"
            using assms(1) i by (simp add: True vec_first_def v\<^sub>n_def)
          moreover have "(b \<cdot>\<^sub>v v\<^sub>n)$i = b * (v\<^sub>n$i)" by (simp add: True v\<^sub>n_def)
          ultimately show ?thesis by (simp add: mult.commute)
        qed
        ultimately show ?thesis by (simp add: True assms(4))
      qed
      thus ?thesis by (simp add: True i v\<^sub>n_def)
    next
      case False
      hence *: "i = n" using i by linarith
      hence "?lhs$i = (row A n) \<bullet> x" using dot by blast
      also have "... = w\<^sub>n \<bullet> x\<^sub>n + a * b"
      proof-
        have "row A n = w\<^sub>n @\<^sub>v vec_last (row A n) 1"
          by (metis "*" w\<^sub>n_def assms(1) i row_carrier_vec semiring_norm(174) vec_first_last_append)
        moreover have "(vec_last (row A n) 1)$0 = (row A n)$n"
          by (metis "*" False assms(1) calculation carrier_matD(2) dim_w\<^sub>n gr0I i index_append_vec(1) index_append_vec(2) index_row(2) zero_less_diff)
        ultimately have "row A n = w\<^sub>n @\<^sub>v (vec 1 (\<lambda>_. A$$(n,n)))"
          by (smt (verit, best) "*" One_nat_def carrier_vecD dim_vec eq_vecI i index_vec less_Suc0 row_j vec_last_carrier)
        moreover have "x = x\<^sub>n @\<^sub>v (vec 1 (\<lambda>_. b))"
        proof
          show *: "dim_vec x = dim_vec (x\<^sub>n @\<^sub>v (vec 1 (\<lambda>_. b)))" by (simp add: assms(2) dim_x\<^sub>n)
          have "\<And>i. i < Suc n \<Longrightarrow> x$i = (x\<^sub>n @\<^sub>v (vec 1 (\<lambda>_. b)))$i"
          proof-
            fix i assume "i < Suc n"
            show "x$i = (x\<^sub>n @\<^sub>v (vec 1 (\<lambda>_. b)))$i"
              apply (cases "i = n")
               apply (simp add: append_vec_def assms(8) dim_x\<^sub>n)
              apply (simp add: append_vec_def)
              by (smt (verit, best) \<open>i < Suc n\<close> dim_x\<^sub>n index_vec less_antisym vec_first_def x\<^sub>n_def)
          qed
          thus "\<And>i. i < dim_vec (x\<^sub>n @\<^sub>v vec 1 (\<lambda>_. b)) \<Longrightarrow> x $ i = (x\<^sub>n @\<^sub>v vec 1 (\<lambda>_. b)) $ i"
            by (metis * assms(2) carrier_vecD)
        qed
        ultimately have "(row A n) \<bullet> x = (w\<^sub>n \<bullet> x\<^sub>n) + ((vec 1 (\<lambda>_. A$$(n,n))) \<bullet> (vec 1 (\<lambda>_. b)))"
          by (metis assms(5) assms(7) scalar_prod_append vec_carrier vec_first_carrier)
        moreover have "((vec 1 (\<lambda>_. A$$(n,n))) \<bullet> (vec 1 (\<lambda>_. b))) = a * b"
          by (simp add: a_def b_def scalar_prod_def)
        ultimately show ?thesis by argo
      qed
      finally show ?thesis by (simp add: * v\<^sub>n_def)
    qed
  qed
qed

lemma vec_first_index: "n \<le> dim_vec v \<Longrightarrow> i < n \<Longrightarrow> v$i = (vec_first v n)$i"
  unfolding vec_first_def by simp

lemma vec_last_index:
    "n \<le> dim_vec v \<Longrightarrow> i \<in> {dim_vec v - m..<m} \<Longrightarrow> v$i = (vec_last v m)$(i - (dim_vec v - m))"
  unfolding vec_last_def by auto

lemma inner_prod_append:
  assumes "x \<in> carrier_vec (dim_vec (u @\<^sub>v v))"
  shows "x \<bullet>c (u @\<^sub>v v) = (vec_first x (dim_vec u)) \<bullet>c u + (vec_last x (dim_vec v)) \<bullet>c v"
        "(u @\<^sub>v v) \<bullet>c x = u \<bullet>c (vec_first x (dim_vec u)) + v \<bullet>c (vec_last x (dim_vec v))"
proof-
  define n where "n \<equiv> dim_vec (u @\<^sub>v v)"
  define n\<^sub>u where "n\<^sub>u \<equiv> dim_vec u"
  define n\<^sub>v where "n\<^sub>v \<equiv> dim_vec v"

  have dims_add: "n\<^sub>u + n\<^sub>v = n" by (simp add: n\<^sub>u_def n\<^sub>v_def n_def)

  have n\<^sub>u_prop: "\<And>i. i < n\<^sub>u \<Longrightarrow> conjugate (u @\<^sub>v v)$i = (conjugate u)$i" by (simp add: n\<^sub>u_def)
  have n\<^sub>v_prop: "\<And>i. i < n\<^sub>v \<Longrightarrow> conjugate (u @\<^sub>v v)$(i + n\<^sub>u) = (conjugate v)$i"
    by (simp add: n\<^sub>u_def n\<^sub>v_def)

  have "n = dim_vec (conjugate (u @\<^sub>v v))" by (simp add: n_def)
  hence "x \<bullet>c (u @\<^sub>v v) = (\<Sum>i \<in> {0..<n}. x$i * (conjugate (u @\<^sub>v v))$i)"
    unfolding scalar_prod_def by blast
  hence "x \<bullet>c (u @\<^sub>v v) =
      (\<Sum>i \<in> {0..<n\<^sub>u}. x$i * (conjugate (u @\<^sub>v v))$i)
      + (\<Sum>i \<in> {n\<^sub>u..<n}. x$i * (conjugate (u @\<^sub>v v))$i)"
    by (smt (verit, best) bot_nat_0.extremum index_append_vec(2) n\<^sub>u_def n_def nat_le_linear nless_le not_add_less1 sum.atLeastLessThan_concat)
  moreover have "(\<Sum>i \<in> {0..<n\<^sub>u}. x$i * (conjugate (u @\<^sub>v v))$i) = (vec_first x (dim_vec u)) \<bullet>c u"
  proof-
    have *: "\<And>i. i \<in> {0..<n\<^sub>u} \<Longrightarrow> x$i = (vec_first x n\<^sub>u)$i"
      by (simp add: vec_first_def)
    have "(\<Sum>i \<in> {0..<n\<^sub>u}. x$i * (conjugate (u @\<^sub>v v))$i) = (\<Sum>i \<in> {0..<n\<^sub>u}. x$i * (conjugate u)$i)"
      using n\<^sub>u_prop by simp
    also have "... = (\<Sum>i \<in> {0..<n\<^sub>u}. (vec_first x n\<^sub>u)$i * (conjugate u)$i)"
      using * by auto
    also have "... = (vec_first x (dim_vec u)) \<bullet>c u"
      by (metis (no_types, lifting) dim_vec_conjugate n\<^sub>u_def scalar_prod_def sum.cong)
    finally show ?thesis .
  qed
  moreover have "(\<Sum>i \<in> {n\<^sub>u..<n}. x$i * (conjugate (u @\<^sub>v v))$i) = (vec_last x (dim_vec v)) \<bullet>c v"
  proof-
    have *: "vec_last (u @\<^sub>v v) n\<^sub>v = v"
      by (metis append_vec_eq carrier_vecI dims_add n\<^sub>u_def n_def vec_first_carrier vec_first_last_append)
    have "\<And>i. i \<in> {n\<^sub>u..<n} \<Longrightarrow> x$i = (vec_last x n\<^sub>v)$(i - (n - n\<^sub>v))"
      unfolding vec_last_def using assms dims_add less_diff_conv2 n_def by simp
    moreover have "\<And>i. i \<in> {n\<^sub>u..<n}
        \<Longrightarrow> (conjugate (u @\<^sub>v v))$i = (vec_last (conjugate (u @\<^sub>v v)) n\<^sub>v)$(i - (n - n\<^sub>v))"
      unfolding vec_last_def using assms dims_add less_diff_conv2 n_def by simp
    ultimately have "(\<Sum>i \<in> {n\<^sub>u..<n}. x$i * (conjugate (u @\<^sub>v v))$i)
        = (\<Sum>i \<in> {n\<^sub>u..<n}. (vec_last x n\<^sub>v)$(i - (n - n\<^sub>v))
          * (vec_last (conjugate (u @\<^sub>v v)) n\<^sub>v)$(i - (n - n\<^sub>v)))"
        (is "_ = (\<Sum>i \<in> _. ?F i)")
      by force
    also have "... = (\<Sum>i \<in> {0..<n-n\<^sub>u}. (vec_last x n\<^sub>v)$((i + n\<^sub>u) - (n - n\<^sub>v))
        * (vec_last (conjugate (u @\<^sub>v v)) n\<^sub>v)$((i + n\<^sub>u) - (n - n\<^sub>v)))"
      using sum.shift_bounds_nat_ivl[of ?F 0 n\<^sub>u n\<^sub>v] dims_add
      by (metis (no_types, lifting) add.commute add_0 add_diff_cancel_left')
    finally show ?thesis
      by (smt (verit, ccfv_SIG) "*" add_diff_cancel_left' add_diff_cancel_right' carrier_vecI conjugate_vec_last dim_vec_conjugate dims_add le_add2 n\<^sub>v_def n_def scalar_prod_def sum.cong)
  qed
  ultimately show "x \<bullet>c (u @\<^sub>v v) = (vec_first x (dim_vec u)) \<bullet>c u + (vec_last x (dim_vec v)) \<bullet>c v"
    by argo

  (* Duplicating the proof allows us to avoid assuming that 'a is commutative *)
  have n\<^sub>u_prop: "\<And>i. i < n\<^sub>u \<Longrightarrow> (u @\<^sub>v v)$i = u$i" by (simp add: n\<^sub>u_def)
  have n\<^sub>v_prop: "\<And>i. i < n\<^sub>v \<Longrightarrow> (u @\<^sub>v v)$(i + n\<^sub>u) = v$i"
    by (simp add: n\<^sub>u_def n\<^sub>v_def)

  have "n = dim_vec (conjugate (u @\<^sub>v v))" by (simp add: n_def)
  moreover have "dim_vec (conjugate x) = n" using assms n_def by auto
  ultimately have "(u @\<^sub>v v) \<bullet>c x = (\<Sum>i \<in> {0..<n}. (u @\<^sub>v v)$i * (conjugate x)$i)"
    unfolding scalar_prod_def by presburger
  hence "(u @\<^sub>v v) \<bullet>c x =
      (\<Sum>i \<in> {0..<n\<^sub>u}. (u @\<^sub>v v)$i * (conjugate x)$i)
      + (\<Sum>i \<in> {n\<^sub>u..<n}. (u @\<^sub>v v)$i * (conjugate x)$i)"
    by (smt (verit, best) bot_nat_0.extremum index_append_vec(2) n\<^sub>u_def n_def nat_le_linear nless_le not_add_less1 sum.atLeastLessThan_concat)
  moreover have "(\<Sum>i \<in> {0..<n\<^sub>u}. (u @\<^sub>v v)$i * (conjugate x)$i) = u \<bullet>c (vec_first x (dim_vec u))"
  proof-
    have *: "\<And>i. i \<in> {0..<n\<^sub>u} \<Longrightarrow> (conjugate x)$i = (vec_first (conjugate x) n\<^sub>u)$i"
      by (simp add: vec_first_def)
    have "(\<Sum>i \<in> {0..<n\<^sub>u}. (u @\<^sub>v v)$i * (conjugate x)$i)
        = (\<Sum>i \<in> {0..<n\<^sub>u}. u$i * (conjugate x)$i)"
      using n\<^sub>u_prop by simp
    also have "... = (\<Sum>i \<in> {0..<n\<^sub>u}. u$i * (vec_first (conjugate x) n\<^sub>u)$i)"
      using * by force
    also have "... = u \<bullet>c (vec_first x (dim_vec u))"
      by (metis (no_types, lifting) add.commute assms conjugate_vec_first dim_vec_first dims_add le_add2 n\<^sub>u_def n_def scalar_prod_def sum.cong)
    finally show ?thesis .
  qed
  moreover have "(\<Sum>i \<in> {n\<^sub>u..<n}. (u @\<^sub>v v)$i * (conjugate x)$i) = v \<bullet>c (vec_last x (dim_vec v))"
  proof-
    have *: "vec_last (u @\<^sub>v v) n\<^sub>v = v"
      by (metis append_vec_eq carrier_vecI dims_add n\<^sub>u_def n_def vec_first_carrier vec_first_last_append)
    have "\<And>i. i \<in> {n\<^sub>u..<n} \<Longrightarrow> (conjugate x)$i = (vec_last (conjugate x) n\<^sub>v)$(i - (n - n\<^sub>v))"
      unfolding vec_last_def using assms dims_add less_diff_conv2 n_def by simp
    moreover have "\<And>i. i \<in> {n\<^sub>u..<n}
        \<Longrightarrow> (u @\<^sub>v v)$i = (vec_last (u @\<^sub>v v) n\<^sub>v)$(i - (n - n\<^sub>v))"
      unfolding vec_last_def using assms dims_add less_diff_conv2 n_def by simp
    ultimately have "(\<Sum>i \<in> {n\<^sub>u..<n}. (u @\<^sub>v v)$i * (conjugate x)$i)
        = (\<Sum>i \<in> {n\<^sub>u..<n}. (vec_last (u @\<^sub>v v) n\<^sub>v)$(i - (n - n\<^sub>v))
          * (vec_last (conjugate x) n\<^sub>v)$(i - (n - n\<^sub>v)))"
        (is "_ = (\<Sum>i \<in> _. ?F i)")
      by force
    also have "... = (\<Sum>i \<in> {0..<n-n\<^sub>u}. (vec_last (u @\<^sub>v v) n\<^sub>v)$((i + n\<^sub>u) - (n - n\<^sub>v))
        * (vec_last (conjugate x) n\<^sub>v)$((i + n\<^sub>u) - (n - n\<^sub>v)))"
      using sum.shift_bounds_nat_ivl[of ?F 0 n\<^sub>u n\<^sub>v] dims_add
      by (metis (no_types, lifting) add.commute add_0 add_diff_cancel_left')
    finally show ?thesis
      by (smt (verit, best) "*" \<open>dim_vec (conjugate x) = n\<close> add_diff_cancel_left' add_diff_cancel_right' conjugate_vec_last dim_vec_conjugate dim_vec_last dims_add le_add2 scalar_prod_def sum.cong)
  qed
  ultimately show "(u @\<^sub>v v) \<bullet>c x = u \<bullet>c (vec_first x (dim_vec u)) + v \<bullet>c (vec_last x (dim_vec v))"
    by argo
qed

subsection "Schur's Formula"

proposition schur_formula:
  fixes M :: "'a::field mat"
  assumes "(A,B,C,D) = split_block M r c"
  assumes "r < dim_row M"
  assumes "c < dim_col M"
  assumes "square_mat M"
  assumes "square_mat A"
  assumes "inverts_mat A' A"
  assumes A'_dim: "A' \<in> carrier_mat r r"
  shows "det M = det A * det (D - C * A' * B)"
proof-
  let ?r\<^sub>M = "dim_row M"
  let ?c\<^sub>M = "dim_col M"
  let ?r\<^sub>A = "r"
  let ?c\<^sub>A = "c"
  let ?r\<^sub>B = "r"
  let ?c\<^sub>B = "?c\<^sub>M - ?c\<^sub>A"
  let ?r\<^sub>C = "?r\<^sub>M - ?r\<^sub>A"
  let ?c\<^sub>C = "c"
  let ?r\<^sub>D = "?r\<^sub>M - ?r\<^sub>A"
  let ?c\<^sub>D = "?c\<^sub>M - ?c\<^sub>A"
  let ?I\<^sub>A = "1\<^sub>m r"
  let ?I\<^sub>D = "1\<^sub>m ?r\<^sub>D"
  let ?O\<^sub>B = "0\<^sub>m ?r\<^sub>B ?c\<^sub>B"
  let ?O\<^sub>C = "0\<^sub>m ?r\<^sub>C ?c\<^sub>C"
  let ?P = "four_block_mat ?I\<^sub>A ?O\<^sub>B (C * A') ?I\<^sub>D"
  let ?Q = "four_block_mat A ?O\<^sub>B ?O\<^sub>C (D - C * A' * B)"
  let ?R = "four_block_mat ?I\<^sub>A (A' * B) ?O\<^sub>C ?I\<^sub>D"

  have M: "M = four_block_mat A B C D"
    using Matrix.split_block(5)[of M r c A B C D] by (metis assms(1-3) le_simps(1) less_eqE)

  have M_dim: "M \<in> carrier_mat ?r\<^sub>M ?c\<^sub>M"
    by blast
  have A_dim: "A \<in> carrier_mat r r"
    using assms(1)
    unfolding split_block_def
    by (metis Pair_inject assms(5) carrier_mat_triv dim_row_mat(1) square_mat.elims(2))
  have square: "?r\<^sub>M - ?r\<^sub>A = ?c\<^sub>M - ?c\<^sub>A" "r = c" "?r\<^sub>M = ?c\<^sub>M"
    using M_dim assms(4)
      apply (metis A_dim assms(1) assms(5) carrier_matD(1) dim_col_mat(1) prod.sel(1) split_block_def square_mat.elims(2))
     apply (metis A_dim assms(1) carrier_matD(2) dim_col_mat(1) prod.sel(1) split_block_def)
    using assms(4) by force
  have C_A'_dim: "C * A' \<in> carrier_mat ?r\<^sub>C ?c\<^sub>C"
    by (smt (verit) A'_dim Pair_inject assms(1) carrier_matD(2) carrier_mat_triv dim_row_mat(1) index_mult_mat(2) index_mult_mat(3) split_block_def square(2))
  have A'_B_dim: "A' * B \<in> carrier_mat ?r\<^sub>B ?c\<^sub>B"
    by (metis (no_types, lifting) A'_dim Pair_inject assms(1) carrier_matD(1) carrier_mat_triv dim_col_mat(1) index_mult_mat(2) index_mult_mat(3) split_block_def)
  have D_min_C_A'_B_dim: "D - C * A' * B \<in> carrier_mat ?c\<^sub>D ?c\<^sub>D"
    by (metis A'_B_dim C_A'_dim carrier_matD(1) carrier_matD(2) carrier_mat_triv index_mult_mat(2) index_mult_mat(3) minus_carrier_mat square(1))
  have P_dim: "?P \<in> carrier_mat ?r\<^sub>M ?c\<^sub>M"
    using assms(2) square(3) by auto
  have Q_dim: "?Q \<in> carrier_mat ?r\<^sub>M ?c\<^sub>M"
    by (smt (verit) A_dim D_min_C_A'_B_dim P_dim carrier_matD(1) carrier_matD(2) carrier_mat_triv index_mat_four_block(2) index_mat_four_block(3) index_one_mat(3) square(2) square(3))
  have R_dim: "?R \<in> carrier_mat ?r\<^sub>M ?c\<^sub>M"
    using P_dim by fastforce

  have M: "M = ?P * ?Q * ?R"
  proof-
    have B_dim: "B \<in> carrier_mat ?r\<^sub>B ?c\<^sub>B"
      by (metis assms(1) assms(2) assms(3) less_imp_le_nat ordered_cancel_comm_monoid_diff_class.add_diff_inverse split_block(2))
    have C_dim: "C \<in> carrier_mat ?r\<^sub>C r"
      by (metis assms(1) assms(3) diff_add_inverse less_eqE less_or_eq_imp_le split_block(3) square(2) square(3))
    have D_dim: "D \<in> carrier_mat ?r\<^sub>D ?c\<^sub>D"
      using A_dim M square(2) by auto

    have 1: "?I\<^sub>A \<in> carrier_mat r r" by simp
    have 2: "?O\<^sub>B \<in> carrier_mat ?r\<^sub>B ?c\<^sub>B" by auto
    have 3: "C * A' \<in> carrier_mat ?r\<^sub>C r" using C_A'_dim square(2) by blast
    have 4: "?I\<^sub>D \<in> carrier_mat ?r\<^sub>C ?c\<^sub>B" using "2" square(1) by auto
    have 6: "?O\<^sub>B \<in> carrier_mat r ?c\<^sub>B" using "2" square(2) by blast
    have 7: "?O\<^sub>C \<in> carrier_mat ?c\<^sub>B r" using "4" square(2) by auto
    have 8: "(D - C * A' * B) \<in> carrier_mat ?c\<^sub>B ?c\<^sub>B"
      using "4" D_min_C_A'_B_dim square(1) square(2) by auto
    have a: "(D - C * A' * B) \<in> carrier_mat ?r\<^sub>D ?c\<^sub>D" using "8" square(1) by presburger
    have b: "?I\<^sub>D \<in> carrier_mat ?c\<^sub>B ?c\<^sub>B" using "2" square(1) by auto
    have ass: "(C * A') * A = C * (A' * A)" using A_dim A'_dim C_dim by (simp add: square(2))
    have "?P * ?Q = four_block_mat A ?O\<^sub>B C (D - C * A' * B)"
    proof-
      have "A = ?I\<^sub>A * A + ?O\<^sub>B * ?O\<^sub>C"
        using A_dim square(2) square(3) by auto
      moreover have "?O\<^sub>B = ?I\<^sub>A * ?O\<^sub>B + ?O\<^sub>B * (D - C * A' * B)"
        by (smt (verit, ccfv_threshold) "1" "2" "8" D_min_C_A'_B_dim carrier_matD(2) left_add_zero_mat left_mult_zero_mat right_mult_zero_mat)
      moreover have "C = (C * A') * A + ?I\<^sub>D * ?O\<^sub>C"
        by (metis A'_dim C_dim square(2) Matrix.right_add_zero_mat ass assms(6) carrier_matD(1) index_zero_mat(2) inverts_mat_def left_mult_one_mat' right_mult_one_mat)
      moreover have "(D - C * A' * B) = ((C * A') * ?O\<^sub>B) + ?I\<^sub>D * (D - C * A' * B)"
        by (metis C_A'_dim D_min_C_A'_B_dim left_add_zero_mat left_mult_one_mat right_mult_zero_mat square(1) square(2))
      ultimately show ?thesis
        using mult_four_block_mat[OF 1 2 3 4 A_dim 6 7 8] by argo
    qed
    also have "... * ?R = four_block_mat A B C D"
    proof- (* ?R = "four_block_mat ?I\<^sub>A (A' * B) ?O\<^sub>C ?I\<^sub>D" *)
      have "A = A * ?I\<^sub>A + ?O\<^sub>B * C"
        using A_dim C_dim square(1) by force
      moreover have "B = A * (A' * B) + ?O\<^sub>B * ?I\<^sub>D"
        by (smt (verit, ccfv_threshold) inverts_mat_symm A_dim B_dim Matrix.right_add_zero_mat assms(6) assms(7) assoc_mult_mat b carrier_mat_triv index_mult_mat(2) inverts_mat_def left_mult_one_mat left_mult_zero_mat)
      moreover have "C = C * ?I\<^sub>A + (D - C * A' * B) * ?O\<^sub>C"
        by (metis "8" C_dim Matrix.right_add_zero_mat right_mult_one_mat right_mult_zero_mat square(1) square(2))
      moreover have "D = C * (A' * B) + (D - C * A' * B) * ?I\<^sub>D"
      proof-
        have "C * A' * B \<in> carrier_mat ?r\<^sub>D ?c\<^sub>D"
          using B_dim C_A'_dim mult_carrier_mat square(2) by blast
        moreover have "C * (A' * B) = C * A' * B" using B_dim C_dim assms(7) by force
        ultimately show ?thesis
          by (metis (no_types, lifting) "8" D_dim left_add_zero_mat mat_minus_minus minus_r_inv_mat right_mult_one_mat square(2) square(3))
      qed
      ultimately show ?thesis 
        using mult_four_block_mat[OF A_dim 2 C_dim a 1 A'_B_dim 7 b] A_dim square(2) square(3)
        by force
    qed
    also have "... = M" unfolding M by simp
    finally show ?thesis by argo
  qed
  hence "det M = det ?P * det ?Q * det ?R"
    by (smt (verit, best) det_mult P_dim Q_dim R_dim assms(4) mult_carrier_mat square_mat.elims(2))
  moreover have "det ?P = 1"
    using det_four_block_mat_upper_right_zero[OF _ _ C_A'_dim, of ?I\<^sub>A ?O\<^sub>B ?I\<^sub>D]
    by (simp add: square)
  moreover have "det ?Q = det A * det (D - C * A' * B)"
    using det_four_block_mat_upper_right_zero[OF A_dim _ _ D_min_C_A'_B_dim, of ?O\<^sub>B ?O\<^sub>C]
    by (simp add: square)
  moreover have "det ?R = 1"
    using det_four_block_mat_lower_left_zero[OF _ A'_B_dim, of ?I\<^sub>A "?O\<^sub>C" ?I\<^sub>D]
    by (simp add: square)
  ultimately show ?thesis by fastforce
qed

section "Positive Definite Lemmas"

definition positive_definite where
  "positive_definite M \<longleftrightarrow> hermitian M
    \<and> (\<forall>x \<in> carrier_vec (dim_col M). x \<noteq> 0\<^sub>v (dim_col M) \<longrightarrow> QF M x > 0)"

lemma leading_principal_submatrix_positive_definite:
  fixes A :: "'a::{conjugatable_field,ord} mat"
  assumes "A \<in> carrier_mat n n"
  assumes "positive_definite A"
  assumes "k \<le> n"
  shows "positive_definite (lps A k)"
proof-
  define B where "B \<equiv> lps A k"
  have B_carrier: "B \<in> carrier_mat k k"
    using B_def assms(1) assms(3) leading_principal_submatrix_carrier by blast
  hence B_dims: "dim_row B = k \<and> dim_col B = k" by simp
  { fix v :: "'a vec"
    assume *: "v \<in> carrier_vec k" "v \<noteq> 0\<^sub>v k"
    define w where "w \<equiv> vec n (\<lambda>i. if i < k then v$i else 0)"
    hence "w \<noteq> 0\<^sub>v n"
      by (smt (verit) "*"(1) "*"(2) assms(3) carrier_vecD dual_order.strict_trans1 eq_vecI index_vec index_zero_vec(1) index_zero_vec(2))
    hence "QF A w > 0" using assms(1) assms(2) positive_definite_def vec_carrier w_def by blast
    moreover have "QF A w = QF B v"
    proof-
      have 1: "\<And>i. i \<in> {k..<n} \<Longrightarrow> conjugate (w$i) = 0" using w_def by simp
      have 2: "\<And>i. i \<in> {0..<k} \<Longrightarrow> w$i = v$i" using assms(3) w_def by auto
      hence 3: "\<And>i. i \<in> {0..<k} \<Longrightarrow> conjugate (w$i) = conjugate (v$i)" by presburger
      have 4: "\<And>i. i \<in> {0..<k} \<Longrightarrow> (A *\<^sub>v w)$i = (B *\<^sub>v v)$i"
      proof-
        fix i assume **: "i \<in> {0..<k}"
        have ***: "\<And>j. j \<in> {0..<k} \<Longrightarrow> (row A i)$j = (row B i)$j"
        proof-
          fix j assume "j \<in> {0..<k}"
          moreover then have "(row A i)$j = A$$(i,j)"
            using "**" * assms(1) assms(3) by force
          ultimately show "(row A i)$j = (row B i)$j"
            by (metis (mono_tags, lifting) ** B_def B_dims assms(1) assms(3) atLeastLessThan_iff index_vec leading_principal_submatrix_index row_def)
        qed
        have ****: "row B i \<in> carrier_vec k \<and> dim_vec v = k"
          using B_carrier B_dims * by auto
        have "(A *\<^sub>v w)$i = row A i \<bullet> w" using ** assms(1) assms(3) by force
        also have "... = (\<Sum>j \<in> {0..<n}. (row A i)$j * w$j)"
          by (metis (no_types, lifting) dim_vec scalar_prod_def sum.cong w_def)
        also have "... = (\<Sum>j \<in> {0..<k}. (row A i)$j * w$j) + (\<Sum>j \<in> {k..<n}. (row A i)$j * w$j)"
          by (simp add: assms(3) sum.atLeastLessThan_concat)
        also have "... = (\<Sum>j \<in> {0..<k}. (row A i)$j * v$j)"
          using 1 2 by auto
        also have "... = (\<Sum>j \<in> {0..<k}. (row B i)$j * v$j)"
          using *** by fastforce
        also have "... = (row B i) \<bullet> v"
          using B_carrier **** unfolding scalar_prod_def by blast
        also have "... = (B *\<^sub>v v)$i" using ** B_carrier by auto
        finally show "(A *\<^sub>v w)$i = (B *\<^sub>v v)$i" .
      qed
      have 5: "v \<in> carrier_vec k" by (simp add: "*"(1))
      hence 6: "B *\<^sub>v v \<in> carrier_vec k \<and> conjugate v \<in> carrier_vec k"
        by (metis B_def Matrix.carrier_vec_conjugate assms(1) assms(3) leading_principal_submatrix_carrier mult_mat_vec_carrier)
      have "QF A w = (A *\<^sub>v w) \<bullet>c w" by simp
      also have "... = (\<Sum>i \<in> {0..<n}. (A *\<^sub>v w)$i * conjugate (w$i))"
        by (smt (verit, ccfv_SIG) atLeastLessThan_iff dim_vec dim_vec_conjugate scalar_prod_def sum.cong vec_index_conjugate w_def)
      also have "... = (\<Sum>i \<in> {0..<k}. (A *\<^sub>v w)$i * conjugate (w$i))
          + (\<Sum>i \<in> {k..<n}. (A *\<^sub>v w)$i * conjugate (w$i))"
        by (simp add: assms(3) sum.atLeastLessThan_concat)
      also have "... = (\<Sum>i \<in> {0..<k}. (A *\<^sub>v w)$i * conjugate (w$i))" using 1 by simp
      also have "... = (\<Sum>i \<in> {0..<k}. (B *\<^sub>v v)$i * conjugate (v$i))" using 3 4 by force
      also have "... = (B *\<^sub>v v) \<bullet>c v"
        by (smt (verit, best) 5 6 atLeastLessThan_iff carrier_vecD scalar_prod_def sum.cong vec_index_conjugate)
      finally show ?thesis using quadratic_form_def by force
    qed
    ultimately have "QF B v > 0" by argo
  }
  thus ?thesis
    using assms(2) leading_principal_submatrix_hermitian
    unfolding positive_definite_def
    by (metis B_def B_dims assms(1) assms(3))
qed

lemma positive_definite_invertible:
  fixes M :: "complex mat"
  assumes "positive_definite M"
  shows "invertible_mat M"
proof-
  define n where "n \<equiv> dim_row M"
  have "\<And>x. x \<in> carrier_vec n \<Longrightarrow> x \<noteq> 0\<^sub>v n \<Longrightarrow> M *\<^sub>v x \<noteq> 0\<^sub>v n"
    using assms n_def positive_definite_def hermitian_is_square by force
  hence "mat_kernel M \<subseteq> {0\<^sub>v n}"
    unfolding mat_kernel_def n_def
    by (metis (mono_tags, lifting) assms hermitian_is_square mem_Collect_eq positive_definite_def singleton_iff square_mat.simps subsetI)
  thus ?thesis
    using trivial_kernel_imp_invertible n_def assms positive_definite_def hermitian_is_square
    by blast
qed

lemma positive_definite_det_nz:
  fixes A :: "complex mat"
  assumes "positive_definite A"
  shows "det A \<noteq> 0"
  using positive_definite_invertible[OF assms] invertible_det invertible_mat_def square_mat.simps
  by blast

end
