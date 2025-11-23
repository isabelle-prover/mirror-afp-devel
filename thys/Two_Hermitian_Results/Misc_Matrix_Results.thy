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
hide_type (open)
  Finite_Cartesian_Product.vec
  Matrix_Legacy.vec
  Matrix_Legacy.mat

hide_fact (open)
  Matrix_Legacy.mat_def
  Finite_Cartesian_Product.mat_def
  Finite_Cartesian_Product.row_def
  Matrix_Legacy.row_def
  Matrix_Legacy.row_def
  Matrix_Legacy.col_def
  Determinants.det_def
  Determinants.det_def
  Finite_Cartesian_Product.vec_def
  Matrix_Legacy.vec_def
  Linear_Algebra.adjoint_def

hide_const (open)
  Matrix_Legacy.mat
  Finite_Cartesian_Product.mat
  Finite_Cartesian_Product.row
  Matrix_Legacy.row
  Matrix_Legacy.row
  Matrix_Legacy.col
  Determinants.det
  Determinants.det
  Finite_Cartesian_Product.vec
  Matrix_Legacy.vec
  Linear_Algebra.adjoint

no_notation fps_nth (infixl "$" 75)

unbundle no inner_syntax
unbundle no vec_syntax

(* There are two definitions of the spectrum of a matrix: one in Spectrual_Radius and 
   one in Projective_Measurements. We prove that they are equal. We choose to hide the
   Spectral_Radius definition as its qualified name is shorter than the alternative. *)
hide_const (open) Spectral_Radius.spectrum
hide_fact (open) Spectral_Radius.spectrum_def

section "Polynomial Factorization"

lemma idom_poly_factor_unique_aux:
  fixes rs rs' :: "'a::idom list"
  assumes eq: "(\<Prod>a\<leftarrow>rs. [:a, 1:]) = (\<Prod>a\<leftarrow>rs'. [:a, 1:])"
  shows "mset rs \<subseteq># mset rs'"
  using eq                        
  by (metis count_list_eq_length_filter count_mset poly_linear_exp_linear_factors
      poly_linear_exp_linear_factors_rev subseteq_mset_def)

lemma idom_poly_factor_unique:
  fixes rs rs' :: "'a::idom list"
  assumes eq: "(\<Prod>a\<leftarrow>rs. [:a, 1:]) = (\<Prod>a\<leftarrow>rs'. [:a, 1:])"
  shows "mset rs = mset rs'"
  using idom_poly_factor_unique_aux[OF eq] idom_poly_factor_unique_aux[OF eq[symmetric]]
  by order

lemma idom_poly_factor_unique':
  fixes rs rs' :: "'a::idom list"
  assumes eq: "(\<Prod>a\<leftarrow>rs. [:- a, 1:]) = (\<Prod>a\<leftarrow>rs'. [:- a, 1:])"
  shows "mset rs = mset rs'"
proof-
  have "(\<Prod>a\<leftarrow>rs. [:- a, 1:]) = (\<Prod>a\<leftarrow>(map uminus rs). [:a, 1:])"
    by (simp add: o_def pCons_def)
  moreover have "(\<Prod>a\<leftarrow>rs'. [:- a, 1:]) = (\<Prod>a\<leftarrow>(map uminus rs'). [:a, 1:])"
    by (simp add: o_def pCons_def)
  ultimately have "mset (map uminus rs) = mset (map uminus rs')"
    using idom_poly_factor_unique[of "map uminus rs" "map uminus rs'"] eq by argo
  moreover have "mset (map uminus (map uminus (as::'a list))) = mset as" for as by simp
  ultimately show ?thesis using mset_map by metis
qed

section "Vector Normalization"

lemma vec_normalize_norm: "v \<in> carrier_vec n \<Longrightarrow> v \<noteq> 0\<^sub>v n \<Longrightarrow> vec_norm (vec_normalize v) = 1"
  by (simp add: normalized_vec_norm vec_norm_def)

section "Determinant, Invertability, and Eigenvalues"

definition eigvals_of [simp]:
  "eigvals_of M es \<longleftrightarrow> char_poly M = (\<Prod>a\<leftarrow>es. [:- a, 1:]) \<and> length es = dim_row M"

lemma eigvals_of_mset_eq:
    "eigvals_of (A::'a::idom mat) es \<Longrightarrow> eigvals_of A es' \<Longrightarrow> mset es = mset es'"
  unfolding eigvals_of by (metis idom_poly_factor_unique')

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
    using 1
    by (metis (mono_tags, lifting) eigvals_poly_length someI_ex)
  obtain Q Q' B where *: "similar_mat_wit A B Q Q' \<and> upper_triangular B \<and> diag_mat B = es"
    using schur_decomposition[OF 1 2] by (metis surj_pair)

  then have "det A = det (Q * B * Q')" unfolding similar_mat_wit_def by metis
  also have "\<dots> = det Q * det B * det Q'"
    by (smt (verit, ccfv_SIG) "*" "1" det_mult mult_carrier_mat similar_mat_witD2(5) similar_mat_witD2(6) similar_mat_witD2(7))
  also have "\<dots> = det Q * det B * 1/(det Q)"
    by (smt (verit, ccfv_threshold) "*" "1" det_mult det_one div_by_0 helper mult_cancel_left1 n_def nonzero_mult_div_cancel_left similar_mat_witD(6) similar_mat_witD(7) similar_mat_witD2(1))
  also have "\<dots> = det Q * (\<Prod>e \<leftarrow> diag_mat B. e) * 1/(det Q)"
    by (metis "*" det_upper_triangular list.map_ident similar_mat_witD(5))
  also have "\<dots> = (\<Prod>e \<leftarrow> (eigvals A). e)"
    by (metis (no_types, lifting) * es_def "1" Groups.mult_ac(2) class_field.zero_not_one det_mult det_one mult_cancel_left2 nonzero_mult_div_cancel_left similar_mat_witD(6) similar_mat_witD(7) similar_mat_witD2(2))
  finally show ?thesis .
qed

lemma eigvals_of_spectrum:
    "(A::(complex mat)) \<in> carrier_mat n n \<Longrightarrow> eigvals_of A \<alpha> \<Longrightarrow> Spectral_Radius.spectrum A = set \<alpha>"
  unfolding eigvals_of
  using eigenvalue_root_char_poly[of A n]
  by (metis Spectral_Radius.spectrum_def equalityI linear_poly_root mem_Collect_eq root_poly_linear subsetI)

lemma spectrum_connect:
    "(A::complex mat) \<in> carrier_mat n n \<Longrightarrow> Spectral_Radius.spectrum A = spectrum A"
  by (metis eigvals_of eigvals_of_spectrum eigvals_poly_length spectrum_def)

lemma spectrum_shift:
  fixes A :: "complex mat"
  assumes dim: "A \<in> carrier_mat n n"
  shows "spectrum (A - r \<cdot>\<^sub>m 1\<^sub>m n) = {\<mu> - r | \<mu>. \<mu> \<in> spectrum A}" (is "?lhs = ?rhs")
proof
  { let ?A' = "A - r \<cdot>\<^sub>m 1\<^sub>m n"
    fix \<mu> assume \<mu>: "\<mu> \<in> ?lhs"
    then obtain v where v: "v \<in> carrier_vec n" "v \<noteq> 0\<^sub>v n" "?A' *\<^sub>v v = \<mu> \<cdot>\<^sub>v v"
      by (metis (no_types, lifting) carrier_mat_triv eigenvalue_def eigenvector_def index_minus_mat(2,3)
          index_one_mat(2,3) index_smult_mat(2,3) spectrum_eigenvalues)
    hence "?A' *\<^sub>v v = A *\<^sub>v v - r \<cdot>\<^sub>v v"
      using dim
      by (smt (verit, best) minus_mult_distrib_mat_vec one_carrier_mat one_mult_mat_vec
          smult_carrier_mat smult_mat_mult_mat_vec_assoc)
    hence "A *\<^sub>v v = \<mu> \<cdot>\<^sub>v v + r \<cdot>\<^sub>v v" using v(1,3) dim by auto
    also have "\<dots> = (\<mu> + r) \<cdot>\<^sub>v v" using v(1) by (simp add: add_smult_distrib_vec)
    finally have "\<mu> + r \<in> spectrum A"
      using spectrum_connect[OF dim] v(1,2) dim
      by (metis Spectral_Radius.spectrum_def carrier_matD(1) eigenvalue_def eigenvector_def mem_Collect_eq)
    hence "\<mu> \<in> ?rhs" by force
  }
  thus "?lhs \<subseteq> ?rhs" by blast
next
  { let ?A' = "A - r \<cdot>\<^sub>m 1\<^sub>m n"
    fix \<mu> assume \<mu>: "\<mu> \<in> ?rhs"
    then obtain \<mu>' where \<mu>': "\<mu> = \<mu>' - r" "\<mu>' \<in> spectrum A" by blast
    then obtain v where v: "v \<in> carrier_vec n" "v \<noteq> 0\<^sub>v n" "A *\<^sub>v v = \<mu>' \<cdot>\<^sub>v v"
      using spectrum_connect[OF dim] dim
      by (metis carrier_matD(1) eigenvalue_def eigenvector_def spectrum_eigenvalues)
    have "?A' *\<^sub>v v = A *\<^sub>v v - r \<cdot>\<^sub>v v"
      using v(1) dim
      by (smt (verit, del_insts) minus_mult_distrib_mat_vec one_carrier_mat one_mult_mat_vec
          smult_carrier_mat smult_mat_mult_mat_vec_assoc)
    also have "\<dots> = \<mu>' \<cdot>\<^sub>v v - r \<cdot>\<^sub>v v" using v(3) by auto
    also have "\<dots> = \<mu> \<cdot>\<^sub>v v" using dim v(1) \<mu>'(1) by (simp add: minus_smult_vec_distrib)
    finally have "\<mu> \<in> spectrum ?A'"
      using v(1,2) spectrum_connect[OF dim]
      by (smt (verit) Spectral_Radius.spectrum_def carrier_mat_def eigenvalue_def eigenvector_def
          index_minus_mat(2,3) index_one_mat(2,3) index_smult_mat(2,3) mem_Collect_eq spectrum_connect)
    hence "\<mu> \<in> ?lhs" by blast
  }
  thus "?rhs \<subseteq> ?lhs" by blast
qed

lemma trivial_kernel_imp_nonzero_eigenvalues:
  fixes M :: "'a::{idom,ring_1_no_zero_divisors} mat"
  assumes "square_mat M"
  assumes "mat_kernel M \<subseteq> {0\<^sub>v (dim_row M)}"
  assumes "eigenvalue M e"
  shows "e \<noteq> 0"
  using assms by (metis (no_types, lifting) carrier_matI carrier_vecD eigenvalue_def eigenvector_def empty_iff mat_kernelI singleton_iff smult_vec_zero square_mat.simps subset_singletonD)

lemma trivial_kernel_imp_invertible: 
  fixes M :: "complex mat"
  assumes "square_mat M"
  assumes "mat_kernel M \<subseteq> {0\<^sub>v (dim_row M)}"
  shows "invertible_mat M"
  using assms by (metis carrier_matI det_0_iff_vec_prod_zero_field empty_iff invertible_det mat_kernelI singletonD square_mat.elims(2) subset_singletonD)

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
  fixes A :: "'a::conjugatable_ordered_field mat"
  assumes "square_mat A"
  assumes "B = c \<cdot>\<^sub>m A"
  assumes "eigvals_of A es"
  shows "eigvals_of B (map (\<lambda>x. c * x) es)"
proof-
  obtain A' P Q where A_decomp: "schur_decomposition A es = (A', P, Q)
      \<and> similar_mat_wit A A' P Q
      \<and> upper_triangular A'
      \<and> diag_mat A' = es"
    using assms(1,3) unfolding eigvals_of square_mat.simps
    by (metis carrier_mat_triv old.prod.exhaust schur_decomposition)
  define B' where "B' \<equiv> c \<cdot>\<^sub>m A'"

  have B'_square: "square_mat B'" using A_decomp B'_def similar_mat_witD(5) by fastforce
  have B_decomp: "similar_mat_wit B B' P Q \<and> upper_triangular B'"
  proof-
    have "upper_triangular B'"
    proof-
      { fix i j assume *: "j < i" "i < dim_row B'"
        hence "B'$$(i,j) = c * A'$$(i,j)" using B'_def B'_square by auto
        also have "\<dots> = 0" using A_decomp * unfolding upper_triangular_def by (simp add: B'_def)
        finally have "B'$$(i,j) = 0" .
      }
      thus ?thesis by blast
    qed
    moreover have "similar_mat_wit B B' P Q"
    proof-
      have "B = c \<cdot>\<^sub>m (P * A' * Q)" using A_decomp assms(2) similar_mat_witD2(3) by blast
      also have "\<dots> = P * (c \<cdot>\<^sub>m A') * Q"
        by (metis A_decomp similar_mat_wit_def similar_mat_wit_smult)
      also have "\<dots> = P * B' * Q" using B'_def by argo
      finally have "B = P * B' * Q" .
      thus ?thesis by (smt (verit, best) A_decomp B'_def assms(2) similar_mat_wit_smult)
    qed
    ultimately show ?thesis by blast
  qed

  hence "char_poly B' = (\<Prod>a\<leftarrow>diag_mat B'. [:- a, 1:])"
    using char_poly_upper_triangular B_decomp B'_square by auto
  moreover have "length (diag_mat B') = dim_row B'" by (simp add: diag_mat_length)
  ultimately have "eigvals_of B' (diag_mat B')" using eigvals_of by blast
  moreover have "diag_mat B' = map (\<lambda>x. c * x) es"
    using A_decomp B'_def by (metis diag_mat_map similar_mat_witD(5) smult_mat_def)
  ultimately show ?thesis                                 
    using similar_mats_eigvals B_decomp assms(2) assms(3) char_poly_similar similar_mat_def
    by fastforce
qed

lemma neg_mat_eigvals:
  fixes A :: "complex mat"
  assumes "square_mat A"
  assumes "eigvals_of A es"
  shows "eigvals_of (-A) (rev (map (\<lambda>x. -x) es))"
proof-
  have "eigvals_of A (rev es)"
    using assms(2)
    unfolding eigvals_of
    by (metis length_rev prod_list.rev rev_map)
  thus ?thesis
    using scale_eigvals[of A "-A" "-1" "rev es"]
    by (metis (lifting) ext assms(1) carrier_mat_triv mult_commute_abs mult_minus1_right rev_map square_mat.elims(2) uminus_mat)
qed

section "Quadratic Form"

definition quadratic_form :: "'a mat \<Rightarrow> 'a vec \<Rightarrow> 'a::{conjugatable_ring}" where
  "quadratic_form M x \<equiv> inner_prod x (M *\<^sub>v x)"

abbreviation "QF \<equiv> quadratic_form"

declare
  quadratic_form_def[simp]

section "Leading Principal Submatrix"

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

section "Hermitian Matrix"

(* TODO: put into cmplx_herm_mat locale *)
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

lemma hermitian_eigvals_of_real: "hermitian (A::complex mat) \<Longrightarrow> eigvals_of A es \<Longrightarrow> set es \<subseteq> \<real>"
  using hermitian_real_diag_decomp_eigvals[of A _ es] hermitian_square by blast

lemma hermitian_is_square: "hermitian A \<Longrightarrow> square_mat A"
  by (metis adjoint_dim_col hermitian_def square_mat.simps)

lemma hermitian_ij_ji_iff:
  "hermitian A
    \<longleftrightarrow> square_mat A \<and> (\<forall>i j. i < dim_row A \<and> j < dim_row A \<longrightarrow> A$$(i,j) = conjugate (A$$(j,i)))"
  by (metis (no_types, lifting) adjoint_dim_col adjoint_dim_row adjoint_eval hermitian_def mat_eq_iff square_mat.simps)

lemma adjoint_is_conjugate_transpose: "A\<^sup>H = adjoint A" 
  by (simp add: adjoint_def transpose_def cong_mat conjugate_mat_def)

subsection "Locale for Complex Hermitian Matrices"

locale cmplx_herm_mat = complex_vec_space n for n +
  fixes A :: "complex mat"
  assumes A_dim: "A \<in> carrier_mat n n"
  assumes A_herm: "hermitian A"
begin

lemma hermitian_quadratic_form_real:
  fixes v :: "complex vec"
  assumes v: "v \<in> carrier_vec n"
  shows "QF A v \<in> Reals"
proof-
  have "conjugate (QF A v) = inner_prod (A *\<^sub>v v) v"
    using A_dim v by (metis inner_prod_swap mult_mat_vec_carrier quadratic_form_def)
  also have "\<dots> = inner_prod v ((adjoint A) *\<^sub>v v)"
    using A_dim A_herm v by (metis adjoint_def_alter hermitian_def)
  also have "\<dots> = inner_prod v (A *\<^sub>v v)" using A_herm by (simp add: hermitian_def)
  finally have "conjugate (QF A v) = QF A v" by simp
  thus ?thesis by (simp add: Reals_cnj_iff)
qed

definition eigenvalues\<^sub>0 :: "complex list" where
  "eigenvalues\<^sub>0 \<equiv> eigvals A"

lemma eigenvalues\<^sub>0_exist: "\<exists>es. eigvals_of A es" using A_dim eigvals_poly_length by auto

lemma eigenvalues\<^sub>0: "eigvals_of A eigenvalues\<^sub>0"
  using eigenvalues\<^sub>0_exist unfolding eigvals_of eigenvalues\<^sub>0_def eigvals_def ..

lemma eigenvalues\<^sub>0_real: "set eigenvalues\<^sub>0 \<subseteq> \<real>"
  using A_herm eigenvalues\<^sub>0 hermitian_eigvals_of_real
  by blast

definition eigenvalues :: "complex list" where
  "eigenvalues \<equiv> rev (sort_key Re eigenvalues\<^sub>0)"

lemma eigenvalues: "eigvals_of A eigenvalues"
proof-
  have "mset eigenvalues = mset eigenvalues\<^sub>0" by (simp add: eigenvalues_def)
  thus ?thesis
    using eigenvalues_def eigvals_of eigenvalues\<^sub>0
    by (metis (mono_tags, lifting) mset_eq_length mset_map prod_mset_prod_list)
qed

lemma eigenvalues_sorted: "sorted_wrt (\<ge>) eigenvalues"
proof-
  have "\<forall>\<mu>\<^sub>1 \<mu>\<^sub>2. \<mu>\<^sub>1 \<in> set eigenvalues\<^sub>0 \<longrightarrow> \<mu>\<^sub>2 \<in> set eigenvalues\<^sub>0 \<longrightarrow> (\<mu>\<^sub>1 \<le> \<mu>\<^sub>2 \<longleftrightarrow> Re \<mu>\<^sub>1 \<le> Re \<mu>\<^sub>2)"
    using eigenvalues_def eigenvalues\<^sub>0_real by (simp add: complex_is_Real_iff less_eq_complex_def subset_iff)
  hence "sorted_wrt (\<le>) (sort_key Re eigenvalues\<^sub>0)"
    by (smt (verit, ccfv_threshold) length_map nth_map nth_mem order_trans_rules(19) set_sort sorted_sort_key
        sorted_wrt_iff_nth_less)
  thus ?thesis unfolding eigenvalues_def sorted_wrt_rev .
qed

lemma eigenvalues_unique:
  assumes es: "eigvals_of A es'"
  assumes es_sorted: "sorted_wrt (\<ge>) es'"
  shows "es' = eigenvalues"
proof-
  have "mset es' = mset eigenvalues" using es eigenvalues eigvals_of_mset_eq by blast
  moreover have "length es' = length eigenvalues" by (metis calculation size_mset)
  moreover have "sorted (rev (map Re es'))"
    using es_sorted by (metis less_eq_complex_def sorted_wrt_map_mono sorted_wrt_rev)
  moreover have "sorted (rev (map Re eigenvalues))"
    using eigenvalues by (simp add: eigenvalues_def rev_map)
  ultimately have "rev (map Re es') = rev (map Re eigenvalues)"
    by (metis mset_map mset_rev properties_for_sort) 
  hence "map Re es' = map Re eigenvalues" by force
  moreover have "set es' \<subseteq> \<real> \<and> set eigenvalues \<subseteq> \<real>"
    using es A_herm eigenvalues hermitian_eigvals_of_real by blast 
  ultimately show "es' = eigenvalues" by (metis list.inj_map_strong of_real_Re subset_code(1))
qed

lemma eigenvalues_real: "set eigenvalues \<subseteq> \<real>"
  using A_herm hermitian_eigvals_of_real eigenvalues(1) by blast

lemma eigenvalues_set_eq: "set eigenvalues\<^sub>0 = set eigenvalues"
  by (simp add: eigenvalues_def)

lemma hermitian_eigenvalues_real:
  assumes e: "eigenvalue A e"
  shows "e \<in> Reals"
  using cpx_sq_mat.hermitian_spectrum_real[OF _ A_dim A_herm, of n n e]
  using A_dim e
  by (metis Projective_Measurements.spectrum_def cpx_sq_mat_axioms.intro cpx_sq_mat_def eigenvalue_imp_nonzero_dim eigenvalue_root_char_poly eigvals_poly_length fixed_carrier_mat.intro root_poly_linear)

lemma hermitian_spectrum_real: "spectrum A \<subseteq> Reals"
  unfolding spectrum_connect[OF A_dim, symmetric]
  by (simp add: Spectral_Radius.spectrum_def hermitian_eigenvalues_real unfold_simps(2))

lemma leading_principal_submatrix_hermitian:
  assumes k: "k \<le> n"
  shows "hermitian (lps A k)" (is "hermitian ?A'")
proof-
  have "\<And>i j. i < dim_row ?A' \<Longrightarrow> j < dim_col ?A' \<Longrightarrow> ?A'$$(i,j) = conjugate (?A'$$(j,i))"
    using k A_dim A_herm
    by (metis (no_types, lifting) adjoint_eval carrier_matD(1) carrier_matD(2) dual_order.strict_trans1 hermitian_def leading_principal_submatrix_carrier leading_principal_submatrix_index)
  thus ?thesis
    using A_dim k
    by (metis (no_types, lifting) adjoint_dim_col adjoint_dim_row adjoint_eval carrier_matD(1) carrier_matD(2) eq_matI hermitian_def leading_principal_submatrix_carrier)
qed

lemma hermitian_mat_inv:
  assumes A'_dim: "A' \<in> carrier_mat n n"
  assumes inv: "inverts_mat A A'"
  shows "hermitian A'"
  using A_dim A_herm assms
  by (metis (no_types, lifting) ext adjoint_dim' adjoint_mult adjoint_one
      carrier_matD(1,2) hermitian_def invertible_det invertible_mat_def inverts_mat_def inverts_mat_sym
      square_mat.simps vec_space.det_nonzero_congruence)

lemma negative_hermitian: "hermitian (-A)"
  using A_dim A_herm
  by (metis hermitian_minus left_add_zero_mat minus_add_uminus_mat uminus_carrier_iff_mat zero_carrier_mat zero_hermitian)

lemma principal_submatrix_hermitian:
  assumes I: "I \<subseteq> {..<n}"
  shows "hermitian (submatrix A I I)" (is "hermitian ?B")
proof-
  have "square_mat ?B"
    using A_dim
    by (metis (full_types) carrier_matD(1) carrier_matD(2) dim_submatrix(1) dim_submatrix(2) square_mat.elims(1))
  moreover {
    fix i j assume *: "i < dim_row ?B \<and> j < dim_row ?B"
    then obtain i' j' where "?B$$(i,j) = A$$(i',j') \<and> i' = pick I i \<and> j' = pick I j"
      unfolding submatrix_def using A_dim pick_le by auto
    moreover then have "?B$$(j,i) = A$$(j',i')"
      unfolding submatrix_def
      using A_dim
      by (metis (no_types, lifting) Collect_cong * carrier_matD(1) carrier_matD(2) case_prod_conv dim_submatrix(1) index_mat(1))
    ultimately have "?B$$(i,j) = conjugate (?B$$(j,i))"
      using * A_herm by (metis dim_submatrix(1) hermitian_ij_ji_iff pick_le)
  }
  ultimately show ?thesis by (metis hermitian_ij_ji_iff)
qed

lemma hermitian_row_col:
  assumes "i < n"
  shows "row A i = conjugate (col A i)"
  using A_dim A_herm assms by (metis adjoint_row carrier_matD(2) hermitian_def)

lemma inner_prod_swap:
  assumes v: "v \<in> carrier_vec n"
  assumes w: "w \<in> carrier_vec n"
  shows "(A *\<^sub>v v) \<bullet>c w = v \<bullet>c (A *\<^sub>v w)"
proof-
  have "(A *\<^sub>v v) \<bullet>c w = v \<bullet>c (A\<^sup>H *\<^sub>v w)"
    using assms by (metis adjoint_def_alter adjoint_is_conjugate_transpose A_dim)
  also have "\<dots> = v \<bullet>c (A *\<^sub>v w)"
    using A_herm assms by (simp add: adjoint_is_conjugate_transpose hermitian_def)
  finally show ?thesis .
qed

end

section "Matrix Conjugate"

lemma conjugate_mat_dist:
  fixes A B :: "'a::conjugatable_ring mat"
  assumes "A \<in> carrier_mat m n"
  assumes "B \<in> carrier_mat n p"
  shows "(conjugate A) * (conjugate B) = conjugate (A * B)"
  using assms
  by (smt (z3) carrier_matD(1) carrier_matD(2) col_conjugate conjugate_scalar_prod dim_col dim_col_conjugate dim_row_conjugate eq_matI index_mult_mat(1) index_mult_mat(2) index_mult_mat(3) index_row(2) mat_index_conjugate row_conjugate)

lemma conjugate_mat_inv:
  fixes A :: "'a::{conjugatable_ring,semiring_1} mat"
  assumes "A \<in> carrier_mat n n"
  assumes "A' \<in> carrier_mat n n"
  assumes "inverts_mat A A'"
  shows "inverts_mat (conjugate A) (conjugate A')"
proof-
  have "(conjugate A) * (conjugate A') = conjugate (A * A')"
    using conjugate_mat_dist assms(1) assms(2) by blast
  also have "\<dots> = conjugate (1\<^sub>m n)"
    by (metis assms(1) assms(3) carrier_matD(1) inverts_mat_def)
  also have "\<dots> = 1\<^sub>m n"
    by (metis (no_types, lifting) carrier_matI conjugate_id conjugate_mat_dist dim_col_conjugate dim_row_conjugate index_one_mat(2) index_one_mat(3) left_mult_one_mat' right_mult_one_mat')
  finally show ?thesis
    by (metis index_mult_mat(2) index_one_mat(2) inverts_mat_def)
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

lemma conjugate_vec_first:
  assumes "v \<in> carrier_vec n"
  assumes "i \<le> n"
  shows "conjugate (vec_first v i) = vec_first (conjugate v) i"
  by (smt (verit, ccfv_SIG) assms carrier_vecD dim_vec_conjugate dim_vec_first eq_vecI index_vec le_less less_trans vec_first_def vec_index_conjugate)

lemma conjugate_vec_last: "i \<le> dim_vec v \<Longrightarrow> conjugate (vec_last v i) = vec_last (conjugate v) i"
  unfolding vec_last_def by auto

lemma cscalar_prod_symm_conj:
  "dim_vec (x::('a::{comm_semiring_0,conjugatable_ring} vec)) = dim_vec (y::'a vec)
    \<Longrightarrow> x \<bullet>c y = conjugate (y \<bullet>c x)"
  by (simp add: conjugate_scalar_prod scalar_prod_comm)

section "Block Matrix"

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
      also have "\<dots> = w\<^sub>n \<bullet> x\<^sub>n + a * b"
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
    also have "\<dots> = (\<Sum>i \<in> {0..<n\<^sub>u}. (vec_first x n\<^sub>u)$i * (conjugate u)$i)"
      using * by auto
    also have "\<dots> = (vec_first x (dim_vec u)) \<bullet>c u"
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
    also have "\<dots> = (\<Sum>i \<in> {0..<n-n\<^sub>u}. (vec_last x n\<^sub>v)$((i + n\<^sub>u) - (n - n\<^sub>v))
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
    also have "\<dots> = (\<Sum>i \<in> {0..<n\<^sub>u}. u$i * (vec_first (conjugate x) n\<^sub>u)$i)"
      using * by force
    also have "\<dots> = u \<bullet>c (vec_first x (dim_vec u))"
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
    also have "\<dots> = (\<Sum>i \<in> {0..<n-n\<^sub>u}. (vec_last (u @\<^sub>v v) n\<^sub>v)$((i + n\<^sub>u) - (n - n\<^sub>v))
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
    also have "\<dots> * ?R = four_block_mat A B C D"
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
    also have "\<dots> = M" unfolding M by simp
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

section "Positive Definite Matrix"

definition positive_definite :: "'a::{ord,conjugatable_field} mat \<Rightarrow> bool" where
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
        also have "\<dots> = (\<Sum>j \<in> {0..<n}. (row A i)$j * w$j)"
          by (metis (no_types, lifting) dim_vec scalar_prod_def sum.cong w_def)
        also have "\<dots> = (\<Sum>j \<in> {0..<k}. (row A i)$j * w$j) + (\<Sum>j \<in> {k..<n}. (row A i)$j * w$j)"
          by (simp add: assms(3) sum.atLeastLessThan_concat)
        also have "\<dots> = (\<Sum>j \<in> {0..<k}. (row A i)$j * v$j)"
          using 1 2 by auto
        also have "\<dots> = (\<Sum>j \<in> {0..<k}. (row B i)$j * v$j)"
          using *** by fastforce
        also have "\<dots> = (row B i) \<bullet> v"
          using B_carrier **** unfolding scalar_prod_def by blast
        also have "\<dots> = (B *\<^sub>v v)$i" using ** B_carrier by auto
        finally show "(A *\<^sub>v w)$i = (B *\<^sub>v v)$i" .
      qed
      have 5: "v \<in> carrier_vec k" by (simp add: "*"(1))
      hence 6: "B *\<^sub>v v \<in> carrier_vec k \<and> conjugate v \<in> carrier_vec k"
        by (metis B_def Matrix.carrier_vec_conjugate assms(1) assms(3) leading_principal_submatrix_carrier mult_mat_vec_carrier)
      have "QF A w = (A *\<^sub>v w) \<bullet>c w" by simp
      also have "\<dots> = (\<Sum>i \<in> {0..<n}. (A *\<^sub>v w)$i * conjugate (w$i))"
        by (smt (verit, ccfv_SIG) atLeastLessThan_iff dim_vec dim_vec_conjugate scalar_prod_def sum.cong vec_index_conjugate w_def)
      also have "\<dots> = (\<Sum>i \<in> {0..<k}. (A *\<^sub>v w)$i * conjugate (w$i))
          + (\<Sum>i \<in> {k..<n}. (A *\<^sub>v w)$i * conjugate (w$i))"
        by (simp add: assms(3) sum.atLeastLessThan_concat)
      also have "\<dots> = (\<Sum>i \<in> {0..<k}. (A *\<^sub>v w)$i * conjugate (w$i))" using 1 by simp
      also have "\<dots> = (\<Sum>i \<in> {0..<k}. (B *\<^sub>v v)$i * conjugate (v$i))" using 3 4 by force
      also have "\<dots> = (B *\<^sub>v v) \<bullet>c v"
        by (smt (verit, best) 5 6 atLeastLessThan_iff carrier_vecD scalar_prod_def sum.cong vec_index_conjugate)
      finally show ?thesis using quadratic_form_def by force
    qed
    ultimately have "QF B v > 0" by argo
  }
  thus ?thesis
    using assms hermitian_ij_ji_iff cmplx_herm_mat.leading_principal_submatrix_hermitian B_dims
    unfolding positive_definite_def B_def
    by (smt (verit, best) carrier_matD(1) leading_principal_submatrix_index order_less_le_trans square_mat.simps)
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

section "Matrix-Vector Multiplication"

(* This lemma is copy/pasted from Generalize Linear_Algebra_Complements.diagonal_unit_vec
   with only the type relaxed from complex to 'a::{ring,zero_neq_one} *)
lemma diagonal_unit_vec':
  assumes "B \<in> carrier_mat n n"
  assumes "diagonal_mat (B::'a::{ring,zero_neq_one} Matrix.mat)"
  shows "B *\<^sub>v (unit_vec n i) = B $$ (i,i)  \<cdot>\<^sub>v (unit_vec n i)"
proof -
  define v :: "'a Matrix.vec" where "v = unit_vec n i"
  have "B *\<^sub>v v = Matrix.vec n (\<lambda> i. Matrix.scalar_prod (Matrix.row B i) v)" 
    using assms unfolding mult_mat_vec_def by simp
  also have "\<dots> = Matrix.vec n (\<lambda> i. B $$(i,i) * Matrix.vec_index v i)" 
  proof -
    have "\<forall>i < n. (Matrix.scalar_prod (Matrix.row B i) v = B $$(i,i) * Matrix.vec_index v i)"
    proof (intro allI impI)
      fix i
      assume "i < n"
      have "(Matrix.scalar_prod (Matrix.row B i) v) = 
        (\<Sum> j \<in> {0 ..< n}. Matrix.vec_index (Matrix.row B i) j * Matrix.vec_index v j)" using assms
        unfolding Matrix.scalar_prod_def v_def by simp
      also have "\<dots> = Matrix.vec_index (Matrix.row B i) i * Matrix.vec_index v i" 
      proof (rule sum_but_one)
        show "\<forall>j < n. j \<noteq> i \<longrightarrow> Matrix.vec_index (Matrix.row B i) j = 0"
        proof (intro allI impI)
          fix j
          assume "j < n" and "j \<noteq> i"
          hence "Matrix.vec_index (Matrix.row B i) j = B $$ (i,j)" using \<open>i < n\<close> \<open>j < n\<close> assms 
            by auto
          also have "\<dots> = 0" using assms \<open>i < n\<close> \<open>j < n\<close> \<open>j\<noteq> i\<close> unfolding diagonal_mat_def by simp
          finally show "Matrix.vec_index (Matrix.row B i) j = 0" .
        qed
        show "i < n" using \<open>i < n\<close> .
      qed
      also have "\<dots> = B $$(i,i) * Matrix.vec_index v i" using assms \<open>i < n\<close> by auto
      finally show "(Matrix.scalar_prod (Matrix.row B i) v) = B $$(i,i) * Matrix.vec_index v i" .
    qed
    thus ?thesis by auto
  qed
  also have "... = B $$ (i,i)  \<cdot>\<^sub>v v" unfolding v_def unit_vec_def by auto
  finally have "B *\<^sub>v v = B $$ (i,i)  \<cdot>\<^sub>v v" .
  thus ?thesis unfolding v_def by simp
qed

lemma mat_vec_idx_disjunct_eq_zero:
  assumes A: "A \<in> carrier_mat m n"
  assumes x: "x \<in> carrier_vec n"
  assumes some_zero: "\<forall>j < n. (row A i)$j = 0 \<or> x$j = 0"
  assumes i: "i < m"
  shows "(A *\<^sub>v x)$i = 0"
proof-
  have dim_x: "dim_vec x = n" using x by simp
  have dim_A: "dim_row A = m" "dim_col A = n" using A by blast+
  have all_zero: "\<forall>j < n. (row A i)$j * x$j = 0" using some_zero by fastforce

  have "(A *\<^sub>v x)$i = (row A i) \<bullet> x" by (rule index_mult_mat_vec, subst dim_A(1), rule i)
  also have "\<dots> = (\<Sum>j < n. (row A i)$j * x$j)"
    unfolding scalar_prod_def dim_x using atLeast0LessThan by presburger
  also have "\<dots> = 0" using all_zero by simp
  finally show ?thesis .
qed

section "Module Span"

context module
begin

lemma mk_coeffs_of_list:
  assumes "\<alpha> \<in> (set A \<rightarrow> carrier R)"
  shows "\<exists>c \<in> {0..<length A} \<rightarrow> carrier R. \<forall>v \<in> set A. mk_coeff A c v = \<alpha> v"
  using assms
proof(induct "length A" arbitrary: A)
  case 0
  thus ?case by fastforce
next
  case (Suc n)
  then obtain a A' where a: "A = A' @ [a]" by (metis length_Suc_conv_rev)
  hence "\<alpha> \<in> (set A' \<rightarrow> carrier R)" using Suc.prems by simp
  moreover from a have len_A': "n = length A'" using Suc(2) by auto
  ultimately obtain c' where c':
      "c' \<in> {0..<length A'} \<rightarrow> carrier R \<and> (\<forall>v \<in> set A'. mk_coeff A' c' v = \<alpha> v)"
    using Suc.hyps by blast

  have len_A'_A: "length A' = length A - 1" using Suc(2) len_A' by presburger
  moreover have "[0..<length A] = [0..<length A - 1] @ [length A - 1]"
    by (metis Suc(2) calculation len_A' upt_Suc_append zero_order(1))
  ultimately have A_A'_int: "[0..<length A] = [0..<length A'] @ [length A']" by presburger
  show ?case
  proof(cases "a \<in> set A'")
    case True
    hence A_A': "set A = set A'" using a by auto
    define c where "c \<equiv> (\<lambda>i. if i \<in> {0..<length A'} then c' i else \<zero>)"
    hence c_carrier: "c \<in> {0..<length A} \<rightarrow> carrier R" using c' by force
    moreover have "\<forall>v \<in> set A. mk_coeff A c v = \<alpha> v"
    proof
      fix v assume *: "v \<in> set A"
      show "mk_coeff A c v = \<alpha> v"
      proof(cases "v = a")
        case True
        hence "find_indices v A = (find_indices v A') @ [length A - 1]" 
        proof-
          from A_A'_int have "find_indices v A
              = (filter (\<lambda>i. A ! i = v) [0..<length A']) @ (filter (\<lambda>i. A ! i = v) [length A'])"
            unfolding find_indices_def by (metis Suc.hyps(2) filter_append len_A')
          moreover then have "(filter (\<lambda>i. A ! i = v) [0..<length A']) = (find_indices v A')"
            using a by auto
          moreover have "filter (\<lambda>i. A ! i = v) [length A'] = [length A']" by (simp add: True a)
          ultimately show ?thesis using len_A'_A by argo
        qed
        hence "map c (find_indices v A) = (map c (find_indices v A')) @ [c (length A - 1)]"
          by auto
        hence "foldr (\<oplus>) (map c (find_indices v A)) \<zero>
            = foldr (\<oplus>) (map c (find_indices v A')) (\<zero> \<oplus> c (length A - 1))"
          by (simp add: c_def len_A'_A)
        also have "\<dots> = (foldr (\<oplus>) (map c (find_indices v A')) \<zero>) \<oplus> c (length A - 1)"
          by (metis R.sumlist_def R.zero_closed c_carrier atLeastLessThan_iff c_def calculation cring_simprules(16) len_A'_A less_irrefl_nat mk_coeff_carrier mk_coeff_def)
        finally have "mk_coeff A c v = mk_coeff A' c v \<oplus> c (length A - 1)"
          unfolding mk_coeff_def R.sumlist_def .
        moreover have "c (length A - 1) = \<zero>" unfolding c_def using len_A' a by force
        moreover have "mk_coeff A' c v \<in> carrier R"
          by (smt (verit) Pi_iff c' c_def mk_coeff_carrier)
        ultimately have "mk_coeff A c v = mk_coeff A' c v" by algebra
        moreover have "mk_coeff A' c v = mk_coeff A' c' v"
          unfolding mk_coeff_def find_indices_def
          by (metis (mono_tags, lifting) c_def list.map_cong mem_Collect_eq set_filter set_upt)
        ultimately show ?thesis by (metis "*" A_A' c')
      next
        case v_neq_a: False
        hence "find_indices v A = find_indices v A'"
        proof-
          from A_A'_int have "find_indices v A
              = (filter (\<lambda>i. A ! i = v) [0..<length A']) @ (filter (\<lambda>i. A ! i = v) [length A'])"
            unfolding find_indices_def by (metis Suc.hyps(2) filter_append len_A')
          moreover have "(filter (\<lambda>i. A ! i = v) [0..<length A']) = find_indices v A'"
            unfolding find_indices_def
            by (smt (verit, ccfv_SIG) a append.right_neutral calculation filter.simps(1) filter.simps(2) filter_cong find_indices_def find_indices_snoc nth_append_length v_neq_a)
          moreover have "(filter (\<lambda>i. A ! i = v) [length A']) = []" using a v_neq_a by auto
          ultimately show ?thesis by force
        qed
        hence "mk_coeff A c v = mk_coeff A' c v" unfolding mk_coeff_def by fastforce
        also have "\<dots> = mk_coeff A' c' v"
          unfolding mk_coeff_def find_indices_def c_def
          by (smt (verit, best) atLeastLessThan_upt list.map_cong mem_Collect_eq set_filter)
        also have "\<dots> = \<alpha> v" using c' * A_A' by blast
        finally show ?thesis .
      qed
    qed
    ultimately show ?thesis by blast
  next
    case False
    hence A_A': "set A' = set A - {a}" by (simp add: a)
    define c where "c \<equiv> (\<lambda>i. if i \<in> {0..<length A'} then c' i else \<alpha> a)"
    hence "c \<in> {0..<length A} \<rightarrow> carrier R" using Suc.prems a c' by fastforce
    moreover have "\<forall>v \<in> set A. mk_coeff A c v = \<alpha> v"
    proof
      fix v assume *: "v \<in> set A"
      show "mk_coeff A c v = \<alpha> v"
      proof(cases "v = a")
        case v_eq_a: True
        hence "filter (\<lambda>i. A ! i = v) [0..<length A] = [length A - 1]"
        proof-
          from A_A'_int have "filter (\<lambda>i. A ! i = v) [0..<length A]
              = (filter (\<lambda>i. A ! i = v) [0..<length A']) @ (filter (\<lambda>i. A ! i = v) [length A'])"
            by (metis Suc.hyps(2) filter_append len_A')
          moreover have "(filter (\<lambda>i. A ! i = v) [0..<length A']) = []"
          proof-
            have "\<And>i. i < length A' \<Longrightarrow> A!i \<noteq> v" by (metis False a nth_append nth_mem v_eq_a)
            thus ?thesis by fastforce
          qed
          moreover have "(filter (\<lambda>i. A ! i = v) [length A']) = [length A']" by (simp add: a v_eq_a)
          ultimately show ?thesis by (metis Suc.hyps(2) diff_Suc_1 len_A' self_append_conv2)
        qed
        hence "map c (filter (\<lambda>i. A ! i = v) [0..<length A]) = [c (length A')]"
          by (metis len_A' Suc.hyps(2) diff_Suc_1 list.map(1) list.map(2))
        moreover have "c (length A') = \<alpha> v" by (simp add: v_eq_a c_def)
        ultimately have "mk_coeff A c v = \<alpha> v \<oplus> \<zero>" unfolding mk_coeff_def find_indices_def by force
        moreover have "\<alpha> v \<in> carrier R" using "*" Suc(3) by blast
        ultimately show ?thesis by auto
      next (* copied exactly from the other v_neq_a case *)
        case v_neq_a: False
        hence "find_indices v A = find_indices v A'"
        proof-
          from A_A'_int have "find_indices v A
              = (filter (\<lambda>i. A ! i = v) [0..<length A']) @ (filter (\<lambda>i. A ! i = v) [length A'])"
            unfolding find_indices_def by (metis Suc.hyps(2) filter_append len_A')
          moreover have "(filter (\<lambda>i. A ! i = v) [0..<length A']) = find_indices v A'"
            unfolding find_indices_def
            by (smt (verit, ccfv_SIG) a append.right_neutral calculation filter.simps(1) filter.simps(2) filter_cong find_indices_def find_indices_snoc nth_append_length v_neq_a)
          moreover have "(filter (\<lambda>i. A ! i = v) [length A']) = []" using a v_neq_a by auto
          ultimately show ?thesis by force
        qed
        hence "mk_coeff A c v = mk_coeff A' c v" unfolding mk_coeff_def by fastforce
        also have "\<dots> = mk_coeff A' c' v"
          unfolding mk_coeff_def find_indices_def c_def
          by (smt (verit, best) atLeastLessThan_upt list.map_cong mem_Collect_eq set_filter)
        also have "\<dots> = \<alpha> v" by (metis c' * a insert_iff v_neq_a vec_space.append_insert)
        finally show ?thesis .
      qed
    qed
    ultimately show ?thesis by blast
  qed
qed

lemma span_list_span:
  assumes "set A \<subseteq> carrier M"
  shows "span_list A = span (set A)"
proof-
  have "span_list A \<subseteq> span (set A)"
  proof(rule subsetI)
    fix x assume "x \<in> span_list A"
    then obtain c where c: "x = lincomb_list c A \<and> c \<in> {0..<length A} \<rightarrow> carrier R"
      unfolding span_list_def by blast
    hence 1: "lincomb_list c A = lincomb (mk_coeff A c) (set A)"
      using lincomb_list_as_lincomb[OF assms(1)] by presburger
    have "mk_coeff A c \<in> (set A) \<rightarrow> carrier R" by (simp add: c mk_coeff_carrier)
    hence 2: "lincomb (mk_coeff A c) (set A) \<in> span (set A)" unfolding span_def by blast
    show "x \<in> span (set A)" using 1 2 c by argo
  qed
  moreover have "span (set A) \<subseteq> span_list A"
  proof(rule subsetI)
    fix x assume *: "x \<in> span (set A)"
    then obtain \<alpha> where \<alpha>: "x = lincomb \<alpha> (set A) \<and> \<alpha> \<in> (set A \<rightarrow> carrier R)"
      using * finite_span assms by auto
    define \<alpha>' where "\<alpha>' = (\<lambda>v. if v \<in> set A then \<alpha> v else \<zero>)"
    hence \<alpha>_\<alpha>': "\<And>v. v \<in> set A \<Longrightarrow> \<alpha> v = \<alpha>' v" by presburger
    hence x_\<alpha>': "x = lincomb \<alpha>' (set A)"
      using \<alpha>
      unfolding lincomb_def
      by (smt (verit) M.add.finprod_cong' Pi_iff assms basic_trans_rules(31) carrier_is_submodule submoduleE(4))
    have 1: "\<alpha>' \<in> (set A \<rightarrow> carrier R)" by (simp add: Pi_cong \<alpha> \<alpha>'_def)
    then obtain c where c: "c \<in> {0..<length A} \<rightarrow> carrier R \<and> (\<forall>v \<in> set A. mk_coeff A c v = \<alpha>' v)"
      using mk_coeffs_of_list by blast
    have "mk_coeff A c = \<alpha>'" unfolding \<alpha>'_def by (metis mk_coeff_0 c \<alpha>_\<alpha>')
    hence "lincomb \<alpha>' (set A) = lincomb_list c A"
        using lincomb_list_as_lincomb[OF assms(1), of c] c by argo
    also have "\<dots> \<in> span_list A" using c in_span_listI by blast
    finally show "x \<in> span_list A" using x_\<alpha>' by blast
  qed
  ultimately show ?thesis by blast
qed

end

section "Module Homomorphism, Linear Combination, and Span"

context mod_hom
begin

lemma lincomb_list_distrib:
  assumes "set S \<subseteq> carrier M"
  assumes "\<alpha> \<in> {..<length S} \<rightarrow> carrier R"
  shows "f (M.lincomb_list \<alpha> S) = N.lincomb_list \<alpha> (map f S)"
  using assms
proof(induct "length S" arbitrary: S \<alpha>)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then obtain v S' where v: "S = v # S'" by (metis length_Suc_conv)
  have 1: "n = length S'" using Suc(2) v by auto
  have 2: "set S' \<subseteq> carrier M" using Suc(3) v by auto
  have 3: "(\<alpha> \<circ> Suc) \<in> {..<length S'} \<rightarrow> carrier R" using "1" Suc(4) Suc.hyps(2) by fastforce
  
  have ih: "f (M.lincomb_list (\<alpha> \<circ> Suc) S') = N.lincomb_list (\<alpha> \<circ> Suc) (map f S')"
    using Suc.hyps(1)[OF 1 2 3] .
  
  have *: "M.lincomb_list \<alpha> (v # S') = (\<alpha> 0 \<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (M.lincomb_list (\<alpha> \<circ> Suc) S')"
    using M.lincomb_list_Cons .
  have "v \<in> carrier M" using Suc.prems(1) v by force
  moreover have "\<alpha> 0 \<in> carrier R" using Suc(4) Suc.hyps(2) by auto
  ultimately have "\<alpha> 0 \<odot>\<^bsub>M\<^esub> v \<in> carrier M" by blast
  moreover have "M.lincomb_list (\<alpha> \<circ> Suc) S' \<in> carrier M"
    by (metis (no_types, lifting) "1" "2" M.lincomb_list_carrier Pi_iff Suc(4) Suc.hyps(2) Suc_less_eq atLeastLessThan_iff lessThan_iff o_apply)
  ultimately have "f (M.lincomb_list \<alpha> S) = (f (\<alpha> 0 \<odot>\<^bsub>M\<^esub> v)) \<oplus>\<^bsub>N\<^esub> (f (M.lincomb_list (\<alpha> \<circ> Suc) S'))"
    using f_hom * v unfolding module_hom_def by force
  also have "\<dots> = (\<alpha> 0 \<odot>\<^bsub>N\<^esub> f v) \<oplus>\<^bsub>N\<^esub> (f (M.lincomb_list (\<alpha> \<circ> Suc) S'))"
    by (simp add: \<open>\<alpha> 0 \<in> carrier R\<close> \<open>v \<in> carrier M\<close>)
  also have "\<dots> = (\<alpha> 0 \<odot>\<^bsub>N\<^esub> f v) \<oplus>\<^bsub>N\<^esub> (N.lincomb_list (\<alpha> \<circ> Suc) (map f S'))" using ih by argo
  also have "\<dots> = N.lincomb_list \<alpha> (map f S)"
    using N.lincomb_list_Cons by (simp add: v)
  finally show ?case .
qed

lemma lincomb_distrib:
  assumes "inj_on f S"
  assumes "S \<subseteq> carrier M"
  assumes "\<alpha> \<in> S \<rightarrow> carrier R"
  assumes "\<forall>v \<in> S. \<alpha> v = \<beta> (f v)"
  assumes "finite S"
  shows "f (M.lincomb \<alpha> S) = N.lincomb \<beta> (f`S)"
proof-
  let ?\<alpha>' = "(\<lambda>v. (\<alpha> v) \<odot>\<^bsub>M\<^esub> v)"
  let ?\<beta>' = "(\<lambda>v. (\<beta> v) \<odot>\<^bsub>N\<^esub> v)"
  have *: "?\<alpha>' \<in> S \<rightarrow> carrier M" using assms(2,3) by auto
  have "f (M.lincomb \<alpha> S) = f (finsum M ?\<alpha>' S)" using M.lincomb_def by presburger
  also have "\<dots> = (\<Oplus>\<^bsub>N\<^esub>a\<in>S. f ((\<alpha> a) \<odot>\<^bsub>M\<^esub> a))" using hom_sum[OF assms(2) *] .
  also have "\<dots> = (\<Oplus>\<^bsub>N\<^esub>a\<in>S. (\<alpha> a) \<odot>\<^bsub>N\<^esub> (f a))"
  proof-
    have "\<forall>a \<in> S. a \<in> carrier M" using assms(2) by fastforce
    moreover have "\<forall>a \<in> S. \<alpha> a \<in> carrier R" using assms(3) by blast
    ultimately show ?thesis
      using f_hom unfolding module_hom_def by (simp add: N.M.add.finprod_cong')
  qed
  also have "\<dots> = (\<Oplus>\<^bsub>N\<^esub>a\<in>S. (\<beta> (f a)) \<odot>\<^bsub>N\<^esub> (f a))"
    by (smt (verit, del_insts) N.M.add.finprod_cong' M.summands_valid PiE Pi_I assms(2-4) basic_trans_rules(31) f_im f_smult)
  also have "\<dots> = (\<Oplus>\<^bsub>N\<^esub>a\<in>(f`S). (?\<beta>' a))"
    by (smt (verit, best) assms(1,4) M.summands_valid N.M.add.finprod_cong' N.M.add.finprod_reindex PiE Pi_I assms(2) assms(3) assms(4) basic_trans_rules(31) f_im f_smult imageE)
  also have "\<dots> = N.lincomb \<beta> (f`S)" using N.lincomb_def by presburger
  finally show ?thesis .
qed

lemma lincomb_distrib_obtain:
  assumes "inj_on f S"
  assumes "S \<subseteq> carrier M"
  assumes "\<alpha> \<in> S \<rightarrow> carrier R"
  assumes "\<forall>v \<in> S. \<alpha> v = \<beta> (f v)"
  assumes "finite S"
  obtains \<beta> where "(\<forall>v \<in> S. \<alpha> v = \<beta> (f v)) \<and> f (M.lincomb \<alpha> S) = N.lincomb \<beta> (f`S)"
proof-
  obtain \<beta> where \<beta>: "\<forall>v \<in> S. \<alpha> v = \<beta> (f v)"
  proof-
    let ?\<beta> = "\<lambda>y. \<alpha> (THE x. x \<in> S \<and> f x = y)"
    have "\<forall>v \<in> S. \<alpha> v = ?\<beta> (f v)"
    proof
      fix v assume "v \<in> S"
      then have "v = (THE x. x \<in> S \<and> f x = f v)"
        using assms(1) by (simp add: inj_on_def the_equality)
      thus "\<alpha> v = ?\<beta> (f v)" by argo
    qed
    thus ?thesis using that by fast
  qed
  thus ?thesis using lincomb_distrib that assms by blast
qed

lemma image_span_list:
  assumes "set vs \<subseteq> carrier M"
  shows "f`(M.span_list vs) = N.span_list (map f vs)" (is "?lhs = ?rhs")
proof-
  have "?lhs \<subseteq> ?rhs"
  proof(rule subsetI)
    fix w assume "w \<in> ?lhs"
    then obtain v where v: "v \<in> M.span_list vs \<and> f v = w" by blast
    then obtain \<alpha> where \<alpha>: "v = M.lincomb_list \<alpha> vs \<and> \<alpha> \<in> {..<length vs} \<rightarrow> carrier R"
      unfolding M.span_list_def by fastforce
    hence "f v = N.lincomb_list \<alpha> (map f vs)" using lincomb_list_distrib[OF assms(1)] v by blast
    thus "w \<in> ?rhs" using v \<alpha> unfolding N.span_list_def by force
  qed
  moreover have "?rhs \<subseteq> ?lhs"
  proof(rule subsetI)
    fix w assume "w \<in> ?rhs"
    then obtain \<alpha> where \<alpha>: "w = N.lincomb_list \<alpha> (map f vs) \<and> \<alpha> \<in> {..<length vs} \<rightarrow> carrier R"
      unfolding N.span_list_def by fastforce
    hence "w = f (M.lincomb_list \<alpha> vs)"
      using lincomb_list_distrib[OF assms] by presburger
    thus "w \<in> ?lhs" using \<alpha> unfolding M.span_list_def by fastforce
  qed
  ultimately show ?thesis by blast
qed

lemma image_span:
  assumes "finite vs"
  assumes "vs \<subseteq> carrier M"
  shows "f`(M.span vs) = N.span (f`vs)"
proof-
  obtain vs_list where vs_list: "set vs_list = vs" using assms(1) finite_list by blast
  have "f`vs = set (map f vs_list)" using vs_list by simp
  hence "N.span (f`vs) = N.span_list (map f vs_list)"
    by (metis N.span_list_span M.sum_simp assms(2) f_im image_subset_iff)
  moreover have "M.span vs = M.span_list vs_list"
    using M.span_list_span vs_list assms(2) by presburger
  ultimately show ?thesis using image_span_list assms vs_list by presburger
qed

lemma submodule_image:
  assumes "submodule R M' M"
  shows "submodule R (f`M') N"
  using assms
  by (smt (verit, ccfv_threshold) submodule_def N.module_axioms f0_is_0 f_add f_im f_smult
      imageE rev_image_eqI subset_iff)

lemma submodule_restrict:
  assumes "submodule R M' M"
  shows "mod_hom R (M.md M') (N.md (f`M')) f"
proof-
  interpret M': module R "M.md M'" by (simp add: M.submodule_is_module assms)
  interpret N': module R "N.md (f`M')" by (rule submodule_is_module, rule submodule_image[OF assms])
  have "f \<in> module_hom R (M.md M') (N.md (f`M'))"
    by (simp add: module_hom_def, meson M'.sum_simp assms f_add f_smult submodule.subset)
  thus ?thesis
    apply (simp add: mod_hom_def mod_hom_axioms_def)
    using M'.module_axioms N'.module_axioms by blast
qed

end

section "Vector Summation"

lemma complex_vec_norm_sum:
  fixes x :: "complex vec"
  assumes "x \<in> carrier_vec n"
  shows "vec_norm x = csqrt ((\<Sum>i \<in> {..<n}. (cmod (x$i))^2))"
proof-
  have *: "\<And>i. i \<in> {..<n} \<Longrightarrow> (conjugate x)$i = conjugate (x$i)"
    using assms by auto
  have **: "\<And>i. i \<in> {..<n} \<Longrightarrow> (x$i) * conjugate (x$i) = (cmod (x$i))^2"
    using mult_conj_cmod_square by blast
  have "vec_norm x = csqrt (x \<bullet>c x)"
    by (simp add: vec_norm_def)
  also have "\<dots> = csqrt (\<Sum>i \<in> {..<n}. (x$i) * (conjugate x)$i)"
    by (metis assms atLeast0LessThan carrier_vecD dim_vec_conjugate scalar_prod_def)
  also have "\<dots> = csqrt (\<Sum>i \<in> {..<n}. (x$i) * conjugate (x$i))"
    by (simp add: *)
  also have "\<dots> = csqrt ((\<Sum>i \<in> {..<n}. (cmod (x$i))^2))" using ** by fastforce
  finally show ?thesis .
qed

lemma inner_prod_vec_sum:
  assumes "v \<in> carrier_vec n"
  assumes "w \<in> carrier_vec n"
  assumes "B \<subseteq> carrier_vec n"
  assumes "finite B"
  assumes "v = finsum_vec TYPE('a::conjugatable_ring) n (\<lambda>b. cs b \<cdot>\<^sub>v b) B"
  shows "inner_prod w v = (\<Sum>b \<in> B. cs b * inner_prod w b)"
proof-
  let ?vs = "\<lambda>b. cs b \<cdot>\<^sub>v b"
  let ?f = "\<lambda>i b. if i \<in> {..<n} then (?vs b)$i * (conjugate w)$i else 0"
  have f: "\<And>y. finite {x. ?f x y \<noteq> 0}"
  proof-
    fix y
    have "{x. ?f x y \<noteq> 0} \<subseteq> {..<n}" by (simp add: subset_eq)
    thus "finite {x. ?f x y \<noteq> 0}" using finite_nat_iff_bounded by blast
  qed
  have vs: "?vs \<in> B \<rightarrow> carrier_vec n" using assms(3) by force
  have b_scale: "\<And>i b. i \<in> {..<n} \<Longrightarrow> b \<in> B \<Longrightarrow> (?vs b)$i = cs b * b$i"
    using assms(3) by auto
  have assoc: "\<And>i b. (cs b * b$i) * (conjugate w)$i = cs b * (b$i * (conjugate w)$i)"
    using Groups.mult_ac(1) by blast

  have "inner_prod w v = (\<Sum>i \<in> {..<n}. v$i * (conjugate w)$i)"
    unfolding scalar_prod_def using atLeast0LessThan assms(2) by force
  moreover have "\<And>i. i \<in> {..<n} \<Longrightarrow> v$i = (\<Sum>b \<in> B. (?vs b)$i)"
    using index_finsum_vec[OF assms(4) _ vs] unfolding assms(5) by blast
  ultimately have "inner_prod w v = (\<Sum>i \<in> {..<n}. (\<Sum>b \<in> B. (?vs b)$i) * (conjugate w)$i)"
    by force
  also have "\<dots> = (\<Sum>i \<in> {..<n}. \<Sum>b \<in> B. (?vs b)$i * (conjugate w)$i)"
    by (simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>i \<in> {..<n}. \<Sum>b \<in> B. ?f i b)"
    by fastforce
  also have "\<dots> = Sum_any (\<lambda>i. \<Sum>b \<in> B. ?f i b)"
    using Sum_any.conditionalize[of "{..<n}" "\<lambda>i. (\<Sum>b \<in> B. ?f i b)"]
    by (smt (verit, ccfv_SIG) Sum_any.cong finite_nat_iff_bounded subset_eq sum.neutral)
  also have "\<dots> = (\<Sum>b \<in> B. (Sum_any (\<lambda>i. ?f i b)))"
    using Sum_any_sum_swap[OF assms(4) f, of "\<lambda>x. x"] .
  also have "\<dots> = (\<Sum>b \<in> B. (\<Sum>i \<in> {..<n}. (?vs b)$i * (conjugate w)$i))"
  proof-
    have "\<And>b. b \<in> B \<Longrightarrow> (\<Sum>i \<in> {..<n}. (?vs b)$i * (conjugate w)$i) = Sum_any (\<lambda>i. ?f i b)"
      using Sum_any.conditionalize[of "{..<n}"] by blast
    thus ?thesis by fastforce
  qed
  also have "\<dots> = (\<Sum>b \<in> B. (\<Sum>i \<in> {..<n}. (cs b * b$i) * (conjugate w)$i))"
    using b_scale by simp
  also have "\<dots> = (\<Sum>b \<in> B. (\<Sum>i \<in> {..<n}. cs b * (b$i * (conjugate w)$i)))"
    using assoc by force
  also have "\<dots> = (\<Sum>b \<in> B. cs b * (\<Sum>i \<in> {..<n}. b$i * (conjugate w)$i))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>b \<in> B. cs b * inner_prod w b)"
    unfolding scalar_prod_def using atLeast0LessThan assms(2) by force
  finally show ?thesis  .
qed

lemma sprod_vec_sum:
  assumes "v \<in> carrier_vec n"
  assumes "w \<in> carrier_vec n"
  assumes "B \<subseteq> carrier_vec n"
  assumes "finite B"
  assumes "v = finsum_vec TYPE('a::{comm_ring}) n (\<lambda>b. cs b \<cdot>\<^sub>v b) B"
  shows "w \<bullet> v = (\<Sum>b \<in> B. cs b * (w \<bullet> b))"
proof-
  let ?vs = "\<lambda>b. cs b \<cdot>\<^sub>v b"
  let ?f = "\<lambda>i b. if i \<in> {..<n} then (?vs b)$i * w$i else 0"
  have f: "\<And>y. finite {x. ?f x y \<noteq> 0}"
  proof-
    fix y
    have "{x. ?f x y \<noteq> 0} \<subseteq> {..<n}" by (simp add: subset_eq)
    thus "finite {x. ?f x y \<noteq> 0}" using finite_nat_iff_bounded by blast
  qed

  have vs: "?vs \<in> B \<rightarrow> carrier_vec n" using assms(3) by force
  have b_scale: "\<And>i b. i \<in> {..<n} \<Longrightarrow> b \<in> B \<Longrightarrow> (?vs b)$i = cs b * b$i"
    using assms(3) by auto
  have assoc: "\<And>i b. (cs b * b$i) * w$i = cs b * (b$i * w$i)"
    using Groups.mult_ac(1) by blast
  have B_dim: "\<And>b. b \<in> B \<Longrightarrow> dim_vec b = n"
    using assms(3) by fastforce

  have "w \<bullet> v = (\<Sum>i \<in> {..<n}. v$i * w$i)"
    unfolding scalar_prod_def using atLeast0LessThan[of n] assms(1)
    by (metis (no_types, lifting) Groups.mult_ac(2) carrier_vecD sum.cong)
  moreover have "\<And>i. i \<in> {..<n} \<Longrightarrow> v$i = (\<Sum>b \<in> B. (?vs b)$i)"
    using index_finsum_vec[OF assms(4) _ vs] unfolding assms(5) by blast
  ultimately have "w \<bullet> v = (\<Sum>i \<in> {..<n}. (\<Sum>b \<in> B. (?vs b)$i) * w$i)"
    by force
  also have "\<dots> = (\<Sum>i \<in> {..<n}. \<Sum>b \<in> B. (?vs b)$i * w$i)"
    by (simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>i \<in> {..<n}. \<Sum>b \<in> B. ?f i b)"
    by fastforce
  also have "\<dots> = Sum_any (\<lambda>i. \<Sum>b \<in> B. ?f i b)"
    using Sum_any.conditionalize[of "{..<n}" "\<lambda>i. (\<Sum>b \<in> B. ?f i b)"]
    by (smt (verit, ccfv_SIG) Sum_any.cong finite_nat_iff_bounded subset_eq sum.neutral)
  also have "\<dots> = (\<Sum>b \<in> B. (Sum_any (\<lambda>i. ?f i b)))"
    using Sum_any_sum_swap[OF assms(4) f, of "\<lambda>x. x"] .
  also have "\<dots> = (\<Sum>b \<in> B. (\<Sum>i \<in> {..<n}. (?vs b)$i * w$i))"
  proof-
    have "\<And>b. b \<in> B \<Longrightarrow> (\<Sum>i \<in> {..<n}. (?vs b)$i * w$i) = Sum_any (\<lambda>i. ?f i b)"
      using Sum_any.conditionalize[of "{..<n}"] by blast
    thus ?thesis by fastforce
  qed
  also have "\<dots> = (\<Sum>b \<in> B. (\<Sum>i \<in> {..<n}. (cs b * b$i) * w$i))"
    using b_scale by simp
  also have "\<dots> = (\<Sum>b \<in> B. (\<Sum>i \<in> {..<n}. cs b * (b$i * w$i)))"
    using assoc by force
  also have "\<dots> = (\<Sum>b \<in> B. cs b * (\<Sum>i \<in> {..<n}. b$i * w$i))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>b \<in> B. cs b * (\<Sum>i \<in> {..<n}. w$i * b$i))"
    by (metis (no_types, lifting) Groups.mult_ac(2) sum.cong)
  also have "\<dots> = (\<Sum>b \<in> B. cs b * (w \<bullet> b))"
    unfolding scalar_prod_def using atLeast0LessThan assms(3) B_dim by fastforce
  finally show ?thesis  .
qed

lemma mat_vec_mult_sum:
  assumes "v \<in> carrier_vec n"
  assumes "A \<in> carrier_mat n n"
  assumes "B \<subseteq> carrier_vec n"
  assumes "finite B"
  assumes "v = finsum_vec TYPE('a::comm_ring) n (\<lambda>b. cs b \<cdot>\<^sub>v b) B"
  shows "A *\<^sub>v v = finsum_vec TYPE('a::comm_ring) n (\<lambda>b. cs b \<cdot>\<^sub>v (A *\<^sub>v b)) B"
    (is "?lhs = ?rhs")
proof-
  have "\<And>i. i < n \<Longrightarrow> ?lhs$i = ?rhs$i"
  proof-
    fix i assume *: "i < n"
    let ?r = "row A i"
    have "?lhs$i = ?r \<bullet> v" using * assms(2) unfolding mult_mat_vec_def by simp
    also have "\<dots> = (\<Sum>b \<in> B. (cs b * (?r \<bullet> b)))"
      using sprod_vec_sum[OF assms(1) _ assms(3) assms(4) assms(5)] assms(2) by fastforce
    also have "\<dots> = (\<Sum>b \<in> B. (cs b * ((A *\<^sub>v b)$i)))"
      using * assms(2) unfolding mult_mat_vec_def by simp
    also have "\<dots> = (\<Sum>b \<in> B. ((cs b \<cdot>\<^sub>v (A *\<^sub>v b))$i))"
      using assms(2) * by force
    also have "\<dots> = (finsum_vec TYPE('a::comm_ring) n (\<lambda>b. cs b \<cdot>\<^sub>v (A *\<^sub>v b)) B)$i"
      using index_finsum_vec[OF assms(4) *]
      by (smt (verit, best) Pi_I assms(2) carrier_matD(1) carrier_vec_dim_vec dim_mult_mat_vec index_smult_vec(2) sum.cong)
    finally show "?lhs$i = ?rhs$i" by blast
  qed
  moreover have "?lhs \<in> carrier_vec n" using assms(1) assms(2) by force
  moreover have "?rhs \<in> carrier_vec n"
    by (smt (verit, ccfv_SIG) Pi_iff assms(2) assms(3) finsum_vec_closed mult_mat_vec_carrier smult_carrier_vec subsetD)
  ultimately show ?thesis by (metis (no_types, lifting) carrier_vecD eq_vecI)
qed

section "Vector Space"

context vectorspace
begin

lemma basis_subset_carrier: "basis B \<Longrightarrow> B \<subseteq> carrier V" by (simp add: basis_def)

lemma dim_of_lin_indpt_span:
  assumes li: "lin_indpt S"
  assumes carrier: "S \<subseteq> carrier V"
  assumes fin: "finite S"
  shows "vectorspace.dim K (vs (span S)) = card S"
  using dim_span[unfolded maximal_def, OF carrier fin] li
  by fast

lemma subspace_fin_dim:
  assumes W: "subspace K W V"
  assumes fin: "fin_dim"
  shows "vectorspace.fin_dim K (vs W)"
proof-
  have ?thesis if "{\<zero>\<^bsub>V\<^esub>} = W"
    using W that
    by (metis empty_subsetI finite.emptyI local.carrier_vs_is_self local.span_empty span_li_not_depend(1) subspace.submod
        subspace_is_vs vectorspace.fin_dim_def)
  moreover have ?thesis if *: "{\<zero>\<^bsub>V\<^esub>} \<noteq> W"
  proof-
    obtain b where b: "b \<in> W \<and> b \<noteq> \<zero>\<^bsub>V\<^esub>" using W * submodule_def subspace_def by blast
    let ?P = "\<lambda>B. B \<subseteq> W \<and> lin_indpt B"
    have "\<And>B. ?P B \<Longrightarrow> finite B \<and> card B \<le> dim"
      using W fin by (metis submodule_def subspace_def dual_order.trans li_le_dim(1,2))
    moreover have Pb: "?P {b}"
    proof-
      have "b \<notin> span {}" by (simp add: b local.span_empty)
      moreover have "{b} \<subseteq> carrier V" using b W[unfolded subspace_def submodule_def] by fast
      ultimately show ?thesis using lindep_span[of "{b}", simplified] b by blast
    qed
    ultimately obtain B where B: "finite B \<and> maximal B ?P" by (metis (no_types, lifting) maximal_exists)

    have "(\<lambda>S. S \<subseteq> W \<and> \<not> LinearCombinations.module.lin_dep K (vs W) S) = ?P"
      using B[unfolded maximal_def] span_li_not_depend(2) W by auto
    hence "vectorspace.basis K (vs W) B"
      using B vectorspace.max_li_is_basis[OF subspace_is_vs[OF W], of B, simplified] by argo
    thus ?thesis
      using B[unfolded maximal_def]
      unfolding vectorspace.fin_dim_def[OF subspace_is_vs[OF W]] vectorspace.basis_def[OF subspace_is_vs[OF W]]
      by auto
  qed
  ultimately show ?thesis by argo
qed

lemma nontriv_obtain:
  assumes "dim \<noteq> 0" "fin_dim"
  obtains v where "v \<in> carrier V" "v \<noteq> \<zero>\<^bsub>V\<^esub>"
proof-
  obtain B where B: "basis B \<and> 0 < card B" using assms dim_basis finite_basis_exists by force
  then obtain b where "b \<in> B \<and> b \<noteq> \<zero>\<^bsub>V\<^esub>"
    by (metis all_not_in_conv basis_def bot_nat_0.not_eq_extremum card_eq_0_iff vs_zero_lin_dep)
  thus ?thesis using that[of b] B[unfolded basis_def] by blast
qed                                          

lemma nontriv_subspace_obtain:
  assumes "subspace K W V"
  assumes "vectorspace.dim K (vs W) \<noteq> 0"
  assumes "fin_dim"
  obtains v where "v \<in> W" "v \<noteq> \<zero>\<^bsub>V\<^esub>"
  using assms vectorspace.nontriv_obtain[of K "vs W"] subspace_fin_dim subspace_is_vs by auto

lemma nontriv_exists:
  assumes "dim \<noteq> 0" "fin_dim"
  shows "\<exists>v \<in> carrier V. v \<noteq> \<zero>\<^bsub>V\<^esub>"
  using nontriv_obtain[OF assms] by metis

lemma nontriv_subspace_exists:
  assumes "subspace K W V"
  assumes "vectorspace.dim K (vs W) \<noteq> 0"
  assumes "fin_dim"
  shows "\<exists>v \<in> W. v \<noteq> \<zero>\<^bsub>V\<^esub>"
  using nontriv_subspace_obtain[OF assms] by metis

lemma dim_sum_nontriv_int:
  assumes W\<^sub>1: "subspace K W\<^sub>1 V"
  assumes W\<^sub>2: "subspace K W\<^sub>2 V"
  assumes dim: "dim < vectorspace.dim K (vs W\<^sub>1) + vectorspace.dim K (vs W\<^sub>2)"
  assumes fin: "fin_dim"
  shows "\<exists>v \<in> W\<^sub>1 \<inter> W\<^sub>2. v \<noteq> \<zero>\<^bsub>V\<^esub>"
proof-
  obtain B\<^sub>1 where B\<^sub>1: "vectorspace.basis K (vs W\<^sub>1) B\<^sub>1" "finite B\<^sub>1"
    using W\<^sub>1 fin subspace_fin_dim subspace_is_vs vectorspace.finite_basis_exists by blast
  obtain B\<^sub>2 where B\<^sub>2: "vectorspace.basis K (vs W\<^sub>2) B\<^sub>2" "finite B\<^sub>2"
    using W\<^sub>2 fin subspace_fin_dim subspace_is_vs vectorspace.finite_basis_exists by blast

  have basis_carriers: "B\<^sub>1 \<subseteq> carrier V" "B\<^sub>2 \<subseteq> carrier V"
    using B\<^sub>1 W\<^sub>1 unfolding vectorspace.basis_def[OF subspace_is_vs[OF W\<^sub>1]] subspace_def submodule_def
    using B\<^sub>2 W\<^sub>2 unfolding vectorspace.basis_def[OF subspace_is_vs[OF W\<^sub>2]] subspace_def submodule_def
    by auto

  show ?thesis
  proof(cases "B\<^sub>1 \<inter> B\<^sub>2 \<noteq> {}")
    case True
    then obtain b where "b \<in> B\<^sub>1 \<inter> B\<^sub>2" by blast
    hence "b \<in> W\<^sub>1 \<inter> W\<^sub>2 \<and> b \<noteq> \<zero>\<^bsub>V\<^esub>"
      using B\<^sub>1 B\<^sub>2 W\<^sub>1 W\<^sub>2
      using basic_trans_rules(31)[of B\<^sub>1 W\<^sub>1 b] basic_trans_rules(31)[of B\<^sub>2 W\<^sub>2 b] one_zeroI
        span_li_not_depend(2)[of B\<^sub>1 W\<^sub>1] subspace_is_vs[of W\<^sub>2] subspace_is_vs[of W\<^sub>1] vectorspace.basis_def[of K "vs W\<^sub>2" B\<^sub>2]
        vectorspace.basis_def[of K "vs W\<^sub>1" B\<^sub>1] zero_lin_dep[of B\<^sub>1]
      by force
    thus ?thesis by blast
  next
    case False
    hence card: "card (B\<^sub>1 \<union> B\<^sub>2) = card B\<^sub>1 + card B\<^sub>2" using B\<^sub>1(2) B\<^sub>2(2) card_Un_disjoint by blast
    hence not_li: "\<not> lin_indpt (B\<^sub>1 \<union> B\<^sub>2)"
      using li_le_dim(2)[OF fin, of "B\<^sub>1 \<union> B\<^sub>2"] B\<^sub>1 B\<^sub>2 basis_carriers dim
      unfolding vectorspace.dim_basis[OF subspace_is_vs[OF W\<^sub>1] B\<^sub>1(2) B\<^sub>1(1)]
      unfolding vectorspace.dim_basis[OF subspace_is_vs[OF W\<^sub>2] B\<^sub>2(2) B\<^sub>2(1)]
      by auto

    have "{} \<subseteq> B\<^sub>1 \<and> lin_indpt ({} \<union> B\<^sub>2)"
      by (metis B\<^sub>2(1) LinearCombinations.module.span_li_not_depend(2) LinearCombinations.submodule_def Un_empty_left
          VectorSpace.subspace_def W\<^sub>2 empty_subsetI local.module.carrier_vs_is_self subspace_is_vs vectorspace.basis_def)
    then obtain B\<^sub>1' where B\<^sub>1': "maximal B\<^sub>1' (\<lambda>B\<^sub>1'. B\<^sub>1' \<subseteq> B\<^sub>1 \<and> lin_indpt (B\<^sub>1' \<union> B\<^sub>2))"
      using B\<^sub>1(2) by (metis (no_types, lifting) maximal_exists_superset)

    have "B\<^sub>1' \<noteq> B\<^sub>1"
      using B\<^sub>1' not_li unfolding maximal_def by fastforce
    then obtain b\<^sub>1 where b\<^sub>1: "b\<^sub>1 \<in> B\<^sub>1 - B\<^sub>1'"
      using B\<^sub>1' by (metis (lifting) maximal_def psubsetI psubset_imp_ex_mem)
    let ?S = "B\<^sub>1' \<union> B\<^sub>2"

    have "lin_dep (?S \<union> {b\<^sub>1})" using b\<^sub>1 B\<^sub>1' unfolding maximal_def by auto
    hence b\<^sub>1_span: "b\<^sub>1 \<in> span ?S"
      using B\<^sub>1'[unfolded maximal_def]
      using lin_dep_iff_in_span[of ?S b\<^sub>1] basis_carriers False b\<^sub>1
      by blast
    also have "\<dots> = subspace_sum (span B\<^sub>1') (span B\<^sub>2)"
      using span_union_is_sum[of B\<^sub>1' B\<^sub>2] basis_carriers B\<^sub>1'[unfolded maximal_def] by force
    finally obtain v\<^sub>1' v\<^sub>2 where vs: "b\<^sub>1 = v\<^sub>1' \<oplus>\<^bsub>V\<^esub> v\<^sub>2 \<and> v\<^sub>1' \<in> span B\<^sub>1' \<and> v\<^sub>2 \<in> span B\<^sub>2"
      unfolding submodule_sum_def by fast

    have "v\<^sub>2 \<noteq> \<zero>\<^bsub>V\<^esub>"
    proof(rule ccontr, clarify)
      assume "v\<^sub>2 = \<zero>\<^bsub>V\<^esub>"
      hence "b\<^sub>1 \<in> span B\<^sub>1'" 
        using vs B\<^sub>1' basis_carriers(1)
        by (metis (no_types, lifting) M.add.r_one maximal_def span_closed subset_trans)
      moreover have "lin_indpt B\<^sub>1'"
        using B\<^sub>1' by (metis (lifting) Un_subset_iff maximal_def order.refl supset_ld_is_ld)
      moreover have "\<not> lin_dep (B\<^sub>1' \<union> {b\<^sub>1})"
      proof-
        have "B\<^sub>1' \<union> {b\<^sub>1} \<subseteq> B\<^sub>1"
          using B\<^sub>1' b\<^sub>1 by (metis (lifting) DiffE insert_subset insert_union maximal_def)
        thus ?thesis
          using B\<^sub>1[unfolded vectorspace.basis_def[OF subspace_is_vs[OF W\<^sub>1]]] W\<^sub>1
          by (metis VectorSpace.subspace_def local.module.carrier_vs_is_self span_li_not_depend(2) subset_li_is_li)
      qed
      ultimately show False
        using lin_dep_iff_in_span[of B\<^sub>1' b\<^sub>1] B\<^sub>1' b\<^sub>1 basis_carriers(1)
        by (metis (no_types, lifting) Diff_iff Set.basic_monos(7) basic_trans_rules(23) maximal_def)
    qed
    moreover have "b\<^sub>1 \<ominus>\<^bsub>V\<^esub> v\<^sub>1' = v\<^sub>2"
      using B\<^sub>1' b\<^sub>1_span basis_carriers vs
      by (smt (verit, ccfv_SIG) M.add.m_comm M.r_neg1 Un_least a_minus_def basic_trans_rules(23)
          local.span_neg maximal_def span_closed)
    moreover have "b\<^sub>1 \<ominus>\<^bsub>V\<^esub> v\<^sub>1' \<in> span B\<^sub>1"
    proof-
      have "v\<^sub>1' \<in> span B\<^sub>1"
        using vs B\<^sub>1' by (metis (no_types, lifting) maximal_def span_is_monotone subsetD)
      thus ?thesis
        using b\<^sub>1 basis_carriers calculation(2) vs by (metis Diff_iff local.span_add span_closed span_mem)
    qed
    moreover have "v\<^sub>2 \<in> span B\<^sub>2" using vs by fast
    ultimately have "v\<^sub>2 \<noteq> \<zero>\<^bsub>V\<^esub> \<and> v\<^sub>2 \<in> span B\<^sub>1 \<inter> span B\<^sub>2"
      by fastforce
    thus ?thesis
      using B\<^sub>1 B\<^sub>2 W\<^sub>1 W\<^sub>2
      by (metis is_module subspace_is_vs vectorspace.basis_def local.module.carrier_vs_is_self span_li_not_depend(1))
  qed
qed

end

section "Linear Map"

context linear_map
begin

lemma inj_image_lin_indpt:
  assumes "inj_on T (carrier V)"
  assumes "S \<subseteq> carrier V"
  assumes "V.module.lin_indpt S"
  assumes "finite S"
  shows "W.module.lin_indpt (T`S)"
proof(rule ccontr)
  assume "\<not> W.module.lin_indpt (T`S)"
  then obtain B \<beta> b where B: "finite B
      \<and> B \<subseteq> T`S
      \<and> (\<beta> \<in> (B \<rightarrow> carrier K))
      \<and> (lincomb \<beta> B = \<zero>\<^bsub>W\<^esub>)
      \<and> (b \<in> B)
      \<and> (\<beta> b \<noteq> \<zero>\<^bsub>K\<^esub>)"
    using W.module.lin_dep_def by auto
  define A where "A \<equiv> {a \<in> S. T a \<in> B}"
  define \<alpha> where "\<alpha> \<equiv> (\<lambda>v. \<beta> (T v))"
  have 1: "inj_on T A"
    by (metis (no_types, lifting) assms(1,2) inj_on_subset A_def mem_Collect_eq subsetI)
  have 2: "A \<subseteq> carrier V" using A_def assms(2) by blast
  have 3: "\<alpha> \<in> A \<rightarrow> carrier K"
  proof
    fix x assume "x \<in> A"
    moreover then have "T x \<in> carrier W" using 2 by blast
    ultimately show "\<alpha> x \<in> carrier K" unfolding \<alpha>_def using B  A_def by blast
  qed
  have 4: "\<forall>v\<in>A. \<alpha> v = \<beta> (T v)" using \<alpha>_def by blast
  have 5: "finite A" using A_def assms(4) by force
  have "B = T`A" unfolding A_def using B by blast
  hence "lincomb \<beta> B = T (V.module.lincomb \<alpha> A)" using lincomb_distrib[OF 1 2 3 4 5] by argo
  hence "T (V.module.lincomb \<alpha> A) = \<zero>\<^bsub>W\<^esub>" using B by argo
  moreover have "T (\<zero>\<^bsub>V\<^esub>) = \<zero>\<^bsub>W\<^esub>" by auto
  ultimately have *: "(V.module.lincomb \<alpha> A) = \<zero>\<^bsub>V\<^esub>" using assms(1) by (simp add: 2 3 inj_onD)
  moreover obtain a where "T a = b \<and> a \<in> A" using B \<open>B = T ` A\<close> by blast
  moreover then have "\<alpha> a \<noteq> \<zero>\<^bsub>K\<^esub>" by (simp add: B \<alpha>_def)
  moreover have "A \<subseteq> S" using A_def by blast
  ultimately show False using assms(3) 5 3 V.module.lin_dep_def by blast
qed

lemma subspace_restrict:
  assumes "subspace K V' V"
  shows "linear_map K (V.vs V') (W.vs (T`V')) T"
  using assms submodule_restrict[of V']
  by (simp add: field_axioms linear_map_def mod_hom.axioms(1,2) vectorspace_def) 

lemma subspace_image:
  assumes "subspace K V' V"
  shows "subspace K (T`V') W"
  using assms submodule_image[of V'] by (meson subspace_def W.vectorspace_axioms)

lemma inj_subspace_image:
  assumes inj: "inj_on T (carrier V)"
  assumes subspace: "subspace K V' V"
  assumes fin: "V.fin_dim"
  shows "vectorspace.dim K (W.vs (T`V')) = vectorspace.dim K (V.vs V')"
proof-
  interpret restrict: linear_map K "V.vs V'" "W.vs (T`V')" T using subspace_restrict[OF subspace] .
  have inj': "inj_on T (carrier (V.vs V'))"
    using inj subspace by (simp add: submodule_def VectorSpace.subspace_def inj_on_subset)
  have carrier_im: "T`carrier (V.vs V') = carrier (W.vs (T`V'))"
    using V.carrier_vs_is_self W.carrier_vs_is_self by presburger
  show ?thesis
    by (rule restrict.dim_eq[OF V.subspace_fin_dim[OF subspace fin] inj' carrier_im, symmetric])
qed

end

lemma linear_map_mat:
  assumes "A \<in> carrier_mat n m"
  shows "linear_map class_ring (module_vec TYPE('a::{field,ring_1}) m) (module_vec TYPE('a) n) ((*\<^sub>v) A)"
    (is "linear_map ?K ?V ?W ?T") 
proof-
  have "vectorspace ?K ?V" using VS_Connect.vec_vs[of "m"] by blast
  moreover have "vectorspace ?K ?W" using VS_Connect.vec_vs[of "n"] by blast
  moreover have "mod_hom ?K ?V ?W ?T"
  proof-
    have V: "module ?K ?V" by (simp add: vec_module)
    moreover have W: "module ?K ?W" by (simp add: vec_module)
    moreover have "?T \<in> LinearCombinations.module_hom ?K ?V ?W"
    proof-
      have "?T \<in> carrier ?V \<rightarrow> carrier ?W" by (metis Pi_I assms mult_mat_vec_carrier vec_space.cV)
      moreover have "\<forall>v\<^sub>1 \<in> carrier ?V. \<forall>v\<^sub>2 \<in> carrier ?V. ?T (v\<^sub>1 + v\<^sub>2) = ?T v\<^sub>1 + ?T v\<^sub>2"
        by (metis module_vec_def assms monoid_record_simps(1) mult_add_distrib_mat_vec)
      moreover have "\<forall>\<alpha> \<in> carrier ?K. \<forall>v \<in> carrier ?V. ?T (\<alpha> \<cdot>\<^sub>v v) = \<alpha> \<cdot>\<^sub>v (?T v)"
        by (metis assms mult_mat_vec vec_space.cV)
      ultimately show ?thesis unfolding module_vec_def module_hom_def by force
    qed
    ultimately show ?thesis
      unfolding mod_hom_def mod_hom_axioms_def by blast
  qed
  ultimately show ?thesis unfolding linear_map_def by blast
qed

section "Matrix as Linear Map"

locale mat_as_linear_map = 
  fixes A :: "'a::field mat"
  fixes m n
  assumes carrier: "A \<in> carrier_mat m n"
begin

abbreviation "V \<equiv> module_vec TYPE('a) n"

abbreviation "W \<equiv> module_vec TYPE('a) m"

sublocale linear_map class_ring V W "(*\<^sub>v) A"
  by (rule linear_map_mat[OF carrier])

abbreviation "f \<equiv> (*\<^sub>v) A"

end

section "Matrix Isometry"

locale isometry_mat = mat_as_linear_map A m n for A :: "complex mat" and m n +
  assumes isom: "A\<^sup>H * A = 1\<^sub>m n"
begin                         

lemma preserves_norm: "v \<in> carrier_vec n \<Longrightarrow> vec_norm v = vec_norm (f v)"
  by (metis adjoint_is_conjugate_transpose carrier inner_prod_mult_mat_vec_right isom one_mult_mat_vec
      vec_norm_def)

lemma is_inj: "inj_on f (carrier V)"
  by (smt (verit, ccfv_threshold) adjoint_dim' adjoint_is_conjugate_transpose assoc_mult_mat_vec carrier inj_on_def
      isom one_mult_mat_vec vec_space.cV)

end

section "Compression"

lemma compression_is_hermitian:
  assumes B: "B \<in> carrier_mat n m"
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "hermitian (B\<^sup>H * A * B)" "B\<^sup>H * A * B \<in> carrier_mat m m"
proof-
  have "((B\<^sup>H * A) * B)\<^sup>H = B\<^sup>H * (B\<^sup>H * A)\<^sup>H"
    using A(1) B
    by (metis adjoint_dim' adjoint_is_conjugate_transpose adjoint_mult mult_carrier_mat)
  also have "\<dots> = B\<^sup>H * (A\<^sup>H * B\<^sup>H\<^sup>H)"
    using A(1) assms(1)
    by (metis adjoint_dim' adjoint_is_conjugate_transpose adjoint_mult)
  also have "\<dots> = B\<^sup>H * A * B"
    using A B
    by (smt (verit, best) Matrix.transpose_transpose adjoint_dim' adjoint_is_conjugate_transpose
        assoc_mult_mat conjugate_id hermitian_def transpose_conjugate)
  finally show "hermitian (B\<^sup>H * A * B)"
    unfolding hermitian_def adjoint_is_conjugate_transpose[of "B\<^sup>H * A * B"] .
  show "B\<^sup>H * A * B \<in> carrier_mat m m"
    using A(1) B by (meson More_Matrix.carrier_vec_conjugate mult_carrier_mat transpose_carrier_mat)
qed

section "Submatrix"

subsection "Submatrix of Injective Function on Indices, as Compression"

text "Note, with this definition of submatrix, reordering the indices is possible."

definition submatrix_of_inj :: "'a mat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "submatrix_of_inj A f g m n \<equiv> mat m n (\<lambda>(i,j). A$$(f i, g j))"

lemma submatrix_of_inj_as_compression:
  fixes A :: "complex mat"
  fixes f :: "nat \<Rightarrow> nat"
  assumes A: "A \<in> carrier_mat n n"
  assumes f: "f : {..<m} \<rightarrow> {..<n}"
  assumes inj: "inj_on f {..<m}"
  defines "B \<equiv> submatrix_of_inj A f f m m"
  defines "(Q::complex mat) \<equiv> mat n m (\<lambda>(i,j). if i = f j then 1 else 0)"
  shows "B = Q\<^sup>H * A * Q" "isometry_mat Q n m" "Q \<in> carrier_mat n m"
proof-
  show dim: "Q \<in> carrier_mat n m" unfolding Q_def by simp
  note m_leq_n = card_inj[OF f inj, simplified]

  let ?\<phi> = "\<lambda>j k. if k = f j then 1 else 0"
  have *: "\<And>j. j < m \<Longrightarrow> (\<Sum>k<n. cnj (?\<phi> j k) * ?\<phi> j k) = 1"
  proof-
    fix j assume j: "j < m"
    have fj: "f j \<in> {..<n}" using f j by blast
    have "(\<Sum>k<n. cnj (?\<phi> j k) * ?\<phi> j k) = (\<Sum>k \<in> {..<n} - {f j}. cnj (?\<phi> j k) * ?\<phi> j k) + (cnj (?\<phi> j (f j)) * ?\<phi> j (f j))"
      using fj by (subst sum_diff1, simp_all)
    thus "(\<Sum>k<n. cnj (?\<phi> j k) * ?\<phi> j k) = 1" by simp
  qed

  have "\<And>i j k. i < m \<Longrightarrow> j < m \<Longrightarrow> i \<noteq> j \<Longrightarrow> k < n \<Longrightarrow> cnj (?\<phi> i k) * ?\<phi> j k = 0"
    using inj by (simp add: inj_on_eq_iff)
  hence **: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> i \<noteq> j \<Longrightarrow> (\<Sum>k<n. cnj (?\<phi> i k) * ?\<phi> j k) = 0"
    by (meson lessThan_iff sum.not_neutral_contains_not_neutral)

  have "Q\<^sup>H * Q = 1\<^sub>m m"
    by (rule eq_matI, auto simp: Q_def m_leq_n * **)
  thus "isometry_mat Q n m"
    using dim isometry_mat_axioms_def[of Q m] mat_as_linear_map.intro[of Q n m]
    unfolding isometry_mat_def
    by blast

  have "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> row (Q\<^sup>H * A) i $ (f j) = A$$(f i, f j)"
  proof-
    fix i j assume i: "i < m" and j: "j < m"
    have fj: "f j < n" using f j m_leq_n by blast
    have "row (Q\<^sup>H * A) i $ (f j) = row A (f i) $ (f j)"
      using i fj A f sum_diff1[of "{..<n}" "\<lambda>k. cnj (if k = f i then 1 else 0) * A $$ (k, f j)" "f i"]
      by (subst adjoint_is_conjugate_transpose) (force simp: Q_def row_def adjoint_def)
    thus "row (Q\<^sup>H * A) i $ (f j) = A$$(f i, f j)"
      using A fj by (metis carrier_matD(2) index_vec row_def)
  qed
  hence "\<And>i j k. i < m \<Longrightarrow> j < m \<Longrightarrow> k < n \<Longrightarrow> row (Q\<^sup>H * A) i $ k * col Q j $ k = (if k = f j then A$$(f i, f j) else 0)"
    unfolding Q_def row_def col_def times_mat_def scalar_prod_def by force
  hence *: "\<And>i j. i < dim_row Q\<^sup>H \<Longrightarrow> j < dim_col Q \<Longrightarrow> B $$ (i, j) = row (Q\<^sup>H * A) i \<bullet> col Q j"
    using dim m_leq_n f by (auto simp: scalar_prod_def B_def submatrix_of_inj_def)

  show "B = Q\<^sup>H * A * Q"
    apply (rule eq_matI, simp add: *)
    using dim A by (simp add: B_def submatrix_of_inj_def)+
qed

lemma submatrix_of_inj_as_compression_obt:
  fixes A :: "complex mat"
  fixes f :: "nat \<Rightarrow> nat"
  assumes A: "A \<in> carrier_mat n n"
  assumes f: "f : {..<m} \<rightarrow> {..<n}"
  assumes inj: "inj_on f {..<m}"
  defines "B \<equiv> submatrix_of_inj A f f m m"
  obtains Q where "B = Q\<^sup>H * A * Q" "isometry_mat Q n m" "Q \<in> carrier_mat n m"
  using submatrix_of_inj_as_compression[OF assms(1-3), folded B_def] by blast

subsection "Submatrix of @{const pick} Function, as Compression"

lemma submatrix_inj:
  assumes A: "A \<in> carrier_mat m n"
  assumes I: "I \<subseteq> {..<m}"
  assumes J: "J \<subseteq> {..<n}"
  defines "m' \<equiv> card I"
  defines "n' \<equiv> card J"
  defines "B \<equiv> submatrix A I J"
  defines "f \<equiv> \<lambda>i. pick I i"
  defines "g \<equiv> \<lambda>j. pick J j"
  shows "f : {..<m'} \<rightarrow> {..<m}" "g : {..<n'} \<rightarrow> {..<n}"
        "inj_on f {..<m'}" "inj_on g {..<n'}"
        "B = submatrix_of_inj A f g m' n'"
proof-
  show "f : {..<m'} \<rightarrow> {..<m}" unfolding f_def m'_def using I(1) pick_in_set_le by fastforce
  show "g : {..<n'} \<rightarrow> {..<n}" unfolding g_def n'_def using J(1) pick_in_set_le by fastforce
  show "inj_on f {..<m'}"
    unfolding inj_on_def f_def m'_def by (metis lessThan_iff nat_neq_iff pick_mono_le)
  show "inj_on g {..<n'}"
    unfolding inj_on_def g_def n'_def by (metis lessThan_iff nat_neq_iff pick_mono_le)

  have "card {i. i < dim_row A \<and> i \<in> I} = card I"
    using A I(1)
    by (smt (verit, del_insts) basic_trans_rules(31) carrier_matD(1) equalityI lessThan_iff mem_Collect_eq subsetI)
  moreover have "card {j. j < dim_col A \<and> j \<in> J} = card J"
    using A J(1)
    by (smt (verit, del_insts) basic_trans_rules(31) carrier_matD(2) equalityI lessThan_iff mem_Collect_eq subsetI)
  ultimately show "B = submatrix_of_inj A f g m' n'"
    unfolding submatrix_of_inj_def B_def submatrix_def f_def g_def m'_def n'_def by argo
qed

lemma submatrix_inj_square:
  assumes A: "A \<in> carrier_mat n n"
  assumes I: "I \<subseteq> {..<n}"
  defines "m \<equiv> card I"
  defines "B \<equiv> submatrix A I I"
  defines "f \<equiv> \<lambda>i. pick I i"
  shows "f : {..<m} \<rightarrow> {..<n}" "inj_on f {..<m}" "B = submatrix_of_inj A f f m m"
  by (rule submatrix_inj[OF A I I, folded m_def B_def f_def])+

lemma submatrix_inj_obt:
  assumes A: "A \<in> carrier_mat m n"
  assumes I: "I \<subseteq> {..<m}"
  assumes J: "J \<subseteq> {..<n}"
  defines "m' \<equiv> card I"
  defines "n' \<equiv> card J"
  defines "B \<equiv> submatrix A I J"
  obtains f g where "f : {..<m'} \<rightarrow> {..<m}" "g : {..<n'} \<rightarrow> {..<n}"
                    "inj_on f {..<m'}" "inj_on g {..<n'}"
                    "B = submatrix_of_inj A f g m' n'"
  using submatrix_inj[OF A I J] m'_def n'_def B_def by blast

lemma submatrix_inj_square_obt:
  assumes A: "A \<in> carrier_mat n n"
  assumes I: "I \<subseteq> {..<n}"
  defines "m \<equiv> card I"
  defines "B \<equiv> submatrix A I I"
  obtains f where "f : {..<m} \<rightarrow> {..<n}" "inj_on f {..<m}" "B = submatrix_of_inj A f f m m"
  using submatrix_inj_square[OF A I] m_def B_def by blast

lemma submatrix_as_compression:
  fixes A :: "complex mat"
  fixes f :: "nat \<Rightarrow> nat"
  assumes A: "A \<in> carrier_mat n n"
  assumes I: "I \<subseteq> {..<n}"
  defines "m \<equiv> card I"
  defines "B \<equiv> submatrix A I I"
  defines "(Q::complex mat) \<equiv> mat n m (\<lambda>(i,j). if i = pick I j then 1 else 0)"
  shows "B = Q\<^sup>H * A * Q" "isometry_mat Q n m" "Q \<in> carrier_mat n m"
  using submatrix_inj_square[OF A I] submatrix_of_inj_as_compression[OF A]
  unfolding m_def B_def Q_def
  by presburger+

lemma submatrix_as_compression_obt:
  fixes A :: "complex mat"
  assumes "A \<in> carrier_mat n n"
  assumes "I \<subseteq> {..<n}"
  defines "m \<equiv> card I"
  defines "B \<equiv> submatrix A I I"
  obtains Q where "B = Q\<^sup>H * A * Q" "isometry_mat Q n m"
  using submatrix_as_compression[OF assms(1,2)] m_def B_def by blast

section "Schur Decomposition"

context
  fixes A \<Lambda> U :: "'a::{conjugatable_field,real_algebra_1,ord} mat"
  fixes n
  assumes *: "real_diag_decomp A \<Lambda> U"
  defines "n \<equiv> dim_row A"
begin

lemma diag_decomp_inverse: "inverts_mat U (adjoint U)"
  using *
  unfolding real_diag_decomp_def unitary_diag_def unitarily_equiv_def similar_mat_wit_def
  using Complex_Matrix.unitary_def by blast

lemma diag_decomp_invertible: "invertible_mat U"
  using diag_decomp_inverse *
  by (meson Complex_Matrix.unitary_def carrier_matD(2) invertible_mat_def real_diag_decompD(1) square_mat.simps unitaryD2
      unitary_diagD(3))

lemma diag_decomp_cols_distinct: "distinct (cols U)"
  using diag_decomp_invertible *
  by (metis carrier_mat_triv invertible_det invertible_mat_def order_less_irrefl square_mat.simps vec_space.low_rank_det_zero
      vec_space.non_distinct_low_rank)

lemma diag_decomp_ortho: "corthogonal_mat U"
  using unitary_is_corthogonal *
  unfolding real_diag_decomp_def unitary_diag_def unitarily_equiv_def unitary_def
  by blast

private lemma carriers: "A \<in> carrier_mat n n" "U \<in> carrier_mat n n" "U\<^sup>H \<in> carrier_mat n n" "\<Lambda> \<in> carrier_mat n n"
  using *[unfolded real_diag_decomp_def unitary_diag_def unitarily_equiv_def similar_mat_wit_def,
      folded adjoint_is_conjugate_transpose]
  using insert_subset n_def
  by metis+

lemma diag_decomp_cols_lin_indpt: "module.lin_indpt class_ring (module_vec TYPE('a) n) (set (cols U))"
  using * carriers unfolding real_diag_decomp_def unitary_diag_def unitary_def n_def
  by (metis diag_decomp_invertible idom_vec.lin_dep_cols_imp_det_0 invertible_det)

lemma real_diag_decomp_eq: "A = U * \<Lambda> * U\<^sup>H"
  using *[unfolded real_diag_decomp_def unitary_diag_def unitarily_equiv_def similar_mat_wit_def]
  by (metis adjoint_is_conjugate_transpose)

private lemma U_unitary: "U\<^sup>H * U = 1\<^sub>m n \<and>  U * U\<^sup>H = 1\<^sub>m n"
  using *[unfolded real_diag_decomp_def unitary_diag_def unitarily_equiv_def unitary_def]
  using n_def carriers
  by (metis adjoint_is_conjugate_transpose carrier_matD(2) inverts_mat_def similar_mat_wit_def)

private lemma \<Lambda>_diag: "diagonal_mat \<Lambda>"
  using * real_diag_decompD(1) unitary_diagD(2) by blast

lemma diag_decomp_cols_are_eigenvectors:
  assumes "i < n"
  shows "eigenvector A (col U i) ((diag_mat \<Lambda>)!i)" (is "eigenvector A ?v ?\<mu>")
proof-
  have "A *\<^sub>v ?v = (U * \<Lambda>) *\<^sub>v (U\<^sup>H *\<^sub>v ?v)"
    using * real_diag_decomp_eq carriers assoc_mult_mat_vec[of "U * \<Lambda>" n n "U\<^sup>H" n ?v] by force
  also have "\<dots> = (U * \<Lambda>) *\<^sub>v (col (1\<^sub>m n) i)"
    using U_unitary n_def assms carriers
    by (metis (mono_tags, lifting) adjoint_is_conjugate_transpose col_mult2)
  also have "\<dots> = U *\<^sub>v (\<Lambda> *\<^sub>v (unit_vec n i))"
    using * real_diag_decomp_eq carriers col_one assms by fastforce
  also have "\<dots> = U *\<^sub>v ((diag_mat \<Lambda>)!i \<cdot>\<^sub>v (unit_vec n i))"
    using *[unfolded real_diag_decomp_def unitary_diag_def]
    using diagonal_unit_vec'[OF carriers(4) \<Lambda>_diag, of i] assms carriers(4)
    unfolding diag_mat_def
    by force
  also have "\<dots> = (diag_mat \<Lambda>)!i \<cdot>\<^sub>v (U *\<^sub>v (unit_vec n i))"
    using carriers(2) by auto
  also have "\<dots> = (diag_mat \<Lambda>)!i \<cdot>\<^sub>v (col U i)"
    by (simp add: assms carriers(2) mat_unit_vec_col)
  finally show ?thesis
    unfolding eigenvector_def
    using assms carriers(2) n_def
    by (metis carrier_matD(1,2) col_dim conjugate_zero_vec corthogonal_matD diag_decomp_ortho scalar_prod_left_zero)
qed

end

section "Rayleigh Quotient"

definition rayleigh_quotient_complex :: "complex mat \<Rightarrow> complex vec \<Rightarrow> complex" ("\<rho>\<^sub>c") where
  "\<rho>\<^sub>c M x = (QF M x) / (x \<bullet>c x)"

definition rayleigh_quotient :: "complex mat \<Rightarrow> complex vec \<Rightarrow> real" ("\<rho>") where
  "\<rho> M x = Re (\<rho>\<^sub>c M x)"

lemma rayleigh_quotient_negative: "A \<in> carrier_mat n n \<Longrightarrow> x \<in> carrier_vec n \<Longrightarrow> \<rho> A x = - \<rho> (- A) x"
  by (simp add: rayleigh_quotient_def rayleigh_quotient_complex_def)

lemma rayleigh_quotient_complex_scale:
  fixes k :: real
  assumes "A \<in> carrier_mat n n"
  assumes "v \<in> carrier_vec n"
  assumes "k \<noteq> 0"
  shows "\<rho>\<^sub>c A v = \<rho>\<^sub>c A (k \<cdot>\<^sub>v v)"
proof-
  have "\<rho>\<^sub>c A v = (k^2 * ((A *\<^sub>v v) \<bullet>c v)) / (k^2 * (v \<bullet>c v))"
    using assms(3) by (simp add: rayleigh_quotient_complex_def)
  also have "\<dots> = (((k \<cdot>\<^sub>v (A *\<^sub>v v)) \<bullet>c (k \<cdot>\<^sub>v v))) / (((k \<cdot>\<^sub>v v) \<bullet>c (k \<cdot>\<^sub>v v)))"
    using assms(1,2) inner_prod_smult_right by force
  also have "\<dots> = ((((A *\<^sub>v (k \<cdot>\<^sub>v v))) \<bullet>c (k \<cdot>\<^sub>v v))) / (((k \<cdot>\<^sub>v v) \<bullet>c (k \<cdot>\<^sub>v v)))"
    using assms by (metis mult_mat_vec)
  also have "\<dots> = \<rho>\<^sub>c A (k \<cdot>\<^sub>v v)" by (simp add: rayleigh_quotient_complex_def)
  finally show ?thesis .
qed

lemma rayleigh_quotient_scale_complex:
  assumes "A \<in> carrier_mat n n"
  assumes "v \<in> carrier_vec n"
  assumes "k \<noteq> 0"
  shows "\<rho> A (k \<cdot>\<^sub>v v) = \<rho> A v"
proof-
  let ?v' = "(k \<cdot>\<^sub>v v)"
  have "(A *\<^sub>v ?v') \<bullet>c ?v' = (cmod k)^2 * (QF A v)"
    using assms(1,2)
    by (smt (verit, ccfv_SIG) cross3_simps(11)inner_prod_smult_left_right mult_conj_cmod_square mult_mat_vec
        mult_mat_vec_carrier quadratic_form_def)
  moreover have "?v' \<bullet>c ?v' = (cmod k)^2 * (v \<bullet>c v)"
    using assms(2) complex_norm_square inner_prod_smult_left_right by force
  ultimately show "\<rho> A ?v' = \<rho> A v"
    by (simp add: rayleigh_quotient_def rayleigh_quotient_complex_def assms(3))
qed

lemma rayleigh_quotient_scale_real:
  fixes k :: real
  assumes "A \<in> carrier_mat n n"
  assumes "v \<in> carrier_vec n"
  assumes "k \<noteq> 0"
  shows "\<rho> A v = \<rho> A (k \<cdot>\<^sub>v v)"
  by (smt (verit, ccfv_SIG) rayleigh_quotient_complex_scale assms Groups.mult_ac(2) complex_norm_square conjugate_complex_def inner_prod_smult_left_right mult_divide_mult_cancel_left_if mult_mat_vec mult_mat_vec_carrier norm_of_real of_real_eq_0_iff power_eq_0_iff quadratic_form_def rayleigh_quotient_complex_def rayleigh_quotient_def)

context cmplx_herm_mat
begin

lemma hermitian_rayleigh_quotient_real:
  assumes "v \<in> carrier_vec n"
  assumes "v \<noteq> 0\<^sub>v n"
  shows "\<rho>\<^sub>c A v \<in> Reals"
proof-
  have "QF A v \<in> Reals"
    using hermitian_quadratic_form_real assms by blast
  moreover have "inner_prod v v \<in> Reals" by (simp add: self_inner_prod_real)
  moreover have "inner_prod v v \<noteq> 0" using assms by fastforce
  ultimately show ?thesis unfolding rayleigh_quotient_complex_def using Reals_divide by blast
qed

lemma rayleigh_quotient_QF:
  assumes x: "x \<noteq> 0\<^sub>v n" "x \<in> carrier_vec n"
  shows "\<rho> A x = (QF A x) / (vec_norm x)\<^sup>2"
  using hermitian_rayleigh_quotient_real[OF x(2,1)]
  unfolding rayleigh_quotient_def rayleigh_quotient_complex_def vec_norm_def
  using of_real_Re power2_csqrt
  by presburger

end

lemma rayleigh_eigenvector:
  assumes "eigenvector A v e"
  shows "\<rho> A v = e"
  unfolding rayleigh_quotient_def rayleigh_quotient_complex_def quadratic_form_def
  using assms[unfolded eigenvector_def]
  by force

end
