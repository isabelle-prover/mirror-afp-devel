(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Matrix to Vector Conversion\<close>

theory DL_Flatten_Matrix
imports HOL.Real Jordan_Normal_Form.Matrix
begin

definition extract_matrix :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
"extract_matrix a m n = mat m n (\<lambda>(i,j). a (i*n + j))"

definition flatten_matrix :: "'a mat \<Rightarrow> (nat \<Rightarrow> 'a)" where
"flatten_matrix A k = A $$ (k div dim_col A, k mod dim_col A)"

lemma two_digit_le:
fixes i j :: nat
assumes "i < m" "j < n"
shows "i*n + j < m*n"
proof -
  have "(i*n + j) div n = i" "m*n div n = m" using assms by auto
  then have "(i * n + j) div m div n = i div m"
    by (metis Divides.div_mult2_eq  mult.commute)
  then show ?thesis
    by (metis Divides.div_mult2_eq \<open>i < m\<close> \<open>m * n div n = m\<close> div_eq_0_iff not_less0)
qed

lemma extract_matrix_cong:
assumes "\<And>i. i < m * n \<Longrightarrow> a i = b i"
shows "extract_matrix a m n = extract_matrix b m n"
proof -
  have "\<And>i j. i < m \<Longrightarrow> j < n \<Longrightarrow> a (i*n + j) = b (i*n + j)" using two_digit_le assms by blast
  then show ?thesis unfolding extract_matrix_def by auto
qed

lemma extract_matrix_flatten_matrix:
"extract_matrix (flatten_matrix A) (dim_row A) (dim_col A) = A"
unfolding extract_matrix_def flatten_matrix_def by auto

lemma flatten_matrix_extract_matrix:
shows "\<And>k. k<m*n \<Longrightarrow> flatten_matrix (extract_matrix a m n) k = a k"
  unfolding extract_matrix_def flatten_matrix_def
  by (metis (no_types, lifting) Divides.div_mult2_eq case_prod_conv div_eq_0_iff dim_col_mat(1)
  index_mat(1) div_mult_mod_eq mod_less_divisor mult.commute mult_zero_right not_gr0 not_less0)

lemma index_extract_matrix:
assumes "i<m" "j<n"
shows "extract_matrix a m n $$ (i,j) = a (i*n + j)"
  unfolding extract_matrix_def using assms by simp

lemma dim_extract_matrix:
shows "dim_row (extract_matrix as m n) = m"
and "dim_col (extract_matrix as m n) = n"
  unfolding extract_matrix_def by simp_all

end
