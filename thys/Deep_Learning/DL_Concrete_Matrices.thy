(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Concrete Matrices\<close>

theory DL_Concrete_Matrices
imports Real "../Jordan_Normal_Form/Matrix" DL_Missing_Matrix
begin

text \<open>The following definition allows non-square-matrices, mat\_one (mat\_one n) only allows square matrices.\<close>

definition eye_matrix::"nat \<Rightarrow> nat \<Rightarrow> real mat" 
where "eye_matrix nr nc = mat nr nc (\<lambda>(r, c). if r=c then 1 else 0)"

lemma eye_matrix_dim: "dim\<^sub>r (eye_matrix nr nc) = nr" "dim\<^sub>c (eye_matrix nr nc) = nc" by (simp_all add: eye_matrix_def)

lemma row_eye_matrix:
assumes "i < nr"
shows "row (eye_matrix nr nc) i = unit\<^sub>v nc i"
  by (rule vec_eqI, simp add: assms eye_matrix_def vec_unit_def, simp add: eye_matrix_dim(2))

lemma unit_eq_0[simp]: 
  assumes i: "i \<ge> n"
  shows "unit\<^sub>v n i = \<zero>\<^sub>v n"
  apply (rule vec_eqI) 
  apply (metis (mono_tags, lifting) i leD vec_dim_vec vec_index_vec vec_unit_def vec_zero_def)
  by simp

lemma mult_eye_matrix:
assumes "i < nr"
shows "(eye_matrix nr (dim\<^sub>v v) \<otimes>\<^sub>m\<^sub>v v) $ i = (if i<dim\<^sub>v v then v $ i else 0)" (is "?a $ i = ?b")
proof -
  have "?a $ i = row (eye_matrix nr (dim\<^sub>v v)) i \<bullet> v" using index_mat_mult_vec assms eye_matrix_dim by auto
  also have "... = unit\<^sub>v (dim\<^sub>v v) i \<bullet> v" using row_eye_matrix assms by auto
  also have "... = ?b" using scalar_prod_left_unit vec_elemsI unit_eq_0 scalar_prod_left_zero by fastforce
  finally show ?thesis by auto
qed


definition all1_vec::"nat \<Rightarrow> real vec" 
where "all1_vec n = vec n (\<lambda>i. 1)"

definition all1_matrix::"nat \<Rightarrow> nat \<Rightarrow> real mat" 
where "all1_matrix nr nc = mat nr nc (\<lambda>(r, c). 1)"

lemma all1_matrix_dim: "dim\<^sub>r (all1_matrix nr nc) = nr" "dim\<^sub>c (all1_matrix nr nc) = nc" 
  by (simp_all add: all1_matrix_def)

lemma row_all1_matrix:
assumes "i < nr"
shows "row (all1_matrix nr nc) i = all1_vec nc"
  apply (rule vec_eqI) 
  apply (simp add: all1_matrix_def all1_vec_def assms)
  by (simp add: all1_matrix_def all1_vec_def)

lemma all1_vec_scalar_prod:
shows "all1_vec (length xs) \<bullet> (vec_of_list xs) = listsum xs" 
proof -
  have "all1_vec (length xs) \<bullet> (vec_of_list xs) = (\<Sum>i = 0..<dim\<^sub>v (vec_of_list xs). vec_of_list xs $ i)"
    unfolding scalar_prod_def by (metis (no_types, lifting) all1_vec_def mult_cancel_right1 setsum_ivl_cong 
    vec.abs_eq vec_dim_vec vec_index_vec vec_of_list.abs_eq)
  also have "... = (\<Sum>i = 0..<length xs. xs ! i)" using vec.abs_eq vec_dim_vec vec_of_list.abs_eq 
    by (metis setsum_ivl_cong vec_index_vec)
  also have "... = listsum xs" by (simp add: listsum_setsum_nth)
  finally show ?thesis by auto
qed


lemma mult_all1_matrix:
assumes "i < nr"
shows "((all1_matrix nr (dim\<^sub>v v)) \<otimes>\<^sub>m\<^sub>v v) $ i = listsum (list_of_vec v)" (is "?a $ i = listsum (list_of_vec v)")
proof -
  have "?a $ i = row (all1_matrix nr (dim\<^sub>v v)) i \<bullet> v" using index_mat_mult_vec assms all1_matrix_dim by auto
  also have "... = listsum (list_of_vec v)" unfolding row_all1_matrix[OF assms] using all1_vec_scalar_prod[of "list_of_vec v"] 
    by (metis vec.abs_eq vec_dim_vec vec_list vec_of_list.abs_eq)
  finally show ?thesis by auto
qed


definition copy_first_matrix::"nat \<Rightarrow> nat \<Rightarrow> real mat" 
where "copy_first_matrix nr nc = mat nr nc (\<lambda>(r, c). if c = 0 then 1 else 0)"

lemma copy_first_matrix_dim: "dim\<^sub>r (copy_first_matrix nr nc) = nr" "dim\<^sub>c (copy_first_matrix nr nc) = nc" 
  by (simp_all add: copy_first_matrix_def)

lemma row_copy_first_matrix:
assumes "i < nr"
shows "row (copy_first_matrix nr nc) i = unit\<^sub>v nc 0"
  apply (rule vec_eqI) 
  apply (auto simp add: copy_first_matrix_def assms)[1]
  by (simp add: copy_first_matrix_def)

lemma mult_copy_first_matrix:
assumes "i < nr" and "dim\<^sub>v v > 0"
shows "(copy_first_matrix nr (dim\<^sub>v v) \<otimes>\<^sub>m\<^sub>v v) $ i = v $ 0" (is "?a $ i = v $ 0")
proof -
  have "?a $ i = row (copy_first_matrix nr (dim\<^sub>v v)) i \<bullet> v" using index_mat_mult_vec assms copy_first_matrix_dim by auto  
  also have "... = unit\<^sub>v (dim\<^sub>v v) 0 \<bullet> v" using row_copy_first_matrix assms by auto
  also have "... = v $ 0" using assms(2) scalar_prod_left_unit vec_elems by blast
  finally show ?thesis by auto
qed

end 
