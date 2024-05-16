theory Integral_Matrix
imports
  Complex_Main
  "HOL-Analysis.Finite_Cartesian_Product"
  "HOL-Analysis.Linear_Algebra"
  "HOL-Analysis.Determinants"
begin

section "Misc. Linear Algebra Setup"

lemma vec_scaleR_2: "(c::real) *\<^sub>R ((vector [a, b])::real^2) = vector [a * c, b * c]"
proof-
  have "(c *\<^sub>R (vector [a, b])::real^2)$1 = a * c" by simp
  moreover have "(c *\<^sub>R (vector [a, b])::real^2)$2 = ((vector [a, b])::real^2)$2 * c" by simp
  ultimately show ?thesis by (smt (verit, best) exhaust_2 vec_eq_iff vector_2(1) vector_2(2))
qed

definition is_int :: "real \<Rightarrow> bool" where
  "is_int x \<longleftrightarrow> (\<exists>n::int. x = n)"

lemma is_int_sum: "is_int x \<and> is_int y \<longrightarrow> is_int (x + y)"
  by (metis is_int_def of_int_add)

lemma is_int_minus: "is_int x \<and> is_int y \<longrightarrow> is_int (x - y)"
  by (metis is_int_def of_int_diff)

lemma is_int_mult: "is_int x \<and> is_int y \<longrightarrow> is_int (x * y)"
  by (metis is_int_def of_int_mult) 

definition integral_vec :: "real^2 \<Rightarrow> bool" where  
  "integral_vec v \<longleftrightarrow> (is_int (v$1) \<and> is_int (v$2))"

lemma integral_vec_sum: "integral_vec v \<and> integral_vec w \<longrightarrow> integral_vec (v + w)"
proof(rule impI)
  fix v w :: "real^2"
  let ?x = "v + w"
  assume "integral_vec v \<and> integral_vec w"
  then obtain v1 v2 w1 w2 :: int where "v$1 = v1 \<and> v$2 = v2 \<and> w$1 = w1 \<and> w$2 = w2"
    using integral_vec_def is_int_def by auto
  then have "?x$1 = v1 + w1" and "?x$2 = v2 + w2" by auto
  thus "integral_vec ?x" using integral_vec_def is_int_def by blast 
qed

lemma integral_vec_minus: "integral_vec v \<longrightarrow> integral_vec (-v)"
proof(rule impI)
  assume "integral_vec v"
  then obtain x y :: int where "v$1 = x \<and> v$2 = y"
    using integral_vec_def is_int_def by auto
  then have "(-v)$1 = -x" and "(-v)$2 = -y"
    using integral_vec_def is_int_def by auto
  thus "integral_vec (-v)"
    using integral_vec_def is_int_def by blast 
qed

lemma real_2_inner:
  shows "((vector [a, b])::(real^2)) \<bullet> ((vector [c, d])::(real^2)) = a*c + b*d"
    (is "?v \<bullet> ?w = a*c + b*d")
proof-
  have "?v \<bullet> ?w = (\<Sum>i \<in> UNIV. ?v$i \<bullet> ?w$i)" using inner_vec_def[of ?v ?w] by blast
  moreover have "\<forall>i. ?v$i \<bullet> ?w$i = ?v$i * ?w$i" using inner_real_def by simp
  ultimately have "?v \<bullet> ?w = (\<Sum>i \<in> UNIV. ?v$i * ?w$i)" by presburger
  thus ?thesis by (simp add: sum_2)
qed

lemma integral_vec_2:
  fixes a b :: "int"
  assumes "v = vector [a, b]"
  shows "integral_vec v"
  by (simp add: assms is_int_def integral_vec_def)

definition matrix_inv :: "real^2^2 \<Rightarrow> real^2^2 \<Rightarrow> bool" where
  "matrix_inv A A' \<longleftrightarrow> (A ** A' = mat 1 \<and> A' ** A = mat 1)"

lemma mat_vec_mult_2:
  fixes v :: "real^2" and
        T :: "real^2^2"
  defines x: "x \<equiv> v$1" and y: "y \<equiv> v$2" and
          a: "a \<equiv> T$1$1" and b: "b \<equiv> T$1$2" and
          c: "c \<equiv> T$2$1" and d: "d \<equiv> T$2$2"
  shows "(T *v v) = vector [x*a + y*b, x*c + y*d]"
proof-
  have "(T *v v)$1 = x*a + y*b" by (simp add: a b matrix_vector_mult_def sum_2 x y)
  moreover have "(T *v v)$2 = x*c + y*d" by (simp add: c d matrix_vector_mult_def sum_2 x y)
  ultimately show "T *v v = vector [x*a + y*b, x*c + y*d]"
    by (smt (verit) exhaust_2 vec_eq_iff vector_2(1) vector_2(2)) 
qed
  
definition integral_mat :: "real^2^2 \<Rightarrow> bool" where
  "integral_mat T \<longleftrightarrow> (\<forall>v. integral_vec v \<longrightarrow> integral_vec (T *v v))"

definition integral_mat_surj :: "real^2^2 \<Rightarrow> bool" where
  "integral_mat_surj T \<longleftrightarrow> (\<forall>v. integral_vec v \<longrightarrow> (\<exists>w. integral_vec w \<and> T *v w = v))"

definition integral_mat_bij :: "real^2^2 \<Rightarrow> bool" where
  "integral_mat_bij T \<longleftrightarrow> integral_mat T \<and> integral_mat_surj T"

lemma integral_mat_integral_vec: "integral_mat A \<longrightarrow> integral_vec v \<longrightarrow> integral_vec (A *v v)"
  using integral_mat_def by blast

(* an integral matrix has integer entries *)
lemma integral_mat_int_entries:
  fixes T :: "real^2^2"
  assumes "integral_mat T"
  defines a: "a \<equiv> T$1$1" and b: "b \<equiv> T$1$2" and
          c: "c \<equiv> T$2$1" and d: "d \<equiv> T$2$2"
  shows "is_int a \<and> is_int b \<and> is_int c \<and> is_int d"
proof-
  let ?v = "vector [1, 0]"
  have "integral_vec (?v)" using integral_vec_2[of "?v" "1" "0"] by auto
  then have "integral_vec (T *v ?v)" using assms integral_mat_def by blast
  moreover have "T *v ?v = vector [a, c]"
    using mat_vec_mult_2[of "T" "?v"] a b c d by auto
  ultimately have "integral_vec (vector [a, c])" by auto
  then have 1: "is_int a \<and> is_int c" using integral_vec_def by auto
  
  let ?w = "vector [0, 1]"
  have "integral_vec (?w)" using integral_vec_2[of "?w" "0" "1"] by auto
  then have "integral_vec (T *v ?w)" using assms integral_mat_def by blast
  moreover have "T *v ?w = vector [b, d]"
    using mat_vec_mult_2[of "T" "?w"] a b c d by auto
  ultimately have "integral_vec (vector [b, d])" by auto
  then have 2: "is_int b \<and> is_int d" using integral_vec_def by auto

  thus ?thesis using 1 2 by auto
qed

section "Integral Bijective Matrix Determinant"

(* a matrix which bijectively maps the integer lattice to itself has an integer determinant *)
lemma integral_mat_int_det:
  fixes T :: "real^2^2"
  assumes "integral_mat T"
  shows "is_int (det T)"  
proof-
  obtain a b c d where abcd: "T$1$1 = a \<and> T$1$2 = b \<and> T$2$1 = c \<and> T$2$2 = d" by auto
  have abcd_int: "is_int a \<and> is_int b \<and> is_int c \<and> is_int d"
    using integral_mat_int_entries[of "T"] abcd assms by auto
  obtain ai bi ci di :: "int" where abcdi: "ai = a \<and> bi = b \<and> ci = c \<and> di = d"
    using abcd_int is_int_def by auto
  have "det T = a*d - b*c" using det_2[of "T"] abcd by auto
  also have "... = ai*di - bi*ci" using abcdi by auto
  finally show ?thesis using is_int_def by blast
qed

lemma integral_mat_bij_inv:
  fixes T :: "real^2^2"
  assumes "integral_mat_bij T"
  obtains Tinv where "invertible T \<and> integral_mat_bij Tinv \<and> matrix_inv T Tinv"
proof-
  let ?e1 = "vector [1, 0]"
  let ?e2 = "vector [0, 1]"
  let ?I = "(vector [?e1, ?e2])::(real^2^2)"
  have id: "?I = ((mat 1)::(real^2^2))"
    unfolding vec_eq_iff
    by (smt (verit, ccfv_threshold) exhaust_2 mat_def vec_lambda_beta vector_2)
  have "integral_vec ?e1"
    by (simp add: integral_vec_def is_int_def)
  moreover have "integral_vec ?e2"
    by (simp add: integral_vec_def is_int_def)
  ultimately obtain x y where xy: "T *v x = ?e1 \<and> integral_vec x \<and> T *v y = ?e2 \<and> integral_vec y"
    by (meson assms integral_mat_bij_def integral_mat_surj_def)

  let ?Tinv = "transpose (vector [x, y])::(real^2^2)"
  have "T ** ?Tinv = mat 1" (is "?TxTinv = mat 1")
  proof-
    have "column 1 ?TxTinv = T *v (column 1 ?Tinv)"
      by (metis matrix_vector_mul_assoc matrix_vector_mult_basis)
    also have "... = T *v x"
      by (simp add: row_def)
    finally have [simp]: "column 1 ?TxTinv = ?e1"
      using xy by presburger

    have "column 2 ?TxTinv = T *v (column 2 ?Tinv)"
      by (metis matrix_vector_mul_assoc matrix_vector_mult_basis)
    also have "... = T *v y"
      by (simp add: row_def)
    finally have [simp]: "column 2 ?TxTinv = ?e2"
      using xy by presburger

    have "\<forall>v. ?TxTinv *v v = v"
    proof(rule allI)
      fix v :: "real^2"

      have "(?TxTinv *v v)$1 = (column 1 ?TxTinv)$1 * v$1 + (column 2 ?TxTinv)$1 * v$2"
        by (metis (no_types, lifting) cart_eq_inner_axis mat_vec_mult_2 matrix_vector_mul_component matrix_vector_mult_basis mult.commute vector_2(1))
      also have "... = v$1" by simp
      finally have v1: "(?TxTinv *v v)$1 = v$1" .

      have "(?TxTinv *v v)$2 = (column 1 ?TxTinv)$2 * v$1 + (column 2 ?TxTinv)$2 * v$2"
        by (metis (no_types, lifting) cart_eq_inner_axis mat_vec_mult_2 matrix_vector_mul_component matrix_vector_mult_basis mult.commute vector_2(2))
      also have "... = v$2" by simp
      finally have v2: "(?TxTinv *v v)$2 = v$2" .

      show "?TxTinv *v v = v" using v1 v2 by (metis mat_vec_mult_2 matrix_vector_mul_lid)
    qed
    thus ?thesis by (simp add: matrix_eq) 
  qed
  then have "matrix_inv T ?Tinv"
    by (simp add: Integral_Matrix.matrix_inv_def matrix_left_right_inverse) 
  moreover have "invertible T" using calculation invertible_def matrix_inv_def by blast
  moreover have "integral_mat_bij ?Tinv"
    by (smt (verit, del_insts) \<open>T ** Finite_Cartesian_Product.transpose (vector [x, y]) = mat 1\<close> assms integral_mat_bij_def integral_mat_def integral_mat_surj_def matrix_left_right_inverse matrix_mul_lid matrix_vector_mul_assoc)
  ultimately show ?thesis
    using \<open>T ** Finite_Cartesian_Product.transpose (vector [x, y]) = mat 1\<close> invertible_right_inverse that by blast
qed

(* a matrix which bijectively maps the integer lattice to itself has determinant \<plusminus>1 *)
lemma integral_mat_bij_det_pm1:
  fixes T :: "real^2^2"
  assumes "integral_mat_bij T"
  shows "det T = 1 \<or> det T = -1"
proof-
  obtain Tinv where Tinv: "invertible T \<and> integral_mat_bij Tinv \<and> matrix_inv T Tinv"
    using integral_mat_bij_inv[of "T"] assms by auto
  moreover have "is_int (det Tinv)"
    using integral_mat_bij_def integral_mat_int_det[of "Tinv"] calculation by auto
  moreover have "is_int (det T)"
    using integral_mat_bij_def integral_mat_int_det[of "T"] assms by auto
  moreover have "det Tinv = 1 / det T"
  proof-
    have id: "Tinv ** T = mat 1" using Tinv unfolding matrix_inv_def invertible_def
      by (simp add: verit_sko_ex')      
    have "det Tinv * det T = det (Tinv ** T)" by (simp add: det_mul)
    also have "... = det ((mat 1)::real^2^2)" using id by auto
    also have "... = (1::real)" by auto
    finally have "det Tinv * det T = 1" .
    thus ?thesis using invertible_det_nz nonzero_eq_divide_eq by fastforce 
  qed
  ultimately have T_Tinv_int: "is_int (det T) \<and> is_int (1 / det T)" by auto
  thus "det T = 1 \<or> det T = -1"
  proof-
    have "abs (det T) \<le> 1" (is "?D \<le> 1")
    proof(rule ccontr)
      assume "\<not> ?D \<le> 1"
      then have "?D > 1" by auto
      moreover from this have "1 / ?D < 1" by auto
      moreover from calculation have "1 / ?D > 0" by auto
      ultimately have "\<not> is_int (1 / ?D)" unfolding is_int_def by force
      moreover from T_Tinv_int have "is_int (1 / ?D)"
        by (smt (verit) \<open>1 / \<bar>det T\<bar> < 1\<close> abs_div_pos abs_divide abs_ge_self abs_minus_cancel divide_cancel_left divide_pos_neg int_less_real_le is_int_def of_int_code(2))
      ultimately show "False" by auto
    qed
    then have "det T \<ge> -1 \<and> det T \<le> 1"
      using assms by auto
    moreover have "det T \<noteq> 0" using integral_mat_bij_inv invertible_det_nz assms by auto
    ultimately show "det T = 1 \<or> det T = -1" using is_int_def T_Tinv_int by auto 
  qed
qed

end