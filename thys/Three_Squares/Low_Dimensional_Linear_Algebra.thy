(*  Title:      Three_Squares/Low_Dimensional_Linear_Algebra.thy
    Author:     Anton Danilkin
*)

section \<open>Vectors and matrices, determinants and
         their properties in dimensions 2 and 3\<close>

theory Low_Dimensional_Linear_Algebra
  imports "HOL-Library.Adhoc_Overloading"
begin

datatype vec2 =
  vec2
  (vec2\<^sub>1 : int)
  (vec2\<^sub>2 : int)

datatype vec3 =
  vec3
  (vec3\<^sub>1 : int)
  (vec3\<^sub>2 : int)
  (vec3\<^sub>3 : int)

datatype mat2 =
  mat2
  (mat2\<^sub>1\<^sub>1 : int) (mat2\<^sub>1\<^sub>2 : int)
  (mat2\<^sub>2\<^sub>1 : int) (mat2\<^sub>2\<^sub>2 : int)

datatype mat3 =
  mat3
  (mat3\<^sub>1\<^sub>1 : int) (mat3\<^sub>1\<^sub>2 : int) (mat3\<^sub>1\<^sub>3 : int)
  (mat3\<^sub>2\<^sub>1 : int) (mat3\<^sub>2\<^sub>2 : int) (mat3\<^sub>2\<^sub>3 : int)
  (mat3\<^sub>3\<^sub>1 : int) (mat3\<^sub>3\<^sub>2 : int) (mat3\<^sub>3\<^sub>3 : int)

instantiation vec2 :: ab_group_add
begin

definition zero_vec2 where
"zero_vec2 =
  vec2
  0
  0"

definition uminus_vec2 where
"uminus_vec2 v =
  vec2
  (- vec2\<^sub>1 v)
  (- vec2\<^sub>2 v)"

definition plus_vec2 where
"plus_vec2 v1 v2 =
  vec2
  (vec2\<^sub>1 v1 + vec2\<^sub>1 v2)
  (vec2\<^sub>2 v1 + vec2\<^sub>2 v2)"

definition minus_vec2 where
"minus_vec2 v1 v2 =
  vec2
  (vec2\<^sub>1 v1 - vec2\<^sub>1 v2)
  (vec2\<^sub>2 v1 - vec2\<^sub>2 v2)"

instance
  apply intro_classes
  unfolding zero_vec2_def uminus_vec2_def plus_vec2_def minus_vec2_def
  apply simp_all
  done

end

instantiation vec3 :: ab_group_add
begin

definition zero_vec3 where
"zero_vec3 =
  vec3
  0
  0
  0"

definition uminus_vec3 where
"uminus_vec3 v =
  vec3
  (- vec3\<^sub>1 v)
  (- vec3\<^sub>2 v)
  (- vec3\<^sub>3 v)"

definition plus_vec3 where
"plus_vec3 v1 v2 =
  vec3
  (vec3\<^sub>1 v1 + vec3\<^sub>1 v2)
  (vec3\<^sub>2 v1 + vec3\<^sub>2 v2)
  (vec3\<^sub>3 v1 + vec3\<^sub>3 v2)"

definition minus_vec3 where
"minus_vec3 v1 v2 =
  vec3
  (vec3\<^sub>1 v1 - vec3\<^sub>1 v2)
  (vec3\<^sub>2 v1 - vec3\<^sub>2 v2)
  (vec3\<^sub>3 v1 - vec3\<^sub>3 v2)"

instance
  apply intro_classes
  unfolding zero_vec3_def uminus_vec3_def plus_vec3_def minus_vec3_def
  apply simp_all
  done

end

instantiation mat2 :: ring_1
begin

definition zero_mat2 where
"zero_mat2 =
  mat2
  0 0
  0 0"

definition one_mat2 where
"one_mat2 =
  mat2
  1 0
  0 1"

definition uminus_mat2 where
"uminus_mat2 m =
  mat2
  (- mat2\<^sub>1\<^sub>1 m) (- mat2\<^sub>1\<^sub>2 m)
  (- mat2\<^sub>2\<^sub>1 m) (- mat2\<^sub>2\<^sub>2 m)"

definition plus_mat2 where
"plus_mat2 m1 m2 =
  mat2
  (mat2\<^sub>1\<^sub>1 m1 + mat2\<^sub>1\<^sub>1 m2) (mat2\<^sub>1\<^sub>2 m1 + mat2\<^sub>1\<^sub>2 m2)
  (mat2\<^sub>2\<^sub>1 m1 + mat2\<^sub>2\<^sub>1 m2) (mat2\<^sub>2\<^sub>2 m1 + mat2\<^sub>2\<^sub>2 m2)"

definition minus_mat2 where
"minus_mat2 m1 m2 =
  mat2
  (mat2\<^sub>1\<^sub>1 m1 - mat2\<^sub>1\<^sub>1 m2) (mat2\<^sub>1\<^sub>2 m1 - mat2\<^sub>1\<^sub>2 m2)
  (mat2\<^sub>2\<^sub>1 m1 - mat2\<^sub>2\<^sub>1 m2) (mat2\<^sub>2\<^sub>2 m1 - mat2\<^sub>2\<^sub>2 m2)"

definition times_mat2 where
"times_mat2 m1 m2 =
  mat2
  (mat2\<^sub>1\<^sub>1 m1 * mat2\<^sub>1\<^sub>1 m2 + mat2\<^sub>1\<^sub>2 m1 * mat2\<^sub>2\<^sub>1 m2) (mat2\<^sub>1\<^sub>1 m1 * mat2\<^sub>1\<^sub>2 m2 + mat2\<^sub>1\<^sub>2 m1 * mat2\<^sub>2\<^sub>2 m2)
  (mat2\<^sub>2\<^sub>1 m1 * mat2\<^sub>1\<^sub>1 m2 + mat2\<^sub>2\<^sub>2 m1 * mat2\<^sub>2\<^sub>1 m2) (mat2\<^sub>2\<^sub>1 m1 * mat2\<^sub>1\<^sub>2 m2 + mat2\<^sub>2\<^sub>2 m1 * mat2\<^sub>2\<^sub>2 m2)"

instance
  apply intro_classes
  unfolding zero_mat2_def one_mat2_def uminus_mat2_def plus_mat2_def minus_mat2_def times_mat2_def
  apply (simp_all add: algebra_simps)
  done

end

instantiation mat3 :: ring_1
begin

definition zero_mat3 where
"zero_mat3 =
  mat3
  0 0 0
  0 0 0
  0 0 0"

definition one_mat3 where
"one_mat3 =
  mat3
  1 0 0
  0 1 0
  0 0 1"

definition uminus_mat3 where
"uminus_mat3 m =
  mat3
  (- mat3\<^sub>1\<^sub>1 m) (- mat3\<^sub>1\<^sub>2 m) (- mat3\<^sub>1\<^sub>3 m)
  (- mat3\<^sub>2\<^sub>1 m) (- mat3\<^sub>2\<^sub>2 m) (- mat3\<^sub>2\<^sub>3 m)
  (- mat3\<^sub>3\<^sub>1 m) (- mat3\<^sub>3\<^sub>2 m) (- mat3\<^sub>3\<^sub>3 m)"

definition plus_mat3 where
"plus_mat3 m1 m2 =
  mat3
  (mat3\<^sub>1\<^sub>1 m1 + mat3\<^sub>1\<^sub>1 m2) (mat3\<^sub>1\<^sub>2 m1 + mat3\<^sub>1\<^sub>2 m2) (mat3\<^sub>1\<^sub>3 m1 + mat3\<^sub>1\<^sub>3 m2)
  (mat3\<^sub>2\<^sub>1 m1 + mat3\<^sub>2\<^sub>1 m2) (mat3\<^sub>2\<^sub>2 m1 + mat3\<^sub>2\<^sub>2 m2) (mat3\<^sub>2\<^sub>3 m1 + mat3\<^sub>2\<^sub>3 m2)
  (mat3\<^sub>3\<^sub>1 m1 + mat3\<^sub>3\<^sub>1 m2) (mat3\<^sub>3\<^sub>2 m1 + mat3\<^sub>3\<^sub>2 m2) (mat3\<^sub>3\<^sub>3 m1 + mat3\<^sub>3\<^sub>3 m2)"

definition minus_mat3 where
"minus_mat3 m1 m2 =
  mat3
  (mat3\<^sub>1\<^sub>1 m1 - mat3\<^sub>1\<^sub>1 m2) (mat3\<^sub>1\<^sub>2 m1 - mat3\<^sub>1\<^sub>2 m2) (mat3\<^sub>1\<^sub>3 m1 - mat3\<^sub>1\<^sub>3 m2)
  (mat3\<^sub>2\<^sub>1 m1 - mat3\<^sub>2\<^sub>1 m2) (mat3\<^sub>2\<^sub>2 m1 - mat3\<^sub>2\<^sub>2 m2) (mat3\<^sub>2\<^sub>3 m1 - mat3\<^sub>2\<^sub>3 m2)
  (mat3\<^sub>3\<^sub>1 m1 - mat3\<^sub>3\<^sub>1 m2) (mat3\<^sub>3\<^sub>2 m1 - mat3\<^sub>3\<^sub>2 m2) (mat3\<^sub>3\<^sub>3 m1 - mat3\<^sub>3\<^sub>3 m2)"

definition times_mat3 where
"times_mat3 m1 m2 =
  mat3
  (mat3\<^sub>1\<^sub>1 m1 * mat3\<^sub>1\<^sub>1 m2 + mat3\<^sub>1\<^sub>2 m1 * mat3\<^sub>2\<^sub>1 m2 + mat3\<^sub>1\<^sub>3 m1 * mat3\<^sub>3\<^sub>1 m2) (mat3\<^sub>1\<^sub>1 m1 * mat3\<^sub>1\<^sub>2 m2 + mat3\<^sub>1\<^sub>2 m1 * mat3\<^sub>2\<^sub>2 m2 + mat3\<^sub>1\<^sub>3 m1 * mat3\<^sub>3\<^sub>2 m2) (mat3\<^sub>1\<^sub>1 m1 * mat3\<^sub>1\<^sub>3 m2 + mat3\<^sub>1\<^sub>2 m1 * mat3\<^sub>2\<^sub>3 m2 + mat3\<^sub>1\<^sub>3 m1 * mat3\<^sub>3\<^sub>3 m2)
  (mat3\<^sub>2\<^sub>1 m1 * mat3\<^sub>1\<^sub>1 m2 + mat3\<^sub>2\<^sub>2 m1 * mat3\<^sub>2\<^sub>1 m2 + mat3\<^sub>2\<^sub>3 m1 * mat3\<^sub>3\<^sub>1 m2) (mat3\<^sub>2\<^sub>1 m1 * mat3\<^sub>1\<^sub>2 m2 + mat3\<^sub>2\<^sub>2 m1 * mat3\<^sub>2\<^sub>2 m2 + mat3\<^sub>2\<^sub>3 m1 * mat3\<^sub>3\<^sub>2 m2) (mat3\<^sub>2\<^sub>1 m1 * mat3\<^sub>1\<^sub>3 m2 + mat3\<^sub>2\<^sub>2 m1 * mat3\<^sub>2\<^sub>3 m2 + mat3\<^sub>2\<^sub>3 m1 * mat3\<^sub>3\<^sub>3 m2)
  (mat3\<^sub>3\<^sub>1 m1 * mat3\<^sub>1\<^sub>1 m2 + mat3\<^sub>3\<^sub>2 m1 * mat3\<^sub>2\<^sub>1 m2 + mat3\<^sub>3\<^sub>3 m1 * mat3\<^sub>3\<^sub>1 m2) (mat3\<^sub>3\<^sub>1 m1 * mat3\<^sub>1\<^sub>2 m2 + mat3\<^sub>3\<^sub>2 m1 * mat3\<^sub>2\<^sub>2 m2 + mat3\<^sub>3\<^sub>3 m1 * mat3\<^sub>3\<^sub>2 m2) (mat3\<^sub>3\<^sub>1 m1 * mat3\<^sub>1\<^sub>3 m2 + mat3\<^sub>3\<^sub>2 m1 * mat3\<^sub>2\<^sub>3 m2 + mat3\<^sub>3\<^sub>3 m1 * mat3\<^sub>3\<^sub>3 m2)"

instance
  apply intro_classes
  unfolding zero_mat3_def one_mat3_def uminus_mat3_def plus_mat3_def minus_mat3_def times_mat3_def
  apply (simp_all add: algebra_simps)
  done

end

consts vec_dot :: "'a \<Rightarrow> 'a \<Rightarrow> int" ("<_ | _>" 65)

definition vec2_dot :: "vec2 \<Rightarrow> vec2 \<Rightarrow> int" where
"vec2_dot v1 v2 = vec2\<^sub>1 v1 * vec2\<^sub>1 v2 + vec2\<^sub>2 v1 * vec2\<^sub>2 v2"

adhoc_overloading vec_dot vec2_dot

definition vec3_dot :: "vec3 \<Rightarrow> vec3 \<Rightarrow> int" where
"vec3_dot v1 v2 = vec3\<^sub>1 v1 * vec3\<^sub>1 v2 + vec3\<^sub>2 v1 * vec3\<^sub>2 v2 + vec3\<^sub>3 v1 * vec3\<^sub>3 v2"

adhoc_overloading vec_dot vec3_dot

lemma vec2_dot_zero_left [simp]:
  fixes v :: vec2
  shows "<0 | v> = 0"
  unfolding vec2_dot_def zero_vec2_def by auto

lemma vec2_dot_zero_right [simp]:
  fixes v :: vec2
  shows "<v | 0> = 0"
  unfolding vec2_dot_def zero_vec2_def by auto

lemma vec3_dot_zero_left [simp]:
  fixes v :: vec3
  shows "<0 | v> = 0"
  unfolding vec3_dot_def zero_vec3_def by auto

lemma vec3_dot_zero_right [simp]:
  fixes v :: vec3
  shows "<v | 0> = 0"
  unfolding vec3_dot_def zero_vec3_def by auto

consts mat_app :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" (infixr "$" 65)

definition mat2_app :: "mat2 \<Rightarrow> vec2 \<Rightarrow> vec2" where
"mat2_app m v =
  vec2
  (mat2\<^sub>1\<^sub>1 m * vec2\<^sub>1 v + mat2\<^sub>1\<^sub>2 m * vec2\<^sub>2 v)
  (mat2\<^sub>2\<^sub>1 m * vec2\<^sub>1 v + mat2\<^sub>2\<^sub>2 m * vec2\<^sub>2 v)"

adhoc_overloading mat_app mat2_app

definition mat3_app :: "mat3 \<Rightarrow> vec3 \<Rightarrow> vec3" where
"mat3_app m v =
  vec3
  (mat3\<^sub>1\<^sub>1 m * vec3\<^sub>1 v + mat3\<^sub>1\<^sub>2 m * vec3\<^sub>2 v + mat3\<^sub>1\<^sub>3 m * vec3\<^sub>3 v)
  (mat3\<^sub>2\<^sub>1 m * vec3\<^sub>1 v + mat3\<^sub>2\<^sub>2 m * vec3\<^sub>2 v + mat3\<^sub>2\<^sub>3 m * vec3\<^sub>3 v)
  (mat3\<^sub>3\<^sub>1 m * vec3\<^sub>1 v + mat3\<^sub>3\<^sub>2 m * vec3\<^sub>2 v + mat3\<^sub>3\<^sub>3 m * vec3\<^sub>3 v)"

adhoc_overloading mat_app mat3_app

lemma mat2_app_zero [simp]:
  fixes m :: mat2
  shows "m $ 0 = 0"
  unfolding mat2_app_def zero_vec2_def by auto

lemma mat3_app_zero [simp]:
  fixes m :: mat3
  shows "m $ 0 = 0"
  unfolding mat3_app_def zero_vec3_def by auto

lemma mat2_app_one [simp]:
  fixes v :: vec2
  shows "1 $ v = v"
  unfolding mat2_app_def one_mat2_def by auto

lemma mat3_app_one [simp]:
  fixes v :: vec3
  shows "1 $ v = v"
  unfolding mat3_app_def one_mat3_def by auto

lemma mat2_app_mul [simp]:
  fixes m1 m2 :: mat2
  fixes v :: vec2
  shows "m1 * m2 $ v = m1 $ m2 $ v"
  unfolding times_mat2_def mat2_app_def by (simp add: algebra_simps)

lemma mat3_app_mul [simp]:
  fixes m1 m2 :: mat3
  fixes v :: vec3
  shows "m1 * m2 $ v = m1 $ m2 $ v"
  unfolding times_mat3_def mat3_app_def by (simp add: algebra_simps)

consts mat_det :: "'a \<Rightarrow> int"

definition mat2_det where
"mat2_det m = mat2\<^sub>1\<^sub>1 m * mat2\<^sub>2\<^sub>2 m - mat2\<^sub>1\<^sub>2 m * mat2\<^sub>2\<^sub>1 m"

adhoc_overloading mat_det mat2_det

definition mat3_det where
"mat3_det m =
    mat3\<^sub>1\<^sub>1 m * mat3\<^sub>2\<^sub>2 m * mat3\<^sub>3\<^sub>3 m
  + mat3\<^sub>1\<^sub>2 m * mat3\<^sub>2\<^sub>3 m * mat3\<^sub>3\<^sub>1 m
  + mat3\<^sub>1\<^sub>3 m * mat3\<^sub>2\<^sub>1 m * mat3\<^sub>3\<^sub>2 m
  - mat3\<^sub>1\<^sub>1 m * mat3\<^sub>2\<^sub>3 m * mat3\<^sub>3\<^sub>2 m
  - mat3\<^sub>1\<^sub>2 m * mat3\<^sub>2\<^sub>1 m * mat3\<^sub>3\<^sub>3 m
  - mat3\<^sub>1\<^sub>3 m * mat3\<^sub>2\<^sub>2 m * mat3\<^sub>3\<^sub>1 m"

adhoc_overloading mat_det mat3_det

lemma mat2_mul_det [simp]:
  fixes m1 m2 :: mat2
  shows "mat_det (m1 * m2) = mat_det m1 * mat_det m2"
  unfolding times_mat2_def mat2_det_def by (simp; algebra)

lemma mat3_mul_det [simp]:
  fixes m1 m2 :: mat3
  shows "mat_det (m1 * m2) = mat_det m1 * mat_det m2"
  unfolding times_mat3_def mat3_det_def by (simp; algebra)

consts mat_sym :: "'a \<Rightarrow> bool"

definition mat2_sym :: "mat2 \<Rightarrow> bool" where
"mat2_sym m = (mat2\<^sub>1\<^sub>2 m = mat2\<^sub>2\<^sub>1 m)"

adhoc_overloading mat_sym mat2_sym

definition mat3_sym :: "mat3 \<Rightarrow> bool" where
"mat3_sym m = (mat3\<^sub>1\<^sub>2 m = mat3\<^sub>2\<^sub>1 m \<and> mat3\<^sub>1\<^sub>3 m = mat3\<^sub>3\<^sub>1 m \<and> mat3\<^sub>2\<^sub>3 m = mat3\<^sub>3\<^sub>2 m)"

adhoc_overloading mat_sym mat3_sym

consts mat_transpose :: "'a \<Rightarrow> 'a" ("_\<^sup>T" [91] 90)

definition mat2_transpose :: "mat2 \<Rightarrow> mat2" where
"mat2_transpose m =
  mat2
  (mat2\<^sub>1\<^sub>1 m) (mat2\<^sub>2\<^sub>1 m)
  (mat2\<^sub>1\<^sub>2 m) (mat2\<^sub>2\<^sub>2 m)"

adhoc_overloading mat_transpose mat2_transpose

definition mat3_transpose :: "mat3 \<Rightarrow> mat3" where
"mat3_transpose m =
  mat3
  (mat3\<^sub>1\<^sub>1 m) (mat3\<^sub>2\<^sub>1 m) (mat3\<^sub>3\<^sub>1 m)
  (mat3\<^sub>1\<^sub>2 m) (mat3\<^sub>2\<^sub>2 m) (mat3\<^sub>3\<^sub>2 m)
  (mat3\<^sub>1\<^sub>3 m) (mat3\<^sub>2\<^sub>3 m) (mat3\<^sub>3\<^sub>3 m)"

adhoc_overloading mat_transpose mat3_transpose

lemma mat2_transpose_involution [simp]:
  fixes m :: mat2
  shows "(m\<^sup>T)\<^sup>T = m"
  unfolding mat2_transpose_def
  by auto

lemma mat3_transpose_involution [simp]:
  fixes m :: mat3
  shows "(m\<^sup>T)\<^sup>T = m"
  unfolding mat3_transpose_def
  by auto

lemma mat2_sym_criterion:
  fixes m :: mat2
  shows "mat_sym m \<longleftrightarrow> m\<^sup>T = m"
  unfolding mat2_sym_def mat2_transpose_def
  by (cases m; auto)

lemma mat3_sym_criterion:
  fixes m :: mat3
  shows "mat_sym m \<longleftrightarrow> m\<^sup>T = m"
  unfolding mat3_sym_def mat3_transpose_def
  by (cases m; auto)

lemma mat2_transpose_one [simp]: "(1 :: mat2)\<^sup>T = 1"
  unfolding mat2_transpose_def one_mat2_def by auto

lemma mat3_transpose_one [simp]: "(1 :: mat3)\<^sup>T = 1"
  unfolding mat3_transpose_def one_mat3_def by auto

lemma mat2_transpose_mul [simp]:
  fixes a b :: mat2
  shows "(a * b)\<^sup>T = b\<^sup>T * a\<^sup>T"
  unfolding mat2_transpose_def times_mat2_def by auto

lemma mat3_transpose_mul [simp]:
  fixes a b :: mat3
  shows "(a * b)\<^sup>T = b\<^sup>T * a\<^sup>T"
  unfolding mat3_transpose_def times_mat3_def by auto

lemma vec2_dot_transpose_left:
  fixes m :: mat2
  fixes u v :: vec2
  shows "<m\<^sup>T $ u | v> = <u | m $ v>"
  unfolding vec2_dot_def mat2_app_def mat2_transpose_def
  by (simp add: algebra_simps)

lemma vec2_dot_transpose_right:
  fixes m :: mat2
  fixes u v :: vec2
  shows "<u | m\<^sup>T $ v> = <m $ u | v>"
  unfolding vec2_dot_def mat2_app_def mat2_transpose_def
  by (simp add: algebra_simps)

lemma vec3_dot_transpose_left:
  fixes m :: mat3
  fixes u v :: vec3
  shows "<m\<^sup>T $ u | v> = <u | m $ v>"
  unfolding vec3_dot_def mat3_app_def mat3_transpose_def
  by (simp add: algebra_simps)

lemma vec3_dot_transpose_right:
  fixes m :: mat3
  fixes u v :: vec3
  shows "<u | m\<^sup>T $ v> = <m $ u | v>"
  unfolding vec3_dot_def mat3_app_def mat3_transpose_def
  by (simp add: algebra_simps)

lemma mat2_det_tranpose [simp]:
  fixes m :: mat2
  shows "mat_det (m\<^sup>T) = mat_det m"
  unfolding mat2_det_def mat2_transpose_def by auto

lemma mat3_det_tranpose [simp]:
  fixes m :: mat3
  shows "mat_det (m\<^sup>T) = mat_det m"
  unfolding mat3_det_def mat3_transpose_def by auto

consts mat_inverse :: "'a \<Rightarrow> 'a" ("_\<^sup>-\<^sup>1" [91] 90)

definition mat2_inverse :: "mat2 \<Rightarrow> mat2" where
"mat2_inverse m =
  mat2
    (mat2\<^sub>2\<^sub>2 m) (- mat2\<^sub>1\<^sub>2 m)
    (- mat2\<^sub>2\<^sub>1 m) (mat2\<^sub>1\<^sub>1 m)
"

adhoc_overloading mat_inverse mat2_inverse

definition mat3_inverse :: "mat3 \<Rightarrow> mat3" where
"mat3_inverse m =
  mat3
    (mat3\<^sub>2\<^sub>2 m * mat3\<^sub>3\<^sub>3 m - mat3\<^sub>2\<^sub>3 m * mat3\<^sub>3\<^sub>2 m) (mat3\<^sub>1\<^sub>3 m * mat3\<^sub>3\<^sub>2 m - mat3\<^sub>1\<^sub>2 m * mat3\<^sub>3\<^sub>3 m) (mat3\<^sub>1\<^sub>2 m * mat3\<^sub>2\<^sub>3 m - mat3\<^sub>1\<^sub>3 m * mat3\<^sub>2\<^sub>2 m)
    (mat3\<^sub>2\<^sub>3 m * mat3\<^sub>3\<^sub>1 m - mat3\<^sub>2\<^sub>1 m * mat3\<^sub>3\<^sub>3 m) (mat3\<^sub>1\<^sub>1 m * mat3\<^sub>3\<^sub>3 m - mat3\<^sub>1\<^sub>3 m * mat3\<^sub>3\<^sub>1 m) (mat3\<^sub>1\<^sub>3 m * mat3\<^sub>2\<^sub>1 m - mat3\<^sub>1\<^sub>1 m * mat3\<^sub>2\<^sub>3 m)
    (mat3\<^sub>2\<^sub>1 m * mat3\<^sub>3\<^sub>2 m - mat3\<^sub>2\<^sub>2 m * mat3\<^sub>3\<^sub>1 m) (mat3\<^sub>1\<^sub>2 m * mat3\<^sub>3\<^sub>1 m - mat3\<^sub>1\<^sub>1 m * mat3\<^sub>3\<^sub>2 m) (mat3\<^sub>1\<^sub>1 m * mat3\<^sub>2\<^sub>2 m - mat3\<^sub>1\<^sub>2 m * mat3\<^sub>2\<^sub>1 m)
"

adhoc_overloading mat_inverse mat3_inverse

lemma mat2_inverse_cancel:
  fixes m :: mat2
  assumes "mat_det m = 1"
  shows "m * m\<^sup>-\<^sup>1 = 1" "m\<^sup>-\<^sup>1 * m = 1"
  using assms unfolding mat2_det_def mat2_inverse_def times_mat2_def one_mat2_def
  by (auto simp add: algebra_simps)

lemma mat3_inverse_cancel:
  fixes m :: mat3
  assumes "mat_det m = 1"
  shows "m * m\<^sup>-\<^sup>1 = 1" "m\<^sup>-\<^sup>1 * m = 1"
  using assms unfolding mat3_det_def mat3_inverse_def times_mat3_def one_mat3_def
  by (auto simp add: algebra_simps)

lemma mat2_inverse_cancel_left:
  fixes m a :: mat2
  assumes "mat_det m = 1"
  shows "m * (m\<^sup>-\<^sup>1 * a) = a" "m\<^sup>-\<^sup>1 * (m * a) = a"
  unfolding mult.assoc[symmetric]
  using assms mat2_inverse_cancel
  by auto

lemma mat3_inverse_cancel_left:
  fixes m a :: mat3
  assumes "mat_det m = 1"
  shows "m * (m\<^sup>-\<^sup>1 * a) = a" "m\<^sup>-\<^sup>1 * (m * a) = a"
  unfolding mult.assoc[symmetric]
  using assms mat3_inverse_cancel
  by auto

lemma mat2_inverse_cancel_right:
  fixes m a :: mat2
  assumes "mat_det m = 1"
  shows "a * (m * m\<^sup>-\<^sup>1) = a" "a * (m\<^sup>-\<^sup>1 * m) = a"
  using assms mat2_inverse_cancel
  by auto

lemma mat3_inverse_cancel_right:
  fixes m a :: mat3
  assumes "mat_det m = 1"
  shows "a * (m * m\<^sup>-\<^sup>1) = a" "a * (m\<^sup>-\<^sup>1 * m) = a"
  using assms mat3_inverse_cancel
  by auto

lemma mat2_inversable_cancel_left:
  fixes m a1 a2 :: mat2
  assumes "mat_det m = 1"
  assumes "m * a1 = m * a2"
  shows "a1 = a2"
  by (metis assms mat2_inverse_cancel_left(2))

lemma mat3_inversable_cancel_left:
  fixes m a1 a2 :: mat3
  assumes "mat_det m = 1"
  assumes "m * a1 = m * a2"
  shows "a1 = a2"
  by (metis assms mat3_inverse_cancel_left(2))

lemma mat2_inversable_cancel_right:
  fixes m a1 a2 :: mat2
  assumes "mat_det m = 1"
  assumes "a1 * m = a2 * m"
  shows "a1 = a2"
  by (metis assms mat2_inverse_cancel(1) mult.assoc mult.right_neutral)

lemma mat3_inversable_cancel_right:
  fixes m a1 a2 :: mat3
  assumes "mat_det m = 1"
  assumes "a1 * m = a2 * m"
  shows "a1 = a2"
  by (metis assms mat3_inverse_cancel(1) mult.assoc mult.right_neutral)

lemma mat2_inverse_det [simp]:
  fixes m :: mat2
  shows "mat_det (m\<^sup>-\<^sup>1) = mat_det m"
  unfolding mat2_inverse_def mat2_det_def
  by auto

lemma mat3_inverse_det [simp]:
  fixes m :: mat3
  shows "mat_det (m\<^sup>-\<^sup>1) = (mat_det m)\<^sup>2"
  unfolding mat3_inverse_def mat3_det_def power2_eq_square
  by (simp add: algebra_simps)

lemma mat2_inverse_transpose:
  fixes m :: mat2
  shows "(m\<^sup>T)\<^sup>-\<^sup>1 = (m\<^sup>-\<^sup>1)\<^sup>T"
  unfolding mat2_inverse_def mat2_transpose_def
  by auto

lemma mat3_inverse_transpose:
  fixes m :: mat3
  shows "(m\<^sup>T)\<^sup>-\<^sup>1 = (m\<^sup>-\<^sup>1)\<^sup>T"
  unfolding mat3_inverse_def mat3_transpose_def
  by auto

lemma mat2_special_preserves_zero:
  fixes u :: mat2
  fixes v :: vec2
  assumes "mat_det u = 1"
  shows "u $ v = 0 \<longleftrightarrow> v = 0"
proof
  assume "u $ v = 0"
  hence "u\<^sup>-\<^sup>1 $ u $ v = 0" by auto
  hence "(u\<^sup>-\<^sup>1 * u) $ v = 0" by auto
  thus "v = 0" using assms mat2_inverse_cancel by auto
next
  assume "v = 0"
  thus "u $ v = 0" by auto
qed

lemma mat3_special_preserves_zero:
  fixes u :: mat3
  fixes v :: vec3
  assumes "mat_det u = 1"
  shows "u $ v = 0 \<longleftrightarrow> v = 0"
proof
  assume "u $ v = 0"
  hence "u\<^sup>-\<^sup>1 $ u $ v = 0" by auto
  hence "(u\<^sup>-\<^sup>1 * u) $ v = 0" by auto
  thus "v = 0" using assms mat3_inverse_cancel by auto
next
  assume "v = 0"
  thus "u $ v = 0" by auto
qed

end
