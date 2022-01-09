theory Matrix_Util
  imports "HOL-Analysis.Analysis"
begin

section \<open>Matrices\<close>

proposition scalar_matrix_assoc':
  fixes C :: "('b::real_algebra_1)^'m^'n"
  shows "k *\<^sub>R (C ** D) = C ** (k *\<^sub>R D)"
  by (simp add: matrix_matrix_mult_def sum_distrib_left mult_ac vec_eq_iff scaleR_sum_right)

subsection \<open>Nonnegative Matrices\<close>

lemma nonneg_matrix_nonneg [dest]: "0 \<le> m \<Longrightarrow> 0 \<le> m $ i $ j"
  by (simp add: Finite_Cartesian_Product.less_eq_vec_def)

lemma matrix_mult_mono: 
  assumes "0 \<le> E" "0 \<le> C" "(E :: real^'c^'c) \<le> B" "C \<le> D"
  shows "E ** C \<le> B ** D"
  using order.trans[OF assms(1) assms(3)] assms
  unfolding Finite_Cartesian_Product.less_eq_vec_def
  by (auto intro!: sum_mono mult_mono simp: matrix_matrix_mult_def)

lemma nonneg_matrix_mult: "0 \<le> (C :: ('b::{field, ordered_ring})^_^_) \<Longrightarrow> 0 \<le> D \<Longrightarrow> 0 \<le> C ** D"
  unfolding Finite_Cartesian_Product.less_eq_vec_def
  by (auto simp: matrix_matrix_mult_def intro!: sum_nonneg)

lemma zero_le_mat_iff [simp]: "0 \<le> mat (x :: 'c :: {zero, order}) \<longleftrightarrow> 0 \<le> x"
  by (auto simp: Finite_Cartesian_Product.less_eq_vec_def mat_def)

lemma nonneg_mat_ge_zero: "0 \<le> Q \<Longrightarrow> 0 \<le> v \<Longrightarrow> 0 \<le> Q *v (v :: real^'c)"
  unfolding Finite_Cartesian_Product.less_eq_vec_def
  by (auto intro!: sum_nonneg simp: matrix_vector_mult_def)

lemma nonneg_mat_mono: "0 \<le> Q \<Longrightarrow> u \<le> v \<Longrightarrow> Q *v u \<le> Q *v (v :: real^'c)"
  using nonneg_mat_ge_zero[of Q "v - u"]
  by (simp add: vec.diff)

lemma nonneg_mult_imp_nonneg_mat:
  assumes "\<And>v. v \<ge> 0 \<Longrightarrow> X *v v \<ge> 0"
  shows "X \<ge> (0 :: real ^ _ ^_)"
proof -
  { assume "\<not> (0 \<le> X)"
    then obtain i j where neg: "X $ i $ j < 0" 
      by (metis less_eq_vec_def not_le zero_index)
    let ?v = "\<chi> k. if j = k then 1::real else 0"
    have "(X *v ?v) $ i < 0"
      using neg
      by (auto simp: matrix_vector_mult_def if_distrib cong: if_cong)
    hence "?v \<ge> 0 \<and> \<not> ((X *v ?v) \<ge> 0)"
      by (auto simp: less_eq_vec_def not_le)
    hence "\<exists>v. v \<ge> 0 \<and> \<not> X *v v \<ge> 0"
      by blast
  }
  thus ?thesis
    using assms by auto
qed

lemma nonneg_mat_iff:
  "(X \<ge> (0 :: real ^ _ ^_)) \<longleftrightarrow> (\<forall>v. v \<ge> 0 \<longrightarrow> X *v v \<ge> 0)"
  using nonneg_mat_ge_zero nonneg_mult_imp_nonneg_mat by auto

lemma mat_le_iff: "(X \<le> Y) \<longleftrightarrow> (\<forall>x\<ge>0. (X::real^_^_) *v x \<le> Y *v x)"
  by (metis diff_ge_0_iff_ge matrix_vector_mult_diff_rdistrib nonneg_mat_iff)

subsection \<open>Matrix Powers\<close>

(* copied from Perron-Frobenius *)
primrec matpow :: "'a::semiring_1^'n^'n \<Rightarrow> nat \<Rightarrow> 'a^'n^'n" where
  matpow_0:   "matpow A 0 = mat 1" |
  matpow_Suc: "matpow A (Suc n) = (matpow A n) ** A"

lemma nonneg_matpow: "0 \<le> X \<Longrightarrow> 0 \<le> matpow (X :: real ^ _ ^ _) i"
  by (induction i) (auto simp: nonneg_matrix_mult)

lemma matpow_mono: "0 \<le> C \<Longrightarrow> C \<le> D \<Longrightarrow> matpow (C :: real^_^_) n \<le> matpow D n"
  by (induction n) (auto intro!: matrix_mult_mono nonneg_matpow)

lemma matpow_scaleR: "matpow (c *\<^sub>R (X :: 'b :: real_algebra_1^_^_)) n = (c^n) *\<^sub>R (matpow X) n"
proof (induction n arbitrary: X c)
  case (Suc n)
  have "matpow (c *\<^sub>R X) (Suc n) = (c^n)*\<^sub>R (matpow X) n ** c *\<^sub>R X"
    using Suc by auto
  also have "\<dots> = c *\<^sub>R ((c^n) *\<^sub>R (matpow X) n ** X)"
    using scalar_matrix_assoc' 
    by (auto simp: scalar_matrix_assoc')
  finally show ?case
    by (simp add: scalar_matrix_assoc)
qed auto

lemma matrix_vector_mult_code': "(X *v x) $ i = (\<Sum>j\<in>UNIV. X $ i $ j * x $ j)"
  by (simp add: matrix_vector_mult_def)

lemma matrix_vector_mult_mono: "(0::real^_^_) \<le> X \<Longrightarrow> 0 \<le> v \<Longrightarrow> X \<le> Y \<Longrightarrow> X *v v \<le> Y *v v"
  by (metis diff_ge_0_iff_ge matrix_vector_mult_diff_rdistrib nonneg_mat_iff)

subsection \<open>Triangular Matrices\<close>

definition "lower_triangular_mat X \<longleftrightarrow> (\<forall>i j. (i :: 'b::{finite, linorder}) < j \<longrightarrow> X $ i $ j = 0)"

definition "strict_lower_triangular_mat X \<longleftrightarrow> (\<forall>i j. (i :: 'b::{finite, linorder}) \<le> j \<longrightarrow> X $ i $ j = 0)"

definition "upper_triangular_mat X \<longleftrightarrow> (\<forall>i j. j < i \<longrightarrow> X $ i $ j = 0)"

lemma stlI: "strict_lower_triangular_mat X \<Longrightarrow> lower_triangular_mat X"
  unfolding strict_lower_triangular_mat_def lower_triangular_mat_def
  by auto

lemma lower_triangular_mat_mat: "lower_triangular_mat (mat x)"
  unfolding lower_triangular_mat_def mat_def
  by auto

lemma lower_triangular_mult:
  assumes "lower_triangular_mat X" "lower_triangular_mat Y"
  shows "lower_triangular_mat (X ** Y)"
  using assms 
  unfolding matrix_matrix_mult_def lower_triangular_mat_def
  by (auto intro!: sum.neutral) (metis mult_not_zero neqE less_trans)

lemma lower_triangular_pow:
  assumes "lower_triangular_mat X"
  shows "lower_triangular_mat (matpow X i)"
  using assms lower_triangular_mult lower_triangular_mat_mat
  by (induction i) auto

lemma lower_triangular_suminf:
  assumes "\<And>i. lower_triangular_mat (f i)" "summable (f :: nat \<Rightarrow> 'b::real_normed_vector^_^_)" 
  shows "lower_triangular_mat (\<Sum>i. f i)"
  using assms
  unfolding lower_triangular_mat_def
  by (subst bounded_linear.suminf) (auto intro: bounded_linear_compose)

lemma lower_triangular_pow_eq:
  assumes "lower_triangular_mat X" "lower_triangular_mat Y" "\<And>s'. s' \<le> s \<Longrightarrow> row s' X = row s' Y" "s' \<le> s"
  shows "row s' (matpow X i) = row s' (matpow Y i)"
  using assms
proof (induction i)
  case (Suc i)
  thus ?case
  proof -
    have ltX: "lower_triangular_mat (matpow X i)"
      by (simp add: Suc(2) lower_triangular_pow)
    have ltY: "lower_triangular_mat (matpow Y i)"
      by (simp add: Suc(3) lower_triangular_pow)
    have " (\<Sum>k\<in>UNIV. matpow X i $ s' $ k * X $ k $ j) = (\<Sum>k\<in>UNIV. matpow Y i $ s' $ k * Y $ k $ j)" for j
    proof -
      have "(\<Sum>k\<in>UNIV. matpow X i $ s' $ k * X $ k $ j) = (\<Sum>k\<in>UNIV. if s' < k then 0 else matpow Y i $ s' $ k * X $ k $ j)"
        using Suc ltY
        by (auto simp: row_def lower_triangular_mat_def intro!: sum.cong)
      also have "\<dots> = (\<Sum>k \<in> UNIV . matpow Y i $ s' $ k * Y $ k $ j)"
        using Suc ltY
        by (auto simp: row_def lower_triangular_mat_def cong: if_cong intro!: sum.cong)
      finally show ?thesis.
    qed
    thus ?thesis
      by (auto simp: row_def matrix_matrix_mult_def)
  qed
qed simp

lemma lower_triangular_mat_mult:
  assumes "lower_triangular_mat M" "\<And>i. i \<le> j \<Longrightarrow> v $ i = v' $ i"
  shows "(M *v v) $ j = (M *v v') $ j"
proof -
  have "(M *v v) $ j = (\<Sum>i\<in>UNIV. (if j < i then 0 else  M $ j $ i * v $ i))"
    using assms unfolding lower_triangular_mat_def
    by (auto simp: matrix_vector_mult_def intro!: sum.cong)
  also have "\<dots> = (\<Sum>i\<in>UNIV. (if j < i then 0 else  M $ j $ i * v' $ i))"
    using assms
    by (auto intro!: sum.cong)
  also have "\<dots> = (M *v v') $ j"
    using assms unfolding lower_triangular_mat_def
    by (auto simp: matrix_vector_mult_def intro!: sum.cong)
  finally show ?thesis.
qed

subsection \<open>Inverses\<close>

(* from AFP/Rank_Nullity_Theorem *)
lemma matrix_inv:
  assumes "invertible M"
  shows matrix_inv_left: "matrix_inv M ** M = mat 1"
    and matrix_inv_right: "M ** matrix_inv M = mat 1"
  using \<open>invertible M\<close> and someI_ex [of "\<lambda> N. M ** N = mat 1 \<and> N ** M = mat 1"]
  unfolding invertible_def and matrix_inv_def
  by simp_all

(* from AFP/Rank_Nullity_Theorem *)
lemma matrix_inv_unique:
  fixes A::"'a::{semiring_1}^'n^'n"
  assumes AB: "A ** B = mat 1" and BA: "B ** A = mat 1"
  shows "matrix_inv A = B"
  by (metis AB BA invertible_def matrix_inv_right matrix_mul_assoc matrix_mul_lid) 

end