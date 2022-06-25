theory Blinfun_Matrix
  imports 
    "MDP-Rewards.Blinfun_Util" 
    Matrix_Util
begin

section \<open>Bounded Linear Functions and Matrices\<close>

definition "blinfun_to_matrix (f :: ('b::finite \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('c::finite \<Rightarrow>\<^sub>b _)) = 
  matrix (\<lambda>v. (\<chi> j. f (Bfun (($) v)) j))"

definition "matrix_to_blinfun X = Blinfun (\<lambda>v. Bfun (\<lambda>i. (X *v (\<chi> i. (apply_bfun v i))) $ i))"

lemma plus_vec_eq: "(\<chi> i. f i  + g i) = (\<chi> i. f i) + (\<chi> i. g i)"
  by (simp add: Finite_Cartesian_Product.plus_vec_def)

lemma matrix_to_blinfun_mult: "matrix_to_blinfun m (v :: 'c::finite \<Rightarrow>\<^sub>b real) i = (m *v (\<chi> i. v i)) $ i"
proof -
  have [simp]: "(\<chi> i. c * x i) = c *\<^sub>R (\<chi> i. x i)" for c x
    by (simp add: vector_scalar_mult_def scalar_mult_eq_scaleR[symmetric])

  have "bounded_linear (\<lambda>v. bfun.Bfun (($) (m *v vec_lambda (apply_bfun v))))"
  proof (rule bounded_linear_compose[of "\<lambda>x. bfun.Bfun (\<lambda>y. x $ y)"], goal_cases)
    case 1
    then show ?case
      using bounded_linear_bfun_nth[of id, simplified] bounded_linear_ident eq_id_iff 
      by metis
  next
    case 2
    then show ?case
      using norm_vec_le_norm_bfun
      by (auto simp: matrix_vector_right_distrib plus_vec_eq
          intro!: bounded_linear_intro bounded_linear_compose[OF matrix_vector_mul_bounded_linear])
  qed
  thus ?thesis
    by (auto simp: Blinfun_inverse matrix_to_blinfun_def Bfun_inverse)
qed

lemma blinfun_to_matrix_mult: "(blinfun_to_matrix f *v (\<chi> i. apply_bfun v i)) $ i = f v i"
proof -
  have "(blinfun_to_matrix f *v (\<chi> i. v i)) $ i = (\<Sum>j\<in>UNIV. (f ((v j *\<^sub>R bfun.Bfun (\<lambda>i. if i = j then 1 else 0)))) i)"
    unfolding blinfun_to_matrix_def matrix_def
    by (auto simp: matrix_vector_mult_def mult.commute axis_def blinfun.scaleR_right vec_lambda_inverse)
  also have "\<dots> = (\<Sum>j\<in>UNIV. (f ((v j *\<^sub>R bfun.Bfun (\<lambda>i. if i = j then 1 else 0))))) i"
    by (auto intro: finite_induct)
  also have "\<dots> = f (\<Sum>j\<in>UNIV. (v j *\<^sub>R bfun.Bfun (\<lambda>i. if i = j then 1 else 0))) i"
    by (auto simp: blinfun.sum_right)
  also have "\<dots> = f v i"
  proof -
    have "(\<Sum>j\<in>UNIV. (v j *\<^sub>R bfun.Bfun (\<lambda>i. if i = j then 1 else 0))) x = v x" for x
    proof -
      have "(\<Sum>j\<in>UNIV. (v j *\<^sub>R bfun.Bfun (\<lambda>i. if i = j then 1 else 0))) x = 
        (\<Sum>j\<in>UNIV. (v j *\<^sub>R bfun.Bfun (\<lambda>i. if i = j then 1 else 0) x))"
        by (auto intro: finite_induct)
      also have "\<dots> = (\<Sum>j\<in>UNIV. (v j *\<^sub>R (\<lambda>i. if i = j then 1 else 0) x))"
        by (subst Bfun_inverse) (metis vec_bfun vec_lambda_inverse[OF UNIV_I, symmetric])+
      also have "\<dots> = (\<Sum>j\<in>UNIV. ((if x = j then v j * 1 else v j * 0)))"
        by (auto simp: if_distrib intro!: sum.cong)
      also have "\<dots> = (\<Sum>j\<in>UNIV. ((if x = j then v j else 0)))"
        by (meson more_arith_simps(6) mult_zero_right)
      also have "\<dots> = v x"
        by auto
      finally show ?thesis.
    qed
    thus ?thesis
      using bfun_eqI
      by fastforce
  qed
  finally show ?thesis.
qed

lemma blinfun_to_matrix_mult': "(blinfun_to_matrix f *v v) $ i = f (Bfun (\<lambda>i. v $ i)) i"
  by (metis bfun.Bfun_inverse blinfun_to_matrix_mult vec_bfun vec_nth_inverse)

lemma blinfun_to_matrix_mult'': "(blinfun_to_matrix f *v v) = (\<chi> i. f (Bfun (\<lambda>i. v $ i)) i)"
  by (metis blinfun_to_matrix_mult' vec_lambda_unique)

lemma matrix_to_blinfun_inv: "matrix_to_blinfun (blinfun_to_matrix f) = f"
  by (auto simp: matrix_to_blinfun_mult blinfun_to_matrix_mult intro!: blinfun_eqI)

lemma blinfun_to_matrix_add: "blinfun_to_matrix (f + g) = blinfun_to_matrix f + blinfun_to_matrix g"
  by (simp add: matrix_eq  blinfun_to_matrix_mult'' matrix_vector_mult_add_rdistrib blinfun.add_left plus_vec_eq)

lemma blinfun_to_matrix_diff: "blinfun_to_matrix (f - g) = blinfun_to_matrix f - blinfun_to_matrix g"
  using blinfun_to_matrix_add
  by (metis add_right_imp_eq diff_add_cancel)

lemma blinfun_to_matrix_scaleR: "blinfun_to_matrix (c *\<^sub>R f) = c *\<^sub>R blinfun_to_matrix f"
  by (auto simp: matrix_eq blinfun_to_matrix_mult'' scaleR_matrix_vector_assoc[symmetric] 
      blinfun.scaleR_left vector_scalar_mult_def[of c, unfolded scalar_mult_eq_scaleR]) 

lemma matrix_to_blinfun_add: 
  "matrix_to_blinfun ((f :: real^_^_) + g) = matrix_to_blinfun f + matrix_to_blinfun g"
  by (auto intro!: blinfun_eqI simp: matrix_to_blinfun_mult blinfun.add_left matrix_vector_mult_add_rdistrib)

lemma matrix_to_blinfun_diff: 
  "matrix_to_blinfun ((f :: real^_^_) - g) = matrix_to_blinfun f - matrix_to_blinfun g"
  using matrix_to_blinfun_add diff_eq_eq
  by metis

lemma matrix_to_blinfun_scaleR: 
  "matrix_to_blinfun (c *\<^sub>R (f :: real^_^_)) = c *\<^sub>R matrix_to_blinfun f"
  by (auto intro!: blinfun_eqI simp: matrix_to_blinfun_mult blinfun.scaleR_left 
      matrix_vector_mult_add_rdistrib scaleR_matrix_vector_assoc[symmetric])

lemma matrix_to_blinfun_comp: "matrix_to_blinfun ((m:: real^_^_) ** n) = (matrix_to_blinfun m) o\<^sub>L (matrix_to_blinfun n)"
  by (auto intro!: blinfun_eqI simp: matrix_vector_mul_assoc[symmetric] matrix_to_blinfun_mult)

lemma blinfun_to_matrix_comp: "blinfun_to_matrix (f o\<^sub>L g) = (blinfun_to_matrix f) ** (blinfun_to_matrix g)"
  by (simp add: matrix_eq apply_bfun_inverse blinfun_to_matrix_mult'' matrix_vector_mul_assoc[symmetric])

lemma blinfun_to_matrix_id: "blinfun_to_matrix id_blinfun = mat 1"
  by (simp add: Bfun_inverse blinfun_to_matrix_mult'' matrix_eq)

lemma matrix_to_blinfun_id: "matrix_to_blinfun (mat 1 :: (real ^_^_)) = id_blinfun"
  by (auto intro!: blinfun_eqI simp: matrix_to_blinfun_mult)

lemma matrix_to_blinfun_inv\<^sub>L:
  assumes "invertible m"
  shows "matrix_to_blinfun (matrix_inv (m :: real^_^_)) = inv\<^sub>L (matrix_to_blinfun m)"
    "invertible\<^sub>L (matrix_to_blinfun m)"
proof -
  have "m ** matrix_inv m = mat 1" "matrix_inv m ** m = mat 1"
    using assms 
    by (auto simp: matrix_inv_right matrix_inv_left)
  hence "matrix_to_blinfun (matrix_inv m) o\<^sub>L matrix_to_blinfun m = id_blinfun" 
    "matrix_to_blinfun m o\<^sub>L matrix_to_blinfun (matrix_inv m) = id_blinfun"
    by (auto simp: matrix_to_blinfun_id matrix_to_blinfun_comp[symmetric])
  thus "matrix_to_blinfun (matrix_inv m) = inv\<^sub>L (matrix_to_blinfun m)" "invertible\<^sub>L (matrix_to_blinfun m)"
    by (auto intro: inv\<^sub>L_I)
qed


lemma blinfun_to_matrix_inverse:
  assumes "invertible\<^sub>L X"
  shows "invertible (blinfun_to_matrix (X :: ('b::finite \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L 'c::finite \<Rightarrow>\<^sub>b real))" 
    "blinfun_to_matrix (inv\<^sub>L X) = matrix_inv (blinfun_to_matrix X)"
proof -
  have "X o\<^sub>L inv\<^sub>L X = id_blinfun"
    by (simp add: assms)
  hence 1: "blinfun_to_matrix X ** blinfun_to_matrix (inv\<^sub>L X) = mat 1"
    by (metis blinfun_to_matrix_comp blinfun_to_matrix_id)
  have "inv\<^sub>L X o\<^sub>L X = id_blinfun"
    by (simp add: assms)
  hence 2: "blinfun_to_matrix (inv\<^sub>L X) ** blinfun_to_matrix (X) = mat 1"
    by (metis blinfun_to_matrix_comp blinfun_to_matrix_id)
  thus "invertible (blinfun_to_matrix X)"
    using "1" invertible_def by blast
  thus "blinfun_to_matrix (inv\<^sub>L X) = matrix_inv (blinfun_to_matrix X)"
    using 1 2 matrix_inv_right matrix_mul_assoc matrix_mul_lid
    by metis
qed

lemma blinfun_to_matrix_inv[simp]: "blinfun_to_matrix (matrix_to_blinfun f) = f"
  by (auto simp: matrix_eq blinfun_to_matrix_mult'' matrix_to_blinfun_mult bfun.Bfun_inverse)

lemma invertible_invertible\<^sub>L_I: "invertible (blinfun_to_matrix f) \<Longrightarrow> invertible\<^sub>L f"
  "invertible\<^sub>L (matrix_to_blinfun X) \<Longrightarrow> invertible (X :: real^_^_)"
  using matrix_to_blinfun_inv\<^sub>L(2) blinfun_to_matrix_inverse(1) matrix_to_blinfun_inv blinfun_to_matrix_inv 
  by metis+

lemma bounded_linear_blinfun_to_matrix: "bounded_linear (blinfun_to_matrix :: ('a \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('b \<Rightarrow>\<^sub>b real) \<Rightarrow> real^'a^'b)"
proof (intro bounded_linear_intro[of _ "real CARD('a::finite) * real CARD('b::finite)"])
  show "\<And>x y. blinfun_to_matrix (x + y) = blinfun_to_matrix x + blinfun_to_matrix y"
    by (auto simp: blinfun_to_matrix_add blinfun_to_matrix_scaleR)
next
  show "\<And>r x. blinfun_to_matrix (r *\<^sub>R x) = r *\<^sub>R blinfun_to_matrix x"
    by (auto simp: blinfun_to_matrix_def matrix_def blinfun.scaleR_left vec_eq_iff)
next
  have *: "\<And>j. (\<lambda>i. if i = j then 1::real else 0) \<in> bfun"
    by auto
  hence **: "\<And>j. norm (Bfun (\<lambda>i. if i = j then 1::real else 0)) = 1"
    by (auto simp: Bfun_inverse[OF *] norm_bfun_def' intro!: cSup_eq_maximum )
  show "norm (blinfun_to_matrix x) \<le> norm x * (real CARD('a) * real CARD('b))" for x :: "('a \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L 'b \<Rightarrow>\<^sub>b real"
  proof -
    have "norm (blinfun_to_matrix x) \<le> (\<Sum>i\<in>UNIV. \<Sum>ia\<in>UNIV. \<bar>(x (bfun.Bfun (\<lambda>i. if i = ia then 1 else 0))) i\<bar>)"
      unfolding norm_vec_def blinfun_to_matrix_def matrix_def axis_def
      by(auto simp: vec_lambda_inverse intro!: order.trans[OF L2_set_le_sum_abs] order.trans[OF sum_mono[OF L2_set_le_sum_abs]])
    also have "\<dots> \<le> (\<Sum>i\<in>(UNIV::'b set). \<Sum>ia\<in>(UNIV :: 'a set). norm x)"
      using norm_blinfun abs_le_norm_bfun
      by (fastforce simp: ** intro!: sum_mono intro: order.trans)
    also have "\<dots> = norm x * (real CARD('a) * real CARD('b))"
      by auto
    finally show ?thesis.
  qed
qed

lemma summable_blinfun_to_matrix:
  assumes "summable (f :: nat \<Rightarrow> ('c::finite \<Rightarrow>\<^sub>b _) \<Rightarrow>\<^sub>L ('c \<Rightarrow>\<^sub>b _))"
  shows "summable (\<lambda>i. blinfun_to_matrix (f i))"
  by (simp add: assms bounded_linear.summable bounded_linear_blinfun_to_matrix)

abbreviation "nonneg_blinfun Q \<equiv> 0 \<le> (blinfun_to_matrix Q)"

lemma nonneg_blinfun_mono: "nonneg_blinfun Q \<Longrightarrow> u \<le> v \<Longrightarrow> Q u \<le> Q v"
  using nonneg_mat_mono[of "blinfun_to_matrix Q" "vec_lambda u" "vec_lambda v"]
  by (fastforce simp: blinfun_to_matrix_mult'' apply_bfun_inverse Finite_Cartesian_Product.less_eq_vec_def)

lemma nonneg_blinfun_nonneg: "nonneg_blinfun Q \<Longrightarrow> 0 \<le> v \<Longrightarrow> 0 \<le> Q v"
  using nonneg_blinfun_mono blinfun.zero_right
  by metis

lemma nonneg_id_blinfun: "nonneg_blinfun id_blinfun"
  by (auto simp: blinfun_to_matrix_id)

lemma norm_nonneg_blinfun_one:
  assumes "0 \<le> blinfun_to_matrix X"
  shows "norm X = norm (blinfun_apply X 1)"
  by (simp add: norm_blinfun_mono_eq_one assms nonneg_blinfun_nonneg)

lemma matrix_le_norm_mono:
  assumes "0 \<le> (blinfun_to_matrix C)"
    and "(blinfun_to_matrix C) \<le> (blinfun_to_matrix D)"
  shows "norm C \<le> norm D"
proof -
  have "0 \<le> C 1" "0 \<le> D 1"
    using assms zero_le_one 
    by (fastforce intro!: nonneg_blinfun_nonneg)+
  have "\<And>v. v \<ge> 0 \<Longrightarrow> blinfun_to_matrix C *v v \<le> blinfun_to_matrix D *v v"
    using assms nonneg_mat_mono[of "blinfun_to_matrix D - blinfun_to_matrix C"]
    by (fastforce simp: matrix_vector_mult_diff_rdistrib)
  hence *: "\<And>v. v \<ge> 0 \<Longrightarrow> C v \<le> D v"
    by (auto simp: less_eq_vec_def less_eq_bfun_def blinfun_to_matrix_mult[symmetric])
  show ?thesis
    using assms(1) assms(2) \<open>0 \<le> C 1\<close> \<open>0 \<le> D 1\<close> less_eq_bfunD[OF *, of 1]
    by (fastforce intro!: cSUP_mono simp: norm_nonneg_blinfun_one norm_bfun_def' less_eq_bfun_def)
qed

lemma blinfun_to_matrix_matpow: "blinfun_to_matrix (X ^^ i) = matpow (blinfun_to_matrix X) i"
  by (induction i) (auto simp: blinfun_to_matrix_id blinfun_to_matrix_comp blinfunpow_assoc simp del: blinfunpow.simps(2))

lemma nonneg_blinfun_iff: "nonneg_blinfun X \<longleftrightarrow> (\<forall>v\<ge>0. X v \<ge> 0)" 
  using nonneg_mat_iff[of "blinfun_to_matrix X"] nonneg_blinfun_nonneg
  by (auto simp: blinfun_to_matrix_mult'' bfun.Bfun_inverse less_eq_vec_def less_eq_bfun_def)

lemma blinfun_apply_mono: "(0::real^_^_) \<le> blinfun_to_matrix X \<Longrightarrow> 0 \<le> v \<Longrightarrow> blinfun_to_matrix X \<le> blinfun_to_matrix Y \<Longrightarrow> X v \<le> Y v"
  by (metis blinfun.diff_left blinfun_to_matrix_diff diff_ge_0_iff_ge nonneg_blinfun_nonneg)

end