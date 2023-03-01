theory Blinfun_To_Matrix
  imports 
    "Jordan_Normal_Form.Matrix"  
    "Perron_Frobenius.HMA_Connect" 
    "MDP-Rewards.Blinfun_Util"
begin
unbundle no_vec_syntax
hide_const Finite_Cartesian_Product.vec
hide_type Finite_Cartesian_Product.vec
subsubsection \<open>Gauss Seidel is a Regular Splitting\<close>

abbreviation "mat_inv m \<equiv> the (mat_inverse m)"

lemma all_imp_Max:
  assumes "finite X" "X \<noteq> {}" "\<forall>x \<in> X. P (f x)" 
  shows "P (MAX x \<in> X. f x)"
proof -
  have "(MAX x \<in> X. f x) \<in> f ` X"
    using assms
    by auto
  thus ?thesis
    using assms by force
qed

lemma vec_add: "Matrix.vec n (\<lambda>i. f i + g i) = Matrix.vec n f + Matrix.vec n g"
  by auto

lemma vec_scale: "Matrix.vec n (\<lambda>i. r * f i) = r \<cdot>\<^sub>v (Matrix.vec n f)"
  by auto


lift_definition bfun_mat :: "real mat \<Rightarrow> (nat \<Rightarrow>\<^sub>b real) \<Rightarrow> (nat \<Rightarrow>\<^sub>b real)" is "(\<lambda>m v i. 
    if i < dim_row m  then (m *\<^sub>v (Matrix.vec (dim_col m) (apply_bfun v))) $ i else 0)"
proof 
  fix m :: "real mat" and v
  have "norm(if i < dim_row m then (m *\<^sub>v Matrix.vec (dim_col m) (apply_bfun v)) $v i else 0) \<le> 
    (if dim_row m = 0 then 0 else (MAX i \<in> {0..<dim_row m}. \<bar>(m *\<^sub>v Matrix.vec (dim_col m) (apply_bfun v)) $v i\<bar>))" for i
    by (force  simp: Max_ge_iff)
  thus "bounded (range (\<lambda>i. if i < dim_row m then (m *\<^sub>v Matrix.vec (dim_col m) (apply_bfun v)) $v i else 0))"
    by (blast intro!: boundedI)
qed

definition "blinfun_to_mat m n (f :: (nat \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L (nat \<Rightarrow>\<^sub>b _)) = 
  Matrix.mat m n (\<lambda>(i, j). f (Bfun (\<lambda>k. if j = k then 1 else 0)) i)"

lemma bounded_mult: 
  assumes "bounded ((f :: 'c \<Rightarrow> real) ` X)" "bounded (g ` X)"
  shows "bounded ((\<lambda>x. f x * g x) ` X)"
proof -
  obtain a b :: real where "\<forall>x\<in>X. norm (f x) \<le> a"  "\<forall>x\<in>X. norm (g x) \<le> b"  
    using assms  by (auto simp: bounded_iff)
  hence "norm (f x * g x) \<le> a * b" if "x \<in> X" for x
    using that by (auto simp: abs_mult intro!: mult_mono)
  thus ?thesis
    by (fastforce intro!: boundedI)
qed

lift_definition mat_to_blinfun :: "real mat \<Rightarrow>  (nat \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L (nat \<Rightarrow>\<^sub>b real)" is bfun_mat
proof
  show "bfun_mat m (x + y) = bfun_mat m x + bfun_mat m y" for m x y
    by (auto simp: vec_add bfun_mat.rep_eq scalar_prod_add_distrib[of _ "dim_col m"])
  show "bfun_mat m (x *\<^sub>R y) = x *\<^sub>R bfun_mat m y" for m x y
    by (auto simp: vec_scale bfun_mat.rep_eq)
  have aux: "0 \<le> Max (abs ` elements_mat (m::real mat))"  if "0 < dim_row m" "0 < dim_col m" for m
    using that by (auto intro: all_imp_Max abs_le_norm_bfun simp: elements_mat_def)
    
  have 1: "\<bar>\<Sum>i = 0..<dim_col (m::real mat). m $$ (n, i) * apply_bfun x i\<bar> \<le> (\<Sum>i = 0..<dim_col m. \<bar>m $$ (n, i) * apply_bfun x i\<bar>)" for x m n
    by (rule sum_abs)
  have 2: "(\<Sum>i = 0..<dim_col m. \<bar>(m::real mat) $$ (n, i) * apply_bfun x i\<bar>) \<le> (\<Sum>i = 0..<dim_col m. Max (abs ` elements_mat m) * \<bar>apply_bfun x i\<bar>) " if "n < dim_row m" for x m n
    unfolding abs_mult elements_mat_def using that by (fastforce intro!: mult_right_mono sum_mono Max_ge)
  have 3: "(\<Sum> i = 0..<dim_col m. Max (abs ` elements_mat m) * \<bar>apply_bfun x i\<bar>) \<le> (\<Sum>i = 0..<dim_col m. Max (abs ` elements_mat m) * norm x)" if "n < dim_row m" for x m n
    using that aux by (intro sum_mono) (auto intro!:  mult_left_mono abs_le_norm_bfun )

  have 4: "(\<Sum>i = 0..<dim_col (m::real mat). Max (abs ` elements_mat m) * norm (x :: (_  \<Rightarrow>\<^sub>b _))) = norm x * dim_col m *  Max (abs ` (elements_mat m))" if "n < dim_row m" for n x m
    using that by auto

  have "\<bar>\<Sum>i = 0..<dim_col (m::real mat). m $$ (n, i) * apply_bfun x i\<bar> \<le> norm x * dim_col m *  Max (abs ` (elements_mat m))" if "n < dim_row m" for x m n
    using order.trans[OF order.trans[OF 1 2[OF that]] 3]  that unfolding 4[OF that] by auto
  hence "norm (bfun_mat m x) \<le> norm x * (if (dim_col m = 0 \<or> dim_row m = 0) then 0 else dim_col m * Max (abs ` (elements_mat m)))" for m x
    using aux 
    by (auto intro!: cSup_least bfun_eqI simp: norm_bfun_def'[of "bfun_mat _ _"] bfun_mat.rep_eq scalar_prod_def mult.assoc)
  thus "\<exists>K. \<forall>x. norm (bfun_mat m x) \<le> norm x * K" for m
    by auto
qed

lemma mat_to_blinfun_mult: "mat_to_blinfun m (v :: nat \<Rightarrow>\<^sub>b real) i = bfun_mat m v i"
  by (simp add: mat_to_blinfun.rep_eq)

lemma blinfun_to_mat_add_scale: "blinfun_to_mat n m (v + b *\<^sub>R u) = blinfun_to_mat n m v + b \<cdot>\<^sub>m (blinfun_to_mat n m u)"
  unfolding blinfun_to_mat_def blinfun.add_left blinfun.scaleR_left
  by auto

lemma mat_scale_one[simp]: "1 \<cdot>\<^sub>m (m::real mat) = m"
  unfolding smult_mat_def
  by (auto simp: map_mat_def mat_eq_iff)

lemma blinfun_to_mat_add: "(blinfun_to_mat n m (v + u) :: real mat) = blinfun_to_mat n m v + (blinfun_to_mat n m u)"
  using blinfun_to_mat_add_scale[where b = 1]
  by auto

lemma blinfun_to_mat_sub: "(blinfun_to_mat n m (v - u) :: real mat) = blinfun_to_mat n m v - blinfun_to_mat n m u"
   using blinfun_to_mat_add_scale[where b = "-1"]
   by auto  

lemma blinfun_to_mat_zero[simp]: "blinfun_to_mat n m 0 = 0\<^sub>m n m"
  by (auto simp: blinfun_to_mat_def)

lemma blinfun_to_mat_scale: "(blinfun_to_mat n m (r *\<^sub>R v) :: real mat) = r \<cdot>\<^sub>m (blinfun_to_mat n m v)"
   using blinfun_to_mat_add_scale[where v = 0, where b = "r"]
   by (auto simp add: blinfun_to_mat_def)

lemma Bfun_if[simp]: "apply_bfun (bfun.Bfun (\<lambda>k. if b k then a else c)) = (\<lambda>k. if b k then a else c)"
  by (auto intro!: Bfun_inverse)

lemma blinfun_to_mat_correct: "blinfun_to_mat (dim_row v) (dim_col v) (mat_to_blinfun v) = v"
    unfolding blinfun_to_mat_def mat_to_blinfun.rep_eq bfun_mat.rep_eq
    by (auto simp: mult_mat_vec_def Matrix.mat_eq_iff scalar_prod_def if_distrib cong: if_cong)


lemma blinfun_to_mat_id: "blinfun_to_mat n n id_blinfun = 1\<^sub>m n"
  by (auto simp: blinfun_to_mat_def)

lemma nonneg_mult_vec_mono:
  assumes "0\<^sub>m (dim_row X) (dim_col X) \<le> X" "v \<le> u" "dim_vec v = dim_col X"
  shows "X *\<^sub>v (v :: real vec) \<le> X *\<^sub>v u"
  using assms
  unfolding Matrix.less_eq_mat_def Matrix.less_eq_vec_def
  by (auto simp: Matrix.scalar_prod_def intro!: sum_mono mult_left_mono)
  
unbundle no_vec_syntax

lemma nonneg_blinfun_mat: "nonneg_blinfun (mat_to_blinfun M) \<longleftrightarrow> (0\<^sub>m (dim_row M) (dim_col M) \<le> M)"
proof
  assume "nonneg_blinfun (mat_to_blinfun M)"
  hence "v \<ge> 0 \<Longrightarrow> 0 \<le> mat_to_blinfun M v" for v unfolding nonneg_blinfun_def by auto
  hence aux: "v \<ge> 0 \<Longrightarrow> 0 \<le> bfun_mat M v" for v unfolding mat_to_blinfun.rep_eq by auto
  hence aux: "(\<And>x. apply_bfun v x \<ge> 0) \<Longrightarrow> 0 \<le> bfun_mat M v x" for v x  unfolding less_eq_bfun_def by auto

  have "0 \<le> M $$ (i, j)" if "i < dim_row M" and "j < dim_col M" for i j
    using aux[of "Bfun (\<lambda>k. if k = j then 1 else 0)"] that
    unfolding bfun_mat.rep_eq
    by (auto cong: if_cong simp: Matrix.mult_mat_vec_def scalar_prod_def if_distrib)
  thus "0\<^sub>m (dim_row M) (dim_col M) \<le> M"
    unfolding less_eq_mat_def by auto
next
  assume "(0\<^sub>m (dim_row M) (dim_col M) \<le> M)"
  hence "0 \<le> M $$ (i,j)" if "i < dim_row M" and "j < dim_col M" for i j
    unfolding less_eq_mat_def using that by auto
  thus "nonneg_blinfun (mat_to_blinfun M)"
    unfolding nonneg_blinfun_def mat_to_blinfun.rep_eq less_eq_bfun_def bfun_mat.rep_eq
    by (auto simp: scalar_prod_def intro!: sum_nonneg)
qed

lemma mat_row_sub: "X \<in> carrier_mat n m \<Longrightarrow> Y \<in> carrier_mat n m \<Longrightarrow> i < n \<Longrightarrow> Matrix.row (X - Y) i = Matrix.row X i - Matrix.row Y i"
  unfolding Matrix.row_def by auto

lemma mat_to_blinfun_sub: "X \<in> carrier_mat n m \<Longrightarrow> Y \<in> carrier_mat n m \<Longrightarrow> mat_to_blinfun (X - Y) = mat_to_blinfun X - mat_to_blinfun Y"
  by (auto intro!: blinfun_eqI simp: minus_scalar_prod_distrib[of _ m] mat_row_sub mat_to_blinfun.rep_eq blinfun.diff_left bfun_mat.rep_eq)
 
definition "inverse_mats C D \<longleftrightarrow> (\<exists>n. C \<in> carrier_mat n n \<and> D \<in> carrier_mat n n) \<and> inverts_mat C D \<and> inverts_mat D C"

lemma inverse_mats_sym: "inverse_mats C D \<Longrightarrow> inverse_mats D C"
  unfolding inverse_mats_def by auto

lemma inverse_mats_unique: 
  assumes "inverse_mats C D" "inverse_mats C E" shows "D = E"
proof -
  have "D = D * (C * E)"
    using assms unfolding inverse_mats_def inverts_mat_def by auto
  also have "\<dots> = (D * C) * E"
    using assms unfolding inverse_mats_def by auto
  finally show ?thesis
    using assms unfolding inverse_mats_def inverts_mat_def by auto
qed

definition "inverse_mat D = (THE E. inverse_mats D E)"

lemma invertible_mat_iff_inverse: "invertible_mat M \<longleftrightarrow> (\<exists>N. inverse_mats M N)"
proof
  show "invertible_mat M \<Longrightarrow> \<exists>N. inverse_mats M N"
  unfolding invertible_mat_def inverts_mat_def inverse_mats_def
  by (metis carrier_matI index_mult_mat(3) index_one_mat(3) square_mat.elims(2))
  show "\<exists>N. inverse_mats M N \<Longrightarrow> invertible_mat M "
    unfolding inverse_mats_def invertible_mat_def
    by (metis carrier_matD(1) carrier_matD(2)  square_mat.elims(1))
qed

lemma mat_inverse_eq_inverse_mat:
  assumes "D \<in> carrier_mat n n" "invertible_mat (D :: real mat)" 
  shows "(mat_inverse D) = Some (inverse_mat D)"
proof (cases "mat_inverse D")
  case None
  have "D \<notin> Units (ring_mat TYPE(real) n n)"
    by (simp add: assms(1) None mat_inverse) 
  hence "x * D \<noteq> 1\<^sub>m n \<or> D * x \<noteq> 1\<^sub>m n" if "x\<in>carrier_mat n n" for x 
    using assms that by (simp add: Units_def ring_mat_simps)
  hence "\<not>invertible_mat D" 
    unfolding invertible_mat_iff_inverse
    by (metis assms(1) carrier_matD(1) inverse_mats_def inverts_mat_def)
  then show ?thesis
    using assms by auto
next
  case (Some a)
  hence "inverse_mats D a"
    using assms(1) mat_inverse(2) unfolding inverse_mats_def inverts_mat_def by auto
  thus ?thesis
    unfolding inverse_mat_def local.Some
    using inverse_mats_unique 
    by (auto intro: HOL.the1_equality[symmetric])
qed

lemma invertible_inverse_mats: 
  assumes "invertible_mat M" 
  shows "inverse_mats M (inverse_mat M)"
  by (metis assms inverse_mat_def inverse_mats_unique invertible_mat_iff_inverse theI_unique)

definition "bfun_to_vec n v = Matrix.vec n (apply_bfun v)"

lemma blinfun_to_mat_mult:
  "(blinfun_to_mat n m A) *\<^sub>v (bfun_to_vec m v) = bfun_to_vec n (A (bfun_if (\<lambda>i. i < m) v 0))"
proof -
  have "(\<Sum>ia = 0..<m. (A (bfun.Bfun (\<lambda>k. if ia = k then 1 else 0))) i * v ia) = (A (bfun_if (\<lambda>k. k < m) v 0)) i" for i
  proof -
  have "(\<Sum>ia = 0..<m. (A (bfun.Bfun (\<lambda>k. if ia = k then 1 else 0))) i * v ia)  =
    (\<Sum>ia = 0..<m. (A (v ia *\<^sub>R bfun.Bfun (\<lambda>k. if ia = k then 1 else 0)) i))"
    by (auto intro!: sum.cong simp add: blinfun.scaleR_right)
  also have "\<dots> = (\<Sum>ia = 0..<m. (A (v ia *\<^sub>R bfun.Bfun (\<lambda>k. if ia = k then 1 else 0)))) i"
    by (induction m) auto
  also have "\<dots> = (A  (\<Sum>ia = 0..<m. (v ia *\<^sub>R bfun.Bfun (\<lambda>k. if ia = k then 1 else 0)))) i"
    unfolding blinfun.sum_right by auto
      also have "\<dots> = blinfun_apply A (bfun_if (\<lambda>k. k < m) v 0) i"
      proof -
        have "(\<Sum>ia = 0..<m. (v ia *\<^sub>R bfun.Bfun (\<lambda>k. if ia = k then 1 else 0))) = 
              (\<Sum>i = 0..<m. bfun_if (\<lambda>k. k = i) v 0)"
          by (auto simp: bfun_if.rep_eq intro!: sum.cong)
        also have "\<dots> = bfun_if (\<lambda>k. k < m) v 0"
          by (induction m arbitrary: v) (auto simp add: bfun_eqI bfun_if.rep_eq)
        finally show ?thesis by auto
      qed
      finally show ?thesis.
    qed
    thus ?thesis
  unfolding blinfun_to_mat_def bfun_to_vec_def mult_mat_vec_def scalar_prod_def
  by auto
qed

lemma Max_geI: 
  assumes "finite X" "(y::_:: linorder) \<in> X" "x \<le> y" shows "x \<le> Max X"
  using assms Max_ge_iff by auto

lift_definition vec_to_bfun :: "real vec \<Rightarrow> (nat \<Rightarrow>\<^sub>b real)" is
  "\<lambda>v i. if i < dim_vec v then v $ i else 0"
proof -
  fix n and v :: "real vec"
  show "(\<lambda>i. if i < n then v $ i else 0) \<in> bfun"
    by (rule bfun_normI[of _ "if n = 0 then 0 else Max (abs ` (($) v) ` {..<n})"]) (auto intro!: Max_geI)
qed

lemma vec_to_bfun_to_vec[simp]: "bfun_to_vec (dim_vec v) (vec_to_bfun v) = v"
  by (auto simp: bfun_to_vec_def vec_to_bfun.rep_eq)

lemma bfun_to_vec_to_bfun[simp]: "vec_to_bfun (bfun_to_vec m v) = bfun_if (\<lambda>i. i < m) v 0"
  by (auto simp: bfun_to_vec_def vec_to_bfun.rep_eq bfun_if.rep_eq)
  
lemma bfun_if_vec_to_bfun[simp]: "(bfun_if (\<lambda>i. i < dim_vec v) (vec_to_bfun v) 0) = vec_to_bfun v"
  by (auto simp: bfun_if.rep_eq vec_to_bfun.rep_eq)

lemma blinfun_to_mat_mult':
  shows "(blinfun_to_mat n (dim_vec v) A) *\<^sub>v v = bfun_to_vec n (blinfun_apply A (vec_to_bfun v))"
  using blinfun_to_mat_mult[of n "dim_vec v" A "vec_to_bfun v"]
  by auto

lemma blinfun_to_mat_mult'':
  assumes "m = dim_vec v"
  shows "(blinfun_to_mat n m A) *\<^sub>v v = bfun_to_vec n (blinfun_apply A (vec_to_bfun v))"
  using blinfun_to_mat_mult' assms
  by auto

lemma matrix_eqI:
  fixes A :: "real mat"
  assumes "\<And>v. v \<in> carrier_vec m \<Longrightarrow> A *\<^sub>v v = B *\<^sub>v v" "A \<in> carrier_mat n m" "B \<in> carrier_mat n m"
  shows "A = B"
proof -
  have "A *\<^sub>v Matrix.vec m (\<lambda>j. if i = j then 1 else 0) = Matrix.col A i" "B *\<^sub>v Matrix.vec m (\<lambda>j. if i = j then 1 else 0) = Matrix.col B i"
      if  "i < m" for i
    using assms that
    by (auto simp: mult_mat_vec_def scalar_prod_def if_distrib cong: if_cong)
  thus ?thesis
    using assms
    by (auto intro: Matrix.mat_col_eqI)
qed

lemma blinfun_to_mat_in_carrier[simp]: "blinfun_to_mat m p A \<in> carrier_mat m p"
  unfolding blinfun_to_mat_def
  by auto

lemma blinfun_to_mat_dim_col[simp]: "dim_col (blinfun_to_mat m p A) = p"
  unfolding blinfun_to_mat_def
  by auto

lemma blinfun_to_mat_dim_row[simp]: "dim_row (blinfun_to_mat m p A) = m"
  unfolding blinfun_to_mat_def
  by auto

lemma bfun_to_vec_carrier[simp]: "bfun_to_vec m v \<in> carrier_vec m"
  by (simp add: bfun_to_vec_def)

lemma vec_cong: "(\<And>i. i < n \<Longrightarrow> f i = g i) \<Longrightarrow> vec n f = vec n g"
  by auto

lemma mat_to_blinfun_compose: 
  assumes "dim_col A = dim_row B"
  shows "(mat_to_blinfun A o\<^sub>L mat_to_blinfun B) = mat_to_blinfun (A * B)"
proof (intro blinfun_eqI bfun_eqI)
  fix i x
  show "apply_bfun (blinfun_apply (mat_to_blinfun A o\<^sub>L mat_to_blinfun B) i) x = apply_bfun (blinfun_apply (mat_to_blinfun (A * B)) i) x "
  proof (cases "x < dim_row A")
    case True
  have "(mat_to_blinfun A o\<^sub>L mat_to_blinfun B) i x = (bfun_mat A (bfun_mat B i)) x"
    by (auto simp: mat_to_blinfun.rep_eq)
  also have "\<dots> = Matrix.row A x \<bullet> vec (dim_col A) (\<lambda>ia. Matrix.row B ia \<bullet> vec (dim_col B) i)"
    using assms by (auto simp: bfun_mat.rep_eq True cong: vec_cong)
  also have "\<dots> = vec (dim_col B) (\<lambda>j. Matrix.row A x \<bullet> col B j) \<bullet> vec (dim_col B) i"
    using assms by (auto simp add: carrier_vecI assoc_scalar_prod[of _ "dim_col A"])    
  also have "\<dots> = Matrix.row (A * B) x \<bullet> vec (dim_col B) (apply_bfun i)"
    by (subst Matrix.row_mult) (auto simp add: assms True)
  also have "\<dots> = mat_to_blinfun (A * B) i x"
    by (simp add: mat_to_blinfun.rep_eq bfun_mat.rep_eq True)
  finally show ?thesis.
qed (simp add: bfun_mat.rep_eq mat_to_blinfun_mult)
qed

lemma blinfun_to_mat_compose:
  fixes A B :: "(nat \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L (nat \<Rightarrow>\<^sub>b real)"
  assumes 
    "\<And>v v' j. (\<And>i. i < m \<Longrightarrow> apply_bfun v i = apply_bfun v' i) \<Longrightarrow> j < n \<Longrightarrow> A v j = A v' j"
  shows "blinfun_to_mat n m A * blinfun_to_mat m p B = blinfun_to_mat n p (A o\<^sub>L B)"
proof  (rule matrix_eqI[of p _ _ n])
  fix v :: "real vec"
  assume v[simp, intro]: "v \<in> carrier_vec p" 
  hence "blinfun_to_mat n m A * blinfun_to_mat m p B *\<^sub>v v = bfun_to_vec n (A (vec_to_bfun (blinfun_to_mat m p B *\<^sub>v v)))"
    by (auto simp: blinfun_to_mat_mult'' blinfun_to_mat_mult assoc_mult_mat_vec[of _ n m _ p])
  also have "\<dots>  = bfun_to_vec n (A (vec_to_bfun (bfun_to_vec m (B (vec_to_bfun v)))))"
    using v by (fastforce simp: blinfun_to_mat_mult'' dest!: carrier_vecD)+
  also have "\<dots> = bfun_to_vec n ((A o\<^sub>L B) (vec_to_bfun v))"
    unfolding bfun_to_vec_to_bfun
    using assms by (fastforce simp add: bfun_if.rep_eq bfun_to_vec_def intro!: vec_cong)
  also have "\<dots> = blinfun_to_mat n p (A o\<^sub>L B) *\<^sub>v v "
    using v by (fastforce simp: blinfun_to_mat_mult'' dest!: carrier_vecD)+
  finally show "blinfun_to_mat n m A * blinfun_to_mat m p B *\<^sub>v v = blinfun_to_mat n p (A o\<^sub>L B) *\<^sub>v v".
qed auto

lemma invertible_mat_dims: "invertible_mat A \<Longrightarrow> dim_col A = dim_row A"
  by (simp add: invertible_mat_def)

lemma invertible_mat_square: "invertible_mat A \<Longrightarrow> square_mat A"
  by (simp add: invertible_mat_dims)

lemma inverse_mat_dims: 
  assumes "invertible_mat A" 
  shows "dim_col (inverse_mat A) = dim_col A" "dim_row (inverse_mat A) = dim_row A"
  using assms inverse_mats_def invertible_inverse_mats by auto

lemma inverse_mat_mult[simp]:
  assumes "invertible_mat A"
  shows "inverse_mat A * A = 1\<^sub>m (dim_row A)" "A * inverse_mat A = 1\<^sub>m (dim_row A)"
  using assms invertible_inverse_mats[OF assms] inverse_mat_dims
  unfolding inverts_mat_def inverse_mats_def
  by auto

lemma invertible_mult:
  assumes "invertible_mat m" "dim_vec a = dim_col m" "dim_vec b = dim_col m"
  shows "a = b \<longleftrightarrow> m *\<^sub>v a = m *\<^sub>v b"
proof -
  have "(inverse_mat m * m) *\<^sub>v a = a" "(inverse_mat m * m) *\<^sub>v b = b"
    by (metis assms carrier_vec_dim_vec inverse_mat_mult(1) invertible_mat_dims one_mult_mat_vec)+
  thus ?thesis
    by (metis assms assoc_mult_mat_vec carrier_mat_triv carrier_vec_dim_vec inverse_mat_dims(1) invertible_mat_dims)
qed

lemma inverse_mult_iff:
  assumes "invertible_mat m" 
  and "dim_vec v = dim_col m" "dim_vec b = dim_row m" 
  shows "v = inverse_mat m *\<^sub>v b \<longleftrightarrow> m *\<^sub>v v = b"
proof -
  have "v = inverse_mat m *\<^sub>v b \<longleftrightarrow> m *\<^sub>v v =  m *\<^sub>v (inverse_mat m *\<^sub>v b)"
    using invertible_mult by (metis assms dim_mult_mat_vec inverse_mat_dims(2) invertible_mat_dims)
  also have "\<dots> \<longleftrightarrow>   m *\<^sub>v v = (m * inverse_mat m) *\<^sub>v b"
    by (subst assoc_mult_mat_vec[of _ "dim_col m" "dim_col m" _ "dim_col m"])
       (auto simp add: assms carrier_vecI inverse_mat_dims invertible_mat_dims)
  also have "\<dots> \<longleftrightarrow> m *\<^sub>v v = b"
    by (metis assms(1) assms(3) carrier_vecI inverse_mat_mult(2) one_mult_mat_vec)
  finally show ?thesis.
qed

lemma inverse_blinfun_to_mat:
  fixes A :: "(nat \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L (nat \<Rightarrow>\<^sub>b real)"
  assumes "invertible\<^sub>L A"
  assumes "(\<And>v v' j. (\<And>i. i < m \<Longrightarrow> apply_bfun v i = apply_bfun v' i) \<Longrightarrow> j < m \<Longrightarrow> (A v) j = (A v') j)" 
  assumes "(\<And>v v' j. (\<And>i. i < m \<Longrightarrow> apply_bfun v i = apply_bfun v' i) \<Longrightarrow> j < m \<Longrightarrow> (inv\<^sub>L A v) j = (inv\<^sub>L A v') j)"
  shows "blinfun_to_mat m m (inv\<^sub>L A) = (inverse_mat (blinfun_to_mat m m A))" "invertible_mat (blinfun_to_mat m m A)" 
proof -
  have *: "blinfun_to_mat m m A * blinfun_to_mat m m (inv\<^sub>L A) = 1\<^sub>m m"
    by (subst blinfun_to_mat_compose) (fastforce simp:  blinfun_to_mat_id assms(1) intro: assms(2))+
  moreover have **: "blinfun_to_mat m m (inv\<^sub>L A) * blinfun_to_mat m m A = 1\<^sub>m m"
    by (subst blinfun_to_mat_compose) (fastforce simp:   blinfun_to_mat_id assms(1) intro: assms(3))+
  ultimately have ***: "invertible_mat (blinfun_to_mat m m A)"
    by (metis blinfun_to_mat_dim_col blinfun_to_mat_dim_row invertible_mat_def inverts_mat_def square_mat.elims(1))
  
  have "inverse_mats (blinfun_to_mat m m A) (blinfun_to_mat m m (inv\<^sub>L A))"
    unfolding inverse_mats_def inverts_mat_def using * ** by force
  hence "inverse_mat (blinfun_to_mat m m A) = blinfun_to_mat m m (inv\<^sub>L A)"
    using *** inverse_mats_unique invertible_inverse_mats by blast
  thus "blinfun_to_mat m m (inv\<^sub>L A) = inverse_mat (blinfun_to_mat m m A)" "invertible_mat (blinfun_to_mat m m A)"  
    using \<open>invertible_mat (blinfun_to_mat m m A)\<close> by auto
qed

end