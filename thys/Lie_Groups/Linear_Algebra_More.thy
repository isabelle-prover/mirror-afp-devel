(*  Title:       Linear_Algebra_More
    Author:      Richard Schmoetten <richard.schmoetten@ed.ac.uk>, 2024
    Maintainer:  Richard Schmoetten <richard.schmoetten@ed.ac.uk>
*)

theory Linear_Algebra_More
imports
  "HOL-Analysis.Analysis"
  "Smooth_Manifolds.Smooth"
  Transfer_Cayley_Hamilton
begin


section \<open>Continuity of the determinant (and other maps)\<close>

lemma continuous_on_proj: "continuous_on s fst" "continuous_on s snd"
  apply (simp add: continuous_on_fst[OF continuous_on_id])
  by (simp add: continuous_on_snd[OF continuous_on_id])

lemma continuous_on_plus:
  fixes s::"('a \<times> 'a::topological_monoid_add) set"
  shows "continuous_on s (\<lambda>(x,y). x+y)"
  by (simp add: continuous_on_add[OF continuous_on_proj] case_prod_beta')

lemma continuous_on_times:
  fixes s::"('a \<times> 'a::real_normed_algebra) set"
  shows "continuous_on s (\<lambda>(x,y). x*y)"
  by (simp add: case_prod_beta' continuous_on_mult[OF continuous_on_proj])

lemma continuous_on_times':
  fixes s::"('a \<times> 'a::topological_monoid_mult) set"
  shows "continuous_on s (\<lambda>(x,y). x*y)"
  by (simp add: case_prod_beta' continuous_on_mult'[OF continuous_on_proj])

text \<open>Only functions between \<open>real_normed_vector\<close> spaces can be \<open>bounded_linear\<close>...\<close>

lemma continuous_on_nth_of_vec:
  fixes s::"('a::real_normed_field,'n::finite)vec set"
  shows "continuous_on s (\<lambda>x. x $ n)"
  by (simp add: bounded_linear_vec_nth linear_continuous_on)

lemma bounded_linear_mat_ijth[intro]: "bounded_linear (\<lambda>x. x $ i $ j)"
  apply (standard; simp?)
  apply (intro exI[of _ 1])
  apply (simp add: norm_nth_le)
  by (meson Finite_Cartesian_Product.norm_nth_le dual_order.trans)

lemma continuous_on_ijth_of_mat:
  fixes s::"('a::real_normed_field,'n::finite)square_matrix set"
  shows "continuous_on s (\<lambda>x. x $ i $ j)"
  by (simp add: bounded_linear_mat_ijth linear_continuous_on)

lemma continuous_on_det:
  fixes s::"('a::real_normed_field,'n::finite)square_matrix set"
  shows "continuous_on s det"
proof (unfold det_def, intro continuous_on_sum)
  fix p
  assume "p \<in> {p. p permutes (UNIV::'n set)}"
  show "continuous_on s (\<lambda>A. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i))"
  proof (intro continuous_on_mult)
    show "continuous_on s (\<lambda>x. of_int (sign p))"
      by simp
    show "continuous_on s (\<lambda>x. \<Prod>i\<in>UNIV. x $ i $ p i)"
      apply (intro continuous_on_prod)
      by (simp add: continuous_on_ijth_of_mat)
  qed
qed

lemma invertible_inv_ex:
  fixes a::"'a::semiring_1^'n^'n"
  assumes "invertible a"
  shows "(matrix_inv a)**a = mat 1" "a**(matrix_inv a) = mat 1"
  using some_eq_ex assms invertible_def matrix_inv_def
  by (smt (verit, ccfv_SIG))+

text \<open>
  A similar result to the below already exists for fields, see e.g. \<open>invertible_left_inverse\<close>.
  This is more general, as it applies to any semiring (with 1).
\<close>
lemma invertible_matrix_inv:
  fixes a::"'a::semiring_1^'n^'n"
  assumes "invertible a"
  shows "invertible (matrix_inv a)"
  using invertible_inv_ex assms invertible_def
  by auto



section \<open>Component expressions for inverse matrices over fields\<close>

lemma inv_adj_det_field_component:
  fixes i j::"'n::finite" and A A'::"'a::field^'n^'n"
  defines invA: "A' \<equiv> map_matrix (\<lambda>x. x / (det A)) (adjugate A)"
  assumes "invertible A"
  shows "(A**A')$i$j = (if i=j then 1 else 0)"
proof -
  let ?D = "det A"
  have det_not_0: "?D \<noteq> 0"
    using assms by (metis det_I det_mul invertible_inv_ex(2) mult_zero_left zero_neq_one)
  have "(\<Sum> k\<in>UNIV. (A$i$k * (adjugate A)$k$j)) = (if i=j then ?D else 0)"
    using mult_adjugate_det_2 [of A] unfolding matrix_matrix_mult_def mat_def
    by (metis (mono_tags, lifting) iso_tuple_UNIV_I vec_lambda_inverse)
  then have "(if i=j then 1 else 0) = (\<Sum> k\<in>UNIV. (A$i$k * (adjugate A)$k$j)) / ?D"
    by (simp add: det_not_0)
  also have "\<dots> = (\<Sum> k\<in>UNIV. (A$i$k * A'$k$j))"
    using sum_divide_distrib invA by force
  finally show ?thesis
    unfolding matrix_matrix_mult_def by simp
qed

lemma inverse_adjugate_det_2:
  fixes A::"'a::field^'n^'n"
  assumes "invertible A"
  shows "matrix_inv A =  map_matrix (\<lambda>x. x / (det A)) (adjugate A)"
  (is "matrix_inv A = ?A'")
proof -
  let ?D = "det A"
  have det_not_0: "?D \<noteq> 0"
    using assms by (metis det_I det_mul invertible_inv_ex(2) mult_zero_left zero_neq_one)
  have AA': "A ** ?A' = mat 1"
    unfolding mat_def using inv_adj_det_field_component[OF assms] by (simp add: vec_eq_iff)
  moreover have "?A' ** A = mat 1"
    using AA' by (simp add: matrix_left_right_inverse)
  ultimately show "matrix_inv A = ?A'"
    by (metis (no_types) invertible_def invertible_inv_ex(2) matrix_mul_assoc matrix_mul_lid)
qed

lemma inverse_adjugate_det:
  fixes A::"'a::field^'n^'n"
  assumes "invertible A"
  shows "matrix_inv A =  (1 / (det A)) *\<^sub>s (adjugate A)"
  using inverse_adjugate_det_2[OF assms] unfolding map_matrix_def smult_mat_def by auto

lemma transpose_component: "(transpose A) $i$j = A$j$i"
  unfolding transpose_def by simp

lemma matrix_inverse_component:
  fixes A::"'a::field^'n^'n" and i j::"'n::finite"
  assumes "invertible A"
  shows "(matrix_inv A)$i$j = det (\<chi> k l. if k = j \<and> l = i then 1 else if k = j \<or> l = i then 0 else A $ k $ l) / (det A)"
  using inverse_adjugate_det_2 [OF assms]
  by (simp add: transpose_component adjugate_def cofac_def minor_mat_def)

lemma matrix_adjugate_component:
  fixes A::"'a::field^'n^'n" and i j::"'n::finite"
  assumes "invertible A"
  shows "(adjugate A)$i$j = det (\<chi> k l. if k = j \<and> l = i then 1 else if k = j \<or> l = i then 0 else A $ k $ l)"
  by (simp add: transpose_component adjugate_def cofac_def minor_mat_def)



section \<open>Smoothness of real matrix operations and \<open>det\<close>\<close>


subsection \<open>Smoothness of matrix multiplication\<close>

lemma smooth_on_ijth_of_mat:                         
  fixes s::"('a::real_normed_field,'n::finite)square_matrix set"
  shows "smooth_on s (\<lambda>x. x $ i $ j)"
  by (simp add: bounded_linear.smooth_on bounded_linear_mat_ijth)

text \<open>
  Notice the following result holds only for matrices over the real numbers.
  (Try removing the type annotations: Isabelle automatically casts to the indicated type anyway.)
  This is because only real inner product spaces are defined: thus whatever "base field"
  a matrix is defined over, is implicitly assumed to also be a real inner product space
  (as is possible, for example, for \<open>\mathbb{C}\<close> with the normal inner product of \<open>\mathbb{R}^2\<close>),
  and the inner product is built on top of the existing one to return a \<open>real\<close> result.
\<close>
lemma matrix_matrix_mul_component_real:
  fixes A::"real^'k^'n"
    and B::"real^'m^'k"
  shows "A**B = (\<chi> i j. inner (row i A) (column j B))"
    and "A**B = (\<chi> i j. inner (A$i) (transpose B$j))"
proof -
  have "(\<Sum>k\<in>UNIV. A $ i $ k * B $ k $ j) = inner (row i A) (column j B)"
  for i j
    unfolding column_def row_def inner_vec_def inner_real_def
    using UNIV_I sum.cong vec_lambda_inverse by force
  thus c1: "A**B = (\<chi> i j. inner (row i A) (column j B))"
    by (simp add: matrix_matrix_mult_def)
  show "A**B = (\<chi> i j. inner (A$i) (transpose B$j))"
  proof -
    have "(\<chi> i j. A $ i \<bullet> transpose B $ j) = (\<chi> i j. row i A \<bullet> column j B)"
      by (simp add: row_def column_def transpose_def)
    then show ?thesis
      using c1 by metis
  qed
qed


lemma matrix_inner_sum:
  shows "x \<bullet> y = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (x$i$j)\<bullet>(y$i$j))"
    and "x \<bullet> y = (\<Sum>(i,j)\<in>UNIV. (x$i$j)\<bullet>(y$i$j))"
    apply (simp add: inner_vec_def)+
    by (simp add: sum.cartesian_product)


lemma matrix_norm_sum_sqrs:
  shows "norm x = sqrt(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (norm (x$i$j))\<^sup>2)"
    and "norm x = sqrt(\<Sum>(i,j)\<in>UNIV. (norm (x$i$j))\<^sup>2)"
  using real_sqrt_abs real_sqrt_power
  by (auto simp: norm_vec_def L2_set_def sum_nonneg sum.cartesian_product)


lemma norm_transpose:
  shows "norm x = norm (transpose x)"
proof -
  have "(\<Sum>(i,j)\<in>UNIV. (norm (x$i$j))\<^sup>2) = (\<Sum>(j,i)\<in>UNIV. (norm (x$i$j))\<^sup>2)"
    using sum.swap[of "\<lambda>i j. (norm (x$i$j))\<^sup>2" UNIV UNIV] by (simp add: sum.cartesian_product)
  then show ?thesis
    unfolding transpose_def matrix_norm_sum_sqrs(2) by simp
qed


lemma matrix_norm_inner:
  fixes x::"real^'n^'m"
  shows "norm x = sqrt(\<Sum>(i,j)\<in>UNIV. (x$i$j)\<bullet>(x$i$j))"
  using matrix_inner_sum(2)[of x x] by (simp add: norm_eq_sqrt_inner)


lemma matrix_norm_row:
  shows "norm x = sqrt(\<Sum>i\<in>UNIV. (norm (row i x))\<^sup>2)"
  unfolding norm_vec_def L2_set_def row_def by simp


lemma matrix_norm_column:
  shows "norm x = sqrt(\<Sum>j\<in>UNIV. (norm (column j x))\<^sup>2)"
  using matrix_norm_row norm_transpose row_transpose
  by (metis (lifting) Finite_Cartesian_Product.sum_cong_aux)


lemma mat_mul_indexed: "(A**B)$i$j = (\<Sum>k\<in>UNIV. A $ i $ k * B $ k $ j)"
  using matrix_matrix_mult_def vec_lambda_beta
  by (metis (no_types, lifting) Finite_Cartesian_Product.sum_cong_aux)


lemma norm_matrix_mult_ineq:
  fixes A :: "real^'l^'n"
    and B :: "real^'m^'l"
  shows "norm (A ** B) \<le> norm A * norm B"
proof -
  have "(A**B)$i$j = row i A \<bullet> column j B" for i j
    by (simp add: matrix_matrix_mul_component_real(1)[of A B])
  then have "norm (A**B) = sqrt(\<Sum>(i,j)\<in>UNIV. (norm (row i A \<bullet> column j B))\<^sup>2)"
    by (simp add: matrix_norm_sum_sqrs(2)[of "A**B"])
  then have "(norm (A**B))\<^sup>2 = (\<Sum>(i,j)\<in>UNIV. (norm (row i A \<bullet> column j B))\<^sup>2)"
    by (metis (no_types, lifting) norm_ge_zero real_sqrt_ge_0_iff real_sqrt_pow2)
  also have "(\<Sum>(i,j)\<in>UNIV. (norm (row i A \<bullet> column j B))\<^sup>2)
      \<le> (\<Sum>(i,j)\<in>UNIV. (norm(row i A) * norm(column j B))\<^sup>2)"
  proof -
    obtain f g where defs:
        "f = (\<lambda>(i::'n,j::'m). (row i A \<bullet> column j B)\<^sup>2)"
        "g = (\<lambda>(i::'n,j::'m). (norm (row i A) * norm (column j B))\<^sup>2)"
      by simp
    then have "f (i,j) \<le> g (i,j)" for i::'n and j::'m
      by (simp add: Cauchy_Schwarz_ineq power2_norm_eq_inner power_mult_distrib)
    hence "(\<Sum>(i,j)\<in>UNIV. f (i,j)) \<le> (\<Sum>(i,j)\<in>UNIV. g (i,j))"
      using sum_mono[of UNIV f g] by fastforce
    thus ?thesis
      by (simp add: defs)
  qed
  also have "(\<Sum>(i,j)\<in>UNIV. (norm(row i A) * norm(column j B))\<^sup>2) = (norm A * norm B)\<^sup>2"
  proof -
    let ?f = "\<lambda>i. (norm (row i A))\<^sup>2"
    let ?g = "\<lambda>j. (norm (column j B))\<^sup>2"
    have "(\<Sum>(i,j)\<in>UNIV. (norm(row i A) * norm(column j B))\<^sup>2)
        = (\<Sum>(i,j)\<in>UNIV. (norm(row i A))\<^sup>2 * (norm(column j B))\<^sup>2)"
      by (simp add: power_mult_distrib)
    then have 1: "(\<Sum>(i,j)\<in>UNIV. (norm(row i A) * norm(column j B))\<^sup>2)
        = (\<Sum>i\<in>UNIV. (norm(row i A))\<^sup>2) * (\<Sum>j\<in>UNIV. (norm(column j B))\<^sup>2)"
      by (simp add: sum_product sum.cartesian_product)
    have 2: "(\<Sum>i\<in>UNIV. (norm(row i A))\<^sup>2) = (norm A)\<^sup>2" "(\<Sum>j\<in>UNIV. (norm(column j B))\<^sup>2) = (norm B)\<^sup>2"
      using matrix_norm_row matrix_norm_column abs_norm_cancel real_sqrt_abs real_sqrt_eq_iff
      by (smt (verit, best) sum.cong)+
    show ?thesis
      using 1 2 by (metis power_mult_distrib)
  qed
  finally show ?thesis
    by simp
qed


lemma bounded_bilinear_matrix_mult: "bounded_bilinear ((**)
    :: real^'l^'m \<Rightarrow> real^'n^'l \<Rightarrow> real^'n^'m)"
  apply (rule bounded_bilinear.intro)
  apply (metis (no_types, lifting) matrix_eq matrix_vector_mul_assoc matrix_vector_mult_add_rdistrib)
  apply (simp add: matrix_add_ldistrib matrix_scalar_ac scalar_matrix_assoc)+
  by (intro exI[of _ 1], simp add: norm_matrix_mult_ineq)

lemma smooth_on_matrix_mult:
  fixes f::"'a::real_normed_vector \<Rightarrow> (real^'n^'m)"
  assumes "k-smooth_on S f" "k-smooth_on S g" "open S"
  shows "k-smooth_on S (\<lambda>x. f x ** g x)"
  by (rule bounded_bilinear.smooth_on[OF bounded_bilinear_matrix_mult assms])


subsection \<open>Smoothness of \<open>\<Prod>\<close> and \<open>det\<close>\<close>

lemma higher_differentiable_on_prod:
  fixes f::"_ \<Rightarrow> _ \<Rightarrow> 'c::{real_normed_algebra, comm_monoid_mult}"
  assumes "\<And>i. i \<in> F \<Longrightarrow> finite F \<Longrightarrow> higher_differentiable_on S (f i) n" "open S"
  shows "higher_differentiable_on S (\<lambda>x. \<Prod>i\<in>F. f i x) n"
  using assms apply (induction F rule: infinite_finite_induct)
  by (simp add: higher_differentiable_on_const higher_differentiable_on_mult)+

lemma smooth_on_prod:
  fixes f::"_ \<Rightarrow> _ \<Rightarrow> 'c::{real_normed_algebra, comm_monoid_mult}"
  assumes "(\<And>i. i \<in> F \<Longrightarrow> finite F \<Longrightarrow> k-smooth_on S (f i))" "open S"
  shows "k-smooth_on S (\<lambda>x. \<Prod>i\<in>F. f i x)"
  using higher_differentiable_on_prod by (metis assms smooth_on_def)

lemma smooth_on_det:
  fixes s::"('a::real_normed_field,'n::finite)square_matrix set"
  assumes "open s"
  shows "k-smooth_on s det"
proof (unfold det_def, intro smooth_on_sum)
  fix p
  assume "p \<in> {p. p permutes (UNIV::'n set)}"
  show "k-smooth_on s (\<lambda>A. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i))"
  proof (intro smooth_on_mult)
    show "k-smooth_on s (\<lambda>x. of_int (sign p))"
      by (simp add: smooth_on_const)
    show "k-smooth_on s (\<lambda>x. \<Prod>i\<in>UNIV. x $ i $ p i)" "open s"
      apply (intro smooth_on_prod)
      apply (simp add: bounded_linear.smooth_on bounded_linear_mat_ijth)
      by (rule assms)+
  qed
qed (rule assms)

(*lemma
  fixes f::"_\<Rightarrow>_::euclidean_space"
  assumes "smooth_on T g" and "smooth_on S f" and "open S" and "open T" and "f`S \<subseteq> T"
  shows "smooth_on S (g\<circ>f)"
  by (rule smooth_on_compose[OF assms])*)


subsection \<open>Smoothness of matrix inversion\<close>

lemma invertible_mat_1: "invertible (mat 1)"
  by (simp add: invertible_def)

lemma continuous_on_vec:
  assumes "\<And>i. continuous_on S (\<lambda>x. f x $ i)"
  shows "continuous_on S f"
  using assms unfolding continuous_on_def by (simp add: vec_tendstoI)

lemma frechet_derivative_eucl:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "f differentiable at x"
  shows "frechet_derivative f (at x) =
    (\<lambda>v. \<Sum>i\<in>Basis. (v \<bullet> i) *\<^sub>R frechet_derivative f (at x) i)"
proof -
  have 1: "id differentiable at x" "f differentiable at (id x)"
    by (simp add: frechet_derivative_works, simp add: assms)
  show ?thesis using frechet_derivative_compose_eucl[OF 1] frechet_derivative_id[of x]
    by (auto, metis comp_id fun.map_ident)
qed


text \<open>TODO! This should maybe be changed in \<open>Finite_Cartesian_Product.norm_le_l1_cart\<close>.
  That result only works for \<open>real^'n\<close>, this one should work for all \<open>'a::real_normed_vector^'n\<close>.\<close>
lemma norm_le_l1_cart': "norm x \<le> sum(\<lambda>i. norm (x$i)) UNIV"
  by (simp add: norm_vec_def L2_set_le_sum)

lemma bounded_linear_vec_nth_fun:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector^'m"
  assumes "\<And>i. bounded_linear (\<lambda>x. (f x)$i)"
  shows "bounded_linear f"
proof
  fix x y and r::real
  interpret fi: bounded_linear "\<lambda>x. (f x)$i" for i by fact
  show "f (r*\<^sub>R x) = r *\<^sub>R f x"
    using fi.scale by (simp add: vec_eq_iff)
  show "f (x+y) = f x + f y"
    using fi.add by (simp add: vec_eq_iff)
  obtain F where "0<F i" and norm_f: "\<And>x. norm ((f x)$i) \<le> norm x * F i" for i
    using fi.pos_bounded by metis
  have "\<forall>x. norm (f x) \<le> norm x * (\<Sum>i\<in>UNIV. F i)"
  proof (rule allI)
    fix x
    have "norm (f x) \<le> (\<Sum>i\<in>UNIV. norm (f x $ i))"
      by (rule norm_le_l1_cart'[of "f x" for x])
    also have "\<dots> \<le> (\<Sum>i\<in>UNIV. norm x * F i)"
      using norm_f[of x i for i] by (simp add: sum_mono)
    also have "\<dots> \<le> norm x * (\<Sum>i\<in>UNIV. F i)"
      by (simp add: sum_distrib_left)
    finally show "norm (f x) \<le> norm x * (\<Sum>i\<in>UNIV. F i)" .
  qed
  thus "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K" by blast
qed

lemma has_derivative_vec_lambda [derivative_intros]:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector^'m"
  assumes "\<And>i. ((\<lambda>x. (f x)$i) has_derivative (\<lambda>x. (f' x)$i)) (at x within s)"
  shows "(f has_derivative f') (at x within s)"
proof (intro has_derivativeI_sandwich[of 1])
  show "bounded_linear f'"
    using assms by (intro bounded_linear_vec_nth_fun has_derivative_bounded_linear)

  let ?Ri = "\<lambda>i y. (f y)$i - (f x)$i - (f' (y-x))$i"
  let ?R = "\<lambda>y. f y - f x - f' (y-x)"

  show "((\<lambda>y. (\<Sum>i\<in>UNIV. norm (?Ri i y) / norm (y-x))) \<longlongrightarrow> 0) (at x within s)"
    using assms apply (intro tendsto_null_sum) by (auto simp: has_derivative_iff_norm)

  fix y assume "y \<noteq> x"
  show "norm (?R y) / norm (y-x) \<le> (\<Sum>i\<in>UNIV. norm (?Ri i y) / norm (y-x))"
    unfolding sum_divide_distrib[symmetric]
    apply (rule divide_right_mono) prefer 2 apply simp
    using norm_le_l1_cart' by (smt (verit, ccfv_SIG) real_norm_def sum_mono vector_minus_component)
qed (simp)

lemma has_derivative_vec_lambda_2:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector^'m"
  assumes "\<And>i. ((\<lambda>x. (f x)$i) has_derivative (f' i)) (at x within s)"
  shows "(f has_derivative (\<lambda>x. \<chi> i. f' i x)) (at x within s)"
  apply (intro has_derivative_vec_lambda[of f "\<lambda>x. \<chi> i. f' i x" x s])
  using assms by auto

lemma differentiable_componentwise:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector^'m"
  assumes "\<And>i. (\<lambda>x. f x $ i) differentiable (at x within s)"
  shows "f differentiable (at x within s)"
proof (unfold differentiable_def, intro exI)
  let ?f' = "\<lambda>i. SOME f'. ((\<lambda>x. f x $ i) has_derivative f') (at x within s)"
  have 1: "\<And>i. ((\<lambda>x. (f x)$i) has_derivative (?f' i)) (at x within s)"
    by (metis assms differentiable_def some_eq_imp)
  show "(f has_derivative (\<lambda>x. \<chi> i. ?f' i x)) (at x within s)"
     by (rule has_derivative_vec_lambda_2[OF 1])
qed

lemma frechet_derivative_vec:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector^'m"
  assumes "\<And>i. (\<lambda>x. f x $ i) differentiable (at x)"
  shows "frechet_derivative f (at x) = (\<lambda>v. \<chi> i. (frechet_derivative (\<lambda>x. f x $ i) (at x) v))"
  apply (rule frechet_derivative_at')
  apply (intro has_derivative_vec_lambda)
  by (auto intro: derivative_eq_intros frechet_derivative_worksI[OF assms])

lemma higher_differentiable_on_vec:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector^'m"
  assumes "\<And>i. higher_differentiable_on S (\<lambda>x. (f x) $ i) n"
    and "open S"
  shows "higher_differentiable_on S f n"
  using assms
proof (induction n arbitrary: f)
  case 0
  then show ?case
    using continuous_on_vec by (metis higher_differentiable_on.simps(1))
next
  case (Suc n)
  have f: "\<And>x i. x \<in> S \<Longrightarrow> (\<lambda>x. f x $ i) differentiable (at x)"
    and hf: "\<And>i. higher_differentiable_on S (\<lambda>x. frechet_derivative (\<lambda>y. f y $ i) (at x) v) n"
    for v using Suc.prems higher_differentiable_on.simps(2) by blast+
  have f': "higher_differentiable_on S f n"
    using Suc(1,2) assms(2) higher_differentiable_on_SucD by blast
  have 1: "\<forall>x\<in>S. f differentiable (at x)"
    using f differentiable_componentwise[of f _ UNIV] by simp
  have 2: "\<forall>v. higher_differentiable_on S (\<lambda>x. frechet_derivative f (at x) v) n"
  proof (intro allI)
    fix v
    let ?f' = "\<lambda>x. frechet_derivative f (at x) v"
    let ?f'\<^sub>i = "\<lambda>x. \<chi> i. frechet_derivative (\<lambda>y. f y $ i) (at x) v"
    { fix x assume "x \<in> S"
      hence "?f' x = (\<chi> i. frechet_derivative (\<lambda>y. f y $ i) (at x) v)"
        using frechet_derivative_vec[OF f] by simp }
    then have "higher_differentiable_on S ?f' n = higher_differentiable_on S ?f'\<^sub>i n"
      using higher_differentiable_on_cong[of S S "?f'" "?f'\<^sub>i" n] assms(2)
      by simp
    then show "higher_differentiable_on S ?f' n"
      using hf Suc.IH assms(2) by auto
  qed
  show ?case
    by (simp add: 1 2 higher_differentiable_on.simps(2))
qed

lemma smooth_on_vec:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector^'m"
  assumes "\<And>i. k-smooth_on S (\<lambda>x. (f x) $ i)" "open S"
  shows "k-smooth_on S f"
proof (unfold smooth_on_def, intro allI impI)
  fix n assume asm: "enat n \<le> k"
  show "higher_differentiable_on S f n"
    apply (intro higher_differentiable_on_vec)
    using assms asm unfolding smooth_on_def by simp+
qed

lemma smooth_on_mat:
  fixes f::"('a::real_normed_vector) \<Rightarrow> ('b::real_normed_vector^'k^'l)"
  assumes "\<And>i j. k-smooth_on S (\<lambda>x. (f x)$i$j)" "open S"
  shows "k-smooth_on S f"
  by (simp add: smooth_on_vec assms)

text \<open>This type constraint is annoying. The \<open>euclidean_space\<close> is inherited from
  \<open>higher_differentiable_on_compose\<close>, where it is marked as:
  `TODO: can we get around this restriction?`.
  Notice this type constraint is exactly \<open>real_normed_eucl\<close> as defined in \<open>Classical_Groups\<close>.\<close>
lemma smooth_on_matrix_inv_component:
  fixes S::"('a::{euclidean_space,real_normed_field}^'n^'n) set"
  assumes "\<forall>A\<in>S. invertible A" "open S"
  shows "k-smooth_on S (\<lambda>A. (matrix_inv A)$i$j)"
  using matrix_inverse_component smooth_on_mat smooth_on_det smooth_on_compose smooth_on_divide smooth_on_cong
proof -
  have smooth_on_div_det: "k-smooth_on S (\<lambda>x. f x / (det x))" if "smooth_on S f" for f
    apply (intro smooth_on_divide[of k S f det])
    using that smooth_on_det[OF assms(2)] assms by (auto simp: smooth_on_def invertible_det_nz)

  let ?inv_comp' = "\<lambda>A::'a^'n^'n. \<chi> k l. if k = j \<and> l = i then 1 else if k = j \<or> l = i then 0 else A $ k $ l"
  let ?inv_comp = "\<lambda>A::'a^'n^'n. det (?inv_comp' A) / det A"

  have matrix_inv_cong: "\<And>A. A\<in>S \<Longrightarrow> (matrix_inv A)$i$j = ?inv_comp A"
    using matrix_inverse_component assms by blast

  have smooth_on_component: "smooth_on S ?inv_comp'"
  proof (intro smooth_on_mat[of \<infinity> S ?inv_comp'])
    fix n m
    consider "n=j \<and> m=i"|"n=j \<and> m\<noteq>i"|"n\<noteq>j \<and> m=i"|"n\<noteq>j \<and> m\<noteq>i" by linarith
    hence "smooth_on S (\<lambda>x. if n = j \<and> m = i then 1 else if n = j \<or> m = i then 0 else x$n$m)"
      apply cases by (simp add: smooth_on_const smooth_on_ijth_of_mat)+
    thus "smooth_on S (\<lambda>x. (\<chi> k l. if k = j \<and> l = i then 1 else if k = j \<or> l = i then 0 else x $ k $ l) $ n $ m)"
      by simp
  qed (fact)

  thus "k-smooth_on S (\<lambda>A. (matrix_inv A)$i$j)"
    apply (intro smooth_on_cong[OF _ assms(2) matrix_inv_cong])
    apply (intro smooth_on_div_det[of "\<lambda>A. det (?inv_comp' A)"])
    using smooth_on_compose[of \<infinity> UNIV det S ?inv_comp'] smooth_on_det[OF open_UNIV]
    using assms(2) smooth_on_cong by fastforce
qed


lemma fin_sum_over_delta:
  fixes f::"'n::finite \<Rightarrow> 'a::semiring_1"
  shows "(\<Sum>(i::'n::finite)\<in>UNIV. ((if i=j then 1 else 0) * f i)) = f j"
proof -
  have "(\<Sum>i\<in>UNIV. (if i = j then 1 else 0) * f i) = (\<Sum>i\<in>UNIV. (if i=j then f j else 0))"
    by (simp add: mult_delta_left)
  also have "(\<Sum>i\<in>UNIV. (if i=j then f j else 0)) = f j"
    using sum.delta by auto
  then show ?thesis
    by (simp add: calculation)
qed


lemma matrix_is_linear_map:
  fixes A::"('a::{real_algebra_1,comm_semiring_1})^'m^'n" \<comment> \<open>again, real-based entries only...\<close>
  shows "linear ((*v) A) \<and> matrix ((*v) A) = A"
proof (rule conjI)
  let ?f = "\<lambda>v. (A *v v)"
  show "linear ?f"
    using matrix_vector_mul_linear by simp
  {
    fix i::'n and j::'m
    let ?v = "\<chi> j'. if j' = j then 1 else 0"
    have "?v $ k = (if k=j then 1 else 0)" for k
      by simp
    then have "A *v ?v = transpose A $ j"
      using matrix_vector_column[where A=A and x="?v"] fin_sum_over_delta
      by (smt (verit, best) mult.commute mult.right_neutral mult_zero_right sum.cong
        vector_smult_lid vector_smult_lzero)
    then have "(A *v (\<chi> j'. if j' = j then 1 else 0))$i = A$i$j"
      using matrix_vector_column[where x="?v"] transpose_def vec_lambda_beta
      by (smt (z3))
  }
  then show "matrix ?f = A"
    unfolding matrix_def axis_def by auto
qed


lemma smooth_on_matrix_inv:
  assumes "\<forall>A. A\<in>S \<longrightarrow> invertible A" "open S"
  shows "k-smooth_on S (matrix_inv::'a::{euclidean_space,real_normed_field}^'n^'n \<Rightarrow> 'a^'n^'n)"
  apply (intro smooth_on_mat[of k S])
  apply (intro smooth_on_matrix_inv_component[of S])
  by (auto simp add: assms)+


end