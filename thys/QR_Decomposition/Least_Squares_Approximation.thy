(*  
    Title:      Least_Squares_Approximation.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section{*Least Squares Approximation*}

theory Least_Squares_Approximation
imports
 QR_Decomposition
begin

subsection{*Second part of the Fundamental Theorem of Linear Algebra*}

text{*See \url{http://en.wikipedia.org/wiki/Fundamental_theorem_of_linear_algebra}*}

definition "orthogonal_complement W = {x. \<forall>y \<in> W. orthogonal x y}"

lemma subspace_orthogonal_complement: "subspace (orthogonal_complement W)"
  unfolding subspace_def orthogonal_complement_def
  by (simp add: orthogonal_def inner_left_distrib)

lemma orthogonal_complement_mono:
  assumes A_in_B: "A \<subseteq> B"
  shows "orthogonal_complement B \<subseteq> orthogonal_complement A"
proof
  fix x assume x: "x \<in> orthogonal_complement B"
  show "x \<in> orthogonal_complement A" using x unfolding orthogonal_complement_def
    by (simp add: orthogonal_def, metis A_in_B in_mono)
qed

lemma B_in_orthogonal_complement_of_orthogonal_complement:
  shows "B \<subseteq> orthogonal_complement (orthogonal_complement B)"
  by (auto simp add: orthogonal_complement_def orthogonal_def inner_commute)

lemma null_space_orthogonal_complement_row_space:
  fixes A::"real^'cols^'rows::{finite,wellorder}"
  shows "null_space A = orthogonal_complement (row_space A)"
proof (unfold null_space_def orthogonal_complement_def, auto)
  fix x xa assume Ax: "A *v x = 0" and xa: "xa \<in> row_space A"
  obtain y where y: "xa = transpose A *v y" using xa unfolding row_space_eq by blast
  have "y v* A = xa"
    using transpose_vector y by fastforce
  thus "orthogonal x xa" unfolding orthogonal_def
    using Ax dot_lmul_matrix inner_commute inner_zero_right
    by (metis Ax dot_lmul_matrix inner_commute inner_zero_right)
next
  fix x assume xa: "\<forall>xa\<in>row_space A. orthogonal x xa"
  show "A *v x = 0"
    using xa unfolding row_space_eq orthogonal_def
    by (auto, metis transpose_transpose dot_lmul_matrix inner_eq_zero_iff transpose_vector)
qed


lemma left_null_space_orthogonal_complement_col_space:
  fixes A::"real^'cols::{finite,wellorder}^'rows"
  shows "left_null_space A = orthogonal_complement (col_space A)"
  using null_space_orthogonal_complement_row_space[of "transpose A"]
  unfolding left_null_space_eq_null_space_transpose
  unfolding col_space_eq_row_space_transpose .


subsection{*Least Squares Approximation*}

text{*See \url{https://people.math.osu.edu/husen.1/teaching/571/least_squares.pdf}*}

lemma phytagorean_theorem_norm:
  assumes o: "orthogonal x y"
  shows "norm (x+y)^2=norm x^2 + norm y^2"
proof -
  have "norm (x+y)^2 = (x+y) \<bullet> (x+y)" unfolding power2_norm_eq_inner ..
  also have "... = ((x+y) \<bullet> x) + ((x+y) \<bullet> y)" unfolding inner_right_distrib ..
  also have "... = (x \<bullet> x) + (x \<bullet> y) + (y \<bullet> x) + (y \<bullet> y) "
    unfolding real_inner_class.inner_add_left by simp
  also have "... = (x \<bullet> x) + (y \<bullet> y)" using o unfolding orthogonal_def 
    by (metis monoid_add_class.add.right_neutral inner_commute)
  also have "... = norm x^2 + norm y^2" unfolding power2_norm_eq_inner ..
  finally show ?thesis .
qed


lemma in_orthogonal_complement_imp_orthogonal:
  assumes x: "y \<in> S"
  and "x \<in> orthogonal_complement S"
  shows "orthogonal x y" 
  using assms orthogonal_commute 
  unfolding orthogonal_complement_def 
  by blast


lemma in_orthogonal_complement_basis:
  fixes B::"'a::{euclidean_space} set"
  assumes S: "real_vector.subspace S"
  and ind_B: "real_vector.independent B"
  and B: "B \<subseteq> S"
  and span_B: "S \<subseteq> real_vector.span B"
  shows "(v \<in> orthogonal_complement S) = (\<forall>a\<in>B. orthogonal a v)" 
proof (unfold orthogonal_complement_def, auto)
  fix a assume "\<forall>x\<in>S. orthogonal v x" and "a \<in> B"  
  thus "orthogonal a v" 
    by (metis B orthogonal_commute set_rev_mp)
next
  fix x assume o: "\<forall>a\<in>B. orthogonal a v" and x: "x \<in> S"
  have finite_B: "finite B" using euclidean_space.independent_bound_general[OF ind_B] ..
  have span_B_eq: "S = real_vector.span B" using B S span_B real_vector.span_subspace by blast
  obtain f where f: "(\<Sum>a\<in>B. f a *\<^sub>R a) = x" using real_vector.span_finite[OF finite_B]
    using x unfolding span_B_eq by blast
  have "v \<bullet> x = v \<bullet> (\<Sum>a\<in>B. f a *\<^sub>R a)" unfolding f ..
  also have "... = (\<Sum>a\<in>B. v \<bullet> (f a *\<^sub>R a))" unfolding inner_setsum_right ..
  also have "... = (\<Sum>a\<in>B. f a * (v \<bullet> a))" unfolding inner_scaleR_right ..
  also have "... = 0" using setsum.neutral o unfolding orthogonal_def inner_commute by simp
  finally show "orthogonal v x" unfolding orthogonal_def .
qed


lemma orthogonal_v_minus_p_basis:
  fixes X::"'a::{euclidean_space} set"
  assumes subspace_S: "real_vector.subspace S"
  and finite_X: "finite X"
  and o: "pairwise orthogonal X"
  and a: "a\<in>X"
  shows "orthogonal (v - (setsum (\<lambda>x. ((v \<bullet> x)/(x \<bullet> x)) *\<^sub>R x)) X) a"
proof -
  let ?p="(setsum (\<lambda>x. ((v \<bullet> x)/(x \<bullet> x)) *\<^sub>R x) X)"
  have s0: "(\<Sum>x\<in>X-{a}. (v \<bullet> x / (x \<bullet> x)) *\<^sub>R x \<bullet> a) = 0"
    by (rule setsum.neutral, auto, metis a o orthogonal_def pairwise_def)
  have "?p \<bullet> a = (\<Sum>x\<in>X. (v \<bullet> x / (x \<bullet> x)) *\<^sub>R x \<bullet> a)" unfolding inner_setsum_left ..
  also have "... = (v \<bullet> a / (a \<bullet> a)) *\<^sub>R a \<bullet> a + (\<Sum>x\<in>X-{a}. (v \<bullet> x / (x \<bullet> x)) *\<^sub>R x \<bullet> a)"
    by (rule setsum.remove[OF finite_X a])
  also have "... = (v \<bullet> a)" unfolding s0 by auto
  finally have pa: "?p \<bullet> a = (v \<bullet> a)" .
  have "(v - ?p) \<bullet> a = (v \<bullet> a) - (?p \<bullet> a)" unfolding inner_diff_left ..
  also have "... = 0" unfolding pa by simp
  finally show ?thesis unfolding orthogonal_def .
qed

text{*Part 1 of the Theorem 1.7 in the previous website, but the proof has been carried out
  in other way.*}

lemma v_minus_p_orthogonal_complement:
  fixes X::"'a::{euclidean_space} set"
  assumes subspace_S: "real_vector.subspace S"
  and ind_X: "real_vector.independent X"
  and X: "X \<subseteq> S"
  and span_X: "S \<subseteq> real_vector.span X"
  and o: "pairwise orthogonal X"
  shows "(v - (setsum (\<lambda>x. ((v \<bullet> x)/(x \<bullet> x)) *\<^sub>R x)) X) \<in> orthogonal_complement S"
  unfolding in_orthogonal_complement_basis[OF subspace_S ind_X X span_X]
proof 
  fix a assume a: "a \<in> X"
  let ?p="(setsum (\<lambda>x. ((v \<bullet> x)/(x \<bullet> x)) *\<^sub>R x) X)"
  show "orthogonal a (v - (\<Sum>x\<in>X. (v \<bullet> x / (x \<bullet> x)) *\<^sub>R x))"
    unfolding orthogonal_commute[of a "v-?p"]
    by (rule orthogonal_v_minus_p_basis[OF subspace_S _ o a],
      simp add: euclidean_space.independent_bound_general[OF ind_X]) 
qed



text{*Part 2 of the Theorem 1.7 in the previous website.*}

lemma UNIV_orthogonal_complement_decomposition:
  fixes S::"'a::{euclidean_space} set"
  assumes s: "real_vector.subspace S"
  shows "UNIV = S + (orthogonal_complement S)"
proof (unfold set_plus_def, auto)
  fix v
  obtain X where ind_X: "real_vector.independent X"
    and X: "X \<subseteq> S"
    and span_X: "S \<subseteq> real_vector.span X"
    and o: "pairwise orthogonal X" 
    by (metis Generalizations.real_vector.span_eq Miscellaneous_QR.orthogonal_basis_exists s)
  have finite_X: "finite X" by (metis euclidean_space.independent_bound_general ind_X)
  let ?p="(setsum (\<lambda>x. ((v \<bullet> x)/(x \<bullet> x)) *\<^sub>R x) X)"
  have "v=?p +(v-?p)" by simp
  moreover have "?p \<in> S"
    by (rule real_vector.subspace_setsum[OF s finite_X], metis X s subsetD real_vector.subspace_mul)
  moreover have "(v-?p) \<in> orthogonal_complement S"
    by (rule v_minus_p_orthogonal_complement[OF s ind_X X span_X o])
  ultimately show "\<exists>a\<in>S. \<exists>b\<in>orthogonal_complement S. v = a + b" by force
qed


text{*Part 3 of the Theorem 1.7 in the previous website.*}

lemma least_squares_approximation:
  fixes X::"'a::{euclidean_space} set"
  assumes subspace_S: "real_vector.subspace S"
  and ind_X: "real_vector.independent X"
  and X: "X \<subseteq> S"
  and span_X: "S \<subseteq> real_vector.span X"
  and o: "pairwise orthogonal X"
  and not_eq: "(setsum (\<lambda>x. ((v \<bullet> x)/(x \<bullet> x)) *\<^sub>R x) X) \<noteq> y"
  and y: "y \<in> S"
  shows "norm (v - (setsum (\<lambda>x. ((v \<bullet> x)/(x \<bullet> x)) *\<^sub>R x)) X) < norm (v - y)"
proof -
  have S_eq_spanX: "S = real_vector.span X"
    by (metis X span_X real_vector.span_subspace subspace_S)
  let ?p="(setsum (\<lambda>x. ((v \<bullet> x)/(x \<bullet> x)) *\<^sub>R x) X)"
  have not_0: "(norm(?p - y))^2 \<noteq> 0"
    by (metis (lifting) eq_iff_diff_eq_0 norm_eq_zero not_eq power_eq_0_iff)
  have "norm (v-y)^2 = norm (v - ?p + ?p - y)^2" by auto
  also have "... = norm ((v - ?p) + (?p - y))^2" 
    unfolding add.assoc[symmetric] by simp
  also have "... = (norm (v - ?p))^2 + (norm(?p - y))^2"
  proof (rule phytagorean_theorem_norm, rule in_orthogonal_complement_imp_orthogonal) 
    show "?p - y \<in> S"
    proof (rule real_vector.subspace_sub[OF subspace_S _ y], 
        rule real_vector.subspace_setsum[OF subspace_S])
      show "finite X" by (metis euclidean_space.independent_bound_general ind_X)
      show "\<forall>x\<in>X. (v \<bullet> x / (x \<bullet> x)) *\<^sub>R x \<in> S" 
        by (metis S_eq_spanX real_vector.span_superset subspace_S real_vector.subspace_mul)
    qed
    show "v - ?p \<in> orthogonal_complement S"
      using v_minus_p_orthogonal_complement assms by auto        
  qed
  finally have "norm (v-?p)^2 < norm (v-y)^2" using not_0 by fastforce
  thus ?thesis by (metis (full_types) norm_gt_square power2_norm_eq_inner)
qed


corollary least_squares_approximation2:
  fixes S::"'a::{euclidean_space} set"
  assumes subspace_S: "real_vector.subspace S"
  and y: "y \<in> S"
  shows "\<exists>p\<in>S. norm (v - p) \<le> norm (v - y) \<and> (v-p) \<in> orthogonal_complement S"
proof -
  obtain X where  ind_X: "real_vector.independent X"
    and X: "X \<subseteq> S"
    and span_X: "S \<subseteq> real_vector.span X"
    and o: "pairwise orthogonal X"
    by (metis Generalizations.real_vector.span_eq Miscellaneous_QR.orthogonal_basis_exists subspace_S)
  let ?p="(setsum (\<lambda>x. ((v \<bullet> x)/(x \<bullet> x)) *\<^sub>R x) X)"
  show ?thesis 
  proof (rule bexI[of _ ?p], rule conjI)
    show " norm (v - (\<Sum>p\<in>X. (v \<bullet> p / (p \<bullet> p)) *\<^sub>R p)) \<le> norm (v - y)"
    proof (cases "?p=y")
      case True thus "norm (v - ?p) \<le> norm (v - y)" by simp
    next
      case False
      have "norm (v - ?p) < norm (v - y)" 
        by (rule least_squares_approximation[OF subspace_S ind_X X span_X o False y])
      thus "norm (v - ?p) \<le> norm (v - y)" by simp
    qed
    show "?p \<in> S" 
    proof (rule real_vector.subspace_setsum)
      show "real_vector.subspace S" using subspace_S .
      show "finite X" by (metis euclidean_space.independent_bound_general ind_X)
      show "\<forall>x\<in>X. (v \<bullet> x / (x \<bullet> x)) *\<^sub>R x \<in> S" 
        by (metis X in_mono subspace_S real_vector.subspace_mul)
    qed
    show "v - ?p\<in> orthogonal_complement S"
      by (rule v_minus_p_orthogonal_complement[OF subspace_S ind_X X span_X o])
  qed
qed

corollary least_squares_approximation3:
  fixes S::"'a::{euclidean_space} set"
  assumes subspace_S: "real_vector.subspace S"
  shows "\<exists>p\<in>S. \<forall>y\<in>S. norm (v - p) \<le> norm (v - y) \<and> (v-p) \<in> orthogonal_complement S"
proof -
  obtain X where  ind_X: "real_vector.independent X"
    and X: "X \<subseteq> S"
    and span_X: "S \<subseteq> real_vector.span X"
    and o: "pairwise orthogonal X"
    by (metis Generalizations.real_vector.span_eq Miscellaneous_QR.orthogonal_basis_exists subspace_S)
  let ?p="(setsum (\<lambda>x. ((v \<bullet> x)/(x \<bullet> x)) *\<^sub>R x) X)"
  show ?thesis
  proof (rule bexI[of _ ?p], auto)
    fix y assume y: "y\<in>S"
    show "norm (v - ?p) \<le> norm (v - y)"
    proof (cases "?p=y")
      case True thus ?thesis by simp
    next
      case False
      have "norm (v - ?p) < norm (v - y)"
        by (rule least_squares_approximation[OF subspace_S ind_X X span_X o False y])
      thus ?thesis by simp
    qed
    show "v - ?p \<in> orthogonal_complement S"
      by (rule v_minus_p_orthogonal_complement[OF subspace_S ind_X X span_X o])
  next
    show "?p \<in> S" 
    proof (rule real_vector.subspace_setsum)
      show "real_vector.subspace S" using subspace_S .
      show "finite X" by (metis euclidean_space.independent_bound_general ind_X)
      show "\<forall>x\<in>X. (v \<bullet> x / (x \<bullet> x)) *\<^sub>R x \<in> S"
        by (metis X in_mono subspace_S real_vector.subspace_mul)
    qed
  qed
qed


lemma norm_least_squares:
  fixes A::"real^'cols::{finite,wellorder}^'rows"
  shows "\<exists>x. \<forall>x'. norm (b - A *v x) \<le> norm (b - A *v x')"
proof -
  have "\<exists>p\<in>col_space A. \<forall>y\<in>col_space A. norm (b - p) \<le> norm (b - y) \<and> (b-p) \<in> orthogonal_complement (col_space A)"
    using least_squares_approximation3[OF subspace_col_space[of A, unfolded op_vec_scaleR]] .
  from this obtain p where p: "p \<in> col_space A" and least: "\<forall>y\<in>col_space A. norm (b - p) \<le> norm (b - y)"
    and bp_orthogonal: "(b-p) \<in> orthogonal_complement (col_space A)"
    by blast
  obtain x where x: "p = A *v x" using p unfolding col_space_eq by blast
  show ?thesis 
  proof (rule exI[of _ x], auto)
    fix x'
    have "A *v x' \<in> col_space A" unfolding col_space_eq by auto
    thus "norm (b - A *v x) \<le> norm (b - A *v x')" using least unfolding x by auto
  qed
qed

definition "set_least_squares_solution A b = {x. \<forall>y. norm (b - A *v x) \<le> norm (b - A *v y)}"

corollary least_squares_approximation4:
  fixes S::"'a::{euclidean_space} set"
  assumes subspace_S: "real_vector.subspace S"
  shows "\<exists>!p\<in>S. \<forall>y\<in>S-{p}. norm (v - p) < norm (v - y)"
proof (auto)
  obtain X where  ind_X: "real_vector.independent X"
    and X: "X \<subseteq> S"
    and span_X: "S \<subseteq> real_vector.span X"
    and o: "pairwise orthogonal X" 
    by (metis Generalizations.real_vector.span_eq Miscellaneous_QR.orthogonal_basis_exists subspace_S)
  let ?p="(setsum (\<lambda>x. ((v \<bullet> x)/(x \<bullet> x)) *\<^sub>R x) X)"
  show "\<exists>p. p \<in> S \<and> (\<forall>y\<in>S - {p}. norm (v - p) < norm (v - y))"
  proof (rule exI[of _ ?p], rule conjI, rule real_vector.subspace_setsum)
    show "real_vector.subspace S" using subspace_S .
    show "finite X" by (metis euclidean_space.independent_bound_general ind_X)
    show "\<forall>x\<in>X. (v \<bullet> x / (x \<bullet> x)) *\<^sub>R x \<in> S" 
      by (metis X span_X real_vector.span_subspace real_vector.span_superset subspace_S real_vector.subspace_mul)
    show "\<forall>y\<in>S - {?p}. norm (v - ?p) < norm (v - y)" 
      using X ind_X least_squares_approximation  o span_X subspace_S 
      by (metis (mono_tags) Diff_iff singletonI)
  qed
  fix p y
  assume p: "p \<in> S"
    and "\<forall>y\<in>S - {p}. norm (v - p) < norm (v - y)"
    and "y \<in> S"
    and "\<forall>ya\<in>S - {y}. norm (v - y) < norm (v - ya)"
  thus "p = y" by (metis member_remove not_less_iff_gr_or_eq remove_def)
qed


corollary least_squares_approximation4':
  fixes S::"'a::{euclidean_space} set"
  assumes subspace_S: "real_vector.subspace S"
  shows "\<exists>!p\<in>S. \<forall>y\<in>S. norm (v - p) \<le> norm (v - y)"
proof (auto)
  obtain X where ind_X: "real_vector.independent X"
    and X: "X \<subseteq> S"
    and span_X: "S \<subseteq> real_vector.span X"
    and o: "pairwise orthogonal X"
    by (metis Generalizations.real_vector.span_eq Miscellaneous_QR.orthogonal_basis_exists subspace_S)
  let ?p="(setsum (\<lambda>x. ((v \<bullet> x)/(x \<bullet> x)) *\<^sub>R x) X)"
  show "\<exists>p. p \<in> S \<and> (\<forall>y\<in>S. norm (v - p) \<le> norm (v - y))"
  proof (rule exI[of _ ?p], rule conjI, rule real_vector.subspace_setsum)
    show "real_vector.subspace S" using subspace_S .
    show "finite X" by (metis euclidean_space.independent_bound_general ind_X)
    show "\<forall>x\<in>X. (v \<bullet> x / (x \<bullet> x)) *\<^sub>R x \<in> S" 
      by (metis X span_X real_vector.span_subspace 
        real_vector.span_superset subspace_S real_vector.subspace_mul)
    show "\<forall>y\<in>S. norm (v - ?p) \<le> norm (v - y)"
      by (metis (mono_tags) X dual_order.refl ind_X least_squares_approximation less_imp_le o span_X subspace_S)
  qed
  fix p y
  assume p: "p \<in> S" and p': "\<forall>y\<in>S. norm (v - p) \<le> norm (v - y)"
    and y: "y \<in> S" and y': "\<forall>ya\<in>S. norm (v - y) \<le> norm (v - ya)"
  obtain a where a: "a\<in>S" and a': "\<forall>y\<in>S-{a}. norm (v - a) < norm (v - y)"
    and a_uniq: "\<forall>b. (b\<in>S \<and> (\<forall>c\<in>S-{b}. norm (v - b) < norm (v - c))) \<longrightarrow> b=a"
    using least_squares_approximation4[OF subspace_S]
    by metis
  have "p=a" using p p' a_uniq leD  by (metis a a' member_remove remove_def)
  moreover have "y=a" using y y' a_uniq
    by (metis a a' leD member_remove remove_def)
  ultimately show "p = y" by simp
qed

corollary least_squares_approximation5:
  fixes S::"'a::{euclidean_space} set"
  assumes subspace_S: "real_vector.subspace S"
  shows "\<exists>!p\<in>S. \<forall>y\<in>S-{p}. norm (v - p) < norm (v - y) \<and> v-p \<in> orthogonal_complement S"
proof (auto)
  obtain X where  ind_X: "real_vector.independent X"
    and X: "X \<subseteq> S"
    and span_X: "S \<subseteq> real_vector.span X"
    and o: "pairwise orthogonal X"
    by (metis Generalizations.real_vector.span_eq Miscellaneous_QR.orthogonal_basis_exists subspace_S)
  let ?p="(setsum (\<lambda>x. ((v \<bullet> x)/(x \<bullet> x)) *\<^sub>R x) X)"
  show "\<exists>p. p \<in> S \<and> (\<forall>y\<in>S - {p}. norm (v - p) < norm (v - y) \<and> v - p \<in> orthogonal_complement S)"
  proof (rule exI[of _ ?p], rule conjI, rule real_vector.subspace_setsum)
    show "real_vector.subspace S" using subspace_S .
    show "finite X" by (metis euclidean_space.independent_bound_general ind_X)
    show "\<forall>x\<in>X. (v \<bullet> x / (x \<bullet> x)) *\<^sub>R x \<in> S" 
      by (metis X span_X real_vector.span_subspace 
        real_vector.span_superset subspace_S real_vector.subspace_mul)
    have "\<forall>y\<in>S - {?p}. norm (v - ?p) < norm (v - y)" 
      using least_squares_approximation[OF subspace_S ind_X X span_X o]
      by (metis (no_types) member_remove remove_def)
    moreover have "v - ?p \<in> orthogonal_complement S" 
      by (metis (no_types) X ind_X o span_X subspace_S v_minus_p_orthogonal_complement)
    ultimately show "\<forall>y\<in>S - {?p}. norm (v - ?p) < norm (v - y) \<and> v - ?p \<in> orthogonal_complement S"
      by auto        
  qed
  fix p y
  assume p: "p \<in> S" and p': "\<forall>y\<in>S - {p}. norm (v - p) < norm (v - y) \<and> v - p \<in> orthogonal_complement S"
    and y: "y \<in> S" and y': "\<forall>ya\<in>S - {y}. norm (v - y) < norm (v - ya) \<and> v - y \<in> orthogonal_complement S"
  show "p=y"
    by (metis least_squares_approximation4 p p' subspace_S y y')
qed

corollary least_squares_approximation5':
  fixes S::"'a::{euclidean_space} set"
  assumes subspace_S: "real_vector.subspace S"
  shows "\<exists>!p\<in>S. \<forall>y\<in>S. norm (v - p) \<le> norm (v - y) \<and> v-p \<in> orthogonal_complement S"
  by (metis least_squares_approximation3 least_squares_approximation4' subspace_S)

corollary least_squares_approximation6:
  fixes S::"'a::{euclidean_space} set"
  assumes subspace_S: "real_vector.subspace S"
  and "p\<in>S"
  and "\<forall>y\<in>S. norm (v - p) \<le> norm (v - y)"
  shows "v-p \<in> orthogonal_complement S"
proof -
  obtain a where a: "a\<in>S" and a': "\<forall>y\<in>S. norm (v - a) \<le> norm (v - y) \<and> v-a \<in> orthogonal_complement S"
    and "\<forall>b. (b\<in>S \<and> (\<forall>y\<in>S. norm (v - b) \<le> norm (v - y) \<and> v-b \<in> orthogonal_complement S)) \<longrightarrow> b=a"
    using least_squares_approximation5'[OF subspace_S] by metis
  have "p=a"
    by (metis a a' assms(2) assms(3) least_squares_approximation4' subspace_S)
  thus ?thesis using a' by (metis assms(2))
qed


corollary least_squares_approximation7:
  fixes S::"'a::{euclidean_space} set"
  assumes subspace_S: "real_vector.subspace S"
  and "v - p \<in> orthogonal_complement S"
  and "p\<in>S"
  and "y \<in> S"
  shows "norm (v - p) \<le> norm (v - y)" 
proof (cases "y=p")
  case True thus ?thesis by simp
next
  case False
  have "norm (v - y)^2 = norm ((v - p) + (p - y))^2"
    by (metis (hide_lams, no_types) add_diff_cancel_left add_ac(1) add_diff_add add_diff_cancel)
  also have "... = norm (v - p)^2 + norm (p - y)^2" 
  proof (rule phytagorean_theorem_norm, rule in_orthogonal_complement_imp_orthogonal)
    show "p - y \<in> S" by (metis assms(3) assms(4) subspace_S real_vector.subspace_sub)
    show "v - p \<in> orthogonal_complement S" by (metis assms(2)) 
  qed
  finally have "norm (v - p)^2 \<le> norm (v - y)^2" by auto
  thus "norm (v - p)\<le> norm (v - y)" by (metis norm_ge_zero power2_le_imp_le)
qed


lemma in_set_least_squares_solution:
  fixes A::"real^'cols::{finite, wellorder}^'rows"
  assumes o: "A *v x - b \<in> orthogonal_complement (col_space A)"
  shows "(x \<in> set_least_squares_solution A b)"
proof (unfold set_least_squares_solution_def, auto)
  fix y 
  show " norm (b - A *v x) \<le> norm (b - A *v y)"
  proof (rule least_squares_approximation7)
    show "real_vector.subspace (col_space A)" using subspace_col_space[of A, unfolded op_vec_scaleR] .
    show "b - A *v x \<in> orthogonal_complement (col_space A)" 
      using o subspace_orthogonal_complement[of "(col_space A)"]
      using minus_diff_eq subspace_neg by metis
    show "A *v x \<in> col_space A" unfolding col_space_eq[of A] by auto
    show "A *v y \<in> col_space A" unfolding col_space_eq by auto
  qed
qed

lemma in_set_least_squares_solution_eq:
  fixes A::"real^'cols::{finite,wellorder}^'rows"
  shows "(x \<in> set_least_squares_solution A b) = (transpose A ** A *v x = transpose A *v b)"
proof
  assume x: "x \<in> set_least_squares_solution A b"
  hence a: "\<forall>a. norm (b - A *v x) \<le> norm (b - A *v a)" unfolding set_least_squares_solution_def by simp
  have "b - A *v x \<in> orthogonal_complement (col_space A)"
  proof (rule least_squares_approximation6)
    show "real_vector.subspace (col_space A)" using subspace_col_space[of A, unfolded op_vec_scaleR] .
    show "A *v x \<in> col_space A" unfolding col_space_eq[of A] by auto
    show "\<forall>y\<in>col_space A. norm (b - A *v x) \<le> norm (b - y)" using a unfolding col_space_eq by auto
  qed
  hence "b - A *v x \<in> null_space (transpose A)"
    unfolding null_space_orthogonal_complement_row_space
    unfolding col_space_eq_row_space_transpose .
  hence "transpose A *v (b - A *v x) = 0" unfolding null_space_def by simp
  thus "(transpose A ** A) *v x = (transpose A) *v b"
    by (metis eq_iff_diff_eq_0 matrix_vector_mul_assoc matrix_vector_right_distrib_minus)
next
  assume "transpose A ** A *v x = transpose A *v b"
  hence "(transpose A) *v (A *v x - b) = 0" 
    by (metis diff_self matrix_vector_mul_assoc matrix_vector_right_distrib_minus)
  hence "(A *v x - b) \<in> null_space (transpose A)" unfolding null_space_def by simp
  hence "(A *v x - b) \<in> orthogonal_complement (col_space A)" 
    by (metis left_null_space_eq_null_space_transpose left_null_space_orthogonal_complement_col_space)
  thus "x \<in> set_least_squares_solution A b" by (rule in_set_least_squares_solution)
qed


lemma in_set_least_squares_solution_eq_full_rank:
  fixes A::"real^'cols::mod_type^'rows::mod_type"
  assumes r: "rank A = ncols A"
  shows "(x \<in> set_least_squares_solution A b) = (x = matrix_inv (transpose A ** A)**transpose A *v b)"
proof -
  have int_tA: "invertible (transpose A ** A)" using invertible_transpose_mult[OF r] .
  show ?thesis
  proof 
    fix x assume "x \<in> set_least_squares_solution A b"
    hence "transpose A ** A *v x = transpose A *v b" using in_set_least_squares_solution_eq by auto
    thus "x = matrix_inv (transpose A ** A) ** transpose A *v b"
      by (metis int_tA matrix_inv_left matrix_vector_mul_assoc matrix_vector_mul_lid)
  next
    fix x assume "x = matrix_inv (transpose A ** A) ** transpose A *v b"
    hence "transpose A ** A *v x = transpose A *v b"
      by (metis int_tA matrix_inv_right matrix_vector_mul_assoc matrix_vector_mul_lid)
    thus "x \<in> set_least_squares_solution A b" unfolding in_set_least_squares_solution_eq .
  qed
qed



lemma in_set_least_squares_solution_eq_full_rank_QR:
  fixes A::"real^'cols::{enum, mod_type}^'rows::{enum, mod_type}"
  assumes r: "rank A = ncols A"
  shows "(x \<in> set_least_squares_solution A b) = ((snd (QR_decomposition A)) *v x = transpose (fst (QR_decomposition A)) *v b)"
proof -
  let ?Q = "fst (QR_decomposition A)"
  let ?R = "snd (QR_decomposition A)"
  have inv_tR: "invertible (transpose ?R)"
    by (metis invertible_snd_QR_decomposition invertible_transpose r)
  have inv_inv_tR: "invertible (matrix_inv (transpose ?R))"
    by (metis inv_tR invertible_fst_Gauss_Jordan_PA matrix_inv_Gauss_Jordan_PA)
  have "(x \<in> set_least_squares_solution A b) = (transpose A ** A *v x = transpose A *v b)"
    using in_set_least_squares_solution_eq .
  also have "... = (transpose (?Q ** ?R) ** (?Q ** ?R) *v x = transpose (?Q ** ?R) *v b)"
    using QR_decomposition_mult[OF r] by simp
  also have "... = (transpose ?R ** transpose ?Q **  (?Q ** ?R) *v x  = transpose ?R ** transpose ?Q *v b)"
    by (metis (hide_lams, no_types) matrix_transpose_mul)
  also have "... = (transpose ?R *v (transpose ?Q ** (?Q ** ?R) *v x)  = transpose ?R *v (transpose ?Q *v b))"
    by (metis (hide_lams, no_types) matrix_vector_mul_assoc)
  also have "... = (matrix_inv (transpose ?R) *v (transpose ?R *v (transpose ?Q ** (?Q ** ?R) *v x))  
    = matrix_inv (transpose ?R) *v (transpose ?R *v (transpose ?Q *v b)))"
    using inv_matrix_vector_mul_left[OF inv_inv_tR] by auto
  also have "... = ((matrix_inv (transpose ?R) ** transpose ?R) *v (transpose ?Q ** (?Q ** ?R) *v x)  
    = (matrix_inv (transpose ?R) ** transpose ?R) *v (transpose ?Q *v b))"
    by (metis (hide_lams, no_types) matrix_vector_mul_assoc)
  also have "... = (transpose ?Q ** (?Q ** ?R) *v x = transpose ?Q *v b)"
    unfolding matrix_inv_left[OF inv_tR]
    unfolding matrix_vector_mul_lid ..
  also have "... = ((transpose ?Q ** ?Q) ** ?R *v x = transpose ?Q *v b)"
    by (metis (hide_lams, no_types) matrix_mul_assoc)
  also have "... = (?R *v x = transpose ?Q *v b)"
    unfolding orthogonal_matrix_fst_QR_decomposition[OF r]
    unfolding matrix_mul_lid ..
  finally show "(x \<in> set_least_squares_solution A b) = (?R *v x = (transpose ?Q) *v b)" .
qed

(*TODO: Maybe demonstrate that in this case there's only one solution.*)
corollary in_set_least_squares_solution_eq_full_rank_QR2:
  fixes A::"real^'cols::{enum, mod_type}^'rows::{enum, mod_type}"
  assumes r: "rank A = ncols A"
  shows "(x \<in> set_least_squares_solution A b) = (x = matrix_inv (snd (QR_decomposition A)) ** transpose (fst (QR_decomposition A)) *v b)"
proof -
  let ?Q = "fst (QR_decomposition A)"
  let ?R = "snd (QR_decomposition A)"
  have inv_R: "invertible ?R" by (metis invertible_snd_QR_decomposition r)
  have "(x \<in> set_least_squares_solution A b) = (?R *v x = transpose ?Q *v b)"
    using in_set_least_squares_solution_eq_full_rank_QR[OF r] .
  also have "... = (matrix_inv ?R ** ?R *v x = matrix_inv ?R ** transpose ?Q *v b)"
    by (metis (hide_lams, no_types) Gauss_Jordan_PA_eq calculation fst_Gauss_Jordan_PA inv_R 
      inv_matrix_vector_mul_left invertible_fst_Gauss_Jordan_PA matrix_inv_Gauss matrix_vector_mul_assoc)
  also have "... = (x = matrix_inv ?R ** transpose ?Q *v b)"
    by (metis inv_R matrix_inv_left matrix_vector_mul_lid)
  finally show "(x \<in> set_least_squares_solution A b) = (x = matrix_inv ?R ** transpose ?Q *v b)" .
qed

lemma set_least_squares_solution_unique_solution:
  fixes A::"real^'cols::{mod_type}^'rows::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "(set_least_squares_solution A b) = {matrix_inv (transpose A ** A)**transpose A *v b}"
  by (metis (hide_lams, mono_tags) empty_iff in_set_least_squares_solution_eq_full_rank
    empty_iff insertI1 r subsetI subset_singletonD)

lemma set_least_squares_solution_unique_solution_QR:
  fixes A::"real^'cols::{enum, mod_type}^'rows::{enum, mod_type}"
  assumes r: "rank A = ncols A"
  shows "(set_least_squares_solution A b) = {matrix_inv (snd (QR_decomposition A)) ** transpose (fst (QR_decomposition A)) *v b}"
  by (metis (hide_lams, mono_tags) empty_iff in_set_least_squares_solution_eq_full_rank_QR2 insertI1 r subsetI subset_singletonD)

end
