(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)

section \<open>\<open>Complex_Inner_Product\<close> -- Complex Inner Product Spaces\<close>

theory Complex_Inner_Product
  imports
    Complex_Inner_Product0
begin

subsection \<open>Complex inner product spaces\<close>

unbundle cinner_syntax

lemma cinner_real: "cinner x x \<in> \<real>"
  by (simp add: cdot_square_norm)

lemmas cinner_commute' [simp] = cinner_commute[symmetric]

lemma (in complex_inner) cinner_eq_flip: \<open>(cinner x y = cinner z w) \<longleftrightarrow> (cinner y x = cinner w z)\<close>
  by (metis cinner_commute)

lemma Im_cinner_x_x[simp]: "Im (x \<bullet>\<^sub>C x) = 0"
  using comp_Im_same[OF cinner_ge_zero] by simp


lemma of_complex_inner_1' [simp]:
  "cinner (1 :: 'a :: {complex_inner, complex_normed_algebra_1}) (of_complex x) = x"
  by (metis cinner_commute complex_cnj_cnj of_complex_inner_1)


class chilbert_space = complex_inner + complete_space
begin
subclass cbanach by standard
end

instantiation complex :: "chilbert_space" begin
instance ..
end

subsection \<open>Misc facts\<close>

lemma cinner_scaleR_left [simp]: "cinner (scaleR r x) y = of_real r * (cinner x y)"
  by (simp add: scaleR_scaleC)

lemma cinner_scaleR_right [simp]: "cinner x (scaleR r y) = of_real r * (cinner x y)"
  by (simp add: scaleR_scaleC)

text \<open>This is a useful rule for establishing the equality of vectors\<close>
lemma cinner_extensionality:
  assumes \<open>\<And>\<gamma>. \<gamma> \<bullet>\<^sub>C \<psi> = \<gamma> \<bullet>\<^sub>C \<phi>\<close>
  shows \<open>\<psi> = \<phi>\<close>
  by (metis assms cinner_eq_zero_iff cinner_simps(3) right_minus_eq)

lemma polar_identity:
  includes notation_norm
  shows \<open>\<parallel>x + y\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 + 2 * Re (x \<bullet>\<^sub>C y)\<close>
    \<comment> \<open>Shown in the proof of Corollary 1.5 in \<^cite>\<open>conway2013course\<close>\<close>
proof -
  have \<open>(x \<bullet>\<^sub>C y) + (y \<bullet>\<^sub>C x) = (x \<bullet>\<^sub>C y) + cnj (x \<bullet>\<^sub>C y)\<close>
    by simp
  hence \<open>(x \<bullet>\<^sub>C y) + (y \<bullet>\<^sub>C x) = 2 * Re (x \<bullet>\<^sub>C y) \<close>
    using complex_add_cnj by presburger
  have \<open>\<parallel>x + y\<parallel>^2 = (x+y) \<bullet>\<^sub>C (x+y)\<close>
    by (simp add: cdot_square_norm)
  hence \<open>\<parallel>x + y\<parallel>^2 = (x \<bullet>\<^sub>C x) + (x \<bullet>\<^sub>C y) + (y \<bullet>\<^sub>C x) + (y \<bullet>\<^sub>C y)\<close>
    by (simp add: cinner_add_left cinner_add_right)
  thus ?thesis using  \<open>(x \<bullet>\<^sub>C y) + (y \<bullet>\<^sub>C x) = 2 * Re (x \<bullet>\<^sub>C y)\<close>
    by (smt (verit, ccfv_SIG) Re_complex_of_real plus_complex.simps(1) power2_norm_eq_cinner')
qed

lemma polar_identity_minus:
  includes notation_norm
  shows \<open>\<parallel>x - y\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 - 2 * Re (x \<bullet>\<^sub>C y)\<close>
proof-
  have \<open>\<parallel>x + (-y)\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>-y\<parallel>^2 + 2 * Re (x \<bullet>\<^sub>C -y)\<close>
    using polar_identity by blast
  hence \<open>\<parallel>x - y\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 - 2*Re (x \<bullet>\<^sub>C y)\<close>
    by simp
  thus ?thesis
    by blast
qed

proposition parallelogram_law:
  includes notation_norm
  fixes x y :: "'a::complex_inner"
  shows \<open>\<parallel>x+y\<parallel>^2 + \<parallel>x-y\<parallel>^2 = 2*( \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 )\<close>
    \<comment> \<open>Shown in the proof of Theorem 2.3 in \<^cite>\<open>conway2013course\<close>\<close>
  by (simp add: polar_identity_minus polar_identity)


theorem pythagorean_theorem:
  includes notation_norm
  shows \<open>(x \<bullet>\<^sub>C y) = 0 \<Longrightarrow> \<parallel> x + y \<parallel>^2 = \<parallel> x \<parallel>^2 + \<parallel> y \<parallel>^2\<close>
    \<comment> \<open>Shown in the proof of Theorem 2.2 in \<^cite>\<open>conway2013course\<close>\<close>
  by (simp add: polar_identity)

lemma pythagorean_theorem_sum:
  assumes q1: "\<And>a a'. a \<in> t \<Longrightarrow> a' \<in> t \<Longrightarrow> a \<noteq> a' \<Longrightarrow> f a \<bullet>\<^sub>C f a' = 0"
    and q2: "finite t"
  shows "(norm  (\<Sum>a\<in>t. f a))^2 = (\<Sum>a\<in>t.(norm (f a))^2)"
proof (insert q1, use q2 in induction)
  case empty
  show ?case
    by auto
next
  case (insert x F)
  have r1: "f x \<bullet>\<^sub>C f a = 0"
    if "a \<in> F"
    for a
    using that insert.hyps(2) insert.prems by auto
  have "sum f F = (\<Sum>a\<in>F. f a)"
    by simp
  hence s4: "f x \<bullet>\<^sub>C sum f F = f x \<bullet>\<^sub>C (\<Sum>a\<in>F. f a)"
    by simp
  also have s3: "\<dots> = (\<Sum>a\<in>F. f x \<bullet>\<^sub>C f a)"
    using cinner_sum_right by auto
  also have s2: "\<dots> = (\<Sum>a\<in>F. 0)"
    using r1
    by simp
  also have s1: "\<dots> = 0"
    by simp
  finally have xF_ortho: "f x \<bullet>\<^sub>C sum f F = 0"
    using s2 s3 by auto
  have "(norm (sum f (insert x F)))\<^sup>2 = (norm (f x + sum f F))\<^sup>2"
    by (simp add: insert.hyps(1) insert.hyps(2))
  also have "\<dots> = (norm (f x))\<^sup>2 + (norm (sum f F))\<^sup>2"
    using xF_ortho by (rule pythagorean_theorem)
  also have "\<dots> = (norm (f x))\<^sup>2 + (\<Sum>a\<in>F.(norm (f a))^2)"
    apply (subst insert.IH) using insert.prems by auto
  also have "\<dots> = (\<Sum>a\<in>insert x F.(norm (f a))^2)"
    by (simp add: insert.hyps(1) insert.hyps(2))
  finally show ?case
    by simp
qed


lemma Cauchy_cinner_Cauchy:
  fixes x y :: \<open>nat \<Rightarrow> 'a::complex_inner\<close>
  assumes a1: \<open>Cauchy x\<close> and a2: \<open>Cauchy y\<close>
  shows \<open>Cauchy (\<lambda> n. x n \<bullet>\<^sub>C y n)\<close>
proof-
  have \<open>bounded (range x)\<close>
    using a1
    by (simp add: Elementary_Metric_Spaces.cauchy_imp_bounded)
  hence b1: \<open>\<exists>M. \<forall>n. norm (x n) < M\<close>
    by (meson bounded_pos_less rangeI)
  have \<open>bounded (range y)\<close>
    using a2
    by (simp add: Elementary_Metric_Spaces.cauchy_imp_bounded)
  hence b2: \<open>\<exists> M. \<forall> n. norm (y n) < M\<close>
    by (meson bounded_pos_less rangeI)
  have \<open>\<exists>M. \<forall>n. norm (x n) < M \<and> norm (y n) < M\<close>
    using b1 b2
    by (metis dual_order.strict_trans linorder_neqE_linordered_idom)
  then obtain M where M1: \<open>\<And>n. norm (x n) < M\<close> and M2: \<open>\<And>n. norm (y n) < M\<close>
    by blast
  have M3: \<open>M > 0\<close>
    by (smt M2 norm_not_less_zero)
  have \<open>\<exists>N. \<forall>n \<ge> N. \<forall>m \<ge> N. norm ( (\<lambda> i. x i \<bullet>\<^sub>C y i) n -  (\<lambda> i. x i \<bullet>\<^sub>C y i) m ) < e\<close>
    if "e > 0" for e
  proof-
    have \<open>e / (2*M) > 0\<close>
      using M3
      by (simp add: that)
    hence \<open>\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. norm (x n - x m) < e / (2*M)\<close>
      using a1
      by (simp add: Cauchy_iff)
    then obtain N1 where N1_def: \<open>\<And>n m. n\<ge>N1 \<Longrightarrow> m\<ge>N1 \<Longrightarrow> norm (x n - x m) < e / (2*M)\<close>
      by blast
    have x1: \<open>\<exists>N. \<forall> n\<ge>N. \<forall> m\<ge>N. norm (y n - y m) < e / (2*M)\<close>
      using a2 \<open>e / (2*M) > 0\<close>
      by (simp add: Cauchy_iff)
    obtain N2 where N2_def: \<open>\<And>n m.  n\<ge>N2 \<Longrightarrow> m\<ge>N2 \<Longrightarrow> norm (y n - y m) < e / (2*M)\<close>
      using x1
      by blast
    define N where N_def: \<open>N = N1 + N2\<close>
    hence \<open>N \<ge> N1\<close>
      by auto
    have \<open>N \<ge> N2\<close>
      using N_def
      by auto
    have \<open>norm (x n \<bullet>\<^sub>C y n - x m \<bullet>\<^sub>C y m) < e\<close>
      if \<open>n \<ge> N\<close> and \<open>m \<ge> N\<close>
      for n m
    proof -
      have \<open>x n \<bullet>\<^sub>C y n - x m \<bullet>\<^sub>C y m = (x n \<bullet>\<^sub>C y n - x m \<bullet>\<^sub>C y n) + (x m \<bullet>\<^sub>C y n - x m \<bullet>\<^sub>C y m)\<close>
        by simp
      hence y1: \<open>norm (x n \<bullet>\<^sub>C y n - x m \<bullet>\<^sub>C y m) \<le> norm (x n \<bullet>\<^sub>C y n - x m \<bullet>\<^sub>C y n)
           + norm (x m \<bullet>\<^sub>C y n - x m \<bullet>\<^sub>C y m)\<close>
        by (metis norm_triangle_ineq)

      have \<open>x n \<bullet>\<^sub>C y n - x m \<bullet>\<^sub>C y n = (x n - x m) \<bullet>\<^sub>C y n\<close>
        by (simp add: cinner_diff_left)
      hence \<open>norm (x n \<bullet>\<^sub>C y n - x m \<bullet>\<^sub>C y n) = norm ((x n - x m) \<bullet>\<^sub>C y n)\<close>
        by simp
      moreover have \<open>norm ((x n - x m) \<bullet>\<^sub>C y n) \<le> norm (x n - x m) * norm (y n)\<close>
        using complex_inner_class.Cauchy_Schwarz_ineq2 by blast
      moreover have \<open>norm (y n) < M\<close>
        by (simp add: M2)
      moreover have \<open>norm (x n - x m) < e/(2*M)\<close>
        using \<open>N \<le> m\<close> \<open>N \<le> n\<close> \<open>N1 \<le> N\<close> N1_def by auto
      ultimately have \<open>norm ((x n \<bullet>\<^sub>C y n) - (x m \<bullet>\<^sub>C y n)) < (e/(2*M)) * M\<close>
        by (smt linordered_semiring_strict_class.mult_strict_mono norm_ge_zero)
      moreover have \<open> (e/(2*M)) * M = e/2\<close>
        using \<open>M > 0\<close> by simp
      ultimately have  \<open>norm ((x n \<bullet>\<^sub>C y n) - (x m \<bullet>\<^sub>C y n)) < e/2\<close>
        by simp
      hence y2: \<open>norm (x n \<bullet>\<^sub>C y n - x m \<bullet>\<^sub>C y n) < e/2\<close>
        by blast
      have \<open>x m \<bullet>\<^sub>C y n - x m \<bullet>\<^sub>C y m = x m \<bullet>\<^sub>C (y n - y m)\<close>
        by (simp add: cinner_diff_right)
      hence \<open>norm ((x m \<bullet>\<^sub>C y n) - (x m \<bullet>\<^sub>C y m)) = norm (x m \<bullet>\<^sub>C (y n - y m))\<close>
        by simp
      moreover have \<open>norm (x m \<bullet>\<^sub>C (y n - y m)) \<le> norm (x m) * norm (y n - y m)\<close>
        by (meson complex_inner_class.Cauchy_Schwarz_ineq2)
      moreover have \<open>norm (x m) < M\<close>
        by (simp add: M1)
      moreover have \<open>norm (y n - y m) < e/(2*M)\<close>
        using \<open>N \<le> m\<close> \<open>N \<le> n\<close> \<open>N2 \<le> N\<close> N2_def by auto
      ultimately have \<open>norm ((x m \<bullet>\<^sub>C y n) - (x m \<bullet>\<^sub>C y m)) < M * (e/(2*M))\<close>
        by (smt linordered_semiring_strict_class.mult_strict_mono norm_ge_zero)
      moreover have \<open>M * (e/(2*M)) = e/2\<close>
        using \<open>M > 0\<close> by simp
      ultimately have  \<open>norm ((x m \<bullet>\<^sub>C y n) - (x m \<bullet>\<^sub>C y m)) < e/2\<close>
        by simp
      hence y3: \<open>norm ((x m \<bullet>\<^sub>C y n) - (x m \<bullet>\<^sub>C y m)) < e/2\<close>
        by blast
      show \<open>norm ( (x n \<bullet>\<^sub>C y n) - (x m \<bullet>\<^sub>C y m) ) < e\<close>
        using y1 y2 y3 by simp
    qed
    thus ?thesis by blast
  qed
  thus ?thesis
    by (simp add: CauchyI)
qed


lemma cinner_sup_norm: \<open>norm \<psi> = (SUP \<phi>. cmod (cinner \<phi> \<psi>) / norm \<phi>)\<close>
proof (rule sym, rule cSup_eq_maximum)
  have \<open>norm \<psi> = cmod (cinner \<psi> \<psi>) / norm \<psi>\<close>
    by (metis norm_eq_sqrt_cinner norm_ge_zero real_div_sqrt)
  then show \<open>norm \<psi> \<in> range (\<lambda>\<phi>. cmod (cinner \<phi> \<psi>) / norm \<phi>)\<close>
    by blast
next
  fix n assume \<open>n \<in> range (\<lambda>\<phi>. cmod (cinner \<phi> \<psi>) / norm \<phi>)\<close>
  then obtain \<phi> where n\<phi>: \<open>n = cmod (cinner \<phi> \<psi>) / norm \<phi>\<close>
    by auto
  show \<open>n \<le> norm \<psi>\<close>
    unfolding n\<phi>
    by (simp add: complex_inner_class.Cauchy_Schwarz_ineq2 divide_le_eq ordered_field_class.sign_simps(33))
qed

lemma cinner_sup_onorm:
  fixes A :: \<open>'a::{real_normed_vector,not_singleton} \<Rightarrow> 'b::complex_inner\<close>
  assumes \<open>bounded_linear A\<close>
  shows \<open>onorm A = (SUP (\<psi>,\<phi>). cmod (cinner \<psi> (A \<phi>)) / (norm \<psi> * norm \<phi>))\<close>
proof (unfold onorm_def, rule cSup_eq_cSup)
  show \<open>bdd_above (range (\<lambda>x. norm (A x) / norm x))\<close>
    by (meson assms bdd_aboveI2 le_onorm)
next
  fix a
  assume \<open>a \<in> range (\<lambda>\<phi>. norm (A \<phi>) / norm \<phi>)\<close>
  then obtain \<phi> where \<open>a = norm (A \<phi>) / norm \<phi>\<close>
    by auto
  then have \<open>a \<le> cmod (cinner (A \<phi>) (A \<phi>)) / (norm (A \<phi>) * norm \<phi>)\<close>
    apply auto
    by (smt (verit) divide_divide_eq_left norm_eq_sqrt_cinner norm_imp_pos_and_ge real_div_sqrt)
  then show \<open>\<exists>b\<in>range (\<lambda>(\<psi>, \<phi>). cmod (cinner \<psi> (A \<phi>)) / (norm \<psi> * norm \<phi>)). a \<le> b\<close>
    by force
next
  fix b
  assume \<open>b \<in> range (\<lambda>(\<psi>, \<phi>). cmod (cinner \<psi> (A \<phi>)) / (norm \<psi> * norm \<phi>))\<close>
  then obtain \<psi> \<phi> where b: \<open>b = cmod (cinner \<psi> (A \<phi>)) / (norm \<psi> * norm \<phi>)\<close>
    by auto
  then have \<open>b \<le> norm (A \<phi>) / norm \<phi>\<close>
    apply auto
    by (smt (verit, ccfv_threshold) complex_inner_class.Cauchy_Schwarz_ineq2 division_ring_divide_zero linordered_field_class.divide_right_mono mult_cancel_left1 nonzero_mult_divide_mult_cancel_left2 norm_imp_pos_and_ge ordered_field_class.sign_simps(33) zero_le_divide_iff)
  then show \<open>\<exists>a\<in>range (\<lambda>x. norm (A x) / norm x). b \<le> a\<close>
    by auto
qed


lemma sum_cinner:
  fixes f :: "'a \<Rightarrow> 'b::complex_inner"
  shows "cinner (sum f A) (sum g B) = (\<Sum>i\<in>A. \<Sum>j\<in>B. cinner (f i) (g j))"
  by (simp add: cinner_sum_right cinner_sum_left) (rule sum.swap)

lemma Cauchy_cinner_product_summable':
  fixes a b :: "nat \<Rightarrow> 'a::complex_inner"
  shows \<open>(\<lambda>(x, y). cinner (a x) (b y)) summable_on UNIV \<longleftrightarrow> (\<lambda>(x, y). cinner (a y) (b (x - y))) summable_on {(k, i). i \<le> k}\<close>
proof -
  have img: \<open>(\<lambda>(k::nat, i). (i, k - i)) ` {(k, i). i \<le> k} = UNIV\<close>
    apply (auto simp: image_def)
    by (metis add.commute add_diff_cancel_right' diff_le_self)
  have inj: \<open>inj_on (\<lambda>(k::nat, i). (i, k - i)) {(k, i). i \<le> k}\<close>
    by (smt (verit, del_insts) Pair_inject case_prodE case_prod_conv eq_diff_iff inj_onI mem_Collect_eq)

  have \<open>(\<lambda>(x, y). cinner (a x) (b y)) summable_on UNIV \<longleftrightarrow> (\<lambda>(k, l). cinner (a k) (b l)) summable_on (\<lambda>(k, i). (i, k - i)) ` {(k, i). i \<le> k}\<close>
    by (simp only: img)
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>(k, l). cinner (a k) (b l)) \<circ> (\<lambda>(k, i). (i, k - i))) summable_on {(k, i). i \<le> k}\<close>
    using inj by (rule summable_on_reindex)
  also have \<open>\<dots> \<longleftrightarrow> (\<lambda>(x, y). cinner (a y) (b (x - y))) summable_on {(k, i). i \<le> k}\<close>
    by (simp add: o_def case_prod_unfold)
  finally show ?thesis
    by -
qed

instantiation prod :: (complex_inner, complex_inner) complex_inner
begin

definition cinner_prod_def:
  "cinner x y = cinner (fst x) (fst y) + cinner (snd x) (snd y)"

instance
proof
  fix r :: complex
  fix x y z :: "'a::complex_inner \<times> 'b::complex_inner"
  show "cinner x y = cnj (cinner y x)"
    unfolding cinner_prod_def
    by simp
  show "cinner (x + y) z = cinner x z + cinner y z"
    unfolding cinner_prod_def
    by (simp add: cinner_add_left)
  show "cinner (scaleC r x) y = cnj r * cinner x y"
    unfolding cinner_prod_def
    by (simp add: distrib_left)
  show "0 \<le> cinner x x"
    unfolding cinner_prod_def
    by (intro add_nonneg_nonneg cinner_ge_zero)
  show "cinner x x = 0 \<longleftrightarrow> x = 0"
    unfolding cinner_prod_def prod_eq_iff
    by (metis antisym cinner_eq_zero_iff cinner_ge_zero fst_zero le_add_same_cancel2 snd_zero verit_sum_simplify)
  show "norm x = sqrt (cmod (cinner x x))"
    unfolding norm_prod_def cinner_prod_def
    by (metis (no_types, lifting) Re_complex_of_real add_nonneg_nonneg cinner_ge_zero complex_of_real_cmod plus_complex.simps(1) power2_norm_eq_cinner')
qed

end

lemma sgn_cinner[simp]: \<open>sgn \<psi> \<bullet>\<^sub>C \<psi> = norm \<psi>\<close>
  apply (cases \<open>\<psi> = 0\<close>)
   apply (auto simp: sgn_div_norm)
  by (smt (verit, ccfv_SIG) cinner_scaleR_left cinner_scaleR_right cnorm_eq cnorm_eq_1 complex_of_real_cmod complex_of_real_nn_iff left_inverse mult.right_neutral mult_scaleR_right norm_eq_zero norm_not_less_zero norm_one of_real_def of_real_eq_iff)

instance prod :: (chilbert_space, chilbert_space) chilbert_space..

subsection \<open>Orthogonality\<close>

definition "orthogonal_complement S = {x| x. \<forall>y\<in>S. cinner x y = 0}"

lemma orthogonal_complement_orthoI:
  \<open>x \<in> orthogonal_complement M \<Longrightarrow> y \<in> M \<Longrightarrow> x \<bullet>\<^sub>C y = 0\<close>
  unfolding orthogonal_complement_def by auto

lemma orthogonal_complement_orthoI':
  \<open>x \<in> M \<Longrightarrow> y \<in> orthogonal_complement M \<Longrightarrow> x \<bullet>\<^sub>C y = 0\<close>
  by (metis cinner_commute' complex_cnj_zero orthogonal_complement_orthoI)

lemma orthogonal_complementI:
  \<open>(\<And>x. x \<in> M \<Longrightarrow> y \<bullet>\<^sub>C x = 0) \<Longrightarrow> y \<in> orthogonal_complement M\<close>
  unfolding orthogonal_complement_def
  by simp

abbreviation is_orthogonal::\<open>'a::complex_inner \<Rightarrow> 'a \<Rightarrow> bool\<close>  where
  \<open>is_orthogonal x y \<equiv> x \<bullet>\<^sub>C y = 0\<close>

bundle orthogonal_notation begin
notation is_orthogonal (infixl "\<bottom>" 69)
end

bundle no_orthogonal_notation begin
no_notation is_orthogonal (infixl "\<bottom>" 69)
end


lemma is_orthogonal_sym: "is_orthogonal \<psi> \<phi> = is_orthogonal \<phi> \<psi>"
  by (metis cinner_commute' complex_cnj_zero)

lemma is_orthogonal_sgn_right[simp]: \<open>is_orthogonal e (sgn f) \<longleftrightarrow> is_orthogonal e f\<close>
proof (cases \<open>f = 0\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  have \<open>cinner e (sgn f) = cinner e f / norm f\<close>
    by (simp add: sgn_div_norm divide_inverse scaleR_scaleC)
  moreover have \<open>norm f \<noteq> 0\<close>
    by (simp add: False)
  ultimately show ?thesis
    by force
qed

lemma is_orthogonal_sgn_left[simp]: \<open>is_orthogonal (sgn e) f \<longleftrightarrow> is_orthogonal e f\<close>
  by (simp add: is_orthogonal_sym)

lemma orthogonal_complement_closed_subspace[simp]:
  "closed_csubspace (orthogonal_complement A)"
  for A :: \<open>('a::complex_inner) set\<close>
proof (intro closed_csubspace.intro complex_vector.subspaceI)
  fix x y and c
  show \<open>0 \<in> orthogonal_complement A\<close>
    by (rule orthogonal_complementI, simp)
  show \<open>x + y \<in> orthogonal_complement A\<close>
    if \<open>x \<in> orthogonal_complement A\<close> and \<open>y \<in> orthogonal_complement A\<close>
    using that by (auto intro!: orthogonal_complementI dest!: orthogonal_complement_orthoI
        simp add: cinner_add_left)
  show \<open>c *\<^sub>C x \<in> orthogonal_complement A\<close> if \<open>x \<in> orthogonal_complement A\<close>
    using that by (auto intro!: orthogonal_complementI dest!: orthogonal_complement_orthoI)

  show "closed (orthogonal_complement A)"
  proof (auto simp add: closed_sequential_limits, rename_tac an a)
    fix an a
    assume ortho: \<open>\<forall>n::nat. an n \<in> orthogonal_complement A\<close>
    assume lim: \<open>an \<longlonglongrightarrow> a\<close>

    have \<open>\<forall> y \<in> A. \<forall> n. is_orthogonal y (an n)\<close>
      using orthogonal_complement_orthoI'
      by (simp add: orthogonal_complement_orthoI' ortho)
    moreover have \<open>isCont (\<lambda> x. y \<bullet>\<^sub>C x) a\<close> for y
      using bounded_clinear_cinner_right clinear_continuous_at
      by (simp add: clinear_continuous_at bounded_clinear_cinner_right)
    ultimately have \<open>(\<lambda> n. (\<lambda> v. y \<bullet>\<^sub>C v) (an n)) \<longlonglongrightarrow> (\<lambda> v. y \<bullet>\<^sub>C v) a\<close> for y
      using isCont_tendsto_compose
      by (simp add: isCont_tendsto_compose lim)
    hence  \<open>\<forall> y\<in>A. (\<lambda> n. y \<bullet>\<^sub>C an n) \<longlonglongrightarrow>  y \<bullet>\<^sub>C a\<close>
      by simp
    hence  \<open>\<forall> y\<in>A. (\<lambda> n. 0) \<longlonglongrightarrow>  y \<bullet>\<^sub>C a\<close>
      using \<open>\<forall> y \<in> A. \<forall> n. is_orthogonal y (an n)\<close>
      by fastforce
    hence  \<open>\<forall> y \<in> A. is_orthogonal y a\<close>
      using limI by fastforce
    then show \<open>a \<in> orthogonal_complement A\<close>
      by (simp add: orthogonal_complementI is_orthogonal_sym)
  qed
qed

lemma orthogonal_complement_zero_intersection:
  assumes "0\<in>M"
  shows \<open>M \<inter> (orthogonal_complement M) = {0}\<close>
proof -
  have "x=0" if "x\<in>M" and "x\<in>orthogonal_complement M" for x
  proof -
    from that have "is_orthogonal x x"
      unfolding orthogonal_complement_def by auto
    thus "x=0"
      by auto
  qed
  with assms show ?thesis
    unfolding orthogonal_complement_def by auto
qed

lemma is_orthogonal_closure_cspan:
  assumes "\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> is_orthogonal x y"
  assumes \<open>x \<in> closure (cspan X)\<close> \<open>y \<in> closure (cspan Y)\<close>
  shows "is_orthogonal x y"
proof -
  have *: \<open>cinner x y = 0\<close> if \<open>y \<in> Y\<close> for y
    using bounded_antilinear_cinner_left apply (rule bounded_antilinear_eq_on[where G=X])
    using assms that by auto
  show \<open>cinner x y = 0\<close>
    using bounded_clinear_cinner_right apply (rule bounded_clinear_eq_on_closure[where G=Y])
    using * assms by auto
qed


instantiation ccsubspace :: (complex_inner) "uminus"
begin
lift_definition uminus_ccsubspace::\<open>'a ccsubspace  \<Rightarrow> 'a ccsubspace\<close>
  is \<open>orthogonal_complement\<close>
  by simp

instance ..
end

lemma orthocomplement_top[simp]: \<open>- top = (bot :: 'a::complex_inner ccsubspace)\<close>
  \<comment> \<open>For \<^typ>\<open>'a\<close> of sort \<^class>\<open>chilbert_space\<close>, this is covered by @{thm [source] orthocomplemented_lattice_class.compl_top_eq} already.
      But here we give it a wider sort.\<close>
  apply transfer
  by (metis Int_UNIV_left UNIV_I orthogonal_complement_zero_intersection)

instantiation ccsubspace :: (complex_inner) minus begin
lift_definition minus_ccsubspace :: "'a ccsubspace \<Rightarrow> 'a ccsubspace \<Rightarrow> 'a ccsubspace"
  is "\<lambda>A B. A \<inter> (orthogonal_complement B)"
  by simp
instance..
end

definition is_ortho_set :: "'a::complex_inner set \<Rightarrow> bool" where
  \<comment> \<open>Orthogonal set\<close>
  \<open>is_ortho_set S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. x \<noteq> y \<longrightarrow> (x \<bullet>\<^sub>C y) = 0) \<and> 0 \<notin> S\<close>

definition is_onb where \<open>is_onb E \<longleftrightarrow> is_ortho_set E \<and> (\<forall>b\<in>E. norm b = 1) \<and> ccspan E = top\<close>

lemma is_ortho_set_empty[simp]: "is_ortho_set {}"
  unfolding is_ortho_set_def by auto

lemma is_ortho_set_antimono: \<open>A \<subseteq> B \<Longrightarrow> is_ortho_set B \<Longrightarrow> is_ortho_set A\<close>
  unfolding is_ortho_set_def by auto

lemma orthogonal_complement_of_closure:
  fixes A ::"('a::complex_inner) set"
  shows "orthogonal_complement A = orthogonal_complement (closure A)"
proof-
  have s1: \<open>is_orthogonal y x\<close>
    if a1: "x \<in> (orthogonal_complement A)"
      and a2: \<open>y \<in> closure A\<close>
    for x y
  proof-
    have \<open>\<forall> y \<in> A. is_orthogonal y x\<close>
      by (simp add: a1 orthogonal_complement_orthoI')
    then obtain yy where \<open>\<forall> n. yy n \<in> A\<close> and \<open>yy \<longlonglongrightarrow> y\<close>
      using a2 closure_sequential by blast
    have \<open>isCont (\<lambda> t. t \<bullet>\<^sub>C x) y\<close>
      by simp
    hence \<open>(\<lambda> n. yy n \<bullet>\<^sub>C x) \<longlonglongrightarrow> y \<bullet>\<^sub>C x\<close>
      using \<open>yy \<longlonglongrightarrow> y\<close> isCont_tendsto_compose
      by fastforce
    hence \<open>(\<lambda> n. 0) \<longlonglongrightarrow> y \<bullet>\<^sub>C x\<close>
      using \<open>\<forall> y \<in> A. is_orthogonal y x\<close>  \<open>\<forall> n. yy n \<in> A\<close> by simp
    thus ?thesis
      using limI by force
  qed
  hence "x \<in> orthogonal_complement (closure A)"
    if a1: "x \<in> (orthogonal_complement A)"
    for x
    using that
    by (meson orthogonal_complementI is_orthogonal_sym)
  moreover have \<open>x \<in> (orthogonal_complement A)\<close>
    if "x \<in> (orthogonal_complement (closure A))"
    for x
    using that
    by (meson closure_subset orthogonal_complement_orthoI orthogonal_complementI subset_eq)
  ultimately show ?thesis by blast
qed


lemma is_orthogonal_closure:
  assumes \<open>\<And>s. s \<in> S \<Longrightarrow> is_orthogonal a  s\<close>
  assumes \<open>x \<in> closure S\<close>
  shows \<open>is_orthogonal a x\<close>
  by (metis assms(1) assms(2) orthogonal_complementI orthogonal_complement_of_closure orthogonal_complement_orthoI)


lemma is_orthogonal_cspan:
  assumes a1: "\<And>s. s \<in> S \<Longrightarrow> is_orthogonal a s" and a3: "x \<in> cspan S"
  shows "is_orthogonal a x"
proof-
  have "\<exists>t r. finite t \<and> t \<subseteq> S \<and> (\<Sum>a\<in>t. r a *\<^sub>C a) = x"
    using complex_vector.span_explicit
    by (smt a3 mem_Collect_eq)
  then obtain t r where b1: "finite t" and b2: "t \<subseteq> S" and b3: "(\<Sum>a\<in>t. r a *\<^sub>C a) = x"
    by blast
  have x1: "is_orthogonal a i"
    if "i\<in>t" for i
    using b2 a1 that by blast
  have  "a \<bullet>\<^sub>C x = a \<bullet>\<^sub>C (\<Sum>i\<in>t. r i *\<^sub>C i)"
    by (simp add: b3)
  also have  "\<dots> = (\<Sum>i\<in>t. r i *\<^sub>C (a \<bullet>\<^sub>C i))"
    by (simp add: cinner_sum_right)
  also have  "\<dots> = 0"
    using x1 by simp
  finally show ?thesis.
qed

lemma ccspan_leq_ortho_ccspan:
  assumes "\<And>s t. s\<in>S \<Longrightarrow> t\<in>T \<Longrightarrow> is_orthogonal s t"
  shows "ccspan S \<le> - (ccspan T)"
  using assms apply transfer
  by (smt (verit, ccfv_threshold) is_orthogonal_closure is_orthogonal_cspan is_orthogonal_sym orthogonal_complementI subsetI)

lemma double_orthogonal_complement_increasing[simp]:
  shows "M \<subseteq> orthogonal_complement (orthogonal_complement M)"
proof (rule subsetI)
  fix x assume s1: "x \<in> M"
  have \<open>\<forall> y \<in> (orthogonal_complement M). is_orthogonal x y\<close>
    using s1 orthogonal_complement_orthoI' by auto
  hence \<open>x \<in> orthogonal_complement (orthogonal_complement M)\<close>
    by (simp add: orthogonal_complement_def)
  then show "x \<in> orthogonal_complement (orthogonal_complement M)"
    by blast
qed


lemma orthonormal_basis_of_cspan:
  fixes S::"'a::complex_inner set"
  assumes "finite S"
  shows "\<exists>A. is_ortho_set A \<and> (\<forall>x\<in>A. norm x = 1) \<and> cspan A = cspan S \<and> finite A"
proof (use assms in induction)
  case empty
  show ?case
    apply (rule exI[of _ "{}"])
    by auto
next
  case (insert s S)
  from insert.IH
  obtain A where orthoA: "is_ortho_set A" and normA: "\<And>x. x\<in>A \<Longrightarrow> norm x = 1" and spanA: "cspan A = cspan S" and finiteA: "finite A"
    by auto
  show ?case
  proof (cases \<open>s \<in> cspan S\<close>)
    case True
    then have \<open>cspan (insert s S) = cspan S\<close>
      by (simp add: complex_vector.span_redundant)
    with orthoA normA spanA finiteA
    show ?thesis
      by auto
  next
    case False
    obtain a where a_ortho: \<open>\<And>x. x\<in>A \<Longrightarrow> is_orthogonal x a\<close> and sa_span: \<open>s - a \<in> cspan A\<close>
    proof (atomize_elim, use \<open>finite A\<close> \<open>is_ortho_set A\<close> in induction)
      case empty
      then show ?case
        by auto
    next
      case (insert x A)
      then obtain a where orthoA: \<open>\<And>x. x \<in> A \<Longrightarrow> is_orthogonal x a\<close> and sa: \<open>s - a \<in> cspan A\<close>
        by (meson is_ortho_set_antimono subset_insertI)
      define a' where \<open>a' = a - cinner x a *\<^sub>C inverse (cinner x x) *\<^sub>C x\<close>
      have \<open>is_orthogonal x a'\<close>
        unfolding a'_def cinner_diff_right cinner_scaleC_right
        apply (cases \<open>cinner x x = 0\<close>)
        by auto
      have orthoA: \<open>is_orthogonal y a'\<close> if \<open>y \<in> A\<close> for y
        unfolding a'_def cinner_diff_right cinner_scaleC_right
        apply auto by (metis insert.prems insertCI is_ortho_set_def mult_not_zero orthoA that)
      have \<open>s - a' \<in> cspan (insert x A)\<close>
        unfolding a'_def apply auto
        by (metis (no_types, lifting) complex_vector.span_breakdown_eq diff_add_cancel diff_diff_add sa)
      with \<open>is_orthogonal x a'\<close> orthoA
      show ?case
        apply (rule_tac exI[of _ a'])
        by auto
    qed

    from False sa_span
    have \<open>a \<noteq> 0\<close>
      unfolding spanA by auto
    define a' where \<open>a' = inverse (norm a) *\<^sub>C a\<close>
    with \<open>a \<noteq> 0\<close> have \<open>norm a' = 1\<close>
      by (simp add: norm_inverse)
    have a: \<open>a = norm a *\<^sub>C a'\<close>
      by (simp add: \<open>a \<noteq> 0\<close> a'_def)

    from sa_span spanA
    have a'_span: \<open>a' \<in> cspan (insert s S)\<close>
      unfolding a'_def
      by (metis complex_vector.eq_span_insert_eq complex_vector.span_scale complex_vector.span_superset in_mono insertI1)
    from sa_span
    have s_span: \<open>s \<in> cspan (insert a' A)\<close>
      apply (subst (asm) a)
      using complex_vector.span_breakdown_eq by blast

    from \<open>a \<noteq> 0\<close> a_ortho orthoA
    have ortho: "is_ortho_set (insert a' A)"
      unfolding is_ortho_set_def a'_def
      apply auto
      by (meson is_orthogonal_sym)

    have span: \<open>cspan (insert a' A) = cspan (insert s S)\<close>
      using a'_span s_span spanA apply auto
       apply (metis (full_types) complex_vector.span_breakdown_eq complex_vector.span_redundant insert_commute s_span)
      by (metis (full_types) complex_vector.span_breakdown_eq complex_vector.span_redundant insert_commute s_span)

    show ?thesis
      apply (rule exI[of _ \<open>insert a' A\<close>])
      by (simp add: ortho \<open>norm a' = 1\<close> normA finiteA span)
  qed
qed

lemma is_ortho_set_cindependent:
  assumes "is_ortho_set A"
  shows "cindependent A"
proof -
  have "u v = 0"
    if b1: "finite t" and b2: "t \<subseteq> A" and b3: "(\<Sum>v\<in>t. u v *\<^sub>C v) = 0" and b4: "v \<in> t"
    for t u v
  proof -
    have "is_orthogonal v v'" if c1: "v'\<in>t-{v}" for v'
      by (metis DiffE assms b2 b4 insertI1 is_ortho_set_antimono is_ortho_set_def that)
    hence sum0: "(\<Sum>v'\<in>t-{v}. u v' * (v \<bullet>\<^sub>C v')) = 0"
      by simp
    have "v \<bullet>\<^sub>C (\<Sum>v'\<in>t. u v' *\<^sub>C v') = (\<Sum>v'\<in>t. u v' * (v \<bullet>\<^sub>C v'))"
      using b1
      by (metis (mono_tags, lifting) cinner_scaleC_right cinner_sum_right sum.cong)
    also have "\<dots> = u v * (v \<bullet>\<^sub>C v) + (\<Sum>v'\<in>t-{v}. u v' * (v \<bullet>\<^sub>C v'))"
      by (meson b1 b4 sum.remove)
    also have "\<dots> = u v * (v \<bullet>\<^sub>C v)"
      using sum0 by simp
    finally have "v \<bullet>\<^sub>C (\<Sum>v'\<in>t. u v' *\<^sub>C v') =  u v * (v \<bullet>\<^sub>C v)"
      by blast
    hence "u v * (v \<bullet>\<^sub>C v) = 0" using b3 by simp
    moreover have "(v \<bullet>\<^sub>C v) \<noteq> 0"
      using assms is_ortho_set_def b2 b4 by auto
    ultimately show "u v = 0" by simp
  qed
  thus ?thesis using complex_vector.independent_explicit_module
    by (smt cdependent_raw_def)
qed


lemma onb_expansion_finite:
  includes notation_norm
  fixes T::\<open>'a::{complex_inner,cfinite_dim} set\<close>
  assumes a1: \<open>cspan T = UNIV\<close> and a3: \<open>is_ortho_set T\<close>
    and a4: \<open>\<And>t. t\<in>T \<Longrightarrow> \<parallel>t\<parallel> = 1\<close>
  shows \<open>x = (\<Sum>t\<in>T. (t \<bullet>\<^sub>C x) *\<^sub>C t)\<close>
proof -
  have \<open>finite T\<close>
    apply (rule cindependent_cfinite_dim_finite)
    by (simp add: a3 is_ortho_set_cindependent)
  have \<open>closure (complex_vector.span T)  = complex_vector.span T\<close>
    by (simp add: a1)
  have \<open>{\<Sum>a\<in>t. r a *\<^sub>C a |t r. finite t \<and> t \<subseteq> T} = {\<Sum>a\<in>T. r a *\<^sub>C a |r. True}\<close>
    apply auto
     apply (rule_tac x=\<open>\<lambda>a. if a \<in> t then r a else 0\<close> in exI)
     apply (simp add: \<open>finite T\<close> sum.mono_neutral_cong_right)
    using \<open>finite T\<close> by blast

  have f1: "\<forall>A. {a. \<exists>Aa f. (a::'a) = (\<Sum>a\<in>Aa. f a *\<^sub>C a) \<and> finite Aa \<and> Aa \<subseteq> A} = cspan A"
    by (simp add: complex_vector.span_explicit)
  have f2: "\<forall>a. (\<exists>f. a = (\<Sum>a\<in>T. f a *\<^sub>C a)) \<or> (\<forall>A. (\<forall>f. a \<noteq> (\<Sum>a\<in>A. f a *\<^sub>C a)) \<or> infinite A \<or> \<not> A \<subseteq> T)"
    using \<open>{\<Sum>a\<in>t. r a *\<^sub>C a |t r. finite t \<and> t \<subseteq> T} = {\<Sum>a\<in>T. r a *\<^sub>C a |r. True}\<close> by auto
  have f3: "\<forall>A a. (\<exists>Aa f. (a::'a) = (\<Sum>a\<in>Aa. f a *\<^sub>C a) \<and> finite Aa \<and> Aa \<subseteq> A) \<or> a \<notin> cspan A"
    using f1 by blast
  have "cspan T = UNIV"
    by (metis (full_types, lifting)  \<open>complex_vector.span T = UNIV\<close>)
  hence \<open>\<exists> r. x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
    using f3 f2 by blast
  then obtain r where \<open>x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
    by blast

  have \<open>r a = a \<bullet>\<^sub>C x\<close> if \<open>a \<in> T\<close> for a
  proof-
    have \<open>norm a = 1\<close>
      using a4
      by (simp add: \<open>a \<in> T\<close>)
    moreover have \<open>norm a = sqrt (norm (a \<bullet>\<^sub>C a))\<close>
      using norm_eq_sqrt_cinner by auto
    ultimately have \<open>sqrt (norm (a \<bullet>\<^sub>C a)) = 1\<close>
      by simp
    hence \<open>norm (a \<bullet>\<^sub>C a) = 1\<close>
      using real_sqrt_eq_1_iff by blast
    moreover have \<open>(a \<bullet>\<^sub>C a) \<in> \<real>\<close>
      by (simp add: cinner_real)
    moreover have \<open>(a \<bullet>\<^sub>C a) \<ge> 0\<close>
      using cinner_ge_zero by blast
    ultimately have w1: \<open>(a \<bullet>\<^sub>C a) = 1\<close>
      by (metis \<open>0 \<le> (a \<bullet>\<^sub>C a)\<close> \<open>cmod (a \<bullet>\<^sub>C a) = 1\<close> complex_of_real_cmod of_real_1)

    have \<open>r t * (a \<bullet>\<^sub>C t) = 0\<close> if \<open>t \<in> T-{a}\<close> for t
      by (metis DiffD1 DiffD2 \<open>a \<in> T\<close> a3 is_ortho_set_def mult_eq_0_iff singletonI that)
    hence s1: \<open>(\<Sum> t\<in>T-{a}. r t * (a \<bullet>\<^sub>C t)) = 0\<close>
      by (simp add: \<open>\<And>t. t \<in> T - {a} \<Longrightarrow> r t * (a \<bullet>\<^sub>C t) = 0\<close>)
    have \<open>(a \<bullet>\<^sub>C x) = a \<bullet>\<^sub>C (\<Sum> t\<in>T. r t *\<^sub>C t)\<close>
      using \<open>x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
      by simp
    also have \<open>\<dots> = (\<Sum> t\<in>T. a \<bullet>\<^sub>C (r t *\<^sub>C t))\<close>
      using cinner_sum_right by blast
    also have \<open>\<dots> = (\<Sum> t\<in>T. r t * (a \<bullet>\<^sub>C t))\<close>
      by simp
    also have \<open>\<dots> = r a * (a \<bullet>\<^sub>C a) + (\<Sum> t\<in>T-{a}. r t * (a \<bullet>\<^sub>C t))\<close>
      using \<open>a \<in> T\<close>
      by (meson \<open>finite T\<close> sum.remove)
    also have \<open>\<dots> = r a * (a \<bullet>\<^sub>C a)\<close>
      using s1
      by simp
    also have \<open>\<dots> = r a\<close>
      by (simp add: w1)
    finally show ?thesis by auto
  qed
  thus ?thesis
    using \<open>x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
    by fastforce
qed

lemma is_ortho_set_singleton[simp]: \<open>is_ortho_set {x} \<longleftrightarrow> x \<noteq> 0\<close>
  by (simp add: is_ortho_set_def)

lemma orthogonal_complement_antimono[simp]:
  fixes  A B :: \<open>('a::complex_inner) set\<close>
  assumes "A \<supseteq> B"
  shows \<open>orthogonal_complement A \<subseteq> orthogonal_complement B\<close>
  by (meson assms orthogonal_complementI orthogonal_complement_orthoI' subsetD subsetI)

lemma orthogonal_complement_UNIV[simp]:
  "orthogonal_complement UNIV = {0}"
  by (metis Int_UNIV_left complex_vector.subspace_UNIV complex_vector.subspace_def orthogonal_complement_zero_intersection)

lemma orthogonal_complement_zero[simp]:
  "orthogonal_complement {0} = UNIV"
  unfolding orthogonal_complement_def by auto

lemma mem_ortho_ccspanI:
  assumes \<open>\<And>y. y \<in> S \<Longrightarrow> is_orthogonal x y\<close>
  shows \<open>x \<in> space_as_set (- ccspan S)\<close>
proof -
  have \<open>x \<in> space_as_set (ccspan {x})\<close>
    using ccspan_superset by blast
  also have \<open>\<dots> \<subseteq> space_as_set (- ccspan S)\<close>
    apply (simp add: flip: less_eq_ccsubspace.rep_eq)
    apply (rule ccspan_leq_ortho_ccspan)
    using assms by auto
  finally show ?thesis
    by -
qed


subsection \<open>Projections\<close>

lemma smallest_norm_exists:
  \<comment> \<open>Theorem 2.5 in \<^cite>\<open>conway2013course\<close> (inside the proof)\<close>
  includes notation_norm
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes q1: \<open>convex M\<close> and q2: \<open>closed M\<close> and q3: \<open>M \<noteq> {}\<close>
  shows  \<open>\<exists>k. is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) k\<close>
proof -
  define d where \<open>d = Inf { \<parallel>x\<parallel>^2 | x. x \<in> M }\<close>
  have w4: \<open>{ \<parallel>x\<parallel>^2 | x. x \<in> M } \<noteq> {}\<close>
    by (simp add: assms(3))
  have \<open>\<forall> x. \<parallel>x\<parallel>^2 \<ge> 0\<close>
    by simp
  hence bdd_below1: \<open>bdd_below { \<parallel>x\<parallel>^2 | x. x \<in> M }\<close>
    by fastforce
  have \<open>d \<le> \<parallel>x\<parallel>^2\<close> if a1: "x \<in> M" for x
  proof-
    have "\<forall>v. (\<exists>w. Re (v \<bullet>\<^sub>C v) = \<parallel>w\<parallel>\<^sup>2 \<and> w \<in> M) \<or> v \<notin> M"
      by (metis (no_types) power2_norm_eq_cinner')
    hence "Re (x \<bullet>\<^sub>C x) \<in> {\<parallel>v\<parallel>\<^sup>2 |v. v \<in> M}"
      using a1 by blast
    thus ?thesis
      unfolding d_def
      by (metis (lifting) bdd_below1 cInf_lower power2_norm_eq_cinner')
  qed

  have \<open>\<forall> \<epsilon> > 0. \<exists> t \<in> { \<parallel>x\<parallel>^2 | x. x \<in> M }.  t < d + \<epsilon>\<close>
    unfolding d_def
    using w4  bdd_below1
    by (meson cInf_lessD less_add_same_cancel1)
  hence \<open>\<forall> \<epsilon> > 0. \<exists> x \<in> M.  \<parallel>x\<parallel>^2 < d + \<epsilon>\<close>
    by auto
  hence \<open>\<forall> \<epsilon> > 0. \<exists> x \<in> M.  \<parallel>x\<parallel>^2 < d + \<epsilon>\<close>
    by (simp add: \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> \<parallel>x\<parallel>\<^sup>2\<close>)
  hence w1: \<open>\<forall> n::nat. \<exists> x \<in> M.  \<parallel>x\<parallel>^2 < d + 1/(n+1)\<close> by auto

  then obtain r::\<open>nat \<Rightarrow> 'a\<close> where w2: \<open>\<forall> n. r n \<in> M \<and>  \<parallel> r n \<parallel>^2 < d + 1/(n+1)\<close>
    by metis
  have w3: \<open>\<forall> n. r n \<in> M\<close>
    by (simp add: w2)
  have \<open>\<forall> n. \<parallel> r n \<parallel>^2 < d + 1/(n+1)\<close>
    by (simp add: w2)
  have w5: \<open>\<parallel> (r n) - (r m) \<parallel>^2 < 2*(1/(n+1) + 1/(m+1))\<close>
    for m n
  proof-
    have w6: \<open>\<parallel> r n \<parallel>^2 < d + 1/(n+1)\<close>
      by (metis w2  of_nat_1 of_nat_add)
    have \<open> \<parallel> r m \<parallel>^2 < d + 1/(m+1)\<close>
      by (metis w2 of_nat_1 of_nat_add)
    have \<open>(r n) \<in> M\<close>
      by (simp add: \<open>\<forall>n. r n \<in> M\<close>)
    moreover have \<open>(r m) \<in> M\<close>
      by (simp add: \<open>\<forall>n. r n \<in> M\<close>)
    ultimately have \<open>(1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<in> M\<close>
      using \<open>convex M\<close>
      by (simp add: convexD)
    hence \<open>\<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>^2 \<ge> d\<close>
      by (simp add: \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> \<parallel>x\<parallel>\<^sup>2\<close>)
    have \<open>\<parallel> (1/2) *\<^sub>R (r n) - (1/2) *\<^sub>R (r m) \<parallel>^2
              = (1/2)*( \<parallel> r n \<parallel>^2 + \<parallel> r m \<parallel>^2 ) - \<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>^2\<close>
      by (smt (z3) div_by_1 field_sum_of_halves nonzero_mult_div_cancel_left parallelogram_law polar_identity power2_norm_eq_cinner' scaleR_collapse times_divide_eq_left)
    also have  \<open>...
              < (1/2)*( d + 1/(n+1) + \<parallel> r m \<parallel>^2 ) - \<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>^2\<close>
      using \<open>\<parallel>r n\<parallel>\<^sup>2 < d + 1 / real (n + 1)\<close> by auto
    also have  \<open>...
              < (1/2)*( d + 1/(n+1) + d + 1/(m+1) ) - \<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>^2\<close>
      using \<open>\<parallel>r m\<parallel>\<^sup>2 < d + 1 / real (m + 1)\<close> by auto
    also have  \<open>...
              \<le> (1/2)*( d + 1/(n+1) + d + 1/(m+1) ) - d\<close>
      by (simp add: \<open>d \<le> \<parallel>(1 / 2) *\<^sub>R r n + (1 / 2) *\<^sub>R r m\<parallel>\<^sup>2\<close>)
    also have  \<open>...
              \<le> (1/2)*( 1/(n+1) + 1/(m+1) + 2*d ) - d\<close>
      by simp
    also have  \<open>...
              \<le> (1/2)*( 1/(n+1) + 1/(m+1) ) + (1/2)*(2*d) - d\<close>
      by (simp add: distrib_left)
    also have  \<open>...
              \<le> (1/2)*( 1/(n+1) + 1/(m+1) ) + d - d\<close>
      by simp
    also have  \<open>...
              \<le> (1/2)*( 1/(n+1) + 1/(m+1) )\<close>
      by simp
    finally have \<open> \<parallel>(1 / 2) *\<^sub>R r n - (1 / 2) *\<^sub>R r m\<parallel>\<^sup>2 < 1 / 2 * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
      by blast
    hence \<open> \<parallel>(1 / 2) *\<^sub>R (r n - r m) \<parallel>\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
      by (simp add: real_vector.scale_right_diff_distrib)
    hence \<open> ((1 / 2)*\<parallel> (r n - r m) \<parallel>)\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
      by simp
    hence \<open> (1 / 2)^2*(\<parallel> (r n - r m) \<parallel>)\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
      by (metis power_mult_distrib)
    hence \<open> (1 / 4) *(\<parallel> (r n - r m) \<parallel>)\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
      by (simp add: power_divide)
    hence \<open> \<parallel> (r n - r m) \<parallel>\<^sup>2 < 2 * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
      by simp
    thus ?thesis
      by (metis of_nat_1 of_nat_add)
  qed
  hence "\<exists> N. \<forall> n m. n \<ge> N \<and> m \<ge> N \<longrightarrow> \<parallel> (r n) - (r m) \<parallel>^2 < \<epsilon>^2"
    if "\<epsilon> > 0"
    for \<epsilon>
  proof-
    obtain N::nat where \<open>1/(N + 1) < \<epsilon>^2/4\<close>
      using LIMSEQ_ignore_initial_segment[OF lim_inverse_n', where k=1]
      by (metis Suc_eq_plus1 \<open>0 < \<epsilon>\<close> nat_approx_posE zero_less_divide_iff zero_less_numeral
          zero_less_power )
    hence \<open>4/(N + 1) < \<epsilon>^2\<close>
      by simp
    have "2*(1/(n+1) + 1/(m+1)) < \<epsilon>^2"
      if f1: "n \<ge> N" and f2: "m \<ge> N"
      for m n::nat
    proof-
      have \<open>1/(n+1) \<le> 1/(N+1)\<close>
        by (simp add: f1 linordered_field_class.frac_le)
      moreover have \<open>1/(m+1) \<le> 1/(N+1)\<close>
        by (simp add: f2 linordered_field_class.frac_le)
      ultimately have  \<open>2*(1/(n+1) + 1/(m+1)) \<le> 4/(N+1)\<close>
        by simp
      thus ?thesis using \<open>4/(N + 1) < \<epsilon>^2\<close>
        by linarith
    qed
    hence "\<parallel> (r n) - (r m) \<parallel>^2 < \<epsilon>^2"
      if y1: "n \<ge> N" and y2: "m \<ge> N"
      for m n::nat
      using that
      by (smt \<open>\<And>n m. \<parallel>r n - r m\<parallel>\<^sup>2 < 2 * (1 / (real n + 1) + 1 / (real m + 1))\<close> of_nat_1 of_nat_add)
    thus ?thesis
      by blast
  qed
  hence  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> n m::nat. n \<ge> N \<and> m \<ge> N \<longrightarrow> \<parallel> (r n) - (r m) \<parallel>^2 < \<epsilon>^2\<close>
    by blast
  hence  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> n m::nat. n \<ge> N \<and> m \<ge> N \<longrightarrow> \<parallel> (r n) - (r m) \<parallel> < \<epsilon>\<close>
    by (meson less_eq_real_def power_less_imp_less_base)
  hence \<open>Cauchy r\<close>
    using CauchyI by fastforce
  then obtain k where \<open>r \<longlonglongrightarrow> k\<close>
    using  convergent_eq_Cauchy by auto
  have \<open>k \<in> M\<close> using \<open>closed M\<close>
    using \<open>\<forall>n. r n \<in> M\<close> \<open>r \<longlonglongrightarrow> k\<close> closed_sequentially by auto
  have  \<open>(\<lambda> n.  \<parallel> r n \<parallel>^2) \<longlonglongrightarrow>  \<parallel> k \<parallel>^2\<close>
    by (simp add: \<open>r \<longlonglongrightarrow> k\<close> tendsto_norm tendsto_power)
  moreover  have  \<open>(\<lambda> n.  \<parallel> r n \<parallel>^2) \<longlonglongrightarrow>  d\<close>
  proof-
    have \<open>\<bar>\<parallel> r n \<parallel>^2 - d\<bar> < 1/(n+1)\<close> for n :: nat
      using \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> \<parallel>x\<parallel>\<^sup>2\<close> \<open>\<forall>n. r n \<in> M \<and> \<parallel>r n\<parallel>\<^sup>2 < d + 1 / (real n + 1)\<close> of_nat_1 of_nat_add
      by smt
    moreover have \<open>(\<lambda>n. 1 / real (n + 1)) \<longlonglongrightarrow> 0\<close>
      using  LIMSEQ_ignore_initial_segment[OF lim_inverse_n', where k=1] by blast
    ultimately have \<open>(\<lambda> n. \<bar>\<parallel> r n \<parallel>^2 - d\<bar> ) \<longlonglongrightarrow> 0\<close>
      by (simp add: LIMSEQ_norm_0)
    hence \<open>(\<lambda> n. \<parallel> r n \<parallel>^2 - d ) \<longlonglongrightarrow> 0\<close>
      by (simp add: tendsto_rabs_zero_iff)
    moreover have \<open>(\<lambda> n. d ) \<longlonglongrightarrow> d\<close>
      by simp
    ultimately have \<open>(\<lambda> n. (\<parallel> r n \<parallel>^2 - d)+d ) \<longlonglongrightarrow> 0+d\<close>
      using tendsto_add by fastforce
    thus ?thesis by simp
  qed
  ultimately have \<open>d = \<parallel> k \<parallel>^2\<close>
    using LIMSEQ_unique by auto
  hence \<open>t \<in> M \<Longrightarrow> \<parallel> k \<parallel>^2 \<le> \<parallel> t \<parallel>^2\<close> for t
    using \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> \<parallel>x\<parallel>\<^sup>2\<close> by auto
  hence q1: \<open>\<exists> k. is_arg_min (\<lambda> x. \<parallel>x\<parallel>^2) (\<lambda> t. t \<in> M) k\<close>
    using \<open>k \<in> M\<close>
      is_arg_min_def \<open>d = \<parallel>k\<parallel>\<^sup>2\<close>
    by smt
  thus \<open>\<exists> k. is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) k\<close>
    by (smt is_arg_min_def norm_ge_zero power2_eq_square power2_le_imp_le)
qed


lemma smallest_norm_unique:
  \<comment> \<open>Theorem 2.5 in \<^cite>\<open>conway2013course\<close> (inside the proof)\<close>
  includes notation_norm
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes q1: \<open>convex M\<close>
  assumes r: \<open>is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) r\<close>
  assumes s: \<open>is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) s\<close>
  shows \<open>r = s\<close>
proof -
  have \<open>r \<in> M\<close>
    using \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) r\<close>
    by (simp add: is_arg_min_def)
  moreover have \<open>s \<in> M\<close>
    using \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) s\<close>
    by (simp add: is_arg_min_def)
  ultimately have \<open>((1/2) *\<^sub>R r + (1/2) *\<^sub>R s) \<in> M\<close> using \<open>convex M\<close>
    by (simp add: convexD)
  hence \<open>\<parallel>r\<parallel> \<le> \<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>\<close>
    by (metis is_arg_min_linorder r)
  hence u2: \<open>\<parallel>r\<parallel>^2 \<le> \<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>^2\<close>
    using norm_ge_zero power_mono by blast

  have \<open>\<parallel>r\<parallel> \<le> \<parallel>s\<parallel>\<close>
    using r s is_arg_min_def
    by (metis is_arg_min_linorder)
  moreover have \<open>\<parallel>s\<parallel> \<le> \<parallel>r\<parallel>\<close>
    using r s is_arg_min_def
    by (metis is_arg_min_linorder)
  ultimately have u3: \<open>\<parallel>r\<parallel> = \<parallel>s\<parallel>\<close> by simp

  have \<open>\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>^2 \<le> 0\<close>
    using u2 u3 parallelogram_law
    by (smt (verit, ccfv_SIG) polar_identity_minus power2_norm_eq_cinner' scaleR_add_right scaleR_half_double)
  hence \<open>\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>^2 = 0\<close>
    by simp
  hence \<open>\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel> = 0\<close>
    by auto
  hence \<open>(1/2) *\<^sub>R r - (1/2) *\<^sub>R s = 0\<close>
    using norm_eq_zero by blast
  thus ?thesis by simp
qed

theorem smallest_dist_exists:
  \<comment> \<open>Theorem 2.5 in \<^cite>\<open>conway2013course\<close>\<close>
  fixes M::\<open>'a::chilbert_space set\<close> and h
  assumes a1: \<open>convex M\<close> and a2: \<open>closed M\<close> and a3: \<open>M \<noteq> {}\<close>
  shows  \<open>\<exists>k. is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k\<close>
proof -
  have *: "is_arg_min (\<lambda>x. dist x h) (\<lambda>x. x\<in>M) (k+h) \<longleftrightarrow> is_arg_min (\<lambda>x. norm x) (\<lambda>x. x\<in>(\<lambda>x. x-h) ` M) k" for k
    unfolding dist_norm is_arg_min_def apply auto using add_implies_diff by blast
  have \<open>\<exists>k. is_arg_min (\<lambda>x. dist x h) (\<lambda>x. x\<in>M) (k+h)\<close>
    apply (subst *)
    apply (rule smallest_norm_exists)
    using assms by (auto simp: closed_translation_subtract)
  then show \<open>\<exists>k. is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k\<close>
    by metis
qed

theorem smallest_dist_unique:
  \<comment> \<open>Theorem 2.5 in \<^cite>\<open>conway2013course\<close>\<close>
  fixes M::\<open>'a::complex_inner set\<close> and h
  assumes a1: \<open>convex M\<close>
  assumes \<open>is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) r\<close>
  assumes \<open>is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) s\<close>
  shows  \<open>r = s\<close>
proof-
  have *: "is_arg_min (\<lambda>x. dist x h) (\<lambda>x. x\<in>M) k \<longleftrightarrow> is_arg_min (\<lambda>x. norm x) (\<lambda>x. x\<in>(\<lambda>x. x-h) ` M) (k-h)" for k
    unfolding dist_norm is_arg_min_def by auto
  have \<open>r - h = s - h\<close>
    using _ assms(2,3)[unfolded *] apply (rule smallest_norm_unique)
    by (simp add: a1)
  thus \<open>r = s\<close>
    by auto
qed


\<comment> \<open>Theorem 2.6 in \<^cite>\<open>conway2013course\<close>\<close>
theorem smallest_dist_is_ortho:
  fixes M::\<open>'a::complex_inner set\<close> and h k::'a
  assumes b1: \<open>closed_csubspace M\<close>
  shows  \<open>(is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k) \<longleftrightarrow>
          h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
proof -
  include notation_norm
  have  \<open>csubspace M\<close>
    using \<open>closed_csubspace M\<close> unfolding closed_csubspace_def by blast
  have r1: \<open>2 * Re ((h - k) \<bullet>\<^sub>C f) \<le> \<parallel> f \<parallel>^2\<close>
    if "f \<in> M" and \<open>k \<in> M\<close> and \<open>is_arg_min (\<lambda>x. dist x h) (\<lambda> x. x \<in> M) k\<close>
    for f
  proof-
    have \<open>k + f \<in>  M\<close>
      using \<open>csubspace M\<close>
      by (simp add:complex_vector.subspace_add that)
    have "\<forall>f A a b. \<not> is_arg_min f (\<lambda> x. x \<in> A) (a::'a) \<or> (f a::real) \<le> f b \<or> b \<notin> A"
      by (metis (no_types) is_arg_min_linorder)
    hence "dist k h \<le> dist (f + k) h"
      by (metis \<open>is_arg_min (\<lambda>x. dist x h) (\<lambda> x. x \<in> M) k\<close> \<open>k + f \<in> M\<close> add.commute)
    hence \<open>dist h k \<le> dist  h (k + f)\<close>
      by (simp add: add.commute dist_commute)
    hence \<open>\<parallel> h - k \<parallel> \<le> \<parallel> h - (k + f) \<parallel>\<close>
      by (simp add: dist_norm)
    hence \<open>\<parallel> h - k \<parallel>^2 \<le> \<parallel> h - (k + f) \<parallel>^2\<close>
      by (simp add: power_mono)
    also have \<open>... \<le> \<parallel> (h - k) - f \<parallel>^2\<close>
      by (simp add: diff_diff_add)
    also have \<open>... \<le> \<parallel> (h - k) \<parallel>^2 + \<parallel> f \<parallel>^2 -  2 * Re ((h - k) \<bullet>\<^sub>C f)\<close>
      by (simp add: polar_identity_minus)
    finally have \<open>\<parallel> (h - k) \<parallel>^2 \<le> \<parallel> (h - k) \<parallel>^2 + \<parallel> f \<parallel>^2 -  2 * Re ((h - k) \<bullet>\<^sub>C f)\<close>
      by simp
    thus ?thesis by simp
  qed

  have q4: \<open>\<forall> c > 0.  2 * Re ((h - k) \<bullet>\<^sub>C f) \<le> c\<close>
    if  \<open>\<forall>c>0. 2 * Re ((h - k) \<bullet>\<^sub>C f) \<le> c * \<parallel>f\<parallel>\<^sup>2\<close>
    for f
  proof (cases \<open>\<parallel> f \<parallel>^2 > 0\<close>)
    case True
    hence \<open>\<forall> c > 0.  2 * Re (((h - k) \<bullet>\<^sub>C f)) \<le> (c/\<parallel> f \<parallel>^2)*\<parallel> f \<parallel>^2\<close>
      using that linordered_field_class.divide_pos_pos by blast
    thus ?thesis
      using True by auto
  next
    case False
    hence \<open>\<parallel> f \<parallel>^2 = 0\<close>
      by simp
    thus ?thesis
      by auto
  qed
  have q3: \<open>\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (((h - k) \<bullet>\<^sub>C f)) \<le> 0\<close>
    if a3: \<open>\<forall>f. f \<in> M \<longrightarrow> (\<forall>c>0. 2 * Re ((h - k) \<bullet>\<^sub>C f) \<le> c * \<parallel>f\<parallel>\<^sup>2)\<close>
      and a2: "f \<in>  M"
      and a1: "is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k"
    for f
  proof-
    have \<open>\<forall> c > 0.  2 * Re (((h - k) \<bullet>\<^sub>C f)) \<le> c*\<parallel> f \<parallel>^2\<close>
      by (simp add: that )
    thus ?thesis
      using q4 by smt
  qed
  have w2: "h - k \<in> orthogonal_complement M \<and> k \<in> M"
    if a1: "is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k"
  proof-
    have  \<open>k \<in> M\<close>
      using is_arg_min_def that by fastforce
    hence \<open>\<forall> f. f \<in>  M \<longrightarrow> 2 * Re (((h - k) \<bullet>\<^sub>C f)) \<le> \<parallel> f \<parallel>^2\<close>
      using r1
      by (simp add: that)
    have \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real.  2 * Re ((h - k) \<bullet>\<^sub>C (c *\<^sub>R f)) \<le> \<parallel> c *\<^sub>R f \<parallel>^2)\<close>
      using  assms scaleR_scaleC complex_vector.subspace_def \<open>csubspace M\<close>
      by (metis \<open>\<forall>f. f \<in> M \<longrightarrow> 2 * Re ((h - k) \<bullet>\<^sub>C f) \<le> \<parallel>f\<parallel>\<^sup>2\<close>)
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c * (2 * Re (((h - k) \<bullet>\<^sub>C f))) \<le> \<parallel> c *\<^sub>R f \<parallel>^2)\<close>
      by (metis Re_complex_of_real cinner_scaleC_right complex_add_cnj complex_cnj_complex_of_real
          complex_cnj_mult of_real_mult scaleR_scaleC semiring_normalization_rules(34))
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c * (2 * Re (((h - k) \<bullet>\<^sub>C f))) \<le> \<bar>c\<bar>^2*\<parallel> f \<parallel>^2)\<close>
      by (simp add: power_mult_distrib)
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c * (2 * Re (((h - k) \<bullet>\<^sub>C f))) \<le> c^2*\<parallel> f \<parallel>^2)\<close>
      by auto
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> c * (2 * Re (((h - k) \<bullet>\<^sub>C f))) \<le> c^2*\<parallel> f \<parallel>^2)\<close>
      by simp
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> c*(2 * Re (((h - k) \<bullet>\<^sub>C f))) \<le> c*(c*\<parallel> f \<parallel>^2))\<close>
      by (simp add: power2_eq_square)
    hence  q4: \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (((h - k) \<bullet>\<^sub>C f)) \<le> c*\<parallel> f \<parallel>^2)\<close>
      by simp
    have  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (((h - k) \<bullet>\<^sub>C f)) \<le> 0)\<close>
      using q3
      by (simp add: q4 that)
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> (2 * Re ((h - k) \<bullet>\<^sub>C (-1 *\<^sub>R f))) \<le> 0)\<close>
      using assms scaleR_scaleC complex_vector.subspace_def
      by (metis \<open>csubspace M\<close>)
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> -(2 * Re (((h - k) \<bullet>\<^sub>C f))) \<le> 0)\<close>
      by simp
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (((h - k) \<bullet>\<^sub>C f)) \<ge> 0)\<close>
      by simp
    hence \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (((h - k) \<bullet>\<^sub>C f)) = 0)\<close>
      using  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> (2 * Re (((h - k) \<bullet>\<^sub>C f))) \<le> 0)\<close>
      by fastforce

    have \<open>\<forall> f. f \<in>  M \<longrightarrow>
                 ((1::real) > 0 \<longrightarrow> 2 * Re (((h - k) \<bullet>\<^sub>C f)) = 0)\<close>
      using \<open>\<forall>f. f \<in>  M \<longrightarrow> (\<forall>c>0. 2 * Re (((h - k) \<bullet>\<^sub>C f) ) = 0)\<close> by blast
    hence \<open>\<forall> f. f \<in>  M \<longrightarrow> 2 * Re (((h - k) \<bullet>\<^sub>C f)) = 0\<close>
      by simp
    hence \<open>\<forall> f. f \<in>  M \<longrightarrow> Re (((h - k) \<bullet>\<^sub>C f)) = 0\<close>
      by simp
    have  \<open>\<forall> f. f \<in>  M \<longrightarrow> Re ((h - k) \<bullet>\<^sub>C ((Complex 0 (-1)) *\<^sub>C f)) = 0\<close>
      using assms  complex_vector.subspace_def \<open>csubspace M\<close>
      by (metis \<open>\<forall>f. f \<in> M \<longrightarrow> Re ((h - k) \<bullet>\<^sub>C f) = 0\<close>)
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> Re ( (Complex 0 (-1))*(((h - k) \<bullet>\<^sub>C f)) ) = 0\<close>
      by simp
    hence \<open>\<forall> f. f \<in>  M \<longrightarrow> Im (((h - k) \<bullet>\<^sub>C f)) = 0\<close>
      using Complex_eq_neg_1 Re_i_times cinner_scaleC_right complex_of_real_def by auto

    have \<open>\<forall> f. f \<in>  M \<longrightarrow> (((h - k) \<bullet>\<^sub>C f)) = 0\<close>
      using complex_eq_iff
      by (simp add: \<open>\<forall>f. f \<in> M \<longrightarrow> Im ((h - k) \<bullet>\<^sub>C f) = 0\<close> \<open>\<forall>f. f \<in> M \<longrightarrow> Re ((h - k) \<bullet>\<^sub>C f) = 0\<close>)
    hence \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
      by (simp add: \<open>k \<in> M\<close> orthogonal_complementI)
    have  \<open>\<forall> c. c *\<^sub>R f \<in> M\<close>
      if "f \<in> M"
      for f
      using that scaleR_scaleC  \<open>csubspace M\<close> complex_vector.subspace_def
      by (simp add: complex_vector.subspace_def scaleR_scaleC)
    have \<open>((h - k) \<bullet>\<^sub>C f) = 0\<close>
      if "f \<in> M"
      for f
      using \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close> orthogonal_complement_orthoI that by auto
    hence \<open>h - k \<in> orthogonal_complement M\<close>
      by (simp add: orthogonal_complement_def)
    thus ?thesis
      using \<open>k \<in> M\<close> by auto
  qed

  have q1: \<open>dist h k \<le> dist h f \<close>
    if "f \<in> M" and  \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
    for f
  proof-
    have \<open>(h - k) \<bullet>\<^sub>C (k - f) = 0\<close>
      by (metis (no_types, lifting) that
          cinner_diff_right diff_0_right orthogonal_complement_orthoI that)
    have \<open>\<parallel> h - f \<parallel>^2 = \<parallel> (h - k) + (k - f) \<parallel>^2\<close>
      by simp
    also have \<open>... = \<parallel> h - k \<parallel>^2 + \<parallel> k - f \<parallel>^2\<close>
      using  \<open>((h - k) \<bullet>\<^sub>C (k - f)) = 0\<close> pythagorean_theorem by blast
    also have \<open>... \<ge> \<parallel> h - k \<parallel>^2\<close>
      by simp
    finally have \<open>\<parallel>h - k\<parallel>\<^sup>2 \<le> \<parallel>h - f\<parallel>\<^sup>2 \<close>
      by blast
    hence \<open>\<parallel>h - k\<parallel> \<le> \<parallel>h - f\<parallel>\<close>
      using norm_ge_zero power2_le_imp_le by blast
    thus ?thesis
      by (simp add: dist_norm)
  qed

  have  w1: "is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k"
    if "h - k \<in> orthogonal_complement M \<and> k \<in>  M"
  proof-
    have \<open>h - k \<in> orthogonal_complement M\<close>
      using that by blast
    have \<open>k \<in> M\<close> using \<open>h - k \<in> orthogonal_complement M \<and> k \<in>  M\<close>
      by blast
    thus ?thesis
      by (metis (no_types, lifting) dist_commute is_arg_min_linorder q1 that)
  qed
  show ?thesis
    using w1 w2 by blast
qed

corollary orthog_proj_exists:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>closed_csubspace M\<close>
  shows  \<open>\<exists>k. h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
proof -
  from  \<open>closed_csubspace M\<close>
  have \<open>M \<noteq> {}\<close>
    using closed_csubspace.subspace complex_vector.subspace_0 by blast
  have \<open>closed  M\<close>
    using  \<open>closed_csubspace M\<close>
    by (simp add: closed_csubspace.closed)
  have \<open>convex  M\<close>
    using  \<open>closed_csubspace M\<close>
    by (simp)
  have \<open>\<exists>k.  is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k\<close>
    by (simp add: smallest_dist_exists \<open>closed M\<close> \<open>convex M\<close> \<open>M \<noteq> {}\<close>)
  thus ?thesis
    by (simp add: assms smallest_dist_is_ortho)
qed

corollary orthog_proj_unique:
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes \<open>closed_csubspace M\<close>
  assumes \<open>h - r \<in> orthogonal_complement M \<and> r \<in> M\<close>
  assumes \<open>h - s \<in> orthogonal_complement M \<and> s \<in> M\<close>
  shows  \<open>r = s\<close>
  using _ assms(2,3) unfolding smallest_dist_is_ortho[OF assms(1), symmetric]
  apply (rule smallest_dist_unique)
  using assms(1) by (simp)

definition is_projection_on::\<open>('a \<Rightarrow> 'a) \<Rightarrow> ('a::metric_space) set \<Rightarrow> bool\<close> where
  \<open>is_projection_on \<pi> M \<longleftrightarrow> (\<forall>h. is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) (\<pi> h))\<close>

lemma is_projection_on_iff_orthog:
  \<open>closed_csubspace M \<Longrightarrow> is_projection_on \<pi> M \<longleftrightarrow> (\<forall>h. h - \<pi> h \<in> orthogonal_complement M \<and> \<pi> h \<in> M)\<close>
  by (simp add: is_projection_on_def smallest_dist_is_ortho)

lemma is_projection_on_exists:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>convex M\<close> and \<open>closed M\<close> and \<open>M \<noteq> {}\<close>
  shows "\<exists>\<pi>. is_projection_on \<pi> M"
  unfolding is_projection_on_def apply (rule choice)
  using smallest_dist_exists[OF assms] by auto

lemma is_projection_on_unique:
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes \<open>convex M\<close>
  assumes "is_projection_on \<pi>\<^sub>1 M"
  assumes "is_projection_on \<pi>\<^sub>2 M"
  shows "\<pi>\<^sub>1 = \<pi>\<^sub>2"
  using smallest_dist_unique[OF assms(1)] using assms(2,3)
  unfolding is_projection_on_def by blast

definition projection :: \<open>'a::metric_space set \<Rightarrow> ('a \<Rightarrow> 'a)\<close> where
  \<open>projection M = (SOME \<pi>. is_projection_on \<pi> M)\<close>

lemma projection_is_projection_on:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>convex M\<close> and \<open>closed M\<close> and \<open>M \<noteq> {}\<close>
  shows "is_projection_on (projection M) M"
  by (metis assms(1) assms(2) assms(3) is_projection_on_exists projection_def someI)

lemma projection_is_projection_on'[simp]:
  \<comment> \<open>Common special case of @{thm projection_is_projection_on}\<close>
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>closed_csubspace M\<close>
  shows "is_projection_on (projection M) M"
  apply (rule projection_is_projection_on)
    apply (auto simp add: assms closed_csubspace.closed)
  using assms closed_csubspace.subspace complex_vector.subspace_0 by blast

lemma projection_orthogonal:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes "closed_csubspace M" and \<open>m \<in> M\<close>
  shows \<open>is_orthogonal (h - projection M h) m\<close>
  by (metis assms(1) assms(2) closed_csubspace.closed closed_csubspace.subspace csubspace_is_convex empty_iff is_projection_on_iff_orthog orthogonal_complement_orthoI projection_is_projection_on)

lemma is_projection_on_in_image:
  assumes "is_projection_on \<pi> M"
  shows "\<pi> h \<in> M"
  using assms
  by (simp add: is_arg_min_def is_projection_on_def)

lemma is_projection_on_image:
  assumes "is_projection_on \<pi> M"
  shows "range \<pi> = M"
  using assms
  apply (auto simp: is_projection_on_in_image)
  by (smt (verit, ccfv_threshold) dist_pos_lt dist_self is_arg_min_def is_projection_on_def rangeI)

lemma projection_in_image[simp]:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>convex M\<close> and \<open>closed M\<close> and \<open>M \<noteq> {}\<close>
  shows \<open>projection M h \<in> M\<close>
  by (simp add: assms(1) assms(2) assms(3) is_projection_on_in_image projection_is_projection_on)

lemma projection_image[simp]:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>convex M\<close> and \<open>closed M\<close> and \<open>M \<noteq> {}\<close>
  shows \<open>range (projection M) = M\<close>
  by (simp add: assms(1) assms(2) assms(3) is_projection_on_image projection_is_projection_on)

lemma projection_eqI':
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes \<open>convex M\<close>
  assumes \<open>is_projection_on f M\<close>
  shows \<open>projection M = f\<close>
  by (metis assms(1) assms(2) is_projection_on_unique projection_def someI_ex)

lemma is_projection_on_eqI:
  fixes  M :: \<open>'a::complex_inner set\<close>
  assumes a1: \<open>closed_csubspace M\<close> and a2: \<open>h - x \<in> orthogonal_complement M\<close> and a3: \<open>x \<in> M\<close>
    and a4: \<open>is_projection_on \<pi> M\<close>
  shows \<open>\<pi> h = x\<close>
  by (meson a1 a2 a3 a4 closed_csubspace.subspace csubspace_is_convex is_projection_on_def smallest_dist_is_ortho smallest_dist_unique)

lemma projection_eqI:
  fixes  M :: \<open>('a::chilbert_space) set\<close>
  assumes  \<open>closed_csubspace M\<close> and \<open>h - x \<in> orthogonal_complement M\<close> and \<open>x \<in> M\<close>
  shows \<open>projection M h = x\<close>
  by (metis assms(1) assms(2) assms(3) is_projection_on_iff_orthog orthog_proj_exists projection_def is_projection_on_eqI tfl_some)

lemma is_projection_on_fixes_image:
  fixes M :: \<open>'a::metric_space set\<close>
  assumes a1: "is_projection_on \<pi> M" and a3: "x \<in> M"
  shows "\<pi> x = x"
  by (metis a1 a3 dist_pos_lt dist_self is_arg_min_def is_projection_on_def)

lemma projection_fixes_image:
  fixes M :: \<open>('a::chilbert_space) set\<close>
  assumes "closed_csubspace M" and "x \<in> M"
  shows "projection M x = x"
  using is_projection_on_fixes_image
    \<comment> \<open>Theorem 2.7 in \<^cite>\<open>conway2013course\<close>\<close>
  by (simp add: assms complex_vector.subspace_0 projection_eqI)

lemma is_projection_on_closed:
  assumes cont_f: \<open>\<And>x. x \<in> closure M \<Longrightarrow> isCont f x\<close>
  assumes \<open>is_projection_on f M\<close>
  shows \<open>closed M\<close>
proof -
  have \<open>x \<in> M\<close> if \<open>s \<longlonglongrightarrow> x\<close> and \<open>range s \<subseteq> M\<close> for s x
  proof -
    from \<open>is_projection_on f M\<close> \<open>range s \<subseteq> M\<close>
    have \<open>s = (f o s)\<close>
      by (simp add: comp_def is_projection_on_fixes_image range_subsetD)
    also from cont_f \<open>s \<longlonglongrightarrow> x\<close> 
    have \<open>(f o s) \<longlonglongrightarrow> f x\<close>
      apply (rule continuous_imp_tendsto)
      using \<open>s \<longlonglongrightarrow> x\<close> \<open>range s \<subseteq> M\<close>
      by (meson closure_sequential range_subsetD)
    finally have \<open>x = f x\<close>
      using \<open>s \<longlonglongrightarrow> x\<close>
      by (simp add: LIMSEQ_unique)
    then have \<open>x \<in> range f\<close>
      by simp
    with \<open>is_projection_on f M\<close> show \<open>x \<in> M\<close>
      by (simp add: is_projection_on_image)
  qed
  then show ?thesis
    by (metis closed_sequential_limits image_subset_iff)
qed

proposition is_projection_on_reduces_norm:
  includes notation_norm
  fixes M :: \<open>('a::complex_inner) set\<close>
  assumes \<open>is_projection_on \<pi> M\<close> and \<open>closed_csubspace M\<close>
  shows \<open>\<parallel> \<pi>  h \<parallel> \<le> \<parallel> h \<parallel>\<close>
proof-
  have \<open>h - \<pi> h \<in> orthogonal_complement M\<close>
    using assms is_projection_on_iff_orthog by blast
  hence \<open>\<forall> k \<in> M. is_orthogonal (h - \<pi> h) k\<close>
    using orthogonal_complement_orthoI by blast
  also have \<open>\<pi> h \<in>  M\<close>
    using \<open>is_projection_on \<pi> M\<close>
    by (simp add: is_projection_on_in_image)
  ultimately have \<open>is_orthogonal (h - \<pi> h) (\<pi> h)\<close>
    by auto
  hence \<open>\<parallel> \<pi> h \<parallel>^2 + \<parallel> h - \<pi> h \<parallel>^2 = \<parallel> h \<parallel>^2\<close>
    using pythagorean_theorem by fastforce
  hence \<open>\<parallel>\<pi> h \<parallel>^2 \<le> \<parallel> h \<parallel>^2\<close>
    by (smt zero_le_power2)
  thus ?thesis
    using norm_ge_zero power2_le_imp_le by blast
qed

proposition projection_reduces_norm:
  includes notation_norm
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes a1: "closed_csubspace M"
  shows \<open>\<parallel> projection M h \<parallel> \<le> \<parallel> h \<parallel>\<close>
  using assms is_projection_on_iff_orthog orthog_proj_exists is_projection_on_reduces_norm projection_eqI by blast

\<comment> \<open>Theorem 2.7 (version) in \<^cite>\<open>conway2013course\<close>\<close>
theorem is_projection_on_bounded_clinear:
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes a1: "is_projection_on \<pi> M" and a2: "closed_csubspace M"
  shows "bounded_clinear \<pi>"
proof
  have b1:  \<open>csubspace (orthogonal_complement M)\<close>
    by (simp add: a2)
  have f1: "\<forall>a. a - \<pi> a \<in> orthogonal_complement M \<and> \<pi> a \<in> M"
    using a1 a2 is_projection_on_iff_orthog by blast
  hence "c *\<^sub>C x - c *\<^sub>C \<pi> x \<in> orthogonal_complement M"
    for c x
    by (metis (no_types) b1
        add_diff_cancel_right' complex_vector.subspace_def diff_add_cancel scaleC_add_right)
  thus r1: \<open>\<pi> (c *\<^sub>C x) = c *\<^sub>C (\<pi> x)\<close> for x c
    using f1 by (meson a2 a1 closed_csubspace.subspace
        complex_vector.subspace_def is_projection_on_eqI)
  show r2: \<open>\<pi> (x + y) =  (\<pi> x) + (\<pi> y)\<close>
    for x y
  proof-
    have "\<forall>A. \<not> closed_csubspace (A::'a set) \<or> csubspace A"
      by (metis closed_csubspace.subspace)
    hence "csubspace M"
      using a2 by auto
    hence \<open>\<pi> (x + y) - ( (\<pi> x) + (\<pi> y) ) \<in> M\<close>
      by (simp add: complex_vector.subspace_add complex_vector.subspace_diff f1)
    have \<open>closed_csubspace (orthogonal_complement M)\<close>
      using a2
      by simp
    have f1: "\<forall>a b. (b::'a) + (a - b) = a"
      by (metis add.commute diff_add_cancel)
    have f2: "\<forall>a b. (b::'a) - b = a - a"
      by auto
    hence f3: "\<forall>a. a - a \<in> orthogonal_complement M"
      by (simp add: complex_vector.subspace_0)
    have "\<forall>a b. (a \<in> orthogonal_complement M \<or> a + b \<notin> orthogonal_complement M)
             \<or> b \<notin> orthogonal_complement M"
      using add_diff_cancel_right' b1 complex_vector.subspace_diff
      by metis
    hence "\<forall>a b c. (a \<in> orthogonal_complement M \<or> c - (b + a) \<notin> orthogonal_complement M)
              \<or> c - b \<notin> orthogonal_complement M"
      using f1 by (metis diff_diff_add)
    hence f4: "\<forall>a b f. (f a - b \<in> orthogonal_complement M \<or> a - b \<notin> orthogonal_complement M)
              \<or> \<not> is_projection_on f M"
      using f1
      by (metis a2 is_projection_on_iff_orthog)
    have f5: "\<forall>a b c d. (d::'a) - (c + (b - a)) = d + (a - (b + c))"
      by auto
    have "x - \<pi> x \<in> orthogonal_complement M"
      using a1 a2 is_projection_on_iff_orthog by blast
    hence q1: \<open>\<pi> (x + y) - ( (\<pi> x) + (\<pi> y) ) \<in> orthogonal_complement M\<close>
      using f5 f4 f3 by (metis \<open>csubspace (orthogonal_complement M)\<close>
          \<open>is_projection_on \<pi> M\<close> add_diff_eq complex_vector.subspace_diff diff_diff_add
          diff_diff_eq2)
    hence \<open>\<pi> (x + y) - ( (\<pi> x) + (\<pi> y) ) \<in> M \<inter> (orthogonal_complement M)\<close>
      by (simp add: \<open>\<pi> (x + y) - (\<pi> x + \<pi> y) \<in> M\<close>)
    moreover have \<open>M \<inter> (orthogonal_complement M) = {0}\<close>
      by (simp add: \<open>closed_csubspace M\<close> complex_vector.subspace_0 orthogonal_complement_zero_intersection)
    ultimately have \<open>\<pi> (x + y) - ( (\<pi> x) + (\<pi> y) ) = 0\<close>
      by auto
    thus ?thesis by simp
  qed
  from is_projection_on_reduces_norm
  show t1: \<open>\<exists> K. \<forall> x. norm (\<pi> x) \<le> norm x * K\<close>
    by (metis a1 a2 mult.left_neutral ordered_field_class.sign_simps(5))
qed

theorem projection_bounded_clinear:
  fixes M :: \<open>('a::chilbert_space) set\<close>
  assumes a1: "closed_csubspace M"
  shows \<open>bounded_clinear (projection M)\<close>
    \<comment> \<open>Theorem 2.7 in \<^cite>\<open>conway2013course\<close>\<close>
  using assms is_projection_on_iff_orthog orthog_proj_exists is_projection_on_bounded_clinear projection_eqI by blast

proposition is_projection_on_idem:
  fixes M :: \<open>('a::complex_inner) set\<close>
  assumes "is_projection_on \<pi> M"
  shows "\<pi> (\<pi> x) = \<pi> x"
  using is_projection_on_fixes_image is_projection_on_in_image assms by blast

proposition projection_idem:
  fixes M :: "'a::chilbert_space set"
  assumes a1: "closed_csubspace M"
  shows "projection M (projection M x) = projection M x"
  by (metis assms closed_csubspace.closed closed_csubspace.subspace complex_vector.subspace_0 csubspace_is_convex equals0D projection_fixes_image projection_in_image)


proposition is_projection_on_kernel_is_orthogonal_complement:
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes a1: "is_projection_on \<pi> M" and a2: "closed_csubspace M"
  shows "\<pi> -` {0} = orthogonal_complement M"
proof-
  have "x \<in> (\<pi> -` {0})"
    if "x \<in> orthogonal_complement M"
    for x
    by (smt (verit, ccfv_SIG) a1 a2 closed_csubspace_def complex_vector.subspace_def complex_vector.subspace_diff is_projection_on_eqI orthogonal_complement_closed_subspace that vimage_singleton_eq)
  moreover have "x \<in> orthogonal_complement M"
    if s1: "x \<in> \<pi> -` {0}" for x
    by (metis a1 a2 diff_zero is_projection_on_iff_orthog that vimage_singleton_eq)
  ultimately show ?thesis
    by blast
qed

\<comment> \<open>Theorem 2.7 in \<^cite>\<open>conway2013course\<close>\<close>
proposition projection_kernel_is_orthogonal_complement:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes "closed_csubspace M"
  shows "(projection M) -` {0} = (orthogonal_complement M)"
  by (metis assms closed_csubspace_def complex_vector.subspace_def csubspace_is_convex insert_absorb insert_not_empty is_projection_on_kernel_is_orthogonal_complement projection_is_projection_on)

lemma is_projection_on_id_minus:
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes is_proj: "is_projection_on \<pi> M"
    and cc: "closed_csubspace M"
  shows "is_projection_on (id - \<pi>) (orthogonal_complement M)"
  using is_proj apply (simp add: cc is_projection_on_iff_orthog)
  using double_orthogonal_complement_increasing by blast


text \<open>Exercise 2 (section 2, chapter I) in  \<^cite>\<open>conway2013course\<close>\<close>
lemma projection_on_orthogonal_complement[simp]:
  fixes M :: "'a::chilbert_space set"
  assumes a1: "closed_csubspace M"
  shows "projection (orthogonal_complement M) = id - projection M"
  apply (auto intro!: ext)
  by (smt (verit, ccfv_SIG) add_diff_cancel_left' assms closed_csubspace.closed closed_csubspace.subspace complex_vector.subspace_0 csubspace_is_convex diff_add_cancel double_orthogonal_complement_increasing insert_absorb insert_not_empty is_projection_on_iff_orthog orthogonal_complement_closed_subspace projection_eqI projection_is_projection_on subset_eq)

lemma is_projection_on_zero:
  "is_projection_on (\<lambda>_. 0) {0}"
  by (simp add: is_projection_on_def is_arg_min_def)

lemma projection_zero[simp]:
  "projection {0} = (\<lambda>_. 0)"
  using is_projection_on_zero
  by (metis (full_types) is_projection_on_in_image projection_def singletonD someI_ex)

lemma is_projection_on_rank1:
  fixes t :: \<open>'a::complex_inner\<close>
  shows \<open>is_projection_on (\<lambda>x. ((t \<bullet>\<^sub>C x) / (t \<bullet>\<^sub>C t)) *\<^sub>C t) (cspan {t})\<close>
proof (cases \<open>t = 0\<close>)
  case True
  then show ?thesis
    by (simp add: is_projection_on_zero)
next
  case False
  define P where \<open>P x = ((t \<bullet>\<^sub>C x) / (t \<bullet>\<^sub>C t)) *\<^sub>C t\<close> for x
  define t' where \<open>t' = t /\<^sub>C norm t\<close>
  with False have \<open>norm t' = 1\<close>
    by (simp add: norm_inverse)
  have P_def': \<open>P x = cinner t' x *\<^sub>C t'\<close> for x
    unfolding P_def t'_def apply auto
    by (metis divide_divide_eq_left divide_inverse mult.commute power2_eq_square power2_norm_eq_cinner)
  have spant': \<open>cspan {t} = cspan {t'}\<close>
    by (simp add: False t'_def)
  have cc: \<open>closed_csubspace (cspan {t})\<close>
    by (auto intro!: finite_cspan_closed closed_csubspace.intro)
  have ortho: \<open>h - P h \<in> orthogonal_complement (cspan {t})\<close> for h
    unfolding orthogonal_complement_def P_def' spant' apply auto
    by (smt (verit, ccfv_threshold) \<open>norm t' = 1\<close> add_cancel_right_left cinner_add_right cinner_commute' cinner_scaleC_right cnorm_eq_1 complex_vector.span_breakdown_eq complex_vector.span_empty diff_add_cancel mult_cancel_left1 singletonD)
  have inspan: \<open>P h \<in> cspan {t}\<close> for h
    unfolding P_def' spant'
    by (simp add: complex_vector.span_base complex_vector.span_scale)
  show \<open>is_projection_on P (cspan {t})\<close>
    apply (subst is_projection_on_iff_orthog)
    using cc ortho inspan by auto
qed

lemma projection_rank1:
  fixes t x :: \<open>'a::complex_inner\<close>
  shows \<open>projection (cspan {t}) x = ((t \<bullet>\<^sub>C x) / (t \<bullet>\<^sub>C t)) *\<^sub>C t\<close>
  apply (rule fun_cong, rule projection_eqI', simp)
  by (rule is_projection_on_rank1)

subsection \<open>More orthogonal complement\<close>

text \<open>The following lemmas logically fit into the "orthogonality" section but depend on projections for their proofs.\<close>

text \<open>Corollary 2.8 in \<^cite>\<open>conway2013course\<close>\<close>
theorem double_orthogonal_complement_id[simp]:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes a1: "closed_csubspace M"
  shows "orthogonal_complement (orthogonal_complement M) = M"
proof-
  have b2: "x \<in> (id - projection M) -` {0}"
    if c1: "x \<in> M" for x
    by (simp add: assms projection_fixes_image that)

  have b3: \<open>x \<in> M\<close>
    if c1: \<open>x \<in> (id - projection M) -` {0}\<close> for x
    by (metis assms closed_csubspace.closed closed_csubspace.subspace complex_vector.subspace_0 csubspace_is_convex eq_id_iff equals0D fun_diff_def projection_in_image right_minus_eq that vimage_singleton_eq)
  have \<open>x \<in>  M \<longleftrightarrow> x \<in> (id - projection M) -` {0}\<close> for x
    using b2 b3 by blast
  hence b4: \<open>( id - (projection M) ) -` {0} =  M\<close>
    by blast
  have b1: "orthogonal_complement (orthogonal_complement M)
          = (projection (orthogonal_complement M)) -` {0}"
    by (simp add: a1 projection_kernel_is_orthogonal_complement del: projection_on_orthogonal_complement)
  also have \<open>... = ( id - (projection M) ) -` {0}\<close>
    by (simp add: a1)
  also have \<open>... = M\<close>
    by (simp add: b4)
  finally show ?thesis by blast
qed

lemma orthogonal_complement_antimono_iff[simp]:
  fixes  A B :: \<open>('a::chilbert_space) set\<close>
  assumes \<open>closed_csubspace A\<close> and  \<open>closed_csubspace B\<close>
  shows \<open>orthogonal_complement A \<subseteq> orthogonal_complement B \<longleftrightarrow> A \<supseteq> B\<close>
proof (rule iffI)
  show \<open>orthogonal_complement A \<subseteq> orthogonal_complement B\<close> if \<open>A \<supseteq> B\<close>
    using that by auto

  assume \<open>orthogonal_complement A \<subseteq> orthogonal_complement B\<close>
  then have \<open>orthogonal_complement (orthogonal_complement A) \<supseteq> orthogonal_complement (orthogonal_complement B)\<close>
    by simp
  then show \<open>A \<supseteq> B\<close>
    using assms by auto
qed

lemma de_morgan_orthogonal_complement_plus:
  fixes A B::"('a::complex_inner) set"
  assumes \<open>0 \<in> A\<close> and \<open>0 \<in> B\<close>
  shows \<open>orthogonal_complement (A +\<^sub>M B) = orthogonal_complement A \<inter> orthogonal_complement B\<close>
proof -
  have "x \<in> (orthogonal_complement A) \<inter> (orthogonal_complement B)"
    if "x \<in> orthogonal_complement (A +\<^sub>M B)" for x
  proof -
    have \<open>orthogonal_complement (A +\<^sub>M B) = orthogonal_complement (A + B)\<close>
      unfolding closed_sum_def by (subst orthogonal_complement_of_closure[symmetric], simp)
    hence \<open>x \<in> orthogonal_complement (A + B)\<close>
      using that by blast
    hence t1: \<open>\<forall>z \<in> (A + B). (z \<bullet>\<^sub>C x) = 0\<close>
      by (simp add: orthogonal_complement_orthoI')
    have \<open>A \<subseteq> A + B\<close>
      using subset_iff add.commute set_zero_plus2 \<open>0 \<in> B\<close>
      by fastforce
    hence \<open>\<forall>z \<in> A. (z \<bullet>\<^sub>C x) = 0\<close>
      using t1 by auto
    hence w1: \<open>x \<in> (orthogonal_complement A)\<close>
      by (smt mem_Collect_eq is_orthogonal_sym orthogonal_complement_def)
    have \<open>B \<subseteq> A + B\<close>
      using \<open>0 \<in> A\<close> subset_iff set_zero_plus2 by blast
    hence \<open>\<forall> z \<in> B. (z \<bullet>\<^sub>C x) = 0\<close>
      using t1 by auto
    hence \<open>x \<in> (orthogonal_complement B)\<close>
      by (smt mem_Collect_eq is_orthogonal_sym orthogonal_complement_def)
    thus ?thesis
      using w1 by auto
  qed
  moreover have "x \<in> (orthogonal_complement (A +\<^sub>M B))"
    if v1: "x \<in> (orthogonal_complement A) \<inter> (orthogonal_complement B)"
    for x
  proof-
    have \<open>x \<in> (orthogonal_complement A)\<close>
      using v1
      by blast
    hence \<open>\<forall>y\<in> A. (y \<bullet>\<^sub>C x) = 0\<close>
      by (simp add: orthogonal_complement_orthoI')
    have \<open>x \<in> (orthogonal_complement B)\<close>
      using v1
      by blast
    hence \<open>\<forall> y\<in> B. (y \<bullet>\<^sub>C x) = 0\<close>
      by (simp add: orthogonal_complement_orthoI')
    have \<open>\<forall> a\<in>A. \<forall> b\<in>B. (a+b) \<bullet>\<^sub>C x = 0\<close>
      by (simp add: \<open>\<forall>y\<in>A. y \<bullet>\<^sub>C x = 0\<close> \<open>\<forall>y\<in>B. (y \<bullet>\<^sub>C x) = 0\<close> cinner_add_left)
    hence \<open>\<forall> y \<in> (A + B). y \<bullet>\<^sub>C x = 0\<close>
      using set_plus_elim by force
    hence \<open>x \<in> (orthogonal_complement (A + B))\<close>
      by (smt mem_Collect_eq is_orthogonal_sym orthogonal_complement_def)
    moreover have \<open>(orthogonal_complement (A + B)) = (orthogonal_complement (A +\<^sub>M B))\<close>
      unfolding closed_sum_def by (subst orthogonal_complement_of_closure[symmetric], simp)
    ultimately have \<open>x \<in> (orthogonal_complement (A +\<^sub>M B))\<close>
      by blast
    thus ?thesis
      by blast
  qed
  ultimately show ?thesis by blast
qed

lemma de_morgan_orthogonal_complement_inter:
  fixes A B::"'a::chilbert_space set"
  assumes a1: \<open>closed_csubspace A\<close> and a2: \<open>closed_csubspace B\<close>
  shows  \<open>orthogonal_complement (A \<inter> B) = orthogonal_complement A +\<^sub>M orthogonal_complement B\<close>
proof-
  have \<open>orthogonal_complement A +\<^sub>M orthogonal_complement B
    = orthogonal_complement (orthogonal_complement (orthogonal_complement A +\<^sub>M orthogonal_complement B))\<close>
    by (simp add: closed_subspace_closed_sum)
  also have \<open>\<dots> = orthogonal_complement (orthogonal_complement (orthogonal_complement A) \<inter> orthogonal_complement (orthogonal_complement B))\<close>
    by (simp add: de_morgan_orthogonal_complement_plus orthogonal_complementI)
  also have \<open>\<dots> = orthogonal_complement (A \<inter> B)\<close>
    by (simp add: a1 a2)
  finally show ?thesis
    by simp
qed

lemma orthogonal_complement_of_cspan: \<open>orthogonal_complement A = orthogonal_complement (cspan A)\<close>
  by (metis (no_types, opaque_lifting) closed_csubspace.subspace complex_vector.span_minimal complex_vector.span_superset double_orthogonal_complement_increasing orthogonal_complement_antimono orthogonal_complement_closed_subspace subset_antisym)

lemma orthogonal_complement_orthogonal_complement_closure_cspan:
  \<open>orthogonal_complement (orthogonal_complement S) = closure (cspan S)\<close> for S :: \<open>'a::chilbert_space set\<close>
proof -
  have \<open>orthogonal_complement (orthogonal_complement S) = orthogonal_complement (orthogonal_complement (closure (cspan S)))\<close>
    by (simp flip: orthogonal_complement_of_closure orthogonal_complement_of_cspan)
  also have \<open>\<dots> = closure (cspan S)\<close>
    by simp
  finally show \<open>orthogonal_complement (orthogonal_complement S) = closure (cspan S)\<close>
    by -
qed

instance ccsubspace :: (chilbert_space) complete_orthomodular_lattice
proof
  fix X Y :: \<open>'a ccsubspace\<close>

  show "inf X (- X) = bot"
    apply transfer
    by (simp add: closed_csubspace_def complex_vector.subspace_0 orthogonal_complement_zero_intersection)

  have \<open>t \<in> M +\<^sub>M orthogonal_complement M\<close>
    if \<open>closed_csubspace M\<close> for t::'a and M
    by (metis (no_types, lifting) UNIV_I closed_csubspace.subspace complex_vector.subspace_def de_morgan_orthogonal_complement_inter double_orthogonal_complement_id orthogonal_complement_closed_subspace orthogonal_complement_zero orthogonal_complement_zero_intersection that)
  hence b1: \<open>M +\<^sub>M orthogonal_complement M = UNIV\<close>
    if \<open>closed_csubspace M\<close> for M :: \<open>'a set\<close>
    using that by blast
  show "sup X (- X) = top"
    apply transfer
    using b1 by auto
  show "- (- X) = X"
    apply transfer by simp

  show "- Y \<le> - X"
    if "X \<le> Y"
    using that apply transfer by simp

  have c1: "M +\<^sub>M orthogonal_complement M \<inter> N \<subseteq> N"
    if "closed_csubspace M" and "closed_csubspace N" and "M \<subseteq> N"
    for M N :: "'a set"
    using that
    by (simp add: closed_sum_is_sup)

  have c2: \<open>u \<in> M +\<^sub>M (orthogonal_complement M \<inter> N)\<close>
    if a1: "closed_csubspace M" and a2: "closed_csubspace N" and a3: "M \<subseteq> N" and x1: \<open>u \<in> N\<close>
    for M :: "'a set" and N :: "'a set"  and u
  proof -
    have d4: \<open>(projection M) u \<in> M\<close>
      by (metis a1 closed_csubspace_def csubspace_is_convex equals0D orthog_proj_exists projection_in_image)
    hence d2: \<open>(projection M) u \<in> N\<close>
      using a3 by auto
    have d1: \<open>csubspace N\<close>
      by (simp add: a2)
    have \<open>u - (projection M) u \<in> orthogonal_complement M\<close>
      by (simp add: a1 orthogonal_complementI projection_orthogonal)
    moreover have  \<open>u - (projection M) u \<in> N\<close>
      by (simp add: d1 d2 complex_vector.subspace_diff x1)
    ultimately have d3: \<open>u - (projection M) u \<in> ((orthogonal_complement M) \<inter> N)\<close>
      by simp
    hence \<open>\<exists> v \<in> ((orthogonal_complement M) \<inter> N). u = (projection M) u + v\<close>
      by (metis d3 diff_add_cancel ordered_field_class.sign_simps(2))
    then obtain v where \<open>v \<in> ((orthogonal_complement M) \<inter> N)\<close> and \<open>u = (projection M) u + v\<close>
      by blast
    hence \<open>u \<in> M + ((orthogonal_complement M) \<inter> N)\<close>
      by (metis d4 set_plus_intro)
    thus ?thesis
      unfolding closed_sum_def
      using closure_subset by blast
  qed

  have c3: "N \<subseteq> M +\<^sub>M ((orthogonal_complement M) \<inter> N)"
    if "closed_csubspace M" and "closed_csubspace N" and "M \<subseteq> N"
    for M N :: "'a set"
    using c2 that by auto

  show "sup X (inf (- X) Y) = Y"
    if "X \<le> Y"
    using that apply transfer
    using c1 c3
    by (simp add: subset_antisym)

  show "X - Y = inf X (- Y)"
    apply transfer by simp
qed

subsection \<open>Orthogonal spaces\<close>

definition \<open>orthogonal_spaces S T \<longleftrightarrow> (\<forall>x\<in>space_as_set S. \<forall>y\<in>space_as_set T. is_orthogonal x y)\<close>

lemma orthogonal_spaces_leq_compl: \<open>orthogonal_spaces S T \<longleftrightarrow> S \<le> -T\<close>
  unfolding orthogonal_spaces_def apply transfer
  by (auto simp: orthogonal_complement_def)

lemma orthogonal_bot[simp]: \<open>orthogonal_spaces S bot\<close>
  by (simp add: orthogonal_spaces_def)

lemma orthogonal_spaces_sym: \<open>orthogonal_spaces S T \<Longrightarrow> orthogonal_spaces T S\<close>
  unfolding orthogonal_spaces_def
  using is_orthogonal_sym by blast

lemma orthogonal_sup: \<open>orthogonal_spaces S T1 \<Longrightarrow> orthogonal_spaces S T2 \<Longrightarrow> orthogonal_spaces S (sup T1 T2)\<close>
  apply (rule orthogonal_spaces_sym)
  apply (simp add: orthogonal_spaces_leq_compl)
  using orthogonal_spaces_leq_compl orthogonal_spaces_sym by blast

lemma orthogonal_sum:
  assumes \<open>finite F\<close> and \<open>\<And>x. x\<in>F \<Longrightarrow> orthogonal_spaces S (T x)\<close> 
  shows \<open>orthogonal_spaces S (sum T F)\<close>
  using assms
  apply induction
  by (auto intro!: orthogonal_sup)

lemma orthogonal_spaces_ccspan: \<open>(\<forall>x\<in>S. \<forall>y\<in>T. is_orthogonal x y) \<longleftrightarrow> orthogonal_spaces (ccspan S) (ccspan T)\<close>
  by (meson ccspan_leq_ortho_ccspan ccspan_superset orthogonal_spaces_def orthogonal_spaces_leq_compl subset_iff)

subsection \<open>Orthonormal bases\<close>

lemma ortho_basis_exists: 
  fixes S :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_ortho_set S\<close>
  shows \<open>\<exists>B. B \<supseteq> S \<and> is_ortho_set B \<and> closure (cspan B) = UNIV\<close>
proof -
  define on where \<open>on B \<longleftrightarrow> B \<supseteq> S \<and> is_ortho_set B\<close> for B :: \<open>'a set\<close>
  have \<open>\<exists>B\<in>Collect on. \<forall>B'\<in>Collect on. B \<subseteq> B' \<longrightarrow> B' = B\<close>
  proof (rule subset_Zorn_nonempty; simp)
    show \<open>\<exists>S. on S\<close>
      apply (rule exI[of _ S])
      using assms on_def by fastforce
  next
    fix C :: \<open>'a set set\<close>
    assume \<open>C \<noteq> {}\<close>
    assume \<open>subset.chain (Collect on) C\<close>
    then have C_on: \<open>B \<in> C \<Longrightarrow> on B\<close> and C_order: \<open>B \<in> C \<Longrightarrow> B' \<in> C \<Longrightarrow> B \<subseteq> B' \<or> B' \<subseteq> B\<close> for B B'
      by (auto simp: subset.chain_def)
    have \<open>is_orthogonal x y\<close> if \<open>x\<in>\<Union>C\<close> \<open>y\<in>\<Union>C\<close> \<open>x \<noteq> y\<close> for x y
      by (smt (verit) UnionE C_order C_on on_def is_ortho_set_def subsetD that(1) that(2) that(3))
    moreover have \<open>0 \<notin> \<Union> C\<close>
      by (meson UnionE C_on is_ortho_set_def on_def)
    moreover have \<open>\<Union>C \<supseteq> S\<close>
      using C_on \<open>C \<noteq> {}\<close> on_def by blast
    ultimately show \<open>on (\<Union> C)\<close>
      unfolding on_def is_ortho_set_def by simp
  qed
  then obtain B where \<open>on B\<close> and B_max: \<open>B' \<supseteq> B \<Longrightarrow> on B' \<Longrightarrow> B=B'\<close> for B'
    by auto
  have \<open>\<psi> = 0\<close> if \<psi>ortho: \<open>\<forall>b\<in>B. is_orthogonal \<psi> b\<close> for \<psi> :: 'a
  proof (rule ccontr)
    assume \<open>\<psi> \<noteq> 0\<close>
    define \<phi> B' where \<open>\<phi> = \<psi> /\<^sub>R norm \<psi>\<close> and \<open>B' = B \<union> {\<phi>}\<close>
    have [simp]: \<open>norm \<phi> = 1\<close>
      using \<open>\<psi> \<noteq> 0\<close> by (auto simp: \<phi>_def)
    have \<phi>ortho: \<open>is_orthogonal \<phi> b\<close> if \<open>b \<in> B\<close> for b
      using \<psi>ortho that \<phi>_def  by auto
    have orthoB': \<open>is_orthogonal x y\<close> if \<open>x\<in>B'\<close> \<open>y\<in>B'\<close> \<open>x \<noteq> y\<close> for x y
      using that \<open>on B\<close> \<phi>ortho \<phi>ortho[THEN is_orthogonal_sym[THEN iffD1]]
      by (auto simp: B'_def on_def is_ortho_set_def)
    have B'0: \<open>0 \<notin> B'\<close>
      using B'_def \<open>norm \<phi> = 1\<close> \<open>on B\<close> is_ortho_set_def on_def by fastforce
    have \<open>S \<subseteq> B'\<close>
      using B'_def \<open>on B\<close> on_def by auto
    from orthoB' B'0 \<open>S \<subseteq> B'\<close> have \<open>on B'\<close>
      by (simp add: on_def is_ortho_set_def)
    with B_max have \<open>B = B'\<close>
      by (metis B'_def Un_upper1)
    then have \<open>\<phi> \<in> B\<close>
      using B'_def by blast
    then have \<open>is_orthogonal \<phi> \<phi>\<close>
      using \<phi>ortho by blast
    then show False
      using B'0 \<open>B = B'\<close> \<open>\<phi> \<in> B\<close> by fastforce
  qed 
  then have \<open>orthogonal_complement B = {0}\<close>
    by (auto simp: orthogonal_complement_def)
  then have \<open>UNIV = orthogonal_complement (orthogonal_complement B)\<close>
    by simp
  also have \<open>\<dots> = orthogonal_complement (orthogonal_complement (closure (cspan B)))\<close>
    by (metis (mono_tags, opaque_lifting) \<open>orthogonal_complement B = {0}\<close> cinner_zero_left complex_vector.span_superset empty_iff insert_iff orthogonal_complementI orthogonal_complement_antimono orthogonal_complement_of_closure subsetI subset_antisym)
  also have \<open>\<dots> = closure (cspan B)\<close>
    apply (rule double_orthogonal_complement_id)
    by simp
  finally have \<open>closure (cspan B) = UNIV\<close>
    by simp
  with \<open>on B\<close> show ?thesis
    by (auto simp: on_def)
qed

lemma orthonormal_basis_exists: 
  fixes S :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_ortho_set S\<close> and \<open>\<And>x. x\<in>S \<Longrightarrow> norm x = 1\<close>
  shows \<open>\<exists>B. B \<supseteq> S \<and> is_onb B\<close>
proof -
  from \<open>is_ortho_set S\<close>
  obtain B where \<open>is_ortho_set B\<close> and \<open>B \<supseteq> S\<close> and \<open>closure (cspan B) = UNIV\<close>
    using ortho_basis_exists by blast
  define B' where \<open>B' = (\<lambda>x. x /\<^sub>R norm x) ` B\<close>
  have \<open>S = (\<lambda>x. x /\<^sub>R norm x) ` S\<close>
    by (simp add: assms(2))
  then have \<open>B' \<supseteq> S\<close>
    using B'_def \<open>S \<subseteq> B\<close> by blast
  moreover 
  have \<open>ccspan B' = top\<close>
    apply (transfer fixing: B')
    apply (simp add: B'_def scaleR_scaleC)
    apply (subst complex_vector.span_image_scale')
    using \<open>is_ortho_set B\<close> \<open>closure (cspan B) = UNIV\<close> is_ortho_set_def 
    by auto
  moreover have \<open>is_ortho_set B'\<close>
    using \<open>is_ortho_set B\<close> by (auto simp: B'_def is_ortho_set_def)
  moreover have \<open>\<forall>b\<in>B'. norm b = 1\<close>
    using \<open>is_ortho_set B\<close> apply (auto simp: B'_def is_ortho_set_def)
    by (metis field_class.field_inverse norm_eq_zero)
  ultimately show ?thesis
    by (auto simp: is_onb_def)
qed


definition some_chilbert_basis :: \<open>'a::chilbert_space set\<close> where
  \<open>some_chilbert_basis = (SOME B::'a set. is_onb B)\<close>

lemma is_onb_some_chilbert_basis[simp]: \<open>is_onb (some_chilbert_basis :: 'a::chilbert_space set)\<close>
  using orthonormal_basis_exists[OF is_ortho_set_empty]
  by (auto simp add: some_chilbert_basis_def intro: someI2)

lemma is_ortho_set_some_chilbert_basis[simp]: \<open>is_ortho_set some_chilbert_basis\<close>
  using is_onb_def is_onb_some_chilbert_basis by blast

lemma is_normal_some_chilbert_basis: \<open>\<And>x. x \<in> some_chilbert_basis \<Longrightarrow> norm x = 1\<close>
  using is_onb_def is_onb_some_chilbert_basis by blast

lemma ccspan_some_chilbert_basis[simp]: \<open>ccspan some_chilbert_basis = top\<close>
  using is_onb_def is_onb_some_chilbert_basis by blast

lemma span_some_chilbert_basis[simp]: \<open>closure (cspan some_chilbert_basis) = UNIV\<close>
  by (metis ccspan.rep_eq ccspan_some_chilbert_basis top_ccsubspace.rep_eq)

lemma cindependent_some_chilbert_basis[simp]: \<open>cindependent some_chilbert_basis\<close>
  using is_ortho_set_cindependent is_ortho_set_some_chilbert_basis by blast

lemma finite_some_chilbert_basis[simp]: \<open>finite (some_chilbert_basis :: 'a :: {chilbert_space, cfinite_dim} set)\<close>
  apply (rule cindependent_cfinite_dim_finite)
  by simp

lemma some_chilbert_basis_nonempty: \<open>(some_chilbert_basis :: 'a::{chilbert_space, not_singleton} set) \<noteq> {}\<close>
proof (rule ccontr, simp)
  define B :: \<open>'a set\<close> where \<open>B = some_chilbert_basis\<close>
  assume [simp]: \<open>B = {}\<close>
  have \<open>UNIV = closure (cspan B)\<close>
    using B_def span_some_chilbert_basis by blast
  also have \<open>\<dots> = {0}\<close>
    by simp
  also have \<open>\<dots> \<noteq> UNIV\<close>
    using Extra_General.UNIV_not_singleton by blast
  finally show False
    by simp
qed

lemma basis_projections_reconstruct_has_sum:
  assumes \<open>is_ortho_set B\<close> and normB: \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<psi>B: \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>((\<lambda>b. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) has_sum \<psi>) B\<close>
proof (rule has_sumI_metric)
  fix e :: real assume \<open>e > 0\<close>
  define e2 where \<open>e2 = e/2\<close>
  have [simp]: \<open>e2 > 0\<close>
    by (simp add: \<open>0 < e\<close> e2_def)
  define bb where \<open>bb \<phi> b = (b \<bullet>\<^sub>C \<phi>) *\<^sub>C b\<close> for \<phi> and b :: 'a
  have linear_bb: \<open>clinear (\<lambda>\<phi>. bb \<phi> b)\<close> for b
    by (simp add: bb_def cinner_add_right clinear_iff scaleC_left.add)
  from \<psi>B obtain \<phi> where dist\<phi>\<psi>: \<open>dist \<phi> \<psi> < e2\<close> and \<phi>B: \<open>\<phi> \<in> cspan B\<close>
    apply atomize_elim apply (simp add: ccspan.rep_eq closure_approachable)
    using \<open>0 < e2\<close> by blast
  from \<phi>B obtain F where \<open>finite F\<close> and \<open>F \<subseteq> B\<close> and \<phi>F: \<open>\<phi> \<in> cspan F\<close>
    by (meson vector_finitely_spanned)
  have \<open>dist (sum (bb \<psi>) G) \<psi> < e\<close> 
    if \<open>finite G\<close> and \<open>F \<subseteq> G\<close> and \<open>G \<subseteq> B\<close> for G
  proof -
    have sum\<phi>: \<open>sum (bb \<phi>) G = \<phi>\<close>
    proof -
      from \<phi>F \<open>F \<subseteq> G\<close> have \<phi>G: \<open>\<phi> \<in> cspan G\<close>
        using complex_vector.span_mono by blast
      then obtain f where \<phi>sum: \<open>\<phi> = (\<Sum>b\<in>G. f b *\<^sub>C b)\<close>
        using complex_vector.span_finite[OF \<open>finite G\<close>] 
        by auto
      have \<open>sum (bb \<phi>) G = (\<Sum>c\<in>G. \<Sum>b\<in>G. bb (f b *\<^sub>C b) c)\<close>
        apply (simp add: \<phi>sum)
        apply (rule sum.cong, simp)
        apply (rule complex_vector.linear_sum[where f=\<open>\<lambda>x. bb x _\<close>])
        by (rule linear_bb)
      also have \<open>\<dots> = (\<Sum>(c,b)\<in>G\<times>G. bb (f b *\<^sub>C b) c)\<close>
        by (simp add: sum.cartesian_product)
      also have \<open>\<dots> = (\<Sum>b\<in>G. f b *\<^sub>C b)\<close>
        apply (rule sym)
        apply (rule sum.reindex_bij_witness_not_neutral
            [where j=\<open>\<lambda>b. (b,b)\<close> and i=fst and T'=\<open>G\<times>G - (\<lambda>b. (b,b)) ` G\<close> and S'=\<open>{}\<close>])
        using \<open>finite G\<close> apply (auto simp: bb_def)
         apply (metis (no_types, lifting) assms(1) imageI is_ortho_set_antimono is_ortho_set_def that(3))
        using normB \<open>G \<subseteq> B\<close> cnorm_eq_1 by blast
      also have \<open>\<dots> = \<phi>\<close>
        by (simp flip: \<phi>sum)
      finally show ?thesis
        by -
    qed
    have \<open>dist (sum (bb \<phi>) G) (sum (bb \<psi>) G) < e2\<close>
    proof -
      define \<gamma> where \<open>\<gamma> = \<phi> - \<psi>\<close>
      have \<open>(dist (sum (bb \<phi>) G) (sum (bb \<psi>) G))\<^sup>2 = (norm (sum (bb \<gamma>) G))\<^sup>2\<close>
        by (simp add: dist_norm \<gamma>_def complex_vector.linear_diff[OF linear_bb] sum_subtractf)
      also have \<open>\<dots> = (norm (sum (bb \<gamma>) G))\<^sup>2 + (norm (\<gamma> - sum (bb \<gamma>) G))\<^sup>2 - (norm (\<gamma> - sum (bb \<gamma>) G))\<^sup>2\<close>
        by simp
      also have \<open>\<dots> = (norm (sum (bb \<gamma>) G + (\<gamma> - sum (bb \<gamma>) G)))\<^sup>2 - (norm (\<gamma> - sum (bb \<gamma>) G))\<^sup>2\<close>
      proof -
        have \<open>(\<Sum>b\<in>G. bb \<gamma> b \<bullet>\<^sub>C bb \<gamma> c) = bb \<gamma> c \<bullet>\<^sub>C \<gamma>\<close> if \<open>c \<in> G\<close> for c
          apply (subst sum_single[where i=c])
          using that apply (auto intro!: \<open>finite G\<close> simp: bb_def)
           apply (metis \<open>G \<subseteq> B\<close> \<open>is_ortho_set B\<close> is_ortho_set_antimono is_ortho_set_def)
          using \<open>G \<subseteq> B\<close> normB cnorm_eq_1 by blast
        then have \<open>is_orthogonal (sum (bb \<gamma>) G) (\<gamma> - sum (bb \<gamma>) G)\<close>
          by (simp add: cinner_sum_left cinner_diff_right cinner_sum_right)
        then show ?thesis
          apply (rule_tac arg_cong[where f=\<open>\<lambda>x. x - _\<close>])
          by (rule pythagorean_theorem[symmetric])
      qed
      also have \<open>\<dots> = (norm \<gamma>)\<^sup>2 - (norm (\<gamma> - sum (bb \<gamma>) G))\<^sup>2\<close>
        by simp
      also have \<open>\<dots> \<le> (norm \<gamma>)\<^sup>2\<close>
        by simp
      also have \<open>\<dots> = (dist \<phi> \<psi>)\<^sup>2\<close>
        by (simp add: \<gamma>_def dist_norm)
      also have \<open>\<dots> < e2\<^sup>2\<close>
        using dist\<phi>\<psi> apply (rule power_strict_mono)
        by auto
      finally show ?thesis
        by (smt (verit) \<open>0 < e2\<close> power_mono)
    qed
    with sum\<phi> dist\<phi>\<psi> show \<open>dist (sum (bb \<psi>) G) \<psi> < e\<close>
      apply (rule_tac dist_triangle_lt[where z=\<phi>])
      by (simp add: e2_def dist_commute)
  qed
  with \<open>finite F\<close> and \<open>F \<subseteq> B\<close> 
  show \<open>\<exists>F. finite F \<and>
             F \<subseteq> B \<and> (\<forall>G. finite G \<and> F \<subseteq> G \<and> G \<subseteq> B \<longrightarrow> dist (sum (bb \<psi>) G) \<psi> < e)\<close>
    by (auto intro!: exI[of _ F])
qed

lemma basis_projections_reconstruct:
  assumes \<open>is_ortho_set B\<close> and \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>b\<in>B. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) = \<psi>\<close>
  using assms basis_projections_reconstruct_has_sum infsumI by blast

lemma basis_projections_reconstruct_summable:
  assumes \<open>is_ortho_set B\<close> and \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>(\<lambda>b. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) summable_on B\<close>
  by (simp add: assms basis_projections_reconstruct basis_projections_reconstruct_has_sum summable_iff_has_sum_infsum)

lemma parseval_identity_has_sum:
  assumes \<open>is_ortho_set B\<close> and normB: \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>((\<lambda>b. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2) has_sum (norm \<psi>)\<^sup>2) B\<close>
proof -
  have *: \<open>(\<lambda>v. (norm v)\<^sup>2) (\<Sum>b\<in>F. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) = (\<Sum>b\<in>F. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2)\<close> if \<open>finite F\<close> and \<open>F \<subseteq> B\<close> for F
    apply (subst pythagorean_theorem_sum)
    using \<open>is_ortho_set B\<close> normB that
      apply (auto intro!: sum.cong[OF refl] simp: is_ortho_set_def)
    by blast
  
  from assms have \<open>((\<lambda>b. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) has_sum \<psi>) B\<close>
    by (simp add: basis_projections_reconstruct_has_sum)
  then have \<open>((\<lambda>F. \<Sum>b\<in>F. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) \<longlongrightarrow> \<psi>) (finite_subsets_at_top B)\<close>
    by (simp add: has_sum_def)
  then have \<open>((\<lambda>F. (\<lambda>v. (norm v)\<^sup>2) (\<Sum>b\<in>F. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b)) \<longlongrightarrow> (norm \<psi>)\<^sup>2) (finite_subsets_at_top B)\<close>
    apply (rule isCont_tendsto_compose[rotated])
    by simp
  then have \<open>((\<lambda>F. (\<Sum>b\<in>F. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2)) \<longlongrightarrow> (norm \<psi>)\<^sup>2) (finite_subsets_at_top B)\<close>
    apply (rule tendsto_cong[THEN iffD2, rotated])
    apply (rule eventually_finite_subsets_at_top_weakI)
    by (simp add: *)
  then show \<open>((\<lambda>b. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2) has_sum (norm \<psi>)\<^sup>2) B\<close>
    by (simp add: has_sum_def)
qed

lemma parseval_identity_summable:
  assumes \<open>is_ortho_set B\<close> and \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>(\<lambda>b. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2) summable_on B\<close>
  using parseval_identity_has_sum[OF assms] has_sum_imp_summable by blast

lemma parseval_identity:
  assumes \<open>is_ortho_set B\<close> and \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>b\<in>B. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2) = (norm \<psi>)\<^sup>2\<close>
  using parseval_identity_has_sum[OF assms]
  using infsumI by blast


subsection \<open>Riesz-representation theorem\<close>

lemma orthogonal_complement_kernel_functional:
  fixes f :: \<open>'a::complex_inner \<Rightarrow> complex\<close>
  assumes \<open>bounded_clinear f\<close>
  shows \<open>\<exists>x. orthogonal_complement (f -` {0}) = cspan {x}\<close>
proof (cases \<open>orthogonal_complement (f -` {0}) = {0}\<close>)
  case True
  then show ?thesis
    apply (rule_tac x=0 in exI) by auto
next
  case False
  then obtain x where xortho: \<open>x \<in> orthogonal_complement (f -` {0})\<close> and xnon0: \<open>x \<noteq> 0\<close>
    using complex_vector.subspace_def by fastforce

  from xnon0 xortho
  have r1: \<open>f x \<noteq> 0\<close>
    by (metis cinner_eq_zero_iff orthogonal_complement_orthoI vimage_singleton_eq)

  have \<open>\<exists> k. y = k *\<^sub>C x\<close> if \<open>y \<in> orthogonal_complement (f -` {0})\<close> for y
  proof (cases \<open>y = 0\<close>)
    case True
    then show ?thesis by auto
  next
    case False
    with that
    have \<open>f y \<noteq> 0\<close>
      by (metis cinner_eq_zero_iff orthogonal_complement_orthoI vimage_singleton_eq)
    then obtain k where k_def: \<open>f x = k * f y\<close>
      by (metis add.inverse_inverse minus_divide_eq_eq)
    with assms have \<open>f x = f (k *\<^sub>C y)\<close>
      by (simp add: bounded_clinear.axioms(1) clinear.scaleC)
    hence \<open>f x - f (k *\<^sub>C y) = 0\<close>
      by simp
    with assms have s1: \<open>f (x - k *\<^sub>C y) = 0\<close>
      by (simp add: bounded_clinear.axioms(1) complex_vector.linear_diff)
    from that have \<open>k *\<^sub>C y \<in> orthogonal_complement (f -` {0})\<close>
      by (simp add: complex_vector.subspace_scale)
    with xortho have s2: \<open>x - (k *\<^sub>C y) \<in> orthogonal_complement (f -` {0})\<close>
      by (simp add: complex_vector.subspace_diff)
    have s3: \<open>(x - (k *\<^sub>C y)) \<in> f -` {0}\<close>
      using s1 by simp
    moreover have \<open>(f -` {0}) \<inter> (orthogonal_complement (f -` {0})) = {0}\<close>
      by (meson assms closed_csubspace_def complex_vector.subspace_def kernel_is_closed_csubspace
          orthogonal_complement_zero_intersection)
    ultimately have \<open>x - (k *\<^sub>C y) = 0\<close>
      using s2 by blast
    thus ?thesis
      by (metis ceq_vector_fraction_iff eq_iff_diff_eq_0 k_def r1 scaleC_scaleC)
  qed
  then have \<open>orthogonal_complement (f -` {0}) \<subseteq> cspan {x}\<close>
    using complex_vector.span_superset complex_vector.subspace_scale by blast

  moreover from xortho have \<open>orthogonal_complement (f -` {0}) \<supseteq> cspan {x}\<close>
    by (simp add: complex_vector.span_minimal)

  ultimately show ?thesis
    by auto
qed

lemma riesz_representation_existence:
  \<comment> \<open>Theorem 3.4 in \<^cite>\<open>conway2013course\<close>\<close>
  fixes f::\<open>'a::chilbert_space \<Rightarrow> complex\<close>
  assumes a1: \<open>bounded_clinear f\<close>
  shows \<open>\<exists>t. \<forall>x.  f x = t \<bullet>\<^sub>C x\<close>
proof(cases \<open>\<forall> x. f x = 0\<close>)
  case True
  thus ?thesis
    by (metis cinner_zero_left)
next
  case False
  obtain t where spant: \<open>orthogonal_complement (f -` {0}) = cspan {t}\<close>
    using orthogonal_complement_kernel_functional
    using assms by blast
  have \<open>projection (orthogonal_complement (f -` {0})) x = ((t \<bullet>\<^sub>C x)/(t \<bullet>\<^sub>C t)) *\<^sub>C t\<close> for x
    apply (subst spant) by (rule projection_rank1)
  hence \<open>f (projection (orthogonal_complement (f -` {0})) x) = (((t \<bullet>\<^sub>C x))/(t \<bullet>\<^sub>C t)) * (f t)\<close> for x
    using a1 unfolding bounded_clinear_def
    by (simp add: complex_vector.linear_scale)
  hence l2: \<open>f (projection (orthogonal_complement (f -` {0})) x) = ((cnj (f t)/(t \<bullet>\<^sub>C t)) *\<^sub>C t) \<bullet>\<^sub>C x\<close> for x
    using complex_cnj_divide by force
  have \<open>f (projection (f -` {0}) x) = 0\<close> for x
    by (metis (no_types, lifting) assms bounded_clinear_def closed_csubspace.closed
        complex_vector.linear_subspace_vimage complex_vector.subspace_0 complex_vector.subspace_single_0
        csubspace_is_convex insert_absorb insert_not_empty kernel_is_closed_csubspace projection_in_image vimage_singleton_eq)
  hence "\<And>a b. f (projection (f -` {0}) a + b) = 0 + f b"
    using additive.add assms
    by (simp add: bounded_clinear_def complex_vector.linear_add)
  hence "\<And>a. 0 + f (projection (orthogonal_complement (f -` {0})) a) = f a"
    apply (simp add: assms)
    by (metis add.commute diff_add_cancel)
  hence \<open>f x = ((cnj (f t)/(t \<bullet>\<^sub>C t)) *\<^sub>C t) \<bullet>\<^sub>C x\<close> for x
    by (simp add: l2)
  thus ?thesis
    by blast
qed

lemma riesz_representation_unique:
  \<comment> \<open>Theorem 3.4 in \<^cite>\<open>conway2013course\<close>\<close>
  fixes f::\<open>'a::complex_inner \<Rightarrow> complex\<close>
  assumes \<open>\<And>x. f x = (t \<bullet>\<^sub>C x)\<close>
  assumes \<open>\<And>x. f x = (u \<bullet>\<^sub>C x)\<close>
  shows \<open>t = u\<close>
  by (metis add_diff_cancel_left' assms(1) assms(2) cinner_diff_left cinner_gt_zero_iff diff_add_cancel diff_zero)

subsection \<open>Adjoints\<close>

definition "is_cadjoint F G \<longleftrightarrow> (\<forall>x. \<forall>y. (F x \<bullet>\<^sub>C y) = (x \<bullet>\<^sub>C G y))"

lemma is_adjoint_sym:
  \<open>is_cadjoint F G \<Longrightarrow> is_cadjoint G F\<close>
  unfolding is_cadjoint_def apply auto
  by (metis cinner_commute')

definition \<open>cadjoint G = (SOME F. is_cadjoint F G)\<close>
  for G :: "'b::complex_inner \<Rightarrow> 'a::complex_inner"

lemma cadjoint_exists:
  fixes G :: "'b::chilbert_space \<Rightarrow> 'a::complex_inner"
  assumes [simp]: \<open>bounded_clinear G\<close>
  shows \<open>\<exists>F. is_cadjoint F G\<close>
proof -
  include notation_norm
  have [simp]: \<open>clinear G\<close>
    using assms unfolding bounded_clinear_def by blast
  define g :: \<open>'a \<Rightarrow> 'b \<Rightarrow> complex\<close>
    where \<open>g x y = (x \<bullet>\<^sub>C G y)\<close> for x y
  have \<open>bounded_clinear (g x)\<close> for x
  proof -
    have \<open>g x (a + b) = g x a + g x b\<close> for a b
      unfolding g_def
      using additive.add cinner_add_right clinear_def
      by (simp add: cinner_add_right complex_vector.linear_add)
    moreover have  \<open>g x (k *\<^sub>C a) = k *\<^sub>C (g x a)\<close>
      for a k
      unfolding g_def
      by (simp add: complex_vector.linear_scale)
    ultimately have \<open>clinear (g x)\<close>
      by (simp add: clinearI)
    moreover
    have \<open>\<exists> M. \<forall> y. \<parallel> G y \<parallel> \<le> \<parallel> y \<parallel> * M\<close>
      using \<open>bounded_clinear G\<close>
      unfolding bounded_clinear_def bounded_clinear_axioms_def by blast
    then have \<open>\<exists>M. \<forall>y. \<parallel> g x y \<parallel> \<le> \<parallel> y \<parallel> * M\<close>
      using g_def
      by (simp add: bounded_clinear.bounded bounded_clinear_cinner_right_comp)
    ultimately show ?thesis unfolding bounded_linear_def
      using bounded_clinear.intro
      using bounded_clinear_axioms_def by blast
  qed
  hence \<open>\<forall>x. \<exists>t. \<forall>y.  g x y = (t \<bullet>\<^sub>C y)\<close>
    using riesz_representation_existence by blast
  then obtain F where \<open>\<forall>x. \<forall>y. g x y = (F x \<bullet>\<^sub>C y)\<close>
    by metis
  then have \<open>is_cadjoint F G\<close>
    unfolding is_cadjoint_def g_def by simp
  thus ?thesis
    by auto
qed

lemma cadjoint_is_cadjoint[simp]:
  fixes G :: "'b::chilbert_space \<Rightarrow> 'a::complex_inner"
  assumes [simp]: \<open>bounded_clinear G\<close>
  shows \<open>is_cadjoint (cadjoint G) G\<close>
  by (metis assms cadjoint_def cadjoint_exists someI_ex)

lemma is_cadjoint_unique:
  assumes \<open>is_cadjoint F1 G\<close>
  assumes \<open>is_cadjoint F2 G\<close>
  shows \<open>F1 = F2\<close>
  by (metis (full_types) assms(1) assms(2) ext is_cadjoint_def riesz_representation_unique)

lemma cadjoint_univ_prop:
  fixes G :: "'b::chilbert_space \<Rightarrow> 'a::complex_inner"
  assumes a1: \<open>bounded_clinear G\<close>
  shows \<open>cadjoint G x \<bullet>\<^sub>C y = x \<bullet>\<^sub>C G y\<close>
  using assms cadjoint_is_cadjoint is_cadjoint_def by blast

lemma cadjoint_univ_prop':
  fixes G :: "'b::chilbert_space \<Rightarrow> 'a::complex_inner"
  assumes a1: \<open>bounded_clinear G\<close>
  shows \<open>x \<bullet>\<^sub>C cadjoint G y = G x \<bullet>\<^sub>C y\<close>
  by (metis cadjoint_univ_prop assms cinner_commute')

notation cadjoint ("_\<^sup>\<dagger>" [99] 100)

lemma cadjoint_eqI:
  fixes G:: \<open>'b::complex_inner \<Rightarrow> 'a::complex_inner\<close>
    and F:: \<open>'a \<Rightarrow> 'b\<close>
  assumes \<open>\<And>x y. (F x \<bullet>\<^sub>C y) = (x \<bullet>\<^sub>C G y)\<close>
  shows \<open>G\<^sup>\<dagger> = F\<close>
  by (metis assms cadjoint_def is_cadjoint_def is_cadjoint_unique someI_ex)

lemma cadjoint_bounded_clinear:
  fixes A :: "'a::chilbert_space \<Rightarrow> 'b::complex_inner"
  assumes a1: "bounded_clinear A"
  shows \<open>bounded_clinear (A\<^sup>\<dagger>)\<close>
proof
  include notation_norm
  have b1: \<open>((A\<^sup>\<dagger>) x \<bullet>\<^sub>C y) = (x \<bullet>\<^sub>C A y)\<close> for x y
    using cadjoint_univ_prop a1 by auto
  have \<open>is_orthogonal ((A\<^sup>\<dagger>) (x1 + x2) - ((A\<^sup>\<dagger>) x1 + (A\<^sup>\<dagger>) x2)) y\<close> for x1 x2 y
    by (simp add: b1 cinner_diff_left cinner_add_left)
  hence b2: \<open>(A\<^sup>\<dagger>) (x1 + x2) - ((A\<^sup>\<dagger>) x1 + (A\<^sup>\<dagger>) x2) = 0\<close> for x1 x2
    using cinner_eq_zero_iff by blast
  thus z1: \<open>(A\<^sup>\<dagger>) (x1 + x2) = (A\<^sup>\<dagger>) x1 + (A\<^sup>\<dagger>) x2\<close> for x1 x2
    by (simp add: b2 eq_iff_diff_eq_0)

  have f1: \<open>is_orthogonal ((A\<^sup>\<dagger>) (r *\<^sub>C x) - (r *\<^sub>C (A\<^sup>\<dagger>) x )) y\<close> for r x y
    by (simp add: b1 cinner_diff_left)
  thus z2: \<open>(A\<^sup>\<dagger>) (r *\<^sub>C x) = r *\<^sub>C (A\<^sup>\<dagger>) x\<close> for r x
    using cinner_eq_zero_iff eq_iff_diff_eq_0 by blast
  have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 = ((A\<^sup>\<dagger>) x \<bullet>\<^sub>C (A\<^sup>\<dagger>) x)\<close> for x
    by (metis cnorm_eq_square)
  moreover have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 \<ge> 0\<close> for x
    by simp
  ultimately have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 = \<bar> ((A\<^sup>\<dagger>) x \<bullet>\<^sub>C (A\<^sup>\<dagger>) x) \<bar>\<close> for x
    by (metis abs_pos cinner_ge_zero)
  hence \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 = \<bar> (x \<bullet>\<^sub>C A ((A\<^sup>\<dagger>) x)) \<bar>\<close> for x
    by (simp add: b1)
  moreover have  \<open>\<bar>(x \<bullet>\<^sub>C A ((A\<^sup>\<dagger>) x))\<bar> \<le> \<parallel>x\<parallel> *  \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel>\<close> for x
    by (simp add: abs_complex_def complex_inner_class.Cauchy_Schwarz_ineq2 less_eq_complex_def)
  ultimately have b5: \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2  \<le> \<parallel>x\<parallel> * \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel>\<close> for x
    by (metis complex_of_real_mono_iff)
  have \<open>\<exists>M. M \<ge> 0 \<and> (\<forall> x. \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le> M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>)\<close>
    using a1
    by (metis (mono_tags, opaque_lifting) bounded_clinear.bounded linear mult_nonneg_nonpos
        mult_zero_right norm_ge_zero order.trans semiring_normalization_rules(7))
  then obtain M where q1: \<open>M \<ge> 0\<close> and q2: \<open>\<forall> x. \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le> M * \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
    by blast
  have \<open>\<forall> x::'b. \<parallel>x\<parallel> \<ge> 0\<close>
    by simp
  hence b6: \<open>\<parallel>x\<parallel> * \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le>  \<parallel>x\<parallel> * M * \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close> for x
    using q2
    by (smt ordered_comm_semiring_class.comm_mult_left_mono vector_space_over_itself.scale_scale)
  have z3: \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel> \<le> \<parallel>x\<parallel> * M\<close> for x
  proof(cases \<open>\<parallel>(A\<^sup>\<dagger>) x\<parallel> = 0\<close>)
    case True
    thus ?thesis
      by (simp add: \<open>0 \<le> M\<close>)
  next
    case False
    have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 \<le> \<parallel>x\<parallel> *  M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
      by (smt b5 b6)
    thus ?thesis
      by (smt False mult_right_cancel mult_right_mono norm_ge_zero semiring_normalization_rules(29))
  qed
  thus \<open>\<exists>K. \<forall>x. \<parallel>(A\<^sup>\<dagger>) x\<parallel> \<le> \<parallel>x\<parallel> * K\<close>
    by auto
qed

proposition double_cadjoint:
  fixes U :: \<open>'a::chilbert_space \<Rightarrow> 'b::complex_inner\<close>
  assumes a1: "bounded_clinear U"
  shows "U\<^sup>\<dagger>\<^sup>\<dagger> = U"
  by (metis assms cadjoint_def cadjoint_is_cadjoint is_adjoint_sym is_cadjoint_unique someI_ex)

lemma cadjoint_id[simp]: \<open>id\<^sup>\<dagger> = id\<close>
  by (simp add: cadjoint_eqI id_def)

lemma scaleC_cadjoint:
  fixes A::"'a::chilbert_space \<Rightarrow> 'b::complex_inner"
  assumes "bounded_clinear A"
  shows \<open>(\<lambda>t. a *\<^sub>C A t)\<^sup>\<dagger> = (\<lambda>s. cnj a *\<^sub>C (A\<^sup>\<dagger>) s)\<close>
proof -
  have b3: \<open>((\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x \<bullet>\<^sub>C y) = (x \<bullet>\<^sub>C (\<lambda> t. a *\<^sub>C (A t)) y)\<close>
    for x y
    by (simp add: assms cadjoint_univ_prop)

  have "((\<lambda>t. a *\<^sub>C A t)\<^sup>\<dagger>) b = cnj a *\<^sub>C (A\<^sup>\<dagger>) b"
    for b::'b
  proof-
    have "bounded_clinear (\<lambda>t. a *\<^sub>C A t)"
      by (simp add: assms bounded_clinear_const_scaleC)
    thus ?thesis
      by (metis (no_types) cadjoint_eqI b3)
  qed
  thus ?thesis
    by blast
qed


lemma is_projection_on_is_cadjoint:
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes a1: \<open>is_projection_on \<pi> M\<close> and a2: \<open>closed_csubspace M\<close>
  shows \<open>is_cadjoint \<pi> \<pi>\<close>
  by (smt (verit, ccfv_threshold) a1 a2 cinner_diff_left cinner_eq_flip is_cadjoint_def is_projection_on_iff_orthog orthogonal_complement_orthoI right_minus_eq)

lemma is_projection_on_cadjoint:
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes \<open>is_projection_on \<pi> M\<close> and \<open>closed_csubspace M\<close>
  shows \<open>\<pi>\<^sup>\<dagger> = \<pi>\<close>
  using assms is_projection_on_is_cadjoint cadjoint_eqI is_cadjoint_def by blast

lemma projection_cadjoint:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>closed_csubspace M\<close>
  shows \<open>(projection M)\<^sup>\<dagger> = projection M\<close>
  using is_projection_on_cadjoint assms
  by (metis closed_csubspace.closed closed_csubspace.subspace csubspace_is_convex empty_iff orthog_proj_exists projection_is_projection_on)


subsection \<open>More projections\<close>

text \<open>These lemmas logically belong in the "projections" section above but depend on lemmas developed later.\<close>

lemma is_projection_on_plus:
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> is_orthogonal x y"
  assumes \<open>closed_csubspace A\<close>
  assumes \<open>closed_csubspace B\<close>
  assumes \<open>is_projection_on \<pi>A A\<close>
  assumes \<open>is_projection_on \<pi>B B\<close>
  shows \<open>is_projection_on (\<lambda>x. \<pi>A x + \<pi>B x) (A +\<^sub>M B)\<close>
proof (rule is_projection_on_iff_orthog[THEN iffD2, rule_format])
  show clAB: \<open>closed_csubspace (A +\<^sub>M B)\<close>
    by (simp add: assms(2) assms(3) closed_subspace_closed_sum)
  fix h
  have 1: \<open>\<pi>A h + \<pi>B h \<in> A +\<^sub>M B\<close>
    by (meson clAB assms(2) assms(3) assms(4) assms(5) closed_csubspace_def closed_sum_left_subset closed_sum_right_subset complex_vector.subspace_def in_mono is_projection_on_in_image)

  have \<open>\<pi>A (\<pi>B h) = 0\<close>
    by (smt (verit, del_insts) assms(1) assms(2) assms(4) assms(5) cinner_eq_zero_iff is_cadjoint_def is_projection_on_in_image is_projection_on_is_cadjoint)
  then have \<open>h - (\<pi>A h + \<pi>B h) = (h - \<pi>B h) - \<pi>A (h - \<pi>B h)\<close>
    by (smt (verit) add.right_neutral add_diff_cancel_left' assms(2) assms(4) closed_csubspace.subspace complex_vector.subspace_diff diff_add_eq_diff_diff_swap diff_diff_add is_projection_on_iff_orthog orthog_proj_unique orthogonal_complement_closed_subspace)
  also have \<open>\<dots> \<in> orthogonal_complement A\<close>
    using assms(2) assms(4) is_projection_on_iff_orthog by blast
  finally have orthoA: \<open>h - (\<pi>A h + \<pi>B h) \<in> orthogonal_complement A\<close>
    by -

  have \<open>\<pi>B (\<pi>A h) = 0\<close>
    by (smt (verit, del_insts) assms(1) assms(3) assms(4) assms(5) cinner_eq_zero_iff is_cadjoint_def is_projection_on_in_image is_projection_on_is_cadjoint)
  then have \<open>h - (\<pi>A h + \<pi>B h) = (h - \<pi>A h) - \<pi>B (h - \<pi>A h)\<close>
    by (smt (verit) add.right_neutral add_diff_cancel assms(3) assms(5) closed_csubspace.subspace complex_vector.subspace_diff diff_add_eq_diff_diff_swap diff_diff_add is_projection_on_iff_orthog orthog_proj_unique orthogonal_complement_closed_subspace)
  also have \<open>\<dots> \<in> orthogonal_complement B\<close>
    using assms(3) assms(5) is_projection_on_iff_orthog by blast
  finally have orthoB: \<open>h - (\<pi>A h + \<pi>B h) \<in> orthogonal_complement B\<close>
    by -

  from orthoA orthoB
  have 2: \<open>h - (\<pi>A h + \<pi>B h) \<in> orthogonal_complement (A +\<^sub>M B)\<close>
    by (metis IntI assms(2) assms(3) closed_csubspace_def complex_vector.subspace_def de_morgan_orthogonal_complement_plus)

  from 1 2 show \<open>h - (\<pi>A h + \<pi>B h) \<in> orthogonal_complement (A +\<^sub>M B) \<and> \<pi>A h + \<pi>B h \<in> A +\<^sub>M B\<close>
    by simp
qed

lemma projection_plus:
  fixes A B :: "'a::chilbert_space set"
  assumes "\<And>x y. x:A \<Longrightarrow> y:B \<Longrightarrow> is_orthogonal x y"
  assumes \<open>closed_csubspace A\<close>
  assumes \<open>closed_csubspace B\<close>
  shows \<open>projection (A +\<^sub>M B) = (\<lambda>x. projection A x + projection B x)\<close>
proof -
  have \<open>is_projection_on (\<lambda>x. projection A x + projection B x) (A +\<^sub>M B)\<close>
    apply (rule is_projection_on_plus)
    using assms by auto
  then show ?thesis
    by (meson assms(2) assms(3) closed_csubspace.subspace closed_subspace_closed_sum csubspace_is_convex projection_eqI')
qed

lemma is_projection_on_insert:
  assumes ortho: "\<And>s. s \<in> S \<Longrightarrow> is_orthogonal a s"
  assumes \<open>is_projection_on \<pi> (closure (cspan S))\<close>
  assumes \<open>is_projection_on \<pi>a (cspan {a})\<close>
  shows "is_projection_on (\<lambda>x. \<pi>a x + \<pi> x) (closure (cspan (insert a S)))"
proof -
  from ortho
  have \<open>x \<in> cspan {a} \<Longrightarrow> y \<in> closure (cspan S) \<Longrightarrow> is_orthogonal x y\<close> for x y
    using is_orthogonal_cspan is_orthogonal_closure is_orthogonal_sym
    by (smt (verit, ccfv_threshold) empty_iff insert_iff)
  then have \<open>is_projection_on (\<lambda>x. \<pi>a x + \<pi> x) (cspan {a} +\<^sub>M closure (cspan S))\<close>
    apply (rule is_projection_on_plus)
    using assms by (auto simp add: closed_csubspace.intro)
  also have \<open>\<dots> = closure (cspan (insert a S))\<close>
    using closed_sum_cspan[where X=\<open>{a}\<close>] by simp
  finally show ?thesis
    by -
qed

lemma projection_insert:
  fixes a :: \<open>'a::chilbert_space\<close>
  assumes a1: "\<And>s. s \<in> S \<Longrightarrow> is_orthogonal a s"
  shows "projection (closure (cspan (insert a S))) u
        = projection (cspan {a}) u + projection (closure (cspan S)) u"
  using is_projection_on_insert[where S=S, OF a1]
  by (metis (no_types, lifting) closed_closure closed_csubspace.intro closure_is_csubspace complex_vector.subspace_span csubspace_is_convex finite.intros(1) finite.intros(2) finite_cspan_closed_csubspace projection_eqI' projection_is_projection_on')

lemma projection_insert_finite:
  fixes S :: \<open>'a::chilbert_space set\<close>
  assumes a1: "\<And>s. s \<in> S \<Longrightarrow> is_orthogonal a s" and a2: "finite S"
  shows "projection (cspan (insert a S)) u
        = projection (cspan {a}) u + projection (cspan S) u"
  using projection_insert
  by (metis a1 a2 closure_finite_cspan finite.insertI)

subsection \<open>Canonical basis (\<open>onb_enum\<close>)\<close>

setup \<open>Sign.add_const_constraint (\<^const_name>\<open>is_ortho_set\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> bool\<close>)\<close>

class onb_enum = basis_enum + complex_inner +
  assumes is_orthonormal: "is_ortho_set (set canonical_basis)"
    and is_normal: "\<And>x. x \<in> (set canonical_basis) \<Longrightarrow> norm x = 1"

setup \<open>Sign.add_const_constraint (\<^const_name>\<open>is_ortho_set\<close>, SOME \<^typ>\<open>'a::complex_inner set \<Rightarrow> bool\<close>)\<close>

lemma cinner_canonical_basis:
  assumes \<open>i < length (canonical_basis :: 'a::onb_enum list)\<close>
  assumes \<open>j < length (canonical_basis :: 'a::onb_enum list)\<close>
  shows \<open>cinner (canonical_basis!i :: 'a) (canonical_basis!j) = (if i=j then 1 else 0)\<close>
  by (metis assms(1) assms(2) distinct_canonical_basis is_normal is_ortho_set_def is_orthonormal nth_eq_iff_index_eq nth_mem of_real_1 power2_norm_eq_cinner power_one)

lemma canonical_basis_is_onb[simp]: \<open>is_onb (set canonical_basis :: 'a::onb_enum set)\<close>
  by (simp add: is_normal is_onb_def is_orthonormal)

instance onb_enum \<subseteq> chilbert_space
proof
  have \<open>complete (UNIV :: 'a set)\<close>
    using finite_cspan_complete[where B=\<open>set canonical_basis\<close>]
    by simp
  then show "convergent X" if "Cauchy X" for X :: "nat \<Rightarrow> 'a"
    by (simp add: complete_def convergent_def that)
qed

subsection \<open>Conjugate space\<close>

instantiation conjugate_space :: (complex_inner) complex_inner begin
lift_definition cinner_conjugate_space :: "'a conjugate_space \<Rightarrow> 'a conjugate_space \<Rightarrow> complex" is
  \<open>\<lambda>x y. cinner y x\<close>.
instance
  apply (intro_classes; transfer)
       apply (simp_all add: )
    apply (simp add: cinner_add_right)
  using cinner_ge_zero norm_eq_sqrt_cinner by auto
end

instance conjugate_space :: (chilbert_space) chilbert_space..

subsection \<open>Misc (ctd.)\<close>


lemma separating_dense_span: 
  assumes \<open>\<And>F G :: 'a::chilbert_space \<Rightarrow> 'b::{complex_normed_vector,not_singleton}. 
           bounded_clinear F \<Longrightarrow> bounded_clinear G \<Longrightarrow> (\<forall>x\<in>S. F x = G x) \<Longrightarrow> F = G\<close>
  shows \<open>closure (cspan S) = UNIV\<close>
proof -
  have \<open>\<psi> = 0\<close> if \<open>\<psi> \<in> orthogonal_complement S\<close> for \<psi>
  proof -
    obtain \<phi> :: 'b where \<open>\<phi> \<noteq> 0\<close>
      by fastforce
    have \<open>(\<lambda>x. cinner \<psi> x *\<^sub>C \<phi>) = (\<lambda>_. 0)\<close> 
      apply (rule assms[rule_format])
      using orthogonal_complement_orthoI that
      by (auto simp add: bounded_clinear_cinner_right bounded_clinear_scaleC_const)
    then have \<open>cinner \<psi> \<psi> = 0\<close>
      by (meson \<open>\<phi> \<noteq> 0\<close> scaleC_eq_0_iff)
    then show \<open>\<psi> = 0\<close>
      by auto
  qed
  then have \<open>orthogonal_complement (orthogonal_complement S) = UNIV\<close>
    by (metis UNIV_eq_I cinner_zero_right orthogonal_complementI)
  then show \<open>closure (cspan S) = UNIV\<close>
    by (simp add: orthogonal_complement_orthogonal_complement_closure_cspan)
qed

end
