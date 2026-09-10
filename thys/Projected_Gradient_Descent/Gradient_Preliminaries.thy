theory Gradient_Preliminaries
  imports
    "HOL-Analysis.Convex_Euclidean_Space"
    "HOL-Analysis.Lipschitz"
begin

section \<open>Gradient preliminaries\<close>

text \<open>
This theory provides a thin optimization-oriented wrapper around Isabelle/HOL's
existing Fréchet derivative interface.

For a real-valued function on a real inner product space, saying that @{text \<open>f\<close>}
has gradient @{text \<open>g\<close>} at @{text \<open>x\<close>} means that the Fréchet derivative of
@{text \<open>f\<close>} at @{text \<open>x\<close>} is the linear map sending a direction @{text \<open>h\<close>}
to @{text \<open>inner h g\<close>}.  This is the usual gradient convention used in
finite-dimensional optimization.
\<close>


subsection \<open>Pointwise gradients\<close>

definition has_gradient ::
  "('a::real_inner \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "has_gradient f x g \<longleftrightarrow>
     (f has_derivative (\<lambda>h. inner h g)) (at x)"

definition has_gradient_within ::
  "('a::real_inner \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "has_gradient_within f S x g \<longleftrightarrow>
     (f has_derivative (\<lambda>h. inner h g)) (at x within S)"

lemma has_gradientD:
  assumes "has_gradient f x g"
  shows "(f has_derivative (\<lambda>h. inner h g)) (at x)"
  using assms
  unfolding has_gradient_def
  by simp

lemma has_gradientI:
  assumes "(f has_derivative (\<lambda>h. inner h g)) (at x)"
  shows "has_gradient f x g"
  using assms
  unfolding has_gradient_def
  by simp

lemma has_gradient_withinD:
  assumes "has_gradient_within f S x g"
  shows "(f has_derivative (\<lambda>h. inner h g)) (at x within S)"
  using assms
  unfolding has_gradient_within_def
  by simp

lemma has_gradient_withinI:
  assumes "(f has_derivative (\<lambda>h. inner h g)) (at x within S)"
  shows "has_gradient_within f S x g"
  using assms
  unfolding has_gradient_within_def
  by simp

lemma has_gradient_imp_differentiable:
  assumes "has_gradient f x g"
  shows "f differentiable (at x)"
  unfolding differentiable_def
  using has_gradientD[OF assms]
  by blast

lemma has_gradient_within_imp_differentiable:
  assumes "has_gradient_within f S x g"
  shows "f differentiable (at x within S)"
  unfolding differentiable_def
  using has_gradient_withinD[OF assms]
  by blast


subsection \<open>Uniqueness and the gradient operator\<close>

text \<open>
At an unrestricted point, the gradient is unique.  This follows from uniqueness
of the Fréchet derivative and non-degeneracy of the inner product.
\<close>

lemma has_gradient_unique:
  fixes f :: "'a::real_inner \<Rightarrow> real"
  assumes g: "has_gradient f x g"
    and h: "has_gradient f x h"
  shows "g = h"
proof -
  have Dg: "(f has_derivative (\<lambda>v. inner v g)) (at x)"
    using g
    by (rule has_gradientD)

  have Dh: "(f has_derivative (\<lambda>v. inner v h)) (at x)"
    using h
    by (rule has_gradientD)

  have lin_eq: "(\<lambda>v. inner v g) = (\<lambda>v. inner v h)"
    using has_derivative_unique[OF Dg Dh] .

  then have eq: "\<And>v. inner v g = inner v h"
    by (simp add: fun_eq_iff)

  have "inner (g - h) (g - h) = 0"
    using eq[of "g - h"]
    by (simp add: inner_diff_right)

  then have "g - h = 0"
    by simp

  then show "g = h"
    by simp
qed

definition gradient ::
  "('a::real_inner \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "gradient f x = (THE g. has_gradient f x g)"

lemma gradient_eqI:
  assumes "has_gradient f x g"
  shows "gradient f x = g"
  unfolding gradient_def
proof (rule the_equality)
  show "has_gradient f x g"
    using assms .
next
  fix h
  assume "has_gradient f x h"
  then show "h = g"
    using assms has_gradient_unique
    by blast
qed

lemma has_gradient_gradient:
  assumes "has_gradient f x g"
  shows "has_gradient f x (gradient f x)"
  using assms gradient_eqI
  by blast

lemma gradient_eq_iff:
  assumes "has_gradient f x g"
  shows "gradient f x = h \<longleftrightarrow> g = h"
  using gradient_eqI[OF assms]
  by simp


subsection \<open>Gradient fields on sets\<close>

text \<open>
For optimization proofs it is often cleaner to assume a named gradient field
rather than repeatedly unpacking the gradient at every point.
\<close>

definition has_gradient_on ::
  "('a::real_inner \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "has_gradient_on f S G \<longleftrightarrow> (\<forall>x\<in>S. has_gradient f x (G x))"

definition has_gradient_within_on ::
  "('a::real_inner \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "has_gradient_within_on f S G \<longleftrightarrow>
     (\<forall>x\<in>S. has_gradient_within f S x (G x))"

lemma has_gradient_onD:
  assumes "has_gradient_on f S G"
    and "x \<in> S"
  shows "has_gradient f x (G x)"
  using assms
  unfolding has_gradient_on_def
  by auto

lemma has_gradient_within_onD:
  assumes "has_gradient_within_on f S G"
    and "x \<in> S"
  shows "has_gradient_within f S x (G x)"
  using assms
  unfolding has_gradient_within_on_def
  by auto

lemma has_gradient_on_imp_differentiable:
  assumes "has_gradient_on f S G"
    and "x \<in> S"
  shows "f differentiable (at x)"
  using has_gradient_onD[OF assms] has_gradient_imp_differentiable
  by blast

lemma has_gradient_within_on_imp_differentiable:
  assumes "has_gradient_within_on f S G"
    and "x \<in> S"
  shows "f differentiable (at x within S)"
  using has_gradient_within_onD[OF assms] has_gradient_within_imp_differentiable
  by blast


subsection \<open>Elementary gradient rules\<close>

text \<open>
These lemmas are readable wrappers around standard derivative rules.  They are
included here so that later optimization proofs can be stated in gradient
language rather than raw Fréchet derivative language.
\<close>

lemma has_gradient_const [simp]:
  "has_gradient (\<lambda>x. c) x 0"
  unfolding has_gradient_def
  by (auto intro!: derivative_eq_intros)

lemma has_gradient_add:
  assumes "has_gradient f x df"
    and "has_gradient g x dg"
  shows "has_gradient (\<lambda>y. f y + g y) x (df + dg)"
proof -
  have Df: "(f has_derivative (\<lambda>h. inner h df)) (at x)"
    using assms(1)
    by (rule has_gradientD)

  have Dg: "(g has_derivative (\<lambda>h. inner h dg)) (at x)"
    using assms(2)
    by (rule has_gradientD)

  have D: "((\<lambda>y. f y + g y) has_derivative
      (\<lambda>h. inner h df + inner h dg)) (at x)"
    using Df Dg
    by (intro derivative_intros)

  show ?thesis
    unfolding has_gradient_def
    by (rule has_derivative_eq_rhs[OF D])
       (simp add: fun_eq_iff inner_add_right)
qed

lemma has_gradient_minus:
  assumes "has_gradient f x df"
  shows "has_gradient (\<lambda>y. - f y) x (- df)"
proof -
  have Df: "(f has_derivative (\<lambda>h. inner h df)) (at x)"
    using assms
    by (rule has_gradientD)

  have D: "((\<lambda>y. - f y) has_derivative
      (\<lambda>h. - inner h df)) (at x)"
    using Df
    by (intro derivative_intros)

  show ?thesis
    unfolding has_gradient_def
    by (rule has_derivative_eq_rhs[OF D])
       (simp add: fun_eq_iff)
qed

lemma has_gradient_diff:
  assumes "has_gradient f x df"
    and "has_gradient g x dg"
  shows "has_gradient (\<lambda>y. f y - g y) x (df - dg)"
proof -
  have Df: "(f has_derivative (\<lambda>h. inner h df)) (at x)"
    using assms(1)
    by (rule has_gradientD)

  have Dg: "(g has_derivative (\<lambda>h. inner h dg)) (at x)"
    using assms(2)
    by (rule has_gradientD)

  have D: "((\<lambda>y. f y - g y) has_derivative
      (\<lambda>h. inner h df - inner h dg)) (at x)"
    using Df Dg
    by (intro derivative_intros)

  show ?thesis
    unfolding has_gradient_def
    by (rule has_derivative_eq_rhs[OF D])
       (simp add: fun_eq_iff inner_diff_right)
qed

lemma has_gradient_scale_const:
  assumes "has_gradient f x df"
  shows "has_gradient (\<lambda>y. c * f y) x (scaleR c df)"
proof -
  have Df: "(f has_derivative (\<lambda>h. inner h df)) (at x)"
    using assms
    by (rule has_gradientD)

  have D: "((\<lambda>y. c * f y) has_derivative
      (\<lambda>h. c * inner h df)) (at x)"
    using Df
    by (intro derivative_intros)

  show ?thesis
    unfolding has_gradient_def
    by (rule has_derivative_eq_rhs[OF D])
       (simp add: fun_eq_iff)
qed

lemma has_gradient_mult:
  assumes "has_gradient f x df"
    and "has_gradient g x dg"
  shows "has_gradient (\<lambda>y. f y * g y) x
    (scaleR (f x) dg + scaleR (g x) df)"
proof -
  have Df: "(f has_derivative (\<lambda>h. inner h df)) (at x)"
    using assms(1)
    by (rule has_gradientD)

  have Dg: "(g has_derivative (\<lambda>h. inner h dg)) (at x)"
    using assms(2)
    by (rule has_gradientD)

  have D: "((\<lambda>y. f y * g y) has_derivative
      (\<lambda>h. f x * inner h dg + g x * inner h df)) (at x)"
    using has_derivative_mult[OF Df Dg]
    by (simp add: mult.commute)

  have rhs_eq:
    "(\<lambda>h. f x * inner h dg + g x * inner h df) =
     (\<lambda>h. inner h (scaleR (f x) dg + scaleR (g x) df))"
  proof
    fix h
    show "f x * inner h dg + g x * inner h df =
      inner h (scaleR (f x) dg + scaleR (g x) df)"
      by (simp only: inner_add_right inner_scaleR_right)
  qed

  show ?thesis
    unfolding has_gradient_def
    using D
    by (simp only: rhs_eq)
qed

lemma has_gradient_neg_scale_const:
  assumes "has_gradient f x df"
  shows "has_gradient (\<lambda>y. - c * f y) x (scaleR (- c) df)"
  using has_gradient_scale_const[OF assms, of "- c"]
  by simp

subsection \<open>Linear functions and inner products\<close>

text \<open>
The following lemmas are useful for examples and for algebraic rewriting in
projection proofs.
\<close>

lemma has_gradient_inner_left [simp]:
  fixes a x :: "'a::real_inner"
  shows "has_gradient (\<lambda>y. inner a y) x a"
  unfolding has_gradient_def
  by (auto intro!: derivative_eq_intros simp: inner_commute)

lemma has_gradient_inner_right [simp]:
  fixes a x :: "'a::real_inner"
  shows "has_gradient (\<lambda>y. inner y a) x a"
  unfolding has_gradient_def
  by (auto intro!: derivative_eq_intros simp: inner_commute)

lemma has_gradient_inner_diff_left [simp]:
  fixes a b x :: "'a::real_inner"
  shows "has_gradient (\<lambda>y. inner a (y - b)) x a"
proof -
  have D1: "has_gradient (\<lambda>y. inner a y) x a"
    by simp

  have D2: "has_gradient (\<lambda>y. inner a b) x 0"
    by simp

  have D: "has_gradient (\<lambda>y. inner a y - inner a b) x (a - 0)"
    by (rule has_gradient_diff[OF D1 D2])

  then have D': "has_gradient (\<lambda>y. inner a y - inner a b) x a"
    by simp

  have eq: "(\<lambda>y. inner a (y - b)) = (\<lambda>y. inner a y - inner a b)"
  proof
    fix y
    show "inner a (y - b) = inner a y - inner a b"
      by (simp only: inner_diff_right)
  qed

  show ?thesis
    using D'
    by (simp only: eq)
qed

lemma has_gradient_inner_diff_right [simp]:
  fixes a b x :: "'a::real_inner"
  shows "has_gradient (\<lambda>y. inner (y - b) a) x a"
proof -
  have D1: "has_gradient (\<lambda>y. inner y a) x a"
    by simp

  have D2: "has_gradient (\<lambda>y. inner b a) x 0"
    by simp

  have D: "has_gradient (\<lambda>y. inner y a - inner b a) x (a - 0)"
    by (rule has_gradient_diff[OF D1 D2])

  then have D': "has_gradient (\<lambda>y. inner y a - inner b a) x a"
    by simp

  have eq: "(\<lambda>y. inner (y - b) a) = (\<lambda>y. inner y a - inner b a)"
  proof
    fix y
    show "inner (y - b) a = inner y a - inner b a"
      by (simp only: inner_diff_left)
  qed

  show ?thesis
    using D'
    by (simp only: eq)
qed

subsection \<open>Affine lines and directional derivatives\<close>

text \<open>
Gradient descent and projected gradient descent proofs often restrict a
multivariate function to an affine line, namely the map that sends
@{text \<open>t\<close>} to @{text \<open>f (x + scaleR t d)\<close>}.

The derivative of this one-dimensional restriction is the directional derivative

  inner d (gradient f (x + scaleR t d)).
\<close>

definition affine_line ::
  "'a::real_vector \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a"
where
  "affine_line x d t = x + scaleR t d"

definition restrict_to_line ::
  "('a::real_vector \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> real"
where
  "restrict_to_line f x d t = f (affine_line x d t)"

lemma affine_line_0 [simp]:
  "affine_line x d 0 = x"
  unfolding affine_line_def
  by simp

lemma affine_line_1 [simp]:
  "affine_line x d 1 = x + d"
  unfolding affine_line_def
  by simp

lemma affine_line_has_derivative:
  "((affine_line x d) has_derivative (\<lambda>r. scaleR r d)) (at t)"
  unfolding affine_line_def
  by (auto intro!: derivative_eq_intros)

lemma has_gradient_restrict_to_line:
  fixes f :: "'a::real_inner \<Rightarrow> real"
  assumes "has_gradient f (affine_line x d t) g"
  shows "((restrict_to_line f x d) has_field_derivative inner d g) (at t)"
proof -
  have line_deriv:
    "((affine_line x d) has_derivative (\<lambda>r. scaleR r d)) (at t)"
    by (rule affine_line_has_derivative)

  have f_deriv:
    "(f has_derivative (\<lambda>h. inner h g)) (at (affine_line x d t))"
    using assms
    by (rule has_gradientD)

  have comp:
    "((\<lambda>s. f (affine_line x d s)) has_derivative
       (\<lambda>r. inner (scaleR r d) g)) (at t)"
    using has_derivative_compose[OF line_deriv f_deriv]
    by simp

  show ?thesis
    unfolding restrict_to_line_def has_field_derivative_def
    by (rule has_derivative_eq_rhs[OF comp])
       (simp add: fun_eq_iff mult.commute)
qed

lemma has_gradient_restrict_to_line_at_0:
  fixes f :: "'a::real_inner \<Rightarrow> real"
  assumes "has_gradient f x g"
  shows "((\<lambda>t::real. f (x + scaleR t d)) has_field_derivative inner d g) (at 0)"
proof -
  have "has_gradient f (affine_line x d 0) g"
    using assms
    by simp

  then have "((restrict_to_line f x d) has_field_derivative inner d g) (at 0)"
    by (rule has_gradient_restrict_to_line)

  then show ?thesis
    unfolding restrict_to_line_def affine_line_def
    by simp
qed


subsection \<open>Inner-product and norm algebra\<close>

text \<open>
These small algebraic lemmas are intentionally placed early.  Later convergence
proofs repeatedly expand squared norms and telescope inequalities.
\<close>

lemma inner_self_eq_norm_sq:
  fixes x :: "'a::real_inner"
  shows "inner x x = norm x ^ 2"
  by (simp add: power2_norm_eq_inner)

lemma norm_sq_nonneg [simp]:
  fixes x :: "'a::real_inner"
  shows "0 \<le> norm x ^ 2"
  by simp

lemma norm_sq_add:
  fixes x y :: "'a::real_inner"
  shows "norm (x + y) ^ 2 =
    norm x ^ 2 + 2 * inner x y + norm y ^ 2"
proof -
  have "norm (x + y) ^ 2 = inner (x + y) (x + y)"
    by (simp add: power2_norm_eq_inner)
  also have "... = inner x x + inner x y + inner y x + inner y y"
    by (simp only: inner_add_left inner_add_right)
  also have "... = norm x ^ 2 + 2 * inner x y + norm y ^ 2"
    by (simp add: power2_norm_eq_inner inner_commute)
  finally show ?thesis .
qed

lemma norm_sq_diff:
  fixes x y :: "'a::real_inner"
  shows "norm (x - y) ^ 2 =
    norm x ^ 2 - 2 * inner x y + norm y ^ 2"
proof -
  have "norm (x - y) ^ 2 = inner (x - y) (x - y)"
    by (simp add: power2_norm_eq_inner)
  also have "... = inner x x - inner x y - inner y x + inner y y"
    by (simp only: inner_diff_left inner_diff_right)
  also have "... = norm x ^ 2 - 2 * inner x y + norm y ^ 2"
    by (simp add: power2_norm_eq_inner inner_commute)
  finally show ?thesis .
qed

lemma norm_sq_diff_commute:
  fixes x y :: "'a::real_inner"
  shows "norm (x - y) ^ 2 = norm (y - x) ^ 2"
  by (simp add: norm_minus_commute)

lemma inner_diff_self:
  fixes x y :: "'a::real_inner"
  shows "inner (x - y) (x - y) = norm (x - y) ^ 2"
  by (simp add: power2_norm_eq_inner)

lemma inner_le_norm:
  fixes x y :: "'a::real_inner"
  shows "inner x y \<le> norm x * norm y"
  by (rule norm_cauchy_schwarz)

lemma abs_inner_le_norm:
  fixes x y :: "'a::real_inner"
  shows "abs (inner x y) \<le> norm x * norm y"
  by (rule Cauchy_Schwarz_ineq2)


subsection \<open>Optimization-oriented notation helpers\<close>

text \<open>
These are tiny wrappers, but they make later statements read like optimization
rather than raw analysis.
\<close>

definition zero_gradient_at ::
  "('a::real_inner \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> bool"
where
  "zero_gradient_at f x \<longleftrightarrow> has_gradient f x 0"

definition stationary_at ::
  "('a::real_inner \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> bool"
where
  "stationary_at f x \<longleftrightarrow> has_gradient f x 0"

lemma zero_gradient_at_iff_stationary_at:
  "zero_gradient_at f x \<longleftrightarrow> stationary_at f x"
  unfolding zero_gradient_at_def stationary_at_def
  by simp

lemma stationary_atD:
  assumes "stationary_at f x"
  shows "has_gradient f x 0"
  using assms
  unfolding stationary_at_def
  by simp

lemma stationary_atI:
  assumes "has_gradient f x 0"
  shows "stationary_at f x"
  using assms
  unfolding stationary_at_def
  by simp

end