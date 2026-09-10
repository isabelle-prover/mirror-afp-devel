theory Examples_Quadratic
  imports Lipschitz_Smoothness
begin

section \<open>Quadratic examples\<close>

text \<open>
This theory gives a basic one-dimensional quadratic example.

The objective is

  @{text \<open>f x = x^2 / 2\<close>},

with gradient field

  G x = x.

This is the simplest nontrivial example satisfying the smooth convex,
Lipschitz-gradient, and strong-convexity interfaces developed in the previous
theories.

The purpose of this file is not to develop a large collection of examples, but
to demonstrate that the abstract assumptions used in the gradient-descent and
projected-gradient-descent theorems can be instantiated concretely.
\<close>


subsection \<open>The one-dimensional quadratic objective\<close>

definition quadratic_real :: "real \<Rightarrow> real"
where
  "quadratic_real x = x ^ 2 / 2"

definition quadratic_real_gradient :: "real \<Rightarrow> real"
where
  "quadratic_real_gradient x = x"


subsection \<open>Elementary algebra\<close>

lemma quadratic_real_nonnegative:
  "0 \<le> quadratic_real x"
  unfolding quadratic_real_def
  by simp

lemma quadratic_real_zero [simp]:
  "quadratic_real 0 = 0"
  unfolding quadratic_real_def
  by simp

lemma quadratic_real_gradient_zero [simp]:
  "quadratic_real_gradient 0 = 0"
  unfolding quadratic_real_gradient_def
  by simp

lemma quadratic_real_expansion:
  "quadratic_real y =
    quadratic_real x
    + inner (quadratic_real_gradient x) (y - x)
    + (1 / 2) * norm (y - x) ^ 2"
  unfolding quadratic_real_def quadratic_real_gradient_def
  by (simp add: power2_eq_square algebra_simps)

lemma quadratic_real_convex_identity:
  fixes u v x y :: real
  assumes sum_one: "u + v = 1"
  shows
    "u * quadratic_real x + v * quadratic_real y
      - quadratic_real (u * x + v * y)
      = (u * v * (x - y) ^ 2) / 2"
proof -
  have v_eq: "v = 1 - u"
    using sum_one by linarith

  show ?thesis
    unfolding quadratic_real_def
    using v_eq
    by (simp add: power2_eq_square algebra_simps; algebra)
qed

lemma quadratic_real_convex_ineq:
  fixes u v x y :: real
  assumes u_nonneg: "0 \<le> u"
    and v_nonneg: "0 \<le> v"
    and sum_one: "u + v = 1"
  shows
    "quadratic_real (u * x + v * y)
      \<le> u * quadratic_real x + v * quadratic_real y"
proof -
  have identity:
    "u * quadratic_real x + v * quadratic_real y
      - quadratic_real (u * x + v * y)
      = (u * v * (x - y) ^ 2) / 2"
    by (rule quadratic_real_convex_identity[OF sum_one])

  have uv_nonneg: "0 \<le> u * v"
    by (rule mult_nonneg_nonneg[OF u_nonneg v_nonneg])

  have rhs_nonneg: "0 \<le> (u * v * (x - y) ^ 2) / 2"
  proof -
    have "0 \<le> u * v * (x - y) ^ 2"
      by (intro mult_nonneg_nonneg uv_nonneg) simp_all
    then show ?thesis
      by simp
  qed

  show ?thesis
    using identity rhs_nonneg by linarith
qed

lemma quadratic_real_convex_on_UNIV:
  "convex_on UNIV quadratic_real"
  unfolding convex_on_def
proof safe
  show "convex (UNIV::real set)"
    by simp
next
  fix x y u v :: real
  assume u_nonneg: "0 \<le> u"
    and v_nonneg: "0 \<le> v"
    and sum_one: "u + v = 1"

  have
    "quadratic_real (u * x + v * y)
      \<le> u * quadratic_real x + v * quadratic_real y"
    by (rule quadratic_real_convex_ineq[
        OF u_nonneg v_nonneg sum_one])

  then show
    "quadratic_real (u *\<^sub>R x + v *\<^sub>R y)
      \<le> u * quadratic_real x + v * quadratic_real y"
    by simp
qed


subsection \<open>Gradient and convexity\<close>

lemma quadratic_real_has_gradient:
  "has_gradient quadratic_real x (quadratic_real_gradient x)"
  unfolding has_gradient_def quadratic_real_def quadratic_real_gradient_def
  by (auto intro!: derivative_eq_intros simp: power2_eq_square field_simps)

lemma quadratic_real_has_gradient_on_UNIV:
  "has_gradient_on quadratic_real UNIV quadratic_real_gradient"
  unfolding has_gradient_on_def
  using quadratic_real_has_gradient
  by auto

lemma quadratic_real_convex_differentiable_on_UNIV:
  "convex_differentiable_on UNIV quadratic_real quadratic_real_gradient"
proof (rule convex_differentiable_onI)
  show "convex_on UNIV quadratic_real"
    by (rule quadratic_real_convex_on_UNIV)
next
  show "has_gradient_on quadratic_real UNIV quadratic_real_gradient"
    by (rule quadratic_real_has_gradient_on_UNIV)
qed

lemma quadratic_real_convex_differentiable_on:
  assumes convex: "convex C"
  shows "convex_differentiable_on C quadratic_real quadratic_real_gradient"
proof (rule convex_differentiable_on_subset)
  show "convex_differentiable_on UNIV quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_convex_differentiable_on_UNIV)
next
  show "C \<subseteq> UNIV"
    by simp
next
  show "convex C"
    using convex .
qed


subsection \<open>Smoothness and Lipschitz gradients\<close>

lemma quadratic_real_smooth_upper_bound_on_UNIV:
  "smooth_upper_bound_on 1 UNIV quadratic_real quadratic_real_gradient"
proof (rule smooth_upper_bound_onI)
  show "0 \<le> (1::real)"
    by simp
next
  fix x y :: real
  assume "x \<in> UNIV" and "y \<in> UNIV"

  have eq:
    "quadratic_real y =
      quadratic_real x
      + inner (quadratic_real_gradient x) (y - x)
      + (1 / 2) * norm (y - x) ^ 2"
    by (rule quadratic_real_expansion)

  show
    "quadratic_real y
      \<le> quadratic_real x
        + inner (quadratic_real_gradient x) (y - x)
        + (1 / 2) * norm (y - x) ^ 2"
    using eq by simp
qed

lemma quadratic_real_smooth_upper_bound_on:
  assumes "C \<subseteq> UNIV"
  shows "smooth_upper_bound_on 1 C quadratic_real quadratic_real_gradient"
  by (rule smooth_upper_bound_on_subset[
      OF quadratic_real_smooth_upper_bound_on_UNIV assms])

lemma quadratic_real_line_descent_bound_on_UNIV:
  "line_descent_bound_on 1 UNIV quadratic_real quadratic_real_gradient"
  by (rule smooth_upper_bound_on_imp_line_descent_bound_on[
      OF quadratic_real_smooth_upper_bound_on_UNIV])

lemma quadratic_real_lipschitz_gradient_on_UNIV:
  "lipschitz_gradient_on 1 UNIV quadratic_real_gradient"
proof (rule lipschitz_gradient_onI)
  show "0 \<le> (1::real)"
    by simp
next
  fix x y :: real
  assume "x \<in> UNIV" and "y \<in> UNIV"

  show "norm (quadratic_real_gradient x - quadratic_real_gradient y)
      \<le> 1 * norm (x - y)"
    unfolding quadratic_real_gradient_def
    by simp
qed

lemma quadratic_real_lipschitz_gradient_on:
  assumes "C \<subseteq> UNIV"
  shows "lipschitz_gradient_on 1 C quadratic_real_gradient"
  by (rule lipschitz_gradient_on_subset[
      OF quadratic_real_lipschitz_gradient_on_UNIV assms])

lemma quadratic_real_smooth_convex_on_UNIV:
  "smooth_convex_on 1 UNIV quadratic_real quadratic_real_gradient"
proof (rule smooth_convex_onI)
  show "convex_differentiable_on UNIV quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_convex_differentiable_on_UNIV)
next
  show "smooth_upper_bound_on 1 UNIV quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_smooth_upper_bound_on_UNIV)
qed

lemma quadratic_real_smooth_convex_on:
  assumes convex: "convex C"
  shows "smooth_convex_on 1 C quadratic_real quadratic_real_gradient"
proof (rule smooth_convex_on_subset)
  show "smooth_convex_on 1 UNIV quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_smooth_convex_on_UNIV)
next
  show "C \<subseteq> UNIV"
    by simp
next
  show "convex C"
    using convex .
qed

lemma quadratic_real_lipschitz_smooth_on_UNIV:
  "lipschitz_smooth_on 1 UNIV quadratic_real quadratic_real_gradient"
proof (rule lipschitz_smooth_onI)
  show "has_gradient_on quadratic_real UNIV quadratic_real_gradient"
    by (rule quadratic_real_has_gradient_on_UNIV)
next
  show "lipschitz_gradient_on 1 UNIV quadratic_real_gradient"
    by (rule quadratic_real_lipschitz_gradient_on_UNIV)
next
  show "line_descent_bound_on 1 UNIV quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_line_descent_bound_on_UNIV)
qed

lemma quadratic_real_lipschitz_smooth_convex_on_UNIV:
  "lipschitz_smooth_convex_on 1 UNIV quadratic_real quadratic_real_gradient"
proof (rule lipschitz_smooth_convex_onI)
  show "convex_on UNIV quadratic_real"
    by (rule quadratic_real_convex_on_UNIV)
next
  show "lipschitz_smooth_on 1 UNIV quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_lipschitz_smooth_on_UNIV)
qed


subsection \<open>Strong convexity\<close>

lemma quadratic_real_strong_lower_bound_on_UNIV:
  "strong_convex_lower_bound_on 1 UNIV quadratic_real quadratic_real_gradient"
proof (rule strong_convex_lower_bound_onI)
  show "0 \<le> (1::real)"
    by simp
next
  fix x y :: real
  assume "x \<in> UNIV" and "y \<in> UNIV"

  have eq:
    "quadratic_real y =
      quadratic_real x
      + inner (quadratic_real_gradient x) (y - x)
      + (1 / 2) * norm (y - x) ^ 2"
    by (rule quadratic_real_expansion)

  show
    "quadratic_real x
      + inner (quadratic_real_gradient x) (y - x)
      + (1 / 2) * norm (y - x) ^ 2
      \<le> quadratic_real y"
    using eq by simp
qed

lemma quadratic_real_strong_lower_bound_on:
  assumes "C \<subseteq> UNIV"
  shows "strong_convex_lower_bound_on 1 C quadratic_real quadratic_real_gradient"
  by (rule strong_convex_lower_bound_on_subset[
      OF quadratic_real_strong_lower_bound_on_UNIV assms])

lemma quadratic_real_strongly_convex_differentiable_on_UNIV:
  "strongly_convex_differentiable_on 1 UNIV quadratic_real quadratic_real_gradient"
proof (rule strongly_convex_differentiable_onI)
  show "convex_differentiable_on UNIV quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_convex_differentiable_on_UNIV)
next
  show "strong_convex_lower_bound_on 1 UNIV quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_strong_lower_bound_on_UNIV)
qed

lemma quadratic_real_strongly_smooth_convex_on_UNIV:
  "strongly_smooth_convex_on 1 1 UNIV quadratic_real quadratic_real_gradient"
proof (rule strongly_smooth_convex_onI)
  show "smooth_convex_on 1 UNIV quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_smooth_convex_on_UNIV)
next
  show "strong_convex_lower_bound_on 1 UNIV quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_strong_lower_bound_on_UNIV)
qed

lemma quadratic_real_strongly_smooth_convex_on:
  assumes convex: "convex C"
  shows "strongly_smooth_convex_on 1 1 C quadratic_real quadratic_real_gradient"
proof (rule strongly_smooth_convex_on_subset)
  show "strongly_smooth_convex_on 1 1 UNIV quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_strongly_smooth_convex_on_UNIV)
next
  show "C \<subseteq> UNIV"
    by simp
next
  show "convex C"
    using convex .
qed


subsection \<open>Global minimizers\<close>

lemma quadratic_real_global_min_on_zero:
  assumes zero_mem: "0 \<in> C"
  shows "global_min_on C quadratic_real 0"
proof (rule global_min_onI)
  show "0 \<in> C"
    using zero_mem .
next
  fix y
  assume "y \<in> C"

  show "quadratic_real 0 \<le> quadratic_real y"
    using quadratic_real_nonnegative[of y]
    by simp
qed

lemma quadratic_real_global_min_UNIV:
  "global_min_on UNIV quadratic_real 0"
  by (rule quadratic_real_global_min_on_zero) simp

lemma quadratic_real_unique_global_min_on:
  assumes convex: "convex C"
    and zero_mem: "0 \<in> C"
    and minimizer: "global_min_on C quadratic_real x"
  shows "x = 0"
proof -
  have strong: "strongly_smooth_convex_on 1 1 C quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_strongly_smooth_convex_on[OF convex])

  have min_zero: "global_min_on C quadratic_real 0"
    by (rule quadratic_real_global_min_on_zero[OF zero_mem])

  have "x = 0"
    by (rule strongly_smooth_convex_global_min_unique[
        where L = 1 and mu = 1 and G = quadratic_real_gradient,
        OF strong _ minimizer min_zero])
      simp

  then show ?thesis .
qed


subsection \<open>Unconstrained gradient descent example\<close>

lemma quadratic_real_gradient_descent_function_value_gap_bound:
  assumes gd: "gradient_descent_iterates alpha quadratic_real_gradient x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
  shows
    "quadratic_real (x N) - quadratic_real 0
      \<le> norm (x 0 - 0) ^ 2 / (2 * alpha * real N)"
proof -
  have feasible: "feasible_iterates UNIV x"
    by (rule feasible_iteratesI) simp

  have step_size': "alpha * 1 \<le> 1"
    using step_size by simp

  show ?thesis
    by (rule gradient_descent_function_value_gap_bound[
        OF quadratic_real_smooth_convex_on_UNIV gd feasible alpha_pos
           step_size' quadratic_real_global_min_UNIV N_pos])
qed

lemma quadratic_real_gradient_descent_function_value_gap_bound_simplified:
  assumes gd: "gradient_descent_iterates alpha quadratic_real_gradient x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
  shows
    "quadratic_real (x N)
      \<le> norm (x 0) ^ 2 / (2 * alpha * real N)"
  using quadratic_real_gradient_descent_function_value_gap_bound[
      OF gd alpha_pos step_size N_pos]
  by simp


subsection \<open>Projected gradient descent example\<close>

lemma quadratic_real_projected_gradient_descent_function_value_gap_bound:
  assumes closed: "closed C"
    and convex: "convex C"
    and zero_mem: "0 \<in> C"
    and pgd: "projected_gradient_descent_iterates C alpha quadratic_real_gradient x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
  shows
    "quadratic_real (x N) - quadratic_real 0
      \<le> norm (x 0 - 0) ^ 2 / (2 * alpha * real N)"
proof -
  have smooth: "smooth_convex_on 1 C quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_smooth_convex_on[OF convex])

  have minimizer: "global_min_on C quadratic_real 0"
    by (rule quadratic_real_global_min_on_zero[OF zero_mem])

  have step_size': "alpha * 1 \<le> 1"
    using step_size by simp

  show ?thesis
    by (rule projected_gradient_descent_function_value_gap_bound[
        OF smooth closed convex pgd x0_mem alpha_pos step_size'
           minimizer N_pos])
qed

lemma quadratic_real_projected_gradient_descent_function_value_gap_bound_simplified:
  assumes closed: "closed C"
    and convex: "convex C"
    and zero_mem: "0 \<in> C"
    and pgd: "projected_gradient_descent_iterates C alpha quadratic_real_gradient x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
  shows
    "quadratic_real (x N)
      \<le> norm (x 0) ^ 2 / (2 * alpha * real N)"
  using quadratic_real_projected_gradient_descent_function_value_gap_bound[
      OF closed convex zero_mem pgd x0_mem alpha_pos step_size N_pos]
  by simp

lemma quadratic_real_projected_gradient_descent_distance_linear_rate:
  assumes closed: "closed C"
    and convex: "convex C"
    and zero_mem: "0 \<in> C"
    and pgd: "projected_gradient_descent_iterates C alpha quadratic_real_gradient x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
  shows
    "norm (x N - 0) ^ 2
      \<le> projected_gradient_linear_rate_factor alpha 1 ^ N
          * norm (x 0 - 0) ^ 2"
proof -
  have strong: "strongly_smooth_convex_on 1 1 C quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_strongly_smooth_convex_on[OF convex])

  have minimizer: "global_min_on C quadratic_real 0"
    by (rule quadratic_real_global_min_on_zero[OF zero_mem])

  have step_size': "alpha * 1 \<le> 1"
    using step_size by simp

  show ?thesis
    by (rule projected_gradient_descent_distance_sq_linear_rate[
        OF strong closed convex pgd x0_mem alpha_pos step_size' minimizer,
        of N])
qed

lemma quadratic_real_projected_gradient_descent_distance_linear_rate_simplified:
  assumes closed: "closed C"
    and convex: "convex C"
    and zero_mem: "0 \<in> C"
    and pgd: "projected_gradient_descent_iterates C alpha quadratic_real_gradient x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
  shows
    "norm (x N) ^ 2
      \<le> projected_gradient_linear_rate_factor alpha 1 ^ N
          * norm (x 0) ^ 2"
  using quadratic_real_projected_gradient_descent_distance_linear_rate[
      OF closed convex zero_mem pgd x0_mem alpha_pos step_size,
      of N]
  by simp


text \<open>
This file demonstrates that the abstract assumptions used throughout the
development are non-vacuous.  The one-dimensional quadratic objective satisfies
the gradient, convexity, smoothness, Lipschitz-gradient, and strong-convexity
interfaces with constants L = 1 and mu = 1.

The final lemmas instantiate both the O(1/N) projected-gradient theorem and the
linear distance-rate theorem for this concrete objective.
\<close>

end