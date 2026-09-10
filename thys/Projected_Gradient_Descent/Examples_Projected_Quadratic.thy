theory Examples_Projected_Quadratic
  imports
    Examples_Quadratic
    Projected_Gradient_Descent_Residual_Convergence
begin

section \<open>Projected quadratic examples\<close>

text \<open>
This theory gives concrete constrained examples for the projected-gradient
descent library.

The objective is the one-dimensional quadratic @{text \<open>f x = x^2 / 2\<close>} with gradient
field G x = x.  The previous example theory instantiated the smoothness,
convexity, and strong-convexity interfaces for this objective.  Here we use
those facts to instantiate the projected-gradient mapping residual bounds and
the finite-horizon epsilon-stationarity certificates.
\<close>


subsection \<open>A reusable constrained quadratic template\<close>

text \<open>
The first group of lemmas works for any closed convex feasible set containing
the unconstrained minimizer 0.  This gives a small reusable template for
instantiating the abstract projected-gradient descent theorems on concrete
quadratic constrained problems.
\<close>

lemma quadratic_real_projected_gradient_descent_exists_small_residual_sq:
  assumes closed: "closed C"
    and convex: "convex C"
    and zero_mem: "0 \<in> C"
    and pgd: "projected_gradient_descent_iterates C alpha quadratic_real_gradient x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
  shows
    "\<exists>n<N.
      projected_gradient_residual_sq C alpha quadratic_real_gradient (x n)
        \<le> (2 / (alpha * real N)) * quadratic_real (x 0)"
proof -
  have smooth: "smooth_convex_on 1 C quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_smooth_convex_on[OF convex])

  have minimizer: "global_min_on C quadratic_real 0"
    by (rule quadratic_real_global_min_on_zero[OF zero_mem])

  have step_size': "alpha * 1 \<le> 1"
    using step_size by simp

  have result:
    "\<exists>n<N.
      projected_gradient_residual_sq C alpha quadratic_real_gradient (x n)
        \<le> (2 / (alpha * real N)) * (quadratic_real (x 0) - quadratic_real 0)"
    by (rule projected_gradient_descent_exists_small_residual_sq_to_minimizer[
      OF smooth closed convex pgd x0_mem alpha_pos step_size' minimizer N_pos])

  then show ?thesis
    by simp
qed

lemma quadratic_real_projected_gradient_descent_exists_epsilon_residual:
  assumes closed: "closed C"
    and convex: "convex C"
    and zero_mem: "0 \<in> C"
    and pgd: "projected_gradient_descent_iterates C alpha quadratic_real_gradient x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
    and eps_pos: "0 < eps"
    and horizon:
      "2 * quadratic_real (x 0) \<le> alpha * real N * eps ^ 2"
  shows
    "\<exists>n<N. projected_gradient_residual C alpha quadratic_real_gradient (x n) \<le> eps"
proof -
  have smooth: "smooth_convex_on 1 C quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_smooth_convex_on[OF convex])

  have minimizer: "global_min_on C quadratic_real 0"
    by (rule quadratic_real_global_min_on_zero[OF zero_mem])

  have step_size': "alpha * 1 \<le> 1"
    using step_size by simp

  have horizon':
    "2 * (quadratic_real (x 0) - quadratic_real 0)
      \<le> alpha * real N * eps ^ 2"
    using horizon by simp

  show ?thesis
    by (rule projected_gradient_descent_exists_epsilon_residual_to_minimizer_product[
      OF smooth closed convex pgd x0_mem alpha_pos step_size' minimizer
         N_pos eps_pos horizon'])
qed

lemma quadratic_real_projected_gradient_residual_zero_imp_zero:
  assumes closed: "closed C"
    and convex: "convex C"
    and zero_mem: "0 \<in> C"
    and x_mem: "x \<in> C"
    and alpha_pos: "0 < alpha"
    and zero:
      "projected_gradient_residual C alpha quadratic_real_gradient x = 0"
  shows "x = 0"
proof -
  have smooth: "smooth_convex_on 1 C quadratic_real quadratic_real_gradient"
    by (rule quadratic_real_smooth_convex_on[OF convex])

  have minimizer: "global_min_on C quadratic_real x"
    by (rule projected_gradient_residual_zero_imp_global_min_on[
      OF smooth closed convex x_mem alpha_pos zero])

  show "x = 0"
    by (rule quadratic_real_unique_global_min_on[
      OF convex zero_mem minimizer])
qed


subsection \<open>The nonnegative half-line\<close>

text \<open>
We now specialize the previous template to the concrete closed convex feasible
set [0,∞).  This is a simple constrained problem whose minimizer lies on the
feasible set and whose projected-gradient residual certificates follow directly
from the abstract theory.
\<close>

definition nonnegative_real :: "real set"
where
  "nonnegative_real = {0..}"

lemma nonnegative_real_iff [simp]:
  "x \<in> nonnegative_real \<longleftrightarrow> 0 \<le> x"
  unfolding nonnegative_real_def by simp

lemma zero_mem_nonnegative_real [simp]:
  "0 \<in> nonnegative_real"
  unfolding nonnegative_real_def by simp

lemma closed_nonnegative_real:
  "closed nonnegative_real"
  unfolding nonnegative_real_def by simp

lemma convex_nonnegative_real:
  "convex nonnegative_real"
  unfolding nonnegative_real_def by simp

lemma quadratic_real_smooth_convex_on_nonnegative:
  "smooth_convex_on 1 nonnegative_real quadratic_real quadratic_real_gradient"
  by (rule quadratic_real_smooth_convex_on[OF convex_nonnegative_real])

lemma quadratic_real_strongly_smooth_convex_on_nonnegative:
  "strongly_smooth_convex_on 1 1 nonnegative_real
    quadratic_real quadratic_real_gradient"
  by (rule quadratic_real_strongly_smooth_convex_on[OF convex_nonnegative_real])

lemma quadratic_real_global_min_on_nonnegative_zero:
  "global_min_on nonnegative_real quadratic_real 0"
  by (rule quadratic_real_global_min_on_zero) simp

lemma quadratic_real_unique_global_min_on_nonnegative:
  assumes minimizer: "global_min_on nonnegative_real quadratic_real x"
  shows "x = 0"
  by (rule quadratic_real_unique_global_min_on[
    OF convex_nonnegative_real zero_mem_nonnegative_real minimizer])


subsection \<open>Projected-gradient step on the nonnegative half-line\<close>

text \<open>
The projected-gradient step for the quadratic objective can be unfolded to the
projection of the scalar point (1 - alpha) * x onto the half-line.  We do not
need a closed-form formula for this projection in order to instantiate the
convergence theory.
\<close>

lemma nonnegative_quadratic_projected_gradient_step_unfold:
  "projected_gradient_step nonnegative_real alpha quadratic_real_gradient x =
    closest_point nonnegative_real ((1 - alpha) * x)"
  unfolding projected_gradient_step_def gradient_step_def quadratic_real_gradient_def
  by (simp add: algebra_simps)

lemma nonnegative_quadratic_projected_gradient_mapping_unfold:
  "projected_gradient_mapping nonnegative_real alpha quadratic_real_gradient x =
    (1 / alpha) * (x - closest_point nonnegative_real ((1 - alpha) * x))"
  unfolding projected_gradient_mapping_def
  by (simp add: nonnegative_quadratic_projected_gradient_step_unfold)

lemma nonnegative_quadratic_projected_gradient_residual_unfold:
  "projected_gradient_residual nonnegative_real alpha quadratic_real_gradient x =
    norm ((1 / alpha) * (x - closest_point nonnegative_real ((1 - alpha) * x)))"
  unfolding projected_gradient_residual_def
  by (simp add: nonnegative_quadratic_projected_gradient_mapping_unfold)

lemma nonnegative_quadratic_projected_gradient_residual_sq_unfold:
  "projected_gradient_residual_sq nonnegative_real alpha quadratic_real_gradient x =
    norm ((1 / alpha) * (x - closest_point nonnegative_real ((1 - alpha) * x))) ^ 2"
  unfolding projected_gradient_residual_sq_def
  by (simp add: nonnegative_quadratic_projected_gradient_mapping_unfold)


subsection \<open>Function-value convergence on the half-line\<close>

lemma nonnegative_quadratic_projected_gradient_descent_function_value_gap_bound:
  assumes pgd:
      "projected_gradient_descent_iterates nonnegative_real alpha
        quadratic_real_gradient x"
    and x0_nonneg: "0 \<le> x 0"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
  shows
    "quadratic_real (x N)
      \<le> norm (x 0) ^ 2 / (2 * alpha * real N)"
proof -
  have x0_mem: "x 0 \<in> nonnegative_real"
    using x0_nonneg by simp

  show ?thesis
    by (rule quadratic_real_projected_gradient_descent_function_value_gap_bound_simplified[
      OF closed_nonnegative_real convex_nonnegative_real zero_mem_nonnegative_real
         pgd x0_mem alpha_pos step_size N_pos])
qed

lemma nonnegative_quadratic_projected_gradient_descent_distance_linear_rate:
  assumes pgd:
      "projected_gradient_descent_iterates nonnegative_real alpha
        quadratic_real_gradient x"
    and x0_nonneg: "0 \<le> x 0"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
  shows
    "norm (x N) ^ 2
      \<le> projected_gradient_linear_rate_factor alpha 1 ^ N * norm (x 0) ^ 2"
proof -
  have x0_mem: "x 0 \<in> nonnegative_real"
    using x0_nonneg by simp

  show ?thesis
    by (rule quadratic_real_projected_gradient_descent_distance_linear_rate_simplified[
      OF closed_nonnegative_real convex_nonnegative_real zero_mem_nonnegative_real
         pgd x0_mem alpha_pos step_size])
qed


subsection \<open>Projected-gradient residual bounds on the half-line\<close>

lemma nonnegative_quadratic_projected_gradient_descent_exists_small_residual_sq:
  assumes pgd:
      "projected_gradient_descent_iterates nonnegative_real alpha
        quadratic_real_gradient x"
    and x0_nonneg: "0 \<le> x 0"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
  shows
    "\<exists>n<N.
      projected_gradient_residual_sq nonnegative_real alpha
        quadratic_real_gradient (x n)
        \<le> (2 / (alpha * real N)) * quadratic_real (x 0)"
proof -
  have x0_mem: "x 0 \<in> nonnegative_real"
    using x0_nonneg by simp

  show ?thesis
    by (rule quadratic_real_projected_gradient_descent_exists_small_residual_sq[
      OF closed_nonnegative_real convex_nonnegative_real zero_mem_nonnegative_real
         pgd x0_mem alpha_pos step_size N_pos])
qed

lemma nonnegative_quadratic_projected_gradient_descent_exists_epsilon_residual:
  assumes pgd:
      "projected_gradient_descent_iterates nonnegative_real alpha
        quadratic_real_gradient x"
    and x0_nonneg: "0 \<le> x 0"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
    and eps_pos: "0 < eps"
    and horizon:
      "2 * quadratic_real (x 0) \<le> alpha * real N * eps ^ 2"
  shows
    "\<exists>n<N.
      projected_gradient_residual nonnegative_real alpha
        quadratic_real_gradient (x n) \<le> eps"
proof -
  have x0_mem: "x 0 \<in> nonnegative_real"
    using x0_nonneg by simp

  show ?thesis
    by (rule quadratic_real_projected_gradient_descent_exists_epsilon_residual[
      OF closed_nonnegative_real convex_nonnegative_real zero_mem_nonnegative_real
         pgd x0_mem alpha_pos step_size N_pos eps_pos horizon])
qed

lemma nonnegative_quadratic_projected_gradient_descent_exists_epsilon_residual_product_form:
  assumes pgd:
      "projected_gradient_descent_iterates nonnegative_real alpha
        quadratic_real_gradient x"
    and x0_nonneg: "0 \<le> x 0"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
    and eps_pos: "0 < eps"
    and horizon:
      "quadratic_real (x 0) \<le> (alpha * real N * eps ^ 2) / 2"
  shows
    "\<exists>n<N.
      projected_gradient_residual nonnegative_real alpha
        quadratic_real_gradient (x n) \<le> eps"
proof -
  have horizon':
    "2 * quadratic_real (x 0) \<le> alpha * real N * eps ^ 2"
    using horizon by simp

  show ?thesis
    by (rule nonnegative_quadratic_projected_gradient_descent_exists_epsilon_residual[
      OF pgd x0_nonneg alpha_pos step_size N_pos eps_pos horizon'])
qed


subsection \<open>Residual-zero certificate on the half-line\<close>

lemma nonnegative_quadratic_projected_gradient_residual_zero_imp_zero:
  assumes x_nonneg: "0 \<le> x"
    and alpha_pos: "0 < alpha"
    and zero:
      "projected_gradient_residual nonnegative_real alpha
        quadratic_real_gradient x = 0"
  shows "x = 0"
proof -
  have x_mem: "x \<in> nonnegative_real"
    using x_nonneg by simp

  show "x = 0"
    by (rule quadratic_real_projected_gradient_residual_zero_imp_zero[
      OF closed_nonnegative_real convex_nonnegative_real zero_mem_nonnegative_real
         x_mem alpha_pos zero])
qed

lemma nonnegative_quadratic_projected_gradient_residual_zero_imp_global_min:
  assumes x_nonneg: "0 \<le> x"
    and alpha_pos: "0 < alpha"
    and zero:
      "projected_gradient_residual nonnegative_real alpha
        quadratic_real_gradient x = 0"
  shows "global_min_on nonnegative_real quadratic_real x"
proof -
  have x_mem: "x \<in> nonnegative_real"
    using x_nonneg by simp

  show ?thesis
    by (rule projected_gradient_residual_zero_imp_global_min_on[
      OF quadratic_real_smooth_convex_on_nonnegative
         closed_nonnegative_real convex_nonnegative_real
         x_mem alpha_pos zero])
qed

subsection \<open>A bounded interval constraint\<close>

text \<open>
We also instantiate the projected-gradient library on a bounded interval
constraint [a,b] containing the unconstrained minimizer 0.  This gives a more
concrete constrained example than the nonnegative half-line, while still using
the same abstract projected-gradient convergence and residual machinery.

The point of this example is that no closed-form formula for the projection is
needed.  The metric projection and its variational inequality are supplied by
the general projection-geometry layer.
\<close>

definition bounded_interval_real :: "real \<Rightarrow> real \<Rightarrow> real set"
where
  "bounded_interval_real a b = {a..b}"

lemma bounded_interval_real_iff [simp]:
  "x \<in> bounded_interval_real a b \<longleftrightarrow> a \<le> x \<and> x \<le> b"
  unfolding bounded_interval_real_def by simp

lemma zero_mem_bounded_interval_real [simp]:
  assumes "a \<le> 0"
    and "0 \<le> b"
  shows "0 \<in> bounded_interval_real a b"
  using assms
  unfolding bounded_interval_real_def
  by simp

lemma closed_bounded_interval_real:
  "closed (bounded_interval_real a b)"
  unfolding bounded_interval_real_def by simp

lemma convex_bounded_interval_real:
  "convex (bounded_interval_real a b)"
  unfolding bounded_interval_real_def by simp

lemma quadratic_real_smooth_convex_on_bounded_interval:
  "smooth_convex_on 1 (bounded_interval_real a b)
    quadratic_real quadratic_real_gradient"
  by (rule quadratic_real_smooth_convex_on[
      OF convex_bounded_interval_real])

lemma quadratic_real_strongly_smooth_convex_on_bounded_interval:
  "strongly_smooth_convex_on 1 1 (bounded_interval_real a b)
    quadratic_real quadratic_real_gradient"
  by (rule quadratic_real_strongly_smooth_convex_on[
      OF convex_bounded_interval_real])

lemma quadratic_real_global_min_on_bounded_interval_zero:
  assumes a0: "a \<le> 0"
    and b0: "0 \<le> b"
  shows "global_min_on (bounded_interval_real a b) quadratic_real 0"
  by (rule quadratic_real_global_min_on_zero[
      OF zero_mem_bounded_interval_real[OF a0 b0]])

lemma quadratic_real_unique_global_min_on_bounded_interval:
  assumes a0: "a \<le> 0"
    and b0: "0 \<le> b"
    and minimizer:
      "global_min_on (bounded_interval_real a b) quadratic_real x"
  shows "x = 0"
  by (rule quadratic_real_unique_global_min_on[
      OF convex_bounded_interval_real
         zero_mem_bounded_interval_real[OF a0 b0]
         minimizer])


subsection \<open>Projected-gradient step on a bounded interval\<close>

text \<open>
For the quadratic objective, the projected-gradient step is the projection of
(1 - alpha) * x onto the interval [a,b].
\<close>

lemma bounded_interval_quadratic_projected_gradient_step_unfold:
  "projected_gradient_step (bounded_interval_real a b) alpha
      quadratic_real_gradient x =
    closest_point (bounded_interval_real a b) ((1 - alpha) * x)"
  unfolding projected_gradient_step_def gradient_step_def
    quadratic_real_gradient_def
  by (simp add: algebra_simps)

lemma bounded_interval_quadratic_projected_gradient_mapping_unfold:
  "projected_gradient_mapping (bounded_interval_real a b) alpha
      quadratic_real_gradient x =
    (1 / alpha) *
      (x - closest_point (bounded_interval_real a b) ((1 - alpha) * x))"
  unfolding projected_gradient_mapping_def
  by (simp add: bounded_interval_quadratic_projected_gradient_step_unfold)

lemma bounded_interval_quadratic_projected_gradient_residual_unfold:
  "projected_gradient_residual (bounded_interval_real a b) alpha
      quadratic_real_gradient x =
    norm ((1 / alpha) *
      (x - closest_point (bounded_interval_real a b) ((1 - alpha) * x)))"
  unfolding projected_gradient_residual_def
  by (simp add: bounded_interval_quadratic_projected_gradient_mapping_unfold)

lemma bounded_interval_quadratic_projected_gradient_residual_sq_unfold:
  "projected_gradient_residual_sq (bounded_interval_real a b) alpha
      quadratic_real_gradient x =
    norm ((1 / alpha) *
      (x - closest_point (bounded_interval_real a b) ((1 - alpha) * x))) ^ 2"
  unfolding projected_gradient_residual_sq_def
  by (simp add: bounded_interval_quadratic_projected_gradient_mapping_unfold)


subsection \<open>Function-value convergence on a bounded interval\<close>

lemma bounded_interval_quadratic_projected_gradient_descent_function_value_gap_bound:
  assumes a0: "a \<le> 0"
    and b0: "0 \<le> b"
    and pgd:
      "projected_gradient_descent_iterates (bounded_interval_real a b) alpha
        quadratic_real_gradient x"
    and x0_lower: "a \<le> x 0"
    and x0_upper: "x 0 \<le> b"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
  shows
    "quadratic_real (x N)
      \<le> norm (x 0) ^ 2 / (2 * alpha * real N)"
proof -
  have zero_mem: "0 \<in> bounded_interval_real a b"
    by (rule zero_mem_bounded_interval_real[OF a0 b0])

  have x0_mem: "x 0 \<in> bounded_interval_real a b"
    using x0_lower x0_upper by simp

  show ?thesis
    by (rule quadratic_real_projected_gradient_descent_function_value_gap_bound_simplified[
      OF closed_bounded_interval_real convex_bounded_interval_real zero_mem
         pgd x0_mem alpha_pos step_size N_pos])
qed

lemma bounded_interval_quadratic_projected_gradient_descent_distance_linear_rate:
  assumes a0: "a \<le> 0"
    and b0: "0 \<le> b"
    and pgd:
      "projected_gradient_descent_iterates (bounded_interval_real a b) alpha
        quadratic_real_gradient x"
    and x0_lower: "a \<le> x 0"
    and x0_upper: "x 0 \<le> b"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
  shows
    "norm (x N) ^ 2
      \<le> projected_gradient_linear_rate_factor alpha 1 ^ N * norm (x 0) ^ 2"
proof -
  have zero_mem: "0 \<in> bounded_interval_real a b"
    by (rule zero_mem_bounded_interval_real[OF a0 b0])

  have x0_mem: "x 0 \<in> bounded_interval_real a b"
    using x0_lower x0_upper by simp

  show ?thesis
    by (rule quadratic_real_projected_gradient_descent_distance_linear_rate_simplified[
      OF closed_bounded_interval_real convex_bounded_interval_real zero_mem
         pgd x0_mem alpha_pos step_size])
qed


subsection \<open>Projected-gradient residual bounds on a bounded interval\<close>

lemma bounded_interval_quadratic_projected_gradient_descent_exists_small_residual_sq:
  assumes a0: "a \<le> 0"
    and b0: "0 \<le> b"
    and pgd:
      "projected_gradient_descent_iterates (bounded_interval_real a b) alpha
        quadratic_real_gradient x"
    and x0_lower: "a \<le> x 0"
    and x0_upper: "x 0 \<le> b"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
  shows
    "\<exists>n<N.
      projected_gradient_residual_sq (bounded_interval_real a b) alpha
        quadratic_real_gradient (x n)
        \<le> (2 / (alpha * real N)) * quadratic_real (x 0)"
proof -
  have zero_mem: "0 \<in> bounded_interval_real a b"
    by (rule zero_mem_bounded_interval_real[OF a0 b0])

  have x0_mem: "x 0 \<in> bounded_interval_real a b"
    using x0_lower x0_upper by simp

  show ?thesis
    by (rule quadratic_real_projected_gradient_descent_exists_small_residual_sq[
      OF closed_bounded_interval_real convex_bounded_interval_real zero_mem
         pgd x0_mem alpha_pos step_size N_pos])
qed

lemma bounded_interval_quadratic_projected_gradient_descent_exists_epsilon_residual:
  assumes a0: "a \<le> 0"
    and b0: "0 \<le> b"
    and pgd:
      "projected_gradient_descent_iterates (bounded_interval_real a b) alpha
        quadratic_real_gradient x"
    and x0_lower: "a \<le> x 0"
    and x0_upper: "x 0 \<le> b"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
    and eps_pos: "0 < eps"
    and horizon:
      "2 * quadratic_real (x 0) \<le> alpha * real N * eps ^ 2"
  shows
    "\<exists>n<N.
      projected_gradient_residual (bounded_interval_real a b) alpha
        quadratic_real_gradient (x n) \<le> eps"
proof -
  have zero_mem: "0 \<in> bounded_interval_real a b"
    by (rule zero_mem_bounded_interval_real[OF a0 b0])

  have x0_mem: "x 0 \<in> bounded_interval_real a b"
    using x0_lower x0_upper by simp

  show ?thesis
    by (rule quadratic_real_projected_gradient_descent_exists_epsilon_residual[
      OF closed_bounded_interval_real convex_bounded_interval_real zero_mem
         pgd x0_mem alpha_pos step_size N_pos eps_pos horizon])
qed

lemma bounded_interval_quadratic_projected_gradient_descent_exists_epsilon_residual_product_form:
  assumes a0: "a \<le> 0"
    and b0: "0 \<le> b"
    and pgd:
      "projected_gradient_descent_iterates (bounded_interval_real a b) alpha
        quadratic_real_gradient x"
    and x0_lower: "a \<le> x 0"
    and x0_upper: "x 0 \<le> b"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha \<le> 1"
    and N_pos: "N > 0"
    and eps_pos: "0 < eps"
    and horizon:
      "quadratic_real (x 0) \<le> (alpha * real N * eps ^ 2) / 2"
  shows
    "\<exists>n<N.
      projected_gradient_residual (bounded_interval_real a b) alpha
        quadratic_real_gradient (x n) \<le> eps"
proof -
  have horizon':
    "2 * quadratic_real (x 0) \<le> alpha * real N * eps ^ 2"
    using horizon by simp

  show ?thesis
    by (rule bounded_interval_quadratic_projected_gradient_descent_exists_epsilon_residual[
      OF a0 b0 pgd x0_lower x0_upper alpha_pos step_size N_pos
         eps_pos horizon'])
qed


subsection \<open>Residual-zero certificate on a bounded interval\<close>

lemma bounded_interval_quadratic_projected_gradient_residual_zero_imp_zero:
  assumes a0: "a \<le> 0"
    and b0: "0 \<le> b"
    and x_lower: "a \<le> x"
    and x_upper: "x \<le> b"
    and alpha_pos: "0 < alpha"
    and zero:
      "projected_gradient_residual (bounded_interval_real a b) alpha
        quadratic_real_gradient x = 0"
  shows "x = 0"
proof -
  have zero_mem: "0 \<in> bounded_interval_real a b"
    by (rule zero_mem_bounded_interval_real[OF a0 b0])

  have x_mem: "x \<in> bounded_interval_real a b"
    using x_lower x_upper by simp

  show "x = 0"
    by (rule quadratic_real_projected_gradient_residual_zero_imp_zero[
      OF closed_bounded_interval_real convex_bounded_interval_real zero_mem
         x_mem alpha_pos zero])
qed

lemma bounded_interval_quadratic_projected_gradient_residual_zero_imp_global_min:
  assumes x_lower: "a \<le> x"
    and x_upper: "x \<le> b"
    and alpha_pos: "0 < alpha"
    and zero:
      "projected_gradient_residual (bounded_interval_real a b) alpha
        quadratic_real_gradient x = 0"
  shows "global_min_on (bounded_interval_real a b) quadratic_real x"
proof -
  have x_mem: "x \<in> bounded_interval_real a b"
    using x_lower x_upper by simp

  show ?thesis
    by (rule projected_gradient_residual_zero_imp_global_min_on[
      OF quadratic_real_smooth_convex_on_bounded_interval
         closed_bounded_interval_real convex_bounded_interval_real
         x_mem alpha_pos zero])
qed


text \<open>
The most important concrete consequences in this file are:
  @{thm nonnegative_quadratic_projected_gradient_descent_function_value_gap_bound},
  @{thm nonnegative_quadratic_projected_gradient_descent_exists_small_residual_sq},
  @{thm nonnegative_quadratic_projected_gradient_descent_exists_epsilon_residual},
  @{thm nonnegative_quadratic_projected_gradient_residual_zero_imp_zero},
  @{thm bounded_interval_quadratic_projected_gradient_descent_function_value_gap_bound},
  @{thm bounded_interval_quadratic_projected_gradient_descent_exists_epsilon_residual},
  and
  @{thm bounded_interval_quadratic_projected_gradient_residual_zero_imp_zero}.

Together, they show that the abstract projected-gradient convergence and
residual-stationarity theorems can be instantiated on simple constrained
smooth strongly convex quadratic problems, including both an unbounded
half-line constraint and a bounded interval constraint.
\<close>

end