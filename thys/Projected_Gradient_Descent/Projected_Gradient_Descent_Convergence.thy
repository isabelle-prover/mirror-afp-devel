theory Projected_Gradient_Descent_Convergence
  imports Projection_Optimization
begin

section \<open>Function-value convergence for projected gradient descent\<close>

text \<open>
This theory proves the standard O(1/N) function-value convergence
bound for projected gradient descent on a closed convex feasible set.

The proof follows the same telescoping structure as the unconstrained
gradient-descent convergence proof.  The only new ingredient is the
projected one-step distance estimate from the projection theory.
\<close>


subsection \<open>Monotonicity of projected gradient descent\<close>

lemma projected_gradient_descent_objective_nonincreasing:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
  shows "nonincreasing_sequence (objective_values f x)"
  unfolding nonincreasing_sequence_def objective_values_def
proof
  fix n

  have xn_mem: "x n \<in> C"
    using feasible by (rule feasible_iteratesD)

  have step:
    "f (x (Suc n)) - f (x n)
      \<le>
     (norm (x n - x n) ^ 2 - norm (x (Suc n) - x n) ^ 2)
      / (2 * alpha)"
    by (rule projected_gradient_descent_one_step_distance_bound_to_point[
        OF smooth closed convex pgd feasible xn_mem alpha_pos step_size])

  have rhs_nonpos:
    "(norm (x n - x n) ^ 2 - norm (x (Suc n) - x n) ^ 2)
      / (2 * alpha) \<le> 0"
    using alpha_pos by simp

  show "f (x (Suc n)) \<le> f (x n)"
    using step rhs_nonpos by linarith
qed


subsection \<open>Summed function-value gaps\<close>

lemma projected_gradient_descent_sum_function_value_gaps_bound_to_point:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and u_mem: "u \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
  shows
    "(\<Sum>n<N. f (x (Suc n)) - f u)
      \<le>
     norm (x 0 - u) ^ 2 / (2 * alpha)
      - norm (x N - u) ^ 2 / (2 * alpha)"
proof (rule sum_progress_le_initial_gap)
  fix n
  assume "n < N"

  have step:
    "f (x (Suc n)) - f u
      \<le>
     (norm (x n - u) ^ 2 - norm (x (Suc n) - u) ^ 2)
      / (2 * alpha)"
    by (rule projected_gradient_descent_one_step_distance_bound_to_point[
        OF smooth closed convex pgd feasible u_mem alpha_pos step_size])

  have split:
    "(norm (x n - u) ^ 2 - norm (x (Suc n) - u) ^ 2)
      / (2 * alpha)
      =
     norm (x n - u) ^ 2 / (2 * alpha)
      - norm (x (Suc n) - u) ^ 2 / (2 * alpha)"
    by (simp add: diff_divide_distrib)

  show
    "f (x (Suc n)) - f u
      \<le> norm (x n - u) ^ 2 / (2 * alpha)
        - norm (x (Suc n) - u) ^ 2 / (2 * alpha)"
    using step split by simp
qed

lemma projected_gradient_descent_sum_function_value_gaps_bound_to_minimizer:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on C f xstar"
  shows
    "(\<Sum>n<N. f (x (Suc n)) - f xstar)
      \<le>
     norm (x 0 - xstar) ^ 2 / (2 * alpha)
      - norm (x N - xstar) ^ 2 / (2 * alpha)"
proof -
  have xstar_mem: "xstar \<in> C"
    using minimizer by (rule global_min_onD_mem)

  show ?thesis
    by (rule projected_gradient_descent_sum_function_value_gaps_bound_to_point[
        OF smooth closed convex pgd feasible xstar_mem alpha_pos step_size])
qed

lemma projected_gradient_descent_sum_function_value_gaps_bound_to_point_initial:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and u_mem: "u \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
  shows
    "(\<Sum>n<N. f (x (Suc n)) - f u)
      \<le> norm (x 0 - u) ^ 2 / (2 * alpha)"
proof -
  have telescoped:
    "(\<Sum>n<N. f (x (Suc n)) - f u)
      \<le>
     norm (x 0 - u) ^ 2 / (2 * alpha)
      - norm (x N - u) ^ 2 / (2 * alpha)"
    by (rule projected_gradient_descent_sum_function_value_gaps_bound_to_point[
        OF smooth closed convex pgd feasible u_mem alpha_pos step_size])

  have terminal_nonneg:
    "0 \<le> norm (x N - u) ^ 2 / (2 * alpha)"
    using alpha_pos by simp

  show ?thesis
    using telescoped terminal_nonneg by linarith
qed

lemma projected_gradient_descent_sum_function_value_gaps_bound_to_minimizer_initial:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on C f xstar"
  shows
    "(\<Sum>n<N. f (x (Suc n)) - f xstar)
      \<le> norm (x 0 - xstar) ^ 2 / (2 * alpha)"
proof -
  have xstar_mem: "xstar \<in> C"
    using minimizer by (rule global_min_onD_mem)

  show ?thesis
    by (rule projected_gradient_descent_sum_function_value_gaps_bound_to_point_initial[
        OF smooth closed convex pgd feasible xstar_mem alpha_pos step_size])
qed


subsection \<open>The O(1/N) convergence rate\<close>

lemma projected_gradient_descent_last_gap_times_N_bound:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on C f xstar"
    and N_pos: "N > 0"
  shows
    "real N * (f (x N) - f xstar)
      \<le> norm (x 0 - xstar) ^ 2 / (2 * alpha)"
proof -
  have mono:
    "nonincreasing_sequence (objective_values f x)"
    by (rule projected_gradient_descent_objective_nonincreasing[
        OF smooth closed convex pgd feasible alpha_pos step_size])

  have lower_sum:
    "real N * (f (x N) - f xstar)
      \<le> (\<Sum>n<N. f (x (Suc n)) - f xstar)"
    using nonincreasing_sequence_shifted_sum_lower_bound[
      OF mono N_pos, of "f xstar"]
    by simp

  have upper_sum:
    "(\<Sum>n<N. f (x (Suc n)) - f xstar)
      \<le> norm (x 0 - xstar) ^ 2 / (2 * alpha)"
    by (rule projected_gradient_descent_sum_function_value_gaps_bound_to_minimizer_initial[
        OF smooth closed convex pgd feasible alpha_pos step_size minimizer])

  show ?thesis
    using lower_sum upper_sum by linarith
qed

theorem projected_gradient_descent_function_value_gap_bound_feasible:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on C f xstar"
    and N_pos: "N > 0"
  shows
    "f (x N) - f xstar
      \<le> norm (x 0 - xstar) ^ 2 / (2 * alpha * real N)"
proof -
  let ?gap = "f (x N) - f xstar"
  let ?B = "norm (x 0 - xstar) ^ 2 / (2 * alpha)"

  have weighted:
    "real N * ?gap \<le> ?B"
    by (rule projected_gradient_descent_last_gap_times_N_bound[
        OF smooth closed convex pgd feasible alpha_pos step_size minimizer N_pos])

  have N_real_pos: "0 < real N"
    using N_pos by simp

  have div_bound:
    "(real N * ?gap) / real N \<le> ?B / real N"
  proof (rule divide_right_mono)
    show "real N * ?gap \<le> ?B"
      using weighted .
    show "0 \<le> real N"
      using N_real_pos by linarith
  qed

  have "?gap = (real N * ?gap) / real N"
    using N_real_pos by simp
  also have "... \<le> ?B / real N"
    using div_bound .
  also have "... = norm (x 0 - xstar) ^ 2 / (2 * alpha * real N)"
    using alpha_pos N_real_pos
    by (simp add: field_simps)
  finally show ?thesis .
qed

theorem projected_gradient_descent_function_value_gap_bound:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on C f xstar"
    and N_pos: "N > 0"
  shows
    "f (x N) - f xstar
      \<le> norm (x 0 - xstar) ^ 2 / (2 * alpha * real N)"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
        OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_function_value_gap_bound_feasible[
        OF smooth closed convex pgd feasible alpha_pos step_size minimizer N_pos])
qed


subsection \<open>Locale form\<close>

locale projected_gradient_descent =
  fixes C :: "'a::{real_inner,heine_borel} set"
    and L alpha :: real
    and f :: "'a \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
    and x :: "nat \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and iterates: "projected_gradient_descent_iterates C alpha G x"
    and initial_feasible: "x 0 \<in> C"
    and step_size: "alpha * L \<le> 1"
begin

lemma feasible:
  "feasible_iterates C x"
  by (rule projected_gradient_descent_feasible_from_initial[
      OF iterates closed initial_feasible])

lemma objective_nonincreasing:
  assumes alpha_pos: "0 < alpha"
  shows "nonincreasing_sequence (objective_values f x)"
  by (rule projected_gradient_descent_objective_nonincreasing[
      OF smooth closed convex iterates feasible alpha_pos step_size])

lemma sum_function_value_gaps_bound_to_point:
  assumes alpha_pos: "0 < alpha"
    and u_mem: "u \<in> C"
  shows
    "(\<Sum>n<N. f (x (Suc n)) - f u)
      \<le>
     norm (x 0 - u) ^ 2 / (2 * alpha)
      - norm (x N - u) ^ 2 / (2 * alpha)"
  by (rule projected_gradient_descent_sum_function_value_gaps_bound_to_point[
      OF smooth closed convex iterates feasible u_mem alpha_pos step_size])

lemma sum_function_value_gaps_bound_to_minimizer:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on C f xstar"
  shows
    "(\<Sum>n<N. f (x (Suc n)) - f xstar)
      \<le>
     norm (x 0 - xstar) ^ 2 / (2 * alpha)
      - norm (x N - xstar) ^ 2 / (2 * alpha)"
  by (rule projected_gradient_descent_sum_function_value_gaps_bound_to_minimizer[
      OF smooth closed convex iterates feasible alpha_pos step_size minimizer])

lemma last_gap_times_N_bound:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on C f xstar"
    and N_pos: "N > 0"
  shows
    "real N * (f (x N) - f xstar)
      \<le> norm (x 0 - xstar) ^ 2 / (2 * alpha)"
  by (rule projected_gradient_descent_last_gap_times_N_bound[
      OF smooth closed convex iterates feasible alpha_pos step_size minimizer N_pos])

theorem function_value_gap_bound:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on C f xstar"
    and N_pos: "N > 0"
  shows
    "f (x N) - f xstar
      \<le> norm (x 0 - xstar) ^ 2 / (2 * alpha * real N)"
  by (rule projected_gradient_descent_function_value_gap_bound[
      OF smooth closed convex iterates initial_feasible alpha_pos step_size minimizer N_pos])

end


text \<open>
The main theorem is
@{thm projected_gradient_descent_function_value_gap_bound}.
It states the classical O(1/N) function-value convergence estimate for
fixed-step projected gradient descent on a closed convex feasible set.
\<close>

end