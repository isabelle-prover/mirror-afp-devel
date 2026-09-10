theory Gradient_Descent_Convergence
  imports Gradient_Descent_Rates
begin

section \<open>Function-value convergence for gradient descent\<close>

text \<open>
This theory proves the standard O(1/N) function-value convergence
bound for fixed-step gradient descent on a smooth convex objective.

The proof is organized around the usual distance-to-comparator estimate:
each gradient step decreases the squared distance potential enough to
pay for the next function-value gap.  The estimate is then telescoped.
\<close>


subsection \<open>Elementary monotonicity lemmas\<close>

lemma nonincreasing_sequence_mono:
  fixes a :: "nat \<Rightarrow> real"
  assumes mono: "nonincreasing_sequence a"
    and mn: "m \<le> n"
  shows "a n \<le> a m"
  using mn
proof (induction n arbitrary: m)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "m = Suc n")
    case True
    then show ?thesis by simp
  next
    case False
    have m_le_n: "m \<le> n"
      using Suc.prems False by linarith
    have "a (Suc n) \<le> a n"
      using mono by (rule nonincreasing_sequenceD)
    also have "a n \<le> a m"
      using Suc.IH[OF m_le_n] .
    finally show ?thesis .
  qed
qed

lemma nonincreasing_sequence_shifted_sum_lower_bound:
  fixes a :: "nat \<Rightarrow> real"
  assumes mono: "nonincreasing_sequence a"
    and N_pos: "N > 0"
  shows "real N * (a N - b) \<le> (\<Sum>n<N. a (Suc n) - b)"
proof -
  have pointwise: "\<And>n. n < N \<Longrightarrow> a N - b \<le> a (Suc n) - b"
  proof -
    fix n
    assume n_lt: "n < N"
    have Suc_le_N: "Suc n \<le> N"
      using n_lt by simp

    have "a N \<le> a (Suc n)"
      using Suc_le_N
      by (rule nonincreasing_sequence_mono[OF mono])

    thus "a N - b \<le> a (Suc n) - b"
      by simp
  qed

  have sum_bound:
    "(\<Sum>n<N. a N - b) \<le> (\<Sum>n<N. a (Suc n) - b)"
  proof (rule sum_mono)
    fix n
    assume n_mem: "n \<in> {..<N}"
    hence "n < N"
      by simp
    thus "a N - b \<le> a (Suc n) - b"
      by (rule pointwise)
  qed

  have "(\<Sum>n<N. a N - b) = real N * (a N - b)"
    by simp

  thus ?thesis
    using sum_bound by simp
qed


subsection \<open>Distance identity for one gradient step\<close>

lemma gradient_step_distance_decrease:
  fixes x xstar :: "'a::real_inner"
  shows
    "norm (x - xstar) ^ 2 - norm (gradient_step alpha G x - xstar) ^ 2 =
      2 * alpha * inner (G x) (x - xstar) - alpha ^ 2 * norm (G x) ^ 2"
proof -
  let ?d = "x - xstar"
  let ?g = "G x"

  have arg_eq:
    "gradient_step alpha G x - xstar = ?d - scaleR alpha ?g"
    unfolding gradient_step_def
    by (simp add: algebra_simps)

  have expand:
    "norm (?d - scaleR alpha ?g) ^ 2 =
      norm ?d ^ 2
      - 2 * alpha * inner ?g ?d
      + alpha ^ 2 * norm ?g ^ 2"
  proof -
    have "norm (?d - scaleR alpha ?g) ^ 2 =
        inner (?d - scaleR alpha ?g) (?d - scaleR alpha ?g)"
      by (simp add: power2_norm_eq_inner)
    also have "... =
        inner ?d ?d
        - 2 * alpha * inner ?g ?d
        + alpha ^ 2 * inner ?g ?g"
      by (simp add:
          inner_commute
          algebra_simps
          power2_eq_square)
    also have "... =
        norm ?d ^ 2
        - 2 * alpha * inner ?g ?d
        + alpha ^ 2 * norm ?g ^ 2"
      by (simp add: power2_norm_eq_inner)
    finally show ?thesis .
  qed

  have norm_step:
    "norm (gradient_step alpha G x - xstar) ^ 2 =
      norm ?d ^ 2
      - 2 * alpha * inner ?g ?d
      + alpha ^ 2 * norm ?g ^ 2"
  proof -
    have "norm (gradient_step alpha G x - xstar) ^ 2 =
        norm (?d - scaleR alpha ?g) ^ 2"
      by (simp only: arg_eq)
    also have "... =
        norm ?d ^ 2
        - 2 * alpha * inner ?g ?d
        + alpha ^ 2 * norm ?g ^ 2"
      by (rule expand)
    finally show ?thesis .
  qed

  show ?thesis
    using norm_step
    by (simp add: algebra_simps)
qed

lemma gradient_step_distance_decrease_divided:
  fixes x xstar :: "'a::real_inner"
  assumes alpha_pos: "0 < alpha"
  shows
    "(norm (x - xstar) ^ 2 - norm (gradient_step alpha G x - xstar) ^ 2)
      / (2 * alpha)
    =
      inner (G x) (x - xstar) - (alpha / 2) * norm (G x) ^ 2"
proof -
  have raw:
    "norm (x - xstar) ^ 2 - norm (gradient_step alpha G x - xstar) ^ 2 =
      2 * alpha * inner (G x) (x - xstar) - alpha ^ 2 * norm (G x) ^ 2"
    by (rule gradient_step_distance_decrease)

  show ?thesis
    using raw alpha_pos
    by (simp add: field_simps power2_eq_square)
qed


subsection \<open>One-step function gap bound\<close>

lemma gradient_descent_one_step_distance_bound_to_point:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L S f G"
    and gd: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and u_mem: "u \<in> S"
  shows
    "f (x (Suc n)) - f u
      \<le>
     (norm (x n - u) ^ 2 - norm (x (Suc n) - u) ^ 2) / (2 * alpha)"
proof -
  have alpha_nonneg: "0 \<le> alpha"
    using alpha_pos by simp

  have smooth_bound: "smooth_upper_bound_on L S f G"
    using smooth by (rule smooth_convex_onD_smooth_upper_bound)

  have cd: "convex_differentiable_on S f G"
    using smooth by (rule smooth_convex_onD_convex_differentiable)

  have lower_bound: "gradient_lower_bound_on S f G"
    using cd by (rule convex_differentiable_on_imp_gradient_lower_bound_on)

  have xn_mem: "x n \<in> S"
    using feasible by (rule feasible_iteratesD)

  have support:
    "f (x n) + inner (G (x n)) (u - x n) \<le> f u"
    using gradient_lower_bound_onD[OF lower_bound xn_mem u_mem] .

  have inner_rewrite:
    "- inner (G (x n)) (u - x n) = inner (G (x n)) (x n - u)"
    by (simp add: inner_diff_right)

  have gap_at_xn:
    "f (x n) - f u \<le> inner (G (x n)) (x n - u)"
    using support inner_rewrite by linarith

  have decrease:
    "f (x (Suc n)) \<le> f (x n) - (alpha / 2) * norm (G (x n)) ^ 2"
    using gradient_descent_one_step_decrease[
      OF smooth_bound gd feasible alpha_nonneg step_size, of n] .

  have gap_step:
    "f (x (Suc n)) - f u
      \<le> inner (G (x n)) (x n - u) - (alpha / 2) * norm (G (x n)) ^ 2"
    using decrease gap_at_xn by linarith

  have step_eq:
    "x (Suc n) = gradient_step alpha G (x n)"
    using gd by (rule gradient_descent_iteratesD)

  have distance_eq:
    "(norm (x n - u) ^ 2 - norm (x (Suc n) - u) ^ 2) / (2 * alpha)
      =
     inner (G (x n)) (x n - u) - (alpha / 2) * norm (G (x n)) ^ 2"
    using gradient_step_distance_decrease_divided[
      where alpha = alpha and x = "x n" and xstar = u and G = G,
      OF alpha_pos]
    by (simp add: step_eq)

  show ?thesis
    using gap_step distance_eq by simp
qed

lemma gradient_descent_one_step_distance_bound_to_minimizer:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L S f G"
    and gd: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on S f xstar"
  shows
    "f (x (Suc n)) - f xstar
      \<le>
     (norm (x n - xstar) ^ 2 - norm (x (Suc n) - xstar) ^ 2) / (2 * alpha)"
proof -
  have xstar_mem: "xstar \<in> S"
    using minimizer by (rule global_min_onD_mem)

  show ?thesis
    using gradient_descent_one_step_distance_bound_to_point[
      OF smooth gd feasible alpha_pos step_size xstar_mem, of n] .
qed


subsection \<open>Telescoped function gap bounds\<close>

lemma gradient_descent_sum_function_value_gaps_bound_to_point:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L S f G"
    and gd: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and u_mem: "u \<in> S"
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
     (norm (x n - u) ^ 2 - norm (x (Suc n) - u) ^ 2) / (2 * alpha)"
    using gradient_descent_one_step_distance_bound_to_point[
      OF smooth gd feasible alpha_pos step_size u_mem, of n] .

  have split:
    "(norm (x n - u) ^ 2 - norm (x (Suc n) - u) ^ 2) / (2 * alpha)
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

lemma gradient_descent_sum_function_value_gaps_bound_to_minimizer:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L S f G"
    and gd: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on S f xstar"
  shows
    "(\<Sum>n<N. f (x (Suc n)) - f xstar)
      \<le>
     norm (x 0 - xstar) ^ 2 / (2 * alpha)
      - norm (x N - xstar) ^ 2 / (2 * alpha)"
proof -
  have xstar_mem: "xstar \<in> S"
    using minimizer by (rule global_min_onD_mem)

  show ?thesis
    using gradient_descent_sum_function_value_gaps_bound_to_point[
      OF smooth gd feasible alpha_pos step_size xstar_mem, of N] .
qed

lemma gradient_descent_sum_function_value_gaps_bound_to_point_initial:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L S f G"
    and gd: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and u_mem: "u \<in> S"
  shows
    "(\<Sum>n<N. f (x (Suc n)) - f u)
      \<le> norm (x 0 - u) ^ 2 / (2 * alpha)"
proof -
  have telescoped:
    "(\<Sum>n<N. f (x (Suc n)) - f u)
      \<le>
     norm (x 0 - u) ^ 2 / (2 * alpha)
      - norm (x N - u) ^ 2 / (2 * alpha)"
    using gradient_descent_sum_function_value_gaps_bound_to_point[
      OF assms, of N] .

  have terminal_nonneg:
    "0 \<le> norm (x N - u) ^ 2 / (2 * alpha)"
    using alpha_pos by simp

  show ?thesis
    using telescoped terminal_nonneg by linarith
qed

lemma gradient_descent_sum_function_value_gaps_bound_to_minimizer_initial:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L S f G"
    and gd: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on S f xstar"
  shows
    "(\<Sum>n<N. f (x (Suc n)) - f xstar)
      \<le> norm (x 0 - xstar) ^ 2 / (2 * alpha)"
proof -
  have xstar_mem: "xstar \<in> S"
    using minimizer by (rule global_min_onD_mem)

  show ?thesis
    using gradient_descent_sum_function_value_gaps_bound_to_point_initial[
      OF smooth gd feasible alpha_pos step_size xstar_mem, of N] .
qed


subsection \<open>The O(1/N) convergence rate\<close>

lemma gradient_descent_last_gap_times_N_bound:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L S f G"
    and gd: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on S f xstar"
    and N_pos: "N > 0"
  shows
    "real N * (f (x N) - f xstar)
      \<le> norm (x 0 - xstar) ^ 2 / (2 * alpha)"
proof -
  have alpha_nonneg: "0 \<le> alpha"
    using alpha_pos by simp

  have smooth_bound: "smooth_upper_bound_on L S f G"
    using smooth by (rule smooth_convex_onD_smooth_upper_bound)

  have mono:
    "nonincreasing_sequence (objective_values f x)"
    using gradient_descent_objective_nonincreasing[
      OF smooth_bound gd feasible alpha_nonneg step_size] .

  have lower_sum:
    "real N * (f (x N) - f xstar)
      \<le> (\<Sum>n<N. f (x (Suc n)) - f xstar)"
    using nonincreasing_sequence_shifted_sum_lower_bound[
      OF mono N_pos, of "f xstar"]
    by simp

  have upper_sum:
    "(\<Sum>n<N. f (x (Suc n)) - f xstar)
      \<le> norm (x 0 - xstar) ^ 2 / (2 * alpha)"
    using gradient_descent_sum_function_value_gaps_bound_to_minimizer_initial[
      OF smooth gd feasible alpha_pos step_size minimizer, of N] .

  show ?thesis
    using lower_sum upper_sum by linarith
qed

theorem gradient_descent_function_value_gap_bound:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L S f G"
    and gd: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on S f xstar"
    and N_pos: "N > 0"
  shows
    "f (x N) - f xstar
      \<le> norm (x 0 - xstar) ^ 2 / (2 * alpha * real N)"
proof -
  let ?gap = "f (x N) - f xstar"
  let ?B = "norm (x 0 - xstar) ^ 2 / (2 * alpha)"

  have weighted:
    "real N * ?gap \<le> ?B"
    using gradient_descent_last_gap_times_N_bound[
      OF smooth gd feasible alpha_pos step_size minimizer N_pos] .

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


subsection \<open>Locale form\<close>

context gradient_descent
begin

lemma smooth_convex_on_self:
  "smooth_convex_on L S f G"
proof (rule smooth_convex_onI)
  show "convex_differentiable_on S f G"
    by (rule convex_differentiable_onI[OF convex_f gradient_f])
next
  show "smooth_upper_bound_on L S f G"
    by (rule smooth_bound)
qed

lemma one_step_distance_bound_to_point:
  assumes alpha_pos: "0 < alpha"
    and u_mem: "u \<in> S"
  shows
    "f (x (Suc n)) - f u
      \<le>
     (norm (x n - u) ^ 2 - norm (x (Suc n) - u) ^ 2) / (2 * alpha)"
  using gradient_descent_one_step_distance_bound_to_point[
    OF smooth_convex_on_self iterates feasible alpha_pos step_size u_mem, of n] .

lemma one_step_distance_bound_to_minimizer:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on S f xstar"
  shows
    "f (x (Suc n)) - f xstar
      \<le>
     (norm (x n - xstar) ^ 2 - norm (x (Suc n) - xstar) ^ 2) / (2 * alpha)"
  using gradient_descent_one_step_distance_bound_to_minimizer[
    OF smooth_convex_on_self iterates feasible alpha_pos step_size minimizer, of n] .

lemma sum_function_value_gaps_bound_to_minimizer:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on S f xstar"
  shows
    "(\<Sum>n<N. f (x (Suc n)) - f xstar)
      \<le>
     norm (x 0 - xstar) ^ 2 / (2 * alpha)
      - norm (x N - xstar) ^ 2 / (2 * alpha)"
  using gradient_descent_sum_function_value_gaps_bound_to_minimizer[
    OF smooth_convex_on_self iterates feasible alpha_pos step_size minimizer, of N] .

lemma sum_function_value_gaps_bound_to_minimizer_initial:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on S f xstar"
  shows
    "(\<Sum>n<N. f (x (Suc n)) - f xstar)
      \<le> norm (x 0 - xstar) ^ 2 / (2 * alpha)"
  using gradient_descent_sum_function_value_gaps_bound_to_minimizer_initial[
    OF smooth_convex_on_self iterates feasible alpha_pos step_size minimizer, of N] .

lemma last_gap_times_N_bound:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on S f xstar"
    and N_pos: "N > 0"
  shows
    "real N * (f (x N) - f xstar)
      \<le> norm (x 0 - xstar) ^ 2 / (2 * alpha)"
  using gradient_descent_last_gap_times_N_bound[
    OF smooth_convex_on_self iterates feasible alpha_pos step_size minimizer N_pos] .

theorem function_value_gap_bound:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on S f xstar"
    and N_pos: "N > 0"
  shows
    "f (x N) - f xstar
      \<le> norm (x 0 - xstar) ^ 2 / (2 * alpha * real N)"
  using gradient_descent_function_value_gap_bound[
    OF smooth_convex_on_self iterates feasible alpha_pos step_size minimizer N_pos] .

end


text \<open>
The main theorem is @{thm gradient_descent_function_value_gap_bound}.
It gives the classical fixed-step O(1/N) convergence estimate for smooth
convex gradient descent, stated using the same gradient-descent recurrence
and feasibility interface as the previous theories.
\<close>

end