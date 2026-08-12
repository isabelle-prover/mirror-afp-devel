theory Gradient_Descent_Rates
  imports
    Gradient_Descent
    Abstract_Descent
begin

section \<open>Rate infrastructure for gradient descent\<close>

text \<open>
  This theory collects the first rate-style consequences of the
  gradient descent development.

  The purpose of this file is intentionally modest.  It does not yet prove
  the full O(1/N) function-value convergence theorem for smooth convex
  minimization.  Instead, it packages the telescoping arguments that follow
  directly from the one-step progress estimate already proved in
  @{text \<open>Gradient_Descent\<close>}.

  These lemmas are meant to be reusable later for projected gradient descent
  and other descent methods.
\<close>

subsection \<open>Finite-sum bounds for gradient descent\<close>

text \<open>
  The main direct consequence of the one-step progress inequality is that
  the weighted sum of squared gradient norms is bounded by the total decrease
  in objective value.
\<close>

lemma gradient_descent_sum_weighted_gradient_norm_sq_bound:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_upper_bound_on L S f G"
  assumes gd: "gradient_descent_iterates alpha G x"
  assumes feasible: "feasible_iterates S x"
  assumes alpha_nonneg: "0 \<le> alpha"
  assumes step_size: "alpha * L \<le> 1"
  shows
    "sum (\<lambda>n. (alpha / 2) * norm (G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - f (x N)"
proof (rule sum_progress_le_initial_gap)
  fix n
  assume "n < N"
  show "(alpha / 2) * norm (G (x n)) ^ 2
      \<le> f (x n) - f (x (Suc n))"
    using gradient_descent_step_progress[
      OF smooth gd feasible alpha_nonneg step_size, of n] .
qed

text \<open>
  A lower-bound version of the same result.
\<close>

lemma gradient_descent_sum_weighted_gradient_norm_sq_bound_below:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_upper_bound_on L S f G"
  assumes gd: "gradient_descent_iterates alpha G x"
  assumes feasible: "feasible_iterates S x"
  assumes alpha_nonneg: "0 \<le> alpha"
  assumes step_size: "alpha * L \<le> 1"
  assumes lower: "B \<le> f (x N)"
  shows
    "sum (\<lambda>n. (alpha / 2) * norm (G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - B"
proof -
  have "sum (\<lambda>n. (alpha / 2) * norm (G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - f (x N)"
    using gradient_descent_sum_weighted_gradient_norm_sq_bound[
      OF smooth gd feasible alpha_nonneg step_size] .
  also have "... \<le> f (x 0) - B"
    using lower by linarith
  finally show ?thesis .
qed

text \<open>
  If the step size is strictly positive, the coefficient alpha / 2 can be
  divided out.  This gives the standard finite-sum squared-gradient bound.
\<close>

lemma gradient_descent_sum_gradient_norm_sq_bound:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_upper_bound_on L S f G"
  assumes gd: "gradient_descent_iterates alpha G x"
  assumes feasible: "feasible_iterates S x"
  assumes alpha_pos: "0 < alpha"
  assumes step_size: "alpha * L \<le> 1"
  shows
    "sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - f (x N))"
proof -
  have alpha_nonneg: "0 \<le> alpha"
    using alpha_pos by simp

  have weighted:
    "sum (\<lambda>n. (alpha / 2) * norm (G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - f (x N)"
    using gradient_descent_sum_weighted_gradient_norm_sq_bound[
      OF smooth gd feasible alpha_nonneg step_size] .

  have coeff_pos: "0 < alpha / 2"
    using alpha_pos by simp

  have weighted_eq:
    "sum (\<lambda>n. (alpha / 2) * norm (G (x n)) ^ 2) {..<N}
      = (alpha / 2) * sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}"
    by (simp add: sum_distrib_left)

  have "(alpha / 2) * sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - f (x N)"
    using weighted weighted_eq by simp

  then show ?thesis
    using coeff_pos by (simp add: field_simps)
qed

lemma gradient_descent_sum_gradient_norm_sq_bound_below:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_upper_bound_on L S f G"
  assumes gd: "gradient_descent_iterates alpha G x"
  assumes feasible: "feasible_iterates S x"
  assumes alpha_pos: "0 < alpha"
  assumes step_size: "alpha * L \<le> 1"
  assumes lower: "B \<le> f (x N)"
  shows
    "sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - B)"
proof -
  have alpha_nonneg: "0 \<le> alpha"
    using alpha_pos by simp

  have weighted:
    "sum (\<lambda>n. (alpha / 2) * norm (G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - B"
    using gradient_descent_sum_weighted_gradient_norm_sq_bound_below[
      OF smooth gd feasible alpha_nonneg step_size lower] .

  have coeff_pos: "0 < alpha / 2"
    using alpha_pos by simp

  have weighted_eq:
    "sum (\<lambda>n. (alpha / 2) * norm (G (x n)) ^ 2) {..<N}
      = (alpha / 2) * sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}"
    by (simp add: sum_distrib_left)

  have "(alpha / 2) * sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - B"
    using weighted weighted_eq by simp

  then show ?thesis
    using coeff_pos by (simp add: field_simps)
qed


subsection \<open>Average and small-gradient consequences\<close>

text \<open>
  The finite-sum bound immediately implies an average squared-gradient bound.
\<close>

lemma gradient_descent_average_gradient_norm_sq_bound:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_upper_bound_on L S f G"
  assumes gd: "gradient_descent_iterates alpha G x"
  assumes feasible: "feasible_iterates S x"
  assumes alpha_pos: "0 < alpha"
  assumes step_size: "alpha * L \<le> 1"
  assumes N_pos: "N > 0"
  shows
    "(1 / real N) * sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}
      \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
proof -
  have sum_bound:
    "sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - f (x N))"
    using gradient_descent_sum_gradient_norm_sq_bound[
      OF smooth gd feasible alpha_pos step_size] .

  have N_real_pos: "0 < real N"
    using N_pos by simp

  have "(1 / real N) * sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}
      \<le> (1 / real N) * ((2 / alpha) * (f (x 0) - f (x N)))"
    using sum_bound N_real_pos by (intro mult_left_mono) simp_all
  also have "... = (2 / (alpha * real N)) * (f (x 0) - f (x N))"
    using alpha_pos N_real_pos by (simp add: field_simps)
  finally show ?thesis .
qed

lemma gradient_descent_average_gradient_norm_sq_bound_below:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_upper_bound_on L S f G"
  assumes gd: "gradient_descent_iterates alpha G x"
  assumes feasible: "feasible_iterates S x"
  assumes alpha_pos: "0 < alpha"
  assumes step_size: "alpha * L \<le> 1"
  assumes lower: "B \<le> f (x N)"
  assumes N_pos: "N > 0"
  shows
    "(1 / real N) * sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}
      \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
proof -
  have sum_bound:
    "sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - B)"
    using gradient_descent_sum_gradient_norm_sq_bound_below[
      OF smooth gd feasible alpha_pos step_size lower] .

  have N_real_pos: "0 < real N"
    using N_pos by simp

  have "(1 / real N) * sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}
      \<le> (1 / real N) * ((2 / alpha) * (f (x 0) - B))"
    using sum_bound N_real_pos by (intro mult_left_mono) simp_all
  also have "... = (2 / (alpha * real N)) * (f (x 0) - B)"
    using alpha_pos N_real_pos by (simp add: field_simps)
  finally show ?thesis .
qed

text \<open>
  The next theorem states the usual small-gradient consequence: among the
  first N iterates, at least one iterate has squared gradient norm bounded
  by the average finite-sum bound.
\<close>

lemma gradient_descent_exists_small_gradient_norm_sq:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_upper_bound_on L S f G"
  assumes gd: "gradient_descent_iterates alpha G x"
  assumes feasible: "feasible_iterates S x"
  assumes alpha_pos: "0 < alpha"
  assumes step_size: "alpha * L \<le> 1"
  assumes N_pos: "N > 0"
  shows
    "\<exists>n<N. norm (G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
proof -
  have sum_bound:
    "sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - f (x N))"
    using gradient_descent_sum_gradient_norm_sq_bound[
      OF smooth gd feasible alpha_pos step_size] .

  have nonneg: "\<And>n. n < N \<Longrightarrow> 0 \<le> norm (G (x n)) ^ 2"
    by simp

  obtain n where n_lt: "n < N"
    and n_bound:
      "norm (G (x n)) ^ 2
        \<le> ((2 / alpha) * (f (x 0) - f (x N))) / real N"
    using exists_le_average_of_sum_bound[OF N_pos nonneg sum_bound] by auto

  have rewrite:
    "((2 / alpha) * (f (x 0) - f (x N))) / real N
      = (2 / (alpha * real N)) * (f (x 0) - f (x N))"
    using alpha_pos N_pos by (simp add: field_simps)

  have "norm (G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
    using n_bound rewrite by simp

  then show ?thesis
    using n_lt by auto
qed

lemma gradient_descent_exists_small_gradient_norm_sq_below:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_upper_bound_on L S f G"
  assumes gd: "gradient_descent_iterates alpha G x"
  assumes feasible: "feasible_iterates S x"
  assumes alpha_pos: "0 < alpha"
  assumes step_size: "alpha * L \<le> 1"
  assumes lower: "B \<le> f (x N)"
  assumes N_pos: "N > 0"
  shows
    "\<exists>n<N. norm (G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
proof -
  have sum_bound:
    "sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - B)"
    using gradient_descent_sum_gradient_norm_sq_bound_below[
      OF smooth gd feasible alpha_pos step_size lower] .

  have nonneg: "\<And>n. n < N \<Longrightarrow> 0 \<le> norm (G (x n)) ^ 2"
    by simp

  obtain n where n_lt: "n < N"
    and n_bound:
      "norm (G (x n)) ^ 2
        \<le> ((2 / alpha) * (f (x 0) - B)) / real N"
    using exists_le_average_of_sum_bound[OF N_pos nonneg sum_bound] by auto

  have rewrite:
    "((2 / alpha) * (f (x 0) - B)) / real N
      = (2 / (alpha * real N)) * (f (x 0) - B)"
    using alpha_pos N_pos by (simp add: field_simps)

  have "norm (G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
    using n_bound rewrite by simp

  then show ?thesis
    using n_lt by auto
qed


subsection \<open>Weighted small-gradient consequences\<close>

text \<open>
  The weighted version does not require dividing by alpha.  It is therefore
  available even for the degenerate case alpha = 0, although the resulting
  statement is mainly useful when alpha is positive.
\<close>

lemma gradient_descent_exists_small_weighted_gradient_norm_sq:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_upper_bound_on L S f G"
  assumes gd: "gradient_descent_iterates alpha G x"
  assumes feasible: "feasible_iterates S x"
  assumes alpha_nonneg: "0 \<le> alpha"
  assumes step_size: "alpha * L \<le> 1"
  assumes N_pos: "N > 0"
  shows
    "\<exists>n<N. (alpha / 2) * norm (G (x n)) ^ 2
      \<le> (f (x 0) - f (x N)) / real N"
proof -
  have sum_bound:
    "sum (\<lambda>n. (alpha / 2) * norm (G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - f (x N)"
    using gradient_descent_sum_weighted_gradient_norm_sq_bound[
      OF smooth gd feasible alpha_nonneg step_size] .

  have nonneg:
    "\<And>n. n < N \<Longrightarrow> 0 \<le> (alpha / 2) * norm (G (x n)) ^ 2"
  proof -
    fix n
    assume "n < N"
    have "0 \<le> alpha / 2"
      using alpha_nonneg by simp
    moreover have "0 \<le> norm (G (x n)) ^ 2"
      by simp
    ultimately show "0 \<le> (alpha / 2) * norm (G (x n)) ^ 2"
      by (rule mult_nonneg_nonneg)
  qed

  show ?thesis
    using exists_le_average_of_sum_bound[OF N_pos nonneg sum_bound] .
qed


subsection \<open>Locale form\<close>

context gradient_descent
begin

lemma sum_weighted_gradient_norm_sq_bound:
  "sum (\<lambda>n. (alpha / 2) * norm (G (x n)) ^ 2) {..<N}
    \<le> f (x 0) - f (x N)"
  using gradient_descent_sum_weighted_gradient_norm_sq_bound[
    OF smooth_bound iterates feasible alpha_nonneg step_size] .

lemma sum_weighted_gradient_norm_sq_bound_below:
  assumes lower: "B \<le> f (x N)"
  shows
    "sum (\<lambda>n. (alpha / 2) * norm (G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - B"
  using gradient_descent_sum_weighted_gradient_norm_sq_bound_below[
    OF smooth_bound iterates feasible alpha_nonneg step_size lower] .

lemma exists_small_weighted_gradient_norm_sq:
  assumes N_pos: "N > 0"
  shows
    "\<exists>n<N. (alpha / 2) * norm (G (x n)) ^ 2
      \<le> (f (x 0) - f (x N)) / real N"
  using gradient_descent_exists_small_weighted_gradient_norm_sq[
    OF smooth_bound iterates feasible alpha_nonneg step_size N_pos] .

lemma sum_gradient_norm_sq_bound:
  assumes alpha_pos: "0 < alpha"
  shows
    "sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - f (x N))"
  using gradient_descent_sum_gradient_norm_sq_bound[
    OF smooth_bound iterates feasible alpha_pos step_size] .

lemma sum_gradient_norm_sq_bound_below:
  assumes alpha_pos: "0 < alpha"
  assumes lower: "B \<le> f (x N)"
  shows
    "sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - B)"
  using gradient_descent_sum_gradient_norm_sq_bound_below[
    OF smooth_bound iterates feasible alpha_pos step_size lower] .

lemma average_gradient_norm_sq_bound:
  assumes alpha_pos: "0 < alpha"
  assumes N_pos: "N > 0"
  shows
    "(1 / real N) * sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}
      \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
  using gradient_descent_average_gradient_norm_sq_bound[
    OF smooth_bound iterates feasible alpha_pos step_size N_pos] .

lemma average_gradient_norm_sq_bound_below:
  assumes alpha_pos: "0 < alpha"
  assumes lower: "B \<le> f (x N)"
  assumes N_pos: "N > 0"
  shows
    "(1 / real N) * sum (\<lambda>n. norm (G (x n)) ^ 2) {..<N}
      \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
  using gradient_descent_average_gradient_norm_sq_bound_below[
    OF smooth_bound iterates feasible alpha_pos step_size lower N_pos] .

lemma exists_small_gradient_norm_sq:
  assumes alpha_pos: "0 < alpha"
  assumes N_pos: "N > 0"
  shows
    "\<exists>n<N. norm (G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
  using gradient_descent_exists_small_gradient_norm_sq[
    OF smooth_bound iterates feasible alpha_pos step_size N_pos] .

lemma exists_small_gradient_norm_sq_below:
  assumes alpha_pos: "0 < alpha"
  assumes lower: "B \<le> f (x N)"
  assumes N_pos: "N > 0"
  shows
    "\<exists>n<N. norm (G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
  using gradient_descent_exists_small_gradient_norm_sq_below[
    OF smooth_bound iterates feasible alpha_pos step_size lower N_pos] .

end


text \<open>
  This file gives the first rate-style consequences of the descent estimate
  for gradient descent.  The next natural step is to prove a stronger
  distance-to-solution one-step inequality under convexity, which can then be
  telescoped to obtain the standard O(1/N) function-value convergence rate.
\<close>

end