theory Projected_Gradient_Mapping_Rates
  imports Projected_Gradient_Mapping
begin

section \<open>Projected-gradient mapping residual rates\<close>

text \<open>
This theory is the technical residual-rate engine for projected-gradient
descent.

The previous theory introduces the projected-gradient mapping and proves its
fixed-point and optimality properties.  This theory proves finite-horizon
estimates for the squared norm of that mapping along projected-gradient
descent iterates.

The main proof pattern is the standard first-order complexity argument:
a one-step progress inequality controls the squared projected-gradient mapping
norm by the objective decrease, and an abstract telescoping argument converts
this into finite-sum, average, and small-residual estimates.

This theory deliberately stays at the level of squared mapping norms.  The
next theory packages these estimates into user-facing residual convergence and
epsilon-stationarity certificates.
\<close>

subsection \<open>Step length and projected-gradient mapping norm\<close>

lemma projected_gradient_step_distance_sq_eq_mapping_norm_sq:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes alpha_pos: "0 < alpha"
  shows
    "norm (projected_gradient_step C alpha G x - x) ^ 2 =
      alpha ^ 2 * norm (projected_gradient_mapping C alpha G x) ^ 2"
proof -
  let ?p = "projected_gradient_step C alpha G x"
  let ?M = "projected_gradient_mapping C alpha G x"

  have alpha_nonzero: "alpha \<noteq> 0"
    using alpha_pos by simp

  have relation: "scaleR alpha ?M = x - ?p"
    using projected_gradient_mapping_step_relation[
      where C = C and G = G and x = x,
      OF alpha_nonzero]
    by simp

  have "norm (?p - x) ^ 2 = norm (x - ?p) ^ 2"
    by (simp add: norm_minus_commute)
  also have "... = norm (scaleR alpha ?M) ^ 2"
    using relation by simp
  also have "... = alpha ^ 2 * norm ?M ^ 2"
    using alpha_pos
    by (simp add: power2_eq_square)
  finally show ?thesis .
qed

lemma projected_gradient_mapping_norm_sq_eq_step_distance_sq:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes alpha_pos: "0 < alpha"
  shows
    "norm (projected_gradient_mapping C alpha G x) ^ 2 =
      norm (projected_gradient_step C alpha G x - x) ^ 2 / alpha ^ 2"
proof -
  let ?p = "projected_gradient_step C alpha G x"
  let ?M = "projected_gradient_mapping C alpha G x"

  have dist:
    "norm (?p - x) ^ 2 = alpha ^ 2 * norm ?M ^ 2"
    by (rule projected_gradient_step_distance_sq_eq_mapping_norm_sq[OF alpha_pos])

  have alpha_sq_pos: "0 < alpha ^ 2"
    using alpha_pos by simp

  have "norm (?p - x) ^ 2 / alpha ^ 2 =
    alpha ^ 2 * norm ?M ^ 2 / alpha ^ 2"
    using dist by simp
  also have "... = norm ?M ^ 2"
    using alpha_sq_pos by simp
  finally show ?thesis
    by simp
qed

subsection \<open>One-step progress in terms of the mapping residual\<close>

lemma projected_gradient_step_progress_mapping:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and x_mem: "x \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
  shows
    "(alpha / 2) * norm (projected_gradient_mapping C alpha G x) ^ 2
      \<le> f x - f (projected_gradient_step C alpha G x)"
proof -
  let ?p = "projected_gradient_step C alpha G x"
  let ?M = "projected_gradient_mapping C alpha G x"

  have step_norm:
    "(1 / (2 * alpha)) * norm (?p - x) ^ 2 \<le> f x - f ?p"
    by (rule projected_gradient_step_progress_step_norm[
      OF smooth closed convex x_mem alpha_pos step_size])

  have dist:
    "norm (?p - x) ^ 2 = alpha ^ 2 * norm ?M ^ 2"
    by (rule projected_gradient_step_distance_sq_eq_mapping_norm_sq[OF alpha_pos])

  have rewrite:
    "(1 / (2 * alpha)) * norm (?p - x) ^ 2 =
      (alpha / 2) * norm ?M ^ 2"
    using dist alpha_pos
    by (simp add: field_simps power2_eq_square)

  show ?thesis
    using step_norm rewrite by simp
qed

lemma projected_gradient_descent_step_progress_mapping:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
  shows
    "(alpha / 2) * norm (projected_gradient_mapping C alpha G (x n)) ^ 2
      \<le> f (x n) - f (x (Suc n))"
proof -
  have xn_mem: "x n \<in> C"
    using feasible by (rule feasible_iteratesD)

  have step_eq:
    "x (Suc n) = projected_gradient_step C alpha G (x n)"
    using pgd by (rule projected_gradient_descent_iteratesD)

  have progress:
    "(alpha / 2) * norm (projected_gradient_mapping C alpha G (x n)) ^ 2
      \<le> f (x n) - f (projected_gradient_step C alpha G (x n))"
    by (rule projected_gradient_step_progress_mapping[
      OF smooth closed convex xn_mem alpha_pos step_size])

  show ?thesis
    using progress step_eq by simp
qed

subsection \<open>Finite-sum mapping-residual bounds\<close>

text \<open>
The following estimates are the summability form of the residual-rate
argument.  The weighted bound is the direct telescoping consequence of the
one-step progress inequality.  The unweighted bounds divide out the positive
stepsize factor.
\<close>

lemma projected_gradient_descent_sum_weighted_mapping_norm_sq_bound_feasible:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
  shows
    "sum (\<lambda>n. (alpha / 2) *
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - f (x N)"
proof (rule sum_progress_le_initial_gap)
  fix n
  assume "n < N"

  show
    "(alpha / 2) * norm (projected_gradient_mapping C alpha G (x n)) ^ 2
      \<le> f (x n) - f (x (Suc n))"
    by (rule projected_gradient_descent_step_progress_mapping[
      OF smooth closed convex pgd feasible alpha_pos step_size])
qed

lemma projected_gradient_descent_sum_weighted_mapping_norm_sq_bound:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
  shows
    "sum (\<lambda>n. (alpha / 2) *
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - f (x N)"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_sum_weighted_mapping_norm_sq_bound_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size])
qed

lemma projected_gradient_descent_sum_weighted_mapping_norm_sq_bound_below_feasible:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and lower: "B \<le> f (x N)"
  shows
    "sum (\<lambda>n. (alpha / 2) *
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - B"
proof (rule sum_progress_le_initial_minus_lower_bound)
  fix n
  assume "n < N"

  show
    "(alpha / 2) * norm (projected_gradient_mapping C alpha G (x n)) ^ 2
      \<le> f (x n) - f (x (Suc n))"
    by (rule projected_gradient_descent_step_progress_mapping[
      OF smooth closed convex pgd feasible alpha_pos step_size])
next
  show "B \<le> f (x N)"
    by (rule lower)
qed

lemma projected_gradient_descent_sum_weighted_mapping_norm_sq_bound_below:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and lower: "B \<le> f (x N)"
  shows
    "sum (\<lambda>n. (alpha / 2) *
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - B"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_sum_weighted_mapping_norm_sq_bound_below_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size lower])
qed

lemma projected_gradient_descent_sum_mapping_norm_sq_bound_feasible:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
  shows
    "sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - f (x N))"
proof -
  have weighted:
    "sum (\<lambda>n. (alpha / 2) *
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - f (x N)"
    by (rule projected_gradient_descent_sum_weighted_mapping_norm_sq_bound_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size])

  have coeff_pos: "0 < alpha / 2"
    using alpha_pos by simp

  have weighted_eq:
    "sum (\<lambda>n. (alpha / 2) *
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      =
      (alpha / 2) *
      sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}"
    by (simp add: sum_distrib_left)

  have
    "(alpha / 2) *
      sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - f (x N)"
    using weighted weighted_eq by simp

  then show ?thesis
    using coeff_pos by (simp add: field_simps)
qed

lemma projected_gradient_descent_sum_mapping_norm_sq_bound:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
  shows
    "sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - f (x N))"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_sum_mapping_norm_sq_bound_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size])
qed

lemma projected_gradient_descent_sum_mapping_norm_sq_bound_below_feasible:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and lower: "B \<le> f (x N)"
  shows
    "sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - B)"
proof -
  have weighted:
    "sum (\<lambda>n. (alpha / 2) *
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - B"
    by (rule projected_gradient_descent_sum_weighted_mapping_norm_sq_bound_below_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size lower])

  have coeff_pos: "0 < alpha / 2"
    using alpha_pos by simp

  have weighted_eq:
    "sum (\<lambda>n. (alpha / 2) *
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      =
      (alpha / 2) *
      sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}"
    by (simp add: sum_distrib_left)

  have
    "(alpha / 2) *
      sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - B"
    using weighted weighted_eq by simp

  then show ?thesis
    using coeff_pos by (simp add: field_simps)
qed

lemma projected_gradient_descent_sum_mapping_norm_sq_bound_below:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and lower: "B \<le> f (x N)"
  shows
    "sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - B)"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_sum_mapping_norm_sq_bound_below_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size lower])
qed

subsection \<open>Average mapping-residual bounds\<close>

text \<open>
Averaging the finite-sum estimates gives the usual O(1/N) bound on the
average squared projected-gradient mapping norm.
\<close>

lemma projected_gradient_descent_average_mapping_norm_sq_bound_feasible:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and N_pos: "N > 0"
  shows
    "(1 / real N) *
      sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
proof -
  have sum_bound:
    "sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - f (x N))"
    by (rule projected_gradient_descent_sum_mapping_norm_sq_bound_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size])

  have N_real_pos: "0 < real N"
    using N_pos by simp

  have
    "(1 / real N) *
      sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le>
      (1 / real N) * ((2 / alpha) * (f (x 0) - f (x N)))"
    using sum_bound N_real_pos
    by (intro mult_left_mono) simp_all

  also have
    "... = (2 / (alpha * real N)) * (f (x 0) - f (x N))"
    using alpha_pos N_real_pos
    by (simp add: field_simps)

  finally show ?thesis .
qed

lemma projected_gradient_descent_average_mapping_norm_sq_bound:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and N_pos: "N > 0"
  shows
    "(1 / real N) *
      sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_average_mapping_norm_sq_bound_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size N_pos])
qed

lemma projected_gradient_descent_average_mapping_norm_sq_bound_below_feasible:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and lower: "B \<le> f (x N)"
    and N_pos: "N > 0"
  shows
    "(1 / real N) *
      sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
proof -
  have sum_bound:
    "sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - B)"
    by (rule projected_gradient_descent_sum_mapping_norm_sq_bound_below_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size lower])

  have N_real_pos: "0 < real N"
    using N_pos by simp

  have
    "(1 / real N) *
      sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le>
      (1 / real N) * ((2 / alpha) * (f (x 0) - B))"
    using sum_bound N_real_pos
    by (intro mult_left_mono) simp_all

  also have
    "... = (2 / (alpha * real N)) * (f (x 0) - B)"
    using alpha_pos N_real_pos
    by (simp add: field_simps)

  finally show ?thesis .
qed

lemma projected_gradient_descent_average_mapping_norm_sq_bound_below:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and lower: "B \<le> f (x N)"
    and N_pos: "N > 0"
  shows
    "(1 / real N) *
      sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_average_mapping_norm_sq_bound_below_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size lower N_pos])
qed

subsection \<open>Small mapping-residual consequences\<close>

text \<open>
The average bound implies that at least one of the first N iterates has
squared projected-gradient mapping norm no larger than the average.  These
lemmas are the technical small-residual estimates later converted into
epsilon-stationarity certificates.
\<close>

lemma projected_gradient_descent_exists_small_mapping_norm_sq_feasible:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and N_pos: "N > 0"
  shows
    "\<exists>n<N.
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
proof -
  have sum_bound:
    "sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - f (x N))"
    by (rule projected_gradient_descent_sum_mapping_norm_sq_bound_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size])

  have nonneg:
    "\<And>n. n < N \<Longrightarrow>
      0 \<le> norm (projected_gradient_mapping C alpha G (x n)) ^ 2"
    by simp

  obtain n where n_lt: "n < N"
    and n_bound:
      "norm (projected_gradient_mapping C alpha G (x n)) ^ 2
        \<le> ((2 / alpha) * (f (x 0) - f (x N))) / real N"
    using exists_le_average_of_sum_bound[OF N_pos nonneg sum_bound]
    by auto

  have rewrite:
    "((2 / alpha) * (f (x 0) - f (x N))) / real N
      =
      (2 / (alpha * real N)) * (f (x 0) - f (x N))"
    using alpha_pos N_pos
    by (simp add: field_simps)

  have
    "norm (projected_gradient_mapping C alpha G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
    using n_bound rewrite by simp

  then show ?thesis
    using n_lt by auto
qed

lemma projected_gradient_descent_exists_small_mapping_norm_sq:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and N_pos: "N > 0"
  shows
    "\<exists>n<N.
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_exists_small_mapping_norm_sq_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size N_pos])
qed

lemma projected_gradient_descent_exists_small_mapping_norm_sq_below_feasible:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and lower: "B \<le> f (x N)"
    and N_pos: "N > 0"
  shows
    "\<exists>n<N.
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
proof -
  have sum_bound:
    "sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - B)"
    by (rule projected_gradient_descent_sum_mapping_norm_sq_bound_below_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size lower])

  have nonneg:
    "\<And>n. n < N \<Longrightarrow>
      0 \<le> norm (projected_gradient_mapping C alpha G (x n)) ^ 2"
    by simp

  obtain n where n_lt: "n < N"
    and n_bound:
      "norm (projected_gradient_mapping C alpha G (x n)) ^ 2
        \<le> ((2 / alpha) * (f (x 0) - B)) / real N"
    using exists_le_average_of_sum_bound[OF N_pos nonneg sum_bound]
    by auto

  have rewrite:
    "((2 / alpha) * (f (x 0) - B)) / real N
      =
      (2 / (alpha * real N)) * (f (x 0) - B)"
    using alpha_pos N_pos
    by (simp add: field_simps)

  have
    "norm (projected_gradient_mapping C alpha G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
    using n_bound rewrite by simp

  then show ?thesis
    using n_lt by auto
qed

lemma projected_gradient_descent_exists_small_mapping_norm_sq_below:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and lower: "B \<le> f (x N)"
    and N_pos: "N > 0"
  shows
    "\<exists>n<N.
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_exists_small_mapping_norm_sq_below_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size lower N_pos])
qed

subsection \<open>Minimizer-based mapping-residual bounds\<close>

text \<open>
When a global minimizer is available, the lower bound can be specialized to
the optimal value.  These versions are the most convenient form for complexity
statements depending on the initial objective gap.
\<close>

lemma projected_gradient_descent_sum_mapping_norm_sq_bound_to_minimizer_feasible:
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
    "sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - f xstar)"
proof -
  have xN_mem: "x N \<in> C"
    using feasible by (rule feasible_iteratesD)

  have lower: "f xstar \<le> f (x N)"
    by (rule global_min_onD[OF minimizer xN_mem])

  show ?thesis
    by (rule projected_gradient_descent_sum_mapping_norm_sq_bound_below_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size lower])
qed

lemma projected_gradient_descent_sum_mapping_norm_sq_bound_to_minimizer:
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
  shows
    "sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - f xstar)"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_sum_mapping_norm_sq_bound_to_minimizer_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size minimizer])
qed

lemma projected_gradient_descent_exists_small_mapping_norm_sq_to_minimizer_feasible:
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
    "\<exists>n<N.
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - f xstar)"
proof -
  have xN_mem: "x N \<in> C"
    using feasible by (rule feasible_iteratesD)

  have lower: "f xstar \<le> f (x N)"
    by (rule global_min_onD[OF minimizer xN_mem])

  show ?thesis
    by (rule projected_gradient_descent_exists_small_mapping_norm_sq_below_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size lower N_pos])
qed

lemma projected_gradient_descent_exists_small_mapping_norm_sq_to_minimizer:
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
    "\<exists>n<N.
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - f xstar)"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_exists_small_mapping_norm_sq_to_minimizer_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size minimizer N_pos])
qed

subsection \<open>Recommended mapping-rate interface\<close>

text \<open>
The following theorem groups collect the main reusable consequences of this
theory.  They separate the technical rate engine from the later residual
notation and epsilon-stationarity layer.
\<close>

lemmas projected_gradient_mapping_step_length_results =
  projected_gradient_step_distance_sq_eq_mapping_norm_sq
  projected_gradient_mapping_norm_sq_eq_step_distance_sq

lemmas projected_gradient_mapping_progress_results =
  projected_gradient_step_progress_mapping
  projected_gradient_descent_step_progress_mapping

lemmas projected_gradient_mapping_weighted_sum_results =
  projected_gradient_descent_sum_weighted_mapping_norm_sq_bound_feasible
  projected_gradient_descent_sum_weighted_mapping_norm_sq_bound
  projected_gradient_descent_sum_weighted_mapping_norm_sq_bound_below_feasible
  projected_gradient_descent_sum_weighted_mapping_norm_sq_bound_below

lemmas projected_gradient_mapping_sum_results =
  projected_gradient_descent_sum_mapping_norm_sq_bound_feasible
  projected_gradient_descent_sum_mapping_norm_sq_bound
  projected_gradient_descent_sum_mapping_norm_sq_bound_below_feasible
  projected_gradient_descent_sum_mapping_norm_sq_bound_below
  projected_gradient_descent_sum_mapping_norm_sq_bound_to_minimizer_feasible
  projected_gradient_descent_sum_mapping_norm_sq_bound_to_minimizer

lemmas projected_gradient_mapping_average_results =
  projected_gradient_descent_average_mapping_norm_sq_bound_feasible
  projected_gradient_descent_average_mapping_norm_sq_bound
  projected_gradient_descent_average_mapping_norm_sq_bound_below_feasible
  projected_gradient_descent_average_mapping_norm_sq_bound_below

lemmas projected_gradient_mapping_small_residual_results =
  projected_gradient_descent_exists_small_mapping_norm_sq_feasible
  projected_gradient_descent_exists_small_mapping_norm_sq
  projected_gradient_descent_exists_small_mapping_norm_sq_below_feasible
  projected_gradient_descent_exists_small_mapping_norm_sq_below
  projected_gradient_descent_exists_small_mapping_norm_sq_to_minimizer_feasible
  projected_gradient_descent_exists_small_mapping_norm_sq_to_minimizer

lemmas projected_gradient_mapping_rate_engine =
  projected_gradient_mapping_step_length_results
  projected_gradient_mapping_progress_results
  projected_gradient_mapping_weighted_sum_results
  projected_gradient_mapping_sum_results
  projected_gradient_mapping_average_results
  projected_gradient_mapping_small_residual_results

subsection \<open>Locale form\<close>

context projected_gradient_descent
begin

lemma step_progress_mapping:
  assumes alpha_pos: "0 < alpha"
  shows
    "(alpha / 2) * norm (projected_gradient_mapping C alpha G (x n)) ^ 2
      \<le> f (x n) - f (x (Suc n))"
  by (rule projected_gradient_descent_step_progress_mapping[
    OF smooth closed convex iterates feasible alpha_pos step_size])

lemma sum_weighted_mapping_norm_sq_bound:
  assumes alpha_pos: "0 < alpha"
  shows
    "sum (\<lambda>n. (alpha / 2) *
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - f (x N)"
  by (rule projected_gradient_descent_sum_weighted_mapping_norm_sq_bound_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size])

lemma sum_weighted_mapping_norm_sq_bound_below:
  assumes alpha_pos: "0 < alpha"
    and lower: "B \<le> f (x N)"
  shows
    "sum (\<lambda>n. (alpha / 2) *
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> f (x 0) - B"
  by (rule projected_gradient_descent_sum_weighted_mapping_norm_sq_bound_below_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size lower])

lemma sum_mapping_norm_sq_bound:
  assumes alpha_pos: "0 < alpha"
  shows
    "sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - f (x N))"
  by (rule projected_gradient_descent_sum_mapping_norm_sq_bound_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size])

lemma sum_mapping_norm_sq_bound_below:
  assumes alpha_pos: "0 < alpha"
    and lower: "B \<le> f (x N)"
  shows
    "sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - B)"
  by (rule projected_gradient_descent_sum_mapping_norm_sq_bound_below_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size lower])

lemma average_mapping_norm_sq_bound:
  assumes alpha_pos: "0 < alpha"
    and N_pos: "N > 0"
  shows
    "(1 / real N) *
      sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
  by (rule projected_gradient_descent_average_mapping_norm_sq_bound_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size N_pos])

lemma average_mapping_norm_sq_bound_below:
  assumes alpha_pos: "0 < alpha"
    and lower: "B \<le> f (x N)"
    and N_pos: "N > 0"
  shows
    "(1 / real N) *
      sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
  by (rule projected_gradient_descent_average_mapping_norm_sq_bound_below_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size lower N_pos])

lemma exists_small_mapping_norm_sq:
  assumes alpha_pos: "0 < alpha"
    and N_pos: "N > 0"
  shows
    "\<exists>n<N.
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
  by (rule projected_gradient_descent_exists_small_mapping_norm_sq_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size N_pos])

lemma exists_small_mapping_norm_sq_below:
  assumes alpha_pos: "0 < alpha"
    and lower: "B \<le> f (x N)"
    and N_pos: "N > 0"
  shows
    "\<exists>n<N.
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
  by (rule projected_gradient_descent_exists_small_mapping_norm_sq_below_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size lower N_pos])

lemma sum_mapping_norm_sq_bound_to_minimizer:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on C f xstar"
  shows
    "sum (\<lambda>n. norm (projected_gradient_mapping C alpha G (x n)) ^ 2) {..<N}
      \<le> (2 / alpha) * (f (x 0) - f xstar)"
  by (rule projected_gradient_descent_sum_mapping_norm_sq_bound_to_minimizer_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size minimizer])

lemma exists_small_mapping_norm_sq_to_minimizer:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on C f xstar"
    and N_pos: "N > 0"
  shows
    "\<exists>n<N.
      norm (projected_gradient_mapping C alpha G (x n)) ^ 2
      \<le> (2 / (alpha * real N)) * (f (x 0) - f xstar)"
  by (rule projected_gradient_descent_exists_small_mapping_norm_sq_to_minimizer_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size minimizer N_pos])

end

text \<open>
The main reusable consequences of this theory are:

  • @{text \<open>projected_gradient_descent_sum_mapping_norm_sq_bound\<close>};
  • @{text \<open>projected_gradient_descent_average_mapping_norm_sq_bound\<close>};
  • @{text \<open>projected_gradient_descent_exists_small_mapping_norm_sq\<close>};
  • @{text \<open>projected_gradient_descent_exists_small_mapping_norm_sq_to_minimizer\<close>}.

Together, these state that the squared projected-gradient mapping residual
satisfies finite-sum, average, and finite-horizon small-residual bounds along
projected-gradient descent.

The theorem group @{text \<open>projected_gradient_mapping_rate_engine\<close>} collects the main
technical rate interface of this theory.
\<close>

end