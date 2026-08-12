theory Projected_Gradient_Descent_Linear_Rate
  imports
    Strong_Convex
    Abstract_Descent
begin

section \<open>Linear convergence of projected gradient descent\<close>

text \<open>
This theory proves a robust linear convergence estimate for projected gradient
descent under a first-order strong-convexity lower-bound assumption.

The proof uses the projected one-step distance inequality from the projected
gradient descent development and the strong-convexity distance-gap lower bound.

The resulting contraction is
@{text \<open>(1 + alpha * mu) * norm (x (Suc n) - xstar) ^ 2 <= norm (x n - xstar) ^ 2\<close>}.
Equivalently, with @{text \<open>q = 1 / (1 + alpha * mu)\<close>}, we obtain
@{text \<open>norm (x N - xstar) ^ 2 <= q^N * norm (x 0 - xstar) ^ 2\<close>}.

This is not intended to be the sharpest possible textbook contraction factor.
Its purpose is to provide a stable Isabelle-friendly linear rate that follows
directly from the existing projected one-step inequality.
\<close>

subsection \<open>The linear-rate contraction factor\<close>

definition projected_gradient_linear_rate_factor :: "real \<Rightarrow> real \<Rightarrow> real"
where
  "projected_gradient_linear_rate_factor alpha mu =
     inverse (1 + alpha * mu)"

lemma projected_gradient_linear_rate_denominator_pos:
  fixes alpha mu :: real
  assumes alpha_nonneg: "0 \<le> alpha"
    and mu_nonneg: "0 \<le> mu"
  shows "0 < 1 + alpha * mu"
proof -
  have prod_nonneg: "0 \<le> alpha * mu"
    using alpha_nonneg mu_nonneg
    by (intro mult_nonneg_nonneg)

  show ?thesis
    using prod_nonneg
    by linarith
qed

lemma projected_gradient_linear_rate_factor_nonnegative:
  assumes alpha_nonneg: "0 \<le> alpha"
    and mu_nonneg: "0 \<le> mu"
  shows "0 \<le> projected_gradient_linear_rate_factor alpha mu"
proof -
  have denom_pos: "0 < 1 + alpha * mu"
    by (rule projected_gradient_linear_rate_denominator_pos[
        OF alpha_nonneg mu_nonneg])

  show ?thesis
    unfolding projected_gradient_linear_rate_factor_def
    using denom_pos by simp
qed

lemma projected_gradient_linear_rate_factor_positive:
  assumes alpha_nonneg: "0 \<le> alpha"
    and mu_nonneg: "0 \<le> mu"
  shows "0 < projected_gradient_linear_rate_factor alpha mu"
proof -
  have denom_pos: "0 < 1 + alpha * mu"
    by (rule projected_gradient_linear_rate_denominator_pos[
        OF alpha_nonneg mu_nonneg])

  show ?thesis
    unfolding projected_gradient_linear_rate_factor_def
    using denom_pos by simp
qed

lemma projected_gradient_linear_rate_factor_le_one:
  assumes alpha_nonneg: "0 \<le> alpha"
    and mu_nonneg: "0 \<le> mu"
  shows "projected_gradient_linear_rate_factor alpha mu \<le> 1"
proof -
  have prod_nonneg: "0 \<le> alpha * mu"
    by (rule mult_nonneg_nonneg[OF alpha_nonneg mu_nonneg])

  have denom_pos: "0 < 1 + alpha * mu"
    using prod_nonneg by linarith

  show ?thesis
    unfolding projected_gradient_linear_rate_factor_def
    using denom_pos prod_nonneg
    by (simp add: field_simps)
qed

lemma projected_gradient_linear_rate_factor_lt_one:
  assumes alpha_pos: "0 < alpha"
    and mu_pos: "0 < mu"
  shows "projected_gradient_linear_rate_factor alpha mu < 1"
proof -
  have prod_pos: "0 < alpha * mu"
    by (rule mult_pos_pos[OF alpha_pos mu_pos])

  have denom_pos: "0 < 1 + alpha * mu"
    using prod_pos by linarith

  show ?thesis
    unfolding projected_gradient_linear_rate_factor_def
    using denom_pos prod_pos
    by (simp add: field_simps)
qed

subsection \<open>One-step distance contraction\<close>

lemma projected_gradient_descent_strong_one_step_distance_contract:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes strong: "strongly_smooth_convex_on L mu C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on C f xstar"
  shows
    "(1 + alpha * mu) * norm (x (Suc n) - xstar) ^ 2
      \<le> norm (x n - xstar) ^ 2"
proof -
  let ?A = "norm (x n - xstar) ^ 2"
  let ?B = "norm (x (Suc n) - xstar) ^ 2"
  let ?gap = "f (x (Suc n)) - f xstar"

  have smooth: "smooth_convex_on L C f G"
    by (rule strongly_smooth_convex_onD_smooth[OF strong])

  have xnext_mem: "x (Suc n) \<in> C"
    using feasible
    by (rule feasible_iteratesD)

  have one_step:
    "?gap \<le> (?A - ?B) / (2 * alpha)"
    by (rule projected_gradient_descent_one_step_distance_bound_to_minimizer[
        OF smooth closed convex pgd feasible alpha_pos step_size minimizer,
        of n])

  have strong_gap:
    "(mu / 2) * ?B \<le> ?gap"
    by (rule strongly_smooth_convex_global_min_distance_gap[
        where L = L and G = G and xstar = xstar,
        OF strong minimizer xnext_mem])

  have gap_to_distance:
    "(mu / 2) * ?B \<le> (?A - ?B) / (2 * alpha)"
    using strong_gap one_step by linarith

  have denom_pos: "0 < 2 * alpha"
    using alpha_pos by simp

  have two_alpha_nonneg: "0 \<le> 2 * alpha"
    using alpha_pos by simp

  have multiplied:
    "(2 * alpha) * ((mu / 2) * ?B)
      \<le> (2 * alpha) * ((?A - ?B) / (2 * alpha))"
  proof (rule mult_left_mono)
    show "(mu / 2) * ?B \<le> (?A - ?B) / (2 * alpha)"
      using gap_to_distance .
    show "0 \<le> 2 * alpha"
      using two_alpha_nonneg .
  qed

  have scaled:
    "alpha * mu * ?B \<le> ?A - ?B"
  proof -
    have left_eq:
      "(2 * alpha) * ((mu / 2) * ?B) = alpha * mu * ?B"
      by (simp add: algebra_simps)

    have right_eq:
      "(2 * alpha) * ((?A - ?B) / (2 * alpha)) = ?A - ?B"
      using alpha_pos by simp

    show ?thesis
      using multiplied
      by (simp only: left_eq right_eq)
  qed

  have expand:
    "(1 + alpha * mu) * ?B = ?B + alpha * mu * ?B"
    by (simp add: algebra_simps)

  have "?B + alpha * mu * ?B \<le> ?A"
    using scaled by linarith

  then show ?thesis
    by (simp only: expand)
qed

lemma projected_gradient_descent_strong_one_step_distance_contract_factor:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes strong: "strongly_smooth_convex_on L mu C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on C f xstar"
  shows
    "norm (x (Suc n) - xstar) ^ 2
      \<le> projected_gradient_linear_rate_factor alpha mu
          * norm (x n - xstar) ^ 2"
proof -
  let ?A = "norm (x n - xstar) ^ 2"
  let ?B = "norm (x (Suc n) - xstar) ^ 2"
  let ?q = "projected_gradient_linear_rate_factor alpha mu"

  have strong_lb: "strong_convex_lower_bound_on mu C f G"
    by (rule strongly_smooth_convex_onD_strong[OF strong])

  have mu_nonneg: "0 \<le> mu"
    using strong_lb
    by (rule strong_convex_lower_bound_onD_nonneg)

  have alpha_nonneg: "0 \<le> alpha"
    using alpha_pos by linarith

  have denom_pos: "0 < 1 + alpha * mu"
    by (rule projected_gradient_linear_rate_denominator_pos[
        OF alpha_nonneg mu_nonneg])

  have contract:
    "(1 + alpha * mu) * ?B \<le> ?A"
    by (rule projected_gradient_descent_strong_one_step_distance_contract[
        OF strong closed convex pgd feasible alpha_pos step_size minimizer,
        of n])

  let ?D = "1 + alpha * mu"

  have D_nonzero: "?D \<noteq> 0"
    using denom_pos by simp

  have inv_nonneg: "0 \<le> inverse ?D"
    using denom_pos by simp

  have B_as_scaled:
    "?B = inverse ?D * (?D * ?B)"
  proof -
    have "inverse ?D * (?D * ?B) =
        (inverse ?D * ?D) * ?B"
      by (simp add: algebra_simps)
    also have "... = ?B"
      using D_nonzero by simp
    finally show ?thesis
      by simp
  qed

  have scaled_bound:
    "inverse ?D * (?D * ?B) \<le> inverse ?D * ?A"
  proof (rule mult_left_mono)
    show "?D * ?B \<le> ?A"
      using contract .
    show "0 \<le> inverse ?D"
      using inv_nonneg .
  qed

  have "?B \<le> inverse ?D * ?A"
  proof -
    have "?B = inverse ?D * (?D * ?B)"
      by (rule B_as_scaled)
    also have "... \<le> inverse ?D * ?A"
      by (rule scaled_bound)
    finally show ?thesis .
  qed

  then show ?thesis
    unfolding projected_gradient_linear_rate_factor_def
    by simp
qed


subsection \<open>Distance linear convergence\<close>

lemma projected_gradient_descent_distance_sq_linear_rate_feasible:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes strong: "strongly_smooth_convex_on L mu C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on C f xstar"
  shows
    "norm (x N - xstar) ^ 2
      \<le> projected_gradient_linear_rate_factor alpha mu ^ N
          * norm (x 0 - xstar) ^ 2"
proof -
  let ?q = "projected_gradient_linear_rate_factor alpha mu"
  define a where "a n = norm (x n - xstar) ^ 2" for n

  have strong_lb: "strong_convex_lower_bound_on mu C f G"
    by (rule strongly_smooth_convex_onD_strong[OF strong])

  have mu_nonneg: "0 \<le> mu"
    using strong_lb
    by (rule strong_convex_lower_bound_onD_nonneg)

  have alpha_nonneg: "0 \<le> alpha"
    using alpha_pos by linarith

  have q_nonneg: "0 \<le> ?q"
    by (rule projected_gradient_linear_rate_factor_nonnegative[
        OF alpha_nonneg mu_nonneg])

  have step: "\<And>n. a (Suc n) \<le> ?q * a n"
  proof -
    fix n
    show "a (Suc n) \<le> ?q * a n"
      unfolding a_def
      by (rule projected_gradient_descent_strong_one_step_distance_contract_factor[
          OF strong closed convex pgd feasible alpha_pos step_size minimizer,
          of n])
  qed

  have "a N \<le> ?q ^ N * a 0"
    by (rule sequence_linear_rate_from_step[
        where a = a and q = ?q,
        OF q_nonneg step])

  then show ?thesis
    unfolding a_def .
qed

lemma projected_gradient_descent_distance_sq_linear_rate:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes strong: "strongly_smooth_convex_on L mu C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on C f xstar"
  shows
    "norm (x N - xstar) ^ 2
      \<le> projected_gradient_linear_rate_factor alpha mu ^ N
          * norm (x 0 - xstar) ^ 2"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
        OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_distance_sq_linear_rate_feasible[
        OF strong closed convex pgd feasible alpha_pos step_size minimizer])
qed


subsection \<open>Function-value linear convergence\<close>

lemma projected_gradient_descent_function_value_linear_rate_Suc_feasible:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes strong: "strongly_smooth_convex_on L mu C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and feasible: "feasible_iterates C x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on C f xstar"
  shows
    "f (x (Suc N)) - f xstar
      \<le> projected_gradient_linear_rate_factor alpha mu ^ N
          * norm (x 0 - xstar) ^ 2 / (2 * alpha)"
proof -
  let ?q = "projected_gradient_linear_rate_factor alpha mu"
  let ?A = "norm (x N - xstar) ^ 2"
  let ?B = "norm (x (Suc N) - xstar) ^ 2"
  let ?D0 = "norm (x 0 - xstar) ^ 2"
  let ?gap = "f (x (Suc N)) - f xstar"

  have smooth: "smooth_convex_on L C f G"
    by (rule strongly_smooth_convex_onD_smooth[OF strong])

  have one_step:
    "?gap \<le> (?A - ?B) / (2 * alpha)"
    by (rule projected_gradient_descent_one_step_distance_bound_to_minimizer[
        OF smooth closed convex pgd feasible alpha_pos step_size minimizer,
        of N])

  have denom_pos: "0 < 2 * alpha"
    using alpha_pos by simp

  have numerator_le: "?A - ?B \<le> ?A"
    by simp

  have divided:
    "(?A - ?B) / (2 * alpha) \<le> ?A / (2 * alpha)"
  proof (rule divide_right_mono)
    show "?A - ?B \<le> ?A"
      using numerator_le .
    show "0 \<le> 2 * alpha"
      using denom_pos by linarith
  qed

  have gap_le_A:
    "?gap \<le> ?A / (2 * alpha)"
    using one_step divided by linarith

  have dist_rate:
    "?A \<le> ?q ^ N * ?D0"
    by (rule projected_gradient_descent_distance_sq_linear_rate_feasible[
        OF strong closed convex pgd feasible alpha_pos step_size minimizer,
        of N])

  have dist_rate_div:
    "?A / (2 * alpha) \<le> (?q ^ N * ?D0) / (2 * alpha)"
  proof (rule divide_right_mono)
    show "?A \<le> ?q ^ N * ?D0"
      using dist_rate .
    show "0 \<le> 2 * alpha"
      using denom_pos by linarith
  qed

  show ?thesis
    using gap_le_A dist_rate_div
    by linarith
qed

lemma projected_gradient_descent_function_value_linear_rate_Suc:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes strong: "strongly_smooth_convex_on L mu C f G"
    and closed: "closed C"
    and convex: "convex C"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on C f xstar"
  shows
    "f (x (Suc N)) - f xstar
      \<le> projected_gradient_linear_rate_factor alpha mu ^ N
          * norm (x 0 - xstar) ^ 2 / (2 * alpha)"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
        OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_function_value_linear_rate_Suc_feasible[
        OF strong closed convex pgd feasible alpha_pos step_size minimizer])
qed

lemma projected_gradient_descent_function_value_linear_rate_feasible:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes strong: "strongly_smooth_convex_on L mu C f G"
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
      \<le> projected_gradient_linear_rate_factor alpha mu ^ (N - 1)
          * norm (x 0 - xstar) ^ 2 / (2 * alpha)"
proof (cases N)
  case 0
  then show ?thesis
    using N_pos by simp
next
  case (Suc n)

  have bound:
    "f (x (Suc n)) - f xstar
      \<le> projected_gradient_linear_rate_factor alpha mu ^ n
          * norm (x 0 - xstar) ^ 2 / (2 * alpha)"
    by (rule projected_gradient_descent_function_value_linear_rate_Suc_feasible[
        OF strong closed convex pgd feasible alpha_pos step_size minimizer,
        of n])

  show ?thesis
    using bound Suc by simp
qed

lemma projected_gradient_descent_function_value_linear_rate:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes strong: "strongly_smooth_convex_on L mu C f G"
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
      \<le> projected_gradient_linear_rate_factor alpha mu ^ (N - 1)
          * norm (x 0 - xstar) ^ 2 / (2 * alpha)"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
        OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_function_value_linear_rate_feasible[
        OF strong closed convex pgd feasible alpha_pos step_size minimizer N_pos])
qed


subsection \<open>Strict contraction under positive strong convexity\<close>

lemma projected_gradient_descent_strict_rate_factor:
  assumes alpha_pos: "0 < alpha"
    and mu_pos: "0 < mu"
  shows "projected_gradient_linear_rate_factor alpha mu < 1"
  by (rule projected_gradient_linear_rate_factor_lt_one[
      OF alpha_pos mu_pos])

lemma projected_gradient_descent_rate_factor_nonnegative_from_strong:
  assumes strong: "strongly_smooth_convex_on L mu C f G"
    and alpha_pos: "0 < alpha"
  shows "0 \<le> projected_gradient_linear_rate_factor alpha mu"
proof -
  have strong_lb: "strong_convex_lower_bound_on mu C f G"
    by (rule strongly_smooth_convex_onD_strong[OF strong])

  have mu_nonneg: "0 \<le> mu"
    using strong_lb
    by (rule strong_convex_lower_bound_onD_nonneg)

  have alpha_nonneg: "0 \<le> alpha"
    using alpha_pos by linarith

  show ?thesis
    by (rule projected_gradient_linear_rate_factor_nonnegative[
        OF alpha_nonneg mu_nonneg])
qed


subsection \<open>Locale form\<close>

locale projected_gradient_descent_linear_rate =
  projected_gradient_descent C L alpha f G x
  for C :: "'a::{real_inner,heine_borel} set"
    and L alpha :: real
    and f :: "'a \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
    and x :: "nat \<Rightarrow> 'a" +
  fixes mu :: real
  assumes strong_lower_bound: "strong_convex_lower_bound_on mu C f G"
begin

lemma strongly_smooth_convex_on_self:
  "strongly_smooth_convex_on L mu C f G"
proof (rule strongly_smooth_convex_onI)
  show "smooth_convex_on L C f G"
    by (rule smooth)
next
  show "strong_convex_lower_bound_on mu C f G"
    by (rule strong_lower_bound)
qed

lemma strong_nonneg:
  "0 \<le> mu"
  using strong_lower_bound
  by (rule strong_convex_lower_bound_onD_nonneg)

lemma rate_factor_nonnegative:
  assumes alpha_pos: "0 < alpha"
  shows "0 \<le> projected_gradient_linear_rate_factor alpha mu"
proof -
  have alpha_nonneg: "0 \<le> alpha"
    using alpha_pos by linarith

  show ?thesis
    by (rule projected_gradient_linear_rate_factor_nonnegative[
        OF alpha_nonneg strong_nonneg])
qed

lemma rate_factor_positive:
  assumes alpha_pos: "0 < alpha"
  shows "0 < projected_gradient_linear_rate_factor alpha mu"
proof -
  have alpha_nonneg: "0 \<le> alpha"
    using alpha_pos by linarith

  show ?thesis
    by (rule projected_gradient_linear_rate_factor_positive[
        OF alpha_nonneg strong_nonneg])
qed

lemma rate_factor_le_one:
  assumes alpha_pos: "0 < alpha"
  shows "projected_gradient_linear_rate_factor alpha mu \<le> 1"
proof -
  have alpha_nonneg: "0 \<le> alpha"
    using alpha_pos by linarith

  show ?thesis
    by (rule projected_gradient_linear_rate_factor_le_one[
        OF alpha_nonneg strong_nonneg])
qed

lemma rate_factor_lt_one:
  assumes alpha_pos: "0 < alpha"
    and mu_pos: "0 < mu"
  shows "projected_gradient_linear_rate_factor alpha mu < 1"
  by (rule projected_gradient_linear_rate_factor_lt_one[
      OF alpha_pos mu_pos])

lemma one_step_distance_contract:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on C f xstar"
  shows
    "(1 + alpha * mu) * norm (x (Suc n) - xstar) ^ 2
      \<le> norm (x n - xstar) ^ 2"
  by (rule projected_gradient_descent_strong_one_step_distance_contract[
      OF strongly_smooth_convex_on_self closed convex iterates feasible
         alpha_pos step_size minimizer,
      of n])

lemma one_step_distance_contract_factor:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on C f xstar"
  shows
    "norm (x (Suc n) - xstar) ^ 2
      \<le> projected_gradient_linear_rate_factor alpha mu
          * norm (x n - xstar) ^ 2"
  by (rule projected_gradient_descent_strong_one_step_distance_contract_factor[
      OF strongly_smooth_convex_on_self closed convex iterates feasible
         alpha_pos step_size minimizer,
      of n])

lemma distance_sq_linear_rate:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on C f xstar"
  shows
    "norm (x N - xstar) ^ 2
      \<le> projected_gradient_linear_rate_factor alpha mu ^ N
          * norm (x 0 - xstar) ^ 2"
  by (rule projected_gradient_descent_distance_sq_linear_rate[
      OF strongly_smooth_convex_on_self closed convex iterates initial_feasible
         alpha_pos step_size minimizer,
      of N])

lemma function_value_linear_rate_Suc:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on C f xstar"
  shows
    "f (x (Suc N)) - f xstar
      \<le> projected_gradient_linear_rate_factor alpha mu ^ N
          * norm (x 0 - xstar) ^ 2 / (2 * alpha)"
  by (rule projected_gradient_descent_function_value_linear_rate_Suc[
      OF strongly_smooth_convex_on_self closed convex iterates initial_feasible
         alpha_pos step_size minimizer,
      of N])

lemma function_value_linear_rate:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on C f xstar"
    and N_pos: "N > 0"
  shows
    "f (x N) - f xstar
      \<le> projected_gradient_linear_rate_factor alpha mu ^ (N - 1)
          * norm (x 0 - xstar) ^ 2 / (2 * alpha)"
  by (rule projected_gradient_descent_function_value_linear_rate[
      OF strongly_smooth_convex_on_self closed convex iterates initial_feasible
         alpha_pos step_size minimizer N_pos])

end


text \<open>
The main distance-rate theorem is
@{thm projected_gradient_descent_distance_sq_linear_rate}.  It gives an
exponential decay estimate for squared distance to a global minimizer, with
factor @{term projected_gradient_linear_rate_factor}.

The main function-value version is
@{thm projected_gradient_descent_function_value_linear_rate_Suc}.  It bounds
the function-value gap at the next iterate by the same linear factor applied to
the initial squared distance.
\<close>

end