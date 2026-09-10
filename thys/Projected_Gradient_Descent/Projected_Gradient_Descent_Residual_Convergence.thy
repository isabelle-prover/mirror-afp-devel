theory Projected_Gradient_Descent_Residual_Convergence
  imports Projected_Gradient_Mapping_Rates
begin

section \<open>Residual convergence certificates for projected gradient descent\<close>

text \<open>
This theory is the residual-complexity layer of the projected-gradient
descent development.

The previous theory proves finite-horizon estimates for the squared norm of
the projected-gradient mapping.  Here we package those estimates as
user-facing residual convergence and epsilon-stationarity certificates.

The projected-gradient residual is the norm of the projected-gradient mapping.
It is the constrained analogue of the gradient norm in unconstrained smooth
optimization.  Small residual therefore gives an approximate first-order
stationarity certificate for constrained smooth convex optimization.

The main high-level result of this theory is a finite-horizon complexity
statement: if the horizon N is large enough relative to the initial objective
gap and the desired tolerance eps, then at least one of the first N
projected-gradient iterates has projected-gradient residual at most eps.

The result is intentionally stated as a finite-horizon certificate rather than
as a filter-limit statement.  This is the form most commonly used in
first-order complexity estimates, and it keeps the statement directly reusable
for algorithmic convergence proofs.
\<close>


subsection \<open>Residual notation\<close>

definition projected_gradient_residual ::
  "'a::{real_inner,heine_borel} set \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> real"
where
  "projected_gradient_residual C alpha G x =
    norm (projected_gradient_mapping C alpha G x)"

definition projected_gradient_residual_sq ::
  "'a::{real_inner,heine_borel} set \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> real"
where
  "projected_gradient_residual_sq C alpha G x =
    norm (projected_gradient_mapping C alpha G x) ^ 2"

lemma projected_gradient_residual_nonneg:
  "0 \<le> projected_gradient_residual C alpha G x"
  unfolding projected_gradient_residual_def by simp

lemma projected_gradient_residual_sq_nonneg:
  "0 \<le> projected_gradient_residual_sq C alpha G x"
  unfolding projected_gradient_residual_sq_def by simp

lemma projected_gradient_residual_sq_eq_residual_power2:
  "projected_gradient_residual_sq C alpha G x =
    projected_gradient_residual C alpha G x ^ 2"
  unfolding projected_gradient_residual_def projected_gradient_residual_sq_def
  by simp

lemma projected_gradient_residual_eq_mapping_norm:
  "projected_gradient_residual C alpha G x =
    norm (projected_gradient_mapping C alpha G x)"
  unfolding projected_gradient_residual_def
  by simp

lemma projected_gradient_residual_sq_eq_mapping_norm_sq:
  "projected_gradient_residual_sq C alpha G x =
    norm (projected_gradient_mapping C alpha G x) ^ 2"
  unfolding projected_gradient_residual_sq_def
  by simp

lemma projected_gradient_residual_le_of_sq_le:
  assumes sq_bound: "projected_gradient_residual_sq C alpha G x \<le> eps ^ 2"
    and eps_nonneg: "0 \<le> eps"
  shows "projected_gradient_residual C alpha G x \<le> eps"
proof -
  have "projected_gradient_residual C alpha G x ^ 2 \<le> eps ^ 2"
    using sq_bound
    unfolding projected_gradient_residual_sq_eq_residual_power2 .
  then have "\<bar>projected_gradient_residual C alpha G x\<bar> \<le> eps"
    using eps_nonneg
    by (simp add: power2_le_iff_abs_le)
  then show ?thesis
    using projected_gradient_residual_nonneg[
      where C = C and alpha = alpha and G = G and x = x]
    by simp
qed

lemma projected_gradient_residual_sq_le_of_residual_le:
  assumes res_bound: "projected_gradient_residual C alpha G x \<le> eps"
    and eps_nonneg: "0 \<le> eps"
  shows "projected_gradient_residual_sq C alpha G x \<le> eps ^ 2"
proof -
  have nonneg: "0 \<le> projected_gradient_residual C alpha G x"
    by (rule projected_gradient_residual_nonneg)

  have "projected_gradient_residual C alpha G x ^ 2 \<le> eps ^ 2"
    using res_bound nonneg eps_nonneg
    by (simp add: power_mono)
  then show ?thesis
    unfolding projected_gradient_residual_sq_eq_residual_power2 .
qed


subsection \<open>Finite-horizon squared-residual certificates\<close>

lemma projected_gradient_descent_exists_small_residual_sq_feasible:
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
      projected_gradient_residual_sq C alpha G (x n)
      \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
proof -
  obtain n where n_lt: "n < N"
    and n_bound:
      "norm (projected_gradient_mapping C alpha G (x n)) ^ 2
        \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
    using projected_gradient_descent_exists_small_mapping_norm_sq_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size N_pos]
    by auto

  have
    "projected_gradient_residual_sq C alpha G (x n)
      \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
    using n_bound
    unfolding projected_gradient_residual_sq_def
    by simp

  then show ?thesis
    using n_lt by auto
qed

lemma projected_gradient_descent_exists_small_residual_sq:
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
      projected_gradient_residual_sq C alpha G (x n)
      \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_exists_small_residual_sq_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size N_pos])
qed

lemma projected_gradient_descent_exists_small_residual_sq_below_feasible:
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
      projected_gradient_residual_sq C alpha G (x n)
      \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
proof -
  obtain n where n_lt: "n < N"
    and n_bound:
      "norm (projected_gradient_mapping C alpha G (x n)) ^ 2
        \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
    using projected_gradient_descent_exists_small_mapping_norm_sq_below_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size lower N_pos]
    by auto

  have
    "projected_gradient_residual_sq C alpha G (x n)
      \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
    using n_bound
    unfolding projected_gradient_residual_sq_def
    by simp

  then show ?thesis
    using n_lt by auto
qed

lemma projected_gradient_descent_exists_small_residual_sq_below:
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
      projected_gradient_residual_sq C alpha G (x n)
      \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_exists_small_residual_sq_below_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size lower N_pos])
qed


subsection \<open>Finite-horizon residual certificates\<close>

lemma projected_gradient_descent_exists_epsilon_residual_feasible:
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
    and eps_nonneg: "0 \<le> eps"
    and horizon:
      "(2 / (alpha * real N)) * (f (x 0) - f (x N)) \<le> eps ^ 2"
  shows
    "\<exists>n<N. projected_gradient_residual C alpha G (x n) \<le> eps"
proof -
  obtain n where n_lt: "n < N"
    and sq_bound:
      "projected_gradient_residual_sq C alpha G (x n)
        \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
    using projected_gradient_descent_exists_small_residual_sq_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size N_pos]
    by auto

  have sq_eps:
    "projected_gradient_residual_sq C alpha G (x n) \<le> eps ^ 2"
    using sq_bound horizon by linarith

  have res_eps:
    "projected_gradient_residual C alpha G (x n) \<le> eps"
    by (rule projected_gradient_residual_le_of_sq_le[
      OF sq_eps eps_nonneg])

  show ?thesis
    using n_lt res_eps by auto
qed

lemma projected_gradient_descent_exists_epsilon_residual:
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
    and eps_nonneg: "0 \<le> eps"
    and horizon:
      "(2 / (alpha * real N)) * (f (x 0) - f (x N)) \<le> eps ^ 2"
  shows
    "\<exists>n<N. projected_gradient_residual C alpha G (x n) \<le> eps"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_exists_epsilon_residual_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size N_pos
         eps_nonneg horizon])
qed

lemma projected_gradient_descent_exists_epsilon_residual_below_feasible:
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
    and eps_nonneg: "0 \<le> eps"
    and horizon:
      "(2 / (alpha * real N)) * (f (x 0) - B) \<le> eps ^ 2"
  shows
    "\<exists>n<N. projected_gradient_residual C alpha G (x n) \<le> eps"
proof -
  obtain n where n_lt: "n < N"
    and sq_bound:
      "projected_gradient_residual_sq C alpha G (x n)
        \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
    using projected_gradient_descent_exists_small_residual_sq_below_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size lower N_pos]
    by auto

  have sq_eps:
    "projected_gradient_residual_sq C alpha G (x n) \<le> eps ^ 2"
    using sq_bound horizon by linarith

  have res_eps:
    "projected_gradient_residual C alpha G (x n) \<le> eps"
    by (rule projected_gradient_residual_le_of_sq_le[
      OF sq_eps eps_nonneg])

  show ?thesis
    using n_lt res_eps by auto
qed

lemma projected_gradient_descent_exists_epsilon_residual_below:
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
    and eps_nonneg: "0 \<le> eps"
    and horizon:
      "(2 / (alpha * real N)) * (f (x 0) - B) \<le> eps ^ 2"
  shows
    "\<exists>n<N. projected_gradient_residual C alpha G (x n) \<le> eps"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_exists_epsilon_residual_below_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size lower N_pos
         eps_nonneg horizon])
qed


subsection \<open>Minimizer-based residual certificates\<close>

lemma projected_gradient_descent_exists_small_residual_sq_to_minimizer_feasible:
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
      projected_gradient_residual_sq C alpha G (x n)
      \<le> (2 / (alpha * real N)) * (f (x 0) - f xstar)"
proof -
  obtain n where n_lt: "n < N"
    and n_bound:
      "norm (projected_gradient_mapping C alpha G (x n)) ^ 2
        \<le> (2 / (alpha * real N)) * (f (x 0) - f xstar)"
    using projected_gradient_descent_exists_small_mapping_norm_sq_to_minimizer_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size minimizer N_pos]
    by auto

  have
    "projected_gradient_residual_sq C alpha G (x n)
      \<le> (2 / (alpha * real N)) * (f (x 0) - f xstar)"
    using n_bound
    unfolding projected_gradient_residual_sq_def
    by simp

  then show ?thesis
    using n_lt by auto
qed

lemma projected_gradient_descent_exists_small_residual_sq_to_minimizer:
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
      projected_gradient_residual_sq C alpha G (x n)
      \<le> (2 / (alpha * real N)) * (f (x 0) - f xstar)"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_exists_small_residual_sq_to_minimizer_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size minimizer N_pos])
qed

lemma projected_gradient_descent_exists_epsilon_residual_to_minimizer_feasible:
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
    and eps_nonneg: "0 \<le> eps"
    and horizon:
      "(2 / (alpha * real N)) * (f (x 0) - f xstar) \<le> eps ^ 2"
  shows
    "\<exists>n<N. projected_gradient_residual C alpha G (x n) \<le> eps"
proof -
  obtain n where n_lt: "n < N"
    and sq_bound:
      "projected_gradient_residual_sq C alpha G (x n)
        \<le> (2 / (alpha * real N)) * (f (x 0) - f xstar)"
    using projected_gradient_descent_exists_small_residual_sq_to_minimizer_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size minimizer N_pos]
    by auto

  have sq_eps:
    "projected_gradient_residual_sq C alpha G (x n) \<le> eps ^ 2"
    using sq_bound horizon by linarith

  have res_eps:
    "projected_gradient_residual C alpha G (x n) \<le> eps"
    by (rule projected_gradient_residual_le_of_sq_le[
      OF sq_eps eps_nonneg])

  show ?thesis
    using n_lt res_eps by auto
qed

lemma projected_gradient_descent_exists_epsilon_residual_to_minimizer:
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
    and eps_nonneg: "0 \<le> eps"
    and horizon:
      "(2 / (alpha * real N)) * (f (x 0) - f xstar) \<le> eps ^ 2"
  shows
    "\<exists>n<N. projected_gradient_residual C alpha G (x n) \<le> eps"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_exists_epsilon_residual_to_minimizer_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size minimizer N_pos
         eps_nonneg horizon])
qed


subsection \<open>Product-form epsilon-stationarity complexity\<close>

text \<open>
The following variants are the main finite-horizon epsilon-stationarity
certificates of the theory.

They use a product-form horizon assumption,
which is often the most readable form in optimization statements.  Instead
of requiring a bound on a quotient, the assumption states directly that the
horizon is large enough relative to the initial objective gap and eps squared.
\<close>

lemma projected_gradient_descent_exists_epsilon_residual_to_minimizer_product_feasible:
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
    and eps_pos: "0 < eps"
    and horizon:
      "2 * (f (x 0) - f xstar) \<le> alpha * real N * eps ^ 2"
  shows
    "\<exists>n<N. projected_gradient_residual C alpha G (x n) \<le> eps"
proof -
  let ?A = "alpha * real N"
  let ?gap = "f (x 0) - f xstar"

  have A_pos: "0 < ?A"
    using alpha_pos N_pos by simp

  have divided:
    "(2 / ?A) * ?gap \<le> eps ^ 2"
  proof -
    have rewrite:
      "(2 / ?A) * ?gap = (2 * ?gap) / ?A"
      by (simp add: divide_inverse algebra_simps)

    have "(2 * ?gap) / ?A \<le> eps ^ 2"
      using horizon A_pos
      by (simp add: pos_divide_le_eq algebra_simps)

    then show ?thesis
      using rewrite by simp
  qed

  have eps_nonneg: "0 \<le> eps"
    using eps_pos by simp

  show ?thesis
    by (rule projected_gradient_descent_exists_epsilon_residual_to_minimizer_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size minimizer N_pos
         eps_nonneg divided])
qed

lemma projected_gradient_descent_exists_epsilon_residual_to_minimizer_product:
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
    and eps_pos: "0 < eps"
    and horizon:
      "2 * (f (x 0) - f xstar) \<le> alpha * real N * eps ^ 2"
  shows
    "\<exists>n<N. projected_gradient_residual C alpha G (x n) \<le> eps"
proof -
  have feasible: "feasible_iterates C x"
    by (rule projected_gradient_descent_feasible_from_initial[
      OF pgd closed x0_mem])

  show ?thesis
    by (rule projected_gradient_descent_exists_epsilon_residual_to_minimizer_product_feasible[
      OF smooth closed convex pgd feasible alpha_pos step_size minimizer N_pos
         eps_pos horizon])
qed


subsection \<open>Residual-zero consequences\<close>

text \<open>
A zero residual is exactly the projected-gradient fixed-point condition, and
therefore gives the usual constrained first-order optimality certificate.
These lemmas simply rephrase the existing projected-gradient mapping
certificates using the residual notation introduced above.
\<close>

lemma projected_gradient_residual_zero_iff_mapping_zero:
  "projected_gradient_residual C alpha G x = 0
    \<longleftrightarrow> projected_gradient_mapping C alpha G x = 0"
  unfolding projected_gradient_residual_def by simp

lemma projected_gradient_residual_zero_iff_fixed_point:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes alpha_nonzero: "alpha \<noteq> 0"
  shows
    "projected_gradient_residual C alpha G x = 0
      \<longleftrightarrow> projected_gradient_step C alpha G x = x"
  using projected_gradient_mapping_zero_iff_fixed_point[
    where C = C and alpha = alpha and G = G and x = x,
    OF alpha_nonzero]
  unfolding projected_gradient_residual_zero_iff_mapping_zero
  by simp

lemma projected_gradient_residual_zero_iff_first_order_condition:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes convex: "convex C"
    and closed: "closed C"
    and x_mem: "x \<in> C"
    and alpha_pos: "0 < alpha"
  shows
    "projected_gradient_residual C alpha G x = 0
      \<longleftrightarrow> first_order_condition_at C (G x) x"
  using projected_gradient_mapping_zero_iff_first_order_condition[
    where C = C and alpha = alpha and G = G and x = x,
    OF convex closed x_mem alpha_pos]
  unfolding projected_gradient_residual_zero_iff_mapping_zero
  by simp

lemma projected_gradient_residual_zero_imp_global_min_on:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and x_mem: "x \<in> C"
    and alpha_pos: "0 < alpha"
    and zero: "projected_gradient_residual C alpha G x = 0"
  shows "global_min_on C f x"
proof -
  have mapping_zero: "projected_gradient_mapping C alpha G x = 0"
    using zero
    unfolding projected_gradient_residual_zero_iff_mapping_zero .
  show ?thesis
    by (rule projected_gradient_mapping_zero_imp_global_min_on[
      OF smooth closed convex x_mem alpha_pos mapping_zero])
qed

subsection \<open>Recommended public residual-complexity interface\<close>

text \<open>
The following aliases give short, stable names to the main user-facing
results of this theory.  They are intended for use in the AFP document,
README, and downstream developments.

The long theorem names above preserve the exact assumptions used in the
proofs.  The aliases below identify the main residual-complexity and
optimality certificates exposed by this theory.
\<close>

lemmas projected_gradient_descent_residual_sq_complexity =
  projected_gradient_descent_exists_small_residual_sq_to_minimizer

lemmas projected_gradient_descent_feasible_residual_sq_complexity =
  projected_gradient_descent_exists_small_residual_sq_to_minimizer_feasible

lemmas projected_gradient_descent_epsilon_stationarity_complexity =
  projected_gradient_descent_exists_epsilon_residual_to_minimizer_product

lemmas projected_gradient_descent_feasible_epsilon_stationarity_complexity =
  projected_gradient_descent_exists_epsilon_residual_to_minimizer_product_feasible

lemmas projected_gradient_residual_fixed_point_certificate =
  projected_gradient_residual_zero_iff_fixed_point

lemmas projected_gradient_residual_optimality_certificate =
  projected_gradient_residual_zero_iff_first_order_condition

lemmas projected_gradient_residual_global_min_certificate =
  projected_gradient_residual_zero_imp_global_min_on

lemmas projected_gradient_residual_public_interface =
  projected_gradient_residual_eq_mapping_norm
  projected_gradient_residual_sq_eq_mapping_norm_sq
  projected_gradient_residual_sq_eq_residual_power2
  projected_gradient_residual_le_of_sq_le
  projected_gradient_residual_sq_le_of_residual_le
  projected_gradient_descent_residual_sq_complexity
  projected_gradient_descent_epsilon_stationarity_complexity
  projected_gradient_residual_fixed_point_certificate
  projected_gradient_residual_optimality_certificate
  projected_gradient_residual_global_min_certificate


subsection \<open>Locale form\<close>

context projected_gradient_descent
begin

lemma exists_small_residual_sq:
  assumes alpha_pos: "0 < alpha"
    and N_pos: "N > 0"
  shows
    "\<exists>n<N.
      projected_gradient_residual_sq C alpha G (x n)
      \<le> (2 / (alpha * real N)) * (f (x 0) - f (x N))"
  by (rule projected_gradient_descent_exists_small_residual_sq_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size N_pos])

lemma exists_small_residual_sq_below:
  assumes alpha_pos: "0 < alpha"
    and lower: "B \<le> f (x N)"
    and N_pos: "N > 0"
  shows
    "\<exists>n<N.
      projected_gradient_residual_sq C alpha G (x n)
      \<le> (2 / (alpha * real N)) * (f (x 0) - B)"
  by (rule projected_gradient_descent_exists_small_residual_sq_below_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size lower N_pos])

lemma exists_epsilon_residual:
  assumes alpha_pos: "0 < alpha"
    and N_pos: "N > 0"
    and eps_nonneg: "0 \<le> eps"
    and horizon:
      "(2 / (alpha * real N)) * (f (x 0) - f (x N)) \<le> eps ^ 2"
  shows
    "\<exists>n<N. projected_gradient_residual C alpha G (x n) \<le> eps"
  by (rule projected_gradient_descent_exists_epsilon_residual_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size N_pos
       eps_nonneg horizon])

lemma exists_epsilon_residual_below:
  assumes alpha_pos: "0 < alpha"
    and lower: "B \<le> f (x N)"
    and N_pos: "N > 0"
    and eps_nonneg: "0 \<le> eps"
    and horizon:
      "(2 / (alpha * real N)) * (f (x 0) - B) \<le> eps ^ 2"
  shows
    "\<exists>n<N. projected_gradient_residual C alpha G (x n) \<le> eps"
  by (rule projected_gradient_descent_exists_epsilon_residual_below_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size lower N_pos
       eps_nonneg horizon])

lemma exists_small_residual_sq_to_minimizer:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on C f xstar"
    and N_pos: "N > 0"
  shows
    "\<exists>n<N.
      projected_gradient_residual_sq C alpha G (x n)
      \<le> (2 / (alpha * real N)) * (f (x 0) - f xstar)"
  by (rule projected_gradient_descent_exists_small_residual_sq_to_minimizer_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size minimizer N_pos])

lemma exists_epsilon_residual_to_minimizer:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on C f xstar"
    and N_pos: "N > 0"
    and eps_nonneg: "0 \<le> eps"
    and horizon:
      "(2 / (alpha * real N)) * (f (x 0) - f xstar) \<le> eps ^ 2"
  shows
    "\<exists>n<N. projected_gradient_residual C alpha G (x n) \<le> eps"
  by (rule projected_gradient_descent_exists_epsilon_residual_to_minimizer_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size minimizer N_pos
       eps_nonneg horizon])

lemma exists_epsilon_residual_to_minimizer_product:
  assumes alpha_pos: "0 < alpha"
    and minimizer: "global_min_on C f xstar"
    and N_pos: "N > 0"
    and eps_pos: "0 < eps"
    and horizon:
      "2 * (f (x 0) - f xstar) \<le> alpha * real N * eps ^ 2"
  shows
    "\<exists>n<N. projected_gradient_residual C alpha G (x n) \<le> eps"
  by (rule projected_gradient_descent_exists_epsilon_residual_to_minimizer_product_feasible[
    OF smooth closed convex iterates feasible alpha_pos step_size minimizer N_pos
       eps_pos horizon])

end


text \<open>
The main public theorem in this file is
@{text \<open>projected_gradient_descent_epsilon_stationarity_complexity\<close>}.

It is an alias for
@{text \<open>projected_gradient_descent_exists_epsilon_residual_to_minimizer_product\<close>}.
It states that, if the horizon N is large enough in the usual product-form
complexity bound, then one of the first N projected-gradient iterates has
projected-gradient residual at most eps.

The theorem group @{text \<open>projected_gradient_residual_public_interface\<close>} collects the
main residual notation, residual-complexity, and residual-optimality facts
provided by this theory.
\<close>

end