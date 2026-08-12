theory Projection_Optimization
  imports
    Gradient_Descent_Convergence
    Projection_Geometry
begin

section \<open>Projection and projected gradient steps\<close>

text \<open>
This theory introduces the projection layer needed for projected gradient
descent.  The main results are the one-step distance inequality for a projected
gradient step on a closed convex feasible set, and the associated one-step
objective decrease in terms of the projected step length.

The projected-gradient mapping itself is introduced later, to avoid making this
basic projection layer depend on the residual interface.
\<close>


subsection \<open>Projected gradient step\<close>

definition projected_gradient_step ::
  "'a::{real_inner,heine_borel} set \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "projected_gradient_step C alpha G x =
    closest_point C (gradient_step alpha G x)"

lemma projected_gradient_step_in_set:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes closed: "closed C"
    and nonempty: "C \<noteq> {}"
  shows "projected_gradient_step C alpha G x \<in> C"
  unfolding projected_gradient_step_def
  by (rule closest_point_in_set[OF closed nonempty])

lemma projected_gradient_step_in_set_if_base_mem:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes closed: "closed C"
    and x_mem: "x \<in> C"
  shows "projected_gradient_step C alpha G y \<in> C"
proof -
  have nonempty: "C \<noteq> {}"
    using x_mem by auto
  show ?thesis
    by (rule projected_gradient_step_in_set[OF closed nonempty])
qed

lemma projected_gradient_step_variational_inequality:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes convex: "convex C"
    and closed: "closed C"
    and u_mem: "u \<in> C"
  shows "inner
    (gradient_step alpha G x - projected_gradient_step C alpha G x)
    (u - projected_gradient_step C alpha G x) \<le> 0"
  unfolding projected_gradient_step_def
  by (rule projection_variational_inequality[OF convex closed u_mem])

lemma projected_gradient_inner_bound:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes convex: "convex C"
    and closed: "closed C"
    and u_mem: "u \<in> C"
    and alpha_pos: "0 < alpha"
  shows
    "inner (G x) (projected_gradient_step C alpha G x - u)
      \<le>
     (norm (x - u) ^ 2
      - norm (projected_gradient_step C alpha G x - u) ^ 2
      - norm (projected_gradient_step C alpha G x - x) ^ 2)
      / (2 * alpha)"
proof -
  let ?p = "projected_gradient_step C alpha G x"

  have vi:
    "inner (gradient_step alpha G x - ?p) (u - ?p) \<le> 0"
    by (rule projected_gradient_step_variational_inequality[OF convex closed u_mem])

  have vi_unfolded:
    "inner (x - scaleR alpha (G x) - ?p) (u - ?p) \<le> 0"
    using vi
    unfolding gradient_step_def
    by (simp add: algebra_simps)

  show ?thesis
    by (rule projected_gradient_inner_bound_from_vi[OF alpha_pos vi_unfolded])
qed


subsection \<open>Projected gradient one-step bound\<close>

lemma projected_gradient_one_step_distance_bound_to_point:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and x_mem: "x \<in> C"
    and u_mem: "u \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
  defines "p \<equiv> projected_gradient_step C alpha G x"
  shows
    "f p - f u
      \<le>
     (norm (x - u) ^ 2 - norm (p - u) ^ 2) / (2 * alpha)"
proof -
  have p_mem: "p \<in> C"
    unfolding p_def
    by (rule projected_gradient_step_in_set_if_base_mem[OF closed x_mem])

  have smooth_bound: "smooth_upper_bound_on L C f G"
    using smooth by (rule smooth_convex_onD_smooth_upper_bound)

  have cd: "convex_differentiable_on C f G"
    using smooth by (rule smooth_convex_onD_convex_differentiable)

  have lower_bound: "gradient_lower_bound_on C f G"
    using cd by (rule convex_differentiable_on_imp_gradient_lower_bound_on)

  have smooth_est:
    "f p \<le> f x + inner (G x) (p - x) + (L / 2) * norm (p - x) ^ 2"
    using smooth_upper_bound_onD[OF smooth_bound x_mem p_mem] .

  have support:
    "f x + inner (G x) (u - x) \<le> f u"
    using gradient_lower_bound_onD[OF lower_bound x_mem u_mem] .

  have gap_at_x:
    "f x - f u \<le> inner (G x) (x - u)"
  proof -
    have "- inner (G x) (u - x) = inner (G x) (x - u)"
      by (simp add: inner_diff_right)
    thus ?thesis
      using support by linarith
  qed

  have combine:
    "f p - f u
      \<le> inner (G x) (p - u) + (L / 2) * norm (p - x) ^ 2"
  proof -
    have "f p - f u
        \<le> inner (G x) (p - x) + inner (G x) (x - u)
          + (L / 2) * norm (p - x) ^ 2"
      using smooth_est gap_at_x by linarith
    also have
      "inner (G x) (p - x) + inner (G x) (x - u)
        = inner (G x) (p - u)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed

  have inner_bound:
    "inner (G x) (p - u)
      \<le>
     (norm (x - u) ^ 2 - norm (p - u) ^ 2 - norm (p - x) ^ 2)
      / (2 * alpha)"
    unfolding p_def
    by (rule projected_gradient_inner_bound[OF convex closed u_mem alpha_pos])

  let ?A = "norm (x - u) ^ 2"
  let ?B = "norm (p - u) ^ 2"
  let ?R = "norm (p - x) ^ 2"

  have before_absorb:
    "f p - f u \<le> (?A - ?B - ?R) / (2 * alpha) + (L / 2) * ?R"
    using combine inner_bound by linarith

  have decomp:
    "(?A - ?B - ?R) / (2 * alpha) + (L / 2) * ?R
      =
     (?A - ?B) / (2 * alpha)
      + (L / 2 - 1 / (2 * alpha)) * ?R"
    using alpha_pos
    by (simp add: field_simps)

  have L_bound: "L \<le> 1 / alpha"
    using step_size alpha_pos
    by (simp add: field_simps)

  have coeff_nonpos:
    "L / 2 - 1 / (2 * alpha) \<le> 0"
    using L_bound alpha_pos
    by (simp add: field_simps)

  have extra_nonpos:
    "(L / 2 - 1 / (2 * alpha)) * ?R \<le> 0"
    by (rule mult_nonpos_nonneg[OF coeff_nonpos]) simp

  have "(?A - ?B - ?R) / (2 * alpha) + (L / 2) * ?R
      \<le> (?A - ?B) / (2 * alpha)"
    using decomp extra_nonpos by linarith

  thus ?thesis
    using before_absorb by linarith
qed

subsection \<open>Projected gradient step descent\<close>

text \<open>
Taking the comparison point u to be the current iterate x in the one-step
distance inequality gives a descent estimate in terms of the projected step
length.  Later theories translate this step-length residual into the
projected-gradient mapping norm.
\<close>

lemma projected_gradient_step_progress_step_norm:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and x_mem: "x \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
  shows
    "(1 / (2 * alpha)) *
      norm (projected_gradient_step C alpha G x - x) ^ 2
      \<le> f x - f (projected_gradient_step C alpha G x)"
proof -
  let ?p = "projected_gradient_step C alpha G x"

  have step:
    "f ?p - f x
      \<le> (norm (x - x) ^ 2 - norm (?p - x) ^ 2) / (2 * alpha)"
    by (rule projected_gradient_one_step_distance_bound_to_point[
      OF smooth closed convex x_mem x_mem alpha_pos step_size])

  have step':
    "f ?p - f x \<le> - (norm (?p - x) ^ 2 / (2 * alpha))"
  proof -
    have
      "(norm (x - x) ^ 2 - norm (?p - x) ^ 2) / (2 * alpha)
        = - (norm (?p - x) ^ 2 / (2 * alpha))"
      by simp
    then show ?thesis
      using step by simp
  qed

  have A_le:
    "norm (?p - x) ^ 2 / (2 * alpha) \<le> f x - f ?p"
    using step' by linarith

  have coeff_rewrite:
    "(1 / (2 * alpha)) * norm (?p - x) ^ 2 =
      norm (?p - x) ^ 2 / (2 * alpha)"
    by simp

  show ?thesis
    using A_le coeff_rewrite by simp
qed

lemma projected_gradient_step_descent_step_norm:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and x_mem: "x \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
  shows
    "f (projected_gradient_step C alpha G x)
      \<le> f x -
        (1 / (2 * alpha)) *
          norm (projected_gradient_step C alpha G x - x) ^ 2"
proof -
  have progress:
    "(1 / (2 * alpha)) *
      norm (projected_gradient_step C alpha G x - x) ^ 2
      \<le> f x - f (projected_gradient_step C alpha G x)"
    by (rule projected_gradient_step_progress_step_norm[
      OF smooth closed convex x_mem alpha_pos step_size])

  show ?thesis
    using progress by linarith
qed

lemma projected_gradient_step_descent_step_norm_add:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and x_mem: "x \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
  shows
    "f (projected_gradient_step C alpha G x)
      + (1 / (2 * alpha)) *
          norm (projected_gradient_step C alpha G x - x) ^ 2
      \<le> f x"
proof -
  have progress:
    "(1 / (2 * alpha)) *
      norm (projected_gradient_step C alpha G x - x) ^ 2
      \<le> f x - f (projected_gradient_step C alpha G x)"
    by (rule projected_gradient_step_progress_step_norm[
      OF smooth closed convex x_mem alpha_pos step_size])

  show ?thesis
    using progress by linarith
qed

lemma projected_gradient_one_step_distance_bound_to_minimizer:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and x_mem: "x \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on C f xstar"
  defines "p \<equiv> projected_gradient_step C alpha G x"
  shows
    "f p - f xstar
      \<le>
     (norm (x - xstar) ^ 2 - norm (p - xstar) ^ 2) / (2 * alpha)"
proof -
  have xstar_mem: "xstar \<in> C"
    using minimizer by (rule global_min_onD_mem)

  show ?thesis
    unfolding p_def
    by (rule projected_gradient_one_step_distance_bound_to_point[
        OF smooth closed convex x_mem xstar_mem alpha_pos step_size])
qed


subsection \<open>Projected gradient descent iterates\<close>

definition projected_gradient_descent_iterates ::
  "'a::{real_inner,heine_borel} set \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "projected_gradient_descent_iterates C alpha G x \<longleftrightarrow>
    (\<forall>n. x (Suc n) = projected_gradient_step C alpha G (x n))"

lemma projected_gradient_descent_iteratesI:
  assumes "\<And>n. x (Suc n) = projected_gradient_step C alpha G (x n)"
  shows "projected_gradient_descent_iterates C alpha G x"
  using assms unfolding projected_gradient_descent_iterates_def by auto

lemma projected_gradient_descent_iteratesD:
  assumes "projected_gradient_descent_iterates C alpha G x"
  shows "x (Suc n) = projected_gradient_step C alpha G (x n)"
  using assms unfolding projected_gradient_descent_iterates_def by auto

lemma projected_gradient_descent_iteratesE:
  assumes "projected_gradient_descent_iterates C alpha G x"
  obtains "x (Suc n) = projected_gradient_step C alpha G (x n)"
  using projected_gradient_descent_iteratesD[OF assms, of n] by auto

lemma projected_gradient_descent_next_mem:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes pgd: "projected_gradient_descent_iterates C alpha G x"
    and closed: "closed C"
    and nonempty: "C \<noteq> {}"
  shows "x (Suc n) \<in> C"
proof -
  have step_eq:
    "x (Suc n) = projected_gradient_step C alpha G (x n)"
    using pgd by (rule projected_gradient_descent_iteratesD)
  have step_mem:
    "projected_gradient_step C alpha G (x n) \<in> C"
    by (rule projected_gradient_step_in_set[OF closed nonempty])
  show ?thesis
    using step_eq step_mem by simp
qed

lemma projected_gradient_descent_feasible_from_initial:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes pgd: "projected_gradient_descent_iterates C alpha G x"
    and closed: "closed C"
    and x0_mem: "x 0 \<in> C"
  shows "feasible_iterates C x"
proof (rule feasible_iteratesI)
  fix n
  show "x n \<in> C"
  proof (induction n)
    case 0
    show ?case
      using x0_mem .
  next
    case (Suc n)
    have nonempty: "C \<noteq> {}"
      using x0_mem by auto
    show ?case
      by (rule projected_gradient_descent_next_mem[OF pgd closed nonempty])
  qed
qed

lemma projected_gradient_descent_one_step_distance_bound_to_point:
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
    "f (x (Suc n)) - f u
      \<le>
     (norm (x n - u) ^ 2 - norm (x (Suc n) - u) ^ 2) / (2 * alpha)"
proof -
  have xn_mem: "x n \<in> C"
    using feasible by (rule feasible_iteratesD)

  have step_eq:
    "x (Suc n) = projected_gradient_step C alpha G (x n)"
    using pgd by (rule projected_gradient_descent_iteratesD)

  show ?thesis
    unfolding step_eq
    by (rule projected_gradient_one_step_distance_bound_to_point[
        OF smooth closed convex xn_mem u_mem alpha_pos step_size])
qed

lemma projected_gradient_descent_step_progress_step_norm:
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
    "(1 / (2 * alpha)) * norm (x (Suc n) - x n) ^ 2
      \<le> f (x n) - f (x (Suc n))"
proof -
  have xn_mem: "x n \<in> C"
    using feasible by (rule feasible_iteratesD)

  have step_eq:
    "x (Suc n) = projected_gradient_step C alpha G (x n)"
    using pgd by (rule projected_gradient_descent_iteratesD)

  have progress:
    "(1 / (2 * alpha)) *
      norm (projected_gradient_step C alpha G (x n) - x n) ^ 2
      \<le> f (x n) - f (projected_gradient_step C alpha G (x n))"
    by (rule projected_gradient_step_progress_step_norm[
      OF smooth closed convex xn_mem alpha_pos step_size])

  show ?thesis
    using progress step_eq by simp
qed

lemma projected_gradient_descent_step_descent_step_norm:
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
    "f (x (Suc n))
      \<le> f (x n) - (1 / (2 * alpha)) * norm (x (Suc n) - x n) ^ 2"
proof -
  have progress:
    "(1 / (2 * alpha)) * norm (x (Suc n) - x n) ^ 2
      \<le> f (x n) - f (x (Suc n))"
    by (rule projected_gradient_descent_step_progress_step_norm[
      OF smooth closed convex pgd feasible alpha_pos step_size])

  show ?thesis
    using progress by linarith
qed

lemma projected_gradient_descent_step_descent_step_norm_add:
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
    "f (x (Suc n)) + (1 / (2 * alpha)) * norm (x (Suc n) - x n) ^ 2
      \<le> f (x n)"
proof -
  have progress:
    "(1 / (2 * alpha)) * norm (x (Suc n) - x n) ^ 2
      \<le> f (x n) - f (x (Suc n))"
    by (rule projected_gradient_descent_step_progress_step_norm[
      OF smooth closed convex pgd feasible alpha_pos step_size])

  show ?thesis
    using progress by linarith
qed

lemma projected_gradient_descent_one_step_distance_bound_to_minimizer:
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
    "f (x (Suc n)) - f xstar
      \<le>
     (norm (x n - xstar) ^ 2 - norm (x (Suc n) - xstar) ^ 2) / (2 * alpha)"
proof -
  have xstar_mem: "xstar \<in> C"
    using minimizer by (rule global_min_onD_mem)

  show ?thesis
    by (rule projected_gradient_descent_one_step_distance_bound_to_point[
        OF smooth closed convex pgd feasible xstar_mem alpha_pos step_size])
qed


text \<open>
The main one-step estimate of this file is
@{thm projected_gradient_one_step_distance_bound_to_point}.
It is the projected analogue of the distance-potential inequality used for
the unconstrained gradient-descent convergence proof.

The descent estimate
@{thm projected_gradient_step_progress_step_norm} is obtained by taking the
comparison point to be the current iterate.  It controls the objective decrease
by the projected step length and is the step-level input for projected-gradient
mapping residual-rate estimates.
\<close>

end