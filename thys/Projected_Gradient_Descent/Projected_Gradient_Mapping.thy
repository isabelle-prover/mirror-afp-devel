theory Projected_Gradient_Mapping
  imports Projected_Gradient_Descent_Convergence
begin

section \<open>Projected-gradient mappings and optimality certificates\<close>

text \<open>
This theory introduces the projected-gradient mapping associated with the
projected-gradient step.

For a closed convex feasible set C and a stepsize alpha > 0, the projected
gradient mapping is

  (1 / alpha) * (x - @{text \<open>P_C\<close>} (x - alpha * G x)).

It measures the normalized residual of the projected-gradient fixed-point
equation.  Equivalently, its norm is the length of one projected-gradient step,
divided by alpha.  Thus the projected-gradient mapping is the constrained
analogue of the gradient residual in unconstrained gradient descent.

The main purpose of this file is to connect four equivalent or closely related
languages:

  • the projected-gradient step residual;
  • zero projected-gradient mapping;
  • fixed points of the projected-gradient step;
  • first-order variational inequalities.

For convex differentiable objectives, the zero-residual condition gives global
optimality.
\<close>


subsection \<open>Projected-gradient mappings\<close>

definition projected_gradient_mapping ::
  "'a::{real_inner,heine_borel} set \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "projected_gradient_mapping C alpha G x =
     (1 / alpha) *\<^sub>R (x - projected_gradient_step C alpha G x)"

lemma projected_gradient_mapping_step_relation:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes alpha_nonzero: "alpha \<noteq> 0"
  shows
    "alpha *\<^sub>R projected_gradient_mapping C alpha G x =
      x - projected_gradient_step C alpha G x"
  using alpha_nonzero
  unfolding projected_gradient_mapping_def
  by simp

lemma projected_gradient_step_eq_sub_mapping:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes alpha_nonzero: "alpha \<noteq> 0"
  shows
    "projected_gradient_step C alpha G x =
      x - alpha *\<^sub>R projected_gradient_mapping C alpha G x"
proof -
  have
    "alpha *\<^sub>R projected_gradient_mapping C alpha G x =
      x - projected_gradient_step C alpha G x"
    by (rule projected_gradient_mapping_step_relation[OF alpha_nonzero])
  then show ?thesis
    by (simp add: algebra_simps)
qed

subsection \<open>Norm interpretation as a residual\<close>

text \<open>
The projected-gradient mapping is the projected step residual normalized by the
stepsize.  The following elementary identities are useful when translating
descent in step length into descent in projected-gradient mapping norm.
\<close>

lemma projected_gradient_mapping_norm_eq_step_distance_divide:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes alpha_pos: "0 < alpha"
  shows
    "norm (projected_gradient_mapping C alpha G x) =
      norm (x - projected_gradient_step C alpha G x) / alpha"
proof -
  have
    "norm (projected_gradient_mapping C alpha G x) =
      norm ((1 / alpha) *\<^sub>R
        (x - projected_gradient_step C alpha G x))"
    unfolding projected_gradient_mapping_def by simp
  also have "... =
      norm (x - projected_gradient_step C alpha G x) / alpha"
    using alpha_pos by simp
  finally show ?thesis .
qed

lemma projected_gradient_base_step_distance_eq_alpha_mapping_norm:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes alpha_pos: "0 < alpha"
  shows
    "norm (x - projected_gradient_step C alpha G x) =
      alpha * norm (projected_gradient_mapping C alpha G x)"
proof -
  have alpha_nonzero: "alpha \<noteq> 0"
    using alpha_pos by simp

  have relation:
    "alpha *\<^sub>R projected_gradient_mapping C alpha G x =
      x - projected_gradient_step C alpha G x"
    by (rule projected_gradient_mapping_step_relation[OF alpha_nonzero])

  have
    "norm (x - projected_gradient_step C alpha G x) =
      norm (alpha *\<^sub>R projected_gradient_mapping C alpha G x)"
    using relation by simp
  also have "... = alpha * norm (projected_gradient_mapping C alpha G x)"
    using alpha_pos by simp
  finally show ?thesis .
qed

lemma projected_gradient_step_base_distance_eq_alpha_mapping_norm:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes alpha_pos: "0 < alpha"
  shows
    "norm (projected_gradient_step C alpha G x - x) =
      alpha * norm (projected_gradient_mapping C alpha G x)"
proof -
  have
    "norm (projected_gradient_step C alpha G x - x) =
      norm (x - projected_gradient_step C alpha G x)"
    by (simp add: norm_minus_commute)
  also have "... =
      alpha * norm (projected_gradient_mapping C alpha G x)"
    by (rule projected_gradient_base_step_distance_eq_alpha_mapping_norm[
      OF alpha_pos])
  finally show ?thesis .
qed

lemma projected_gradient_step_distance_sq_eq_mapping_norm_sq:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes alpha_pos: "0 < alpha"
  shows
    "norm (projected_gradient_step C alpha G x - x) ^ 2 =
      alpha ^ 2 * norm (projected_gradient_mapping C alpha G x) ^ 2"
proof -
  have norm_eq:
    "norm (projected_gradient_step C alpha G x - x) =
      alpha * norm (projected_gradient_mapping C alpha G x)"
    by (rule projected_gradient_step_base_distance_eq_alpha_mapping_norm[
      OF alpha_pos])

  show ?thesis
    using norm_eq
    by (simp add: power2_eq_square)
qed

lemma projected_gradient_mapping_norm_sq_eq_step_distance_sq:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes alpha_pos: "0 < alpha"
  shows
    "norm (projected_gradient_mapping C alpha G x) ^ 2 =
      norm (projected_gradient_step C alpha G x - x) ^ 2 / alpha ^ 2"
proof -
  have dist:
    "norm (projected_gradient_step C alpha G x - x) ^ 2 =
      alpha ^ 2 * norm (projected_gradient_mapping C alpha G x) ^ 2"
    by (rule projected_gradient_step_distance_sq_eq_mapping_norm_sq[
      OF alpha_pos])

  have alpha_sq_pos: "0 < alpha ^ 2"
    using alpha_pos by simp

  have
    "norm (projected_gradient_step C alpha G x - x) ^ 2 / alpha ^ 2 =
      norm (projected_gradient_mapping C alpha G x) ^ 2"
    using dist alpha_sq_pos by simp

  then show ?thesis
    by simp
qed

lemma projected_gradient_mapping_zero_imp_step_eq:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes alpha_nonzero: "alpha \<noteq> 0"
    and zero: "projected_gradient_mapping C alpha G x = 0"
  shows "projected_gradient_step C alpha G x = x"
proof -
  have
    "alpha *\<^sub>R projected_gradient_mapping C alpha G x =
      x - projected_gradient_step C alpha G x"
    by (rule projected_gradient_mapping_step_relation[OF alpha_nonzero])
  then have "x - projected_gradient_step C alpha G x = 0"
    using zero by simp
  then show ?thesis
    by simp
qed

lemma projected_gradient_step_eq_imp_mapping_zero:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes step: "projected_gradient_step C alpha G x = x"
  shows "projected_gradient_mapping C alpha G x = 0"
  using step
  unfolding projected_gradient_mapping_def
  by simp

lemma projected_gradient_mapping_zero_iff_fixed_point:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes alpha_nonzero: "alpha \<noteq> 0"
  shows
    "projected_gradient_mapping C alpha G x = 0
      \<longleftrightarrow> projected_gradient_step C alpha G x = x"
proof
  assume zero: "projected_gradient_mapping C alpha G x = 0"
  show "projected_gradient_step C alpha G x = x"
    by (rule projected_gradient_mapping_zero_imp_step_eq[
        OF alpha_nonzero zero])
next
  assume step: "projected_gradient_step C alpha G x = x"
  show "projected_gradient_mapping C alpha G x = 0"
    by (rule projected_gradient_step_eq_imp_mapping_zero[OF step])
qed

lemma projected_gradient_mapping_zero_iff_step_distance_zero:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes alpha_nonzero: "alpha \<noteq> 0"
  shows
    "projected_gradient_mapping C alpha G x = 0
      \<longleftrightarrow> norm (projected_gradient_step C alpha G x - x) = 0"
proof
  assume zero: "projected_gradient_mapping C alpha G x = 0"

  have step_eq:
    "projected_gradient_step C alpha G x = x"
    by (rule projected_gradient_mapping_zero_imp_step_eq[
      OF alpha_nonzero zero])

  show "norm (projected_gradient_step C alpha G x - x) = 0"
    using step_eq by simp
next
  assume dist_zero:
    "norm (projected_gradient_step C alpha G x - x) = 0"

  have step_eq:
    "projected_gradient_step C alpha G x = x"
    using dist_zero by simp

  show "projected_gradient_mapping C alpha G x = 0"
    by (rule projected_gradient_step_eq_imp_mapping_zero[OF step_eq])
qed

subsection \<open>Residual form of the projection variational inequality\<close>

lemma gradient_step_minus_projected_gradient_step_eq_mapping_residual:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes alpha_nonzero: "alpha \<noteq> 0"
  shows
    "gradient_step alpha G x - projected_gradient_step C alpha G x =
      alpha *\<^sub>R
        (projected_gradient_mapping C alpha G x - G x)"
  using alpha_nonzero
  unfolding gradient_step_def projected_gradient_mapping_def
  by (simp add: algebra_simps)

lemma projected_gradient_mapping_variational_inequality:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes convex: "convex C"
    and closed: "closed C"
    and u_mem: "u \<in> C"
    and alpha_pos: "0 < alpha"
  shows
    "inner
      (projected_gradient_mapping C alpha G x - G x)
      (u - projected_gradient_step C alpha G x)
      \<le> 0"
proof -
  let ?p = "projected_gradient_step C alpha G x"
  let ?M = "projected_gradient_mapping C alpha G x - G x"

  have alpha_nonzero: "alpha \<noteq> 0"
    using alpha_pos by simp

  have vi:
    "inner (gradient_step alpha G x - ?p) (u - ?p) \<le> 0"
    by (rule projected_gradient_step_variational_inequality[
        OF convex closed u_mem])

  have residual:
    "gradient_step alpha G x - ?p = alpha *\<^sub>R ?M"
    by (rule gradient_step_minus_projected_gradient_step_eq_mapping_residual[
        OF alpha_nonzero])

  have scaled: "alpha * inner ?M (u - ?p) \<le> 0"
    using vi residual by simp

  show ?thesis
  proof (rule ccontr)
    assume not_le: "\<not> inner ?M (u - ?p) \<le> 0"
    then have pos: "0 < inner ?M (u - ?p)"
      by simp
    then have "0 < alpha * inner ?M (u - ?p)"
      using alpha_pos by simp
    then show False
      using scaled by linarith
  qed
qed


subsection \<open>Fixed points and first-order conditions\<close>

lemma projected_gradient_fixed_point_imp_first_order_condition:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes convex: "convex C"
    and closed: "closed C"
    and x_mem: "x \<in> C"
    and alpha_pos: "0 < alpha"
    and fixed: "projected_gradient_step C alpha G x = x"
  shows "first_order_condition_at C (G x) x"
proof (rule first_order_condition_atI)
  show "x \<in> C"
    using x_mem .
next
  fix u
  assume u_mem: "u \<in> C"

  have vi:
    "inner
      (gradient_step alpha G x - projected_gradient_step C alpha G x)
      (u - projected_gradient_step C alpha G x)
      \<le> 0"
    by (rule projected_gradient_step_variational_inequality[
        OF convex closed u_mem])

  have vi_fixed:
    "inner (gradient_step alpha G x - x) (u - x) \<le> 0"
    using vi fixed by simp

  have expanded:
    "- alpha * inner (G x) (u - x) \<le> 0"
    using vi_fixed
    unfolding gradient_step_def
    by (simp add: algebra_simps)

  have scaled_nonneg:
    "0 \<le> alpha * inner (G x) (u - x)"
    using expanded by linarith

  have
    "0 / alpha \<le> (alpha * inner (G x) (u - x)) / alpha"
  proof (rule divide_right_mono)
    show "0 \<le> alpha * inner (G x) (u - x)"
      using scaled_nonneg .
    show "0 \<le> alpha"
      using alpha_pos by linarith
  qed

  then show "0 \<le> inner (G x) (u - x)"
    using alpha_pos by simp
qed

lemma first_order_condition_imp_projected_gradient_fixed_point:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes convex: "convex C"
    and closed: "closed C"
    and alpha_pos: "0 < alpha"
    and foc: "first_order_condition_at C (G x) x"
  shows "projected_gradient_step C alpha G x = x"
proof -
  let ?p = "projected_gradient_step C alpha G x"

  have x_mem: "x \<in> C"
    using foc by (rule first_order_condition_atD_mem)

  have p_mem: "?p \<in> C"
    by (rule projected_gradient_step_in_set_if_base_mem[OF closed x_mem])

  have vi:
    "inner (gradient_step alpha G x - ?p) (x - ?p) \<le> 0"
    by (rule projected_gradient_step_variational_inequality[
        OF convex closed x_mem])

  have foc_p:
    "0 \<le> inner (G x) (?p - x)"
    by (rule first_order_condition_atD[OF foc p_mem])

  have gx_xp_nonpos:
    "inner (G x) (x - ?p) \<le> 0"
    using foc_p
    by (simp add: inner_diff_right)

  have expanded:
    "inner (gradient_step alpha G x - ?p) (x - ?p) =
      norm (x - ?p) ^ 2 - alpha * inner (G x) (x - ?p)"
    unfolding gradient_step_def
    by (simp add: algebra_simps power2_norm_eq_inner)

  have bound:
    "norm (x - ?p) ^ 2 - alpha * inner (G x) (x - ?p) \<le> 0"
    using vi expanded by simp

  have extra_nonneg:
    "0 \<le> - alpha * inner (G x) (x - ?p)"
  proof -
    have "0 \<le> alpha * (- inner (G x) (x - ?p))"
    proof (rule mult_nonneg_nonneg)
      show "0 \<le> alpha"
        using alpha_pos by linarith
    next
      show "0 \<le> - inner (G x) (x - ?p)"
        using gx_xp_nonpos by simp
    qed
    then show ?thesis
      by simp
  qed

  have norm_sq_nonpos:
    "norm (x - ?p) ^ 2 \<le> 0"
    using bound extra_nonneg by linarith

  have "x - ?p = 0"
    using norm_sq_nonpos by simp

  then show ?thesis
    by simp
qed

theorem projected_gradient_fixed_point_iff_first_order_condition:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes convex: "convex C"
    and closed: "closed C"
    and x_mem: "x \<in> C"
    and alpha_pos: "0 < alpha"
  shows
    "projected_gradient_step C alpha G x = x
      \<longleftrightarrow> first_order_condition_at C (G x) x"
proof
  assume fixed: "projected_gradient_step C alpha G x = x"
  show "first_order_condition_at C (G x) x"
    by (rule projected_gradient_fixed_point_imp_first_order_condition[
        OF convex closed x_mem alpha_pos fixed])
next
  assume foc: "first_order_condition_at C (G x) x"
  show "projected_gradient_step C alpha G x = x"
    by (rule first_order_condition_imp_projected_gradient_fixed_point[
        where C = C and alpha = alpha and G = G and x = x,
        OF convex closed alpha_pos foc])
qed


subsection \<open>Zero projected-gradient mapping and first-order conditions\<close>

lemma projected_gradient_mapping_zero_imp_first_order_condition:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes convex: "convex C"
    and closed: "closed C"
    and x_mem: "x \<in> C"
    and alpha_pos: "0 < alpha"
    and zero: "projected_gradient_mapping C alpha G x = 0"
  shows "first_order_condition_at C (G x) x"
proof -
  have alpha_nonzero: "alpha \<noteq> 0"
    using alpha_pos by simp

  have fixed: "projected_gradient_step C alpha G x = x"
    by (rule projected_gradient_mapping_zero_imp_step_eq[
        OF alpha_nonzero zero])

  show ?thesis
    by (rule projected_gradient_fixed_point_imp_first_order_condition[
        OF convex closed x_mem alpha_pos fixed])
qed

lemma first_order_condition_imp_projected_gradient_mapping_zero:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes convex: "convex C"
    and closed: "closed C"
    and alpha_pos: "0 < alpha"
    and foc: "first_order_condition_at C (G x) x"
  shows "projected_gradient_mapping C alpha G x = 0"
proof -
  have fixed: "projected_gradient_step C alpha G x = x"
    by (rule first_order_condition_imp_projected_gradient_fixed_point[
        where C = C and alpha = alpha and G = G and x = x,
        OF convex closed alpha_pos foc])

  show ?thesis
    by (rule projected_gradient_step_eq_imp_mapping_zero[OF fixed])
qed

theorem projected_gradient_mapping_zero_iff_first_order_condition:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes convex: "convex C"
    and closed: "closed C"
    and x_mem: "x \<in> C"
    and alpha_pos: "0 < alpha"
  shows
    "projected_gradient_mapping C alpha G x = 0
      \<longleftrightarrow> first_order_condition_at C (G x) x"
proof
  assume zero: "projected_gradient_mapping C alpha G x = 0"
  show "first_order_condition_at C (G x) x"
    by (rule projected_gradient_mapping_zero_imp_first_order_condition[
        OF convex closed x_mem alpha_pos zero])
next
  assume foc: "first_order_condition_at C (G x) x"
  show "projected_gradient_mapping C alpha G x = 0"
    by (rule first_order_condition_imp_projected_gradient_mapping_zero[
        where C = C and alpha = alpha and G = G and x = x,
        OF convex closed alpha_pos foc])
qed


subsection \<open>Optimality consequences\<close>

lemma projected_gradient_fixed_point_imp_global_min_on:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and x_mem: "x \<in> C"
    and alpha_pos: "0 < alpha"
    and fixed: "projected_gradient_step C alpha G x = x"
  shows "global_min_on C f x"
proof -
  have foc: "first_order_condition_at C (G x) x"
    by (rule projected_gradient_fixed_point_imp_first_order_condition[
        OF convex closed x_mem alpha_pos fixed])

  have cd: "convex_differentiable_on C f G"
    using smooth
    by (rule smooth_convex_onD_convex_differentiable)

  show ?thesis
    by (rule convex_differentiable_on_foc_imp_global_min_on[
        OF cd foc])
qed

lemma projected_gradient_mapping_zero_imp_global_min_on:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and x_mem: "x \<in> C"
    and alpha_pos: "0 < alpha"
    and zero: "projected_gradient_mapping C alpha G x = 0"
  shows "global_min_on C f x"
proof -
  have foc: "first_order_condition_at C (G x) x"
    by (rule projected_gradient_mapping_zero_imp_first_order_condition[
        OF convex closed x_mem alpha_pos zero])

  have cd: "convex_differentiable_on C f G"
    using smooth
    by (rule smooth_convex_onD_convex_differentiable)

  show ?thesis
    by (rule convex_differentiable_on_foc_imp_global_min_on[
        OF cd foc])
qed

lemma first_order_condition_imp_global_min_on_smooth_convex:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and foc: "first_order_condition_at C (G x) x"
  shows "global_min_on C f x"
proof -
  have cd: "convex_differentiable_on C f G"
    using smooth
    by (rule smooth_convex_onD_convex_differentiable)

  show ?thesis
    by (rule convex_differentiable_on_foc_imp_global_min_on[
        OF cd foc])
qed


subsection \<open>Locale form\<close>

locale projected_gradient_mapping_context =
  fixes C :: "'a::{real_inner,heine_borel} set"
    and L alpha :: real
    and f :: "'a \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes smooth: "smooth_convex_on L C f G"
    and closed: "closed C"
    and convex: "convex C"
    and alpha_pos: "0 < alpha"
begin

lemma alpha_nonzero:
  "alpha \<noteq> 0"
  using alpha_pos by simp

lemma mapping_step_relation:
  "alpha *\<^sub>R projected_gradient_mapping C alpha G x =
    x - projected_gradient_step C alpha G x"
  by (rule projected_gradient_mapping_step_relation[OF alpha_nonzero])

lemma step_eq_sub_mapping:
  "projected_gradient_step C alpha G x =
    x - alpha *\<^sub>R projected_gradient_mapping C alpha G x"
  by (rule projected_gradient_step_eq_sub_mapping[OF alpha_nonzero])

lemma mapping_norm_eq_step_distance_divide:
  "norm (projected_gradient_mapping C alpha G x) =
    norm (x - projected_gradient_step C alpha G x) / alpha"
  by (rule projected_gradient_mapping_norm_eq_step_distance_divide[
    OF alpha_pos])

lemma base_step_distance_eq_alpha_mapping_norm:
  "norm (x - projected_gradient_step C alpha G x) =
    alpha * norm (projected_gradient_mapping C alpha G x)"
  by (rule projected_gradient_base_step_distance_eq_alpha_mapping_norm[
    OF alpha_pos])

lemma step_base_distance_eq_alpha_mapping_norm:
  "norm (projected_gradient_step C alpha G x - x) =
    alpha * norm (projected_gradient_mapping C alpha G x)"
  by (rule projected_gradient_step_base_distance_eq_alpha_mapping_norm[
    OF alpha_pos])

lemma step_distance_sq_eq_mapping_norm_sq:
  "norm (projected_gradient_step C alpha G x - x) ^ 2 =
    alpha ^ 2 * norm (projected_gradient_mapping C alpha G x) ^ 2"
  by (rule projected_gradient_step_distance_sq_eq_mapping_norm_sq[
    OF alpha_pos])

lemma mapping_norm_sq_eq_step_distance_sq:
  "norm (projected_gradient_mapping C alpha G x) ^ 2 =
    norm (projected_gradient_step C alpha G x - x) ^ 2 / alpha ^ 2"
  by (rule projected_gradient_mapping_norm_sq_eq_step_distance_sq[
    OF alpha_pos])

lemma mapping_zero_iff_step_distance_zero:
  "projected_gradient_mapping C alpha G x = 0
    \<longleftrightarrow> norm (projected_gradient_step C alpha G x - x) = 0"
  by (rule projected_gradient_mapping_zero_iff_step_distance_zero[
    OF alpha_nonzero])

lemma mapping_zero_iff_fixed_point:
  "projected_gradient_mapping C alpha G x = 0
    \<longleftrightarrow> projected_gradient_step C alpha G x = x"
  by (rule projected_gradient_mapping_zero_iff_fixed_point[
      OF alpha_nonzero])

lemma mapping_variational_inequality:
  assumes u_mem: "u \<in> C"
  shows
    "inner
      (projected_gradient_mapping C alpha G x - G x)
      (u - projected_gradient_step C alpha G x)
      \<le> 0"
  by (rule projected_gradient_mapping_variational_inequality[
      OF convex closed u_mem alpha_pos])

lemma fixed_point_imp_first_order_condition:
  assumes x_mem: "x \<in> C"
    and fixed: "projected_gradient_step C alpha G x = x"
  shows "first_order_condition_at C (G x) x"
  by (rule projected_gradient_fixed_point_imp_first_order_condition[
      OF convex closed x_mem alpha_pos fixed])

lemma first_order_condition_imp_fixed_point:
  assumes foc: "first_order_condition_at C (G x) x"
  shows "projected_gradient_step C alpha G x = x"
  by (rule first_order_condition_imp_projected_gradient_fixed_point[
      where C = C and alpha = alpha and G = G and x = x,
      OF convex closed alpha_pos foc])

lemma fixed_point_iff_first_order_condition:
  assumes x_mem: "x \<in> C"
  shows
    "projected_gradient_step C alpha G x = x
      \<longleftrightarrow> first_order_condition_at C (G x) x"
  by (rule projected_gradient_fixed_point_iff_first_order_condition[
      OF convex closed x_mem alpha_pos])

lemma mapping_zero_imp_first_order_condition:
  assumes x_mem: "x \<in> C"
    and zero: "projected_gradient_mapping C alpha G x = 0"
  shows "first_order_condition_at C (G x) x"
  by (rule projected_gradient_mapping_zero_imp_first_order_condition[
      OF convex closed x_mem alpha_pos zero])

lemma first_order_condition_imp_mapping_zero:
  assumes foc: "first_order_condition_at C (G x) x"
  shows "projected_gradient_mapping C alpha G x = 0"
  by (rule first_order_condition_imp_projected_gradient_mapping_zero[
      where C = C and alpha = alpha and G = G and x = x,
      OF convex closed alpha_pos foc])

lemma mapping_zero_iff_first_order_condition:
  assumes x_mem: "x \<in> C"
  shows
    "projected_gradient_mapping C alpha G x = 0
      \<longleftrightarrow> first_order_condition_at C (G x) x"
  by (rule projected_gradient_mapping_zero_iff_first_order_condition[
      OF convex closed x_mem alpha_pos])

lemma fixed_point_imp_global_min_on:
  assumes x_mem: "x \<in> C"
    and fixed: "projected_gradient_step C alpha G x = x"
  shows "global_min_on C f x"
  by (rule projected_gradient_fixed_point_imp_global_min_on[
      OF smooth closed convex x_mem alpha_pos fixed])

lemma mapping_zero_imp_global_min_on:
  assumes x_mem: "x \<in> C"
    and zero: "projected_gradient_mapping C alpha G x = 0"
  shows "global_min_on C f x"
  by (rule projected_gradient_mapping_zero_imp_global_min_on[
      OF smooth closed convex x_mem alpha_pos zero])

lemma first_order_condition_imp_global_min_on:
  assumes foc: "first_order_condition_at C (G x) x"
  shows "global_min_on C f x"
  by (rule first_order_condition_imp_global_min_on_smooth_convex[
      OF smooth foc])

end


text \<open>
This file packages the projected-gradient mapping as an explicit optimization
residual.  The norm identities
@{thm projected_gradient_mapping_norm_eq_step_distance_divide} and
@{thm projected_gradient_step_distance_sq_eq_mapping_norm_sq} show that the
mapping norm is exactly the projected-step residual normalized by the stepsize.

The main bridge theorem is
@{thm projected_gradient_mapping_zero_iff_first_order_condition}: for a feasible
point x and a positive stepsize, the projected-gradient mapping vanishes exactly
when x satisfies the constrained first-order variational inequality.

Together with smooth convexity, this gives the optimality certificate
@{thm projected_gradient_mapping_zero_imp_global_min_on}.
\<close>

end