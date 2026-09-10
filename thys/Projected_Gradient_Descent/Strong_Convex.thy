theory Strong_Convex
  imports Projected_Gradient_Mapping
begin

section \<open>Strong convexity for smooth first-order methods\<close>

text \<open>
This theory introduces a first-order lower-bound interface for strong convexity.

The main interface is
@{text \<open>f y >= f x + inner (G x) (y - x) + (mu / 2) * norm (y - x) ^ 2\<close>}.
This formulation is well suited to the existing development because it uses
the same named gradient field @{text \<open>G\<close>} as the smooth-convex and
projected-gradient layers.

The file proves three kinds of consequences:
strong convexity implies the ordinary convex first-order lower bound; at a
first-order optimal point, the function-value gap controls squared distance;
under positive strong convexity, global minimizers are unique.

These results are intended to feed into later linear-convergence proofs for
gradient descent and projected gradient descent.
\<close>


subsection \<open>First-order strong convexity lower bounds\<close>

definition strong_convex_lower_bound_on ::
  "real \<Rightarrow> 'a::real_inner set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "strong_convex_lower_bound_on mu S f G \<longleftrightarrow>
     0 \<le> mu \<and>
     (\<forall>x\<in>S. \<forall>y\<in>S.
        f x + inner (G x) (y - x) + (mu / 2) * norm (y - x) ^ 2 \<le> f y)"

lemma strong_convex_lower_bound_onI:
  assumes "0 \<le> mu"
    and "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow>
      f x + inner (G x) (y - x) + (mu / 2) * norm (y - x) ^ 2 \<le> f y"
  shows "strong_convex_lower_bound_on mu S f G"
  using assms
  unfolding strong_convex_lower_bound_on_def
  by auto

lemma strong_convex_lower_bound_onD_nonneg:
  assumes "strong_convex_lower_bound_on mu S f G"
  shows "0 \<le> mu"
  using assms
  unfolding strong_convex_lower_bound_on_def
  by auto

lemma strong_convex_lower_bound_onD:
  assumes "strong_convex_lower_bound_on mu S f G"
    and "x \<in> S"
    and "y \<in> S"
  shows
    "f x + inner (G x) (y - x) + (mu / 2) * norm (y - x) ^ 2 \<le> f y"
  using assms
  unfolding strong_convex_lower_bound_on_def
  by auto

lemma strong_convex_lower_bound_on_subset:
  assumes strong: "strong_convex_lower_bound_on mu T f G"
    and subset: "S \<subseteq> T"
  shows "strong_convex_lower_bound_on mu S f G"
proof (rule strong_convex_lower_bound_onI)
  show "0 \<le> mu"
    using strong
    by (rule strong_convex_lower_bound_onD_nonneg)
next
  fix x y
  assume xS: "x \<in> S" and yS: "y \<in> S"

  have xT: "x \<in> T"
    using subset xS by auto

  have yT: "y \<in> T"
    using subset yS by auto

  show
    "f x + inner (G x) (y - x) + (mu / 2) * norm (y - x) ^ 2 \<le> f y"
    by (rule strong_convex_lower_bound_onD[OF strong xT yT])
qed

lemma strong_convex_lower_bound_on_mono_mu:
  assumes strong: "strong_convex_lower_bound_on mu S f G"
    and nu_nonneg: "0 \<le> nu"
    and nu_le_mu: "nu \<le> mu"
  shows "strong_convex_lower_bound_on nu S f G"
proof (rule strong_convex_lower_bound_onI)
  show "0 \<le> nu"
    using nu_nonneg .
next
  fix x y
  assume x: "x \<in> S" and y: "y \<in> S"

  have strong_est:
    "f x + inner (G x) (y - x) + (mu / 2) * norm (y - x) ^ 2 \<le> f y"
    by (rule strong_convex_lower_bound_onD[OF strong x y])

  have coeff:
    "nu / 2 \<le> mu / 2"
    using nu_le_mu by simp

  have term_mono:
    "(nu / 2) * norm (y - x) ^ 2
      \<le> (mu / 2) * norm (y - x) ^ 2"
    using coeff
    by (intro mult_right_mono) simp_all

  show
    "f x + inner (G x) (y - x) + (nu / 2) * norm (y - x) ^ 2 \<le> f y"
    using strong_est term_mono by linarith
qed

lemma strong_convex_lower_bound_on_imp_gradient_lower_bound_on:
  assumes strong: "strong_convex_lower_bound_on mu S f G"
  shows "gradient_lower_bound_on S f G"
proof (rule gradient_lower_bound_onI)
  fix x y
  assume x: "x \<in> S" and y: "y \<in> S"

  have strong_est:
    "f x + inner (G x) (y - x) + (mu / 2) * norm (y - x) ^ 2 \<le> f y"
    by (rule strong_convex_lower_bound_onD[OF strong x y])

  have mu_nonneg: "0 \<le> mu"
    using strong
    by (rule strong_convex_lower_bound_onD_nonneg)

  have term_nonneg:
    "0 \<le> (mu / 2) * norm (y - x) ^ 2"
  proof -
    have "0 \<le> mu / 2"
      using mu_nonneg by simp
    moreover have "0 \<le> norm (y - x) ^ 2"
      by simp
    ultimately show ?thesis
      by (rule mult_nonneg_nonneg)
  qed

  show "f x + inner (G x) (y - x) \<le> f y"
    using strong_est term_nonneg by linarith
qed

lemma strong_convex_lower_bound_on_imp_supports_on:
  assumes strong: "strong_convex_lower_bound_on mu S f G"
  shows "supports_on S f G"
  using gradient_lower_bound_on_imp_supports_on[
      OF strong_convex_lower_bound_on_imp_gradient_lower_bound_on[OF strong]] .


subsection \<open>Strongly convex differentiable functions\<close>

definition strongly_convex_differentiable_on ::
  "real \<Rightarrow> 'a::real_inner set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "strongly_convex_differentiable_on mu S f G \<longleftrightarrow>
     convex_differentiable_on S f G \<and> strong_convex_lower_bound_on mu S f G"

lemma strongly_convex_differentiable_onI:
  assumes "convex_differentiable_on S f G"
    and "strong_convex_lower_bound_on mu S f G"
  shows "strongly_convex_differentiable_on mu S f G"
  using assms
  unfolding strongly_convex_differentiable_on_def
  by auto

lemma strongly_convex_differentiable_onD_convex_differentiable:
  assumes "strongly_convex_differentiable_on mu S f G"
  shows "convex_differentiable_on S f G"
  using assms
  unfolding strongly_convex_differentiable_on_def
  by auto

lemma strongly_convex_differentiable_onD_strong:
  assumes "strongly_convex_differentiable_on mu S f G"
  shows "strong_convex_lower_bound_on mu S f G"
  using assms
  unfolding strongly_convex_differentiable_on_def
  by auto

lemma strongly_convex_differentiable_onD_nonneg:
  assumes "strongly_convex_differentiable_on mu S f G"
  shows "0 \<le> mu"
  using strongly_convex_differentiable_onD_strong[OF assms]
  by (rule strong_convex_lower_bound_onD_nonneg)

lemma strongly_convex_differentiable_onD_convex_on:
  assumes "strongly_convex_differentiable_on mu S f G"
  shows "convex_on S f"
  using strongly_convex_differentiable_onD_convex_differentiable[OF assms]
  by (rule convex_differentiable_onD_convex_on)

lemma strongly_convex_differentiable_onD_has_gradient_on:
  assumes "strongly_convex_differentiable_on mu S f G"
  shows "has_gradient_on f S G"
  using strongly_convex_differentiable_onD_convex_differentiable[OF assms]
  by (rule convex_differentiable_onD_has_gradient_on)

lemma strongly_convex_differentiable_on_subset:
  assumes strong: "strongly_convex_differentiable_on mu T f G"
    and subset: "S \<subseteq> T"
    and convex: "convex S"
  shows "strongly_convex_differentiable_on mu S f G"
proof (rule strongly_convex_differentiable_onI)
  show "convex_differentiable_on S f G"
    by (rule convex_differentiable_on_subset[
        OF strongly_convex_differentiable_onD_convex_differentiable[
          OF strong] subset convex])
next
  show "strong_convex_lower_bound_on mu S f G"
    by (rule strong_convex_lower_bound_on_subset[
        OF strongly_convex_differentiable_onD_strong[OF strong] subset])
qed

lemma strongly_convex_differentiable_on_imp_gradient_lower_bound_on:
  assumes strong: "strongly_convex_differentiable_on mu S f G"
  shows "gradient_lower_bound_on S f G"
  using strongly_convex_differentiable_onD_strong[OF strong]
  by (rule strong_convex_lower_bound_on_imp_gradient_lower_bound_on)

lemma strongly_convex_differentiable_on_imp_supports_on:
  assumes strong: "strongly_convex_differentiable_on mu S f G"
  shows "supports_on S f G"
  using strongly_convex_differentiable_onD_strong[OF strong]
  by (rule strong_convex_lower_bound_on_imp_supports_on)


subsection \<open>Strongly smooth convex functions\<close>

definition strongly_smooth_convex_on ::
  "real \<Rightarrow> real \<Rightarrow> 'a::real_inner set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "strongly_smooth_convex_on L mu S f G \<longleftrightarrow>
     smooth_convex_on L S f G \<and> strong_convex_lower_bound_on mu S f G"

lemma strongly_smooth_convex_onI:
  assumes "smooth_convex_on L S f G"
    and "strong_convex_lower_bound_on mu S f G"
  shows "strongly_smooth_convex_on L mu S f G"
  using assms
  unfolding strongly_smooth_convex_on_def
  by auto

lemma strongly_smooth_convex_onD_smooth:
  assumes "strongly_smooth_convex_on L mu S f G"
  shows "smooth_convex_on L S f G"
  using assms
  unfolding strongly_smooth_convex_on_def
  by auto

lemma strongly_smooth_convex_onD_strong:
  assumes "strongly_smooth_convex_on L mu S f G"
  shows "strong_convex_lower_bound_on mu S f G"
  using assms
  unfolding strongly_smooth_convex_on_def
  by auto

lemma strongly_smooth_convex_onD_convex_differentiable:
  assumes "strongly_smooth_convex_on L mu S f G"
  shows "convex_differentiable_on S f G"
  using strongly_smooth_convex_onD_smooth[OF assms]
  by (rule smooth_convex_onD_convex_differentiable)

lemma strongly_smooth_convex_onD_smooth_upper_bound:
  assumes "strongly_smooth_convex_on L mu S f G"
  shows "smooth_upper_bound_on L S f G"
  using strongly_smooth_convex_onD_smooth[OF assms]
  by (rule smooth_convex_onD_smooth_upper_bound)

lemma strongly_smooth_convex_onD_strongly_convex_differentiable:
  assumes "strongly_smooth_convex_on L mu S f G"
  shows "strongly_convex_differentiable_on mu S f G"
proof (rule strongly_convex_differentiable_onI)
  show "convex_differentiable_on S f G"
    by (rule strongly_smooth_convex_onD_convex_differentiable[OF assms])
next
  show "strong_convex_lower_bound_on mu S f G"
    by (rule strongly_smooth_convex_onD_strong[OF assms])
qed

lemma strongly_smooth_convex_on_subset:
  assumes strong: "strongly_smooth_convex_on L mu T f G"
    and subset: "S \<subseteq> T"
    and convex: "convex S"
  shows "strongly_smooth_convex_on L mu S f G"
proof (rule strongly_smooth_convex_onI)
  show "smooth_convex_on L S f G"
    by (rule smooth_convex_on_subset[
        OF strongly_smooth_convex_onD_smooth[OF strong] subset convex])
next
  show "strong_convex_lower_bound_on mu S f G"
    by (rule strong_convex_lower_bound_on_subset[
        OF strongly_smooth_convex_onD_strong[OF strong] subset])
qed


subsection \<open>Global minimizers and first-order conditions\<close>

lemma global_min_on_value_eq:
  assumes min_x: "global_min_on S f x"
    and min_y: "global_min_on S f y"
  shows "f x = f y"
proof -
  have x_mem: "x \<in> S"
    using min_x
    by (rule global_min_onD_mem)

  have y_mem: "y \<in> S"
    using min_y
    by (rule global_min_onD_mem)

  have xy: "f x \<le> f y"
    by (rule global_min_onD[OF min_x y_mem])

  have yx: "f y \<le> f x"
    by (rule global_min_onD[OF min_y x_mem])

  show ?thesis
    using xy yx by linarith
qed

lemma global_min_on_has_gradient_imp_first_order_condition:
  fixes f :: "'a::real_inner \<Rightarrow> real"
  assumes convex: "convex S"
    and minimizer: "global_min_on S f x"
    and grad: "has_gradient f x g"
  shows "first_order_condition_at S g x"
proof -
  have x_mem: "x \<in> S"
    using minimizer
    by (rule global_min_onD_mem)

  show ?thesis
  proof (rule first_order_condition_atI)
    show "x \<in> S"
      using x_mem .
  next
    fix y
    assume y_mem: "y \<in> S"

    define d where "d = y - x"

    have ev01:
      "eventually (\<lambda>t::real. t \<in> {0<..<1}) (at_right 0)"
      using eventually_at_right_real[OF zero_less_one] .

    have ev_nonneg:
      "eventually
        (\<lambda>t::real. 0 \<le> (f (x + t *\<^sub>R d) - f x) / t)
        (at_right 0)"
      using ev01
    proof eventually_elim
      fix t :: real
      assume t: "t \<in> {0<..<1}"

      have tpos: "0 < t"
        using t by simp

      have tle: "t \<le> 1"
        using t by simp

      have z_mem: "x + t *\<^sub>R d \<in> S"
        unfolding d_def
        by (rule convex_contains_affine_line[
            OF convex x_mem y_mem, of t]) (use tpos tle in simp_all)

      have min_bound: "f x \<le> f (x + t *\<^sub>R d)"
        by (rule global_min_onD[OF minimizer z_mem])

      show "0 \<le> (f (x + t *\<^sub>R d) - f x) / t"
        using min_bound tpos
        by (simp add: field_simps)
    qed

    have nontriv: "\<not> trivial_limit (at_right (0::real))"
      by simp

    have zero_tendsto:
      "((\<lambda>t::real. 0) \<longlongrightarrow> (0::real)) (at_right 0)"
      by simp

    have slope_tendsto:
      "((\<lambda>t::real. (f (x + t *\<^sub>R d) - f x) / t) \<longlongrightarrow> inner d g)
        (at_right 0)"
      using has_gradient_line_slope_tendsto[OF grad, of d] .

    have ev_le:
      "eventually
        (\<lambda>t::real. (\<lambda>t::real. 0) t \<le>
          (f (x + t *\<^sub>R d) - f x) / t)
        (at_right 0)"
      using ev_nonneg by simp

    have "0 \<le> inner d g"
      by (rule tendsto_le[
          OF nontriv slope_tendsto zero_tendsto ev_le])

    then show "0 \<le> inner g (y - x)"
      unfolding d_def
      by (simp add: inner_commute)
  qed
qed

lemma convex_differentiable_on_global_min_imp_first_order_condition:
  assumes cd: "convex_differentiable_on S f G"
    and minimizer: "global_min_on S f x"
  shows "first_order_condition_at S (G x) x"
proof -
  have x_mem: "x \<in> S"
    using minimizer
    by (rule global_min_onD_mem)

  have convex: "convex S"
    using cd
    by (rule convex_differentiable_on_convex)

  have grad: "has_gradient f x (G x)"
    using cd x_mem
    by (rule convex_differentiable_on_gradientD)

  show ?thesis
    by (rule global_min_on_has_gradient_imp_first_order_condition[
        OF convex minimizer grad])
qed


subsection \<open>Distance-gap lower bounds\<close>

lemma strong_convex_foc_distance_gap:
  fixes f :: "'a::real_inner \<Rightarrow> real"
  assumes strong: "strong_convex_lower_bound_on mu S f G"
    and foc: "first_order_condition_at S (G xstar) xstar"
    and x_mem: "x \<in> S"
  shows
    "(mu / 2) * norm (x - xstar) ^ 2 \<le> f x - f xstar"
proof -
  have xstar_mem: "xstar \<in> S"
    using foc
    by (rule first_order_condition_atD_mem)

  have lower:
    "f xstar + inner (G xstar) (x - xstar)
      + (mu / 2) * norm (x - xstar) ^ 2 \<le> f x"
    by (rule strong_convex_lower_bound_onD[
        OF strong xstar_mem x_mem])

  have foc_nonneg:
    "0 \<le> inner (G xstar) (x - xstar)"
    by (rule first_order_condition_atD[OF foc x_mem])

  show ?thesis
    using lower foc_nonneg by linarith
qed

lemma strongly_convex_global_min_distance_gap:
  fixes f :: "'a::real_inner \<Rightarrow> real"
  assumes strong: "strongly_convex_differentiable_on mu S f G"
    and minimizer: "global_min_on S f xstar"
    and x_mem: "x \<in> S"
  shows
    "(mu / 2) * norm (x - xstar) ^ 2 \<le> f x - f xstar"
proof -
  have cd: "convex_differentiable_on S f G"
    by (rule strongly_convex_differentiable_onD_convex_differentiable[
        OF strong])

  have strong_lb: "strong_convex_lower_bound_on mu S f G"
    by (rule strongly_convex_differentiable_onD_strong[OF strong])

  have foc: "first_order_condition_at S (G xstar) xstar"
    by (rule convex_differentiable_on_global_min_imp_first_order_condition[
        where G = G and x = xstar,
        OF cd minimizer])

  show ?thesis
    by (rule strong_convex_foc_distance_gap[
        where G = G and xstar = xstar,
        OF strong_lb foc x_mem])
qed

lemma strongly_smooth_convex_global_min_distance_gap:
  fixes f :: "'a::real_inner \<Rightarrow> real"
  assumes strong: "strongly_smooth_convex_on L mu S f G"
    and minimizer: "global_min_on S f xstar"
    and x_mem: "x \<in> S"
  shows
    "(mu / 2) * norm (x - xstar) ^ 2 \<le> f x - f xstar"
proof -
  have scd: "strongly_convex_differentiable_on mu S f G"
    by (rule strongly_smooth_convex_onD_strongly_convex_differentiable[
        OF strong])

  show ?thesis
    by (rule strongly_convex_global_min_distance_gap[
        where G = G and xstar = xstar,
        OF scd minimizer x_mem])
qed

lemma strong_convex_foc_distance_gap_nonnegative:
  fixes f :: "'a::real_inner \<Rightarrow> real"
  assumes strong: "strong_convex_lower_bound_on mu S f G"
    and foc: "first_order_condition_at S (G xstar) xstar"
    and x_mem: "x \<in> S"
  shows "0 \<le> f x - f xstar"
proof -
  have gap:
    "(mu / 2) * norm (x - xstar) ^ 2 \<le> f x - f xstar"
    by (rule strong_convex_foc_distance_gap[
        where G = G and xstar = xstar,
        OF strong foc x_mem])

  have mu_nonneg: "0 \<le> mu"
    using strong
    by (rule strong_convex_lower_bound_onD_nonneg)

  have lhs_nonneg:
    "0 \<le> (mu / 2) * norm (x - xstar) ^ 2"
  proof -
    have "0 \<le> mu / 2"
      using mu_nonneg by simp
    moreover have "0 \<le> norm (x - xstar) ^ 2"
      by simp
    ultimately show ?thesis
      by (rule mult_nonneg_nonneg)
  qed

  show ?thesis
    using lhs_nonneg gap by linarith
qed


subsection \<open>Uniqueness of minimizers\<close>

lemma strongly_convex_global_min_unique:
  fixes f :: "'a::real_inner \<Rightarrow> real"
  assumes strong: "strongly_convex_differentiable_on mu S f G"
    and mu_pos: "0 < mu"
    and min_x: "global_min_on S f x"
    and min_y: "global_min_on S f y"
  shows "x = y"
proof -
  have y_mem: "y \<in> S"
    using min_y
    by (rule global_min_onD_mem)

  have gap:
    "(mu / 2) * norm (y - x) ^ 2 \<le> f y - f x"
    by (rule strongly_convex_global_min_distance_gap[
        where G = G and xstar = x,
        OF strong min_x y_mem])

  have value_eq: "f x = f y"
    by (rule global_min_on_value_eq[OF min_x min_y])

  have term_nonpos:
    "(mu / 2) * norm (y - x) ^ 2 \<le> 0"
    using gap value_eq by simp

  have term_nonneg:
    "0 \<le> (mu / 2) * norm (y - x) ^ 2"
  proof -
    have "0 \<le> mu / 2"
      using mu_pos by simp
    moreover have "0 \<le> norm (y - x) ^ 2"
      by simp
    ultimately show ?thesis
      by (rule mult_nonneg_nonneg)
  qed

  have term_zero:
    "(mu / 2) * norm (y - x) ^ 2 = 0"
    using term_nonneg term_nonpos by linarith

  have norm_zero:
    "norm (y - x) ^ 2 = 0"
    using term_zero mu_pos by simp

  have "y - x = 0"
    using norm_zero by simp

  then show "x = y"
    by simp
qed

lemma strongly_smooth_convex_global_min_unique:
  fixes f :: "'a::real_inner \<Rightarrow> real"
  assumes strong: "strongly_smooth_convex_on L mu S f G"
    and mu_pos: "0 < mu"
    and min_x: "global_min_on S f x"
    and min_y: "global_min_on S f y"
  shows "x = y"
proof -
  have scd: "strongly_convex_differentiable_on mu S f G"
    by (rule strongly_smooth_convex_onD_strongly_convex_differentiable[
        OF strong])

  show ?thesis
    by (rule strongly_convex_global_min_unique[
        where G = G,
        OF scd mu_pos min_x min_y])
qed


subsection \<open>Consequences for projected-gradient optimality\<close>

lemma strongly_smooth_projected_mapping_zero_distance_gap:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
  assumes strong: "strongly_smooth_convex_on L mu C f G"
    and closed: "closed C"
    and convex: "convex C"
    and xstar_mem: "xstar \<in> C"
    and alpha_pos: "0 < alpha"
    and zero: "projected_gradient_mapping C alpha G xstar = 0"
    and x_mem: "x \<in> C"
  shows
    "(mu / 2) * norm (x - xstar) ^ 2 \<le> f x - f xstar"
proof -
  have smooth: "smooth_convex_on L C f G"
    by (rule strongly_smooth_convex_onD_smooth[OF strong])

  have min_xstar: "global_min_on C f xstar"
    by (rule projected_gradient_mapping_zero_imp_global_min_on[
        where L = L and alpha = alpha and G = G and x = xstar,
        OF smooth closed convex xstar_mem alpha_pos zero])

  show ?thesis
    by (rule strongly_smooth_convex_global_min_distance_gap[
        where G = G and xstar = xstar,
        OF strong min_xstar x_mem])
qed

lemma strongly_smooth_projected_mapping_zero_unique_global_min:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
  assumes strong: "strongly_smooth_convex_on L mu C f G"
    and mu_pos: "0 < mu"
    and closed: "closed C"
    and convex: "convex C"
    and x_mem: "x \<in> C"
    and alpha_pos: "0 < alpha"
    and zero: "projected_gradient_mapping C alpha G x = 0"
    and minimizer: "global_min_on C f y"
  shows "x = y"
proof -
  have smooth: "smooth_convex_on L C f G"
    by (rule strongly_smooth_convex_onD_smooth[OF strong])

  have min_x: "global_min_on C f x"
    by (rule projected_gradient_mapping_zero_imp_global_min_on[
        where L = L and alpha = alpha and G = G and x = x,
        OF smooth closed convex x_mem alpha_pos zero])

  show ?thesis
    by (rule strongly_smooth_convex_global_min_unique[
        where G = G,
        OF strong mu_pos min_x minimizer])
qed


subsection \<open>Locale form: strongly convex differentiable functions\<close>

locale strongly_convex_differentiable =
  convex_differentiable S f G
  for S :: "'a::real_inner set"
    and f :: "'a \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a" +
  fixes mu :: real
  assumes strong_lower_bound: "strong_convex_lower_bound_on mu S f G"
begin

lemma strong_nonneg:
  "0 \<le> mu"
  using strong_lower_bound
  by (rule strong_convex_lower_bound_onD_nonneg)

lemma strong_lower:
  assumes "x \<in> S"
    and "y \<in> S"
  shows
    "f x + inner (G x) (y - x) + (mu / 2) * norm (y - x) ^ 2 \<le> f y"
  by (rule strong_convex_lower_bound_onD[
      OF strong_lower_bound assms])

lemma strongly_convex_differentiable_on_self:
  "strongly_convex_differentiable_on mu S f G"
proof (rule strongly_convex_differentiable_onI)
  show "convex_differentiable_on S f G"
    by (rule convex_differentiable_onI[OF convex_f gradient_f])
next
  show "strong_convex_lower_bound_on mu S f G"
    by (rule strong_lower_bound)
qed

lemma gradient_lower_bound:
  "gradient_lower_bound_on S f G"
  by (rule strong_convex_lower_bound_on_imp_gradient_lower_bound_on[
      OF strong_lower_bound])

lemma supports:
  "supports_on S f G"
  by (rule strong_convex_lower_bound_on_imp_supports_on[
      OF strong_lower_bound])

lemma global_min_imp_first_order_condition:
  assumes minimizer: "global_min_on S f x"
  shows "first_order_condition_at S (G x) x"
proof -
  have cd: "convex_differentiable_on S f G"
    by (rule convex_differentiable_onI[OF convex_f gradient_f])

  show ?thesis
    by (rule convex_differentiable_on_global_min_imp_first_order_condition[
        where G = G and x = x,
        OF cd minimizer])
qed

lemma foc_distance_gap:
  assumes foc: "first_order_condition_at S (G xstar) xstar"
    and x_mem: "x \<in> S"
  shows
    "(mu / 2) * norm (x - xstar) ^ 2 \<le> f x - f xstar"
  by (rule strong_convex_foc_distance_gap[
      where G = G and xstar = xstar,
      OF strong_lower_bound foc x_mem])

lemma global_min_distance_gap:
  assumes minimizer: "global_min_on S f xstar"
    and x_mem: "x \<in> S"
  shows
    "(mu / 2) * norm (x - xstar) ^ 2 \<le> f x - f xstar"
  by (rule strongly_convex_global_min_distance_gap[
      where G = G and xstar = xstar,
      OF strongly_convex_differentiable_on_self minimizer x_mem])

lemma global_min_unique:
  assumes mu_pos: "0 < mu"
    and min_x: "global_min_on S f x"
    and min_y: "global_min_on S f y"
  shows "x = y"
  by (rule strongly_convex_global_min_unique[
      where G = G,
      OF strongly_convex_differentiable_on_self mu_pos min_x min_y])

end


subsection \<open>Locale form: strongly smooth convex functions\<close>

locale strongly_smooth_convex =
  smooth_convex S f G L
  for S :: "'a::real_inner set"
    and f :: "'a \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
    and L :: real +
  fixes mu :: real
  assumes strong_lower_bound: "strong_convex_lower_bound_on mu S f G"
begin

lemma strong_nonneg:
  "0 \<le> mu"
  using strong_lower_bound
  by (rule strong_convex_lower_bound_onD_nonneg)

lemma strongly_smooth_convex_on_self:
  "strongly_smooth_convex_on L mu S f G"
proof (rule strongly_smooth_convex_onI)
  show "smooth_convex_on L S f G"
  proof (rule smooth_convex_onI)
    show "convex_differentiable_on S f G"
      by (rule convex_differentiable_onI[OF convex_f gradient_f])
  next
    show "smooth_upper_bound_on L S f G"
      by (rule smooth_bound)
  qed
next
  show "strong_convex_lower_bound_on mu S f G"
    by (rule strong_lower_bound)
qed

lemma strongly_convex_differentiable_on_self:
  "strongly_convex_differentiable_on mu S f G"
  by (rule strongly_smooth_convex_onD_strongly_convex_differentiable[
      OF strongly_smooth_convex_on_self])

lemma strong_lower:
  assumes "x \<in> S"
    and "y \<in> S"
  shows
    "f x + inner (G x) (y - x) + (mu / 2) * norm (y - x) ^ 2 \<le> f y"
  by (rule strong_convex_lower_bound_onD[
      OF strong_lower_bound assms])

lemma global_min_distance_gap:
  assumes minimizer: "global_min_on S f xstar"
    and x_mem: "x \<in> S"
  shows
    "(mu / 2) * norm (x - xstar) ^ 2 \<le> f x - f xstar"
  by (rule strongly_smooth_convex_global_min_distance_gap[
      where L = L and G = G and xstar = xstar,
      OF strongly_smooth_convex_on_self minimizer x_mem])

lemma global_min_unique:
  assumes mu_pos: "0 < mu"
    and min_x: "global_min_on S f x"
    and min_y: "global_min_on S f y"
  shows "x = y"
  by (rule strongly_smooth_convex_global_min_unique[
      where L = L and G = G,
      OF strongly_smooth_convex_on_self mu_pos min_x min_y])

end


text \<open>
The main reusable theorem for later convergence arguments is
@{thm strongly_smooth_convex_global_min_distance_gap}.  It says that, for a
strongly smooth convex objective, the function-value gap to a global minimizer
controls the squared distance to that minimizer.

This is the key ingredient needed to turn the existing O(1/N) convergence
arguments into linear-convergence arguments under positive strong convexity.
\<close>

end