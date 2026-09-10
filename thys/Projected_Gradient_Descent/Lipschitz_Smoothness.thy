theory Lipschitz_Smoothness
  imports Projected_Gradient_Descent_Linear_Rate
begin

section \<open>Lipschitz gradients and smoothness interfaces\<close>

text \<open>
This theory connects the reusable smooth quadratic upper-bound interface with
a more primitive Lipschitz-gradient assumption.

The main bridge is the standard descent lemma along line segments:
@{text \<open>f y <= f x + inner (G x) (y - x) + (L / 2) * norm (y - x) ^ 2\<close>}.
The theory packages this bridge so that later convergence proofs can use the
same smoothness interface regardless of whether smoothness is assumed directly
or derived from a Lipschitz-gradient condition.
\<close>

subsection \<open>Line-segment descent-lemma certificates\<close>

definition line_descent_bound_on ::
  "real \<Rightarrow> 'a::real_inner set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "line_descent_bound_on L S f G \<longleftrightarrow>
     0 \<le> L \<and>
     (\<forall>x\<in>S. \<forall>y\<in>S.
        f y \<le> f x + inner (G x) (y - x) + (L / 2) * norm (y - x) ^ 2)"

lemma line_descent_bound_onI:
  assumes "0 \<le> L"
    and "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow>
      f y \<le> f x + inner (G x) (y - x) + (L / 2) * norm (y - x) ^ 2"
  shows "line_descent_bound_on L S f G"
  using assms
  unfolding line_descent_bound_on_def
  by auto

lemma line_descent_bound_onD_nonneg:
  assumes "line_descent_bound_on L S f G"
  shows "0 \<le> L"
  using assms
  unfolding line_descent_bound_on_def
  by auto

lemma line_descent_bound_onD:
  assumes "line_descent_bound_on L S f G"
    and "x \<in> S"
    and "y \<in> S"
  shows "f y \<le> f x + inner (G x) (y - x) + (L / 2) * norm (y - x) ^ 2"
  using assms
  unfolding line_descent_bound_on_def
  by auto

lemma line_descent_bound_on_imp_smooth_upper_bound_on:
  assumes line: "line_descent_bound_on L S f G"
  shows "smooth_upper_bound_on L S f G"
proof (rule smooth_upper_bound_onI)
  show "0 \<le> L"
    using line
    by (rule line_descent_bound_onD_nonneg)
next
  fix x y
  assume x: "x \<in> S" and y: "y \<in> S"

  show "f y \<le> f x + inner (G x) (y - x) + (L / 2) * norm (y - x) ^ 2"
    by (rule line_descent_bound_onD[OF line x y])
qed

lemma smooth_upper_bound_on_imp_line_descent_bound_on:
  assumes smooth: "smooth_upper_bound_on L S f G"
  shows "line_descent_bound_on L S f G"
proof (rule line_descent_bound_onI)
  show "0 \<le> L"
    using smooth
    by (rule smooth_upper_bound_onD_nonneg)
next
  fix x y
  assume x: "x \<in> S" and y: "y \<in> S"

  show "f y \<le> f x + inner (G x) (y - x) + (L / 2) * norm (y - x) ^ 2"
    by (rule smooth_upper_bound_onD[OF smooth x y])
qed

lemma line_descent_bound_on_iff_smooth_upper_bound_on:
  "line_descent_bound_on L S f G \<longleftrightarrow> smooth_upper_bound_on L S f G"
proof
  assume "line_descent_bound_on L S f G"
  then show "smooth_upper_bound_on L S f G"
    by (rule line_descent_bound_on_imp_smooth_upper_bound_on)
next
  assume "smooth_upper_bound_on L S f G"
  then show "line_descent_bound_on L S f G"
    by (rule smooth_upper_bound_on_imp_line_descent_bound_on)
qed

lemma line_descent_bound_on_subset:
  assumes line: "line_descent_bound_on L T f G"
    and subset: "S \<subseteq> T"
  shows "line_descent_bound_on L S f G"
proof (rule line_descent_bound_onI)
  show "0 \<le> L"
    using line
    by (rule line_descent_bound_onD_nonneg)
next
  fix x y
  assume xS: "x \<in> S" and yS: "y \<in> S"

  have xT: "x \<in> T"
    using subset xS by auto

  have yT: "y \<in> T"
    using subset yS by auto

  show "f y \<le> f x + inner (G x) (y - x) + (L / 2) * norm (y - x) ^ 2"
    by (rule line_descent_bound_onD[OF line xT yT])
qed

lemma line_descent_bound_on_mono_L:
  assumes line: "line_descent_bound_on L S f G"
    and LM: "L \<le> M"
  shows "line_descent_bound_on M S f G"
proof (rule line_descent_bound_onI)
  have L_nonneg: "0 \<le> L"
    using line
    by (rule line_descent_bound_onD_nonneg)

  show "0 \<le> M"
    using L_nonneg LM by linarith
next
  fix x y
  assume x: "x \<in> S" and y: "y \<in> S"

  have base:
    "f y \<le> f x + inner (G x) (y - x) + (L / 2) * norm (y - x) ^ 2"
    by (rule line_descent_bound_onD[OF line x y])

  have coeff:
    "L / 2 \<le> M / 2"
    using LM by simp

  have term_mono:
    "(L / 2) * norm (y - x) ^ 2 \<le> (M / 2) * norm (y - x) ^ 2"
    using coeff
    by (intro mult_right_mono) simp_all

  show "f y \<le> f x + inner (G x) (y - x) + (M / 2) * norm (y - x) ^ 2"
    using base term_mono by linarith
qed


subsection \<open>Lipschitz-supported smoothness\<close>

definition lipschitz_smooth_on ::
  "real \<Rightarrow> 'a::real_inner set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "lipschitz_smooth_on L S f G \<longleftrightarrow>
     has_gradient_on f S G \<and>
     lipschitz_gradient_on L S G \<and>
     line_descent_bound_on L S f G"

lemma lipschitz_smooth_onI:
  assumes "has_gradient_on f S G"
    and "lipschitz_gradient_on L S G"
    and "line_descent_bound_on L S f G"
  shows "lipschitz_smooth_on L S f G"
  using assms
  unfolding lipschitz_smooth_on_def
  by auto

lemma lipschitz_smooth_onD_has_gradient_on:
  assumes "lipschitz_smooth_on L S f G"
  shows "has_gradient_on f S G"
  using assms
  unfolding lipschitz_smooth_on_def
  by auto

lemma lipschitz_smooth_onD_lipschitz_gradient:
  assumes "lipschitz_smooth_on L S f G"
  shows "lipschitz_gradient_on L S G"
  using assms
  unfolding lipschitz_smooth_on_def
  by auto

lemma lipschitz_smooth_onD_line_descent:
  assumes "lipschitz_smooth_on L S f G"
  shows "line_descent_bound_on L S f G"
  using assms
  unfolding lipschitz_smooth_on_def
  by auto

lemma lipschitz_smooth_onD_smooth_upper_bound:
  assumes "lipschitz_smooth_on L S f G"
  shows "smooth_upper_bound_on L S f G"
  using lipschitz_smooth_onD_line_descent[OF assms]
  by (rule line_descent_bound_on_imp_smooth_upper_bound_on)

lemma lipschitz_smooth_onD_nonneg:
  assumes "lipschitz_smooth_on L S f G"
  shows "0 \<le> L"
  using lipschitz_smooth_onD_lipschitz_gradient[OF assms]
  by (rule lipschitz_gradient_onD_nonneg)

lemma lipschitz_smooth_on_subset:
  assumes smooth: "lipschitz_smooth_on L T f G"
    and subset: "S \<subseteq> T"
  shows "lipschitz_smooth_on L S f G"
proof (rule lipschitz_smooth_onI)
  show "has_gradient_on f S G"
    by (rule has_gradient_on_subset[
        OF lipschitz_smooth_onD_has_gradient_on[OF smooth] subset])
next
  show "lipschitz_gradient_on L S G"
    by (rule lipschitz_gradient_on_subset[
        OF lipschitz_smooth_onD_lipschitz_gradient[OF smooth] subset])
next
  show "line_descent_bound_on L S f G"
    by (rule line_descent_bound_on_subset[
        OF lipschitz_smooth_onD_line_descent[OF smooth] subset])
qed

lemma lipschitz_smooth_on_mono_L:
  assumes smooth: "lipschitz_smooth_on L S f G"
    and LM: "L \<le> M"
  shows "lipschitz_smooth_on M S f G"
proof (rule lipschitz_smooth_onI)
  show "has_gradient_on f S G"
    by (rule lipschitz_smooth_onD_has_gradient_on[OF smooth])
next
  show "lipschitz_gradient_on M S G"
    by (rule lipschitz_gradient_on_mono_L[
        OF lipschitz_smooth_onD_lipschitz_gradient[OF smooth] LM])
next
  show "line_descent_bound_on M S f G"
    by (rule line_descent_bound_on_mono_L[
        OF lipschitz_smooth_onD_line_descent[OF smooth] LM])
qed


subsection \<open>Connection with smooth convexity\<close>

definition lipschitz_smooth_convex_on ::
  "real \<Rightarrow> 'a::real_inner set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "lipschitz_smooth_convex_on L S f G \<longleftrightarrow>
     convex_on S f \<and> lipschitz_smooth_on L S f G"

lemma lipschitz_smooth_convex_onI:
  assumes "convex_on S f"
    and "lipschitz_smooth_on L S f G"
  shows "lipschitz_smooth_convex_on L S f G"
  using assms
  unfolding lipschitz_smooth_convex_on_def
  by auto

lemma lipschitz_smooth_convex_onD_convex_on:
  assumes "lipschitz_smooth_convex_on L S f G"
  shows "convex_on S f"
  using assms
  unfolding lipschitz_smooth_convex_on_def
  by auto

lemma lipschitz_smooth_convex_onD_lipschitz_smooth:
  assumes "lipschitz_smooth_convex_on L S f G"
  shows "lipschitz_smooth_on L S f G"
  using assms
  unfolding lipschitz_smooth_convex_on_def
  by auto

lemma lipschitz_smooth_convex_onD_has_gradient_on:
  assumes "lipschitz_smooth_convex_on L S f G"
  shows "has_gradient_on f S G"
  using lipschitz_smooth_convex_onD_lipschitz_smooth[OF assms]
  by (rule lipschitz_smooth_onD_has_gradient_on)

lemma lipschitz_smooth_convex_onD_lipschitz_gradient:
  assumes "lipschitz_smooth_convex_on L S f G"
  shows "lipschitz_gradient_on L S G"
  using lipschitz_smooth_convex_onD_lipschitz_smooth[OF assms]
  by (rule lipschitz_smooth_onD_lipschitz_gradient)

lemma lipschitz_smooth_convex_onD_smooth_upper_bound:
  assumes "lipschitz_smooth_convex_on L S f G"
  shows "smooth_upper_bound_on L S f G"
  using lipschitz_smooth_convex_onD_lipschitz_smooth[OF assms]
  by (rule lipschitz_smooth_onD_smooth_upper_bound)

lemma lipschitz_smooth_convex_on_imp_convex_differentiable_on:
  assumes smooth: "lipschitz_smooth_convex_on L S f G"
  shows "convex_differentiable_on S f G"
proof (rule convex_differentiable_onI)
  show "convex_on S f"
    by (rule lipschitz_smooth_convex_onD_convex_on[OF smooth])
next
  show "has_gradient_on f S G"
    by (rule lipschitz_smooth_convex_onD_has_gradient_on[OF smooth])
qed

lemma lipschitz_smooth_convex_on_imp_smooth_convex_on:
  assumes smooth: "lipschitz_smooth_convex_on L S f G"
  shows "smooth_convex_on L S f G"
proof (rule smooth_convex_onI)
  show "convex_differentiable_on S f G"
    by (rule lipschitz_smooth_convex_on_imp_convex_differentiable_on[
        OF smooth])
next
  show "smooth_upper_bound_on L S f G"
    by (rule lipschitz_smooth_convex_onD_smooth_upper_bound[
        OF smooth])
qed

lemma smooth_convex_on_and_lipschitz_gradient_imp_lipschitz_smooth_convex_on:
  assumes smooth: "smooth_convex_on L S f G"
    and lip: "lipschitz_gradient_on L S G"
  shows "lipschitz_smooth_convex_on L S f G"
proof (rule lipschitz_smooth_convex_onI)
  show "convex_on S f"
    by (rule smooth_convex_onD_convex_on[OF smooth])
next
  show "lipschitz_smooth_on L S f G"
  proof (rule lipschitz_smooth_onI)
    show "has_gradient_on f S G"
      by (rule smooth_convex_onD_has_gradient_on[OF smooth])
  next
    show "lipschitz_gradient_on L S G"
      using lip .
  next
    have smooth_bound: "smooth_upper_bound_on L S f G"
      by (rule smooth_convex_onD_smooth_upper_bound[OF smooth])
    show "line_descent_bound_on L S f G"
      by (rule smooth_upper_bound_on_imp_line_descent_bound_on[
          OF smooth_bound])
  qed
qed


subsection \<open>Elementary consequences of Lipschitz gradients\<close>

lemma lipschitz_gradient_on_dist:
  fixes G :: "'a::real_inner \<Rightarrow> 'a"
  assumes lip: "lipschitz_gradient_on L S G"
    and x: "x \<in> S"
    and y: "y \<in> S"
  shows "norm (G y - G x) \<le> L * norm (y - x)"
proof -
  have base: "norm (G x - G y) \<le> L * norm (x - y)"
    by (rule lipschitz_gradient_onD[OF lip x y])

  have norm_grad: "norm (G y - G x) = norm (G x - G y)"
    by (simp add: norm_minus_commute)

  have norm_arg: "norm (y - x) = norm (x - y)"
    by (simp add: norm_minus_commute)

  show ?thesis
    using base
    by (simp only: norm_grad norm_arg)
qed

lemma lipschitz_gradient_on_inner_difference_bound:
  fixes G :: "'a::real_inner \<Rightarrow> 'a"
  assumes lip: "lipschitz_gradient_on L S G"
    and x: "x \<in> S"
    and y: "y \<in> S"
  shows "inner (G y - G x) (y - x) \<le> L * norm (y - x) ^ 2"
proof -
  have lip_bound: "norm (G y - G x) \<le> L * norm (y - x)"
    by (rule lipschitz_gradient_on_dist[OF lip x y])

  have L_nonneg: "0 \<le> L"
    using lip
    by (rule lipschitz_gradient_onD_nonneg)

  have norm_nonneg: "0 \<le> norm (y - x)"
    by simp

  have rhs_nonneg: "0 \<le> L * norm (y - x)"
    by (rule mult_nonneg_nonneg[OF L_nonneg norm_nonneg])

  have inner_le_abs:
    "inner (G y - G x) (y - x) \<le> abs (inner (G y - G x) (y - x))"
    by simp

  have abs_le:
    "abs (inner (G y - G x) (y - x))
      \<le> norm (G y - G x) * norm (y - x)"
    by (rule Cauchy_Schwarz_ineq2)

  have norm_prod_le:
    "norm (G y - G x) * norm (y - x)
      \<le> (L * norm (y - x)) * norm (y - x)"
  proof (rule mult_right_mono)
    show "norm (G y - G x) \<le> L * norm (y - x)"
      using lip_bound .
    show "0 \<le> norm (y - x)"
      by simp
  qed

  have "(L * norm (y - x)) * norm (y - x)
      = L * norm (y - x) ^ 2"
    by (simp add: power2_eq_square algebra_simps)

  then show ?thesis
    using inner_le_abs abs_le norm_prod_le by linarith
qed

lemma lipschitz_gradient_on_inner_difference_abs_bound:
  fixes G :: "'a::real_inner \<Rightarrow> 'a"
  assumes lip: "lipschitz_gradient_on L S G"
    and x: "x \<in> S"
    and y: "y \<in> S"
  shows "abs (inner (G y - G x) (y - x)) \<le> L * norm (y - x) ^ 2"
proof -
  have lip_bound: "norm (G y - G x) \<le> L * norm (y - x)"
    by (rule lipschitz_gradient_on_dist[OF lip x y])

  have abs_le:
    "abs (inner (G y - G x) (y - x))
      \<le> norm (G y - G x) * norm (y - x)"
    by (rule Cauchy_Schwarz_ineq2)

  have norm_prod_le:
    "norm (G y - G x) * norm (y - x)
      \<le> (L * norm (y - x)) * norm (y - x)"
  proof (rule mult_right_mono)
    show "norm (G y - G x) \<le> L * norm (y - x)"
      using lip_bound .
    show "0 \<le> norm (y - x)"
      by simp
  qed

  have "(L * norm (y - x)) * norm (y - x)
      = L * norm (y - x) ^ 2"
    by (simp add: power2_eq_square algebra_simps)

  then show ?thesis
    using abs_le norm_prod_le by linarith
qed

lemma lipschitz_gradient_on_segment_dist:
  fixes G :: "'a::real_inner \<Rightarrow> 'a"
  assumes lip: "lipschitz_gradient_on L S G"
    and convex: "convex S"
    and x: "x \<in> S"
    and y: "y \<in> S"
    and t_nonneg: "0 \<le> t"
    and t_le: "t \<le> 1"
  shows
    "norm (G (x + t *\<^sub>R (y - x)) - G x)
      \<le> L * t * norm (y - x)"
proof -
  have z_mem: "x + t *\<^sub>R (y - x) \<in> S"
    by (rule convex_contains_affine_line[
        OF convex x y t_nonneg t_le])

  have lip_bound:
    "norm (G (x + t *\<^sub>R (y - x)) - G x)
      \<le> L * norm ((x + t *\<^sub>R (y - x)) - x)"
    by (rule lipschitz_gradient_on_dist[OF lip x z_mem])

  have diff_eq:
    "(x + t *\<^sub>R (y - x)) - x = t *\<^sub>R (y - x)"
    by simp

  have norm_eq:
    "norm ((x + t *\<^sub>R (y - x)) - x) = t * norm (y - x)"
  proof -
    have "norm ((x + t *\<^sub>R (y - x)) - x) =
        norm (t *\<^sub>R (y - x))"
      by (simp only: diff_eq)
    also have "... = \<bar>t\<bar> * norm (y - x)"
      by simp
    also have "... = t * norm (y - x)"
      using t_nonneg by simp
    finally show ?thesis .
  qed

  have "norm (G (x + t *\<^sub>R (y - x)) - G x)
      \<le> L * (t * norm (y - x))"
    using lip_bound
    by (simp only: norm_eq)

  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma lipschitz_gradient_on_segment_inner_bound:
  fixes G :: "'a::real_inner \<Rightarrow> 'a"
  assumes lip: "lipschitz_gradient_on L S G"
    and convex: "convex S"
    and x: "x \<in> S"
    and y: "y \<in> S"
    and t_nonneg: "0 \<le> t"
    and t_le: "t \<le> 1"
  shows
    "inner (G (x + t *\<^sub>R (y - x)) - G x) (y - x)
      \<le> L * t * norm (y - x) ^ 2"
proof -
  let ?z = "x + t *\<^sub>R (y - x)"

  have z_mem: "?z \<in> S"
    by (rule convex_contains_affine_line[
        OF convex x y t_nonneg t_le])

  have dist:
    "norm (G ?z - G x) \<le> L * t * norm (y - x)"
    by (rule lipschitz_gradient_on_segment_dist[
        OF lip convex x y t_nonneg t_le])

  have inner_le_abs:
    "inner (G ?z - G x) (y - x) \<le> abs (inner (G ?z - G x) (y - x))"
    by simp

  have abs_le:
    "abs (inner (G ?z - G x) (y - x))
      \<le> norm (G ?z - G x) * norm (y - x)"
    by (rule Cauchy_Schwarz_ineq2)

  have prod_le:
    "norm (G ?z - G x) * norm (y - x)
      \<le> (L * t * norm (y - x)) * norm (y - x)"
  proof (rule mult_right_mono)
    show "norm (G ?z - G x) \<le> L * t * norm (y - x)"
      using dist .
    show "0 \<le> norm (y - x)"
      by simp
  qed

  have "(L * t * norm (y - x)) * norm (y - x)
      = L * t * norm (y - x) ^ 2"
    by (simp add: power2_eq_square algebra_simps)

  then show ?thesis
    using inner_le_abs abs_le prod_le by linarith
qed

subsection \<open>A mean-value bridge from Lipschitz gradients\<close>

text \<open>
The following interface records the one-dimensional mean-value identity along
each feasible line segment.  It is intentionally separated from
@{term has_gradient_on}: different developments may prove this certificate from
their preferred differentiability infrastructure.

Together with a Lipschitz gradient, this certificate gives a quadratic
upper-bound with constant 2 * L.  This is not the sharp descent lemma, but it is
already enough to connect primitive Lipschitz-gradient assumptions to the
algorithmic convergence theorems in this entry.
\<close>

definition line_mean_value_gradient_on ::
  "'a::real_inner set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "line_mean_value_gradient_on S f G \<longleftrightarrow>
     (\<forall>x\<in>S. \<forall>y\<in>S.
        \<exists>t. 0 \<le> t \<and> t \<le> 1 \<and>
          f y - f x =
            inner (G (x + t *\<^sub>R (y - x))) (y - x))"

lemma line_mean_value_gradient_onI:
  assumes "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow>
    \<exists>t. 0 \<le> t \<and> t \<le> 1 \<and>
      f y - f x =
        inner (G (x + t *\<^sub>R (y - x))) (y - x)"
  shows "line_mean_value_gradient_on S f G"
  using assms
  unfolding line_mean_value_gradient_on_def
  by auto

lemma line_mean_value_gradient_onD:
  assumes mvt: "line_mean_value_gradient_on S f G"
    and x: "x \<in> S"
    and y: "y \<in> S"
  obtains t where
    "0 \<le> t"
    "t \<le> 1"
    "f y - f x =
      inner (G (x + t *\<^sub>R (y - x))) (y - x)"
  using assms
  unfolding line_mean_value_gradient_on_def
  by blast

lemma line_mean_value_and_lipschitz_gradient_imp_line_descent_bound_on_twice:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes lip: "lipschitz_gradient_on L S G"
    and convex: "convex S"
    and mvt: "line_mean_value_gradient_on S f G"
  shows "line_descent_bound_on (2 * L) S f G"
proof (rule line_descent_bound_onI)
  have L_nonneg: "0 \<le> L"
    using lip
    by (rule lipschitz_gradient_onD_nonneg)

  show "0 \<le> 2 * L"
    using L_nonneg by simp
next
  fix x y
  assume x: "x \<in> S" and y: "y \<in> S"

  let ?d = "y - x"

  obtain t where t_nonneg: "0 \<le> t"
    and t_le: "t \<le> 1"
    and mvt_eq:
      "f y - f x =
        inner (G (x + t *\<^sub>R ?d)) ?d"
    using line_mean_value_gradient_onD[OF mvt x y]
    by blast

  let ?z = "x + t *\<^sub>R ?d"

  have segment_bound:
    "inner (G ?z - G x) ?d \<le> L * t * norm ?d ^ 2"
    by (rule lipschitz_gradient_on_segment_inner_bound[
        OF lip convex x y t_nonneg t_le])

  have inner_diff:
    "inner (G ?z - G x) ?d =
      inner (G ?z) ?d - inner (G x) ?d"
    by (simp add: inner_diff_left)

  have inner_decomp:
    "inner (G ?z) ?d =
      inner (G x) ?d + inner (G ?z - G x) ?d"
    using inner_diff by linarith

  have L_nonneg: "0 \<le> L"
    using lip
    by (rule lipschitz_gradient_onD_nonneg)

  have Lt_le_L: "L * t \<le> L"
  proof -
    have "L * t \<le> L * 1"
      by (rule mult_left_mono[OF t_le L_nonneg])
    then show ?thesis by simp
  qed

  have norm_sq_nonneg: "0 \<le> norm ?d ^ 2"
    by simp

  have product_bound:
    "L * t * norm ?d ^ 2 \<le> L * norm ?d ^ 2"
  proof -
    have "(L * t) * norm ?d ^ 2 \<le> L * norm ?d ^ 2"
      by (rule mult_right_mono[OF Lt_le_L norm_sq_nonneg])
    then show ?thesis
      by simp
  qed

  have inner_bound:
    "inner (G ?z - G x) ?d \<le> L * norm ?d ^ 2"
    using segment_bound product_bound by linarith

  have value_bound:
    "f y - f x \<le> inner (G x) ?d + L * norm ?d ^ 2"
    using mvt_eq inner_decomp inner_bound by linarith

  have coeff_eq:
    "(2 * L / 2) * norm ?d ^ 2 = L * norm ?d ^ 2"
    by simp

  show
    "f y \<le> f x + inner (G x) (y - x) +
      (2 * L / 2) * norm (y - x) ^ 2"
    using value_bound coeff_eq by linarith
qed

lemma line_mean_value_and_lipschitz_gradient_imp_smooth_upper_bound_on_twice:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes lip: "lipschitz_gradient_on L S G"
    and convex: "convex S"
    and mvt: "line_mean_value_gradient_on S f G"
  shows "smooth_upper_bound_on (2 * L) S f G"
proof -
  have line: "line_descent_bound_on (2 * L) S f G"
    by (rule line_mean_value_and_lipschitz_gradient_imp_line_descent_bound_on_twice[
        OF lip convex mvt])
  show ?thesis
    by (rule line_descent_bound_on_imp_smooth_upper_bound_on[OF line])
qed

lemma line_mean_value_and_lipschitz_gradient_imp_lipschitz_smooth_on_twice:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes grad: "has_gradient_on f S G"
    and lip: "lipschitz_gradient_on L S G"
    and convex: "convex S"
    and mvt: "line_mean_value_gradient_on S f G"
  shows "lipschitz_smooth_on (2 * L) S f G"
proof (rule lipschitz_smooth_onI)
  show "has_gradient_on f S G"
    using grad .
next
  have L_nonneg: "0 \<le> L"
    using lip
    by (rule lipschitz_gradient_onD_nonneg)

  have L_le_twice: "L \<le> 2 * L"
    using L_nonneg by linarith

  show "lipschitz_gradient_on (2 * L) S G"
    by (rule lipschitz_gradient_on_mono_L[OF lip L_le_twice])
next
  show "line_descent_bound_on (2 * L) S f G"
    by (rule line_mean_value_and_lipschitz_gradient_imp_line_descent_bound_on_twice[
        OF lip convex mvt])
qed

lemma line_mean_value_and_lipschitz_gradient_imp_lipschitz_smooth_convex_on_twice:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes convex_f: "convex_on S f"
    and grad: "has_gradient_on f S G"
    and lip: "lipschitz_gradient_on L S G"
    and convex: "convex S"
    and mvt: "line_mean_value_gradient_on S f G"
  shows "lipschitz_smooth_convex_on (2 * L) S f G"
proof (rule lipschitz_smooth_convex_onI)
  show "convex_on S f"
    using convex_f .
next
  show "lipschitz_smooth_on (2 * L) S f G"
    by (rule line_mean_value_and_lipschitz_gradient_imp_lipschitz_smooth_on_twice[
        OF grad lip convex mvt])
qed

lemma line_mean_value_and_lipschitz_gradient_imp_smooth_convex_on_twice:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes convex_f: "convex_on S f"
    and grad: "has_gradient_on f S G"
    and lip: "lipschitz_gradient_on L S G"
    and convex: "convex S"
    and mvt: "line_mean_value_gradient_on S f G"
  shows "smooth_convex_on (2 * L) S f G"
proof -
  have lsc: "lipschitz_smooth_convex_on (2 * L) S f G"
    by (rule line_mean_value_and_lipschitz_gradient_imp_lipschitz_smooth_convex_on_twice[
        OF convex_f grad lip convex mvt])
  show ?thesis
    by (rule lipschitz_smooth_convex_on_imp_smooth_convex_on[OF lsc])
qed


subsection \<open>Algorithmic consequences through smoothness\<close>

lemma lipschitz_smooth_convex_gradient_step_decrease:
  assumes lsc: "lipschitz_smooth_convex_on L S f G"
    and x: "x \<in> S"
    and step: "gradient_step alpha G x \<in> S"
    and alpha_nonneg: "0 \<le> alpha"
    and step_size: "alpha * L \<le> 1"
  shows
    "f (gradient_step alpha G x)
      \<le> f x - (alpha / 2) * norm (G x) ^ 2"
proof -
  have smooth: "smooth_upper_bound_on L S f G"
    by (rule lipschitz_smooth_convex_onD_smooth_upper_bound[OF lsc])

  show ?thesis
    by (rule smooth_upper_bound_gradient_step_decrease[
        OF smooth x step alpha_nonneg step_size])
qed

lemma lipschitz_smooth_convex_gradient_descent_objective_nonincreasing:
  assumes lsc: "lipschitz_smooth_convex_on L S f G"
    and gd: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
    and alpha_nonneg: "0 \<le> alpha"
    and step_size: "alpha * L \<le> 1"
  shows "nonincreasing_sequence (objective_values f x)"
proof -
  have smooth: "smooth_upper_bound_on L S f G"
    by (rule lipschitz_smooth_convex_onD_smooth_upper_bound[OF lsc])

  show ?thesis
    by (rule gradient_descent_objective_nonincreasing[
        OF smooth gd feasible alpha_nonneg step_size])
qed

lemma lipschitz_smooth_convex_gradient_descent_function_value_gap_bound:
  fixes f :: "'a::real_inner \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes lsc: "lipschitz_smooth_convex_on L S f G"
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
  have smooth_convex: "smooth_convex_on L S f G"
    by (rule lipschitz_smooth_convex_on_imp_smooth_convex_on[
        OF lsc])

  show ?thesis
    by (rule gradient_descent_function_value_gap_bound[
        OF smooth_convex gd feasible alpha_pos step_size minimizer N_pos])
qed

lemma lipschitz_smooth_convex_projected_gradient_descent_function_value_gap_bound:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes lsc: "lipschitz_smooth_convex_on L C f G"
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
  have smooth_convex: "smooth_convex_on L C f G"
    by (rule lipschitz_smooth_convex_on_imp_smooth_convex_on[
        OF lsc])

  show ?thesis
    by (rule projected_gradient_descent_function_value_gap_bound[
        OF smooth_convex closed convex pgd x0_mem alpha_pos step_size
           minimizer N_pos])
qed

lemma line_mean_value_lipschitz_projected_gradient_descent_function_value_gap_bound:
  fixes f :: "'a::{real_inner,heine_borel} \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes convex_f: "convex_on C f"
    and grad: "has_gradient_on f C G"
    and lip: "lipschitz_gradient_on L C G"
    and closed: "closed C"
    and convex: "convex C"
    and mvt: "line_mean_value_gradient_on C f G"
    and pgd: "projected_gradient_descent_iterates C alpha G x"
    and x0_mem: "x 0 \<in> C"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * (2 * L) \<le> 1"
    and minimizer: "global_min_on C f xstar"
    and N_pos: "N > 0"
  shows
    "f (x N) - f xstar
      \<le> norm (x 0 - xstar) ^ 2 / (2 * alpha * real N)"
proof -
  have lsc: "lipschitz_smooth_convex_on (2 * L) C f G"
    by (rule line_mean_value_and_lipschitz_gradient_imp_lipschitz_smooth_convex_on_twice[
        OF convex_f grad lip convex mvt])

  show ?thesis
    by (rule lipschitz_smooth_convex_projected_gradient_descent_function_value_gap_bound[
        OF lsc closed convex pgd x0_mem alpha_pos step_size minimizer N_pos])
qed


subsection \<open>Locale form\<close>

locale lipschitz_smooth =
  fixes S :: "'a::real_inner set"
    and L :: real
    and f :: "'a \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes gradient_f: "has_gradient_on f S G"
    and lipschitz_G: "lipschitz_gradient_on L S G"
    and line_descent: "line_descent_bound_on L S f G"
begin

lemma lipschitz_smooth_on_self:
  "lipschitz_smooth_on L S f G"
  by (rule lipschitz_smooth_onI[
      OF gradient_f lipschitz_G line_descent])

lemma smooth_upper_bound:
  "smooth_upper_bound_on L S f G"
  by (rule lipschitz_smooth_onD_smooth_upper_bound[
      OF lipschitz_smooth_on_self])

lemma L_nonneg:
  "0 \<le> L"
  using lipschitz_G
  by (rule lipschitz_gradient_onD_nonneg)

lemma line_descent_bound:
  assumes "x \<in> S"
    and "y \<in> S"
  shows "f y \<le> f x + inner (G x) (y - x) + (L / 2) * norm (y - x) ^ 2"
  by (rule line_descent_bound_onD[
      OF line_descent assms])

lemma lipschitz_dist:
  assumes "x \<in> S"
    and "y \<in> S"
  shows "norm (G y - G x) \<le> L * norm (y - x)"
  by (rule lipschitz_gradient_on_dist[
      OF lipschitz_G assms])

lemma inner_difference_bound:
  assumes "x \<in> S"
    and "y \<in> S"
  shows "inner (G y - G x) (y - x) \<le> L * norm (y - x) ^ 2"
  by (rule lipschitz_gradient_on_inner_difference_bound[
      OF lipschitz_G assms])

end

locale lipschitz_smooth_convex =
  lipschitz_smooth S L f G
  for S :: "'a::real_inner set"
    and L :: real
    and f :: "'a \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a" +
  assumes convex_f: "convex_on S f"
begin

lemma lipschitz_smooth_convex_on_self:
  "lipschitz_smooth_convex_on L S f G"
proof (rule lipschitz_smooth_convex_onI)
  show "convex_on S f"
    by (rule convex_f)
next
  show "lipschitz_smooth_on L S f G"
    by (rule lipschitz_smooth_on_self)
qed

lemma smooth_convex_on_self:
  "smooth_convex_on L S f G"
  by (rule lipschitz_smooth_convex_on_imp_smooth_convex_on[
      OF lipschitz_smooth_convex_on_self])

lemma convex_differentiable_on_self:
  "convex_differentiable_on S f G"
  by (rule smooth_convex_onD_convex_differentiable[
      OF smooth_convex_on_self])

lemma gradient_step_decrease:
  assumes "x \<in> S"
    and "gradient_step alpha G x \<in> S"
    and "0 \<le> alpha"
    and "alpha * L \<le> 1"
  shows
    "f (gradient_step alpha G x)
      \<le> f x - (alpha / 2) * norm (G x) ^ 2"
  by (rule lipschitz_smooth_convex_gradient_step_decrease[
      OF lipschitz_smooth_convex_on_self assms])

lemma gradient_descent_function_value_gap_bound:
  assumes gd: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
    and alpha_pos: "0 < alpha"
    and step_size: "alpha * L \<le> 1"
    and minimizer: "global_min_on S f xstar"
    and N_pos: "N > 0"
  shows
    "f (x N) - f xstar
      \<le> norm (x 0 - xstar) ^ 2 / (2 * alpha * real N)"
  by (rule lipschitz_smooth_convex_gradient_descent_function_value_gap_bound[
      OF lipschitz_smooth_convex_on_self gd feasible alpha_pos step_size
         minimizer N_pos])

end


text \<open>
The main bridge theorem for the sharp certificate interface is
@{thm lipschitz_smooth_convex_on_imp_smooth_convex_on}.  It allows any
development stated in terms of @{term smooth_convex_on} to be used with the
more informative @{term lipschitz_smooth_convex_on} interface.

The mean-value bridge
@{thm line_mean_value_and_lipschitz_gradient_imp_smooth_convex_on_twice}
connects primitive Lipschitz-gradient assumptions to the same convergence
framework, with constant 2 * L.  This loses the sharp textbook constant but
avoids committing the algorithmic library to a particular integration
formalization.  A future refinement can recover the sharp constant L by proving
the standard integral descent lemma along line segments.
\<close>

end