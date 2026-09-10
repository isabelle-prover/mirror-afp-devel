theory Smooth_Convex
  imports Convex_Differentiable
begin

section \<open>Smooth convex functions and quadratic upper bounds\<close>

text \<open>
This theory introduces the smoothness layer used later for gradient descent
and projected gradient descent.

The central interface is the quadratic upper-bound property
@{text \<open>f y <= f x + inner (G x) (y - x) + (L / 2) * norm (y - x) ^ 2\<close>}.
This is the standard descent-lemma form of L-smoothness.  For the purposes
of the algorithmic development, it is useful to package this property directly
as a reusable assumption.  A later file can derive it from more primitive
Lipschitz-gradient assumptions if needed.
\<close>


subsection \<open>Lipschitz gradient fields\<close>

definition lipschitz_gradient_on ::
  "real \<Rightarrow> 'a::real_normed_vector set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "lipschitz_gradient_on L S G \<longleftrightarrow>
     0 \<le> L \<and> (\<forall>x\<in>S. \<forall>y\<in>S. norm (G x - G y) \<le> L * norm (x - y))"

lemma lipschitz_gradient_onI:
  assumes "0 \<le> L"
    and "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow>
      norm (G x - G y) \<le> L * norm (x - y)"
  shows "lipschitz_gradient_on L S G"
  using assms
  unfolding lipschitz_gradient_on_def
  by auto

lemma lipschitz_gradient_onD_nonneg:
  assumes "lipschitz_gradient_on L S G"
  shows "0 \<le> L"
  using assms
  unfolding lipschitz_gradient_on_def
  by auto

lemma lipschitz_gradient_onD:
  assumes "lipschitz_gradient_on L S G"
    and "x \<in> S"
    and "y \<in> S"
  shows "norm (G x - G y) \<le> L * norm (x - y)"
  using assms
  unfolding lipschitz_gradient_on_def
  by auto

lemma lipschitz_gradient_on_subset:
  assumes lip: "lipschitz_gradient_on L T G"
    and subset: "S \<subseteq> T"
  shows "lipschitz_gradient_on L S G"
proof (rule lipschitz_gradient_onI)
  show "0 \<le> L"
    using lip
    by (rule lipschitz_gradient_onD_nonneg)
next
  fix x y
  assume xS: "x \<in> S" and yS: "y \<in> S"

  have xT: "x \<in> T"
    using subset xS
    by auto

  have yT: "y \<in> T"
    using subset yS
    by auto

  show "norm (G x - G y) \<le> L * norm (x - y)"
    by (rule lipschitz_gradient_onD[OF lip xT yT])
qed

lemma lipschitz_gradient_on_mono_L:
  assumes lip: "lipschitz_gradient_on L S G"
    and LM: "L \<le> M"
  shows "lipschitz_gradient_on M S G"
proof (rule lipschitz_gradient_onI)
  show "0 \<le> M"
    using lipschitz_gradient_onD_nonneg[OF lip] LM
    by simp
next
  fix x y
  assume x: "x \<in> S" and y: "y \<in> S"

  have bound: "norm (G x - G y) \<le> L * norm (x - y)"
    using lipschitz_gradient_onD[OF lip x y] .

  have mono: "L * norm (x - y) \<le> M * norm (x - y)"
    using LM
    by (intro mult_right_mono) simp_all

  show "norm (G x - G y) \<le> M * norm (x - y)"
    using bound mono
    by linarith
qed


subsection \<open>Quadratic upper bounds\<close>

definition smooth_upper_bound_on ::
  "real \<Rightarrow> 'a::real_inner set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "smooth_upper_bound_on L S f G \<longleftrightarrow>
     0 \<le> L \<and>
     (\<forall>x\<in>S. \<forall>y\<in>S.
        f y \<le> f x + inner (G x) (y - x) + (L / 2) * norm (y - x) ^ 2)"

lemma smooth_upper_bound_onI:
  assumes "0 \<le> L"
    and "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow>
      f y \<le> f x + inner (G x) (y - x) + (L / 2) * norm (y - x) ^ 2"
  shows "smooth_upper_bound_on L S f G"
  using assms
  unfolding smooth_upper_bound_on_def
  by auto

lemma smooth_upper_bound_onD_nonneg:
  assumes "smooth_upper_bound_on L S f G"
  shows "0 \<le> L"
  using assms
  unfolding smooth_upper_bound_on_def
  by auto

lemma smooth_upper_bound_onD:
  assumes "smooth_upper_bound_on L S f G"
    and "x \<in> S"
    and "y \<in> S"
  shows "f y \<le> f x + inner (G x) (y - x) + (L / 2) * norm (y - x) ^ 2"
  using assms
  unfolding smooth_upper_bound_on_def
  by auto

lemma smooth_upper_bound_on_subset:
  assumes smooth: "smooth_upper_bound_on L T f G"
    and subset: "S \<subseteq> T"
  shows "smooth_upper_bound_on L S f G"
proof (rule smooth_upper_bound_onI)
  show "0 \<le> L"
    using smooth
    by (rule smooth_upper_bound_onD_nonneg)
next
  fix x y
  assume xS: "x \<in> S" and yS: "y \<in> S"

  have xT: "x \<in> T"
    using subset xS
    by auto

  have yT: "y \<in> T"
    using subset yS
    by auto

  show "f y \<le> f x + inner (G x) (y - x) + (L / 2) * norm (y - x) ^ 2"
    by (rule smooth_upper_bound_onD[OF smooth xT yT])
qed

lemma smooth_upper_bound_on_mono_L:
  assumes smooth: "smooth_upper_bound_on L S f G"
    and LM: "L \<le> M"
  shows "smooth_upper_bound_on M S f G"
proof (rule smooth_upper_bound_onI)
  show "0 \<le> M"
    using smooth_upper_bound_onD_nonneg[OF smooth] LM
    by simp
next
  fix x y
  assume x: "x \<in> S" and y: "y \<in> S"

  have base:
    "f y \<le> f x + inner (G x) (y - x) + (L / 2) * norm (y - x) ^ 2"
    using smooth_upper_bound_onD[OF smooth x y] .

  have mono:
    "(L / 2) * norm (y - x) ^ 2 \<le> (M / 2) * norm (y - x) ^ 2"
    using LM
    by (intro mult_right_mono) simp_all

  show "f y \<le> f x + inner (G x) (y - x) + (M / 2) * norm (y - x) ^ 2"
    using base mono
    by linarith
qed


subsection \<open>Smooth convex functions\<close>

definition smooth_convex_on ::
  "real \<Rightarrow> 'a::real_inner set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "smooth_convex_on L S f G \<longleftrightarrow>
     convex_differentiable_on S f G \<and> smooth_upper_bound_on L S f G"

lemma smooth_convex_onI:
  assumes "convex_differentiable_on S f G"
    and "smooth_upper_bound_on L S f G"
  shows "smooth_convex_on L S f G"
  using assms
  unfolding smooth_convex_on_def
  by auto

lemma smooth_convex_onD_convex_differentiable:
  assumes "smooth_convex_on L S f G"
  shows "convex_differentiable_on S f G"
  using assms
  unfolding smooth_convex_on_def
  by auto

lemma smooth_convex_onD_smooth_upper_bound:
  assumes "smooth_convex_on L S f G"
  shows "smooth_upper_bound_on L S f G"
  using assms
  unfolding smooth_convex_on_def
  by auto

lemma smooth_convex_onD_convex_on:
  assumes "smooth_convex_on L S f G"
  shows "convex_on S f"
  using smooth_convex_onD_convex_differentiable[OF assms]
  by (rule convex_differentiable_onD_convex_on)

lemma smooth_convex_onD_has_gradient_on:
  assumes "smooth_convex_on L S f G"
  shows "has_gradient_on f S G"
  using smooth_convex_onD_convex_differentiable[OF assms]
  by (rule convex_differentiable_onD_has_gradient_on)

lemma smooth_convex_onD_smooth_nonneg:
  assumes "smooth_convex_on L S f G"
  shows "0 \<le> L"
  using smooth_convex_onD_smooth_upper_bound[OF assms]
  by (rule smooth_upper_bound_onD_nonneg)

lemma smooth_convex_on_subset:
  assumes smooth: "smooth_convex_on L T f G"
    and subset: "S \<subseteq> T"
    and convex: "convex S"
  shows "smooth_convex_on L S f G"
proof (rule smooth_convex_onI)
  show "convex_differentiable_on S f G"
    using convex_differentiable_on_subset[
      OF smooth_convex_onD_convex_differentiable[OF smooth] subset convex] .
next
  show "smooth_upper_bound_on L S f G"
    using smooth_upper_bound_on_subset[
      OF smooth_convex_onD_smooth_upper_bound[OF smooth] subset] .
qed


subsection \<open>Gradient steps\<close>

definition gradient_step ::
  "real \<Rightarrow> ('a::real_vector \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "gradient_step alpha G x = x - scaleR alpha (G x)"

lemma gradient_step_zero_stepsize [simp]:
  "gradient_step 0 G x = x"
  unfolding gradient_step_def
  by simp

lemma gradient_step_zero_gradient [simp]:
  assumes "G x = 0"
  shows "gradient_step alpha G x = x"
  using assms
  unfolding gradient_step_def
  by simp

lemma gradient_step_diff:
  "gradient_step alpha G x - x = - scaleR alpha (G x)"
  unfolding gradient_step_def
  by simp

lemma gradient_step_inner:
  fixes G :: "'a::real_inner \<Rightarrow> 'a"
  shows "inner (G x) (gradient_step alpha G x - x) =
    - alpha * norm (G x) ^ 2"
  unfolding gradient_step_def
  by (simp add: power2_norm_eq_inner)

lemma gradient_step_norm_sq:
  fixes G :: "'a::real_inner \<Rightarrow> 'a"
  shows "norm (gradient_step alpha G x - x) ^ 2 =
    alpha ^ 2 * norm (G x) ^ 2"
proof -
  have norm_eq:
    "norm (gradient_step alpha G x - x) = abs alpha * norm (G x)"
    unfolding gradient_step_def
    by simp

  show ?thesis
    using norm_eq
    by (simp add: power_mult_distrib)
qed

subsection \<open>One-step descent from the smooth upper bound\<close>

lemma smooth_upper_bound_gradient_step:
  assumes smooth: "smooth_upper_bound_on L S f G"
    and x: "x \<in> S"
    and step: "gradient_step alpha G x \<in> S"
  shows
    "f (gradient_step alpha G x)
      \<le> f x - alpha * norm (G x) ^ 2
          + (L / 2) * alpha ^ 2 * norm (G x) ^ 2"
proof -
  let ?z = "gradient_step alpha G x"
  let ?n = "norm (G x) ^ 2"

  have bound:
    "f ?z \<le> f x + inner (G x) (?z - x) + (L / 2) * norm (?z - x) ^ 2"
    using smooth_upper_bound_onD[OF smooth x step] .

  have inner_eq:
    "inner (G x) (?z - x) = - alpha * ?n"
    by (rule gradient_step_inner)

  have norm_eq:
    "norm (?z - x) ^ 2 = alpha ^ 2 * ?n"
    by (rule gradient_step_norm_sq)

  have "f ?z \<le> f x + (- alpha * ?n) + (L / 2) * (alpha ^ 2 * ?n)"
    using bound
    by (simp only: inner_eq norm_eq)

  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma descent_coefficient_bound:
  fixes alpha L :: real
  assumes alpha_nonneg: "0 \<le> alpha"
    and step_size: "alpha * L \<le> 1"
  shows "- alpha + (L / 2) * alpha ^ 2 \<le> - alpha / 2"
proof (cases "alpha = 0")
  case True
  then show ?thesis
    by simp
next
  case False

  have alpha_pos: "0 < alpha"
    using alpha_nonneg False
    by linarith

  have L_alpha_le_one: "L * alpha \<le> 1"
    using step_size
    by (simp add: mult.commute)

  have L_alpha_sq_le_alpha: "L * alpha ^ 2 \<le> alpha"
  proof -
    have "L * alpha ^ 2 = alpha * (L * alpha)"
      by (simp add: algebra_simps power2_eq_square)
    also have "... \<le> alpha * 1"
      using L_alpha_le_one alpha_nonneg
      by (rule mult_left_mono)
    also have "... = alpha"
      by simp
    finally show ?thesis .
  qed

  show ?thesis
    using L_alpha_sq_le_alpha
    by linarith
qed

lemma smooth_upper_bound_gradient_step_decrease:
  assumes smooth: "smooth_upper_bound_on L S f G"
    and x: "x \<in> S"
    and step: "gradient_step alpha G x \<in> S"
    and alpha_nonneg: "0 \<le> alpha"
    and step_size: "alpha * L \<le> 1"
  shows
    "f (gradient_step alpha G x)
      \<le> f x - (alpha / 2) * norm (G x) ^ 2"
proof -
  let ?n = "norm (G x) ^ 2"

  have step_bound:
    "f (gradient_step alpha G x)
      \<le> f x + (- alpha + (L / 2) * alpha ^ 2) * ?n"
    using smooth_upper_bound_gradient_step[OF smooth x step]
    by (simp add: algebra_simps)

  have coeff:
    "- alpha + (L / 2) * alpha ^ 2 \<le> - alpha / 2"
    using descent_coefficient_bound[OF alpha_nonneg step_size] .

  have mono:
    "(- alpha + (L / 2) * alpha ^ 2) * ?n \<le> (- alpha / 2) * ?n"
    using coeff
    by (intro mult_right_mono) simp_all

  have "f (gradient_step alpha G x) \<le> f x + (- alpha / 2) * ?n"
    using step_bound mono
    by linarith

  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma smooth_upper_bound_gradient_step_decrease_inverse_L:
  assumes smooth: "smooth_upper_bound_on L S f G"
    and Lpos: "0 < L"
    and x: "x \<in> S"
    and step: "gradient_step (inverse L) G x \<in> S"
  shows
    "f (gradient_step (inverse L) G x)
      \<le> f x - (1 / (2 * L)) * norm (G x) ^ 2"
proof -
  have alpha_nonneg: "0 \<le> inverse L"
    using Lpos
    by simp

  have step_size: "inverse L * L \<le> 1"
    using Lpos
    by simp

  have decrease:
    "f (gradient_step (inverse L) G x)
      \<le> f x - (inverse L / 2) * norm (G x) ^ 2"
    using smooth_upper_bound_gradient_step_decrease[
      OF smooth x step alpha_nonneg step_size] .

  then show ?thesis
    using Lpos
    by (simp add: field_simps)
qed


subsection \<open>Locale form\<close>

locale smooth_convex =
  convex_differentiable S f G
  for S :: "'a::real_inner set"
    and f :: "'a \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a" +
  fixes L :: real
  assumes smooth_bound: "smooth_upper_bound_on L S f G"
begin

lemma smooth_nonneg:
  "0 \<le> L"
  using smooth_bound
  by (rule smooth_upper_bound_onD_nonneg)

lemma smooth_upper_bound:
  assumes "x \<in> S"
    and "y \<in> S"
  shows "f y \<le> f x + inner (G x) (y - x) + (L / 2) * norm (y - x) ^ 2"
  using smooth_upper_bound_onD[OF smooth_bound assms] .

lemma gradient_step_bound:
  assumes "x \<in> S"
    and "gradient_step alpha G x \<in> S"
  shows
    "f (gradient_step alpha G x)
      \<le> f x - alpha * norm (G x) ^ 2
          + (L / 2) * alpha ^ 2 * norm (G x) ^ 2"
  using smooth_upper_bound_gradient_step[OF smooth_bound assms] .

lemma gradient_step_decrease:
  assumes "x \<in> S"
    and "gradient_step alpha G x \<in> S"
    and "0 \<le> alpha"
    and "alpha * L \<le> 1"
  shows
    "f (gradient_step alpha G x)
      \<le> f x - (alpha / 2) * norm (G x) ^ 2"
  using smooth_upper_bound_gradient_step_decrease[OF smooth_bound assms] .

lemma gradient_step_decrease_inverse_L:
  assumes "0 < L"
    and "x \<in> S"
    and "gradient_step (inverse L) G x \<in> S"
  shows
    "f (gradient_step (inverse L) G x)
      \<le> f x - (1 / (2 * L)) * norm (G x) ^ 2"
  using smooth_upper_bound_gradient_step_decrease_inverse_L[
    OF smooth_bound assms] .

end

text \<open>
This file packages the smooth quadratic upper-bound interface and derives the
basic one-step decrease estimate for gradient steps.

The next theory can use these lemmas to prove descent and convergence
properties for gradient descent sequences.  For constrained problems, the same
upper-bound interface will combine with projection variational inequalities.
\<close>

end