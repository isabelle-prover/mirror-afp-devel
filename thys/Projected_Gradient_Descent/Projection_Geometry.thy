theory Projection_Geometry
  imports "HOL-Analysis.Analysis"
begin

section \<open>Projection geometry\<close>

text \<open>
This theory contains the geometric and algebraic projection facts used by
projected first-order methods.  It is independent of any particular objective
function or projected-gradient iteration.
\<close>

subsection \<open>Variational inequality for metric projections\<close>

lemma projection_variational_inequality:
  fixes C :: "'a::{real_inner,heine_borel} set"
  assumes convex: "convex C"
    and closed: "closed C"
    and u_mem: "u \<in> C"
  shows "inner (z - closest_point C z) (u - closest_point C z) \<le> 0"
  by (rule closest_point_dot[OF convex closed u_mem])

subsection \<open>Three-point identity\<close>

lemma three_point_inner_identity:
  fixes x p u :: "'a::real_inner"
  shows "2 * inner (x - p) (p - u) =
    norm (x - u) ^ 2 - norm (p - u) ^ 2 - norm (p - x) ^ 2"
proof -
  have xu_decomp: "x - u = (x - p) + (p - u)"
    by (simp add: algebra_simps)

  have expand:
    "norm ((x - p) + (p - u)) ^ 2 =
      norm (x - p) ^ 2 + 2 * inner (x - p) (p - u) + norm (p - u) ^ 2"
  proof -
    have "norm ((x - p) + (p - u)) ^ 2 =
      inner ((x - p) + (p - u)) ((x - p) + (p - u))"
      by (simp add: power2_norm_eq_inner)
    also have "... =
      inner (x - p) (x - p) +
      2 * inner (x - p) (p - u) +
      inner (p - u) (p - u)"
      by (simp add: inner_commute algebra_simps)
    also have "... =
      norm (x - p) ^ 2 +
      2 * inner (x - p) (p - u) +
      norm (p - u) ^ 2"
      by (simp add: power2_norm_eq_inner)
    finally show ?thesis .
  qed

  have norm_sym: "norm (x - p) ^ 2 = norm (p - x) ^ 2"
    by (simp add: norm_minus_commute)

  have "norm (x - u) ^ 2 =
    norm (x - p) ^ 2 + 2 * inner (x - p) (p - u) + norm (p - u) ^ 2"
    using xu_decomp expand by simp
  hence "norm (x - u) ^ 2 =
    norm (p - x) ^ 2 + 2 * inner (x - p) (p - u) + norm (p - u) ^ 2"
    using norm_sym by simp
  thus ?thesis
    by simp
qed

subsection \<open>Inner-product estimate from a projection inequality\<close>

text \<open>
The following lemma is the algebraic core behind the projected-gradient
one-step estimate.  It only uses a variational inequality and the three-point
identity.
\<close>

lemma projected_gradient_inner_bound_from_vi:
  fixes x p u g :: "'a::real_inner"
  assumes alpha_pos: "0 < alpha"
    and vi: "inner (x - scaleR alpha g - p) (u - p) \<le> 0"
  shows "inner g (p - u) \<le>
    (norm (x - u) ^ 2 - norm (p - u) ^ 2 - norm (p - x) ^ 2) / (2 * alpha)"
proof -
  have vi_rewrite:
    "inner ((x - p) - scaleR alpha g) (u - p) \<le> 0"
    using vi by (simp add: algebra_simps)

  have vi_expanded:
    "inner (x - p) (u - p) - alpha * inner g (u - p) \<le> 0"
    using vi_rewrite by (simp add: inner_diff_left)

  have flipped:
    "alpha * inner g (p - u) \<le> inner (x - p) (p - u)"
  proof -
    have a: "inner (x - p) (u - p) = - inner (x - p) (p - u)"
      by (simp add: inner_diff_right)
    have b: "inner g (u - p) = - inner g (p - u)"
      by (simp add: inner_diff_right)
    have rewritten:
      "- inner (x - p) (p - u) + alpha * inner g (p - u) \<le> 0"
      using vi_expanded by (simp only: a b)
    show ?thesis
      using rewritten by linarith
  qed

  let ?E =
    "norm (x - u) ^ 2 - norm (p - u) ^ 2 - norm (p - x) ^ 2"

  have identity: "inner (x - p) (p - u) = ?E / 2"
    using three_point_inner_identity[of x p u]
    by (simp add: field_simps)

  have multiplied: "alpha * inner g (p - u) \<le> ?E / 2"
    using flipped identity by simp

  have divided: "(alpha * inner g (p - u)) / alpha \<le> (?E / 2) / alpha"
  proof (rule divide_right_mono)
    show "alpha * inner g (p - u) \<le> ?E / 2"
      using multiplied .
    show "0 \<le> alpha"
      using alpha_pos by linarith
  qed

  have "inner g (p - u) \<le> ?E / (2 * alpha)"
    using divided alpha_pos by (simp add: field_simps)
  thus ?thesis .
qed

end