theory Convex_Differentiable
  imports Gradient_Preliminaries
begin

section \<open>Convex differentiable functions and first-order certificates\<close>

text \<open>
This theory introduces the first-order certificate language used later for
gradient descent and projected gradient descent.

The file isolates four basic notions:

  • global minimizers on a feasible set;
  • first-order variational inequalities;
  • supporting affine lower bounds;
  • convex differentiable functions with a named gradient field.

The main result is the standard first-order supporting-hyperplane property:
if f is convex and has gradient g at x, then

  the affine first-order lower bound at x is below f y

for every feasible y.

Consequently, every convex differentiable function with a named gradient field
satisfies a global gradient lower-bound property.  Combined with the
variational first-order condition, this gives a global optimality certificate.
\<close>


subsection \<open>Global minimizers\<close>

definition global_min_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> bool"
where
  "global_min_on S f x \<longleftrightarrow> x \<in> S \<and> (\<forall>y\<in>S. f x \<le> f y)"

lemma global_min_onI:
  assumes "x \<in> S"
    and "\<And>y. y \<in> S \<Longrightarrow> f x \<le> f y"
  shows "global_min_on S f x"
  using assms
  unfolding global_min_on_def
  by auto

lemma global_min_onD_mem:
  assumes "global_min_on S f x"
  shows "x \<in> S"
  using assms
  unfolding global_min_on_def
  by auto

lemma global_min_onD:
  assumes "global_min_on S f x"
    and "y \<in> S"
  shows "f x \<le> f y"
  using assms
  unfolding global_min_on_def
  by auto

lemma global_min_on_singleton [simp]:
  "global_min_on {x} f x"
  unfolding global_min_on_def
  by simp

lemma global_min_on_UNIV_iff:
  "global_min_on UNIV f x \<longleftrightarrow> (\<forall>y. f x \<le> f y)"
  unfolding global_min_on_def
  by simp


subsection \<open>First-order variational inequalities\<close>

text \<open>
For constrained convex minimization, the first-order condition at x with
gradient g is

  the directional inner product inner g (y - x) is nonnegative

for every feasible y.

This is the variational-inequality form of first-order optimality.
\<close>

definition first_order_condition_at ::
  "'a::real_inner set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "first_order_condition_at S g x \<longleftrightarrow>
     x \<in> S \<and> (\<forall>y\<in>S. 0 \<le> inner g (y - x))"

lemma first_order_condition_atI:
  assumes "x \<in> S"
    and "\<And>y. y \<in> S \<Longrightarrow> 0 \<le> inner g (y - x)"
  shows "first_order_condition_at S g x"
  using assms
  unfolding first_order_condition_at_def
  by auto

lemma first_order_condition_atD_mem:
  assumes "first_order_condition_at S g x"
  shows "x \<in> S"
  using assms
  unfolding first_order_condition_at_def
  by auto

lemma first_order_condition_atD:
  assumes "first_order_condition_at S g x"
    and "y \<in> S"
  shows "0 \<le> inner g (y - x)"
  using assms
  unfolding first_order_condition_at_def
  by auto

lemma first_order_condition_zero_iff_mem [simp]:
  "first_order_condition_at S 0 x \<longleftrightarrow> x \<in> S"
  unfolding first_order_condition_at_def
  by simp


subsection \<open>Supporting affine lower bounds\<close>

text \<open>
A vector g supports f at x on S if the corresponding affine first-order
approximation is a global lower bound for f on S.

For differentiable convex functions, g will later be the gradient at x.
\<close>

definition supports_at ::
  "'a::real_inner set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "supports_at S f x g \<longleftrightarrow>
     x \<in> S \<and> (\<forall>y\<in>S. f x + inner g (y - x) \<le> f y)"

definition supports_on ::
  "'a::real_inner set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "supports_on S f G \<longleftrightarrow> (\<forall>x\<in>S. supports_at S f x (G x))"

lemma supports_atI:
  assumes "x \<in> S"
    and "\<And>y. y \<in> S \<Longrightarrow> f x + inner g (y - x) \<le> f y"
  shows "supports_at S f x g"
  using assms
  unfolding supports_at_def
  by auto

lemma supports_atD_mem:
  assumes "supports_at S f x g"
  shows "x \<in> S"
  using assms
  unfolding supports_at_def
  by auto

lemma supports_atD:
  assumes "supports_at S f x g"
    and "y \<in> S"
  shows "f x + inner g (y - x) \<le> f y"
  using assms
  unfolding supports_at_def
  by auto

lemma supports_onI:
  assumes "\<And>x. x \<in> S \<Longrightarrow> supports_at S f x (G x)"
  shows "supports_on S f G"
  using assms
  unfolding supports_on_def
  by auto

lemma supports_onD:
  assumes "supports_on S f G"
    and "x \<in> S"
  shows "supports_at S f x (G x)"
  using assms
  unfolding supports_on_def
  by auto

lemma supports_at_zero_iff_global_min_on:
  "supports_at S f x 0 \<longleftrightarrow> global_min_on S f x"
  unfolding supports_at_def global_min_on_def
  by simp

lemma supports_at_zero_imp_global_min_on:
  assumes "supports_at S f x 0"
  shows "global_min_on S f x"
  using assms
  by (simp add: supports_at_zero_iff_global_min_on)

lemma global_min_on_imp_supports_at_zero:
  assumes "global_min_on S f x"
  shows "supports_at S f x 0"
  using assms
  by (simp add: supports_at_zero_iff_global_min_on)

lemma supports_at_and_first_order_condition_imp_global_min_on:
  assumes supp: "supports_at S f x g"
    and foc: "first_order_condition_at S g x"
  shows "global_min_on S f x"
proof (rule global_min_onI)
  show "x \<in> S"
    using supp
    by (rule supports_atD_mem)
next
  fix y
  assume y: "y \<in> S"

  have "f x \<le> f x + inner g (y - x)"
    using first_order_condition_atD[OF foc y]
    by simp
  also have "... \<le> f y"
    using supports_atD[OF supp y] .
  finally show "f x \<le> f y" .
qed

lemma supports_at_gradient_and_foc_imp_global_min_on:
  assumes supp: "supports_at S f x (gradient f x)"
    and foc: "first_order_condition_at S (gradient f x) x"
  shows "global_min_on S f x"
  using supports_at_and_first_order_condition_imp_global_min_on[OF supp foc] .


subsection \<open>Gradient lower-bound fields\<close>

text \<open>
This is the pointwise supporting-hyperplane property written with a named
gradient field G.

Later, for convex differentiable functions, we will prove this property from
convexity and differentiability.
\<close>

definition gradient_lower_bound_on ::
  "'a::real_inner set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "gradient_lower_bound_on S f G \<longleftrightarrow>
     (\<forall>x\<in>S. \<forall>y\<in>S. f x + inner (G x) (y - x) \<le> f y)"

lemma gradient_lower_bound_onI:
  assumes "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> f x + inner (G x) (y - x) \<le> f y"
  shows "gradient_lower_bound_on S f G"
  using assms
  unfolding gradient_lower_bound_on_def
  by auto

lemma gradient_lower_bound_onD:
  assumes "gradient_lower_bound_on S f G"
    and "x \<in> S"
    and "y \<in> S"
  shows "f x + inner (G x) (y - x) \<le> f y"
  using assms
  unfolding gradient_lower_bound_on_def
  by auto

lemma gradient_lower_bound_on_imp_supports_on:
  assumes "gradient_lower_bound_on S f G"
  shows "supports_on S f G"
proof (rule supports_onI)
  fix x
  assume x: "x \<in> S"
  show "supports_at S f x (G x)"
  proof (rule supports_atI)
    show "x \<in> S"
      using x .
  next
    fix y
    assume y: "y \<in> S"
    show "f x + inner (G x) (y - x) \<le> f y"
      using gradient_lower_bound_onD[OF assms x y] .
  qed
qed

lemma gradient_lower_bound_on_and_foc_imp_global_min_on:
  assumes lb: "gradient_lower_bound_on S f G"
    and foc: "first_order_condition_at S (G x) x"
  shows "global_min_on S f x"
proof -
  have x: "x \<in> S"
    using foc
    by (rule first_order_condition_atD_mem)

  have supp: "supports_at S f x (G x)"
    using gradient_lower_bound_on_imp_supports_on[OF lb] x
    by (rule supports_onD)

  show ?thesis
    using supports_at_and_first_order_condition_imp_global_min_on[OF supp foc] .
qed


subsection \<open>Convexity along feasible segments\<close>

text \<open>
The next lemmas convert the standard convex-combination statement into the
optimization form x + t * (y - x).
\<close>

lemma convex_contains_affine_line:
  fixes x y :: "'a::real_vector"
  assumes "convex S"
    and "x \<in> S"
    and "y \<in> S"
    and "0 \<le> t"
    and "t \<le> 1"
  shows "x + scaleR t (y - x) \<in> S"
proof -
  have combo: "scaleR (1 - t) x + scaleR t y \<in> S"
    using convexD_alt[OF assms(1) assms(2) assms(3) assms(4) assms(5)] .

  have eq: "x + scaleR t (y - x) = scaleR (1 - t) x + scaleR t y"
    by (simp add: algebra_simps)

  show ?thesis
    using combo
    by (simp only: eq)
qed

lemma convex_on_affine_lineD:
  fixes x y :: "'a::real_vector"
  assumes "convex_on S f"
    and "x \<in> S"
    and "y \<in> S"
    and "0 \<le> t"
    and "t \<le> 1"
  shows "f (x + scaleR t (y - x)) \<le> (1 - t) * f x + t * f y"
proof -
  have bound:
    "f (scaleR (1 - t) x + scaleR t y) \<le> (1 - t) * f x + t * f y"
    using convex_onD[OF assms(1) assms(4) assms(5) assms(2) assms(3)] .

  have eq: "x + scaleR t (y - x) = scaleR (1 - t) x + scaleR t y"
    by (simp add: algebra_simps)

  show ?thesis
    using bound
    by (simp only: eq)
qed

lemma convex_on_affine_lineD_open01:
  fixes x y :: "'a::real_vector"
  assumes "convex_on S f"
    and "x \<in> S"
    and "y \<in> S"
    and "0 < t"
    and "t < 1"
  shows "f (x + scaleR t (y - x)) \<le> (1 - t) * f x + t * f y"
  using convex_on_affine_lineD[OF assms(1) assms(2) assms(3)]
  using assms(4) assms(5)
  by simp

subsection \<open>First-order lower bound for convex differentiable functions\<close>

lemma convex_line_secant_slope_bound:
  fixes f :: "'a::real_inner \<Rightarrow> real"
  assumes conv: "convex_on S f"
    and x: "x \<in> S"
    and y: "y \<in> S"
    and tpos: "0 < t"
    and tle: "t \<le> 1"
  shows "(f (x + t *\<^sub>R (y - x)) - f x) / t \<le> f y - f x"
proof -
  have bound:
    "f (x + t *\<^sub>R (y - x)) \<le> (1 - t) * f x + t * f y"
    using convex_on_affine_lineD[OF conv x y] tpos tle
    by simp

  have "f (x + t *\<^sub>R (y - x)) - f x \<le> t * (f y - f x)"
    using bound
    by (simp add: algebra_simps)

  then show ?thesis
    using tpos
    by (simp add: field_simps)
qed

lemma has_gradient_line_slope_tendsto:
  fixes f :: "'a::real_inner \<Rightarrow> real"
  assumes grad: "has_gradient f x g"
  shows "((\<lambda>t::real. (f (x + t *\<^sub>R d) - f x) / t) \<longlongrightarrow> inner d g) (at_right 0)"
proof -
  have D:
    "((\<lambda>t::real. f (x + t *\<^sub>R d)) has_field_derivative inner d g) (at 0)"
    using has_gradient_restrict_to_line_at_0[OF grad, of d] .

  have D_right:
    "((\<lambda>t::real. f (x + t *\<^sub>R d)) has_field_derivative inner d g)
       (at (0::real) within {0<..})"
    using D
    unfolding has_field_derivative_def
    by (rule has_derivative_at_withinI)

  show ?thesis
    using D_right
    unfolding has_field_derivative_iff
    by simp
qed

lemma convex_has_gradient_supports:
  fixes f :: "'a::real_inner \<Rightarrow> real"
  assumes conv: "convex_on S f"
    and grad: "has_gradient f x g"
    and x: "x \<in> S"
    and y: "y \<in> S"
  shows "f x + inner g (y - x) \<le> f y"
proof -
  define d where "d = y - x"

  have lim:
    "((\<lambda>t::real. (f (x + t *\<^sub>R d) - f x) / t) \<longlongrightarrow> inner d g) (at_right 0)"
    using has_gradient_line_slope_tendsto[OF grad, of d] .

  have ev01:
    "eventually (\<lambda>t::real. t \<in> {0<..<1}) (at_right 0)"
    using eventually_at_right_real[OF zero_less_one] .

  have ev:
    "eventually
      (\<lambda>t::real. (f (x + t *\<^sub>R d) - f x) / t \<le> f y - f x)
      (at_right 0)"
    using ev01
  proof eventually_elim
    fix t :: real
    assume t: "t \<in> {0<..<1}"
    then have tpos: "0 < t"
      by auto
    from t have tle: "t \<le> 1"
      by auto

    show "(f (x + t *\<^sub>R d) - f x) / t \<le> f y - f x"
      unfolding d_def
      using convex_line_secant_slope_bound[OF conv x y tpos tle] .
  qed

  have nontriv: "\<not> trivial_limit (at_right (0::real))"
    by simp

  have "f y - f x \<ge> inner d g"
    using tendsto_upperbound[OF lim ev nontriv] .

  then show ?thesis
    unfolding d_def
    by (simp add: inner_commute algebra_simps)
qed

subsection \<open>Convex differentiable functions with a named gradient field\<close>

definition convex_differentiable_on ::
  "'a::real_inner set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "convex_differentiable_on S f G \<longleftrightarrow>
     convex_on S f \<and> has_gradient_on f S G"

lemma convex_differentiable_onI:
  assumes "convex_on S f"
    and "has_gradient_on f S G"
  shows "convex_differentiable_on S f G"
  using assms
  unfolding convex_differentiable_on_def
  by auto

lemma convex_differentiable_onD_convex_on:
  assumes "convex_differentiable_on S f G"
  shows "convex_on S f"
  using assms
  unfolding convex_differentiable_on_def
  by auto

lemma convex_differentiable_onD_has_gradient_on:
  assumes "convex_differentiable_on S f G"
  shows "has_gradient_on f S G"
  using assms
  unfolding convex_differentiable_on_def
  by auto

lemma convex_differentiable_on_convex:
  assumes "convex_differentiable_on S f G"
  shows "convex S"
  using assms convex_on_imp_convex
  unfolding convex_differentiable_on_def
  by blast

lemma convex_differentiable_on_gradientD:
  assumes "convex_differentiable_on S f G"
    and "x \<in> S"
  shows "has_gradient f x (G x)"
  using convex_differentiable_onD_has_gradient_on[OF assms(1)] assms(2)
  by (rule has_gradient_onD)

lemma convex_differentiable_on_differentiable:
  assumes "convex_differentiable_on S f G"
    and "x \<in> S"
  shows "f differentiable (at x)"
  using convex_differentiable_on_gradientD[OF assms]
  by (rule has_gradient_imp_differentiable)

lemma has_gradient_on_subset:
  assumes "has_gradient_on f T G"
    and "S \<subseteq> T"
  shows "has_gradient_on f S G"
  using assms
  unfolding has_gradient_on_def
  by auto

lemma convex_differentiable_on_subset:
  assumes "convex_differentiable_on T f G"
    and "S \<subseteq> T"
    and "convex S"
  shows "convex_differentiable_on S f G"
proof (rule convex_differentiable_onI)
  show "convex_on S f"
    using convex_differentiable_onD_convex_on[OF assms(1)] assms(2) assms(3)
    by (rule convex_on_subset)

  show "has_gradient_on f S G"
    using convex_differentiable_onD_has_gradient_on[OF assms(1)] assms(2)
    by (rule has_gradient_on_subset)
qed

lemma convex_differentiable_on_imp_gradient_lower_bound_on:
  assumes cd: "convex_differentiable_on S f G"
  shows "gradient_lower_bound_on S f G"
proof (rule gradient_lower_bound_onI)
  fix x y
  assume x: "x \<in> S"
    and y: "y \<in> S"

  have conv: "convex_on S f"
    using cd
    by (rule convex_differentiable_onD_convex_on)

  have grad: "has_gradient f x (G x)"
    using cd x
    by (rule convex_differentiable_on_gradientD)

  show "f x + inner (G x) (y - x) \<le> f y"
    using convex_has_gradient_supports[OF conv grad x y] .
qed

lemma convex_differentiable_on_imp_supports_on:
  assumes cd: "convex_differentiable_on S f G"
  shows "supports_on S f G"
  using gradient_lower_bound_on_imp_supports_on[
      OF convex_differentiable_on_imp_gradient_lower_bound_on[OF cd]] .

lemma convex_differentiable_on_supports_at:
  assumes cd: "convex_differentiable_on S f G"
    and x: "x \<in> S"
  shows "supports_at S f x (G x)"
  using convex_differentiable_on_imp_supports_on[OF cd] x
  by (rule supports_onD)

lemma convex_differentiable_on_foc_imp_global_min_on:
  assumes cd: "convex_differentiable_on S f G"
    and foc: "first_order_condition_at S (G x) x"
  shows "global_min_on S f x"
  using gradient_lower_bound_on_and_foc_imp_global_min_on[
      OF convex_differentiable_on_imp_gradient_lower_bound_on[OF cd] foc] .

subsection \<open>Main first-order consequences\<close>

theorem convex_differentiable_on_supporting_hyperplanes:
  assumes cd: "convex_differentiable_on S f G"
  shows "supports_on S f G"
  using convex_differentiable_on_imp_supports_on[OF cd] .

theorem convex_differentiable_on_first_order_sufficient:
  assumes cd: "convex_differentiable_on S f G"
    and foc: "first_order_condition_at S (G x) x"
  shows "global_min_on S f x"
  using convex_differentiable_on_foc_imp_global_min_on[OF cd foc] .

subsection \<open>Locale form\<close>

locale convex_differentiable =
  fixes S :: "'a::real_inner set"
    and f :: "'a \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
  assumes convex_f: "convex_on S f"
    and gradient_f: "has_gradient_on f S G"
begin

lemma convex_set:
  "convex S"
  using convex_f
  by (rule convex_on_imp_convex)

lemma has_gradient:
  assumes "x \<in> S"
  shows "has_gradient f x (G x)"
  using gradient_f assms
  by (rule has_gradient_onD)

lemma differentiable:
  assumes "x \<in> S"
  shows "f differentiable (at x)"
  using has_gradient[OF assms]
  by (rule has_gradient_imp_differentiable)

lemma segment_mem:
  assumes "x \<in> S"
    and "y \<in> S"
    and "0 \<le> t"
    and "t \<le> 1"
  shows "x + scaleR t (y - x) \<in> S"
  using convex_contains_affine_line[OF convex_set assms] .

lemma convex_bound_on_segment:
  assumes "x \<in> S"
    and "y \<in> S"
    and "0 \<le> t"
    and "t \<le> 1"
  shows "f (x + scaleR t (y - x)) \<le> (1 - t) * f x + t * f y"
  using convex_on_affine_lineD[OF convex_f assms] .

lemma gradient_lower_bound:
  "gradient_lower_bound_on S f G"
proof (rule gradient_lower_bound_onI)
  fix x y
  assume x: "x \<in> S"
    and y: "y \<in> S"

  show "f x + inner (G x) (y - x) \<le> f y"
    using convex_has_gradient_supports[OF convex_f has_gradient[OF x] x y] .
qed

lemma supports:
  assumes "x \<in> S"
  shows "supports_at S f x (G x)"
  using gradient_lower_bound_on_imp_supports_on[OF gradient_lower_bound] assms
  by (rule supports_onD)

lemma foc_imp_global_min:
  assumes "first_order_condition_at S (G x) x"
  shows "global_min_on S f x"
  using gradient_lower_bound_on_and_foc_imp_global_min_on[
      OF gradient_lower_bound assms] .

end

text \<open>
This completes the first-order convex certificate layer.

The main bridge theorem is @{thm convex_has_gradient_supports}: for a convex
function that has a gradient at x, the gradient defines a supporting affine
lower bound on the feasible set.  The bundled consequence
@{thm convex_differentiable_on_first_order_sufficient} gives the usual
first-order sufficient condition for global optimality in convex optimization.

Later theories use these results as the first-order part of the analysis of
smooth gradient descent and projected gradient descent.
\<close>

end