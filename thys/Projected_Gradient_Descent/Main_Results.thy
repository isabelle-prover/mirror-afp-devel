theory Main_Results
  imports
    Lipschitz_Smoothness
    Examples_Projected_Quadratic
begin

section \<open>Main reusable theorem interface\<close>

text \<open>
This theory is the recommended public import target of the entry.

It collects the main reusable theorem groups for smooth convex first-order
optimization, while hiding the internal proof structure of the individual
theory files.  Downstream developments should normally import this theory
instead of importing the lower-level proof files directly.

The entry is organized as a small library layer for smooth convex first-order
optimization.  The main reusable components are:

  1. gradient and convex first-order interfaces;
  2. smooth upper-bound and descent interfaces;
  3. abstract telescoping lemmas for convergence proofs;
  4. gradient descent and projected-gradient descent convergence theorems;
  5. projection geometry and projected-gradient step rules;
  6. projected-gradient mapping optimality and residual certificates;
  7. strong-convexity and linear-rate results;
  8. concrete quadratic examples.

The theorem groups below are organized from low-level analytic interfaces to
high-level convergence and residual-complexity statements.  The final section
collects the recommended citation surface of the entry.
\<close>


subsection \<open>Gradient interfaces\<close>

text \<open>
These theorem groups provide the basic gradient-like interface used throughout
the entry.  The pointwise rules introduce and eliminate gradient facts at a
single point, while the set-based rules are used to work on feasible regions.
The algebraic rules are useful for instantiating the framework on concrete
objectives.
\<close>

lemmas gradient_pointwise_interface =
  has_gradientI
  has_gradientD
  has_gradient_unique
  gradient_eqI
  has_gradient_gradient

lemmas gradient_field_interface =
  has_gradient_onD
  has_gradient_within_onD
  has_gradient_on_subset

lemmas gradient_rule_interface =
  has_gradient_const
  has_gradient_add
  has_gradient_minus
  has_gradient_diff
  has_gradient_scale_const
  has_gradient_mult
  has_gradient_inner_left
  has_gradient_inner_right


subsection \<open>Convex first-order certificates\<close>

text \<open>
These facts connect convexity, gradients, and first-order optimality.  They are
the main bridge between an analytic certificate, such as a variational
inequality, and global optimality for a convex objective.
\<close>

lemmas global_min_interface =
  global_min_onI
  global_min_onD_mem
  global_min_onD

lemmas first_order_condition_interface =
  first_order_condition_atI
  first_order_condition_atD_mem
  first_order_condition_atD

lemmas convex_first_order_results =
  convex_has_gradient_supports
  convex_differentiable_on_imp_gradient_lower_bound_on
  convex_differentiable_on_supporting_hyperplanes
  convex_differentiable_on_first_order_sufficient


subsection \<open>Smooth convex interfaces and descent lemmas\<close>

text \<open>
The convergence proofs are parameterized by a quadratic smooth upper-bound
certificate.  This isolates the algorithmic descent argument from the analytic
source of smoothness.  Later theories can instantiate this certificate from
Lipschitz-gradient assumptions, line-descent bounds, or concrete examples.
\<close>

lemmas smooth_upper_bound_interface =
  smooth_upper_bound_onI
  smooth_upper_bound_onD_nonneg
  smooth_upper_bound_onD
  smooth_upper_bound_on_subset
  smooth_upper_bound_on_mono_L

lemmas smooth_convex_interface =
  smooth_convex_onI
  smooth_convex_onD_convex_differentiable
  smooth_convex_onD_smooth_upper_bound
  smooth_convex_onD_convex_on
  smooth_convex_onD_has_gradient_on
  smooth_convex_on_subset

lemmas gradient_step_interface =
  gradient_step_diff
  gradient_step_inner
  gradient_step_norm_sq

lemmas gradient_step_descent_results =
  smooth_upper_bound_gradient_step
  smooth_upper_bound_gradient_step_decrease
  smooth_upper_bound_gradient_step_decrease_inverse_L


subsection \<open>Abstract descent and telescoping\<close>

text \<open>
These lemmas are independent of gradients and projections.  They package the
finite-sum and averaging arguments used by the convergence proofs.  They are
intended to be reusable for other first-order algorithms with one-step progress
estimates.
\<close>

lemmas abstract_descent_results =
  sum_progress_le_initial_gap
  sum_progress_le_initial_minus_lower_bound
  exists_le_average_of_sum_bound
  exists_le_average_of_nonnegative_sum
  sequence_linear_rate_from_step


subsection \<open>Gradient descent\<close>

text \<open>
The following groups expose the unconstrained gradient-descent layer.  They
include the iteration predicate, one-step descent estimates, gradient-residual
rate bounds, and the standard O(1/N) function-value convergence theorem.
\<close>

lemmas gradient_descent_iteration_interface =
  gradient_descent_iteratesI
  gradient_descent_iteratesD
  gradient_descent_iteratesE
  feasible_iteratesI
  feasible_iteratesD
  feasible_iterates_subset

lemmas gradient_descent_one_step_results =
  gradient_descent_one_step_bound
  gradient_descent_one_step_decrease
  gradient_descent_objective_mono_step
  gradient_descent_objective_nonincreasing
  gradient_descent_step_progress

lemmas gradient_descent_rate_results =
  gradient_descent_sum_weighted_gradient_norm_sq_bound
  gradient_descent_sum_gradient_norm_sq_bound
  gradient_descent_average_gradient_norm_sq_bound
  gradient_descent_exists_small_gradient_norm_sq
  gradient_descent_exists_small_weighted_gradient_norm_sq

lemmas gradient_descent_convergence_results =
  gradient_descent_one_step_distance_bound_to_point
  gradient_descent_one_step_distance_bound_to_minimizer
  gradient_descent_sum_function_value_gaps_bound_to_point
  gradient_descent_sum_function_value_gaps_bound_to_minimizer
  gradient_descent_last_gap_times_N_bound
  gradient_descent_function_value_gap_bound


subsection \<open>Projection geometry\<close>

text \<open>
This group provides the metric-projection geometry used by the projected
method.  The variational inequality for closest points is the central geometric
input for projected-gradient descent.
\<close>

lemmas projection_geometry_results =
  projection_variational_inequality
  three_point_inner_identity
  projected_gradient_inner_bound_from_vi


subsection \<open>Projected gradient steps\<close>

text \<open>
These rules describe a single projected-gradient step.  They expose feasibility
of the projected point, the projection variational inequality, and the one-step
distance estimates used in the convergence proof.
\<close>

lemmas projected_gradient_step_interface =
  projected_gradient_step_in_set
  projected_gradient_step_in_set_if_base_mem
  projected_gradient_step_variational_inequality
  projected_gradient_inner_bound

lemmas projected_gradient_step_descent_results =
  projected_gradient_one_step_distance_bound_to_point
  projected_gradient_one_step_distance_bound_to_minimizer


subsection \<open>Projected gradient descent\<close>

text \<open>
These theorem groups give the core projected-gradient descent convergence
layer.  They prove feasibility preservation, monotonicity of the objective, and
the O(1/N) function-value convergence bound for smooth convex objectives over a
closed convex feasible set.
\<close>

lemmas projected_gradient_descent_iteration_interface =
  projected_gradient_descent_iteratesI
  projected_gradient_descent_iteratesD
  projected_gradient_descent_iteratesE
  projected_gradient_descent_next_mem
  projected_gradient_descent_feasible_from_initial

lemmas projected_gradient_descent_one_step_results =
  projected_gradient_descent_one_step_distance_bound_to_point
  projected_gradient_descent_one_step_distance_bound_to_minimizer
  projected_gradient_descent_objective_nonincreasing

lemmas projected_gradient_descent_convergence_results =
  projected_gradient_descent_sum_function_value_gaps_bound_to_point
  projected_gradient_descent_sum_function_value_gaps_bound_to_minimizer
  projected_gradient_descent_last_gap_times_N_bound
  projected_gradient_descent_function_value_gap_bound_feasible
  projected_gradient_descent_function_value_gap_bound


subsection \<open>Projected-gradient mappings\<close>

text \<open>
The projected-gradient mapping is the constrained analogue of the gradient
residual.  A zero projected-gradient mapping is equivalent to a projected fixed
point and, over a closed convex feasible set, to the first-order variational
inequality.  For smooth convex objectives, this gives a global optimality
certificate.
\<close>

lemmas projected_gradient_mapping_interface =
  projected_gradient_mapping_step_relation
  projected_gradient_step_eq_sub_mapping
  projected_gradient_mapping_zero_iff_fixed_point
  projected_gradient_mapping_zero_imp_step_eq
  projected_gradient_step_eq_imp_mapping_zero
  gradient_step_minus_projected_gradient_step_eq_mapping_residual
  projected_gradient_mapping_variational_inequality

lemmas projected_gradient_mapping_optimality_results =
  projected_gradient_fixed_point_iff_first_order_condition
  projected_gradient_mapping_zero_iff_first_order_condition
  projected_gradient_fixed_point_imp_global_min_on
  projected_gradient_mapping_zero_imp_global_min_on
  first_order_condition_imp_global_min_on_smooth_convex


subsection \<open>Projected-gradient mapping residual rates\<close>

text \<open>
These results strengthen projected-gradient descent from function-value
convergence to residual convergence.  They show that the projected-gradient
mapping residual has a finite O(1/N) small-residual certificate along the
iterates.
\<close>

lemmas projected_gradient_mapping_residual_norm_results =
  projected_gradient_mapping_norm_eq_step_distance_divide
  projected_gradient_base_step_distance_eq_alpha_mapping_norm
  projected_gradient_step_base_distance_eq_alpha_mapping_norm
  projected_gradient_step_distance_sq_eq_mapping_norm_sq
  projected_gradient_mapping_norm_sq_eq_step_distance_sq
  projected_gradient_mapping_zero_iff_step_distance_zero

lemmas projected_gradient_mapping_step_progress_results =
  projected_gradient_step_progress_step_norm
  projected_gradient_step_progress_mapping
  projected_gradient_descent_step_progress_mapping

lemmas projected_gradient_mapping_sum_rate_results =
  projected_gradient_descent_sum_weighted_mapping_norm_sq_bound_feasible
  projected_gradient_descent_sum_weighted_mapping_norm_sq_bound
  projected_gradient_descent_sum_mapping_norm_sq_bound_feasible
  projected_gradient_descent_sum_mapping_norm_sq_bound
  projected_gradient_descent_sum_mapping_norm_sq_bound_to_minimizer_feasible
  projected_gradient_descent_sum_mapping_norm_sq_bound_to_minimizer

lemmas projected_gradient_mapping_average_rate_results =
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


subsection \<open>Residual convergence and epsilon-stationarity\<close>

text \<open>
This group rephrases projected-gradient mapping bounds as residual convergence
certificates.  The main user-facing statement is an epsilon-stationarity
complexity result: if the finite horizon is large enough, then one of the first
N iterates has projected-gradient residual at most eps.
\<close>

lemmas projected_gradient_residual_interface =
  projected_gradient_residual_nonneg
  projected_gradient_residual_sq_nonneg
  projected_gradient_residual_sq_eq_residual_power2
  projected_gradient_residual_le_of_sq_le
  projected_gradient_residual_sq_le_of_residual_le

lemmas projected_gradient_residual_small_sq_results =
  projected_gradient_descent_exists_small_residual_sq_feasible
  projected_gradient_descent_exists_small_residual_sq
  projected_gradient_descent_exists_small_residual_sq_below_feasible
  projected_gradient_descent_exists_small_residual_sq_below
  projected_gradient_descent_exists_small_residual_sq_to_minimizer_feasible
  projected_gradient_descent_exists_small_residual_sq_to_minimizer

lemmas projected_gradient_epsilon_stationarity_results =
  projected_gradient_descent_exists_epsilon_residual_feasible
  projected_gradient_descent_exists_epsilon_residual
  projected_gradient_descent_exists_epsilon_residual_below_feasible
  projected_gradient_descent_exists_epsilon_residual_below
  projected_gradient_descent_exists_epsilon_residual_to_minimizer_feasible
  projected_gradient_descent_exists_epsilon_residual_to_minimizer
  projected_gradient_descent_exists_epsilon_residual_to_minimizer_product_feasible
  projected_gradient_descent_exists_epsilon_residual_to_minimizer_product

lemmas projected_gradient_residual_zero_results =
  projected_gradient_residual_zero_iff_mapping_zero
  projected_gradient_residual_zero_iff_fixed_point
  projected_gradient_residual_zero_iff_first_order_condition
  projected_gradient_residual_zero_imp_global_min_on


subsection \<open>Strong convexity\<close>

text \<open>
The strong-convexity layer provides distance-gap estimates, uniqueness of
global minimizers, and sharper certificates for projected-gradient stationary
points.
\<close>

lemmas strong_convex_interface =
  strong_convex_lower_bound_onI
  strong_convex_lower_bound_onD_nonneg
  strong_convex_lower_bound_onD
  strong_convex_lower_bound_on_subset
  strong_convex_lower_bound_on_mono_mu

lemmas strongly_convex_interface =
  strongly_convex_differentiable_onI
  strongly_convex_differentiable_onD_convex_differentiable
  strongly_convex_differentiable_onD_strong
  strongly_smooth_convex_onI
  strongly_smooth_convex_onD_smooth
  strongly_smooth_convex_onD_strong

lemmas strong_convex_optimality_results =
  convex_differentiable_on_global_min_imp_first_order_condition
  strong_convex_foc_distance_gap
  strongly_convex_global_min_distance_gap
  strongly_smooth_convex_global_min_distance_gap
  strongly_convex_global_min_unique
  strongly_smooth_convex_global_min_unique
  strongly_smooth_projected_mapping_zero_distance_gap
  strongly_smooth_projected_mapping_zero_unique_global_min


subsection \<open>Linear convergence for projected gradient descent\<close>

text \<open>
Under strong convexity, projected-gradient descent admits a linear convergence
rate.  The first group collects elementary facts about the contraction factor,
and the second group gives the distance and function-value linear-rate
theorems.
\<close>

lemmas projected_gradient_linear_rate_factor_results =
  projected_gradient_linear_rate_denominator_pos
  projected_gradient_linear_rate_factor_nonnegative
  projected_gradient_linear_rate_factor_positive
  projected_gradient_linear_rate_factor_le_one
  projected_gradient_linear_rate_factor_lt_one

lemmas projected_gradient_descent_linear_rate_results =
  projected_gradient_descent_strong_one_step_distance_contract
  projected_gradient_descent_strong_one_step_distance_contract_factor
  projected_gradient_descent_distance_sq_linear_rate
  projected_gradient_descent_function_value_linear_rate_Suc
  projected_gradient_descent_function_value_linear_rate
  projected_gradient_descent_strict_rate_factor


subsection \<open>Lipschitz smoothness and mean-value bridge\<close>

text \<open>
This interface separates Lipschitz-gradient-style assumptions from the
algorithmic convergence layer.  The basic certificate interface records the
equivalence between line-descent bounds and the smooth upper-bound property.

The mean-value bridge connects primitive Lipschitz-gradient assumptions to the
same convergence framework with constant 2 * L.  This gives a reusable route
from standard differentiability-style assumptions to the projected-gradient
descent convergence theorems, without committing the algorithmic layer to a
particular integration formalization.
\<close>

lemmas lipschitz_smoothness_interface =
  line_descent_bound_onI
  line_descent_bound_onD_nonneg
  line_descent_bound_onD
  line_descent_bound_on_imp_smooth_upper_bound_on
  smooth_upper_bound_on_imp_line_descent_bound_on
  line_descent_bound_on_iff_smooth_upper_bound_on
  lipschitz_smooth_onI
  lipschitz_smooth_onD_has_gradient_on
  lipschitz_smooth_onD_lipschitz_gradient
  lipschitz_smooth_onD_line_descent
  lipschitz_smooth_onD_smooth_upper_bound
  lipschitz_smooth_convex_onI
  lipschitz_smooth_convex_on_imp_smooth_convex_on
  smooth_convex_on_and_lipschitz_gradient_imp_lipschitz_smooth_convex_on

lemmas lipschitz_mean_value_bridge_interface =
  line_mean_value_gradient_onI
  line_mean_value_gradient_onD
  line_mean_value_and_lipschitz_gradient_imp_line_descent_bound_on_twice
  line_mean_value_and_lipschitz_gradient_imp_smooth_upper_bound_on_twice
  line_mean_value_and_lipschitz_gradient_imp_lipschitz_smooth_on_twice
  line_mean_value_and_lipschitz_gradient_imp_lipschitz_smooth_convex_on_twice
  line_mean_value_and_lipschitz_gradient_imp_smooth_convex_on_twice

lemmas lipschitz_mean_value_algorithmic_results =
  line_mean_value_lipschitz_projected_gradient_descent_function_value_gap_bound


subsection \<open>Quadratic examples\<close>

text \<open>
The quadratic examples instantiate the abstract interfaces on the one-dimensional
quadratic objective.  They are useful both as regression tests for the library
and as compact demonstrations of how to use the public API.
\<close>

lemmas quadratic_real_example_results =
  quadratic_real_has_gradient
  quadratic_real_has_gradient_on_UNIV
  quadratic_real_convex_on_UNIV
  quadratic_real_convex_differentiable_on_UNIV
  quadratic_real_smooth_upper_bound_on_UNIV
  quadratic_real_lipschitz_gradient_on_UNIV
  quadratic_real_smooth_convex_on_UNIV
  quadratic_real_lipschitz_smooth_on_UNIV
  quadratic_real_lipschitz_smooth_convex_on_UNIV
  quadratic_real_strong_lower_bound_on_UNIV
  quadratic_real_strongly_smooth_convex_on_UNIV
  quadratic_real_global_min_on_zero

lemmas projected_quadratic_template_results =
  quadratic_real_projected_gradient_descent_exists_small_residual_sq
  quadratic_real_projected_gradient_descent_exists_epsilon_residual
  quadratic_real_projected_gradient_residual_zero_imp_zero

lemmas nonnegative_quadratic_example_results =
  closed_nonnegative_real
  convex_nonnegative_real
  quadratic_real_smooth_convex_on_nonnegative
  quadratic_real_strongly_smooth_convex_on_nonnegative
  quadratic_real_global_min_on_nonnegative_zero
  quadratic_real_unique_global_min_on_nonnegative
  nonnegative_quadratic_projected_gradient_step_unfold
  nonnegative_quadratic_projected_gradient_mapping_unfold
  nonnegative_quadratic_projected_gradient_residual_unfold
  nonnegative_quadratic_projected_gradient_descent_function_value_gap_bound
  nonnegative_quadratic_projected_gradient_descent_distance_linear_rate
  nonnegative_quadratic_projected_gradient_descent_exists_small_residual_sq
  nonnegative_quadratic_projected_gradient_descent_exists_epsilon_residual
  nonnegative_quadratic_projected_gradient_residual_zero_imp_zero


subsection \<open>Recommended public API\<close>

text \<open>
The following theorem groups are the recommended public surface of the entry.
The larger groups provide a stable overview for downstream developments, while
the final citation surface gives short aliases for the main high-level
theorems.

The lower-level groups above remain available for specialized uses, but
downstream developments should prefer the stable aliases below when referring
to the main convergence, residual, optimality, and linear-rate results.
\<close>

subsubsection \<open>Core infrastructure\<close>

lemmas main_first_order_infrastructure =
  gradient_pointwise_interface
  gradient_field_interface
  gradient_rule_interface
  global_min_interface
  first_order_condition_interface
  convex_first_order_results

lemmas main_smooth_descent_infrastructure =
  smooth_upper_bound_interface
  smooth_convex_interface
  gradient_step_interface
  gradient_step_descent_results
  abstract_descent_results

lemmas main_projection_infrastructure =
  projection_geometry_results
  projected_gradient_step_interface
  projected_gradient_step_descent_results


subsubsection \<open>Main convergence theorems\<close>

lemmas main_gradient_descent_theorems =
  gradient_descent_function_value_gap_bound
  gradient_descent_sum_gradient_norm_sq_bound
  gradient_descent_average_gradient_norm_sq_bound
  gradient_descent_exists_small_gradient_norm_sq

lemmas main_projected_gradient_descent_theorems =
  projected_gradient_descent_function_value_gap_bound
  projected_gradient_descent_sum_function_value_gaps_bound_to_minimizer
  projected_gradient_descent_last_gap_times_N_bound
  projected_gradient_descent_objective_nonincreasing

lemmas main_lipschitz_bridge_theorems =
  line_mean_value_and_lipschitz_gradient_imp_smooth_convex_on_twice
  line_mean_value_lipschitz_projected_gradient_descent_function_value_gap_bound

lemmas main_projected_gradient_mapping_theorems =
  projected_gradient_mapping_zero_iff_fixed_point
  projected_gradient_mapping_zero_iff_first_order_condition
  projected_gradient_mapping_zero_imp_global_min_on
  projected_gradient_descent_sum_mapping_norm_sq_bound
  projected_gradient_descent_average_mapping_norm_sq_bound
  projected_gradient_descent_exists_small_mapping_norm_sq
  projected_gradient_descent_exists_small_mapping_norm_sq_to_minimizer

lemmas main_epsilon_stationarity_theorems =
  projected_gradient_residual_zero_iff_first_order_condition
  projected_gradient_residual_zero_imp_global_min_on
  projected_gradient_descent_exists_small_residual_sq_to_minimizer
  projected_gradient_descent_exists_epsilon_residual_to_minimizer
  projected_gradient_descent_exists_epsilon_residual_to_minimizer_product

lemmas main_strong_convexity_and_linear_rate_theorems =
  strongly_smooth_convex_global_min_distance_gap
  strongly_smooth_convex_global_min_unique
  projected_gradient_descent_distance_sq_linear_rate
  projected_gradient_descent_function_value_linear_rate
  projected_gradient_descent_strict_rate_factor

lemmas main_example_theorems =
  quadratic_real_smooth_convex_on_UNIV
  quadratic_real_strongly_smooth_convex_on_UNIV
  quadratic_real_global_min_on_zero
  nonnegative_quadratic_projected_gradient_descent_function_value_gap_bound
  nonnegative_quadratic_projected_gradient_descent_exists_epsilon_residual
  nonnegative_quadratic_projected_gradient_residual_zero_imp_zero
  bounded_interval_quadratic_projected_gradient_descent_function_value_gap_bound
  bounded_interval_quadratic_projected_gradient_descent_exists_epsilon_residual
  bounded_interval_quadratic_projected_gradient_residual_zero_imp_zero

subsubsection \<open>Stable aliases for citation\<close>

text \<open>
The following aliases give short, stable names to the main high-level
statements of the entry.  They are intended for use in the AFP document,
README, and downstream developments.

These aliases are the part of the public surface that should remain stable
under later internal refactorings of the proof files.
\<close>

lemmas gradient_descent_sublinear_complexity =
  gradient_descent_function_value_gap_bound

lemmas gradient_descent_gradient_residual_complexity =
  gradient_descent_exists_small_gradient_norm_sq

lemmas projected_gradient_descent_sublinear_complexity =
  projected_gradient_descent_function_value_gap_bound

lemmas projected_gradient_descent_mapping_residual_complexity =
  projected_gradient_descent_exists_small_mapping_norm_sq_to_minimizer

lemmas projected_gradient_descent_epsilon_stationarity_complexity =
  projected_gradient_descent_exists_epsilon_residual_to_minimizer_product

lemmas projected_gradient_mapping_optimality_certificate =
  projected_gradient_mapping_zero_iff_first_order_condition

lemmas projected_gradient_mapping_global_min_certificate =
  projected_gradient_mapping_zero_imp_global_min_on

lemmas projected_gradient_residual_optimality_certificate =
  projected_gradient_residual_zero_iff_first_order_condition

lemmas projected_gradient_residual_global_min_certificate =
  projected_gradient_residual_zero_imp_global_min_on

lemmas lipschitz_mean_value_smooth_convex_bridge =
  line_mean_value_and_lipschitz_gradient_imp_smooth_convex_on_twice

lemmas lipschitz_mean_value_projected_gradient_descent_sublinear_complexity =
  line_mean_value_lipschitz_projected_gradient_descent_function_value_gap_bound

lemmas strongly_convex_distance_gap_certificate =
  strongly_smooth_convex_global_min_distance_gap

lemmas projected_gradient_descent_linear_distance_complexity =
  projected_gradient_descent_distance_sq_linear_rate

lemmas projected_gradient_descent_linear_function_value_complexity =
  projected_gradient_descent_function_value_linear_rate


subsubsection \<open>Complete recommended theorem surface\<close>

text \<open>
This final group collects the recommended high-level API of the entry.
It is useful as a compact overview of the main reusable results.
\<close>

lemmas first_order_methods_public_api =
  main_first_order_infrastructure
  main_smooth_descent_infrastructure
  lipschitz_smoothness_interface
  lipschitz_mean_value_bridge_interface
  lipschitz_mean_value_algorithmic_results
  main_projection_infrastructure
  main_gradient_descent_theorems
  main_projected_gradient_descent_theorems
  main_lipschitz_bridge_theorems
  main_projected_gradient_mapping_theorems
  main_epsilon_stationarity_theorems
  main_strong_convexity_and_linear_rate_theorems
  main_example_theorems

lemmas first_order_methods_citation_surface =
  gradient_descent_sublinear_complexity
  gradient_descent_gradient_residual_complexity
  projected_gradient_descent_sublinear_complexity
  projected_gradient_descent_mapping_residual_complexity
  projected_gradient_descent_epsilon_stationarity_complexity
  projected_gradient_mapping_optimality_certificate
  projected_gradient_mapping_global_min_certificate
  projected_gradient_residual_optimality_certificate
  projected_gradient_residual_global_min_certificate
  lipschitz_mean_value_smooth_convex_bridge
  lipschitz_mean_value_projected_gradient_descent_sublinear_complexity
  strongly_convex_distance_gap_certificate
  projected_gradient_descent_linear_distance_complexity
  projected_gradient_descent_linear_function_value_complexity

lemmas bounded_interval_quadratic_example_results =
  bounded_interval_real_iff
  zero_mem_bounded_interval_real
  closed_bounded_interval_real
  convex_bounded_interval_real
  quadratic_real_smooth_convex_on_bounded_interval
  quadratic_real_strongly_smooth_convex_on_bounded_interval
  quadratic_real_global_min_on_bounded_interval_zero
  quadratic_real_unique_global_min_on_bounded_interval
  bounded_interval_quadratic_projected_gradient_step_unfold
  bounded_interval_quadratic_projected_gradient_mapping_unfold
  bounded_interval_quadratic_projected_gradient_residual_unfold
  bounded_interval_quadratic_projected_gradient_descent_function_value_gap_bound
  bounded_interval_quadratic_projected_gradient_descent_distance_linear_rate
  bounded_interval_quadratic_projected_gradient_descent_exists_small_residual_sq
  bounded_interval_quadratic_projected_gradient_descent_exists_epsilon_residual
  bounded_interval_quadratic_projected_gradient_residual_zero_imp_zero

text \<open>
Recommended theorem groups for downstream users:

  • @{text first_order_methods_public_api}
  • @{text first_order_methods_citation_surface}

The individual aliases in @{text first_order_methods_citation_surface} provide
stable names for the main convergence, residual, optimality, Lipschitz-bridge,
and linear-rate results of the entry.
\<close>

end