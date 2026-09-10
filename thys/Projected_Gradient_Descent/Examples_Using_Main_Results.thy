theory Examples_Using_Main_Results
  imports Main_Results
begin

section \<open>Using the public theorem interface\<close>

text \<open>
This theory illustrates how a downstream development can use the public
interface collected in @{text \<open>Main_Results\<close>}.

The point of this file is deliberately modest: it does not import any of the
internal proof layers directly.  Instead, it treats @{text \<open>Main_Results\<close>} as the public
entry point of the library and shows how client developments can refer to the
stable theorem groups and aliases collected there.

This is useful as a regression test for the public API: if the internal proof
files are later reorganized, the facts used below should remain available from
@{text \<open>Main_Results\<close>}.
\<close>


subsection \<open>Accessing the recommended public surface\<close>

text \<open>
A client theory can first collect the complete recommended public API.  This is
mostly useful as a compact overview of the entry.
\<close>

lemmas client_public_api =
  first_order_methods_public_api

text \<open>
For citation and downstream reuse, the smaller citation surface is usually the
more appropriate entry point.
\<close>

lemmas client_citation_surface =
  first_order_methods_citation_surface


subsection \<open>Smooth convex first-order infrastructure\<close>

text \<open>
The following groups demonstrate that the analytic and descent infrastructure
is available without importing the lower-level theories directly.
\<close>

lemmas client_first_order_infrastructure =
  main_first_order_infrastructure

lemmas client_smooth_descent_infrastructure =
  main_smooth_descent_infrastructure

lemmas client_projection_infrastructure =
  main_projection_infrastructure


subsection \<open>Gradient descent results\<close>

text \<open>
A downstream user interested in unconstrained gradient descent can reuse the
stable sublinear convergence and gradient-residual complexity aliases.
\<close>

lemmas client_gradient_descent_sublinear_rate =
  gradient_descent_sublinear_complexity

lemmas client_gradient_descent_residual_rate =
  gradient_descent_gradient_residual_complexity

lemmas client_gradient_descent_results =
  main_gradient_descent_theorems


subsection \<open>Projected-gradient descent results\<close>

text \<open>
For constrained smooth convex optimization, the projected-gradient descent
layer exposes the standard function-value convergence theorem.
\<close>

lemmas client_projected_gradient_descent_sublinear_rate =
  projected_gradient_descent_sublinear_complexity

lemmas client_projected_gradient_descent_results =
  main_projected_gradient_descent_theorems


subsection \<open>Projected-gradient mapping and residual certificates\<close>

text \<open>
The projected-gradient mapping is the constrained stationarity residual used
by this entry.  The following aliases expose the main optimality and residual
complexity certificates from the public interface.
\<close>

lemmas client_projected_gradient_mapping_optimality =
  projected_gradient_mapping_optimality_certificate

lemmas client_projected_gradient_mapping_global_min =
  projected_gradient_mapping_global_min_certificate

lemmas client_projected_gradient_residual_optimality =
  projected_gradient_residual_optimality_certificate

lemmas client_projected_gradient_residual_global_min =
  projected_gradient_residual_global_min_certificate

lemmas client_projected_gradient_mapping_residual_complexity =
  projected_gradient_descent_mapping_residual_complexity

lemmas client_projected_gradient_epsilon_stationarity =
  projected_gradient_descent_epsilon_stationarity_complexity

lemmas client_projected_gradient_mapping_results =
  main_projected_gradient_mapping_theorems

lemmas client_projected_gradient_epsilon_stationarity_results =
  main_epsilon_stationarity_theorems


subsection \<open>Strong convexity and linear-rate results\<close>

text \<open>
The strongly convex layer provides distance-gap certificates and linear
convergence estimates for projected-gradient descent.
\<close>

lemmas client_strongly_convex_distance_gap =
  strongly_convex_distance_gap_certificate

lemmas client_projected_gradient_linear_distance_rate =
  projected_gradient_descent_linear_distance_complexity

lemmas client_projected_gradient_linear_function_value_rate =
  projected_gradient_descent_linear_function_value_complexity

lemmas client_strong_convexity_and_linear_rate_results =
  main_strong_convexity_and_linear_rate_theorems


subsection \<open>Concrete quadratic examples\<close>

text \<open>
The example layer can also be accessed from @{text \<open>Main_Results\<close>}.  These facts show
how the abstract theorem surface is instantiated on a simple one-dimensional
quadratic objective and on the nonnegative half-line constraint.
\<close>

lemmas client_quadratic_examples =
  main_example_theorems

lemmas client_quadratic_smooth_convex_example =
  quadratic_real_smooth_convex_on_UNIV

lemmas client_quadratic_strongly_smooth_convex_example =
  quadratic_real_strongly_smooth_convex_on_UNIV

lemmas client_quadratic_global_min_example =
  quadratic_real_global_min_on_zero

lemmas client_nonnegative_quadratic_pgd_rate_example =
  nonnegative_quadratic_projected_gradient_descent_function_value_gap_bound

lemmas client_nonnegative_quadratic_epsilon_stationarity_example =
  nonnegative_quadratic_projected_gradient_descent_exists_epsilon_residual

lemmas client_nonnegative_quadratic_residual_optimality_example =
  nonnegative_quadratic_projected_gradient_residual_zero_imp_zero


subsection \<open>A compact downstream package\<close>

text \<open>
A downstream project may collect only the parts of the public API that it needs.
The following bundle is an example of a small client-facing package for smooth
convex projected-gradient descent.
\<close>

lemmas client_projected_gradient_descent_package =
  client_smooth_descent_infrastructure
  client_projection_infrastructure
  client_projected_gradient_descent_sublinear_rate
  client_projected_gradient_mapping_optimality
  client_projected_gradient_mapping_global_min
  client_projected_gradient_mapping_residual_complexity
  client_projected_gradient_epsilon_stationarity
  client_strongly_convex_distance_gap
  client_projected_gradient_linear_distance_rate
  client_projected_gradient_linear_function_value_rate


text \<open>
This file intentionally proves no new mathematical theorem.  Its purpose is to
document and test the public theorem surface exposed by @{text \<open>Main_Results\<close>}.  In
particular, it shows that client developments can work with the stable aliases
and recommended theorem groups without depending on the internal organization
of the proof files.
\<close>

subsection \<open>Lipschitz-gradient bridge\<close>

text \<open>
The mean-value bridge shows how a client can connect primitive
Lipschitz-gradient assumptions to the smooth-convex interface used by the
algorithmic convergence theorems.
\<close>

lemmas client_lipschitz_mean_value_smooth_convex_bridge =
  lipschitz_mean_value_smooth_convex_bridge

lemmas client_lipschitz_mean_value_projected_gradient_rate =
  lipschitz_mean_value_projected_gradient_descent_sublinear_complexity

end