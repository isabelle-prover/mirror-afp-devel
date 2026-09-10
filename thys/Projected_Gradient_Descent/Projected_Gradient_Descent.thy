theory Projected_Gradient_Descent
  imports Main_Results
begin

section \<open>Projected Gradient Descent\<close>

text \<open>
This is the umbrella theory of the entry.

It imports the complete public development for smooth convex first-order
optimization through @{text \<open>Main_Results\<close>}.  The imported material includes reusable
interfaces for gradients, convex first-order reasoning, smooth upper bounds,
abstract descent arguments, projection geometry, projected-gradient descent,
projected-gradient mappings, residual convergence certificates, strong
convexity, linear-rate refinements, Lipschitz-smoothness bridges, and
quadratic examples.

The recommended public theorem surface is collected in @{text \<open>Main_Results\<close>}.
Downstream developments should normally import @{text \<open>Main_Results\<close>} when they want to
reuse the library, rather than depending on the internal organization of the
individual proof files.
\<close>

end