# Projected Gradient Descent in Isabelle/HOL

This repository contains an Isabelle/HOL formalization of reusable infrastructure for first-order methods in smooth convex optimization, with projected-gradient descent as the central application.

The development is designed as a library for formal reasoning about gradient-based optimization methods.  It provides abstract interfaces for gradients, convexity, smooth upper bounds, descent estimates, projection geometry, projected-gradient mappings, residual certificates, strong convexity, linear convergence rates, Lipschitz-smoothness bridges, and concrete quadratic examples.

The project is structured as an AFP-oriented entry under the theme:

**Projected-gradient descent and reusable descent/projection convergence infrastructure for smooth convex optimization in Isabelle/HOL.**

## Overview

The entry formalizes a reusable fragment of smooth convex optimization theory.

The main development includes:

* gradient interfaces for functions on real inner-product spaces;
* first-order characterizations of convex differentiable functions;
* quadratic smooth upper-bound assumptions;
* a Lipschitz-smoothness and mean-value bridge interface;
* algorithm-independent descent and telescoping lemmas;
* descent lemmas for gradient descent;
* sublinear O(1/N) convergence estimates for gradient descent;
* projection geometry for closed convex sets;
* projected-gradient descent and its feasibility properties;
* sublinear O(1/N) convergence estimates for projected-gradient descent;
* projected-gradient mappings and their relation to first-order optimality;
* projected-gradient residual certificates and epsilon-stationarity bounds;
* strong convexity assumptions;
* linear-rate estimates for projected-gradient descent under strong convexity;
* simple quadratic and projected quadratic examples;
* a public theorem interface for downstream developments.

The formalization is deliberately structured around reusable assumptions rather than a single concrete algorithm.  In particular, the main convergence proofs use abstract smooth upper-bound, convexity, projection, and descent interfaces, so that future methods can reuse the same proof infrastructure.

## Main entry points

For most downstream developments, the recommended public import target is:

```isabelle
theory My_Client_Theory
  imports Main_Results
begin

end
```

The theory `Main_Results` collects the main reusable theorem groups and stable aliases intended for downstream use.

The umbrella theory collecting the complete entry is:

```isabelle
theory Projected_Gradient_Descent
  imports Main_Results
begin

end
```

After installation as an AFP entry, client theories should import the entry through the AFP session-qualified theory name.

For local development inside this repository, the theories can be built directly using the Isabelle session defined in `ROOT`.

## Public theorem surface

The theory `Main_Results` provides the recommended public theorem surface of the entry.

The main theorem groups are:

* `first_order_methods_public_api`

  A compact overview of the main reusable infrastructure and high-level theorem groups.

* `first_order_methods_citation_surface`

  A smaller group of stable aliases intended for use in documentation, downstream developments, and citations.

Important stable aliases include:

* `gradient_descent_sublinear_complexity`
* `gradient_descent_gradient_residual_complexity`
* `projected_gradient_descent_sublinear_complexity`
* `projected_gradient_descent_mapping_residual_complexity`
* `projected_gradient_descent_epsilon_stationarity_complexity`
* `projected_gradient_mapping_optimality_certificate`
* `projected_gradient_mapping_global_min_certificate`
* `projected_gradient_residual_optimality_certificate`
* `projected_gradient_residual_global_min_certificate`
* `strongly_convex_distance_gap_certificate`
* `projected_gradient_descent_linear_distance_complexity`
* `projected_gradient_descent_linear_function_value_complexity`

The public surface also includes the Lipschitz mean-value bridge aliases:

* `lipschitz_mean_value_smooth_convex_bridge`
* `lipschitz_mean_value_projected_gradient_descent_sublinear_complexity`

These names are intended to remain stable even if the internal proof files are later reorganized.

## Repository structure

The current theory files are organized as follows.

* `Gradient_Preliminaries.thy`

  Basic gradient-related definitions and elementary facts used throughout the development.

* `Convex_Differentiable.thy`

  First-order reasoning for convex differentiable functions, including reusable first-order convexity inequalities.

* `Smooth_Convex.thy`

  Smooth convex interfaces based on quadratic upper bounds.

* `Abstract_Descent.thy`

  Algorithm-independent telescoping, averaging, and finite-sum lemmas used in convergence proofs.

* `Gradient_Descent.thy`

  Definitions and one-step estimates for gradient descent.

* `Gradient_Descent_Rates.thy`

  Gradient-residual rate estimates and finite-horizon bounds for gradient descent.

* `Gradient_Descent_Convergence.thy`

  Sublinear function-value convergence results for gradient descent.

* `Projection_Geometry.thy`

  Pure projection geometry, including variational inequalities for metric projections onto closed convex sets.

* `Projection_Optimization.thy`

  Projected-gradient one-step estimates and projection-based optimization rules.

* `Projected_Gradient_Descent_Convergence.thy`

  Feasibility preservation and O(1/N)-type convergence results for projected-gradient descent.

* `Projected_Gradient_Mapping.thy`

  Projected-gradient mappings and their connection with projected fixed points and first-order optimality.

* `Projected_Gradient_Mapping_Rates.thy`

  Summability, averaging, and small-residual estimates for projected-gradient mappings along projected-gradient descent iterates.

* `Projected_Gradient_Descent_Residual_Convergence.thy`

  Projected-gradient residual certificates and finite-horizon epsilon-stationarity complexity results.

* `Strong_Convex.thy`

  Strong convexity definitions, distance-gap estimates, uniqueness of minimizers, and related optimality consequences.

* `Projected_Gradient_Descent_Linear_Rate.thy`

  Linear-rate convergence estimates for projected-gradient descent under strong convexity.

* `Lipschitz_Smoothness.thy`

  A Lipschitz-gradient interface, the line-descent certificate interface, and a mean-value bridge to the smooth upper-bound framework.

* `Examples_Quadratic.thy`

  Basic one-dimensional quadratic examples illustrating the abstract interfaces.

* `Examples_Projected_Quadratic.thy`

  Projected quadratic examples, including the nonnegative half-line constraint, a bounded interval constraint, and residual/e-stationarity consequences.

* `Main_Results.thy`

  Public theorem interface collecting the main reusable theorem groups and stable aliases.

* `Examples_Using_Main_Results.thy`

  A downstream-usage demonstration showing how client developments can use `Main_Results` without importing lower-level proof files directly.

* `Projected_Gradient_Descent.thy`

  Umbrella theory collecting the full development.

## Mathematical content

The development is centered around the following standard first-order optimization schemes.

For unconstrained gradient descent, the update is:

```text
x_{n+1} = x_n - alpha * G x_n
```

For projected-gradient descent over a closed convex set C, the update is:

```text
x_{n+1} = P_C (x_n - alpha * G x_n)
```

where `P_C` is the metric projection onto `C`.

The formalization proves convergence results under assumptions of the following form:

* `f` is convex on a feasible set;
* `G` is a gradient-like map for `f`;
* `f` satisfies a quadratic smooth upper bound with constant `L`;
* the step size `alpha` is positive and satisfies the usual smoothness restriction;
* in the projected case, the feasible set is closed and convex;
* for residual convergence, the projected-gradient mapping is used as a constrained stationarity measure;
* for linear convergence, `f` additionally satisfies a strong convexity condition.

The projected-gradient mapping is used as a reusable optimality and stationarity certificate.  Informally, it measures the failure of a point to be fixed by one projected-gradient step.  A zero projected-gradient mapping corresponds to the usual first-order variational inequality for the constrained problem, and under convexity assumptions this gives a global minimizer.

The residual layer strengthens the convergence theory from function-value convergence to finite-horizon stationarity certificates.  In particular, the development proves that among the first `N` projected-gradient iterates, one iterate has small projected-gradient residual under suitable assumptions.

## Design goals

This project is designed around the following principles.

### Reusable interfaces

The theory avoids hard-coding a specific Euclidean space or a specific objective function whenever possible.  Most statements are formulated over real inner-product spaces and abstract feasible sets.

### Separation between assumptions and algorithms

Smoothness, convexity, projection geometry, descent estimates, residual estimates, and convergence-rate arguments are separated into different theory files.  This makes it easier to reuse parts of the development for other first-order methods.

### Stable public API

The internal proof files are organized into layers, while `Main_Results` exposes a stable public theorem surface.  Downstream developments should normally import `Main_Results` rather than depending on the internal organization of the proof files.

### AFP-oriented structure

The repository is structured as an Isabelle session with a `ROOT` file, an AFP-style document, public theorem interface, examples, and an umbrella theory.  The goal is to make the formalization suitable for AFP submission after final build checks and style cleanup.

### Stability for future extensions

The current theory names and theorem interfaces are intended to be kept stable as much as possible.  Future extensions should preferably add new lemmas and theories without breaking existing imports.

## Building the project

To build the Isabelle session from the root of the repository, run:

```bash
isabelle build -D .
```

To build with document generation enabled, run:

```bash
isabelle build -v -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML" -D .
```

The session depends on `HOL-Analysis`, so the first build may spend most of its time building Isabelle's analysis library.  Once the dependency is cached, the project session itself should build quickly.

## Current status

The current development contains:

* basic gradient and convexity infrastructure;
* smooth upper-bound interfaces;
* abstract descent and telescoping lemmas;
* gradient descent convergence;
* projected-gradient descent convergence;
* projection geometry for closed convex sets;
* projected-gradient mapping optimality results;
* projected-gradient residual convergence and epsilon-stationarity results;
* strong convexity and distance-gap estimates;
* linear-rate results for projected-gradient descent;
* Lipschitz-smoothness and mean-value bridge interfaces;
* quadratic and projected quadratic examples;
* a public theorem interface in `Main_Results`;
* a downstream-usage demonstration in `Examples_Using_Main_Results`;
* an umbrella theory for the whole entry;
* an AFP-oriented document and bibliography.

At this stage, the development is intended to be kept stable for AFP submission. Further work should focus on documentation polish, theorem naming stability, and build hygiene rather than adding unrelated algorithms.

## Suggested final checks before AFP submission

Before submission, check the following.

1. Run a full Isabelle build:

```bash
isabelle build -D .
```

2. Run a document build:

```bash
isabelle build -v -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML" -D .
```

3. Check for unfinished or interactive proof artifacts:

```bash
grep -RInE '\bsorry\b|\bback\b|\bsledgehammer\b|\bsmt_oracle\b|\boops\b' -- *.thy
grep -RInE '^\s*(nitpick|quickcheck|nunchaku)\b' -- *.thy
grep -RIn '\[simp\]' -- *.thy
```

4. Check for unnamed simp rules:

```bash
grep -R "\[simp\]" -n -- *.thy
```

5. Check that every theory listed in `ROOT` exists and has the same theory name as its file name.

6. Check that `Main_Results.thy` imports only real existing theory files.

7. Check that `Examples_Using_Main_Results.thy` builds using only `Main_Results` as its import.

8. Check that all bibliography keys used in `document/root.tex` appear in `document/root.bib`.

9. Check that the public aliases in `first_order_methods_citation_surface` are stable and intentionally named.

10. Check that the README, AFP document, and theory comments describe the same public structure.

## Possible future extensions

The current entry focuses on reusable infrastructure for smooth convex first-order methods and the convergence theory of gradient descent and projected-gradient descent.

Possible future extensions include:

* a sharp integral proof that Lipschitz continuity of the gradient implies the quadratic smooth upper-bound interface with constant `L`;
* additional constrained examples such as box, ball, or polyhedral constraints;
* least-squares examples;
* proximal-gradient methods;
* conditional-gradient methods;
* accelerated gradient methods;
* projected methods for more specialized feasible sets;
* additional convergence criteria based on projected-gradient mappings;
* more downstream client examples using the public theorem surface.

These extensions are not required for the current AFP-oriented core, but they would naturally build on the existing interfaces.

## References

The mathematical development follows standard material from convex optimization and first-order methods, including:

* Yurii Nesterov, `Introductory Lectures on Convex Optimization: A Basic Course`;
* Yurii Nesterov, `Lectures on Convex Optimization`;
* Amir Beck, `First-Order Methods in Optimization`;
* Dimitri P. Bertsekas, `Nonlinear Programming`.

The AFP document also discusses related formalization work, including the AFP entry `Unconstrained Optimization` and recent Lean4 work on formalizing convergence rates of first-order algorithms for convex optimization.

## License

This development is distributed under the BSD 2-Clause License.
See the file `LICENSE` for details.
