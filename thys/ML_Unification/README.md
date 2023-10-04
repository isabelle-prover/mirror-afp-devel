# ML-Unification

## Content

1. First-order and higher-order pattern
[E-unification](https://en.wikipedia.org/wiki/Unification_(computer_science%29#E-unification)
and E-matching.
While unifiers in Isabelle/ML only consider the alpha-beta-eta-equational theory of the lambda-calculus,
unifiers in this article
may take an extra background theory, in the form of an equational prover, into account.
For example, the unification problem `n + 1 = ?m + Suc 0`
may be solved by providing a prover for the background theory `forall n. n + 1 = n + Suc 0`.
2. Tactics, methods, and attributes with adjustable unifiers (e.g.\ resolution, fact, assumption, OF).
3. A generalisation of [unification hints](https://www.researchgate.net/publication/221302555_Hints_in_Unification).
Unification hints are a flexible extension for unifiers.
Among other things, they can be used for reflective tactics,
to provide canonical unification instances,
or to simply strengthen the background theory of a unifier in a controlled manner.
4. Simplifier integration for e-unifiers.
5. Practical combinations of unification algorithms, e.g. a combination of first-order and
higher-order pattern unification.
6. A hierarchical logger for Isabelle/ML,
including per logger configurations with log levels, output channels, message filters.
See `Logger/README.md` for details.

While this entry works with every object logic,
some extra setup for Isabelle/HOL and application examples are provided.
All unifiers are tested with SpecCheck.

See `Examples/` for some application examples.

## Build

Requirements:
1. The Isabelle development version
2. The AFP development version

## Future Tasks

1. Add higher-order unifier E-unification and matching
4. tests:
    - adapt tests to work for open terms

