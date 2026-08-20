# Andrew's Monotone Chain Convex Hull Algorithm

This Isabelle/HOL development formalizes the executable core of Andrew's
monotone chain convex hull algorithm for planar points.

Authors:

- Arthur Freitas Ramos
- David Barros Hulak
- Ruy J. G. B. de Queiroz

The entry defines:

- the orientation determinant `cross` and left-turn predicate,
- the monotone stack scan used by both lower and upper chains,
- lexicographic duplicate removal,
- `lower_hull`, `upper_hull`, and the top-level `andrew_hull`, and
- executable examples for duplicate, collinear, square, and diamond-shaped
  inputs.

The main checked facts include subset preservation for hull vertices, stack
turn invariants for lower and upper scans, distinctness of the computed chains,
ordered lower and upper chain facts, a precise criterion for distinctness of
the final concatenation, length bounds, support-function invariants for the two
scans, convex-hull coverage for real-coordinate inputs, and the final
top-level theorem `andrew_hull_correctness`.  That theorem states the
specification in one place: the returned vertices are input points, every input
point lies in the convex hull of the returned vertices, and the returned
vertices have exactly the same convex hull as the input, and the returned
vertex set is irredundant: deleting any returned point changes the convex hull
of the returned set.  The examples evaluate the executable algorithm on integer
inputs and instantiate the real-coordinate correctness and irredundancy theorem
for square, collinear, and diamond-shaped inputs.

The executable definitions are polymorphic over ordered integral domains
because the scan only uses lexicographic ordering and orientation signs.  The
geometric convex-hull theorem is specialized to real coordinates because
Isabelle's convexity and separating-hyperplane results are stated in real
vector spaces.  The integer examples are therefore code/evaluation examples;
the real examples are the corresponding geometric-correctness instantiations.

Proof idea: whenever the scan removes a middle point, that point is dominated
by the remaining adjacent points in every support direction relevant to the
current chain.  The lower and upper scan invariants cover non-horizontal
directions, the sorted endpoints cover horizontal directions, and a separating
hyperplane argument converts this support domination into convex-hull coverage.

Scope: this is a functional-correctness development.  It does not formalize
the asymptotic `O(n log n)` running time of Andrew's algorithm.

Reference: A. M. Andrew, "Another Efficient Algorithm for Convex Hulls in Two
Dimensions", Information Processing Letters 9(5), 216-219, 1979.
DOI: `10.1016/0020-0190(79)90072-3`.

Build from this directory with the local Isabelle wrapper:

```powershell
$project = (Resolve-Path .).Path
isabelle build -D $project Andrew_Monotone_Chain
```

For a quick proof-only check while editing:

```powershell
$project = (Resolve-Path .).Path
isabelle build -o document=false -D $project Andrew_Monotone_Chain
```
