# Napoleon's Theorem in Isabelle/HOL

This project formalizes Napoleon's theorem in the complex plane.  For a
nondegenerate triangle, construct equilateral triangles externally on its
three sides.  The three centres of those equilateral triangles form an
equilateral triangle.

The development is intentionally parameterized by the two possible
orientations of a 60-degree complex rotation.  It reuses the published
AFP `Morley_Theorem` session for the characterization of equilateral complex
triangles and the published `Complex_Geometry` infrastructure for the complex
plane and collinearity.  No equilateral-triangle predicate is duplicated
locally.

Exteriority is formalized rather than left implicit in the prose.  The
`side_orientation` function records the signed position of a point relative
to a directed side, and `external_side` requires the strict product of the
two side orientations to be negative.  The theorem
`napoleon_external_construction` proves that the three selected apices are
equilateral and lie on the exterior side of their respective directed sides.
The cyclic invariance of the orientation choice is proved explicitly.  The
final `napoleon_external_theorem` bundles those construction facts with the
equilateral-centre conclusion under the non-collinearity assumption.

## Build

With the Isabelle 2025-2 distribution and the AFP checkout containing
`Complex_Geometry` and `Morley_Theorem` available as session directories:

```bash
isabelle build -d /path/to/afp/thys -D . Napoleon
```

The repository wrapper can be used on the supported Windows workspace:

```powershell
.\tools\build.ps1 -Project napoleon-theorem-isabelle -NoDocument
.\tools\build.ps1 -Project napoleon-theorem-isabelle
```

## AI assistance

AI assistance was used for proof engineering. The final definitions,
statements, and proofs are checked by Isabelle.
