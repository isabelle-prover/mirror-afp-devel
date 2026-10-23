# Steiner's Line Theorem (Isabelle/HOL)

This entry formalizes Steiner's line theorem for a nondegenerate triangle in
complex coordinates. If `M` lies on the circumcircle of `A B C`, reflect `M`
in the three sidelines `BC`, `CA`, and `AB`. The three reflected points are
collinear, and their line passes through the orthocenter.

The session depends on the published AFP session `Simson`. The development
reuses its `foot` definition, `simson_line` theorem, circle interface, and
complex collinearity lemmas; it does not copy the Simson theories into this
entry.

## Main results

- `orthocenter_is_orthocenter` verifies the geometric meaning of the
  coordinate definition by proving the three altitude perpendicularities. Its
  algebraic statement only assumes that the vertices lie on a common circle.
- `steiner_line` proves collinearity of the three reflected points.
- `steiner_line_through_orthocenter` proves all three cyclic
  orthocenter/reflection collinearities. This covers vertex parameters where
  one pair of reflected points coincides and another pair determines the line.

## Build

The published `Simson` release and its `Complex_Geometry` dependency must be
available as Isabelle session directories. For the local AFP checkout used
in development:

```powershell
.\tools\build.ps1 -Project steiner-line-isabelle -NoDocument `
  -ExtraDir C:\Tools\afp-2026-08-12\thys\Simson, `
            C:\Tools\afp-2026-08-12\thys\Complex_Geometry

.\tools\build.ps1 -Project steiner-line-isabelle `
  -ExtraDir C:\Tools\afp-2026-08-12\thys\Simson, `
            C:\Tools\afp-2026-08-12\thys\Complex_Geometry
```

For another AFP checkout, replace the two `-ExtraDir` paths with its
`thys\Simson` and `thys\Complex_Geometry` directories.

## AI assistance

AI assistance was used for proof engineering. The final definitions,
statements, and proofs are checked by Isabelle.

## AFP submission record

- Submitted: 2026-08-12
- Entry: `Steiner`
- Submission: [`2026-08-12_17-00-42_938`](https://isa-afp.org/webapp/submission?id=2026-08-12_17-00-42_938)
- Status: `Build Success`; `AFP editors notified.`
- Topic: Mathematics/Geometry
- License: BSD
