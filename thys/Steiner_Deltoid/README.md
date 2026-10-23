# The Steiner Deltoid in Isabelle/HOL

This project formalizes the unit-circumcircle parametrisation of the Steiner
deltoid using only the published AFP session `Simson`:

```text
d(m) = (a + b + c) / 2 + m + a * b * c * cnj(m)^2 / 2
```

For a non-collinear triangle with vertices on the unit circle and a moving
point m on that circle, the theory proves:

- the explicit real parametrisation gamma t has derivative
  i * steiner_deltoid_normal a b c (unit_circle_param t);
- the derivative vanishes exactly at the stationary parameters
  m^3 = a * b * c, and those parameters are ordinary cusps with nonzero,
  real-linearly independent second and third derivatives; in this curve those
  derivatives are additionally proved perpendicular;
- the three cyclic Wallace--Simson incidence statements, with an alternate
  pair of feet available when the moving point equals a vertex;
- an equality-of-sets theorem identifying the appropriate Wallace--Simson line
  with the explicitly defined tangent line at every parameter, including the
  stationary cases;
- the parametrised point belongs to the defined image set
  steiner_deltoid a b c.

The tangent direction is i * normal at regular parameters and m at a
stationary parameter.  The theorem
steiner_deltoid_cusp_tangent_is_second_derivative formally identifies the
cusp tangent with the line in the direction of the second derivative -3 * m.
The normal-perpendicular theorem itself does not assume a nonzero normal.  The
equality theorem uses the alternate pair of feet at a vertex parameter instead
of imposing an artificial exception on the construction.

The regular-only foot-membership theorems are named
simson_line_is_tangent_to_steiner_deltoid_at_regular and
simson_line_is_tangent_to_steiner_deltoid_regular; the set-equality theorems
simson_line_eq_steiner_deltoid_tangent_at_all and
simson_line_eq_steiner_deltoid_tangent_all cover all parameters.

The historical background includes Butchart's 1939 treatment and de Guzmán's
2001 elementary proof; the Isabelle development depends formally only on the
published AFP session.

## Dependency boundary

`ROOT` declares `Simson` as the sole parent session.  The project does not
copy the Simson theories and does not import the local `steiner-line-isabelle`
development.  To build it against the published AFP checkout:

```bash
/opt/homebrew/bin/isabelle build -o document=false -d /path/to/afp/thys -D . Steiner_Deltoid
```

For the current local checkout, `/Users/arthur/afp-2026-08-05/thys` contains the
published AFP sessions used for the verification build.

## Files

- `ROOT`: session `Steiner_Deltoid = Simson +`.
- `Steiner_Deltoid.thy`: definitions and checked incidence, derivative, cusp,
  normal, and tangent theorems.
- `document/root.tex`, `document/root.bib`: AFP-style documentation.

## AI Assistance

AI assistance was used for proof engineering. The final definitions, statements,
and proofs are checked by Isabelle.
