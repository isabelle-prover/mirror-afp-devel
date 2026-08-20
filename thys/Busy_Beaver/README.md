# The Busy Beaver Upper-Bound Principle

This repository formalizes the Busy Beaver upper-bound principle and its
computability consequences for the Turing machines from AFP's
`Universal_Turing_Machine` entry.  It is structured as an AFP-style Isabelle
session and connects a reusable abstract development to concrete halting
problems from that library.

## Authors

Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz.

## Result

The development has three connected layers:

- `Busy_Beaver_Base.thy` gives an abstract model-parametric theorem package for
  machines with finite size classes and unique exact halting times.  It defines
  `BB_time`, proves that any upper bound for `BB_time` decides zero-input
  halting, and derives noncomputability and eventual-domination consequences
  from explicit computability assumptions.
- `Turing_Busy_Beaver.thy` connects the abstract development to AFP's
  `Universal_Turing_Machine` entry.  It defines exact numeric-result halting
  times for AFP Turing programs, a finite Turing-program size measure, a
  concrete `Turing_BB_time`, a code-indexed Busy Beaver function tied to AFP's
  special halting problem `K1`, and a strengthened program/input-pair Busy
  Beaver function tied to AFP's two-argument halting problem `H1`.
- `Busy_Beaver.thy` is the AFP entry point that imports both parts under the
  entry name `Busy_Beaver`.

The central theorem package shows:

- `halting_decider_from_correct_0`: any total upper bound for the Busy Beaver
  time function decides zero-input halting.
- `BB_time_not_computable_if_halting_undecidable`: if zero-input halting has no
  computable decider, then `BB_time` is not computable.
- `BB_time_eventually_dominates_computable`: under the standard compilation
  witness assumption, `BB_time` eventually dominates every total computable
  function.
- `Turing_BB_time_ge`: the concrete AFP Turing-machine Busy Beaver function
  bounds exact halting times of bounded-size Turing programs.
- `coded_BB_upper_bound_decides_K1`: in AFP's `hpk` locale, any upper bound for
  the code-indexed Busy Beaver function decides the special halting problem
  `K1`.
- `pair_BB_upper_bound_decides_H1_pair`: any upper bound for the pair-indexed
  Busy Beaver function decides whether a specific encoded machine/input pair is
  in AFP's `H1`.
- `H1_decider_from_correct`: the induced list-level decider is correct for the
  full AFP set `H1`.
- `no_turing_computable_total_H1_deciding_upper_bound`: no upper-bound-induced
  `H1` decider set has a Turing-computable total characteristic function.
- `no_turing_computable_total_Pair_BB_time_decider`: in particular, the
  characteristic function of the `H1` decider set induced by `Pair_BB_time`
  itself is not Turing-computable total.

## Scope and strengthened halting result

The abstract base locale is intentionally a fixed-input Busy Beaver framework:
`time_set n` ranges over machines run on input `0`, and
`halting_decider_from_correct_0` decides `halts p 0`.  Thus the base theorem is
about the zero-input or special halting predicate.

The AFP Turing-machine bridge strengthens this at the concrete level by folding
the input into the Busy Beaver object.  The pair-indexed development uses
objects `(c, m)` consisting of a machine code and an input, with finite size
classes given by `c + m`.  Its upper-bound theorem yields a correct decider for
AFP's full list-coded two-argument halting set `H1`.  Using AFP's
`TuringComputable` theory, the development also proves an explicit
noncomputability consequence: for any such upper bound, the characteristic
function of the induced `H1` decider set is not Turing-computable total; this is
specialized to the decider induced by `Pair_BB_time`.

The eventual-domination result is also conditional in the formal development.
The locale assumption `computable_has_busy_witness` packages the usual
input-to-program compilation argument: for every computed function value `f n`,
there must eventually be a zero-input program of size at most `n` whose halting
time is at least `f n`.  The theorem then proves that `BB_time` dominates from
that witness assumption; it is not derived from finite size classes alone.

## Proof structure

1. Define halting and exact halting time over an abstract program type.
2. Use finite size-bounded program classes to define `BB_time` as a maximum.
3. Prove that `BB_time` bounds every exact halting time in its size class.
4. Derive a zero-input halting decider from any total upper bound for `BB_time`.
5. Add a generic computability interface to obtain noncomputability and
   conditional eventual-domination consequences.
6. Instantiate the base locale with AFP Turing programs by defining exact
   numeric-result halting times and a finite size measure for instructions and
   program lists.
7. Instantiate a code-indexed version inside AFP's `hpk` locale and relate its
   halting predicate to `K1`.
8. Instantiate a program/input-pair version inside `hpk` and prove that any
   upper bound decides `H1`, first on concrete pairs and then as a list-level
   decider for AFP's `H1` set.
9. Use AFP's equivalence between decidability and characteristic-function
   computability to prove concrete noncomputability corollaries for the induced
   `H1` decider sets.

## Files

- `ROOT`: AFP-style Isabelle session declaration.
- `Busy_Beaver_Base.thy`: abstract Busy Beaver definitions and theorem
  package.
- `Turing_Busy_Beaver.thy`: bridge to AFP's Universal Turing Machine
  formalization.
- `Busy_Beaver.thy`: entry-point theory importing the abstract and Turing
  developments.
- `document/root.tex`: Isabelle document wrapper.
- `document/root.bib`: bibliography.
- `build.ps1`: local Windows build helper.

## Build

Build with Isabelle2025-2 and AFP available:

```powershell
..\..\tools\build.ps1 -Project busy-beaver-isabelle -Clean `
  -ExtraDir C:\path\to\afp\thys\Universal_Turing_Machine
```

The session declares `Universal_Turing_Machine` as a session dependency and
imports only `TuringComputable` by its session-qualified name.  This makes the
existing AFP session available without using it as the parent session, so the
Busy Beaver build does not run that entry's generated-code theory.  When
building outside AFP's own ROOTS setup, pass the Universal Turing Machine
directory with `-ExtraDir` (or `-d`) so Isabelle can discover the session.

Equivalent command from an Isabelle shell:

```bash
isabelle build -d /cygdrive/c/path/to/afp/thys/Universal_Turing_Machine -D . Busy_Beaver
```

## References

Tibor Radó introduced the Busy Beaver function in "On Non-Computable
Functions", *Bell System Technical Journal* 41(3):877--884, 1962.

The concrete Turing-machine bridge uses AFP's Universal Turing Machine
formalization, corresponding to Xu, Zhang, and Urban's ITP 2013 paper
"Mechanising Turing Machines and Computability Theory in Isabelle/HOL".
