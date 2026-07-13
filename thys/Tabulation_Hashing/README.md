# Tabulation Hashing (Isabelle/HOL)
This repository formalizes key properties of **simple tabulation hashing** in Isabelle/HOL, including:
- uniformity,
- 3-independence / 3-universality, and
- non-4-independence / non-4-universality.

The formal development is centered around the session `Tabulation_Hashing` defined in `ROOT`.

## Main results
The primary theorems are in `Simple_Tabulation_Hashing.thy`:
- `uniform`
- `three_universal`
- `not_four_universal`

At a high level, the development proves that simple tabulation hashing is 3-universal but not 4-universal (under standard cardinality assumptions on key and range spaces).

## Repository layout
- `ROOT`
  Isabelle session definition (`Tabulation_Hashing`) and document configuration.
- `Simple_Tabulation_Hashing.thy`
  Main formalization: definitions, probability-space arguments, and core proofs.
- `Xor.thy`
  Abstract XOR algebra (`abel_group_xor`), n-ary fold (`xor_fold`), and big-operator (`xor_sum`) infrastructure.
- `Xor_Inst.thy`
  Additional XOR instances, especially for fixed-length vectors.
- `Vec_Extras.thy`, `Vec_Extras_Inst.thy`
  Supporting lemmas and typeclass instances for fixed-length vectors.
- `Dependent_Product.thy`
  Reproduced helper lemmas used by the probabilistic proofs.
- `Examples.thy`
  Example instantiations and demonstration lemmas.
- `document/root.tex`, `document/root.bib`
  AFP-style session document sources.
- `archive/`
  Historical/experimental theory files not part of the active session build.

## Session definition
From `ROOT`:
- Session name: `Tabulation_Hashing`
- Parent session: `Universal_Hash_Families`
- Additional session dependency: `Fixed_Length_Vector`
- Main theories: `Xor`, `Simple_Tabulation_Hashing`
- Auxiliary non-document theories: `Dependent_Product`, `Vec_Extras`, `Examples`

## Prerequisites
You need an Isabelle + AFP environment where the following are available:
- `Universal_Hash_Families`
- `Fixed_Length_Vector`

## Build
From the repository root:

```sh
isabelle build -D .
```

Build only this session explicitly:

```sh
isabelle build -D . -b Tabulation_Hashing
```

Build with PDF document output:

```sh
isabelle build -D . -b -o document=pdf Tabulation_Hashing
```

## Reading order (recommended)
1. `Xor.thy` (algebraic foundations),
2. `Vec_Extras.thy` and `Xor_Inst.thy` (vector/XOR infrastructure),
3. `Simple_Tabulation_Hashing.thy` (definitions and proofs),
4. `Examples.thy` (instantiations and usage patterns).

## Development notes
- A minimal pre-commit setup exists in `.pre-commit-config.yaml` (currently trailing whitespace checks).
- Generated output is ignored via `.gitignore` (`output/` and editor backup files).

## Guidelines

- prefer ordering `finite J` before `J != {}` in assumptions

- It was decided that vectors (lists with fixed lengths) are best represented by
  - `Fixed_Length_Vector.vec` when indexing order is important
  - simple functions (FuncSets / PiE) when indexing order is not important
  - *(note)* `length = n` (`{xs. length xs = n}`) were also considered but most lemmas were removed in favour of simple functions (see archive)

