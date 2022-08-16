# A Verified Imperative Implementation of B-Trees

This repository contains all definitions, lemmas and proofs
related to the Bachelors Thesis "A Verified Imperative Implementation of B-Trees"
by Niels Mündler and the paper "A Verified Implementation of B+-trees in Isabelle/HOL" by Niels Mündler and Tobias Nipkow.

For a detailed description of the B-Tree implementation, [see the thesis](https://github.com/nielstron/btrees-thesis).
For a detailed description of the B+-Tree implementation, see the paper published in ICTAC 2022.

## Overview

A functional specification of B-trees, B-tree operations and a
height analysis may be found in
the files `BTree*.thy` that do not contain `Imp`.

An imperative specification of B-trees may be found in `BTree_Imp*.thy`.

The same structure applies for B+-trees and the prefix `BPlusTree*.thy`.

The imperative specification make use of the auxiliary definition
of "Partially Filled Arrays" as list refinements, which may be found in `Partially_Filled_Array.thy`.
Further an extension of the standard array blit operation in Isabelle,
such that it allows error-free array-internal copy operations,
may be found in `Array_SBlit.thy`.
Moreover this repository introduces a general "Flattening Iterator", which flattens two iterators on distinct data structures.

The remaining files contain auxiliary lemmas and definitions that are due to
Dr. Peter Lammich or me. 

All above mentioned files contain definitions as well as proofs of functional correctness.


## Usage

These theories have been tested with [Isabelle2021-1](https://isabelle.in.tum.de/website-Isabelle2021/index.html).

The files `BTree*.thy` and `BPlusTree*.thy` that do not contain `Imp` only need a regular Isabelle setup.

The rest of the theories build upon [Refine_Imperative_HOL](https://www.isa-afp.org/entries/Refine_Imperative_HOL.html), you will need to succesfully set up that project first as described in the [Archive of Formal Proofs](https://www.isa-afp.org/using.html).
The script `start_isabelle.sh` uses and if not available compiles a session
containing the content of the Refinement Framework which significantly enhances
working with the files provided in this project.
