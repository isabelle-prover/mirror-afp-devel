<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
     Copyright (c) 2024 Apple Inc. All rights reserved.
     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# AutoCorres2

AutoCorres2 is a tool that assists reasoning about C programs.
More information about usage, history and internals is part of the regular 
AFP entry documentation.

AutoCorres2 is a fork of AutoCorres:
  https://trustworthy.systems/projects/OLD/autocorres/

## Acknowledgements

### Authors of the new / refined material in AutoCorres2

* Johannes Hölz
* Fabian Immler
* Norbert Schirmer
* Salomon Sickert-Zehnter
* Simon Wimmer
 
Here is a list of authors and contributors to the original AutoCorres project:

### C-Parser authors:

* Michael Norrish
* Gerwin Klein
* Harvey Tuch
* Matthew Brecknell
* Rafal Kolanski
* David Greenaway
* Thomas Sewell

### AutoCorres authors:

* David Greenaway
* Japheth Lim
* Gerwin Klein

### C-Parser acknowledgements:

* Rohan Jacob-Rao
* Andrew Skelton
* Thomas Sewell
* Matthew Fernandez
* Matthew Brecknell
* Alejandro Gomez-Londono
* Lars Noschinski
* Pang Luo
* Edward Pierzchalski
* Florian Haftmann
* Ramana Kumar
* Corey Lewis
* Xin Gao
* Toby Murray

### AutoCorres acknowledgements

* Simon Windwood
* Joel Beeren
* Edward Pierzchalski
* Lars Noschinski
* Japheth Lim
* Brian Huffman
* Ramana Kumar
* Michael McInerney
* Pang Luo
* Vincent Jackson
* Corey Lewis
* Sophie Taylor
* David Cock
* Timothy Bourke
* Jia Meng
* Matthias Daum
* Nelson Billing
* Andrew Boyton
* Matthew Fernandez

## Other Open Source Projects

The tool contains some code of other open source projects:

1. Code from SML/NJ:
   - an implementation of binary sets (c-parser/Binaryset.ML)
   - the mllex and mlyacc tools (c-parser/tools/{mllex,mlyacc})

   This code is covered by SML/NJ's BSD-ish licence.
   SPDX-License-Identifier: SMLNJ

   See also http://www.smlnj.org

2. Code from the mlton compiler:
   - regions during lexing and parsing (c-parser/Region.ML, c-parser/SourceFile.ML and
     c-parser/SourcePos.ML)

   This code is governed by a BSD licence.
   SPDX-License-Identifier: HPND

   See http://mlton.org


## Examples

Some examples are in the `tests/examples` directory.

Many of these examples are quick-and-dirty proofs, and should not
necessary be considered the best style.

None-the-less, some of the examples available are, in approximate
increasing level of difficulty:

  * `Simple.thy`: Proofs of some simple functions, including
    `max` and `gcd`.

  * `Swap.thy`: Proof of a simple `swap` function.

  * `MultByAdd.thy`: Proof of a function that carries out
    multiplication using addition.

  * `Factorial.thy`: Proof of a factorial function, using
    several different methods.

  * `FibProof.thy`: Proof of the Fibonacci function, using
    several different methods.

  * `ListRev.thy`: Proof of a function that carries out an
    in-place linked list reversal.

  * `CList.thy`: Another list reversal, based on a proof by
    Mehta and Nipkow. See [the paper][3].

  * `IsPrime.thy`: Proof of a function that determines if
    the input number is prime.

  * `Memset.thy`: Proof of a C `memset` implementation.

  * `Quicksort.thy`: Proof of a simple quicksort
    implementation on an array of `int`s.

  * `BinarySearch.thy`: Proof of a function that determines
    if a sorted input array of `unsigned int` contains the
    given `unsigned int`.

  * `SchorrWaite.thy`: Proof a C implementation of the
    Schorr-Waite algorithm, using Mehta and Nipkow's
    high-level proof. See [the paper][3].

  * `Memcpy.thy`: Proof of a C `memcpy` implementation.
    The proof connects the C parser's byte-level heap
    with AutoCorres's type-safe heap representation.

