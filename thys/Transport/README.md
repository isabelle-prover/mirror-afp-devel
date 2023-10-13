# Transport via Partial Galois Connections and Equivalences

The supplementary material for the paper
"Transport via Partial Galois Connections and Equivalences",
Asian Symposium on Programming Languages and Systems (APLAS) 2023.

## Connections Paper <--> Formalisation

- All links are given in
  `Transport/Transport_Via_Partial_Galois_Connections_Equivalences_Paper.thy`.
   You can CTRL+click on each referenced theorem, definition, file, etc.

## Future Work

To make the framework usable in practice, the following steps needs to be done:
1. Integrate the results for natural functors into Isabelle’s (co)datatypes package.
2. Extend the prototype to automate the construction of compositions.
3. Polish the white-box transport support of the prototype to deal with arbitrary side conditions.
4. Derive and set up proper conditional transport rules for propositions
   (cf. Section 4.4 of Ondřej Kunčar's PhD thesis
   "Types, Abstraction and Parametric Polymorphism in Higher-Order Logic",
   https://www21.in.tum.de/~kuncar/documents/kuncar-phdthesis.pdf)