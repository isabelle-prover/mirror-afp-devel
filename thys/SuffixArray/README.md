#Formally Verified Suffix Array Construction

##Requirements:

This artefact requires Isabelle/HOL 2024 version.

##Usage:

Open Isabelle/HOL and open any of the theory files.

To run the verification of the _Suffix Array construction by Induced Sorting_, i.e. SA-IS algorithm, open the file `sais/proof/SAIS_Verification.thy`.  
The HOL model of the SA-IS algorithm is in `sais/def/SAIS.thy`.  
To extract the algorithm to Haskell, open `sais/code/Code_Extraction.thy`.
Note that the bulk of the verification of the SA-IS algorithm is achieved by proving the correctness of an abstract model, with the definition found in `sais/abs-def/Abs_SAIS.thy` and proof in `sais/abs-proof/Abs_SAIS_Verification.thy`.

To run the verification of the simple algorithm, open the file `simple/Simple_SACA_Proof.thy`.  
The HOL model of the simple algorithm is in `simple/Simple_SACA.thy`.

To compare the two verifications, open `SACA_Equiv.thy`.

##Content Structure:

This artefact directory is as follows:

 - `README.md`: This README file.
 - `ROOT`: The root file.
 - `SACA_Equiv.thy`: Equivalence between the simple and SAIS algorithms.
 - `document`: The latex document.
 - `sais`: The SA-IS algorithm, its underlying theory, verification of the abstract and concrete HOL models, and code extraction.
 - `simple`: A simple suffix array construction algorithm and its verification.
 - `spec`: Axiomatic specification and properties about suffix arrays.
 - `util`: General theorems about bijections, sorting, monotonic functions and other miscellaneous theorems.
 - `order`: Theorems about ordering suffixes. 
 - `extra`: Additional theorems that are useful but are no longer needed by this formalization.
