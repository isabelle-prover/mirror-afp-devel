# SeCaV Prover
This is an automated theorem prover for the SeCaV system for first-order logic with functions.

It has been formally verified to be sound and complete, which means that it will never pretend to have proven an invalid formula, and that it will prove any valid formula if given enough time.
The SeCaV Prover produces human-readable proofs in the SeCaV system, which means that users can verify the proofs by hand, and study them to understand why a formula is valid.

The prover is implemented and verified in Isabelle, with some supporting functions implemented in Haskell.

## Installation
You can download an executable binary version of the prover from the [release section](https://github.com/fkj/secav-prover/releases) of the development repository, or you can compile one yourself.

### Compilation
The prover is implemented in Isabelle and Haskell.

To compile the prover, you will need the following:
* [The Isabelle proof assistant (isabelle)](https://isabelle.in.tum.de/)
* [The Glasgow Haskell compiler (ghc)](https://www.haskell.org/ghc/)
* [The Cabal build system (cabal)](https://www.haskell.org/cabal/)
* [The Make build system (make)](https://www.gnu.org/software/make/)

If you are on a Linux system, most of these can probably be installed through the package manager of your distribution.
Otherwise, you will have to manually install each of them following the instructions on the pages linked above.
If you are on Windows, you may additionally want a Cygwin installation to get a Unix-like environment.

Additionally, the [Archive of Formal Proof](https://www.isa-afp.org/) must be installed and available to Isabelle.
The ["Using Entries"](https://www.isa-afp.org/using.html) section of the linked page contains instructions on how to do this.

If all of these are available, the prover can be compiled by invoking `make`.
This will first build the Isabelle theory, which involves checking the proofs of soundness and completeness, then exporting the prover into Haskell code.
The Cabal build system will then be called on to compile and link the exported code with the supporting (hand-written) Haskell code.
This will produce an executable binary somewhere in the `dist-newstyle` folder.

You can test that the prover works correctly by invoking `make test`.
This will start two automated test suites consisting of integration tests for soundness and completeness.
Since the Isabelle implementation of the prover has been formally verified to be sound and complete, these tests are mostly for the Haskell parts of the prover.
Note that especially the completeness test suite may take quite a while to run since it involves processing many Isabelle theories.

You can now run the prover through the `cabal run` command, e.g.
```
cabal run secav-prover -- "Imp P P"
```
In the usage examples below, simply replace `secav-prover` with `cabal run secav-prover --` to obtain equivalent results.

If you want to, you can also install the prover using the command `cabal install secav-prover`.
The command `secav-prover` should then become available on your PATH.

## Usage
The prover can be run by providing it with a formula in SeCaV Unshortener syntax, e.g.:
```
secav-prover "Imp P P"
```
If the formula is valid, the prover will then output a proof of the formula in SeCaV Unshortener syntax on standard output.
If the formula is not valid, the prover will loop forever, possibly printing parts of the failed proof tree as it goes.
For proof-theoretical reasons, there is generally no way to determine whether the prover is working on a proof that may still finish or is in an infinite loop.
For small formulas, however, the prover should finish very quickly if the formula is valid.

If you would like the proof in Isabelle syntax instead, you may give a filename to write an Isabelle proof to using the `-i` (or `--isabelle`) switch, e.g.:
```
secav-prover "Imp P P" -i Proof.thy
```
The generated file can then be opened in Isabelle to verify the proof.
To do so, the SeCaV theory must be available to Isabelle, e.g. by placing a copy of the `SeCaV.thy` file in the same folder as the generated file.

## Organisation of the repository
The implementation of the prover is split into two main parts: the top folder contains the implementation of the proof search procedure itself as well as the formal proofs of soundness and completeness in Isabelle files (`.thy`), while the `haskell` folder contains implementations of supporting functions such as parsing and code generation.

The top folder contains the following theories:
* `SeCaV.thy` contains the definition of the Sequent Calculus Verifier system, which is the logic we are working in, and a soundness theorem for the proof system
* `Sequent1.thy` is a shim theory for linking the AFP theory to the `Sequent_Calculus_Verifier` theory
* `Sequent_Calculus_Verifier.thy` contains a completeness result for the SeCaV proof system
* `Prover.thy` contains the definition of the proof search procedure
* `Export.thy` contains the configuration of the Isabelle-to-Haskell code generator for the proof search procedure
* `ProverLemmas.thy` contains formal proofs of a number of useful properties of the proof search procedure
* `Hintikka.thy` contains a definition of Hintikka sets for SeCaV formulas
* `EPathHintikka.thy` contains formal proof that the sets of formulas in infinite proof trees produced by the proof search procedure are Hintikka sets
* `Usemantics.thy` contains a definition of an alternative bounded semantics for SeCaV, which is used in the completeness proof
* `Countermodel.thy` contains a formal proof that an infinite proof tree produced by the proof search procedure gives rise to a countermodel of the formula given to the procedure
* `Soundness.thy` contains a formal proof of the soundness of the proof search procedure
* `Completeness.thy` contains a formal proof of the completeness of the proof search procedure
* `Results.thy` contains a summary of our theorems as well as some extra results linking the proof system, the SeCaV semantics, and the bounded semantics

The `haskell` folder initially contains two subfolders:
* `lib` contains a parser for SeCaV Unshortener syntax, an Unshortener to SeCaV/Isabelle syntax, and a procedure for converting proof trees into SeCaV Unshortener proofs
* `app` contains a definition of the command line interface of the prover

The Isabelle code generation will create a third subfolder, `prover`, which contains the generated proof search procedure in Haskell.

The `test` folder contains the definitions of the automated test suites for soundness and completeness.
The files `secav-prover.cabal` and `Setup.hs` are used to configure the Cabal build system.
The file `.hlint.yaml` is used to configure the HLint tool to ignore the generated Haskell code.

## Examples
A very simple example is the one used above:
```
> secav-prover "Imp P P"

Imp P P

AlphaImp
  Neg P
  P
Ext
  P
  Neg P
Basic
```

If we add the `--isabelle Imp.thy` option, we instead obtain a file containing:
```
theory Imp imports SeCaV begin

proposition \<open>P \<longrightarrow> P\<close> by metis

text \<open>
  Predicate numbers

    0 = P
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Pre 0 []) (Pre 0 [])
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Pre 0 []
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

end
```

The prover works in first-order logic with functions, so we can also try:
```
> secav-prover "Imp (Uni p[0]) (Exi (p[f[0]]))"
Imp (Uni (p [0])) (Exi (p [f[0]]))

AlphaImp
  Neg (Uni (p [0]))
  Exi (p [f[0]])
Ext
  Exi (p [f[0]])
  Exi (p [f[0]])
  Neg (Uni (p [0]))
GammaExi[f[0]]
  p [f[f[0]]]
  Exi (p [f[0]])
  Neg (Uni (p [0]))
Ext
  Exi (p [f[0]])
  Exi (p [f[0]])
  Neg (Uni (p [0]))
  p [f[f[0]]]
GammaExi[0]
  p [f[0]]
  Exi (p [f[0]])
  Neg (Uni (p [0]))
  p [f[f[0]]]
Ext
  Neg (Uni (p [0]))
  Neg (Uni (p [0]))
  Exi (p [f[0]])
  p [f[f[0]]]
  p [f[0]]
GammaUni[f[f[0]]]
  Neg (p [f[f[0]]])
  Neg (Uni (p [0]))
  Exi (p [f[0]])
  p [f[f[0]]]
  p [f[0]]
Ext
  Neg (Uni (p [0]))
  Neg (Uni (p [0]))
  Exi (p [f[0]])
  p [f[f[0]]]
  p [f[0]]
  Neg (p [f[f[0]]])
GammaUni[f[0]]
  Neg (p [f[0]])
  Neg (Uni (p [0]))
  Exi (p [f[0]])
  p [f[f[0]]]
  p [f[0]]
  Neg (p [f[f[0]]])
Ext
  Neg (Uni (p [0]))
  Neg (Uni (p [0]))
  Exi (p [f[0]])
  p [f[f[0]]]
  p [f[0]]
  Neg (p [f[f[0]]])
  Neg (p [f[0]])
GammaUni[0]
  Neg (p [0])
  Neg (Uni (p [0]))
  Exi (p [f[0]])
  p [f[f[0]]]
  p [f[0]]
  Neg (p [f[f[0]]])
  Neg (p [f[0]])
Ext
  p [f[f[0]]]
  p [f[0]]
  Neg (Uni (p [0]))
  Neg (p [f[f[0]]])
  Neg (p [f[0]])
  Neg (p [0])
  Exi (p [f[0]])
Basic
```

## Authors and license
Developers:
* [Asta Halkjær From](http://people.compute.dtu.dk/ahfrom/)
* [Frederik Krogsdal Jacobsen](http://people.compute.dtu.dk/fkjac/)

The prover is licensed under the GNU General Public License, version 3.0.
See the `LICENSE` file for the text of the license.
