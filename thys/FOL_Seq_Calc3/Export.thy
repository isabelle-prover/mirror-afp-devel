section \<open>Export\<close>

theory Export imports Prover begin

definition \<open>prove_sequent \<equiv> i.mkTree eff rules\<close>
definition \<open>prove \<equiv> \<lambda>p. prove_sequent ([], [p])\<close>

declare Stream.smember_code [code del]
lemma [code]: \<open>Stream.smember x (y ## s) = (x = y \<or> Stream.smember x s)\<close>
  unfolding Stream.smember_def by auto

code_printing
  constant the \<rightharpoonup> (Haskell) "(\\x -> case x of { Just y -> y })"
  | constant Option.is_none \<rightharpoonup> (Haskell) "(\\x -> case x of { Just y -> False; Nothing -> True })"

code_identifier
  code_module Product_Type \<rightharpoonup> (Haskell) Arith
  | code_module Orderings \<rightharpoonup> (Haskell) Arith
  | code_module Arith \<rightharpoonup> (Haskell) Prover
  | code_module MaybeExt \<rightharpoonup> (Haskell) Prover
  | code_module List \<rightharpoonup> (Haskell) Prover
  | code_module Nat_Bijection \<rightharpoonup> (Haskell) Prover
  | code_module Syntax \<rightharpoonup> (Haskell) Prover
  | code_module Encoding \<rightharpoonup> (Haskell) Prover
  | code_module HOL \<rightharpoonup> (Haskell) Prover
  | code_module Set \<rightharpoonup> (Haskell) Prover
  | code_module FSet \<rightharpoonup> (Haskell) Prover
  | code_module Stream \<rightharpoonup> (Haskell) Prover
  | code_module Fair_Stream \<rightharpoonup> (Haskell) Prover
  | code_module Sum_Type \<rightharpoonup> (Haskell) Prover
  | code_module Abstract_Completeness \<rightharpoonup> (Haskell) Prover
  | code_module Export \<rightharpoonup> (Haskell) Prover

export_code open prove in Haskell

text \<open>
To export the Haskell code run:
\begin{verbatim}
  > isabelle build -e -D .
\end{verbatim}

To compile the exported code run:
\begin{verbatim}
  > ghc -O2 -i./program Main.hs
\end{verbatim}

To prove a formula, supply it using raw constructor names, e.g.:
\begin{verbatim}
  > ./Main "Imp (Pre 0 []) (Imp (Pre 1 []) (Pre 0 []))"
  |- (P) --> ((Q) --> (P))
  + ImpR on P and (Q) --> (P)
  P |- (Q) --> (P)
  + ImpR on Q and P
  Q, P |- P
 + Axiom on P
\end{verbatim}

The output is pretty-printed.
\<close>

end
