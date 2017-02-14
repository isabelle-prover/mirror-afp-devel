section \<open>dL Formalization\<close>

text \<open>
  We present a formalization of a uniform substitution calculus for
  differential dynamic logic (dL). In this calculus, the soundness of dL
  proofs is reduced to the soundness of a finite number of axioms, standard
  propositional rules and a central \textit{uniform substitution} rule for
  combining axioms. We present a formal definition for the denotational
  semantics of dL and prove the uniform substitution calculus sound by showing
  that all inference rules are sound with respect to the denotational
  semantics, and all axioms valid (true in every state and interpretation).

  See: 
  Brandon Bohrer, Vincent Rahli, Ivana Vukotic, Marcus Völp, André Platzer.
  Formally verified differential dynamic logic. CPP 2017, pages 208-221

  Andre Platzer. A uniform substitution calculus for differential
  dynamic logic.  CADE'15, pages 467-481.
\<close>
theory "Differential_Dynamic_Logic" 
imports
  Complex_Main
  "../Ordinary_Differential_Equations/ODE_Analysis"
  "./Ids"
  "./Lib"
  "./Syntax"
  "./Denotational_Semantics"
  "./Frechet_Correctness"
  "./Static_Semantics"
  "./Coincidence"
  "./Bound_Effect"
  "./Axioms"
  "./Differential_Axioms"
  "./USubst"
  "./USubst_Lemma"
  "./Uniform_Renaming"
  "./Proof_Checker"
begin
end