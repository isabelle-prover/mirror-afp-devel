(*  Title:      Containers/Collection_Eq.thy
    Author:     René Thiemann, UIBK *)
theory Containers_Generator
imports 
  "../Deriving/Generator_Aux"
  "../Deriving/Derive_Manager"
  "~~/src/HOL/Library/Phantom_Type"
  Containers_Auxiliary
begin

subsection Introduction

text {* 
  In the following, we provide generators for the major classes 
  of the container framework: \texttt{ceq}, \texttt{corder}, \texttt{cenum},
  \texttt{set-impl}, and \texttt{mapping-impl}. 

  In this file we provide some common infrastructure on the ML-level which will
  be used by the individual generators.
*}

ML_file "containers_generator.ML"

end
