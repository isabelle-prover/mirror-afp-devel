theory Seifert_Van_Kampen
  imports
    Classical_Seifert_Van_Kampen
    Topological_Seifert_Van_Kampen
begin

section \<open>Top-level entry point\<close>

text \<open>
  This session formalizes a quotient-oriented version of the classical
  Seifert--van Kampen theorem in Isabelle/HOL.  It develops reusable
  infrastructure for pushout glue relations, free-product words, carrier-based
  amalgamated free products, and explicit path/homotopy quotients.  The
  unconditional classical open-union theorem is proved in
  \<open>Classical_Seifert_Van_Kampen\<close>.

  Auxiliary theories package the abstract encode/decode interface and the
  pushout-level constructions used internally by the proof.  The headline
  theorem exported by this entry is the classical result for open unions.
\<close>

end
