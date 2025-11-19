\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Unification Hints\<close>
theory ML_Unification_Hints_Base
  imports
    ML_Conversion_Utils
    ML_Functor_Instances
    ML_Generic_Data_Utils
    ML_Costs_Priorities
    ML_Term_Index
    ML_Tactic_Utils
    ML_Term_Utils
    ML_Unifiers_Base
    ML_Unification_Parsers
begin

paragraph \<open>Summary\<close>
text \<open>A generalisation of unification hints, originally introduced in \<^cite>\<open>"unif-hints"\<close>.
The general shape of a hint is:
\<open>\<And>y1...yn. (\<And>x1...xn1. lhs1 \<equiv> rhs1) \<Longrightarrow> ... \<Longrightarrow> (\<And>x1...xnk. lhsk \<equiv> rhsk) \<Longrightarrow> lhs \<equiv> rhs\<close>

Originally, unification hints are restricted to produce equal terms with respect to the prover's
built-in definitional equality (e.g. \<open>\<alpha>\<beta>\<eta>\<close>-equality). Since we use proof-producing unification, we
can lift this restriction and support unification hints producing equal terms with respect to the
prover's logic (which widely subsumes definitional equality).

More specifically, we support a generalisation of unification hints that
\<^enum> creates provably equal terms,
\<^enum> allows arbitrary, proof-producing functions to perform the matching/unification,
\<^enum> allows non-atomic left-hand sides for premises (cf. \<^cite>\<open>"unif-hints"\<close>), and
\<^enum> allows additional universal variables in premises.
\<close>

ML_file\<open>unification_hints_base.ML\<close>
ML_file\<open>unification_hints.ML\<close>
ML_file\<open>term_index_unification_hints.ML\<close>

end
