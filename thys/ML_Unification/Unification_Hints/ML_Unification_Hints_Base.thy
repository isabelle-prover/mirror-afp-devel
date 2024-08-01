\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Unification Hints\<close>
theory ML_Unification_Hints_Base
  imports
    ML_Conversion_Utils
    ML_Functor_Instances
    ML_Generic_Data_Utils
    ML_Priorities
    ML_Term_Index
    ML_Tactic_Utils
    ML_Term_Utils
    ML_Unifiers_Base
    ML_Unification_Parsers
begin

paragraph \<open>Summary\<close>
text \<open>A generalisation of unification hints, originally introduced in \<^cite>\<open>"unif-hints"\<close>.
We support a generalisation that
\<^enum> allows additional universal variables in premises
\<^enum> allows non-atomic left-hand sides for premises
\<^enum> allows arbitrary functions to perform the matching/unification of a hint with a disagreement pair.

General shape of a hint:
\<open>\<And>y1...yn. (\<And>x1...xn1. lhs1 \<equiv> rhs1) \<Longrightarrow> ... \<Longrightarrow> (\<And>x1...xnk. lhsk \<equiv> rhsk) \<Longrightarrow> lhs \<equiv> rhs\<close>
\<close>

ML_file\<open>unification_hints_base.ML\<close>
ML_file\<open>unification_hints.ML\<close>
ML_file\<open>term_index_unification_hints.ML\<close>

end
