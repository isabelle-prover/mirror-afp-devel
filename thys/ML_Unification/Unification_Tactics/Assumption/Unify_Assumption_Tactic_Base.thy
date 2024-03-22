\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Assumption Tactic\<close>
theory Unify_Assumption_Tactic_Base
  imports
    ML_Functor_Instances
    ML_Tactic_Utils
    ML_Unification_Parsers
begin

paragraph \<open>Summary\<close>
text \<open>Assumption tactic and method with adjustable unifier.\<close>

ML_file\<open>unify_assumption_base.ML\<close>
ML_file\<open>unify_assumption.ML\<close>

end
