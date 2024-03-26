\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Resolution Tactics\<close>
theory Unify_Resolve_Tactics_Base
  imports
    Unify_Assumption_Tactic_Base
    ML_Unifiers_Base
    ML_Method_Utils
begin

paragraph \<open>Summary\<close>
text \<open>Resolution tactics and methods with adjustable unifier.\<close>

ML_file\<open>unify_resolve_base.ML\<close>
ML_file\<open>unify_resolve.ML\<close>

end
