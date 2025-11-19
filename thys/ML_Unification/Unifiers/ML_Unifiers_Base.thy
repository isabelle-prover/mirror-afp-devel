\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>ML Unifiers\<close>
theory ML_Unifiers_Base
  imports
    ML_Unification_Base
    ML_Tactic_Utils
begin

paragraph \<open>Summary\<close>
text \<open>Unification modulo equations and combinators for unifiers.\<close>

paragraph \<open>Combinators\<close>

ML_file\<open>unification_combinator.ML\<close>

paragraph \<open>Type Unifiers\<close>

ML_file\<open>type_unification.ML\<close>

paragraph \<open>Standard Unifiers\<close>

ML_file\<open>higher_order_unification.ML\<close>
ML_file\<open>higher_order_pattern_unification.ML\<close>
ML_file\<open>first_order_unification.ML\<close>

paragraph \<open>Unification via Tactics\<close>

ML_file\<open>tactic_unification.ML\<close>

end
