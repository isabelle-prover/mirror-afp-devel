\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>ML Conversion Utils\<close>
theory ML_Conversion_Utils
  imports
    Pure
begin

paragraph \<open>Summary\<close>
text \<open>Utilities for conversions.\<close>


lemma meta_eq_symmetric: "(A \<equiv> B) \<equiv> (B \<equiv> A)"
  by (rule equal_intr_rule) simp_all
ML_file\<open>conversion_util.ML\<close>

end