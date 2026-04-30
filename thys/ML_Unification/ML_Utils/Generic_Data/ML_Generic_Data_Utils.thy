\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>ML Generic Data Utils\<close>
theory ML_Generic_Data_Utils
  imports
    ML_Functor_Instances
    ML_Identifiers
    ML_Logger
begin

paragraph \<open>Summary\<close>
text \<open>Utilities for @{ML_functor Generic_Data}.\<close>

ML_file\<open>pair_generic_data_args.ML\<close>
ML_file\<open>generic_ord_list_id_data.ML\<close>

end