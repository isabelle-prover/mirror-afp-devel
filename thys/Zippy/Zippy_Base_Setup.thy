\<^marker>\<open>creator "Kevin Kappelmann"\<close>
chapter \<open>Zippy\<close>
theory Zippy_Base_Setup
  imports
    ML_Unification.ML_Logger
    ML_Unification.Setup_Result_Commands
begin

paragraph \<open>Summary\<close>
text \<open>Zippy is a tree-search framework based on (alternating) zippers.\<close>

setup_result zippy_base_logger = \<open>Logger.new_logger Logger.root "Zippy_Base"\<close>


end
