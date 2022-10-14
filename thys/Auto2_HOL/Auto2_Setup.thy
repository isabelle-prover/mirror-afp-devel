(*
  File: Auto2_Base.thy
  Author: Bohua Zhan

  Base file for auto2 setup.
*)

theory Auto2_Setup
  imports Pure
begin

ML_file \<open>util.ML\<close>
ML_file \<open>util_base.ML\<close>
ML_file \<open>util_logic.ML\<close>
ML_file \<open>box_id.ML\<close>
ML_file \<open>consts.ML\<close>
ML_file \<open>property.ML\<close>
ML_file \<open>wellform.ML\<close>
ML_file \<open>wfterm.ML\<close>
ML_file \<open>rewrite.ML\<close>
ML_file \<open>propertydata.ML\<close>
ML_file \<open>matcher.ML\<close>
ML_file \<open>items.ML\<close>
ML_file \<open>wfdata.ML\<close>
ML_file \<open>auto2_data.ML\<close>
ML_file \<open>status.ML\<close>
ML_file \<open>normalize.ML\<close>
ML_file \<open>proofsteps.ML\<close>
ML_file \<open>auto2_state.ML\<close>
ML_file \<open>logic_steps.ML\<close>
ML_file \<open>auto2.ML\<close>
ML_file \<open>auto2_outer.ML\<close>
ML_file \<open>auto2_setup.ML\<close>

end
