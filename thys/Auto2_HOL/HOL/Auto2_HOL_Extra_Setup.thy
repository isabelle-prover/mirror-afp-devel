(*
  File: Auto2_HOL_Extra_Setup.thy
  Author: Kevin Kappelmann

  Extra setup files for auto2 in HOL.
*)

theory Auto2_HOL_Extra_Setup
  imports
    HOL.HOL
    Auto2_Setup
begin

ML_file \<open>acdata.ML\<close>
ML_file \<open>ac_steps.ML\<close>
ML_file \<open>unfolding.ML\<close>
ML_file \<open>induct_outer.ML\<close>
ML_file \<open>extra_hol.ML\<close>
ML_file \<open>auto2_hol_extra_setup.ML\<close>

end
