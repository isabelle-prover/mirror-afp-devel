(*
  File: auto2_hol_extra_setup.ML
  Author: Kevin Kappelmann

  Extra setup for auto2 in HOL.
*)

signature AUTO2_HOL_EXTRA_SETUP =
sig
  structure Unfolding_Keyword: UNFOLDING_KEYWORD
  structure Induct_ProofSteps_Keywords: INDUCT_PROOFSTEPS_KEYWORDS
  structure ACUtil: ACUTIL
  structure AC_ProofSteps: AC_PROOFSTEPS
  structure Unfolding: UNFOLDING
  structure Induct_ProofSteps: INDUCT_PROOFSTEPS
  structure Extra_HOL: EXTRA_HOL
end

functor Auto2_HOL_Extra_Setup(
  structure Auto2_Setup: AUTO2_SETUP;
  structure Unfolding_Keyword: UNFOLDING_KEYWORD;
  structure Induct_ProofSteps_Keywords: INDUCT_PROOFSTEPS_KEYWORDS;
  ): AUTO2_HOL_EXTRA_SETUP =
struct

structure Unfolding_Keyword = Unfolding_Keyword
structure Induct_ProofSteps_Keywords = Induct_ProofSteps_Keywords
structure ACUtil = ACUtil(
  structure Basic_UtilBase = Auto2_Setup.UtilBase;
  structure Basic_UtilLogic = Auto2_Setup.UtilLogic;
)
structure AC_ProofSteps = AC_ProofSteps(
  structure ACUtil = ACUtil;
  structure Basic_UtilLogic = Auto2_Setup.UtilLogic;
  structure ProofStepData = Auto2_Setup.ProofStepData;
  structure RewriteTable = Auto2_Setup.RewriteTable;
  structure Update = Auto2_Setup.Update;
)
val _ = Theory.setup AC_ProofSteps.add_ac_proofsteps
structure Unfolding = Unfolding(
  structure Auto2_Outer = Auto2_Setup.Auto2_Outer;
  structure Basic_UtilLogic = Auto2_Setup.UtilLogic;
  structure Unfolding_Keyword = Unfolding_Keyword;
)
structure Induct_ProofSteps = Induct_ProofSteps(
  structure Auto2_Outer = Auto2_Setup.Auto2_Outer;
  structure Induct_ProofSteps_Keywords = Induct_ProofSteps_Keywords;
  structure UtilBase = Auto2_Setup.UtilBase;
  structure UtilLogic = Auto2_Setup.UtilLogic;
)
structure Extra_HOL = Extra_HOL(
  structure Basic_UtilBase = Auto2_Setup.UtilBase;
  structure Basic_UtilLogic = Auto2_Setup.UtilLogic;
  structure ProofStep = Auto2_Setup.ProofStep;
  structure ProofStepData = Auto2_Setup.ProofStepData;
)

end