(*
  File: Auto2_HOL_Setup.thy
  Author: Bohua Zhan

  Setup of auto2 in HOL.
*)

theory Auto2_HOL_Setup
  imports
    Auto2_HOL_Extra_Setup
    HOL_Base
  keywords "@proof" :: prf_block % "proof"
    and "@have" "@case" "@obtain" "@let" "@contradiction" "@strong_induct" :: prf_decl % "proof"
    and "@unfold" :: prf_decl % "proof"
    and "@induct" "@fun_induct" "@case_induct" "@prop_induct" "@cases" :: prf_decl % "proof"
    and "@apply_induct_hyp" :: prf_decl % "proof"
    and "@subgoal" "@endgoal" "@end" :: prf_decl % "proof"
    and "@qed" :: qed_block % "proof"
    and "@with" "where" "arbitrary" "@rule" :: quasi_command
begin

ML_file \<open>auto2_hol_util_base.ML\<close>
ML\<open>
  structure Auto2_Keywords : AUTO2_KEYWORDS =
  struct
    val case' = @{command_keyword "@case"}
    val contradiction = @{command_keyword "@contradiction"}
    val end' = @{command_keyword "@end"}
    val endgoal = @{command_keyword "@endgoal"}
    val have = @{command_keyword "@have"}
    val let' = @{command_keyword "@let"}
    val obtain = @{command_keyword "@obtain"}
    val proof = @{command_keyword "@proof"}
    val qed = @{command_keyword "@qed"}
    val subgoal = @{command_keyword "@subgoal"}
    val rule = @{keyword "@rule"}
    val with' = @{keyword "@with"}
  end;
  structure Auto2_Setup = Auto2_Setup(
    structure Auto2_Keywords = Auto2_Keywords;
    structure UtilBase = Auto2_UtilBase;
  );
\<close>

ML\<open>
  structure Unfolding_Keyword : UNFOLDING_KEYWORD =
  struct val unfold = @{command_keyword "@unfold"} end;
  structure Induct_ProofSteps_Keywords : INDUCT_PROOFSTEPS_KEYWORDS =
  struct
    val apply_induct_hyp = @{command_keyword "@apply_induct_hyp"}
    val case_induct = @{command_keyword "@case_induct"}
    val cases = @{command_keyword "@cases"}
    val fun_induct = @{command_keyword "@fun_induct"}
    val induct = @{command_keyword "@induct"}
    val prop_induct = @{command_keyword "@prop_induct"}
    val strong_induct = @{command_keyword "@strong_induct"}
    val arbitrary = @{keyword "arbitrary"}
    val with' = @{keyword "@with"}
  end;
  structure Auto2_HOL_Extra_Setup = Auto2_HOL_Extra_Setup(
    structure Auto2_Setup = Auto2_Setup;
    structure Unfolding_Keyword = Unfolding_Keyword;
    structure Induct_ProofSteps_Keywords = Induct_ProofSteps_Keywords;
  );
\<close>
method_setup auto2 = \<open>Scan.succeed (SIMPLE_METHOD o Auto2_Setup.Auto2.auto2_tac)\<close> "auto2 prover"

ML\<open>
  open Auto2_Basic_UtilBase
  open Auto2_Setup.Basic_UtilLogic

  val WithTerm = Auto2_Setup.ProofStep.WithTerm
  val WithGoal = Auto2_Setup.ProofStep.WithGoal
  val WithProp = Auto2_Setup.ProofStep.WithProp
  val neq_filter = Auto2_Setup.ProofStep.neq_filter
  val order_filter = Auto2_Setup.ProofStep.order_filter
  val size1_filter = Auto2_Setup.ProofStep.size1_filter
  val not_type_filter = Auto2_Setup.ProofStep.not_type_filter

  open Auto2_Setup.ProofStepData
  open Auto2_HOL_Extra_Setup.Extra_HOL

  val add_strong_induct_rule = Auto2_HOL_Extra_Setup.Induct_ProofSteps.add_strong_induct_rule
  val add_case_induct_rule = Auto2_HOL_Extra_Setup.Induct_ProofSteps.add_case_induct_rule
  val add_prop_induct_rule = Auto2_HOL_Extra_Setup.Induct_ProofSteps.add_prop_induct_rule
  val add_var_induct_rule = Auto2_HOL_Extra_Setup.Induct_ProofSteps.add_var_induct_rule
  val add_fun_induct_rule = Auto2_HOL_Extra_Setup.Induct_ProofSteps.add_fun_induct_rule
  val add_cases_rule = Auto2_HOL_Extra_Setup.Induct_ProofSteps.add_cases_rule
\<close>

attribute_setup forward = \<open>setup_attrib add_forward_prfstep\<close>
attribute_setup backward = \<open>setup_attrib add_backward_prfstep\<close>
attribute_setup backward1 = \<open>setup_attrib add_backward1_prfstep\<close>
attribute_setup backward2 = \<open>setup_attrib add_backward2_prfstep\<close>
attribute_setup resolve = \<open>setup_attrib add_resolve_prfstep\<close>
attribute_setup rewrite = \<open>setup_attrib add_rewrite_rule\<close>
attribute_setup rewrite_back = \<open>setup_attrib add_rewrite_rule_back\<close>
attribute_setup rewrite_bidir = \<open>setup_attrib add_rewrite_rule_bidir\<close>
attribute_setup forward_arg1 = \<open>setup_attrib add_forward_arg1_prfstep\<close>
attribute_setup forward_arg = \<open>setup_attrib add_forward_arg_prfstep\<close>
attribute_setup rewrite_arg = \<open>setup_attrib add_rewrite_arg_rule\<close>


end
