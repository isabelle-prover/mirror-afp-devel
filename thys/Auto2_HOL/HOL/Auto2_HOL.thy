(*
  File: Auto2_HOL.thy
  Author: Bohua Zhan

  Main file for auto2 setup in HOL.
*)

theory Auto2_HOL
  imports HOL_Base
  keywords "@proof" :: prf_block % "proof"
    and "@have" "@case" "@obtain" "@let" "@contradiction" "@strong_induct" :: prf_decl % "proof"
    and "@unfold" :: prf_decl % "proof"
    and "@induct" "@fun_induct" "@case_induct" "@prop_induct" "@cases" :: prf_decl % "proof"
    and "@apply_induct_hyp" :: prf_decl % "proof"
    and "@subgoal" "@endgoal" "@end" :: prf_decl % "proof"
    and "@qed" :: prf_decl % "proof"
    and "@with" "where" "arbitrary" "@rule" :: quasi_command
begin

ML_file \<open>../util.ML\<close>
ML_file \<open>../util_base.ML\<close>
ML_file \<open>auto2_hol.ML\<close>
ML_file \<open>../util_logic.ML\<close>
ML_file \<open>../box_id.ML\<close>
ML_file \<open>../consts.ML\<close>
ML_file \<open>../property.ML\<close>
ML_file \<open>../wellform.ML\<close>
ML_file \<open>../wfterm.ML\<close>
ML_file \<open>../rewrite.ML\<close>
ML_file \<open>../propertydata.ML\<close>
ML_file \<open>../matcher.ML\<close>
ML_file \<open>../items.ML\<close>
ML_file \<open>../wfdata.ML\<close>
ML_file \<open>../auto2_data.ML\<close>
ML_file \<open>../status.ML\<close>
ML_file \<open>../normalize.ML\<close>
ML_file \<open>../proofsteps.ML\<close>
ML_file \<open>../auto2_state.ML\<close>
ML_file \<open>../logic_steps.ML\<close>
ML_file \<open>../auto2.ML\<close>
ML_file \<open>../auto2_outer.ML\<close>

ML_file \<open>acdata.ML\<close>
ML_file \<open>ac_steps.ML\<close>
ML_file \<open>unfolding.ML\<close>
ML_file \<open>induct_outer.ML\<close>
ML_file \<open>extra_hol.ML\<close>

method_setup auto2 = {* Scan.succeed (SIMPLE_METHOD o Auto2.auto2_tac) *} "auto2 prover"

attribute_setup forward = {* setup_attrib add_forward_prfstep *}
attribute_setup backward = {* setup_attrib add_backward_prfstep *}
attribute_setup backward1 = {* setup_attrib add_backward1_prfstep *}
attribute_setup backward2 = {* setup_attrib add_backward2_prfstep *}
attribute_setup resolve = {* setup_attrib add_resolve_prfstep *}
attribute_setup rewrite = {* setup_attrib add_rewrite_rule *}
attribute_setup rewrite_back = {* setup_attrib add_rewrite_rule_back *}
attribute_setup rewrite_bidir = {* setup_attrib add_rewrite_rule_bidir *}
attribute_setup forward_arg1 = {* setup_attrib add_forward_arg1_prfstep *}
attribute_setup forward_arg = {* setup_attrib add_forward_arg_prfstep *}
attribute_setup rewrite_arg = {* setup_attrib add_rewrite_arg_rule *}

end
