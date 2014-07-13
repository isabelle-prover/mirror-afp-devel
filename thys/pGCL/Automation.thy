(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

header "Automated Reasoning"

theory Automation imports StructuredReasoning
begin

text {* This theory serves as a container for automated reasoning
  tactics for pGCL, implemented in ML.  At present, there is a basic
  verification condition generator (VCG). *}

ML_file "pVCG.ML"

setup pVCG.setup

method_setup pvcg =
  {* Scan.succeed (fn ctxt => SIMPLE_METHOD' (pVCG.pVCG_tac ctxt)) *}
  "Probabilistic weakest preexpectation tactic"

declare wd_intros[wd]

lemmas core_wp_rules =
  wp_Skip        wlp_Skip
  wp_Abort       wlp_Abort
  wp_Apply       wlp_Apply
  wp_Seq         wlp_Seq
  wp_DC_split    wlp_DC_split
  wp_PC_fixed    wlp_PC_fixed
  wp_SetDC       wlp_SetDC
  wp_SetPC_split wlp_SetPC_split

declare core_wp_rules[pwp_core]

end
