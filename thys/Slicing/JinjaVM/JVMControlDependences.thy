section {* Instantiating the control dependences *}

theory JVMControlDependences imports
  JVMPostdomination
  JVMCFG_wf
  "../Dynamic/DynPDG"
  "../StaticIntra/CDepInstantiations"
begin

subsection {* Dynamic dependences *}

interpretation JVMDynStandardControlDependence:
  DynStandardControlDependencePDG "sourcenode" "targetnode" "kind" 
  "valid_edge\<^bsub>CFG\<^esub> prog" "(_Entry_)" "Def (fst\<^bsub>CFG\<^esub> prog)" "Use (fst\<^bsub>CFG\<^esub> prog)" 
  "state_val" "(_Exit_)" .. 

interpretation JVMDynWeakControlDependence:
  DynWeakControlDependencePDG "sourcenode" "targetnode" "kind" 
  "valid_edge\<^bsub>CFG\<^esub> prog" "(_Entry_)" "Def (fst\<^bsub>CFG\<^esub> prog)" "Use (fst\<^bsub>CFG\<^esub> prog)" 
  "state_val" "(_Exit_)" ..

subsection {* Static dependences *}

interpretation JVMStandardControlDependence:
  StandardControlDependencePDG "sourcenode" "targetnode" "kind" 
  "valid_edge\<^bsub>CFG\<^esub> prog" "(_Entry_)" "Def (fst\<^bsub>CFG\<^esub> prog)" "Use (fst\<^bsub>CFG\<^esub> prog)" 
  "state_val" "(_Exit_)" ..

interpretation JVMWeakControlDependence:
  WeakControlDependencePDG "sourcenode" "targetnode" "kind" 
  "valid_edge\<^bsub>CFG\<^esub> prog" "(_Entry_)" "Def (fst\<^bsub>CFG\<^esub> prog)" "Use (fst\<^bsub>CFG\<^esub> prog)" 
  "state_val" "(_Exit_)" ..

end



