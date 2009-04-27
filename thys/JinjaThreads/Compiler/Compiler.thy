(*  Title:      JinjaThreads/Compiler/Compiler.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Preservation of well-formedness} *}

theory Compiler
imports Correctness TypeComp
begin

theorem wt_J2JVM:
  "wf_J_prog P \<Longrightarrow> wf_jvm_prog (J2JVM P)"
by(simp only:o_def J2JVM_def)(intro wt_compP2 compP1_pres_wf)

end
