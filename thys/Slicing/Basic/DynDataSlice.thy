header {* \isaheader{Realization of a dynamic data slice} *}

theory DynDataSlice imports PDG begin

subsection{* Define empty control dependence *}

definition (in CFG) empty_control_dependence :: "'node \<Rightarrow> 'node \<Rightarrow> 'edge list \<Rightarrow> bool"
where "empty_control_dependence n n' as \<equiv> False"

lemma (in CFGExit_wf) DynPDG_scd:
  "DynPDG sourcenode targetnode kind valid_edge (_Entry_) (_Exit_) 
          Def Use state_val empty_control_dependence"
proof
  fix n n' as assume "empty_control_dependence n n' as"
  thus "n' \<noteq> (_Exit_)" by(simp add:empty_control_dependence_def)
next
  fix n n' as assume "empty_control_dependence n n' as"
  thus "n -as\<rightarrow>* n' \<and> as \<noteq> []" by(simp add:empty_control_dependence_def)
qed


end