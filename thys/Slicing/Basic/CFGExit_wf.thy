theory CFGExit_wf imports CFGExit CFG_wf begin

subsection {* New well-formedness lemmas using @{text "(_Exit_)"} *}

locale CFGExit_wf = CFG_wf + CFGExit + 
  assumes Exit_empty:"Def (_Exit_) = {} \<and> Use (_Exit_) = {}"

begin

lemma Exit_Use_empty [dest!]: "V \<in> Use (_Exit_) \<Longrightarrow> False"
by(simp add:Exit_empty)

lemma Exit_Def_empty [dest!]: "V \<in> Def (_Exit_) \<Longrightarrow> False"
by(simp add:Exit_empty)

end

end