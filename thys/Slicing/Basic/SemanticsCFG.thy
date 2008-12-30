header {* \isaheader{CFG and semantics conform} *}

theory SemanticsCFG imports CFG begin

locale CFG_semantics_wf = CFG _ _ kind valid_edge Entry
  for kind :: "'edge \<Rightarrow> 'state edge_kind"
    and valid_edge :: "'edge \<Rightarrow> bool"
    and Entry :: 'node ("'('_Entry'_')")
  +
  fixes sem::"'com \<Rightarrow> 'state \<Rightarrow> 'com \<Rightarrow> 'state \<Rightarrow> bool" 
    ("((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [0,0,0,0] 81)
  fixes identifies::"'node \<Rightarrow> 'com \<Rightarrow> bool"
    ("_ identifies _" [51,0] 80)
  constrains state_val::"'state \<Rightarrow> 'var \<Rightarrow> 'val option"
  constrains valid_edge :: "'edge \<Rightarrow> bool"
  assumes fundamental_property:
    "\<lbrakk>n identifies c; \<langle>c,s\<rangle> \<Rightarrow> \<langle>c',s'\<rangle>\<rbrakk> \<Longrightarrow>
      \<exists>n' as. CFG.path sourcenode targetnode valid_edge n as n' \<and> 
              transfers (CFG.kinds kind as) s = s' \<and> preds (CFG.kinds kind as) s \<and>
               n' identifies c'"


end
