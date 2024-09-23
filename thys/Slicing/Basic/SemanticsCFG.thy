section \<open>CFG and semantics conform\<close>

theory SemanticsCFG imports CFG begin

locale CFG_semantics_wf = CFG sourcenode targetnode kind valid_edge Entry
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" (\<open>'('_Entry'_')\<close>) +
  fixes sem::"'com \<Rightarrow> 'state \<Rightarrow> 'com \<Rightarrow> 'state \<Rightarrow> bool" 
    (\<open>((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))\<close> [0,0,0,0] 81)
  fixes identifies::"'node \<Rightarrow> 'com \<Rightarrow> bool" (\<open>_ \<triangleq> _\<close> [51,0] 80)
  assumes fundamental_property:
    "\<lbrakk>n \<triangleq> c; \<langle>c,s\<rangle> \<Rightarrow> \<langle>c',s'\<rangle>\<rbrakk> \<Longrightarrow>
      \<exists>n' as. n -as\<rightarrow>* n' \<and> transfers (kinds as) s = s' \<and> preds (kinds as) s \<and>
               n' \<triangleq> c'"


end
