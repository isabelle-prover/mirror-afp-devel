theory SepLogic_Misc
  imports DataRefinement
begin
    
subsection \<open>Relators\<close> 
  
definition nrest_rel where 
  nres_rel_def_internal: "nrest_rel R \<equiv> {(c,a). c \<le> \<Down>R a}"

lemma nrest_rel_def: "\<langle>R\<rangle>nrest_rel \<equiv> {(c,a). c \<le> \<Down>R a}"
  by (simp add: nres_rel_def_internal relAPP_def)

lemma nrest_relD: "(c,a)\<in>\<langle>R\<rangle>nrest_rel \<Longrightarrow> c \<le>\<Down>R a" by (simp add: nrest_rel_def)
lemma nrest_relI: "c \<le>\<Down>R a \<Longrightarrow> (c,a)\<in>\<langle>R\<rangle>nrest_rel" by (simp add: nrest_rel_def)

lemma nrest_rel_comp: "\<langle>A\<rangle>nrest_rel O \<langle>B\<rangle>nrest_rel = \<langle>A O B\<rangle>nrest_rel"
  by (auto simp: nrest_rel_def conc_fun_chain[symmetric] conc_trans)

lemma pw_nrest_rel_iff: "(a,b)\<in>\<langle>A\<rangle>nrest_rel \<longleftrightarrow> nofailT (\<Down> A b) \<longrightarrow> nofailT a \<and> (\<forall>x t. inresT a x t \<longrightarrow> inresT (\<Down> A b) x t)"
  by (simp add: pw_le_iff nrest_rel_def)
     

lemma param_FAIL[param]: "(FAILT,FAILT) \<in> \<langle>R\<rangle>nrest_rel"
  by (auto simp: nrest_rel_def)
 

lemma param_RETURN[param]: 
  "(RETURNT,RETURNT) \<in> R \<rightarrow> \<langle>R\<rangle>nrest_rel"
  by (auto simp: nrest_rel_def RETURNT_refine)

lemma param_bind[param]:
  "(bindT,bindT) \<in> \<langle>Ra\<rangle>nrest_rel \<rightarrow> (Ra\<rightarrow>\<langle>Rb\<rangle>nrest_rel) \<rightarrow> \<langle>Rb\<rangle>nrest_rel"
  by (auto simp: nrest_rel_def intro: bindT_refine dest: fun_relD)


end