section {* Dynamic data dependence *}

theory DynDataDependence imports CFG_wf begin

context CFG_wf begin 

definition dyn_data_dependence :: 
  "'node \<Rightarrow> 'var \<Rightarrow> 'node \<Rightarrow> 'edge list \<Rightarrow> bool" ("_ influences _ in _ via _" [51,0,0])
where "n influences V in n' via as \<equiv>
    ((V \<in> Def n) \<and> (V \<in> Use n') \<and> (n -as\<rightarrow>* n') \<and> 
     (\<exists>a' as'. (as = a'#as') \<and> (\<forall>n'' \<in> set (sourcenodes as'). V \<notin> Def n'')))"


lemma dyn_influence_Cons_source:
  "n influences V in n' via a#as \<Longrightarrow> sourcenode a = n"
  by(simp add:dyn_data_dependence_def,auto elim:path.cases)


lemma dyn_influence_source_notin_tl_edges: 
  assumes "n influences V in n' via a#as"
  shows "n \<notin> set (sourcenodes as)"
proof(rule ccontr)
  assume "\<not> n \<notin> set (sourcenodes as)"
  hence "n \<in> set (sourcenodes as)" by simp
  from `n influences V in n' via a#as` have "\<forall>n'' \<in> set (sourcenodes as). V \<notin> Def n''"
    and "V \<in> Def n" by(simp_all add:dyn_data_dependence_def)
  from `\<forall>n'' \<in> set (sourcenodes as). V \<notin> Def n''` 
    `n \<in> set (sourcenodes as)` have "V \<notin> Def n" by simp
  with `V \<in> Def n` show False by simp
qed


lemma dyn_influence_only_first_edge:
  assumes "n influences V in n' via a#as" and "preds (kinds (a#as)) s"
  shows "state_val (transfers (kinds (a#as)) s) V = 
         state_val (transfer (kind a) s) V"
proof -
  from `preds (kinds (a#as)) s` have "preds (kinds as) (transfer (kind a) s)"
    by(simp add:kinds_def)
  from `n influences V in n' via a#as` have "n -a#as\<rightarrow>* n'"
    and "\<forall>n'' \<in> set (sourcenodes as). V \<notin> Def n''"
    by(simp_all add:dyn_data_dependence_def)
  from `n -a#as\<rightarrow>* n'` have "n = sourcenode a" and "targetnode a -as\<rightarrow>* n'"
    by(auto elim:path_split_Cons)
  from `n influences V in n' via a#as` `n = sourcenode a` 
  have "sourcenode a \<notin> set (sourcenodes as)"
    by(fastforce intro!:dyn_influence_source_notin_tl_edges)
  { fix n'' assume "n'' \<in> set (sourcenodes as)"
    with `sourcenode a \<notin> set (sourcenodes as)` `n = sourcenode a` 
    have "n'' \<noteq> n" by(fastforce simp:sourcenodes_def)
    with `\<forall>n'' \<in> set (sourcenodes as). V \<notin> Def n''` `n'' \<in> set (sourcenodes as)`
    have "V \<notin> Def n''" by(auto simp:sourcenodes_def) }
  hence "\<forall>n'' \<in> set (sourcenodes as). V \<notin> Def n''" by simp
  with `targetnode a -as\<rightarrow>* n'` `preds (kinds as) (transfer (kind a) s)`
  have "state_val (transfers (kinds as) (transfer (kind a) s)) V = 
        state_val (transfer (kind a) s) V"
    by -(rule CFG_path_no_Def_equal)
  thus ?thesis by(auto simp:kinds_def)
qed

end

end
