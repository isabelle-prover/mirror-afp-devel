header {* \isaheader{Dynamic and static data dependence} *}

theory DataDependence imports CFGExit_wf begin

subsection {* Dynamic data dependence *} 

definition (in CFG_wf) dyn_data_dependence :: 
  "'node \<Rightarrow> 'var \<Rightarrow> 'node \<Rightarrow> 'edge list \<Rightarrow> bool" ("_ influences _ in _ via _" [51,0,0])
where "n influences V in n' via as \<equiv>
    ((V \<in> Def n) \<and> (V \<in> Use n') \<and> (n -as\<rightarrow>* n') \<and> 
     (\<exists>a' as'. (as = a'#as') \<and> (\<forall>n'' \<in> set (sourcenodes as'). V \<notin> Def n'')))"


lemma (in CFG_wf) dyn_influence_Cons_source:
  "n influences V in n' via a#as \<Longrightarrow> sourcenode a = n"
  by(simp add:dyn_data_dependence_def,auto elim:path.cases)


lemma (in CFG_wf) dyn_influence_source_notin_tl_edges: 
  assumes ddep:"n influences V in n' via a#as"
  shows "n \<notin> set (sourcenodes as)"
proof(rule ccontr)
  assume "\<not> n \<notin> set (sourcenodes as)"
  hence isin:"n \<in> set (sourcenodes as)" by simp
  from ddep have all:"\<forall>n'' \<in> set (sourcenodes as). V \<notin> Def n''"
    and Def:"V \<in> Def n" by(simp_all add:dyn_data_dependence_def)
  from all isin have "V \<notin> Def n" by simp
  with Def show False by simp
qed


lemma (in CFG_wf) dyn_influence_only_first_edge:
  assumes ddep:"n influences V in n' via a#as"
  shows "state_val (transfers (kinds (a#as)) s) V = 
         state_val (transfer (kind a) s) V"
proof -
  from ddep have Def:"V \<in> Def n" and Use:"V \<in> Use n'"
    and path:"n -a#as\<rightarrow>* n'"
    and noDefs:"\<forall>n'' \<in> set (sourcenodes as). V \<notin> Def n''"
    by(simp_all add:dyn_data_dependence_def)
  from path have "n -[]@a#as\<rightarrow>* n'" by simp
  hence source:"n = sourcenode a"
    and edge:"sourcenode a -[a]\<rightarrow>* targetnode a"
    and path2:"targetnode a -as\<rightarrow>* n'"
    by(fastsimp dest:path_split elim:path.cases)+
  from ddep source have tail:"sourcenode a \<notin> set (sourcenodes as)"
    by(fastsimp intro!:dyn_influence_source_notin_tl_edges)
  { fix n'' assume isin:"n'' \<in> set (sourcenodes as)"
    with tail source have "n'' \<noteq> n" by(fastsimp simp:sourcenodes_def)
    with noDefs isin have "V \<notin> Def n''" by(auto simp:sourcenodes_def) }
  hence "\<forall>n'' \<in> set (sourcenodes as). V \<notin> Def n''" by simp
  with path2 have "state_val (transfers (kinds as) (transfer (kind a) s)) V = 
                   state_val (transfer (kind a) s) V"
    by(rule CFG_path_no_Def_equal)
  thus ?thesis by(auto simp:kinds_def)
qed


subsection {* Static data dependence *}


definition (in CFG_wf) data_dependence :: "'node \<Rightarrow> 'var \<Rightarrow> 'node \<Rightarrow> bool"
    ("_ influences _ in _" [51,0])
where data_dependences_eq:"n influences V in n' \<equiv> \<exists>as. n influences V in n' via as"

lemma (in CFG_wf) data_dependence_def: "n influences V in n' = 
  (\<exists>as a' as'. (as = a'#as') \<and> (V \<in> Def n) \<and> (V \<in> Use n') \<and>
                 (n -as\<rightarrow>* n') \<and> (\<forall>n'' \<in> set (sourcenodes as'). V \<notin> Def n''))"
by(auto simp:data_dependences_eq dyn_data_dependence_def)

end
