section {* Dependent Live Variables *}

theory DependentLiveVariables imports DynPDG begin

text {* @{text dependent_live_vars} calculates variables which
  can change\\ the value of the @{term Use} variables of the target node *}

context DynPDG begin

inductive_set
  dependent_live_vars :: "'node \<Rightarrow> ('var \<times> 'edge list \<times> 'edge list) set"
  for n' :: "'node"
  where dep_vars_Use: 
  "V \<in> Use n' \<Longrightarrow> (V,[],[]) \<in> dependent_live_vars n'"

  | dep_vars_Cons_cdep:
  "\<lbrakk>V \<in> Use (sourcenode a); sourcenode a -a#as'\<rightarrow>\<^bsub>cd\<^esub> n''; n'' -as''\<rightarrow>\<^sub>d* n'\<rbrakk>
  \<Longrightarrow> (V,[],a#as'@as'') \<in> dependent_live_vars n'"

  | dep_vars_Cons_ddep:
  "\<lbrakk>(V,as',as) \<in> dependent_live_vars n'; V' \<in> Use (sourcenode a);
    n' = last(targetnodes (a#as));
    sourcenode a -{V}a#as'\<rightarrow>\<^bsub>dd\<^esub> last(targetnodes (a#as'))\<rbrakk>
  \<Longrightarrow> (V',[],a#as) \<in> dependent_live_vars n'"

  | dep_vars_Cons_keep:
  "\<lbrakk>(V,as',as) \<in> dependent_live_vars n'; n' = last(targetnodes (a#as));
     \<not> sourcenode a -{V}a#as'\<rightarrow>\<^bsub>dd\<^esub> last(targetnodes (a#as'))\<rbrakk>
  \<Longrightarrow> (V,a#as',a#as) \<in> dependent_live_vars n'"



lemma dependent_live_vars_fst_prefix_snd:
  "(V,as',as) \<in> dependent_live_vars n' \<Longrightarrow> \<exists>as''. as'@as'' = as"
by(induct rule:dependent_live_vars.induct,simp_all)


lemma dependent_live_vars_Exit_empty [dest]:
  "(V,as',as) \<in> dependent_live_vars (_Exit_) \<Longrightarrow> False"
proof(induct rule:dependent_live_vars.induct)
  case (dep_vars_Cons_cdep V a as' n'' as'')
  from `n'' -as''\<rightarrow>\<^sub>d* (_Exit_)` have "n'' = (_Exit_)"
    by(fastforce intro:DynPDG_path_Exit)
  with `sourcenode a -a#as'\<rightarrow>\<^bsub>cd\<^esub> n''` have "sourcenode a -a#as'\<rightarrow>\<^sub>d* (_Exit_)"
    by(fastforce intro:DynPDG_path_cdep)
  hence "sourcenode a = (_Exit_)" by(fastforce intro:DynPDG_path_Exit)
  with `V \<in> Use (sourcenode a)` show False by simp(erule Exit_Use_empty)
qed auto


lemma dependent_live_vars_lastnode:
  "\<lbrakk>(V,as',as) \<in> dependent_live_vars n'; as \<noteq> []\<rbrakk> 
  \<Longrightarrow> n' = last(targetnodes as)"
proof(induct rule:dependent_live_vars.induct)
  case (dep_vars_Cons_cdep V a as' n'' as'')
  from `sourcenode a -a#as'\<rightarrow>\<^bsub>cd\<^esub> n''` have "sourcenode a -a#as'\<rightarrow>* n''"
    by(rule DynPDG_cdep_edge_CFG_path(1))
  from `n'' -as''\<rightarrow>\<^sub>d* n'` have "n'' -as''\<rightarrow>* n'" by(rule DynPDG_path_CFG_path)
  show ?case
  proof(cases "as'' = []")
    case True
    with `n'' -as''\<rightarrow>* n'` have "n'' = n'" by (auto elim: DynPDG.dependent_live_vars.cases)
    with `sourcenode a -a#as'\<rightarrow>* n''` True
    show ?thesis by(fastforce intro:path_targetnode[THEN sym])
  next
    case False
    with `n'' -as''\<rightarrow>* n'` have "n' = last(targetnodes as'')"
      by(fastforce intro:path_targetnode[THEN sym])
    with False show ?thesis by(fastforce simp:targetnodes_def)
  qed
qed simp_all


lemma dependent_live_vars_Use_cases:
  "\<lbrakk>(V,as',as) \<in> dependent_live_vars n'; n -as\<rightarrow>* n'\<rbrakk>
  \<Longrightarrow> \<exists>nx as''. as = as'@as'' \<and> n -as'\<rightarrow>* nx \<and> nx -as''\<rightarrow>\<^sub>d* n' \<and> V \<in> Use nx \<and> 
               (\<forall>n'' \<in> set (sourcenodes as'). V \<notin> Def n'')"
proof(induct arbitrary:n rule:dependent_live_vars.induct)
  case (dep_vars_Use V)
  from `n -[]\<rightarrow>* n'` have "valid_node n'" by(rule path_valid_node(2))
  hence "n' -[]\<rightarrow>\<^sub>d* n'" by(rule DynPDG_path_Nil)
  with `V \<in> Use n'` `n -[]\<rightarrow>* n'` show ?case 
    by(auto simp:sourcenodes_def)
next
  case (dep_vars_Cons_cdep V a as' n'' as'' n)
  from `n -a#as'@as''\<rightarrow>* n'` have "sourcenode a = n"
    by(auto elim:path.cases)
  from `sourcenode a -a#as'\<rightarrow>\<^bsub>cd\<^esub> n''` have "sourcenode a -a#as'\<rightarrow>* n''"
    by(rule DynPDG_cdep_edge_CFG_path(1))
  hence "valid_edge a" by(auto elim:path.cases) 
  hence "sourcenode a -[]\<rightarrow>* sourcenode a" by(fastforce intro:empty_path)
  from `sourcenode a -a#as'\<rightarrow>\<^bsub>cd\<^esub> n''` have "sourcenode a -a#as'\<rightarrow>\<^sub>d* n''"
    by(rule DynPDG_path_cdep)
  with `n'' -as''\<rightarrow>\<^sub>d* n'` have "sourcenode a -(a#as')@as''\<rightarrow>\<^sub>d* n'"
    by(rule DynPDG_path_Append)
  with `sourcenode a -[]\<rightarrow>* sourcenode a` `V \<in> Use (sourcenode a)` `sourcenode a = n`
  show ?case by(auto simp:sourcenodes_def)
next
  case(dep_vars_Cons_ddep V as' as V' a n)
  note ddep = `sourcenode a -{V}a#as'\<rightarrow>\<^bsub>dd\<^esub> last (targetnodes (a#as'))`
  note IH = `\<And>n. n -as\<rightarrow>* n'
    \<Longrightarrow> \<exists>nx as''. as = as'@as'' \<and> n -as'\<rightarrow>* nx \<and> nx -as''\<rightarrow>\<^sub>d* n' \<and> 
                   V \<in> Use nx \<and> (\<forall>n''\<in>set (sourcenodes as'). V \<notin> Def n'')`
  from `n -a#as\<rightarrow>* n'` have "n -[]@a#as\<rightarrow>* n'" by simp
  hence "n = sourcenode a" and "targetnode a -as\<rightarrow>* n'" and "valid_edge a"
    by(fastforce dest:path_split)+
  hence "n -[]\<rightarrow>* n" 
    by(fastforce intro:empty_path simp:valid_node_def)
  from IH[OF `targetnode a -as\<rightarrow>* n'`]
  have "\<exists>nx as''. as = as'@as'' \<and> targetnode a -as'\<rightarrow>* nx \<and> nx -as''\<rightarrow>\<^sub>d* n' \<and> 
                  V \<in> Use nx \<and> (\<forall>n''\<in>set (sourcenodes as'). V \<notin> Def n'')" .
  then obtain nx'' as'' where "targetnode a -as'\<rightarrow>* nx''"
    and "nx'' -as''\<rightarrow>\<^sub>d* n'" and "as = as'@as''" by blast
  have "last (targetnodes (a#as')) -as''\<rightarrow>\<^sub>d* n'"
  proof(cases as')
    case Nil
    with `targetnode a -as'\<rightarrow>* nx''` have "nx'' = targetnode a"
      by(auto elim:path.cases)
    with `nx'' -as''\<rightarrow>\<^sub>d* n'` Nil show ?thesis by(simp add:targetnodes_def)
  next
    case (Cons ax asx)
    hence "last (targetnodes (a#as')) = last (targetnodes as')"
      by(simp add:targetnodes_def)
    from Cons `targetnode a -as'\<rightarrow>* nx''` have "last (targetnodes as') = nx''"
      by(fastforce intro:path_targetnode)
    with `last (targetnodes (a#as')) = last (targetnodes as')` `nx'' -as''\<rightarrow>\<^sub>d* n'`
    show ?thesis by simp
  qed
  with ddep `as = as'@as''` have "sourcenode a -a#as\<rightarrow>\<^sub>d* n'"
    by(fastforce dest:DynPDG_path_ddep DynPDG_path_Append)
  with `V' \<in> Use (sourcenode a)` `n = sourcenode a` `n -[]\<rightarrow>* n`
  show ?case by(auto simp:sourcenodes_def)
next
  case (dep_vars_Cons_keep V as' as a n)
  note no_dep = `\<not> sourcenode a -{V}a#as'\<rightarrow>\<^bsub>dd\<^esub> last (targetnodes (a#as'))`
  note IH = `\<And>n. n -as\<rightarrow>* n'
    \<Longrightarrow> \<exists>nx as''. (as = as'@as'') \<and> (n -as'\<rightarrow>* nx) \<and> (nx -as''\<rightarrow>\<^sub>d* n') \<and> 
                   V \<in> Use nx \<and> (\<forall>n''\<in>set (sourcenodes as'). V \<notin> Def n'')`
  from `n -a#as\<rightarrow>* n'` have "n = sourcenode a" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* n'" by(auto elim:path_split_Cons)
  from IH[OF `targetnode a -as\<rightarrow>* n'`]
  have "\<exists>nx as''. as = as'@as'' \<and> targetnode a -as'\<rightarrow>* nx \<and> nx -as''\<rightarrow>\<^sub>d* n' \<and> 
               V \<in> Use nx \<and> (\<forall>n''\<in>set (sourcenodes as'). V \<notin> Def n'')" .
  then obtain nx'' as'' where "V \<in> Use nx''"
    and "\<forall>n''\<in>set (sourcenodes as'). V \<notin> Def n''" and "targetnode a -as'\<rightarrow>* nx''"
    and "nx'' -as''\<rightarrow>\<^sub>d* n'" and "as = as'@as''" by blast
  from `valid_edge a` `targetnode a -as'\<rightarrow>* nx''` have "sourcenode a -a#as'\<rightarrow>* nx''"
    by(fastforce intro:Cons_path)
  hence "last(targetnodes (a#as')) = nx''" by(fastforce dest:path_targetnode)
  { assume "V \<in> Def (sourcenode a)"
    with `V \<in> Use nx''` `sourcenode a -a#as'\<rightarrow>* nx''`
      `\<forall>n''\<in>set (sourcenodes as'). V \<notin> Def n''` 
    have "(sourcenode a) influences V in nx'' via a#as'"
      by(simp add:dyn_data_dependence_def sourcenodes_def)
    with no_dep `last(targetnodes (a#as')) = nx''`
      `\<forall>n''\<in>set (sourcenodes as'). V \<notin> Def n''` `V \<in> Def (sourcenode a)`
    have False by(fastforce dest:DynPDG_ddep_edge) }
  with `\<forall>n''\<in>set (sourcenodes as'). V \<notin> Def n''` 
  have "\<forall>n''\<in>set (sourcenodes (a#as')). V \<notin> Def n''"
    by(fastforce simp:sourcenodes_def)
  with `V \<in> Use nx''` `sourcenode a -a#as'\<rightarrow>* nx''` `nx'' -as''\<rightarrow>\<^sub>d* n'`
    `as = as'@as''` `n = sourcenode a` show ?case by fastforce
qed


lemma dependent_live_vars_dependent_edge:
  assumes "(V,as',as) \<in> dependent_live_vars n'" 
  and "targetnode a -as\<rightarrow>* n'"
  and "V \<in> Def (sourcenode a)" and "valid_edge a"
  obtains nx as'' where "as = as'@as''" and "sourcenode a -{V}a#as'\<rightarrow>\<^bsub>dd\<^esub> nx"
  and "nx -as''\<rightarrow>\<^sub>d* n'"
proof(atomize_elim)
  from `(V,as',as) \<in> dependent_live_vars n'` `targetnode a -as\<rightarrow>* n'`
  have "\<exists>nx as''. as = as'@as'' \<and> targetnode a -as'\<rightarrow>* nx \<and> nx -as''\<rightarrow>\<^sub>d* n' \<and> 
    V \<in> Use nx \<and> (\<forall>n'' \<in> set (sourcenodes as'). V \<notin> Def n'')"
    by(rule dependent_live_vars_Use_cases)
  then obtain nx as'' where "V \<in> Use nx"
    and "\<forall>n''\<in> set(sourcenodes as'). V \<notin> Def n''"
    and "targetnode a -as'\<rightarrow>* nx" and "nx -as''\<rightarrow>\<^sub>d* n'"
    and "as = as'@as''" by blast
  from `targetnode a -as'\<rightarrow>* nx` `valid_edge a` have "sourcenode a -a#as'\<rightarrow>* nx"
    by(fastforce intro:Cons_path)
  with `V \<in> Def (sourcenode a)` `V \<in> Use nx` 
    `\<forall>n''\<in> set(sourcenodes as'). V \<notin> Def n''` 
  have "sourcenode a influences V in nx via a#as'"
    by(auto simp:dyn_data_dependence_def sourcenodes_def)
  hence "sourcenode a -{V}a#as'\<rightarrow>\<^bsub>dd\<^esub> nx" by(rule DynPDG_ddep_edge)
  with `nx -as''\<rightarrow>\<^sub>d* n'` `as = as'@as''` 
  show "\<exists>as'' nx. (as = as'@as'') \<and> (sourcenode a -{V}a#as'\<rightarrow>\<^bsub>dd\<^esub> nx) \<and> 
    (nx -as''\<rightarrow>\<^sub>d* n')" by fastforce
qed



lemma dependent_live_vars_same_pathsI:
  assumes "V \<in> Use n'"
  shows "\<lbrakk>\<forall>as' a as''. as = as'@a#as'' \<longrightarrow> \<not> sourcenode a -{V}a#as''\<rightarrow>\<^bsub>dd\<^esub> n'; 
          as \<noteq> [] \<longrightarrow> n' = last(targetnodes as)\<rbrakk>
  \<Longrightarrow> (V,as,as) \<in> dependent_live_vars n'"
proof(induct as)
  case Nil
  from `V \<in> Use n'` show ?case by(rule dep_vars_Use)
next
  case (Cons ax asx)
  note lastnode = `ax#asx \<noteq> [] \<longrightarrow> n' = last (targetnodes (ax#asx))`
  note IH = `\<lbrakk>\<forall>as' a as''. asx = as'@a#as'' \<longrightarrow>
                           \<not> sourcenode a -{V}a#as''\<rightarrow>\<^bsub>dd\<^esub> n';
             asx \<noteq> [] \<longrightarrow> n' = last (targetnodes asx)\<rbrakk>
           \<Longrightarrow> (V, asx, asx) \<in> dependent_live_vars n'`
  from `\<forall>as' a as''. ax#asx = as'@a#as'' \<longrightarrow> \<not> sourcenode a -{V}a#as''\<rightarrow>\<^bsub>dd\<^esub> n'`
  have all':"\<forall>as' a as''. asx = as'@a#as'' \<longrightarrow> \<not> sourcenode a -{V}a#as''\<rightarrow>\<^bsub>dd\<^esub> n'"
    and "\<not> sourcenode ax -{V}ax#asx\<rightarrow>\<^bsub>dd\<^esub> n'"
    by simp_all
  show ?case
  proof(cases "asx = []")
    case True
    from `V \<in> Use n'` have "(V,[],[]) \<in> dependent_live_vars n'" by(rule dep_vars_Use)
    with `\<not> sourcenode ax -{V}ax#asx\<rightarrow>\<^bsub>dd\<^esub> n'` True lastnode
    have "(V,[ax],[ax]) \<in> dependent_live_vars n'"
      by(fastforce intro:dep_vars_Cons_keep)
    with True show ?thesis by simp
  next
    case False
    with lastnode have "asx \<noteq> [] \<longrightarrow> n' = last (targetnodes asx)"
      by(simp add:targetnodes_def)
    from IH[OF all' this] have "(V, asx, asx) \<in> dependent_live_vars n'" .
    with `\<not> sourcenode ax -{V}ax#asx\<rightarrow>\<^bsub>dd\<^esub> n'` lastnode 
    show ?thesis by(fastforce intro:dep_vars_Cons_keep)
  qed
qed


lemma dependent_live_vars_same_pathsD:
  "\<lbrakk>(V,as,as) \<in> dependent_live_vars n';  as \<noteq> [] \<longrightarrow> n' = last(targetnodes as)\<rbrakk>
  \<Longrightarrow> V \<in> Use n' \<and> (\<forall>as' a as''. as = as'@a#as'' \<longrightarrow>
                       \<not> sourcenode a -{V}a#as''\<rightarrow>\<^bsub>dd\<^esub> n')"
proof(induct as)
  case Nil
  have "(V,[],[]) \<in> dependent_live_vars n'" by fact
  thus ?case
    by(fastforce elim:dependent_live_vars.cases simp:targetnodes_def sourcenodes_def)
next
  case (Cons ax asx)
  note IH = `\<lbrakk>(V,asx,asx) \<in> dependent_live_vars n'; 
              asx \<noteq> [] \<longrightarrow> n' = last (targetnodes asx)\<rbrakk>
    \<Longrightarrow> V \<in> Use n' \<and> (\<forall>as' a as''. asx = as'@a#as'' \<longrightarrow>
                          \<not> sourcenode a -{V}a#as''\<rightarrow>\<^bsub>dd\<^esub> n')`
  from `(V,ax#asx,ax#asx) \<in> dependent_live_vars n'`
  have "(V,asx,asx) \<in> dependent_live_vars n'"
    and "\<not> sourcenode ax -{V}ax#asx\<rightarrow>\<^bsub>dd\<^esub> last(targetnodes (ax#asx))"
    by(auto elim:dependent_live_vars.cases)
  from `ax#asx \<noteq> [] \<longrightarrow> n' = last (targetnodes (ax#asx))`
  have "n' = last (targetnodes (ax#asx))" by simp
  show ?case
  proof(cases "asx = []")
    case True
    with `(V,asx,asx) \<in> dependent_live_vars n'` have "V \<in> Use n'"
      by(fastforce elim:dependent_live_vars.cases)
    from `\<not> sourcenode ax -{V}ax#asx\<rightarrow>\<^bsub>dd\<^esub> last(targetnodes (ax#asx))` 
      True `n' = last (targetnodes (ax#asx))`
    have "\<forall>as' a as''. ax#asx = as'@a#as'' \<longrightarrow> \<not> sourcenode a -{V}a#as''\<rightarrow>\<^bsub>dd\<^esub> n'"
      by auto(case_tac as',auto)
    with `V \<in> Use n'` show ?thesis by simp
  next
    case False
    with `n' = last (targetnodes (ax#asx))`
    have "asx \<noteq> [] \<longrightarrow> n' = last (targetnodes asx)"
      by(simp add:targetnodes_def)
    from IH[OF `(V,asx,asx) \<in> dependent_live_vars n'` this] 
    have "V \<in> Use n' \<and> (\<forall>as' a as''. asx = as'@a#as'' \<longrightarrow>
                            \<not> sourcenode a -{V}a#as''\<rightarrow>\<^bsub>dd\<^esub> n')" .
    with `\<not> sourcenode ax -{V}ax#asx\<rightarrow>\<^bsub>dd\<^esub> last(targetnodes (ax#asx))`
      `n' = last (targetnodes (ax#asx))` have "V \<in> Use n'"
      and "\<forall>as' a as''. ax#asx = as'@a#as'' \<longrightarrow>
                            \<not> sourcenode a -{V}a#as''\<rightarrow>\<^bsub>dd\<^esub> n'"
      by auto(case_tac as',auto)
    thus ?thesis by simp
  qed
qed


lemma dependent_live_vars_same_paths:
  "as \<noteq> [] \<longrightarrow> n' = last(targetnodes as) \<Longrightarrow>
  (V,as,as) \<in> dependent_live_vars n' = 
  (V \<in> Use n' \<and> (\<forall>as' a as''. as = as'@a#as'' \<longrightarrow>
                       \<not> sourcenode a -{V}a#as''\<rightarrow>\<^bsub>dd\<^esub> n'))"
by(fastforce intro!:dependent_live_vars_same_pathsD dependent_live_vars_same_pathsI)


lemma dependent_live_vars_cdep_empty_fst:
assumes "n'' -as\<rightarrow>\<^bsub>cd\<^esub> n'" and "V' \<in> Use n''"
  shows "(V',[],as) \<in> dependent_live_vars n'"
proof(cases as)
  case Nil
  with `n'' -as\<rightarrow>\<^bsub>cd\<^esub> n'` show ?thesis
    by(fastforce elim:DynPDG_edge.cases dest:dyn_control_dependence_path)
next
  case (Cons ax asx)
  with `n'' -as\<rightarrow>\<^bsub>cd\<^esub> n'` have "sourcenode ax = n''"
    by(auto dest:DynPDG_cdep_edge_CFG_path elim:path.cases)
  from `n'' -as\<rightarrow>\<^bsub>cd\<^esub> n'` have "valid_node n'"
    by(fastforce intro:path_valid_node(2) DynPDG_cdep_edge_CFG_path(1))
  from Cons `n'' -as\<rightarrow>\<^bsub>cd\<^esub> n'` have "last(targetnodes as) = n'"
    by(fastforce intro:path_targetnode dest:DynPDG_cdep_edge_CFG_path)
  with Cons `n'' -as\<rightarrow>\<^bsub>cd\<^esub> n'` `V' \<in> Use n''` `sourcenode ax = n''` `valid_node n'`
  have "(V', [], ax#asx@[]) \<in> dependent_live_vars n'"
    by(fastforce intro:dep_vars_Cons_cdep DynPDG_path_Nil)
  with Cons show ?thesis by simp
qed
  

lemma dependent_live_vars_ddep_empty_fst:
  assumes "n'' -{V}as\<rightarrow>\<^bsub>dd\<^esub> n'" and "V' \<in> Use n''"
  shows "(V',[],as) \<in> dependent_live_vars n'"
proof(cases as)
  case Nil
  with `n'' -{V}as\<rightarrow>\<^bsub>dd\<^esub> n'` show ?thesis
    by(fastforce elim:DynPDG_edge.cases simp:dyn_data_dependence_def)
next
  case (Cons ax asx)
  with `n'' -{V}as\<rightarrow>\<^bsub>dd\<^esub> n'` have "sourcenode ax = n''"
    by(auto dest:DynPDG_ddep_edge_CFG_path elim:path.cases)
  from Cons `n'' -{V}as\<rightarrow>\<^bsub>dd\<^esub> n'` have "last(targetnodes as) = n'"
    by(fastforce intro:path_targetnode elim:DynPDG_ddep_edge_CFG_path(1))
  from Cons `n'' -{V}as\<rightarrow>\<^bsub>dd\<^esub> n'` have all:"\<forall>as' a as''. asx = as'@a#as'' \<longrightarrow>
                             \<not> sourcenode a -{V}a#as''\<rightarrow>\<^bsub>dd\<^esub> n'"
    by(fastforce dest:DynPDG_ddep_edge_no_shorter_ddep_edge)
  from `n'' -{V}as\<rightarrow>\<^bsub>dd\<^esub> n'` have "V \<in> Use n'" 
    by(auto elim!:DynPDG_edge.cases simp:dyn_data_dependence_def)
  from Cons `n'' -{V}as\<rightarrow>\<^bsub>dd\<^esub> n'` have "as \<noteq> [] \<longrightarrow> n' = last(targetnodes as)"
    by(fastforce dest:DynPDG_ddep_edge_CFG_path path_targetnode)
  with Cons have "asx \<noteq> [] \<longrightarrow> n' = last(targetnodes asx)"
    by(fastforce simp:targetnodes_def)
  with all `V \<in> Use n'` have "(V,asx,asx) \<in> dependent_live_vars n'"
    by -(rule dependent_live_vars_same_pathsI)
  with `V' \<in> Use n''` `n'' -{V}as\<rightarrow>\<^bsub>dd\<^esub> n'` `last(targetnodes as) = n'`
    Cons `sourcenode ax = n''` show ?thesis
    by(fastforce intro:dep_vars_Cons_ddep)
qed




lemma ddep_dependent_live_vars_keep_notempty:
  assumes "n -{V}a#as\<rightarrow>\<^bsub>dd\<^esub> n''" and "as' \<noteq> []"
  and "(V,as'',as') \<in> dependent_live_vars n'"
  shows "(V,as@as'',as@as') \<in> dependent_live_vars n'"
proof -
  from `n -{V}a#as\<rightarrow>\<^bsub>dd\<^esub> n''` have "\<forall>n'' \<in> set (sourcenodes as). V \<notin> Def n''"
    by(auto elim:DynPDG_edge.cases simp:dyn_data_dependence_def)
  with `(V,as'',as') \<in> dependent_live_vars n'` show ?thesis
  proof(induct as)
    case Nil thus ?case by simp
  next
    case (Cons ax asx)
    note IH = `\<lbrakk>(V,as'',as') \<in> dependent_live_vars n';
                \<forall>n''\<in>set (sourcenodes asx). V \<notin> Def n''\<rbrakk>
               \<Longrightarrow> (V, asx@as'',asx@as') \<in> dependent_live_vars n'`
    from `\<forall>n''\<in>set (sourcenodes (ax#asx)). V \<notin> Def n''`
    have "\<forall>n''\<in>set (sourcenodes asx). V \<notin> Def n''"
      by(auto simp:sourcenodes_def)
    from IH[OF `(V,as'',as') \<in> dependent_live_vars n'` this]
    have "(V,asx@as'',asx@as') \<in> dependent_live_vars n'" .
    from `as' \<noteq> []` `(V,as'',as') \<in> dependent_live_vars n'`
    have "n' = last(targetnodes as')" 
      by(fastforce intro:dependent_live_vars_lastnode)
    with `as' \<noteq> []` have "n' = last(targetnodes (ax#asx@as'))"
      by(fastforce simp:targetnodes_def)
    have "\<not> sourcenode ax -{V}ax#asx@as''\<rightarrow>\<^bsub>dd\<^esub> last(targetnodes (ax#asx@as''))"
    proof
      assume "sourcenode ax -{V}ax#asx@as''\<rightarrow>\<^bsub>dd\<^esub> last(targetnodes (ax#asx@as''))"
      hence "sourcenode ax -{V}ax#asx@as''\<rightarrow>\<^bsub>dd\<^esub> last(targetnodes (ax#asx@as''))"
        by simp
      with `\<forall>n''\<in>set (sourcenodes (ax#asx)). V \<notin> Def n''`
      show False
        by(fastforce elim:DynPDG_edge.cases 
                    simp:dyn_data_dependence_def sourcenodes_def)
    qed
    with `(V,asx@as'',asx@as') \<in> dependent_live_vars n'` 
      `n' = last(targetnodes (ax#asx@as'))`
    show ?case by(fastforce intro:dep_vars_Cons_keep)
  qed
qed



lemma dependent_live_vars_cdep_dependent_live_vars:
  assumes "n'' -as''\<rightarrow>\<^bsub>cd\<^esub> n'" and "(V',as',as) \<in> dependent_live_vars n''"
  shows "(V',as',as@as'') \<in> dependent_live_vars n'"
proof -
  from `n'' -as''\<rightarrow>\<^bsub>cd\<^esub> n'` have "as'' \<noteq> []"
    by(fastforce elim:DynPDG_edge.cases dest:dyn_control_dependence_path)
  with `n'' -as''\<rightarrow>\<^bsub>cd\<^esub> n'` have "last(targetnodes as'') = n'"
    by(fastforce intro:path_targetnode elim:DynPDG_cdep_edge_CFG_path(1))
  from `(V',as',as) \<in> dependent_live_vars n''` show ?thesis
  proof(induct rule:dependent_live_vars.induct)
    case (dep_vars_Use V')
    from `V' \<in> Use n''` `n'' -as''\<rightarrow>\<^bsub>cd\<^esub> n'` `last(targetnodes as'') = n'` show ?case
      by(fastforce intro:dependent_live_vars_cdep_empty_fst simp:targetnodes_def)
  next
    case (dep_vars_Cons_cdep V a as' nx asx)
    from `n'' -as''\<rightarrow>\<^bsub>cd\<^esub> n'` have "n'' -as''\<rightarrow>\<^sub>d* n'" by(rule DynPDG_path_cdep)
    with `nx -asx\<rightarrow>\<^sub>d* n''` have "nx -asx@as''\<rightarrow>\<^sub>d* n'"
      by -(rule DynPDG_path_Append)
    with `V \<in> Use (sourcenode a)` `(sourcenode a) -a#as'\<rightarrow>\<^bsub>cd\<^esub> nx`
    show ?case by(fastforce intro:dependent_live_vars.dep_vars_Cons_cdep)
  next
    case (dep_vars_Cons_ddep V as' as V' a)
    from `as'' \<noteq> []` `last(targetnodes as'') = n'`
    have "n' = last(targetnodes ((a#as)@as''))"
      by(simp add:targetnodes_def)
    with dep_vars_Cons_ddep
    show ?case by(fastforce intro:dependent_live_vars.dep_vars_Cons_ddep)
  next
    case (dep_vars_Cons_keep V as' as a)
    from `as'' \<noteq> []` `last(targetnodes as'') = n'`
    have "n' = last(targetnodes ((a#as)@as''))"
      by(simp add:targetnodes_def)
    with dep_vars_Cons_keep
    show ?case by(fastforce intro:dependent_live_vars.dep_vars_Cons_keep)
  qed
qed


lemma dependent_live_vars_ddep_dependent_live_vars:
  assumes "n'' -{V}as''\<rightarrow>\<^bsub>dd\<^esub> n'" and "(V',as',as) \<in> dependent_live_vars n''"
  shows "(V',as',as@as'') \<in> dependent_live_vars n'"
proof -
  from `n'' -{V}as''\<rightarrow>\<^bsub>dd\<^esub> n'` have "as'' \<noteq> []"
    by(rule DynPDG_ddep_edge_CFG_path(2))
  with `n'' -{V}as''\<rightarrow>\<^bsub>dd\<^esub> n'` have "last(targetnodes as'') = n'"
    by(fastforce intro:path_targetnode elim:DynPDG_ddep_edge_CFG_path(1))
  from `n'' -{V}as''\<rightarrow>\<^bsub>dd\<^esub> n'` have notExit:"n' \<noteq> (_Exit_)" 
    by(fastforce elim:DynPDG_edge.cases simp:dyn_data_dependence_def)
  from `(V',as',as) \<in> dependent_live_vars n''` show ?thesis
  proof(induct rule:dependent_live_vars.induct)
    case (dep_vars_Use V')
    from `V' \<in> Use n''` `n'' -{V}as''\<rightarrow>\<^bsub>dd\<^esub> n'` `last(targetnodes as'') = n'` show ?case
      by(fastforce intro:dependent_live_vars_ddep_empty_fst simp:targetnodes_def)
  next
    case (dep_vars_Cons_cdep V' a as' nx asx)
    from `n'' -{V}as''\<rightarrow>\<^bsub>dd\<^esub> n'` have "n'' -as''\<rightarrow>\<^sub>d* n'" by(rule DynPDG_path_ddep)
    with `nx -asx\<rightarrow>\<^sub>d* n''` have "nx -asx@as''\<rightarrow>\<^sub>d* n'"
      by -(rule DynPDG_path_Append)
    with `V' \<in> Use (sourcenode a)` `sourcenode a -a#as'\<rightarrow>\<^bsub>cd\<^esub> nx` notExit
    show ?case by(fastforce intro:dependent_live_vars.dep_vars_Cons_cdep)
  next
    case (dep_vars_Cons_ddep V as' as V' a)
    from `as'' \<noteq> []` `last(targetnodes as'') = n'`
    have "n' = last(targetnodes ((a#as)@as''))"
      by(simp add:targetnodes_def)
    with dep_vars_Cons_ddep
    show ?case by(fastforce intro:dependent_live_vars.dep_vars_Cons_ddep)
  next
    case (dep_vars_Cons_keep V as' as a)
    from `as'' \<noteq> []` `last(targetnodes as'') = n'`
    have "n' = last(targetnodes ((a#as)@as''))"
      by(simp add:targetnodes_def)
    with dep_vars_Cons_keep
    show ?case by(fastforce intro:dependent_live_vars.dep_vars_Cons_keep)
  qed
qed


lemma dependent_live_vars_dep_dependent_live_vars:
  "\<lbrakk>n'' -as''\<rightarrow>\<^sub>d* n'; (V',as',as) \<in> dependent_live_vars n''\<rbrakk>
  \<Longrightarrow> (V',as',as@as'') \<in> dependent_live_vars n'"
proof(induct rule:DynPDG_path.induct)
  case (DynPDG_path_Nil n) thus ?case by simp
next
  case (DynPDG_path_Append_cdep n asx n'' asx' n')
  note IH = `(V', as', as) \<in> dependent_live_vars n \<Longrightarrow>
             (V', as', as @ asx) \<in> dependent_live_vars n''`
  from IH[OF `(V',as',as) \<in> dependent_live_vars n`]
  have "(V',as',as@asx) \<in> dependent_live_vars n''" .
  with `n'' -asx'\<rightarrow>\<^bsub>cd\<^esub> n'` have "(V',as',(as@asx)@asx') \<in> dependent_live_vars n'"
    by(rule dependent_live_vars_cdep_dependent_live_vars)
  thus ?case by simp
next
  case (DynPDG_path_Append_ddep n asx n'' V asx' n')
  note IH = `(V', as', as) \<in> dependent_live_vars n \<Longrightarrow>
             (V', as', as @ asx) \<in> dependent_live_vars n''`
  from IH[OF `(V',as',as) \<in> dependent_live_vars n`]
  have "(V',as',as@asx) \<in> dependent_live_vars n''" .
  with `n'' -{V}asx'\<rightarrow>\<^bsub>dd\<^esub> n'` have "(V',as',(as@asx)@asx') \<in> dependent_live_vars n'"
    by(rule dependent_live_vars_ddep_dependent_live_vars)
  thus ?case by simp
qed

end


end
