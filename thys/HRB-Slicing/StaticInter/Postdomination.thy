section {* Postdomination *}

theory Postdomination imports CFGExit begin

text {* For static interprocedural slicing, we only consider standard control 
  dependence, hence we only need standard postdomination. *}

locale Postdomination = CFGExit sourcenode targetnode kind valid_edge Entry 
    get_proc get_return_edges procs Main Exit
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind" 
  and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')")  and get_proc :: "'node \<Rightarrow> 'pname"
  and get_return_edges :: "'edge \<Rightarrow> 'edge set"
  and procs :: "('pname \<times> 'var list \<times> 'var list) list" and Main :: "'pname"
  and Exit::"'node"  ("'('_Exit'_')") +
  assumes Entry_path:"valid_node n \<Longrightarrow> \<exists>as. (_Entry_) -as\<rightarrow>\<^sub>\<surd>* n"
  and Exit_path:"valid_node n \<Longrightarrow> \<exists>as. n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)"
  and method_exit_unique:
    "\<lbrakk>method_exit n; method_exit n'; get_proc n = get_proc n'\<rbrakk> \<Longrightarrow> n = n'"

begin

lemma get_return_edges_unique:
  assumes "valid_edge a" and "a' \<in> get_return_edges a" and "a'' \<in> get_return_edges a"
  shows "a' = a''"
proof -
  from `valid_edge a` `a' \<in> get_return_edges a` 
  obtain Q r p fs where "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    by(fastforce dest!:only_call_get_return_edges)
  with `valid_edge a` `a' \<in> get_return_edges a` obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    by(fastforce dest!:call_return_edges)
  from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'" 
    by(rule get_return_edges_valid)
  from this `kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` have "get_proc (sourcenode a') = p" 
    by(rule get_proc_return)
  from `valid_edge a'` `kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` have "method_exit (sourcenode a')"
    by(fastforce simp:method_exit_def)
  from `valid_edge a` `a'' \<in> get_return_edges a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
  obtain Q'' f'' where "kind a'' = Q''\<hookleftarrow>\<^bsub>p\<^esub>f''" by(fastforce dest!:call_return_edges)
  from `valid_edge a` `a'' \<in> get_return_edges a` have "valid_edge a''" 
    by(rule get_return_edges_valid)
  from this `kind a'' = Q''\<hookleftarrow>\<^bsub>p\<^esub>f''` have "get_proc (sourcenode a'') = p" 
    by(rule get_proc_return)
  from `valid_edge a''` `kind a'' = Q''\<hookleftarrow>\<^bsub>p\<^esub>f''` have "method_exit (sourcenode a'')"
    by(fastforce simp:method_exit_def)
  with `method_exit (sourcenode a')` `get_proc (sourcenode a') = p`
    `get_proc (sourcenode a'') = p` have "sourcenode a' = sourcenode a''"
    by(fastforce elim!:method_exit_unique)
  from `valid_edge a` `a' \<in> get_return_edges a`
  obtain ax' where "valid_edge ax'" and "sourcenode ax' = sourcenode a"
    and "targetnode ax' = targetnode a'" and "intra_kind(kind ax')"
    by -(drule call_return_node_edge,auto simp:intra_kind_def)
  from `valid_edge a` `a'' \<in> get_return_edges a`
  obtain ax'' where "valid_edge ax''" and "sourcenode ax'' = sourcenode a"
    and "targetnode ax'' = targetnode a''" and "intra_kind(kind ax'')"
    by -(drule call_return_node_edge,auto simp:intra_kind_def)
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `valid_edge ax'` 
    `sourcenode ax' = sourcenode a` `intra_kind(kind ax')`
    `valid_edge ax''` `sourcenode ax'' = sourcenode a` `intra_kind(kind ax'')`
  have "ax' = ax''" by -(drule call_only_one_intra_edge,auto)
  with `targetnode ax' = targetnode a'` `targetnode ax'' = targetnode a''`
  have "targetnode a' = targetnode a''" by simp
  with `valid_edge a'` `valid_edge a''` `sourcenode a' = sourcenode a''`
  show ?thesis by(rule edge_det)
qed


definition postdominate :: "'node \<Rightarrow> 'node \<Rightarrow> bool" ("_ postdominates _" [51,0])
where postdominate_def:"n' postdominates n \<equiv> 
  (valid_node n \<and> valid_node n' \<and>
  (\<forall>as pex. (n -as\<rightarrow>\<^sub>\<iota>* pex \<and> method_exit pex) \<longrightarrow> n' \<in> set (sourcenodes as)))"


lemma postdominate_implies_inner_path: 
  assumes "n' postdominates n" 
  obtains as where "n -as\<rightarrow>\<^sub>\<iota>* n'" and "n' \<notin> set (sourcenodes as)"
proof(atomize_elim)
  from `n' postdominates n` have "valid_node n"
    and all:"\<forall>as pex. (n -as\<rightarrow>\<^sub>\<iota>* pex \<and> method_exit pex) \<longrightarrow> n' \<in> set (sourcenodes as)"
    by(auto simp:postdominate_def)
  from `valid_node n` obtain asx where "n -asx\<rightarrow>\<^sub>\<surd>* (_Exit_)" by(auto dest:Exit_path)
  then obtain as where "n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)"
    and "\<forall>a \<in> set as. intra_kind(kind a) \<or> (\<exists>Q f p. kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f)"
    by -(erule valid_Exit_path_descending_path)
  show "\<exists>as. n -as\<rightarrow>\<^sub>\<iota>* n' \<and> n' \<notin> set (sourcenodes as)"
  proof(cases "\<exists>a \<in> set as. \<exists>Q f p. kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f")
    case True
    then obtain asx ax asx' where [simp]:"as = asx@ax#asx'" 
      and "\<exists>Q f p. kind ax = Q\<hookleftarrow>\<^bsub>p\<^esub>f" and "\<forall>a \<in> set asx. \<forall>Q f p. kind a \<noteq> Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      by -(erule split_list_first_propE,simp)
    with `\<forall>a \<in> set as. intra_kind(kind a) \<or> (\<exists>Q f p. kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f)`
    have "\<forall>a \<in> set asx. intra_kind(kind a)" by auto
    from `n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)` have "n -asx\<rightarrow>\<^sub>\<surd>* sourcenode ax"
      and "valid_edge ax" by(auto dest:vp_split)
    from `n -asx\<rightarrow>\<^sub>\<surd>* sourcenode ax` `\<forall>a \<in> set asx. intra_kind(kind a)`
    have "n -asx\<rightarrow>\<^sub>\<iota>* sourcenode ax" by(simp add:vp_def intra_path_def)
    from `valid_edge ax` `\<exists>Q f p. kind ax = Q\<hookleftarrow>\<^bsub>p\<^esub>f` 
    have "method_exit (sourcenode ax)" by(fastforce simp:method_exit_def)
    with `n -asx\<rightarrow>\<^sub>\<iota>* sourcenode ax` all have "n' \<in> set (sourcenodes asx)" by fastforce
    then obtain xs ys where "sourcenodes asx = xs@n'#ys" and "n' \<notin> set xs"
      by(fastforce dest:split_list_first)
    then obtain as' a as'' where "xs = sourcenodes as'"
      and [simp]:"asx = as'@a#as''" and "sourcenode a = n'"
      by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
    from `n -asx\<rightarrow>\<^sub>\<iota>* sourcenode ax` have "n -as'\<rightarrow>\<^sub>\<iota>* sourcenode a"
      by(fastforce dest:path_split simp:intra_path_def)
    with `sourcenode a = n'` `n' \<notin> set xs` `xs = sourcenodes as'`
    show ?thesis by fastforce
  next
    case False
    with `\<forall>a \<in> set as. intra_kind(kind a) \<or> (\<exists>Q f p. kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f)`
    have "\<forall>a \<in> set as. intra_kind(kind a)" by fastforce
    with `n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)` all have "n' \<in> set (sourcenodes as)"
      by(auto simp:vp_def intra_path_def simp:method_exit_def)
    then obtain xs ys where "sourcenodes as = xs@n'#ys" and "n' \<notin> set xs"
      by(fastforce dest:split_list_first)
    then obtain as' a as'' where "xs = sourcenodes as'"
      and [simp]:"as = as'@a#as''" and "sourcenode a = n'"
      by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
    from `n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)` `\<forall>a \<in> set as. intra_kind(kind a)` `as = as'@a#as''`
    have "n -as'\<rightarrow>\<^sub>\<iota>* sourcenode a"
      by(fastforce dest:path_split simp:vp_def intra_path_def)
    with `sourcenode a = n'` `n' \<notin> set xs` `xs = sourcenodes as'`
    show ?thesis by fastforce
  qed
qed


lemma postdominate_variant:
  assumes "n' postdominates n" 
  shows "\<forall>as. n -as\<rightarrow>\<^sub>\<surd>* (_Exit_) \<longrightarrow> n' \<in> set (sourcenodes as)"
proof -
  from `n' postdominates n`
  have all:"\<forall>as pex. (n -as\<rightarrow>\<^sub>\<iota>* pex \<and> method_exit pex) \<longrightarrow> n' \<in> set (sourcenodes as)"
    by(simp add:postdominate_def)
  { fix as assume "n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)"
    then obtain as' pex where "n -as'\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex"
      and "set(sourcenodes as') \<subseteq> set(sourcenodes as)"
      by(erule valid_Exit_path_intra_path)
    from `n -as'\<rightarrow>\<^sub>\<iota>* pex` `method_exit pex` `n' postdominates n`
    have "n' \<in> set (sourcenodes as')" by(fastforce simp:postdominate_def)
    with `set(sourcenodes as') \<subseteq> set(sourcenodes as)`
    have "n' \<in> set (sourcenodes as)" by fastforce }
  thus ?thesis by simp
qed


lemma postdominate_refl:
  assumes "valid_node n" and "\<not> method_exit n" shows "n postdominates n"
using `valid_node n`
proof(induct rule:valid_node_cases)
  case Entry
  { fix as pex assume "(_Entry_) -as\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex"
    from `method_exit pex` have "(_Entry_) \<in> set (sourcenodes as)"
    proof(rule method_exit_cases)
      assume "pex = (_Exit_)"
      with `(_Entry_) -as\<rightarrow>\<^sub>\<iota>* pex` have "as \<noteq> []" 
        apply(clarsimp simp:intra_path_def) apply(erule path.cases)
        by (drule sym,simp,drule Exit_noteq_Entry,auto)
      with `(_Entry_) -as\<rightarrow>\<^sub>\<iota>* pex` have "hd (sourcenodes as) = (_Entry_)" 
        by(fastforce intro:path_sourcenode simp:intra_path_def)
      with `as \<noteq> []`show ?thesis by(fastforce intro:hd_in_set simp:sourcenodes_def)
    next
      fix a Q p f assume "pex = sourcenode a" and "valid_edge a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      from `(_Entry_) -as\<rightarrow>\<^sub>\<iota>* pex` have "get_proc (_Entry_) = get_proc pex"
        by(rule intra_path_get_procs)
      hence "get_proc pex = Main" by(simp add:get_proc_Entry)
      from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "get_proc (sourcenode a) = p"
        by(rule get_proc_return)
      with `pex = sourcenode a` `get_proc pex = Main` have "p = Main" by simp
      with `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have False
        by simp (rule Main_no_return_source)
      thus ?thesis by simp
    qed }
  with Entry show ?thesis 
    by(fastforce intro:empty_path simp:postdominate_def intra_path_def)
next
  case Exit
  with `\<not> method_exit n` have False by(simp add:method_exit_def)
  thus ?thesis by simp
next
  case inner
  show ?thesis
  proof(cases "\<exists>as. n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)")
    case True
    { fix as pex assume "n -as\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex"
      with `\<not> method_exit n` have "as \<noteq> []" 
        by(fastforce elim:path.cases simp:intra_path_def)
      with `n -as\<rightarrow>\<^sub>\<iota>* pex` inner have "hd (sourcenodes as) = n"
        by(fastforce intro:path_sourcenode simp:intra_path_def)
      from `as \<noteq> []` have "sourcenodes as \<noteq> []" by(simp add:sourcenodes_def)
      with `hd (sourcenodes as) = n`[THEN sym] 
      have "n \<in> set (sourcenodes as)" by simp }
    hence "\<forall>as pex. (n -as\<rightarrow>\<^sub>\<iota>* pex \<and> method_exit pex) \<longrightarrow> n \<in> set (sourcenodes as)"
      by fastforce
    with True inner show ?thesis 
      by(fastforce intro:empty_path 
                   simp:postdominate_def inner_is_valid intra_path_def)
  next
    case False
    with inner show ?thesis by(fastforce dest:inner_is_valid Exit_path)
  qed
qed



lemma postdominate_trans:
  assumes "n'' postdominates n" and "n' postdominates n''"
  shows "n' postdominates n"
proof -
  from `n'' postdominates n` `n' postdominates n''`
  have "valid_node n" and "valid_node n'" by(simp_all add:postdominate_def)
  { fix as pex assume "n -as\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex"
    with `n'' postdominates n` have "n'' \<in> set (sourcenodes as)"
      by(fastforce simp:postdominate_def)
    then obtain ns' ns'' where "sourcenodes as = ns'@n''#ns''"
      by(auto dest:split_list)
    then obtain as' as'' a where "sourcenodes as'' = ns''" and [simp]:"as=as'@a#as''"
      and [simp]:"sourcenode a = n''"
      by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
    from `n -as\<rightarrow>\<^sub>\<iota>* pex` have "n -as'@a#as''\<rightarrow>\<^sub>\<iota>* pex" by simp
    hence "n'' -a#as''\<rightarrow>\<^sub>\<iota>* pex"
      by(fastforce dest:path_split_second simp:intra_path_def)
    with `n' postdominates n''` `method_exit pex`
    have "n' \<in> set(sourcenodes (a#as''))" by(fastforce simp:postdominate_def)
    hence "n' \<in> set (sourcenodes as)" by(fastforce simp:sourcenodes_def) }
  with `valid_node n` `valid_node n'`
  show ?thesis by(fastforce simp:postdominate_def)
qed


lemma postdominate_antisym:
  assumes "n' postdominates n" and "n postdominates n'"
  shows "n = n'"
proof -
  from `n' postdominates n` have "valid_node n" and "valid_node n'" 
    by(auto simp:postdominate_def)
  from `valid_node n` obtain asx where "n -asx\<rightarrow>\<^sub>\<surd>* (_Exit_)" by(auto dest:Exit_path)
  then obtain as' pex where "n -as'\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex"
    by -(erule valid_Exit_path_intra_path)
  with `n' postdominates n` have "\<exists>nx \<in> set(sourcenodes as'). nx = n'"
    by(fastforce simp:postdominate_def)
  then obtain ns ns' where "sourcenodes as' = ns@n'#ns'"
    and "\<forall>nx \<in> set ns'. nx \<noteq> n'"
    by(fastforce elim!:split_list_last_propE)
  from `sourcenodes as' = ns@n'#ns'` obtain asx a asx' 
    where [simp]:"ns' = sourcenodes asx'" "as' = asx@a#asx'" "sourcenode a = n'"
    by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
  from `n -as'\<rightarrow>\<^sub>\<iota>* pex` have "n' -a#asx'\<rightarrow>\<^sub>\<iota>* pex"
    by(fastforce dest:path_split_second simp:intra_path_def)
  with `n postdominates n'` `method_exit pex` have "n \<in> set(sourcenodes (a#asx'))" 
    by(fastforce simp:postdominate_def)
  hence "n = n' \<or> n \<in> set(sourcenodes asx')" by(simp add:sourcenodes_def)
  thus ?thesis
  proof
    assume "n = n'" thus ?thesis .
  next
    assume "n \<in> set(sourcenodes asx')"
    then obtain nsx' nsx'' where "sourcenodes asx' = nsx'@n#nsx''"
      by(auto dest:split_list)
    then obtain asi asi' a' where [simp]:"asx' = asi@a'#asi'" "sourcenode a' = n"
      by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
    with `n -as'\<rightarrow>\<^sub>\<iota>* pex` have "n -(asx@a#asi)@a'#asi'\<rightarrow>\<^sub>\<iota>* pex" by simp
    hence "n -(asx@a#asi)@a'#asi'\<rightarrow>* pex"
      and "\<forall>a \<in> set ((asx@a#asi)@a'#asi'). intra_kind (kind a)"
      by(simp_all add:intra_path_def)
    from `n -(asx@a#asi)@a'#asi'\<rightarrow>* pex`
    have "n -a'#asi'\<rightarrow>* pex" by(fastforce dest:path_split_second)
    with `\<forall>a \<in> set ((asx@a#asi)@a'#asi'). intra_kind (kind a)`
    have "n -a'#asi'\<rightarrow>\<^sub>\<iota>* pex" by(simp add:intra_path_def)
    with `n' postdominates n` `method_exit pex` 
    have "n' \<in> set(sourcenodes (a'#asi'))" by(fastforce simp:postdominate_def)
    hence "n' = n \<or> n' \<in> set(sourcenodes asi')"
      by(simp add:sourcenodes_def)
    thus ?thesis
    proof
      assume "n' = n" thus ?thesis by(rule sym)
    next
      assume "n' \<in> set(sourcenodes asi')"
      with `\<forall>nx \<in> set ns'. nx \<noteq> n'` have False by(fastforce simp:sourcenodes_def)
      thus ?thesis by simp
    qed
  qed
qed


lemma postdominate_path_branch:
  assumes "n -as\<rightarrow>* n''" and "n' postdominates n''" and "\<not> n' postdominates n"
  obtains a as' as'' where "as = as'@a#as''" and "valid_edge a"
  and "\<not> n' postdominates (sourcenode a)" and "n' postdominates (targetnode a)"
proof(atomize_elim)
  from assms
  show "\<exists>as' a as''. as = as'@a#as'' \<and> valid_edge a \<and> 
    \<not> n' postdominates (sourcenode a) \<and> n' postdominates (targetnode a)"
  proof(induct rule:path.induct)
    case (Cons_path n'' as nx a n)
    note IH = `\<lbrakk>n' postdominates nx; \<not> n' postdominates n''\<rbrakk>
      \<Longrightarrow> \<exists>as' a as''. as = as'@a#as'' \<and> valid_edge a \<and>
        \<not> n' postdominates sourcenode a \<and> n' postdominates targetnode a`
    show ?case
    proof(cases "n' postdominates n''")
      case True
      with `\<not> n' postdominates n` `sourcenode a = n` `targetnode a = n''`
        `valid_edge a` show ?thesis by blast
    next
      case False
      from IH[OF `n' postdominates nx` this] show ?thesis
        by clarsimp(rule_tac x="a#as'" in exI,clarsimp)
    qed
  qed simp
qed


lemma Exit_no_postdominator:
  assumes "(_Exit_) postdominates n" shows False
proof -
  from `(_Exit_) postdominates n` have "valid_node n" by(simp add:postdominate_def)
  from `valid_node n` obtain asx where "n -asx\<rightarrow>\<^sub>\<surd>* (_Exit_)" by(auto dest:Exit_path)
  then obtain as' pex where "n -as'\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex"
    by -(erule valid_Exit_path_intra_path)
  with `(_Exit_) postdominates n` have "(_Exit_) \<in> set (sourcenodes as')"
    by(fastforce simp:postdominate_def)
  with `n -as'\<rightarrow>\<^sub>\<iota>* pex` show False by(fastforce simp:intra_path_def)
qed


lemma postdominate_inner_path_targetnode:
  assumes "n' postdominates n" and "n -as\<rightarrow>\<^sub>\<iota>* n''" and "n' \<notin> set(sourcenodes as)"
  shows "n' postdominates n''"
proof -
  from `n' postdominates n` obtain asx 
    where "valid_node n" and "valid_node n'"
    and all:"\<forall>as pex. (n -as\<rightarrow>\<^sub>\<iota>* pex \<and> method_exit pex) \<longrightarrow> n' \<in> set (sourcenodes as)"
    by(auto simp:postdominate_def)
  from `n -as\<rightarrow>\<^sub>\<iota>* n''` have "valid_node n''"
    by(fastforce dest:path_valid_node simp:intra_path_def)
  have "\<forall>as' pex'. (n'' -as'\<rightarrow>\<^sub>\<iota>* pex' \<and> method_exit pex') \<longrightarrow> 
                   n' \<in> set (sourcenodes as')"
  proof(rule ccontr)
    assume "\<not> (\<forall>as' pex'. (n'' -as'\<rightarrow>\<^sub>\<iota>* pex' \<and> method_exit pex') \<longrightarrow> 
                          n' \<in> set (sourcenodes as'))"
    then obtain as' pex' where "n'' -as'\<rightarrow>\<^sub>\<iota>* pex'" and "method_exit pex'"
      and "n' \<notin> set (sourcenodes as')" by blast
    from `n -as\<rightarrow>\<^sub>\<iota>* n''` `n'' -as'\<rightarrow>\<^sub>\<iota>* pex'` have "n -as@as'\<rightarrow>\<^sub>\<iota>* pex'"
      by(fastforce intro:path_Append simp:intra_path_def)
    from `n' \<notin> set(sourcenodes as)` `n' \<notin> set (sourcenodes as')`
    have "n' \<notin> set (sourcenodes (as@as'))"
      by(simp add:sourcenodes_def)
    with `n -as@as'\<rightarrow>\<^sub>\<iota>* pex'` `method_exit pex'` `n' postdominates n`
    show False by(fastforce simp:postdominate_def)
  qed
  with `valid_node n'` `valid_node n''`
  show ?thesis by(auto simp:postdominate_def)
qed


lemma not_postdominate_source_not_postdominate_target:
  assumes "\<not> n postdominates (sourcenode a)" 
  and "valid_node n" and "valid_edge a" and "intra_kind (kind a)"
  obtains ax where "sourcenode a = sourcenode ax" and "valid_edge ax"
  and "\<not> n postdominates targetnode ax"
proof(atomize_elim)
  show "\<exists>ax. sourcenode a = sourcenode ax \<and> valid_edge ax \<and> 
    \<not> n postdominates targetnode ax"
  proof -
    from assms obtain asx pex 
      where "sourcenode a -asx\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex"
      and "n \<notin> set(sourcenodes asx)" by(fastforce simp:postdominate_def)
    show ?thesis
    proof(cases asx)
      case Nil
      with `sourcenode a -asx\<rightarrow>\<^sub>\<iota>* pex` have "pex = sourcenode a"
        by(fastforce simp:intra_path_def)
      with `method_exit pex` have "method_exit (sourcenode a)" by simp
      thus ?thesis
      proof(rule method_exit_cases)
        assume "sourcenode a = (_Exit_)"
        with `valid_edge a` have False by(rule Exit_source)
        thus ?thesis by simp
      next
        fix a' Q f p assume "sourcenode a = sourcenode a'"
          and "valid_edge a'" and "kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
        hence False using `intra_kind (kind a)` `valid_edge a`
          by(fastforce dest:return_edges_only simp:intra_kind_def)
        thus ?thesis by simp
      qed
    next
      case (Cons ax asx')
      with `sourcenode a -asx\<rightarrow>\<^sub>\<iota>* pex`
      have "sourcenode a -[]@ax#asx'\<rightarrow>* pex" 
        and "\<forall>a \<in> set (ax#asx'). intra_kind (kind a)" by(simp_all add:intra_path_def)
      from `sourcenode a -[]@ax#asx'\<rightarrow>* pex`
      have "sourcenode a = sourcenode ax" and "valid_edge ax"
        and "targetnode ax -asx'\<rightarrow>* pex"  by(fastforce dest:path_split)+
      with `\<forall>a \<in> set (ax#asx'). intra_kind (kind a)`
      have "targetnode ax -asx'\<rightarrow>\<^sub>\<iota>* pex" by(simp add:intra_path_def)
      with `n \<notin> set(sourcenodes asx)` Cons `method_exit pex`
      have "\<not> n postdominates targetnode ax"
        by(fastforce simp:postdominate_def sourcenodes_def) 
      with `sourcenode a = sourcenode ax` `valid_edge ax` show ?thesis by blast
    qed
  qed
qed


lemma inner_node_Exit_edge:
  assumes "inner_node n" 
  obtains a where "valid_edge a" and "intra_kind (kind a)" 
  and "inner_node (sourcenode a)" and "targetnode a = (_Exit_)"
proof(atomize_elim)
  from `inner_node n` have "valid_node n" by(rule inner_is_valid)
  then obtain as where "n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)" by(fastforce dest:Exit_path)
  show "\<exists>a. valid_edge a \<and> intra_kind (kind a) \<and> inner_node (sourcenode a) \<and> 
    targetnode a = (_Exit_)"
  proof(cases "as = []")
    case True
    with `inner_node n` `n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)` have False by(fastforce simp:vp_def)
    thus ?thesis by simp
  next
    case False
    with `n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)` obtain a' as' where "as = as'@[a']" 
      and "n -as'\<rightarrow>\<^sub>\<surd>* sourcenode a'" and "valid_edge a'" 
      and "(_Exit_) = targetnode a'" by -(erule vp_split_snoc)
    from `valid_edge a'` have "valid_node (sourcenode a')" by simp
    thus ?thesis
    proof(cases "sourcenode a'" rule:valid_node_cases)
      case Entry
      with `n -as'\<rightarrow>\<^sub>\<surd>* sourcenode a'` have "n -as'\<rightarrow>* (_Entry_)" by(simp add:vp_def)
      with `inner_node n`
      have False by -(drule path_Entry_target,auto simp:inner_node_def)
      thus ?thesis by simp
    next
      case Exit
      from `valid_edge a'` this have False by(rule Exit_source)
      thus ?thesis by simp
    next
      case inner
      have "intra_kind (kind a')"
      proof(cases "kind a'" rule:edge_kind_cases)
        case Intra thus ?thesis by simp
      next
        case (Call Q r p fs)
        with `valid_edge a'` have "get_proc(targetnode a') = p" by(rule get_proc_call)
        with `(_Exit_) = targetnode a'` get_proc_Exit have "p = Main" by simp
        with `kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "kind a' = Q:r\<hookrightarrow>\<^bsub>Main\<^esub>fs" by simp
        with `valid_edge a'` have False by(rule Main_no_call_target)
        thus ?thesis by simp
      next
        case (Return Q p f)
        from `valid_edge a'` `kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `(_Exit_) = targetnode a'`[THEN sym]
        have False by(rule Exit_no_return_target)
        thus ?thesis by simp
      qed
      with `valid_edge a'` `(_Exit_) = targetnode a'` `inner_node (sourcenode a')` 
      show ?thesis by simp blast
    qed
  qed
qed


lemma inner_node_Entry_edge:
  assumes "inner_node n" 
  obtains a where "valid_edge a" and "intra_kind (kind a)" 
  and "inner_node (targetnode a)" and "sourcenode a = (_Entry_)"
proof(atomize_elim)
  from `inner_node n` have "valid_node n" by(rule inner_is_valid)
  then obtain as where "(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n" by(fastforce dest:Entry_path)
  show "\<exists>a. valid_edge a \<and> intra_kind (kind a) \<and> inner_node (targetnode a) \<and> 
    sourcenode a = (_Entry_)"
  proof(cases "as = []")
    case True
    with `inner_node n` `(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n` have False
      by(fastforce simp:inner_node_def vp_def)
    thus ?thesis by simp
  next
    case False
    with `(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n` obtain a' as' where "as = a'#as'" 
      and "targetnode a' -as'\<rightarrow>\<^sub>\<surd>* n" and "valid_edge a'" 
      and "(_Entry_) = sourcenode a'" by -(erule vp_split_Cons)
    from `valid_edge a'` have "valid_node (targetnode a')" by simp
    thus ?thesis
    proof(cases "targetnode a'" rule:valid_node_cases)
      case Entry
      from `valid_edge a'` this have False by(rule Entry_target)
      thus ?thesis by simp
    next
      case Exit
      with `targetnode a' -as'\<rightarrow>\<^sub>\<surd>* n` have "(_Exit_) -as'\<rightarrow>* n" by(simp add:vp_def)
      with `inner_node n`
      have False by -(drule path_Exit_source,auto simp:inner_node_def)
      thus ?thesis by simp
    next
      case inner
      have "intra_kind (kind a')"
      proof(cases "kind a'" rule:edge_kind_cases)
        case Intra thus ?thesis by simp
      next
        case (Call Q r p fs)
        from `valid_edge a'` `kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` 
          `(_Entry_) = sourcenode a'`[THEN sym]
        have False by(rule Entry_no_call_source)
        thus ?thesis by simp
      next
        case (Return Q p f)
        with `valid_edge a'` have "get_proc(sourcenode a') = p" 
          by(rule get_proc_return)
        with `(_Entry_) = sourcenode a'` get_proc_Entry have "p = Main" by simp
        with `kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "kind a' = Q\<hookleftarrow>\<^bsub>Main\<^esub>f" by simp
        with `valid_edge a'` have False by(rule Main_no_return_source)
        thus ?thesis by simp
      qed
      with `valid_edge a'` `(_Entry_) = sourcenode a'` `inner_node (targetnode a')` 
      show ?thesis by simp blast
    qed
  qed
qed


lemma intra_path_to_matching_method_exit:
  assumes "method_exit n'" and "get_proc n = get_proc n'" and "valid_node n"
  obtains as where "n -as\<rightarrow>\<^sub>\<iota>* n'"
proof(atomize_elim)
  from `valid_node n` obtain as' where "n -as'\<rightarrow>\<^sub>\<surd>* (_Exit_)"
    by(fastforce dest:Exit_path)
  then obtain as mex where "n -as\<rightarrow>\<^sub>\<iota>* mex" and "method_exit mex"
    by(fastforce elim:valid_Exit_path_intra_path)
  from `n -as\<rightarrow>\<^sub>\<iota>* mex` have "get_proc n = get_proc mex" 
    by(rule intra_path_get_procs)
  with `method_exit n'` `get_proc n = get_proc n'` `method_exit mex`
  have "mex = n'" by(fastforce intro:method_exit_unique)
  with `n -as\<rightarrow>\<^sub>\<iota>* mex` show "\<exists>as. n -as\<rightarrow>\<^sub>\<iota>* n'" by fastforce
qed


end

end