header {* \isaheader{Postdomination} *}

theory Postdomination imports CFGExit begin

subsection {* Standard Postdomination *}

locale Postdomination = CFGExit _ _ kind valid_edge "(_Entry_)" "(_Exit_)"
  for kind :: "'edge \<Rightarrow> 'state edge_kind"
    and valid_edge :: "'edge \<Rightarrow> bool"
    and Entry :: "'node" ("'('_Entry'_')")
    and Exit :: "'node" ("'('_Exit'_')")
  +
  assumes Entry_path:"CFG.valid_node sourcenode targetnode valid_edge n \<Longrightarrow> 
  \<exists>as. CFG.path sourcenode targetnode valid_edge (_Entry_) as n"
  and Exit_path:"CFG.valid_node sourcenode targetnode valid_edge n \<Longrightarrow>
  \<exists>as. CFG.path sourcenode targetnode valid_edge n as (_Exit_)"

begin

definition postdominate :: "'node \<Rightarrow> 'node \<Rightarrow> bool" ("_ postdominates _" [51,0])
where postdominate_def:"n' postdominates n \<equiv> 
    (valid_node n \<and> valid_node n' \<and>
    ((\<forall>as. n -as\<rightarrow>* (_Exit_) \<longrightarrow> n' \<in> set (sourcenodes as))))"


lemma postdominate_implies_path: 
  assumes "n' postdominates n" obtains as where "n -as\<rightarrow>* n'"
proof -
  have "\<exists>as. n -as\<rightarrow>* n'"
  proof -
    from `n' postdominates n` have "valid_node n"
    and all:"\<forall>as. n -as\<rightarrow>* (_Exit_) \<longrightarrow> n' \<in> set(sourcenodes as)"
      by(auto simp:postdominate_def)
    from `valid_node n` obtain as where "n -as\<rightarrow>* (_Exit_)" by(auto dest:Exit_path)
    with all have "n' \<in> set(sourcenodes as)" by simp
    then obtain ns ns' where "sourcenodes as = ns@n'#ns'" by(auto dest:split_list)
    then obtain as' a as'' where "sourcenodes as' = ns" 
      and "sourcenode a = n'" and "as = as'@a#as''"
      by(fastsimp elim:map_append_append_maps simp:sourcenodes_def)
    from `n -as\<rightarrow>* (_Exit_)` `as = as'@a#as''` have "n -as'\<rightarrow>* sourcenode a"
      by(fastsimp dest:path_split)
    with `sourcenode a = n'` show ?thesis by blast
  qed
  with that show ?thesis by blast
qed


lemma postdominate_refl:
  assumes valid:"valid_node n" and notExit:"n \<noteq> (_Exit_)"
  shows "n postdominates n"
using valid
proof(induct rule:valid_node_cases)
  case Entry
  { fix as assume path:"(_Entry_) -as\<rightarrow>* (_Exit_)"
    hence notempty:"as \<noteq> []" 
      apply - apply(erule path.cases)
      by (drule sym,simp,drule Exit_noteq_Entry,auto)
    with path have "hd (sourcenodes as) = (_Entry_)" 
      by(fastsimp intro:path_sourcenode)
    with notempty have "(_Entry_) \<in> set (sourcenodes as)"
      by(fastsimp intro:hd_in_set simp:sourcenodes_def) }
  with Entry show ?thesis by(simp add:postdominate_def)
next
  case Exit
  with notExit have False by simp
  thus ?thesis by simp
next
  case inner
  show ?thesis
  proof(cases "\<exists>as. n -as\<rightarrow>* (_Exit_)")
    case True
    { fix as' assume path':"n -as'\<rightarrow>* (_Exit_)"
      with inner have notempty:"as' \<noteq> []"
	by(cases as',auto elim!:path.cases simp:inner_node_def)
      with path' inner have hd:"hd (sourcenodes as') = n"
	by -(rule path_sourcenode)
      from notempty have "sourcenodes as' \<noteq> []" by(simp add:sourcenodes_def)
      with hd[THEN sym] have "n \<in> set (sourcenodes as')" by simp }
    hence "\<forall>as. n -as\<rightarrow>* (_Exit_) \<longrightarrow> n \<in> set (sourcenodes as)" by simp
    with True inner show ?thesis by(simp add:postdominate_def inner_is_valid)
  next
    case False
    with inner show ?thesis by(simp add:postdominate_def inner_is_valid)
  qed
qed


lemma postdominate_trans:
  assumes pd1:"n'' postdominates n" and pd2:"n' postdominates n''"
  shows "n' postdominates n"
proof -
  from pd1 pd2 have valid:"valid_node n" and valid':"valid_node n'"
    by(simp_all add:postdominate_def)
  { fix as assume path:"n -as\<rightarrow>* (_Exit_)"
    with pd1 have "n'' \<in> set (sourcenodes as)" by(simp add:postdominate_def)
    then obtain ns' ns'' where "sourcenodes as = ns'@n''#ns''"
      by(auto dest:split_list)
    then obtain as' as'' a
      where as'':"sourcenodes as'' = ns''" and as:"as=as'@a#as''"
      and source:"sourcenode a = n''"
      by(fastsimp elim:map_append_append_maps simp:sourcenodes_def)
    from as path have "n -as'@a#as''\<rightarrow>* (_Exit_)" by simp
    with source have path':"n'' -a#as''\<rightarrow>* (_Exit_)"
      by(fastsimp dest:path_split_second)
    with pd2 have "n' \<in> set(sourcenodes (a#as''))"
      by(auto simp:postdominate_def)
    with as have "n' \<in> set(sourcenodes as)" by(auto simp:sourcenodes_def) }
  with valid valid' show ?thesis by(simp add:postdominate_def)
qed


lemma postdominate_antisym:
  assumes pd1:"n' postdominates n" and pd2:"n postdominates n'"
  shows "n = n'"
proof -
  from pd1 have valid:"valid_node n" and valid':"valid_node n'" 
    by(auto simp:postdominate_def)
  from valid obtain as where path1:"n -as\<rightarrow>* (_Exit_)" by(fastsimp dest:Exit_path)
  from valid' obtain as' where path2:"n' -as'\<rightarrow>* (_Exit_)" by(fastsimp dest:Exit_path)
  from pd1 path1 have "\<exists>nx \<in> set(sourcenodes as). nx = n'"
    by(simp add:postdominate_def)
  then obtain ns ns' where sources:"sourcenodes as = ns@n'#ns'"
    and all:"\<forall>nx \<in> set ns'. nx \<noteq> n'"
    by(fastsimp elim!: rightmost_element_property)
  from sources obtain asx a asx' where ns':"ns' = sourcenodes asx'"
    and as:"as = asx@a#asx'" and source:"sourcenode a = n'"
    by(fastsimp elim:map_append_append_maps simp:sourcenodes_def)
  from path1 as have "n -asx@a#asx'\<rightarrow>* (_Exit_)" by simp
  with source have "n' -a#asx'\<rightarrow>* (_Exit_)" by(fastsimp dest:path_split_second)
  with pd2 have "n \<in> set(sourcenodes (a#asx'))" by(simp add:postdominate_def)
  with source have "n = n' \<or> n \<in> set(sourcenodes asx')" by(simp add:sourcenodes_def)
  thus ?thesis
  proof
    assume "n = n'" thus ?thesis .
  next
    assume "n \<in> set(sourcenodes asx')"
    then obtain nsx' nsx'' where "sourcenodes asx' = nsx'@n#nsx''"
      by(auto dest:split_list)
    then obtain asi asi' a' where asx':"asx' = asi@a'#asi'"
      and source':"sourcenode a' = n"
      by(fastsimp elim:map_append_append_maps simp:sourcenodes_def)
    with path1 as have "n -(asx@a#asi)@a'#asi'\<rightarrow>* (_Exit_)" by simp
    with source' have "n -a'#asi'\<rightarrow>* (_Exit_)" by(fastsimp dest:path_split_second)
    with pd1 have "n' \<in> set(sourcenodes (a'#asi'))" by(auto simp:postdominate_def)
    with source' have "n' = n \<or> n' \<in> set(sourcenodes asi')"
      by(simp add:sourcenodes_def)
    thus ?thesis
    proof
      assume "n' = n" thus ?thesis by(rule sym)
    next
      assume "n' \<in> set(sourcenodes asi')"
      with asx' ns' have "n' \<in> set ns'" by(simp add:sourcenodes_def)
      with all have False by blast
      thus ?thesis by simp
    qed
  qed
qed


lemma postdominate_path_branch:
  assumes pd:"n' postdominates n''" and not_pd:"\<not> n' postdominates n"
  and path:"n -as\<rightarrow>* n''"
  obtains a as' as'' where "as = as'@a#as''" and "valid_edge a"
  and "\<not> n' postdominates (sourcenode a)" and "n' postdominates (targetnode a)"
proof -
  from path pd not_pd
  have "\<exists>a as' as''. as = as'@a#as'' \<and> valid_edge a \<and> 
    \<not> n' postdominates (sourcenode a) \<and> n' postdominates (targetnode a)"
  proof(induct rule:path.induct)
    case (Cons_path n'' as nx a n)
    note valid = `valid_edge a`
    note source = `sourcenode a = n`
    note target = `targetnode a = n''`
    note pd = `n' postdominates nx`
    note not_pd = `\<not> n' postdominates n`
    note IH = `\<lbrakk>n' postdominates nx; \<not> n' postdominates n''\<rbrakk>
      \<Longrightarrow> \<exists>a as' as''. as = as'@a#as'' \<and> valid_edge a \<and>
        \<not> n' postdominates sourcenode a \<and> n' postdominates targetnode a`
    show ?case
    proof(cases "n' postdominates n''")
      case True
      with not_pd source target valid show ?thesis by blast
    next
      case False
      from IH[OF pd this] show ?thesis
	apply clarsimp
	apply(rule_tac x="aa" in exI,clarsimp)
	apply(rule_tac x="a#as'" in exI,clarsimp)
	done
    qed
  qed simp
  with that show ?thesis by blast
qed


lemma Exit_no_postdominator:
  "\<lbrakk>(_Exit_) postdominates n; n -as\<rightarrow>* (_Exit_)\<rbrakk> \<Longrightarrow> False"
by(fastsimp simp:postdominate_def)


lemma postdominate_path_targetnode:
  assumes pd:"n' postdominates n" and path:"n -as\<rightarrow>* n''" 
  and notin:"n' \<notin> set(sourcenodes as)"
  shows "n' postdominates n''"
proof -
  from pd have "valid_node n" and valid1:"valid_node n'"
    and all:"\<forall>as''. n -as''\<rightarrow>* (_Exit_) \<longrightarrow> n' \<in> set(sourcenodes as'')"
    by(simp_all add:postdominate_def)
  then obtain as' where path_exit:"n -as'\<rightarrow>* (_Exit_)" by(fastsimp dest:Exit_path)
  from path have valid2:"valid_node n''" by(fastsimp dest:path_valid_node)
  have "\<forall>as''. n'' -as''\<rightarrow>* (_Exit_) \<longrightarrow> n' \<in> set(sourcenodes as'')"
  proof(rule ccontr)
    assume "\<not> (\<forall>as''. n'' -as''\<rightarrow>* (_Exit_) \<longrightarrow> n' \<in> set (sourcenodes as''))"
    then obtain as'' where path_exit2:"n'' -as''\<rightarrow>* (_Exit_)"
      and notin':"n' \<notin> set (sourcenodes as'')" by blast
    from path path_exit2 have path_exit3:"n -as@as''\<rightarrow>* (_Exit_)" 
      by(rule path_Append)
    with notin notin' have "n' \<notin> set (sourcenodes (as@as''))"
      by(simp add:sourcenodes_def)
    with path_exit3 pd show False by(simp add:postdominate_def)
  qed
  with valid1 valid2 show ?thesis by(simp add:postdominate_def)
qed


lemma not_postdominate_source_not_postdominate_target:
  assumes not_pd:"\<not> n postdominates (sourcenode a)"
  and valid:"valid_node n" and valid_edge:"valid_edge a"
  obtains ax where "sourcenode a = sourcenode ax" and "valid_edge ax"
  and "\<not> n postdominates targetnode ax"
proof -
  have "\<exists>ax. sourcenode a = sourcenode ax \<and> valid_edge ax \<and> 
    \<not> n postdominates targetnode ax"
  proof -
    from not_pd valid_edge valid obtain asx 
      where path:"sourcenode a -asx\<rightarrow>* (_Exit_)"
      and notin:"n \<notin> set(sourcenodes asx)" by(auto simp:postdominate_def)
    from path valid_edge obtain ax asx' where asx:"asx = ax#asx'"
      apply - apply(erule path.cases)
      apply(drule_tac s="(_Exit_)" in sym)
      apply simp
      apply(drule Exit_source)
      apply simp_all
      by fastsimp
    with path have "sourcenode a -[]@ax#asx'\<rightarrow>* (_Exit_)" by simp
    hence valid_edge':"valid_edge ax" and source:"sourcenode a = sourcenode ax"
      and path':"targetnode ax -asx'\<rightarrow>* (_Exit_)"
      by(fastsimp dest:path_split)+
    from path' notin asx have "\<not> n postdominates targetnode ax"
      by(fastsimp simp:postdominate_def sourcenodes_def)
    with source valid_edge' show ?thesis by blast
  qed
  with that show ?thesis by blast
qed


end

subsection {* Strong Postdomination *}


locale StrongPostdomination = Postdomination _ _ kind valid_edge "(_Entry_)" "(_Exit_)"
  for kind :: "'edge \<Rightarrow> 'state edge_kind"
    and valid_edge :: "'edge \<Rightarrow> bool"
    and Entry :: "'node" ("'('_Entry'_')")
    and Exit :: "'node" ("'('_Exit'_')")
  +
  assumes successor_set_finite:
  "CFG.valid_node sourcenode targetnode valid_edge n 
   \<Longrightarrow> finite {n'. \<exists>a'. valid_edge a' \<and> sourcenode a' = n \<and>
                       targetnode a' = n'}"

begin

definition  strong_postdominate :: "'node \<Rightarrow> 'node \<Rightarrow> bool" 
("_ strongly-postdominates _" [51,0])
where strong_postdominate_def:"n' strongly-postdominates n \<equiv>
  (n' postdominates n \<and> 
  (\<exists>k \<ge> 1. \<forall>as nx. n -as\<rightarrow>* nx \<and> 
                    length as \<ge> k \<longrightarrow> n' \<in> set(sourcenodes as)))"


lemma strong_postdominate_prop_smaller_path:
  assumes all:"\<forall>as nx. n -as\<rightarrow>* nx \<and> length as \<ge> k \<longrightarrow> n' \<in> set(sourcenodes as)"
  and path:"n -as\<rightarrow>* n''" and length:"length as \<ge> k"
  obtains as' as'' where "n -as'\<rightarrow>* n'" and "length as' < k" and "n' -as''\<rightarrow>* n''"
  and "as = as'@as''"
proof -
  have "\<exists>as' as''. n -as'\<rightarrow>* n' \<and> length as' < k \<and> n' -as''\<rightarrow>* n'' \<and> as = as'@as''"
  proof(rule ccontr)
    assume "\<not> (\<exists>as' as''. n -as'\<rightarrow>* n' \<and> length as' < k \<and> n' -as''\<rightarrow>* n'' \<and> 
                          as = as'@as'')"
    hence all':"\<forall>as' as''. n -as'\<rightarrow>* n' \<and> n' -as''\<rightarrow>* n'' \<and> as = as'@as'' 
      \<longrightarrow> length as' \<ge> k" by fastsimp
    from all path length have "\<exists>nx \<in> set(sourcenodes as). nx = n'" by fastsimp
    then obtain ns ns' where sources:"sourcenodes as = ns@n'#ns'"
      and nodes:"\<forall>nx \<in> set ns. nx \<noteq> n'"
      by(fastsimp elim!: leftmost_element_property)
    from sources obtain asx a asx' where ns:"ns = sourcenodes asx"
      and as:"as = asx@a#asx'" and source:"sourcenode a = n'"
      by(fastsimp elim:map_append_append_maps simp:sourcenodes_def)
    from path as have "n -asx@a#asx'\<rightarrow>* n''" by simp
    with source have path':"n -asx\<rightarrow>* n'" and "valid_edge a"
      and "targetnode a -asx'\<rightarrow>* n''" by(fastsimp dest:path_split)+
    with source have path'':"n' -a#asx'\<rightarrow>* n''" by(fastsimp intro:Cons_path)
    with path' as all' have "length asx \<ge> k" by simp
    with path' all have "n' \<in> set(sourcenodes asx)" by fastsimp
    with nodes ns show False by fastsimp
  qed
  with that show ?thesis by blast
qed



lemma strong_postdominate_refl:
  assumes valid:"valid_node n" and notExit:"n \<noteq> (_Exit_)"
  shows "n strongly-postdominates n"
proof -
  from valid notExit have pd:"n postdominates n" by(rule postdominate_refl)
  { fix as nx assume path:"n -as\<rightarrow>* nx" and ge:"length as \<ge> 1"
    from ge obtain a' as' where as:"as = a'#as'" by(cases as) auto
    with path have "n -[]@a'#as'\<rightarrow>* nx" by simp
    hence "n = sourcenode a'" by(fastsimp dest:path_split)
    with as have "n \<in> set(sourcenodes as)" by(simp add:sourcenodes_def) }
  hence "\<forall>as nx. n -as\<rightarrow>* nx \<and> length as \<ge> 1 \<longrightarrow> n \<in> set(sourcenodes as)"
    by auto
  hence "\<exists>k \<ge> 1. \<forall>as nx. n -as\<rightarrow>* nx \<and> length as \<ge> k \<longrightarrow> n \<in> set(sourcenodes as)"
    by blast
  with pd show ?thesis by(simp add:strong_postdominate_def)
qed


lemma strong_postdominate_trans:
  assumes spd1:"n'' strongly-postdominates n" and spd2:"n' strongly-postdominates n''"
  shows "n' strongly-postdominates n"
proof -
  from spd1 have pd1:"n'' postdominates n"
    and paths1:"\<exists>k \<ge> 1. \<forall>as nx. n -as\<rightarrow>* nx \<and> length as \<ge> k 
             \<longrightarrow> n'' \<in> set(sourcenodes as)"
    by(auto simp only:strong_postdominate_def)
  from paths1 obtain k1 
    where all1:"\<forall>as nx. n -as\<rightarrow>* nx \<and> length as \<ge> k1 \<longrightarrow> n'' \<in> set(sourcenodes as)"
    and ge1:"k1 \<ge> 1" by blast
  from spd2 have pd2:"n' postdominates n''"
    and paths2:"\<exists>k \<ge> 1. \<forall>as nx. n'' -as\<rightarrow>* nx \<and> length as \<ge> k 
             \<longrightarrow> n' \<in> set(sourcenodes as)"
    by(auto simp only:strong_postdominate_def)
  from paths2 obtain k2 
    where all2:"\<forall>as nx. n'' -as\<rightarrow>* nx \<and> length as \<ge> k2 \<longrightarrow> n' \<in> set(sourcenodes as)"
    and ge2:"k2 \<ge> 1" by blast
  from pd1 pd2 have pd:"n' postdominates n" by(rule postdominate_trans)
  { fix as nx assume path:"n -as\<rightarrow>* nx" and ge:"length as \<ge> k1 + k2"
    hence "length as \<ge> k1" by fastsimp
    with path all1 obtain asx asx' where path_asx:"n -asx\<rightarrow>* n''"
      and length:"length asx < k1" and path_asx':"n'' -asx'\<rightarrow>* nx"
      and as:"as = asx@asx'" by -(erule strong_postdominate_prop_smaller_path)
    with ge have "length asx' \<ge> k2" by fastsimp
    with path_asx' all2 have "n' \<in> set(sourcenodes asx')" by fastsimp
    with as have "n' \<in> set(sourcenodes as)" by(simp add:sourcenodes_def) }
  with ge1 ge2 have "\<exists>k \<ge> 1. \<forall>as nx. n -as\<rightarrow>* nx \<and> length as \<ge> k 
             \<longrightarrow> n' \<in> set(sourcenodes as)"
    by(rule_tac x="k1 + k2" in exI,auto)
  with pd show ?thesis by(simp add:strong_postdominate_def)
qed


lemma strong_postdominate_antisym:
  "\<lbrakk>n' strongly-postdominates n; n strongly-postdominates n'\<rbrakk> \<Longrightarrow> n = n'"
by(fastsimp intro:postdominate_antisym simp:strong_postdominate_def)


lemma strong_postdominate_path_branch:
  assumes spd:"n' strongly-postdominates n''" 
  and not_spd:"\<not> n' strongly-postdominates n" and path:"n -as\<rightarrow>* n''"
  obtains a as' as'' where "as = as'@a#as''" and "valid_edge a"
  and "\<not> n' strongly-postdominates (sourcenode a)" 
  and "n' strongly-postdominates (targetnode a)"
proof -
  from path spd not_spd
  have "\<exists>a as' as''. as = as'@a#as'' \<and> valid_edge a \<and> 
    \<not> n' strongly-postdominates (sourcenode a) \<and> 
      n' strongly-postdominates (targetnode a)"
  proof(induct rule:path.induct)
    case (Cons_path n'' as nx a n)
    note valid = `valid_edge a`
    note source = `sourcenode a = n`
    note target = `targetnode a = n''`
    note spd = `n' strongly-postdominates nx`
    note not_spd = `\<not> n' strongly-postdominates n`
    note IH = `\<lbrakk>n' strongly-postdominates nx; \<not> n' strongly-postdominates n''\<rbrakk>
      \<Longrightarrow> \<exists>a as' as''. as = as'@a#as'' \<and> valid_edge a \<and>
        \<not> n' strongly-postdominates sourcenode a \<and> 
          n' strongly-postdominates targetnode a`
    show ?case
    proof(cases "n' strongly-postdominates n''")
      case True
      with not_spd source target valid show ?thesis by blast
    next
      case False
      from IH[OF spd this] show ?thesis
	apply clarsimp
	apply(rule_tac x="aa" in exI,clarsimp)
	apply(rule_tac x="a#as'" in exI,clarsimp)
	done
    qed
  qed simp
  with that show ?thesis by blast
qed


lemma Exit_no_strong_postdominator:
  "\<lbrakk>(_Exit_) strongly-postdominates n; n -as\<rightarrow>* (_Exit_)\<rbrakk> \<Longrightarrow> False"
by(fastsimp intro:Exit_no_postdominator simp:strong_postdominate_def)


lemma strong_postdominate_path_targetnode:
  assumes spd:"n' strongly-postdominates n" and path:"n -as\<rightarrow>* n''" 
  and notin:"n' \<notin> set(sourcenodes as)"
  shows "n' strongly-postdominates n''"
proof -
  from spd have pd:"n' postdominates n"
    and "\<exists>k \<ge> 1. \<forall>as nx. n -as\<rightarrow>* nx \<and> length as \<ge> k 
             \<longrightarrow> n' \<in> set(sourcenodes as)"
    by(auto simp only:strong_postdominate_def)
  then obtain k where ge:"k \<ge> 1"
    and paths:"\<forall>as nx. n -as\<rightarrow>* nx \<and> length as \<ge> k 
                         \<longrightarrow> n' \<in> set(sourcenodes as)" by auto
  from pd path notin have pd':"n' postdominates n''"
    by(rule postdominate_path_targetnode)
  { fix as' nx assume path':"n'' -as'\<rightarrow>* nx" and length:"length as' \<ge> k"
    with path have "n -as@as'\<rightarrow>* nx" and "length (as@as') \<ge> k"
      by(auto intro:path_Append)
    with paths have "n' \<in> set(sourcenodes (as@as'))" by fastsimp
    with notin have "n' \<in> set(sourcenodes as')" by(fastsimp simp:sourcenodes_def) }
  with ge have "\<exists>k \<ge> 1. \<forall>as' nx. n'' -as'\<rightarrow>* nx \<and> length as' \<ge> k 
             \<longrightarrow> n' \<in> set(sourcenodes as')" by auto
  with pd' show ?thesis by(simp add:strong_postdominate_def)
qed


lemma not_strong_postdominate_successor_set:
  assumes not_spd:"\<not> n strongly-postdominates (sourcenode a)" and valid:"valid_node n"
  and valid_edge:"valid_edge a"
  and all:"\<forall>nx \<in> N. \<exists>a'. valid_edge a' \<and> sourcenode a' = sourcenode a \<and>
    targetnode a' = nx \<and> n strongly-postdominates nx"
  obtains a' where "valid_edge a'" and "sourcenode a' =  sourcenode a"
  and "targetnode a' \<notin> N"
proof -
  have "\<exists>a'. valid_edge a' \<and> sourcenode a' =  sourcenode a \<and> targetnode a' \<notin> N"
  proof(cases "n postdominates (sourcenode a)")
    case False
    with valid_edge valid obtain a' where sources:"sourcenode a = sourcenode a'"
      and valid_edge':"valid_edge a'" and "\<not> n postdominates targetnode a'"
      by -(erule not_postdominate_source_not_postdominate_target)
    with all have "targetnode a' \<notin> N" by(auto simp:strong_postdominate_def)
    with sources[THEN sym] valid_edge' show ?thesis by blast
  next
    case True
    let ?M = "{n'. \<exists>a'. valid_edge a' \<and> sourcenode a' =  sourcenode a \<and> 
                         targetnode a' = n'}"
    let ?M' = "{n'. \<exists>a'. valid_edge a' \<and> sourcenode a' =  sourcenode a \<and> 
                          targetnode a' = n' \<and> n strongly-postdominates n'}"
    let ?N' = "(\<lambda>n'. SOME i. i \<ge> 1 \<and> 
      (\<forall>as nx. n' -as\<rightarrow>* nx \<and> length as \<ge> i 
                                \<longrightarrow> n \<in> set(sourcenodes as))) ` N"
    obtain k where k:"k = Max ?N'" by simp
    have eq:"{x \<in> ?M. (\<lambda>n'. n strongly-postdominates n') x} = ?M'" by auto
    from valid_edge have "finite ?M" by(simp add:successor_set_finite)
    hence "finite {x \<in> ?M. (\<lambda>n'. n strongly-postdominates n') x}" by simp
    with eq have finM':"finite ?M'" by simp
    from all have "N \<subseteq> ?M'" by auto
    with finM' have "finite N" by(auto intro:finite_subset)
    hence finN':"finite ?N'" by fastsimp
    show ?thesis
    proof(rule ccontr)
      assume "\<not> (\<exists>a'. valid_edge a' \<and> sourcenode a' = sourcenode a \<and> 
                      targetnode a' \<notin> N)"
      hence allImp:"\<forall>a'. valid_edge a' \<and> sourcenode a' = sourcenode a
                         \<longrightarrow> targetnode a' \<in> N" by blast
      from True not_spd
      have allPaths:"\<forall>k \<ge> 1. \<exists>as nx. sourcenode a -as\<rightarrow>* nx \<and> length as \<ge> k 
	\<and> n \<notin> set(sourcenodes as)" by(auto simp:strong_postdominate_def)
      with k obtain as nx where "sourcenode a -as\<rightarrow>* nx"
	and length:"length as \<ge> k + 1" and notin:"n \<notin> set(sourcenodes as)"
	by (erule_tac x="k + 1" in allE) auto
      then obtain ax as' where as:"as = ax#as'" and "valid_edge ax"
	and "sourcenode ax = sourcenode a"
	and path:"targetnode ax -as'\<rightarrow>* nx"
	by -(erule path.cases,auto)
      with allImp have inN:"targetnode ax \<in> N" by fastsimp
      with all have spd':"n strongly-postdominates (targetnode ax)"
	by auto
      then obtain k' where k':"k' = (SOME i. i \<ge> 1 \<and>
	(\<forall>as nx. targetnode ax -as\<rightarrow>* nx \<and> length as \<ge> i 
	         \<longrightarrow> n \<in> set(sourcenodes as)))" by simp
      with spd' have "k' \<ge> 1 \<and> (\<forall>as nx. targetnode ax -as\<rightarrow>* nx \<and> length as \<ge> k'
        \<longrightarrow> n \<in> set(sourcenodes as))"
	by(auto elim!:someI_ex simp:strong_postdominate_def)
      hence "k' \<ge> 1"
	and spdAll:"\<forall>as nx. targetnode ax -as\<rightarrow>* nx \<and> length as \<ge> k'
	\<longrightarrow> n \<in> set(sourcenodes as)"
	by simp_all
      from k' inN have "k' \<in> ?N'" by blast
      moreover
      from this inN have "?N' \<noteq> {}" by auto
      ultimately have "k' \<le> Max ?N'" using finN' by(fastsimp intro:Max_ge)
      with k have "k' \<le> k" by simp
      with path as length spdAll have "n \<in> set(sourcenodes as')"
	by fastsimp
      with as notin show False by(simp add:sourcenodes_def)
    qed
  qed
  with that show ?thesis by blast
qed



lemma not_strong_postdominate_predecessor_successor:
  assumes not_spd:"\<not> n strongly-postdominates (sourcenode a)"
  and valid:"valid_node n" and valid_edge:"valid_edge a"
  obtains a' where "valid_edge a'" and "sourcenode a' = sourcenode a"
  and "\<not> n strongly-postdominates (targetnode a')"
proof -
  have "\<exists>a'. valid_edge a' \<and> sourcenode a' = sourcenode a \<and> 
             \<not> n strongly-postdominates (targetnode a')"
  proof(rule ccontr)
    assume "\<not> (\<exists>a'. valid_edge a' \<and> sourcenode a' = sourcenode a \<and>
            \<not> n strongly-postdominates targetnode a')"
    hence all:"\<forall>a'. valid_edge a' \<and> sourcenode a' = sourcenode a \<longrightarrow> 
                    n strongly-postdominates (targetnode a')" by auto
    let ?N = "{n'. \<exists>a'. sourcenode a' =  sourcenode a \<and> valid_edge a' \<and> 
                        targetnode a' = n'}"
    from all have "\<forall>nx \<in> ?N. \<exists>a'. valid_edge a' \<and> sourcenode a' = sourcenode a \<and> 
      targetnode a' = nx \<and> n strongly-postdominates nx"
      by auto
    with not_spd valid valid_edge obtain a' where "valid_edge a'" 
      and "sourcenode a' =  sourcenode a" and "targetnode a' \<notin> ?N"
      by(erule not_strong_postdominate_successor_set)
    thus False by auto
  qed
  with that show ?thesis by blast
qed


end


end
