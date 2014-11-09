section {* Postdomination *}

theory Postdomination imports CFGExit begin

subsection {* Standard Postdomination *}

locale Postdomination = CFGExit sourcenode targetnode kind valid_edge Entry Exit 
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Exit :: "'node" ("'('_Exit'_')") +
  assumes Entry_path:"valid_node n \<Longrightarrow> \<exists>as. (_Entry_) -as\<rightarrow>* n"
  and Exit_path:"valid_node n \<Longrightarrow> \<exists>as. n -as\<rightarrow>* (_Exit_)"

begin

definition postdominate :: "'node \<Rightarrow> 'node \<Rightarrow> bool" ("_ postdominates _" [51,0])
where postdominate_def:"n' postdominates n \<equiv> 
    (valid_node n \<and> valid_node n' \<and>
    ((\<forall>as. n -as\<rightarrow>* (_Exit_) \<longrightarrow> n' \<in> set (sourcenodes as))))"


lemma postdominate_implies_path: 
  assumes "n' postdominates n" obtains as where "n -as\<rightarrow>* n'"
proof(atomize_elim)
  from `n' postdominates n` have "valid_node n"
    and all:"\<forall>as. n -as\<rightarrow>* (_Exit_) \<longrightarrow> n' \<in> set(sourcenodes as)"
    by(auto simp:postdominate_def)
  from `valid_node n` obtain as where "n -as\<rightarrow>* (_Exit_)" by(auto dest:Exit_path)
  with all have "n' \<in> set(sourcenodes as)" by simp
  then obtain ns ns' where "sourcenodes as = ns@n'#ns'" by(auto dest:split_list)
  then obtain as' a as'' where "sourcenodes as' = ns" 
    and "sourcenode a = n'" and "as = as'@a#as''"
    by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
  from `n -as\<rightarrow>* (_Exit_)` `as = as'@a#as''` have "n -as'\<rightarrow>* sourcenode a"
    by(fastforce dest:path_split)
  with `sourcenode a = n'` show "\<exists>as. n -as\<rightarrow>* n'" by blast
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
      by(fastforce intro:path_sourcenode)
    with notempty have "(_Entry_) \<in> set (sourcenodes as)"
      by(fastforce intro:hd_in_set simp:sourcenodes_def) }
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
      by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
    from as path have "n -as'@a#as''\<rightarrow>* (_Exit_)" by simp
    with source have path':"n'' -a#as''\<rightarrow>* (_Exit_)"
      by(fastforce dest:path_split_second)
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
  from valid obtain as where path1:"n -as\<rightarrow>* (_Exit_)" by(fastforce dest:Exit_path)
  from valid' obtain as' where path2:"n' -as'\<rightarrow>* (_Exit_)" by(fastforce dest:Exit_path)
  from pd1 path1 have "\<exists>nx \<in> set(sourcenodes as). nx = n'"
    by(simp add:postdominate_def)
  then obtain ns ns' where sources:"sourcenodes as = ns@n'#ns'"
    and all:"\<forall>nx \<in> set ns'. nx \<noteq> n'"
    by(fastforce elim!: rightmost_element_property)
  from sources obtain asx a asx' where ns':"ns' = sourcenodes asx'"
    and as:"as = asx@a#asx'" and source:"sourcenode a = n'"
    by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
  from path1 as have "n -asx@a#asx'\<rightarrow>* (_Exit_)" by simp
  with source have "n' -a#asx'\<rightarrow>* (_Exit_)" by(fastforce dest:path_split_second)
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
      by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
    with path1 as have "n -(asx@a#asi)@a'#asi'\<rightarrow>* (_Exit_)" by simp
    with source' have "n -a'#asi'\<rightarrow>* (_Exit_)" by(fastforce dest:path_split_second)
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
        `valid_edge a`
      show ?thesis by blast
    next
      case False
      from IH[OF `n' postdominates nx` this] show ?thesis
        by clarsimp(rule_tac x="a#as'" in exI,clarsimp)
    qed
  qed simp
qed


lemma Exit_no_postdominator:
  "(_Exit_) postdominates n \<Longrightarrow> False"
by(fastforce dest:Exit_path simp:postdominate_def)


lemma postdominate_path_targetnode:
  assumes "n' postdominates n" and "n -as\<rightarrow>* n''" and "n' \<notin> set(sourcenodes as)"
  shows "n' postdominates n''"
proof -
  from `n' postdominates n` have "valid_node n" and "valid_node n'"
    and all:"\<forall>as''. n -as''\<rightarrow>* (_Exit_) \<longrightarrow> n' \<in> set(sourcenodes as'')"
    by(simp_all add:postdominate_def)
  from `n -as\<rightarrow>* n''` have "valid_node n''" by(fastforce dest:path_valid_node)
  have "\<forall>as''. n'' -as''\<rightarrow>* (_Exit_) \<longrightarrow> n' \<in> set(sourcenodes as'')"
  proof(rule ccontr)
    assume "\<not> (\<forall>as''. n'' -as''\<rightarrow>* (_Exit_) \<longrightarrow> n' \<in> set (sourcenodes as''))"
    then obtain as'' where "n'' -as''\<rightarrow>* (_Exit_)"
      and "n' \<notin> set (sourcenodes as'')" by blast
    from `n -as\<rightarrow>* n''` `n'' -as''\<rightarrow>* (_Exit_)` have "n -as@as''\<rightarrow>* (_Exit_)" 
      by(rule path_Append)
    with `n' \<notin> set(sourcenodes as)` `n' \<notin> set (sourcenodes as'')`
    have "n' \<notin> set (sourcenodes (as@as''))"
      by(simp add:sourcenodes_def)
    with `n -as@as''\<rightarrow>* (_Exit_)` `n' postdominates n` show False
      by(simp add:postdominate_def)
  qed
  with `valid_node n'` `valid_node n''` show ?thesis by(simp add:postdominate_def)
qed


lemma not_postdominate_source_not_postdominate_target:
  assumes "\<not> n postdominates (sourcenode a)" and "valid_node n" and "valid_edge a"
  obtains ax where "sourcenode a = sourcenode ax" and "valid_edge ax"
  and "\<not> n postdominates targetnode ax"
proof(atomize_elim)
  show "\<exists>ax. sourcenode a = sourcenode ax \<and> valid_edge ax \<and> 
    \<not> n postdominates targetnode ax"
  proof -
    from assms obtain asx 
      where "sourcenode a -asx\<rightarrow>* (_Exit_)"
      and "n \<notin> set(sourcenodes asx)" by(auto simp:postdominate_def)
    from `sourcenode a -asx\<rightarrow>* (_Exit_)` `valid_edge a` 
    obtain ax asx' where [simp]:"asx = ax#asx'"
      apply - apply(erule path.cases)
      apply(drule_tac s="(_Exit_)" in sym)
      apply simp
      apply(drule Exit_source)
      by simp_all
    with `sourcenode a -asx\<rightarrow>* (_Exit_)` have "sourcenode a -[]@ax#asx'\<rightarrow>* (_Exit_)"
      by simp
    hence "valid_edge ax" and "sourcenode a = sourcenode ax"
      and "targetnode ax -asx'\<rightarrow>* (_Exit_)"
      by(fastforce dest:path_split)+
    with `n \<notin> set(sourcenodes asx)` have "\<not> n postdominates targetnode ax"
      by(fastforce simp:postdominate_def sourcenodes_def)
    with `sourcenode a = sourcenode ax` `valid_edge ax` show ?thesis by blast
  qed
qed


lemma inner_node_Entry_edge:
  assumes "inner_node n" 
  obtains a where "valid_edge a" and "inner_node (targetnode a)"
  and "sourcenode a = (_Entry_)"
proof(atomize_elim)
  from `inner_node n` have "valid_node n" by(rule inner_is_valid)
  then obtain as where "(_Entry_) -as\<rightarrow>* n" by(fastforce dest:Entry_path)
  show "\<exists>a. valid_edge a \<and> inner_node (targetnode a) \<and> sourcenode a = (_Entry_)"
  proof(cases "as = []")
    case True
    with `inner_node n` `(_Entry_) -as\<rightarrow>* n` have False 
      by(fastforce simp:inner_node_def)
    thus ?thesis by simp
  next
    case False
    with `(_Entry_) -as\<rightarrow>* n` obtain a' as' where "as = a'#as'"
      and "(_Entry_) = sourcenode a'" and "valid_edge a'" 
      and "targetnode a' -as'\<rightarrow>* n" 
      by -(erule path_split_Cons)
    from `valid_edge a'` have "valid_node (targetnode a')" by simp
    thus ?thesis
    proof(cases "targetnode a'" rule:valid_node_cases)
      case Entry
      from `valid_edge a'` this have False by(rule Entry_target)
      thus ?thesis by simp
    next
      case Exit
      with `targetnode a' -as'\<rightarrow>* n` `inner_node n`
      have False by simp (drule path_Exit_source,auto simp:inner_node_def)
      thus ?thesis by simp
    next
      case inner
      with `valid_edge a'` `(_Entry_) = sourcenode a'` show ?thesis by simp blast
    qed
  qed
qed


lemma inner_node_Exit_edge:
  assumes "inner_node n" 
  obtains a where "valid_edge a" and "inner_node (sourcenode a)"
  and "targetnode a = (_Exit_)"
proof(atomize_elim)
  from `inner_node n` have "valid_node n" by(rule inner_is_valid)
  then obtain as where "n -as\<rightarrow>* (_Exit_)" by(fastforce dest:Exit_path)
  show "\<exists>a. valid_edge a \<and> inner_node (sourcenode a) \<and> targetnode a = (_Exit_)"
  proof(cases "as = []")
    case True
    with `inner_node n` `n -as\<rightarrow>* (_Exit_)` have False by fastforce
    thus ?thesis by simp
  next
    case False
    with `n -as\<rightarrow>* (_Exit_)` obtain a' as' where "as = as'@[a']" 
      and "n -as'\<rightarrow>* sourcenode a'" and "valid_edge a'" 
      and "(_Exit_) = targetnode a'" by -(erule path_split_snoc)
    from `valid_edge a'` have "valid_node (sourcenode a')" by simp
    thus ?thesis
    proof(cases "sourcenode a'" rule:valid_node_cases)
      case Entry
      with `n -as'\<rightarrow>* sourcenode a'` `inner_node n`
      have False by simp (drule path_Entry_target,auto simp:inner_node_def)
      thus ?thesis by simp
    next
      case Exit
      from `valid_edge a'` this have False by(rule Exit_source)
      thus ?thesis by simp
    next
      case inner
      with `valid_edge a'` `(_Exit_) = targetnode a'` show ?thesis by simp blast
    qed
  qed
qed




end

subsection {* Strong Postdomination *}


locale StrongPostdomination = 
  Postdomination sourcenode targetnode kind valid_edge Entry Exit 
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Exit :: "'node" ("'('_Exit'_')") +
  assumes successor_set_finite: "valid_node n \<Longrightarrow> 
  finite {n'. \<exists>a'. valid_edge a' \<and> sourcenode a' = n \<and> targetnode a' = n'}"

begin

definition  strong_postdominate :: "'node \<Rightarrow> 'node \<Rightarrow> bool" 
("_ strongly-postdominates _" [51,0])
where strong_postdominate_def:"n' strongly-postdominates n \<equiv>
  (n' postdominates n \<and> 
  (\<exists>k \<ge> 1. \<forall>as nx. n -as\<rightarrow>* nx \<and> 
                    length as \<ge> k \<longrightarrow> n' \<in> set(sourcenodes as)))"


lemma strong_postdominate_prop_smaller_path:
  assumes all:"\<forall>as nx. n -as\<rightarrow>* nx \<and> length as \<ge> k \<longrightarrow> n' \<in> set(sourcenodes as)"
  and "n -as\<rightarrow>* n''" and "length as \<ge> k"
  obtains as' as'' where "n -as'\<rightarrow>* n'" and "length as' < k" and "n' -as''\<rightarrow>* n''"
  and "as = as'@as''"
proof(atomize_elim)
  show "\<exists>as' as''. n -as'\<rightarrow>* n' \<and> length as' < k \<and> n' -as''\<rightarrow>* n'' \<and> as = as'@as''"
  proof(rule ccontr)
    assume "\<not> (\<exists>as' as''. n -as'\<rightarrow>* n' \<and> length as' < k \<and> n' -as''\<rightarrow>* n'' \<and> 
                          as = as'@as'')"
    hence all':"\<forall>as' as''. n -as'\<rightarrow>* n' \<and> n' -as''\<rightarrow>* n'' \<and> as = as'@as'' 
      \<longrightarrow> length as' \<ge> k" by fastforce
    from all `n -as\<rightarrow>* n''` `length as \<ge> k` have "\<exists>nx \<in> set(sourcenodes as). nx = n'"
      by fastforce
    then obtain ns ns' where "sourcenodes as = ns@n'#ns'"
      and "\<forall>nx \<in> set ns. nx \<noteq> n'"
      by(fastforce elim!:split_list_first_propE)
    then obtain asx a asx' where [simp]:"ns = sourcenodes asx"
      and [simp]:"as = asx@a#asx'" and "sourcenode a = n'"
      by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
    from `n -as\<rightarrow>* n''` have "n -asx@a#asx'\<rightarrow>* n''" by simp
    with `sourcenode a = n'` have "n -asx\<rightarrow>* n'" and "valid_edge a"
      and "targetnode a -asx'\<rightarrow>* n''" by(fastforce dest:path_split)+
    with `sourcenode a = n'` have "n' -a#asx'\<rightarrow>* n''" by(fastforce intro:Cons_path)
    with `n -asx\<rightarrow>* n'` all' have "length asx \<ge> k" by simp
    with `n -asx\<rightarrow>* n'` all have "n' \<in> set(sourcenodes asx)" by fastforce
    with `\<forall>nx \<in> set ns. nx \<noteq> n'` show False by fastforce
  qed
qed



lemma strong_postdominate_refl:
  assumes "valid_node n" and "n \<noteq> (_Exit_)"
  shows "n strongly-postdominates n"
proof -
  from assms have "n postdominates n" by(rule postdominate_refl)
  { fix as nx assume "n -as\<rightarrow>* nx" and "length as \<ge> 1"
    then obtain a' as' where [simp]:"as = a'#as'" by(cases as) auto
    with `n -as\<rightarrow>* nx` have "n -[]@a'#as'\<rightarrow>* nx" by simp
    hence "n = sourcenode a'" by(fastforce dest:path_split)
    hence "n \<in> set(sourcenodes as)" by(simp add:sourcenodes_def) }
  hence "\<forall>as nx. n -as\<rightarrow>* nx \<and> length as \<ge> 1 \<longrightarrow> n \<in> set(sourcenodes as)"
    by auto
  hence "\<exists>k \<ge> 1. \<forall>as nx. n -as\<rightarrow>* nx \<and> length as \<ge> k \<longrightarrow> n \<in> set(sourcenodes as)"
    by blast
  with `n postdominates n` show ?thesis by(simp add:strong_postdominate_def)
qed


lemma strong_postdominate_trans:
  assumes "n'' strongly-postdominates n" and "n' strongly-postdominates n''"
  shows "n' strongly-postdominates n"
proof -
  from `n'' strongly-postdominates n` have "n'' postdominates n"
    and paths1:"\<exists>k \<ge> 1. \<forall>as nx. n -as\<rightarrow>* nx \<and> length as \<ge> k 
             \<longrightarrow> n'' \<in> set(sourcenodes as)"
    by(auto simp only:strong_postdominate_def)
  from paths1 obtain k1 
    where all1:"\<forall>as nx. n -as\<rightarrow>* nx \<and> length as \<ge> k1 \<longrightarrow> n'' \<in> set(sourcenodes as)"
    and "k1 \<ge> 1" by blast
  from `n' strongly-postdominates n''` have "n' postdominates n''"
    and paths2:"\<exists>k \<ge> 1. \<forall>as nx. n'' -as\<rightarrow>* nx \<and> length as \<ge> k 
             \<longrightarrow> n' \<in> set(sourcenodes as)"
    by(auto simp only:strong_postdominate_def)
  from paths2 obtain k2 
    where all2:"\<forall>as nx. n'' -as\<rightarrow>* nx \<and> length as \<ge> k2 \<longrightarrow> n' \<in> set(sourcenodes as)"
    and "k2 \<ge> 1" by blast
  from `n'' postdominates n` `n' postdominates n''` 
  have "n' postdominates n" by(rule postdominate_trans)
  { fix as nx assume "n -as\<rightarrow>* nx" and "length as \<ge> k1 + k2"
    hence "length as \<ge> k1" by fastforce
    with `n -as\<rightarrow>* nx` all1 obtain asx asx' where "n -asx\<rightarrow>* n''"
      and "length asx < k1" and "n'' -asx'\<rightarrow>* nx"
      and [simp]:"as = asx@asx'" by -(erule strong_postdominate_prop_smaller_path)
    with `length as \<ge> k1 + k2` have "length asx' \<ge> k2" by fastforce
    with `n'' -asx'\<rightarrow>* nx` all2 have "n' \<in> set(sourcenodes asx')" by fastforce
    hence "n' \<in> set(sourcenodes as)" by(simp add:sourcenodes_def) }
  with `k1 \<ge> 1` `k2 \<ge> 1` have "\<exists>k \<ge> 1. \<forall>as nx. n -as\<rightarrow>* nx \<and> length as \<ge> k 
             \<longrightarrow> n' \<in> set(sourcenodes as)"
    by(rule_tac x="k1 + k2" in exI,auto)
  with `n' postdominates n` show ?thesis by(simp add:strong_postdominate_def)
qed


lemma strong_postdominate_antisym:
  "\<lbrakk>n' strongly-postdominates n; n strongly-postdominates n'\<rbrakk> \<Longrightarrow> n = n'"
by(fastforce intro:postdominate_antisym simp:strong_postdominate_def)


lemma strong_postdominate_path_branch:
  assumes "n -as\<rightarrow>* n''" and "n' strongly-postdominates n''" 
  and "\<not> n' strongly-postdominates n"
  obtains a as' as'' where "as = as'@a#as''" and "valid_edge a"
  and "\<not> n' strongly-postdominates (sourcenode a)" 
  and "n' strongly-postdominates (targetnode a)"
proof(atomize_elim)
  from assms
  show "\<exists>as' a as''. as = as'@a#as'' \<and> valid_edge a \<and> 
    \<not> n' strongly-postdominates (sourcenode a) \<and> 
      n' strongly-postdominates (targetnode a)"
  proof(induct rule:path.induct)
    case (Cons_path n'' as nx a n)
    note IH = `\<lbrakk>n' strongly-postdominates nx; \<not> n' strongly-postdominates n''\<rbrakk>
      \<Longrightarrow> \<exists>as' a as''. as = as'@a#as'' \<and> valid_edge a \<and>
        \<not> n' strongly-postdominates sourcenode a \<and> 
          n' strongly-postdominates targetnode a`
    show ?case
    proof(cases "n' strongly-postdominates n''")
      case True
      with `\<not> n' strongly-postdominates n` `sourcenode a = n` `targetnode a = n''`
        `valid_edge a`
      show ?thesis by blast
    next
      case False
      from IH[OF `n' strongly-postdominates nx` this] show ?thesis
        by clarsimp(rule_tac x="a#as'" in exI,clarsimp)
    qed
  qed simp
qed


lemma Exit_no_strong_postdominator:
  "\<lbrakk>(_Exit_) strongly-postdominates n; n -as\<rightarrow>* (_Exit_)\<rbrakk> \<Longrightarrow> False"
by(fastforce intro:Exit_no_postdominator path_valid_node simp:strong_postdominate_def)


lemma strong_postdominate_path_targetnode:
  assumes "n' strongly-postdominates n" and "n -as\<rightarrow>* n''"
  and "n' \<notin> set(sourcenodes as)"
  shows "n' strongly-postdominates n''"
proof -
  from `n' strongly-postdominates n` have "n' postdominates n"
    and "\<exists>k \<ge> 1. \<forall>as nx. n -as\<rightarrow>* nx \<and> length as \<ge> k 
             \<longrightarrow> n' \<in> set(sourcenodes as)"
    by(auto simp only:strong_postdominate_def)
  then obtain k where "k \<ge> 1"
    and paths:"\<forall>as nx. n -as\<rightarrow>* nx \<and> length as \<ge> k 
                         \<longrightarrow> n' \<in> set(sourcenodes as)" by auto
  from `n' postdominates n` `n -as\<rightarrow>* n''` `n' \<notin> set(sourcenodes as)`
  have "n' postdominates n''"
    by(rule postdominate_path_targetnode)
  { fix as' nx assume "n'' -as'\<rightarrow>* nx" and "length as' \<ge> k"
    with `n -as\<rightarrow>* n''` have "n -as@as'\<rightarrow>* nx" and "length (as@as') \<ge> k"
      by(auto intro:path_Append)
    with paths have "n' \<in> set(sourcenodes (as@as'))" by fastforce
    with `n' \<notin> set(sourcenodes as)` have "n' \<in> set(sourcenodes as')"
      by(fastforce simp:sourcenodes_def) }
  with `k \<ge> 1` have "\<exists>k \<ge> 1. \<forall>as' nx. n'' -as'\<rightarrow>* nx \<and> length as' \<ge> k 
             \<longrightarrow> n' \<in> set(sourcenodes as')" by auto
  with `n' postdominates n''` show ?thesis by(simp add:strong_postdominate_def)
qed


lemma not_strong_postdominate_successor_set:
  assumes "\<not> n strongly-postdominates (sourcenode a)" and "valid_node n"
  and "valid_edge a"
  and all:"\<forall>nx \<in> N. \<exists>a'. valid_edge a' \<and> sourcenode a' = sourcenode a \<and>
    targetnode a' = nx \<and> n strongly-postdominates nx"
  obtains a' where "valid_edge a'" and "sourcenode a' =  sourcenode a"
  and "targetnode a' \<notin> N"
proof(atomize_elim)
  show "\<exists>a'. valid_edge a' \<and> sourcenode a' =  sourcenode a \<and> targetnode a' \<notin> N"
  proof(cases "n postdominates (sourcenode a)")
    case False
    with `valid_edge a` `valid_node n`
    obtain a' where [simp]:"sourcenode a = sourcenode a'"
      and "valid_edge a'" and "\<not> n postdominates targetnode a'"
      by -(erule not_postdominate_source_not_postdominate_target)
    with all have "targetnode a' \<notin> N" by(auto simp:strong_postdominate_def)
    with `valid_edge a'` show ?thesis by simp blast
  next
    case True
    let ?M = "{n'. \<exists>a'. valid_edge a' \<and> sourcenode a' =  sourcenode a \<and> 
                         targetnode a' = n'}"
    let ?M' = "{n'. \<exists>a'. valid_edge a' \<and> sourcenode a' =  sourcenode a \<and> 
                          targetnode a' = n' \<and> n strongly-postdominates n'}"
    let ?N' = "(\<lambda>n'. SOME i. i \<ge> 1 \<and> 
      (\<forall>as nx. n' -as\<rightarrow>* nx \<and> length as \<ge> i 
                                \<longrightarrow> n \<in> set(sourcenodes as))) ` N"
    obtain k where [simp]:"k = Max ?N'" by simp
    have eq:"{x \<in> ?M. (\<lambda>n'. n strongly-postdominates n') x} = ?M'" by auto
    from `valid_edge a` have "finite ?M" by(simp add:successor_set_finite)
    hence "finite {x \<in> ?M. (\<lambda>n'. n strongly-postdominates n') x}" by fastforce
    with eq have "finite ?M'" by simp
    from all have "N \<subseteq> ?M'" by auto
    with `finite ?M'` have "finite N" by(auto intro:finite_subset)
    hence "finite ?N'" by fastforce
    show ?thesis
    proof(rule ccontr)
      assume "\<not> (\<exists>a'. valid_edge a' \<and> sourcenode a' = sourcenode a \<and> 
                      targetnode a' \<notin> N)"
      hence allImp:"\<forall>a'. valid_edge a' \<and> sourcenode a' = sourcenode a
                         \<longrightarrow> targetnode a' \<in> N" by blast
      from True `\<not> n strongly-postdominates (sourcenode a)`
      have allPaths:"\<forall>k \<ge> 1. \<exists>as nx. sourcenode a -as\<rightarrow>* nx \<and> length as \<ge> k 
        \<and> n \<notin> set(sourcenodes as)" by(auto simp:strong_postdominate_def)
      then obtain as nx where "sourcenode a -as\<rightarrow>* nx"
        and "length as \<ge> k + 1" and "n \<notin> set(sourcenodes as)"
        by (erule_tac x="k + 1" in allE) auto
      then obtain ax as' where [simp]:"as = ax#as'" and "valid_edge ax"
        and "sourcenode ax = sourcenode a" and "targetnode ax -as'\<rightarrow>* nx"
        by -(erule path.cases,auto)
      with allImp have "targetnode ax \<in> N" by fastforce
      with all have "n strongly-postdominates (targetnode ax)"
        by auto
      then obtain k' where k':"k' = (SOME i. i \<ge> 1 \<and>
        (\<forall>as nx. targetnode ax -as\<rightarrow>* nx \<and> length as \<ge> i 
                 \<longrightarrow> n \<in> set(sourcenodes as)))" by simp
      with `n strongly-postdominates (targetnode ax)`
      have "k' \<ge> 1 \<and> (\<forall>as nx. targetnode ax -as\<rightarrow>* nx \<and> length as \<ge> k'
        \<longrightarrow> n \<in> set(sourcenodes as))"
        by(auto elim!:someI_ex simp:strong_postdominate_def)
      hence "k' \<ge> 1"
        and spdAll:"\<forall>as nx. targetnode ax -as\<rightarrow>* nx \<and> length as \<ge> k'
        \<longrightarrow> n \<in> set(sourcenodes as)"
        by simp_all
      from `targetnode ax \<in> N` k' have "k' \<in> ?N'" by blast
      moreover
      from this `targetnode ax \<in> N` have "?N' \<noteq> {}" by auto
      ultimately have "k' \<le> Max ?N'" using `finite ?N'` by(fastforce intro:Max_ge)
      hence "k' \<le> k" by simp
      with `targetnode ax -as'\<rightarrow>* nx` `length as \<ge> k + 1` spdAll 
      have "n \<in> set(sourcenodes as')"
        by fastforce
      with `n \<notin> set(sourcenodes as)` show False by(simp add:sourcenodes_def)
    qed
  qed
qed



lemma not_strong_postdominate_predecessor_successor:
  assumes "\<not> n strongly-postdominates (sourcenode a)"
  and "valid_node n" and "valid_edge a"
  obtains a' where "valid_edge a'" and "sourcenode a' = sourcenode a"
  and "\<not> n strongly-postdominates (targetnode a')"
proof(atomize_elim)
  show "\<exists>a'. valid_edge a' \<and> sourcenode a' = sourcenode a \<and> 
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
    with assms obtain a' where "valid_edge a'" 
      and "sourcenode a' =  sourcenode a" and "targetnode a' \<notin> ?N"
      by(erule not_strong_postdominate_successor_set)
    thus False by auto
  qed
qed


end


end
