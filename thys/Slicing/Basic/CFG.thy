header {* \isaheader{CFG} *}

theory CFG imports BasicDefs begin

subsection {* The abstract CFG *}

locale CFG =
  fixes sourcenode :: "'edge \<Rightarrow> 'node"
  fixes targetnode :: "'edge \<Rightarrow> 'node"
  fixes kind :: "'edge \<Rightarrow> 'state edge_kind"
  fixes valid_edge :: "'edge \<Rightarrow> bool"
  fixes Entry::"'node" ("'('_Entry'_')")
  assumes Entry_target [dest]: "\<lbrakk>valid_edge a; targetnode a = (_Entry_)\<rbrakk> \<Longrightarrow> False"
  and edge_det: 
  "\<lbrakk>valid_edge a; valid_edge a'; sourcenode a = sourcenode a'; 
    targetnode a = targetnode a'\<rbrakk> \<Longrightarrow> a = a'"

begin

definition valid_node :: "'node \<Rightarrow> bool"
  where "valid_node n \<equiv> 
  (\<exists>a. valid_edge a \<and> (n = sourcenode a \<or> n = targetnode a))"

lemma [simp]: "valid_edge a \<Longrightarrow> valid_node (sourcenode a)"
  by(fastsimp simp:valid_node_def)

lemma [simp]: "valid_edge a \<Longrightarrow> valid_node (targetnode a)"
  by(fastsimp simp:valid_node_def)


subsection {* CFG paths and lemmas *}

inductive path :: "'node \<Rightarrow> 'edge list \<Rightarrow> 'node \<Rightarrow> bool"
  ("_ -_\<rightarrow>* _" [51,0,0] 80)
where 
  empty_path:"valid_node n \<Longrightarrow> n -[]\<rightarrow>* n"

  | Cons_path:
  "\<lbrakk>n'' -as\<rightarrow>* n'; valid_edge a; sourcenode a = n; targetnode a = n''\<rbrakk>
    \<Longrightarrow> n -a#as\<rightarrow>* n'"


lemma path_valid_node:"n -as\<rightarrow>* n' \<Longrightarrow> valid_node n \<and> valid_node n'"
  by(induct rule:path.induct,auto)

lemma empty_path_nodes [simp]:"n -[]\<rightarrow>* n' \<Longrightarrow> n = n'"
by(fastsimp elim:path.cases)

lemma path_edge:"valid_edge a \<Longrightarrow> sourcenode a -[a]\<rightarrow>* targetnode a"
  by(fastsimp intro:Cons_path empty_path)

lemma path_Entry_target:
  "\<lbrakk>n -as\<rightarrow>* n'; n' = (_Entry_)\<rbrakk> \<Longrightarrow> n = (_Entry_) \<and> as = []"
proof(induct rule:path.induct)
  case (Cons_path n'' as n' a n)
  from `n' = (_Entry_)` `n' = (_Entry_) \<Longrightarrow> n'' = (_Entry_) \<and> as = []`
  have "n'' = (_Entry_)" by simp
  with `targetnode a = n''` `valid_edge a` have False
    by -(rule Entry_target,simp_all)
  thus ?case by simp
qed simp

lemma [dest]:"n -as\<rightarrow>* (_Entry_) \<Longrightarrow> n = (_Entry_) \<and> as = []"
  by(fastsimp elim!:path_Entry_target)


lemma path_Append:"\<lbrakk>n -as\<rightarrow>* n''; n'' -as'\<rightarrow>* n'\<rbrakk> 
  \<Longrightarrow> n -as@as'\<rightarrow>* n'"
by(induct rule:path.induct,auto intro:Cons_path)


lemma path_split:"n -as@a#as'\<rightarrow>* n'
  \<Longrightarrow> (n -as\<rightarrow>* sourcenode a) \<and> (sourcenode a -[a]\<rightarrow>* targetnode a) \<and>
      (valid_edge a) \<and> (targetnode a -as'\<rightarrow>* n')"
proof(induct as arbitrary:n)
  case Nil
  thus ?case by(auto elim:path.cases intro!:empty_path path_edge)
next
  case (Cons ax asx)
  note IH = `\<And>n. n -asx@a#as'\<rightarrow>* n' \<Longrightarrow>
    (n -asx\<rightarrow>* sourcenode a) \<and> (sourcenode a -[a]\<rightarrow>* targetnode a) \<and>
    (valid_edge a) \<and> (targetnode a -as'\<rightarrow>* n')`
  from `n -(ax#asx)@a#as'\<rightarrow>* n'` have "sourcenode ax = n"
    and path:"targetnode ax -asx@a#as'\<rightarrow>* n'"
    and "valid_edge ax"
    by(auto elim:path.cases)
  from IH[OF path] have path1:"targetnode ax -asx\<rightarrow>* sourcenode a"
    and rest:"sourcenode a -[a]\<rightarrow>* targetnode a" "valid_edge a" 
             "targetnode a -as'\<rightarrow>* n'"
    by simp_all
  from path1 `sourcenode ax = n` `valid_edge ax` have "n -ax#asx\<rightarrow>* sourcenode a"
    by(fastsimp intro:Cons_path)
  with rest show ?case by fastsimp
qed


lemma path_split_second:
  assumes path:"n -as@a#as'\<rightarrow>* n'"
  shows "sourcenode a -a#as'\<rightarrow>* n'"
proof -
  from path have "sourcenode a -[a]\<rightarrow>* targetnode a" 
    and "targetnode a -as'\<rightarrow>* n'"
    by(auto dest:path_split)
  thus ?thesis by(auto dest:path_Append)
qed


lemma path_Entry_Cons:
  assumes path:"(_Entry_) -as\<rightarrow>* n'" and notEntry:"n' \<noteq> (_Entry_)"
  shows "\<exists>n a. sourcenode a = (_Entry_) \<and> targetnode a = n \<and> 
               n -tl as\<rightarrow>* n' \<and> valid_edge a \<and> a = hd as"
proof -
  from path notEntry have notempty:"as \<noteq> []"
    by(cases as,auto elim:path.cases)
  then obtain a as' where as:"as = a#as'" by(cases as) auto
  with path have "(_Entry_) -[]@a#as'\<rightarrow>* n'" by simp
  hence "(_Entry_) = sourcenode a"
    and "sourcenode a -[a]\<rightarrow>* targetnode a"
    and "valid_edge a" 
    and "targetnode a -as'\<rightarrow>* n'"
    by(fastsimp dest:path_split)+
  with as show ?thesis by auto
qed


lemma path_det:
  "\<lbrakk>n -as\<rightarrow>* n'; n -as\<rightarrow>* n''\<rbrakk> \<Longrightarrow> n' = n''"
proof(induct as arbitrary:n)
  case Nil thus ?case by(auto elim:path.cases)
next
  case (Cons a' as')
  note IH = `\<And>n. \<lbrakk>n -as'\<rightarrow>* n'; n -as'\<rightarrow>* n''\<rbrakk> \<Longrightarrow> n' = n''`
  from `n -a'#as'\<rightarrow>* n'` have "n -[]@a'#as'\<rightarrow>* n'" by simp
  hence "targetnode a' -as'\<rightarrow>* n'"
    by(fastsimp dest:path_split)+
  from `n -a'#as'\<rightarrow>* n''` have "n -[]@a'#as'\<rightarrow>* n''" by simp
  hence "targetnode a' -as'\<rightarrow>* n''" by(fastsimp dest:path_split)+
  from IH[OF `targetnode a' -as'\<rightarrow>* n'` this] show ?thesis .
qed


subsection {* Some lemmas concerning source- and targetnodes of CFG paths *}

definition
  sourcenodes :: "'edge list \<Rightarrow> 'node list"
  where "sourcenodes xs \<equiv> map sourcenode xs"

definition
  kinds :: "'edge list \<Rightarrow> 'state edge_kind list"
  where "kinds xs \<equiv> map kind xs"

definition
  targetnodes :: "'edge list \<Rightarrow> 'node list"
  where "targetnodes xs \<equiv> map targetnode xs"


lemma path_sourcenode:
  assumes "n -as\<rightarrow>* n'" and "as \<noteq> []" shows "hd (sourcenodes as) = n"
proof -
  from `as \<noteq> []` obtain a' as' where "as = a'#as'" by(cases as) auto
  with `n -as\<rightarrow>* n'` have "n -[]@a'#as'\<rightarrow>* n'" by simp
  hence "sourcenode a' = n" by(auto elim:path.cases)
  with `as = a'#as'` show ?thesis by(simp add:sourcenodes_def)
qed


lemma path_targetnode:
  assumes "n -as\<rightarrow>* n'" and "as \<noteq> []" shows "last (targetnodes as) = n'"
proof -
  from `as \<noteq> []` obtain a' as' where "as = as'@[a']"
    by(induct as rule:rev_induct,auto)
  with `n -as\<rightarrow>* n'` have "n -as'@a'#[]\<rightarrow>* n'" by simp
  hence "sourcenode a' -a'#[]\<rightarrow>* n'" by(fastsimp dest:path_split intro:Cons_path)
  hence "targetnode a' = n'" by(auto elim:path.cases)
  with `as = as'@[a']` show ?thesis by(simp add:targetnodes_def)
qed


lemma sourcenodes_is_n_Cons_butlast_targetnodes:
  "\<lbrakk>n -as\<rightarrow>* n'; as \<noteq> []\<rbrakk> \<Longrightarrow> 
  sourcenodes as = n#(butlast (targetnodes as))"
proof(induct as arbitrary:n)
  case Nil thus ?case by simp
next
  case (Cons a' as')
  note path = `n -a' # as'\<rightarrow>* n'`
  note IH = `\<And>n. \<lbrakk>n -as'\<rightarrow>* n'; as' \<noteq> []\<rbrakk>
            \<Longrightarrow> sourcenodes as' = n#(butlast (targetnodes as'))`
  show ?case
  proof(cases "as' = []")
    case True
    with path have "sourcenode a' = n \<and> targetnode a' = n'" 
      by(auto elim:path.cases)
    with True show ?thesis by(simp add:sourcenodes_def targetnodes_def)
  next
    case False
    from path have "n -[]@a'#as'\<rightarrow>* n'" by simp
    with False have "n -[]\<rightarrow>* sourcenode a'" and "targetnode a' -as'\<rightarrow>* n'"
      by(fastsimp dest:path_split)+
    from `n -[]\<rightarrow>* sourcenode a'` have "n = sourcenode a'" by simp
    from IH[OF `targetnode a' -as'\<rightarrow>* n'` False] 
    have "sourcenodes as' = targetnode a' # butlast (targetnodes as')" .
    with `n = sourcenode a'` False 
    show ?thesis by(simp add:sourcenodes_def targetnodes_def)
  qed
qed


lemma targetnodes_is_tl_sourcenodes_App_n':
  "\<lbrakk>n -as\<rightarrow>* n'; as \<noteq> []\<rbrakk> \<Longrightarrow> targetnodes as = (tl (sourcenodes as))@[n']"
proof(induct as arbitrary:n' rule:rev_induct)
  case Nil thus ?case by simp
next
  case (snoc a' as')
  note IH = `\<And>n'. \<lbrakk>n -as'\<rightarrow>* n'; as' \<noteq> []\<rbrakk>
            \<Longrightarrow> targetnodes as' = tl (sourcenodes as') @ [n']`
  show ?case
  proof(cases "as' = []")
    case True
    with `n -as' @ [a']\<rightarrow>* n'` have "sourcenode a' = n \<and> targetnode a' = n'"
      by(auto elim:path.cases)
    with True show ?thesis by(simp add:sourcenodes_def targetnodes_def)
  next
    case False
    from `n -as' @ [a']\<rightarrow>* n'` have "n -as'@a'#[]\<rightarrow>* n'" by simp
    with False have "n -as'\<rightarrow>* sourcenode a'"
      and "targetnode a' -[]\<rightarrow>* n'"
      by(fastsimp dest:path_split)+
    from `targetnode a' -[]\<rightarrow>* n'` have "targetnode a' = n'" by simp
    from IH[OF `n -as'\<rightarrow>* sourcenode a'` False]
    have "targetnodes as' = tl (sourcenodes as') @ [sourcenode a']" .
    with `targetnode a' = n'` False 
    show ?thesis by(simp add:sourcenodes_def targetnodes_def)
  qed
qed


lemma Entry_sourcenode_hd:
  "\<lbrakk>n -as\<rightarrow>* n';(_Entry_) \<in> set (sourcenodes as)\<rbrakk>
  \<Longrightarrow> n = (_Entry_) \<and> (_Entry_) \<notin> set (sourcenodes (tl as))"
proof(induct rule:path.induct)
  case (empty_path n)
  from `(_Entry_) \<in> set (sourcenodes [])` have False by(simp add:sourcenodes_def)
  thus ?case by simp
next
  case (Cons_path n'' as n' a n)
  note IH = `(_Entry_) \<in> set (sourcenodes as) \<Longrightarrow>
            n'' = (_Entry_) \<and> (_Entry_) \<notin> set (sourcenodes (tl as))`
  from `(_Entry_) \<in> set (sourcenodes (a#as))`
  have or:"(_Entry_) = sourcenode a \<or> (_Entry_) \<in> set (sourcenodes as)"
    by(simp add:sourcenodes_def)
  have "(_Entry_) \<notin> set (sourcenodes(tl(a#as)))"
  proof(rule ccontr)
    assume "\<not> (_Entry_) \<notin> set (sourcenodes (tl (a#as)))"
    hence "(_Entry_) \<in> set (sourcenodes as)" by simp
    from IH[OF this] have "n'' = (_Entry_)" by simp
    with `targetnode a = n''` `valid_edge a` show False by -(erule Entry_target,simp)
  qed
  hence "(_Entry_) \<notin> set (sourcenodes(tl(a#as)))" by fastsimp
  with or `sourcenode a = n` show ?case by fastsimp
qed

end

end
