section {* CFG *}

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
  by(fastforce simp:valid_node_def)

lemma [simp]: "valid_edge a \<Longrightarrow> valid_node (targetnode a)"
  by(fastforce simp:valid_node_def)


subsection {* CFG paths and lemmas *}

inductive path :: "'node \<Rightarrow> 'edge list \<Rightarrow> 'node \<Rightarrow> bool"
  ("_ -_\<rightarrow>* _" [51,0,0] 80)
where 
  empty_path:"valid_node n \<Longrightarrow> n -[]\<rightarrow>* n"

  | Cons_path:
  "\<lbrakk>n'' -as\<rightarrow>* n'; valid_edge a; sourcenode a = n; targetnode a = n''\<rbrakk>
    \<Longrightarrow> n -a#as\<rightarrow>* n'"


lemma path_valid_node:
  assumes "n -as\<rightarrow>* n'" shows "valid_node n" and "valid_node n'"
  using `n -as\<rightarrow>* n'`
  by(induct rule:path.induct,auto)

lemma empty_path_nodes [dest]:"n -[]\<rightarrow>* n' \<Longrightarrow> n = n'"
  by(fastforce elim:path.cases)

lemma path_valid_edges:"n -as\<rightarrow>* n' \<Longrightarrow> \<forall>a \<in> set as. valid_edge a"
by(induct rule:path.induct) auto


lemma path_edge:"valid_edge a \<Longrightarrow> sourcenode a -[a]\<rightarrow>* targetnode a"
  by(fastforce intro:Cons_path empty_path)


lemma path_Entry_target [dest]:
  assumes "n -as\<rightarrow>* (_Entry_)"
  shows "n = (_Entry_)" and "as = []"
using `n -as\<rightarrow>* (_Entry_)`
proof(induct n as n'\<equiv>"(_Entry_)" rule:path.induct)
  case (Cons_path n'' as a n)
  from `targetnode a = n''` `valid_edge a` `n'' = (_Entry_)` have False
    by -(rule Entry_target,simp_all)
  { case 1
    with `False` show ?case ..
  next
    case 2
    with `False` show ?case ..
  }
qed simp_all



lemma path_Append:"\<lbrakk>n -as\<rightarrow>* n''; n'' -as'\<rightarrow>* n'\<rbrakk> 
  \<Longrightarrow> n -as@as'\<rightarrow>* n'"
by(induct rule:path.induct,auto intro:Cons_path)


lemma path_split:
  assumes "n -as@a#as'\<rightarrow>* n'"
  shows "n -as\<rightarrow>* sourcenode a" and "valid_edge a" and "targetnode a -as'\<rightarrow>* n'"
  using `n -as@a#as'\<rightarrow>* n'`
proof(induct as arbitrary:n)
  case Nil case 1
  thus ?case by(fastforce elim:path.cases intro:empty_path)
next
  case Nil case 2
  thus ?case by(fastforce elim:path.cases intro:path_edge)
next
  case Nil case 3
  thus ?case by(fastforce elim:path.cases)
next
  case (Cons ax asx) 
  note IH1 = `\<And>n. n -asx@a#as'\<rightarrow>* n' \<Longrightarrow> n -asx\<rightarrow>* sourcenode a`
  note IH2 = `\<And>n. n -asx@a#as'\<rightarrow>* n' \<Longrightarrow> valid_edge a`
  note IH3 = `\<And>n. n -asx@a#as'\<rightarrow>* n' \<Longrightarrow> targetnode a -as'\<rightarrow>* n'`
  { case 1 
    hence "sourcenode ax = n" and "targetnode ax -asx@a#as'\<rightarrow>* n'" and "valid_edge ax"
      by(auto elim:path.cases)
    from IH1[OF ` targetnode ax -asx@a#as'\<rightarrow>* n'`] 
    have "targetnode ax -asx\<rightarrow>* sourcenode a" .
    with `sourcenode ax = n` `valid_edge ax` show ?case by(fastforce intro:Cons_path)
  next
    case 2 hence "targetnode ax -asx@a#as'\<rightarrow>* n'" by(auto elim:path.cases)
    from IH2[OF this] show ?case .
  next
    case 3 hence "targetnode ax -asx@a#as'\<rightarrow>* n'" by(auto elim:path.cases)
    from IH3[OF this] show ?case .
  }
qed


lemma path_split_Cons:
  assumes "n -as\<rightarrow>* n'" and "as \<noteq> []"
  obtains a' as' where "as = a'#as'" and "n = sourcenode a'"
  and "valid_edge a'" and "targetnode a' -as'\<rightarrow>* n'"
proof -
  from `as \<noteq> []` obtain a' as' where "as = a'#as'" by(cases as) auto
  with `n -as\<rightarrow>* n'` have "n -[]@a'#as'\<rightarrow>* n'" by simp
  hence "n -[]\<rightarrow>* sourcenode a'" and "valid_edge a'" and "targetnode a' -as'\<rightarrow>* n'"
    by(rule path_split)+
  from `n -[]\<rightarrow>* sourcenode a'` have "n = sourcenode a'" by fast
  with `as = a'#as'` `valid_edge a'` `targetnode a' -as'\<rightarrow>* n'` that show ?thesis 
    by fastforce
qed


lemma path_split_snoc:
  assumes "n -as\<rightarrow>* n'" and "as \<noteq> []"
  obtains a' as' where "as = as'@[a']" and "n -as'\<rightarrow>* sourcenode a'"
  and "valid_edge a'" and "n' = targetnode a'"
proof -
  from `as \<noteq> []` obtain a' as' where "as = as'@[a']" by(cases as rule:rev_cases) auto
  with `n -as\<rightarrow>* n'` have "n -as'@a'#[]\<rightarrow>* n'" by simp
  hence "n -as'\<rightarrow>* sourcenode a'" and "valid_edge a'" and "targetnode a' -[]\<rightarrow>* n'"
    by(rule path_split)+
  from `targetnode a' -[]\<rightarrow>* n'` have "n' = targetnode a'" by fast
  with `as = as'@[a']` `valid_edge a'` `n -as'\<rightarrow>* sourcenode a'` that show ?thesis 
    by fastforce
qed


lemma path_split_second:
  assumes "n -as@a#as'\<rightarrow>* n'" shows "sourcenode a -a#as'\<rightarrow>* n'"
proof -
  from `n -as@a#as'\<rightarrow>* n'` have "valid_edge a" and "targetnode a -as'\<rightarrow>* n'"
    by(auto intro:path_split)
  thus ?thesis by(fastforce intro:Cons_path)
qed


lemma path_Entry_Cons:
  assumes "(_Entry_) -as\<rightarrow>* n'" and "n' \<noteq> (_Entry_)"
  obtains n a where "sourcenode a = (_Entry_)" and "targetnode a = n"
  and "n -tl as\<rightarrow>* n'" and "valid_edge a" and "a = hd as"
proof -
  from `(_Entry_) -as\<rightarrow>* n'` `n' \<noteq> (_Entry_)` have "as \<noteq> []"
    by(cases as,auto elim:path.cases)
  with `(_Entry_) -as\<rightarrow>* n'` obtain a' as' where "as = a'#as'" 
    and "(_Entry_) = sourcenode a'" and "valid_edge a'" and "targetnode a' -as'\<rightarrow>* n'"
    by(erule path_split_Cons)
  with that show ?thesis by fastforce
qed


lemma path_det:
  "\<lbrakk>n -as\<rightarrow>* n'; n -as\<rightarrow>* n''\<rbrakk> \<Longrightarrow> n' = n''"
proof(induct as arbitrary:n)
  case Nil thus ?case by(auto elim:path.cases)
next
  case (Cons a' as')
  note IH = `\<And>n. \<lbrakk>n -as'\<rightarrow>* n'; n -as'\<rightarrow>* n''\<rbrakk> \<Longrightarrow> n' = n''`
  from `n -a'#as'\<rightarrow>* n'` have "targetnode a' -as'\<rightarrow>* n'" 
    by(fastforce elim:path_split_Cons)
  from `n -a'#as'\<rightarrow>* n''` have "targetnode a' -as'\<rightarrow>* n''" 
    by(fastforce elim:path_split_Cons)
  from IH[OF `targetnode a' -as'\<rightarrow>* n'` this] show ?thesis .
qed


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
  "\<lbrakk>n -as\<rightarrow>* n'; as \<noteq> []\<rbrakk> \<Longrightarrow> hd (sourcenodes as) = n"
by(fastforce elim:path_split_Cons simp:sourcenodes_def)



lemma path_targetnode:
  "\<lbrakk>n -as\<rightarrow>* n'; as \<noteq> []\<rbrakk> \<Longrightarrow> last (targetnodes as) = n'"
by(fastforce elim:path_split_snoc simp:targetnodes_def)



lemma sourcenodes_is_n_Cons_butlast_targetnodes:
  "\<lbrakk>n -as\<rightarrow>* n'; as \<noteq> []\<rbrakk> \<Longrightarrow> 
  sourcenodes as = n#(butlast (targetnodes as))"
proof(induct as arbitrary:n)
  case Nil thus ?case by simp
next
  case (Cons a' as')
  note IH = `\<And>n. \<lbrakk>n -as'\<rightarrow>* n'; as' \<noteq> []\<rbrakk>
            \<Longrightarrow> sourcenodes as' = n#(butlast (targetnodes as'))`
  from `n -a'#as'\<rightarrow>* n'` have "n = sourcenode a'" and "targetnode a' -as'\<rightarrow>* n'"
    by(auto elim:path_split_Cons)
  show ?case
  proof(cases "as' = []")
    case True
    with `targetnode a' -as'\<rightarrow>* n'` have "targetnode a' = n'" by fast
    with True `n = sourcenode a'` show ?thesis
      by(simp add:sourcenodes_def targetnodes_def)
  next
    case False
    from IH[OF `targetnode a' -as'\<rightarrow>* n'` this] 
    have "sourcenodes as' = targetnode a' # butlast (targetnodes as')" .
    with `n = sourcenode a'` False show ?thesis
      by(simp add:sourcenodes_def targetnodes_def)
  qed
qed



lemma targetnodes_is_tl_sourcenodes_App_n':
  "\<lbrakk>n -as\<rightarrow>* n'; as \<noteq> []\<rbrakk> \<Longrightarrow> 
    targetnodes as = (tl (sourcenodes as))@[n']"
proof(induct as arbitrary:n' rule:rev_induct)
  case Nil thus ?case by simp
next
  case (snoc a' as')
  note IH = `\<And>n'. \<lbrakk>n -as'\<rightarrow>* n'; as' \<noteq> []\<rbrakk>
    \<Longrightarrow> targetnodes as' = tl (sourcenodes as') @ [n']`
  from `n -as'@[a']\<rightarrow>* n'` have "n -as'\<rightarrow>* sourcenode a'" and "n' = targetnode a'"
    by(auto elim:path_split_snoc)
  show ?case
  proof(cases "as' = []")
    case True
    with `n -as'\<rightarrow>* sourcenode a'` have "n = sourcenode a'" by fast
    with True `n' = targetnode a'` show ?thesis
      by(simp add:sourcenodes_def targetnodes_def)
  next
    case False
    from IH[OF `n -as'\<rightarrow>* sourcenode a'` this]
    have "targetnodes as' = tl (sourcenodes as')@[sourcenode a']" .
    with `n' = targetnode a'` False show ?thesis
      by(simp add:sourcenodes_def targetnodes_def)
  qed
qed

lemma Entry_sourcenode_hd:
  assumes "n -as\<rightarrow>* n'" and "(_Entry_) \<in> set (sourcenodes as)"
  shows "n = (_Entry_)" and "(_Entry_) \<notin> set (sourcenodes (tl as))"
  using `n -as\<rightarrow>* n'` `(_Entry_) \<in> set (sourcenodes as)`
proof(induct rule:path.induct)
  case (empty_path n) case 1
  thus ?case by(simp add:sourcenodes_def)
next
  case (empty_path n) case 2
  thus ?case by(simp add:sourcenodes_def)
next
  case (Cons_path n'' as n' a n)
  note IH1 = `(_Entry_) \<in> set(sourcenodes as) \<Longrightarrow> n'' = (_Entry_)`
  note IH2 = `(_Entry_) \<in> set(sourcenodes as) \<Longrightarrow> (_Entry_) \<notin> set(sourcenodes(tl as))`
  have "(_Entry_) \<notin> set (sourcenodes(tl(a#as)))"
  proof
    assume "(_Entry_) \<in> set (sourcenodes (tl (a#as)))"
    hence "(_Entry_) \<in> set (sourcenodes as)" by simp
    from IH1[OF this] have "n'' = (_Entry_)" by simp
    with `targetnode a = n''` `valid_edge a` show False by -(erule Entry_target,simp)
  qed
  hence "(_Entry_) \<notin> set (sourcenodes(tl(a#as)))" by fastforce
  { case 1
    with `(_Entry_) \<notin> set (sourcenodes(tl(a#as)))` `sourcenode a = n`
    show ?case by(simp add:sourcenodes_def)
  next
    case 2
    with `(_Entry_) \<notin> set (sourcenodes(tl(a#as)))` `sourcenode a = n`
    show ?case by(simp add:sourcenodes_def)
  }
qed

end

end
