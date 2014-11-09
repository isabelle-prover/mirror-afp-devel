section {* Observable Sets of Nodes *}

theory Observable imports "../Basic/CFG" begin

context CFG begin

inductive_set obs :: "'node \<Rightarrow> 'node set \<Rightarrow> 'node set" 
for n::"'node" and S::"'node set"
where obs_elem: 
  "\<lbrakk>n -as\<rightarrow>* n'; \<forall>nx \<in> set(sourcenodes as). nx \<notin> S; n' \<in> S\<rbrakk> \<Longrightarrow> n' \<in> obs n S"


lemma obsE:
  assumes "n' \<in> obs n S"
  obtains as where "n -as\<rightarrow>* n'" and "\<forall>nx \<in> set(sourcenodes as). nx \<notin> S"
  and "n' \<in> S"
proof(atomize_elim)
  from `n' \<in> obs n S` 
  have "\<exists>as. n -as\<rightarrow>* n' \<and> (\<forall>nx \<in> set(sourcenodes as). nx \<notin> S) \<and> n' \<in> S"
    by(auto elim:obs.cases)
  thus "\<exists>as. n -as\<rightarrow>* n' \<and> (\<forall>nx\<in>set (sourcenodes as). nx \<notin> S) \<and> n' \<in> S" by blast
qed


lemma n_in_obs:
  assumes "valid_node n" and "n \<in> S" shows "obs n S = {n}"
proof -
  from `valid_node n` have "n -[]\<rightarrow>* n" by(rule empty_path)
  with `n \<in> S` have "n \<in> obs n S" by(fastforce elim:obs_elem simp:sourcenodes_def)
  { fix n' assume "n' \<in> obs n S"
    have "n' = n"
    proof(rule ccontr)
      assume "n' \<noteq> n"
      from `n' \<in> obs n S` obtain as where "n -as\<rightarrow>* n'"
        and "\<forall>nx \<in> set(sourcenodes as). nx \<notin> S"
        and "n' \<in> S" by(erule obsE)
      from `n -as\<rightarrow>* n'` `\<forall>nx \<in> set(sourcenodes as). nx \<notin> S` `n' \<noteq> n` `n \<in> S`
      show False
      proof(induct rule:path.induct)
        case (Cons_path n'' as n' a n)
        from `\<forall>nx\<in>set (sourcenodes (a#as)). nx \<notin> S` `sourcenode a = n`
        have "n \<notin> S" by(simp add:sourcenodes_def)
        with `n \<in> S` show False by simp
      qed simp
    qed }
  with `n \<in> obs n S` show ?thesis by fastforce
qed


lemma in_obs_valid:
  assumes "n' \<in> obs n S" shows "valid_node n" and "valid_node n'"
  using `n' \<in> obs n S`
  by(auto elim:obsE intro:path_valid_node)


lemma edge_obs_subset:
  assumes"valid_edge a" and "sourcenode a \<notin> S"
  shows "obs (targetnode a) S \<subseteq> obs (sourcenode a) S"
proof
  fix n assume "n \<in> obs (targetnode a) S"
  then obtain as where "targetnode a -as\<rightarrow>* n" 
    and all:"\<forall>nx \<in> set(sourcenodes as). nx \<notin> S" and "n \<in> S" by(erule obsE)
  from `valid_edge a` `targetnode a -as\<rightarrow>* n`
  have "sourcenode a -a#as\<rightarrow>* n" by(fastforce intro:Cons_path)
  moreover
  from all `sourcenode a \<notin> S` have "\<forall>nx \<in> set(sourcenodes (a#as)). nx \<notin> S"
    by(simp add:sourcenodes_def)
  ultimately show "n \<in> obs (sourcenode a) S" using `n \<in> S`
    by(rule obs_elem)
qed


lemma path_obs_subset:
  "\<lbrakk>n -as\<rightarrow>* n'; \<forall>n' \<in> set(sourcenodes as). n' \<notin> S\<rbrakk>
  \<Longrightarrow> obs n' S \<subseteq> obs n S"
proof(induct rule:path.induct)
  case (Cons_path n'' as n' a n)
  note IH = `\<forall>n'\<in>set (sourcenodes as). n' \<notin> S \<Longrightarrow> obs n' S \<subseteq> obs n'' S`
  from `\<forall>n'\<in>set (sourcenodes (a#as)). n' \<notin> S` 
  have all:"\<forall>n'\<in>set (sourcenodes as). n' \<notin> S" and "sourcenode a \<notin> S"
    by(simp_all add:sourcenodes_def)
  from IH[OF all] have "obs n' S \<subseteq> obs n'' S" .
  from `valid_edge a` `targetnode a = n''` `sourcenode a = n` `sourcenode a \<notin> S`
  have "obs n'' S \<subseteq> obs n S" by(fastforce dest:edge_obs_subset)
  with `obs n' S \<subseteq> obs n'' S` show ?case by fastforce
qed simp


lemma path_ex_obs:
  assumes "n -as\<rightarrow>* n'" and "n' \<in> S"
  obtains m where "m \<in> obs n S"
proof(atomize_elim)
  show "\<exists>m. m \<in> obs n S"
  proof(cases "\<forall>nx \<in> set(sourcenodes as). nx \<notin> S")
    case True
    with `n -as\<rightarrow>* n'` `n' \<in> S` have "n' \<in> obs n S" by -(rule obs_elem)
    thus ?thesis by fastforce
  next
    case False
    hence "\<exists>nx \<in> set(sourcenodes as). nx \<in> S" by fastforce
    then obtain nx ns ns' where "sourcenodes as = ns@nx#ns'"
      and "nx \<in> S" and "\<forall>n' \<in> set ns. n' \<notin> S"
      by(fastforce elim!:split_list_first_propE)
    from `sourcenodes as = ns@nx#ns'` obtain as' a as'' 
      where "ns = sourcenodes as'"
      and "as = as'@a#as''" and "sourcenode a = nx"
      by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
    with `n -as\<rightarrow>* n'` have "n -as'\<rightarrow>* nx" by(fastforce dest:path_split)
    with `nx \<in> S` `\<forall>n' \<in> set ns. n' \<notin> S` `ns = sourcenodes as'` have "nx \<in> obs n S"
      by(fastforce intro:obs_elem)
    thus ?thesis by fastforce
  qed
qed

end

end

