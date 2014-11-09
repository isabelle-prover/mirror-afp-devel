section {* Instantiate framework with control dependences *}

theory CDepInstantiations imports 
  Slice 
  PDG 
  WeakOrderDependence 
begin

subsection{* Standard control dependence *}

context StandardControlDependencePDG begin

lemma Exit_in_obs_slice_node:"(_Exit_) \<in> obs n' (PDG_BS S) \<Longrightarrow> (_Exit_) \<in> S"
  by(auto elim:obsE PDG_path_CFG_path simp:PDG_BS_def split:split_if_asm)


abbreviation PDG_path' :: "'node \<Rightarrow> 'node \<Rightarrow> bool" ("_ \<longrightarrow>\<^sub>d* _" [51,0] 80)
  where "n \<longrightarrow>\<^sub>d* n' \<equiv> PDG.PDG_path sourcenode targetnode valid_edge Def Use
  standard_control_dependence n n'"

lemma cd_closed:
  "\<lbrakk>n' \<in> PDG_BS S; n controls\<^sub>s n'\<rbrakk> \<Longrightarrow> n \<in> PDG_BS S"
  by(simp add:PDG_BS_def)(blast dest:PDG_cdep_edge PDG_path_Append PDG_path_cdep)


lemma obs_postdominate:
  assumes "n \<in> obs n' (PDG_BS S)" and "n \<noteq> (_Exit_)" shows "n postdominates n'"
proof(rule ccontr)
  assume "\<not> n postdominates n'"
  from `n \<in> obs n' (PDG_BS S)` have "valid_node n" by(fastforce dest:in_obs_valid)
  with `n \<in> obs n' (PDG_BS S)` `n \<noteq> (_Exit_)` have "n postdominates n"
    by(fastforce intro:postdominate_refl)
  from `n \<in> obs n' (PDG_BS S)` obtain as where "n' -as\<rightarrow>* n"
    and "\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)"
    and "n \<in> (PDG_BS S)" by(erule obsE)
  from `n postdominates n` `\<not> n postdominates n'` `n' -as\<rightarrow>* n`
  obtain as' a as'' where [simp]:"as = as'@a#as''" and "valid_edge a"
    and "\<not> n postdominates (sourcenode a)" and "n postdominates (targetnode a)"
    by -(erule postdominate_path_branch)
  from `\<not> n postdominates (sourcenode a)` `valid_edge a` `valid_node n`
  obtain asx  where "sourcenode a -asx\<rightarrow>* (_Exit_)"
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
  hence "valid_edge ax" and [simp]:"sourcenode a = sourcenode ax"
    and "targetnode ax -asx'\<rightarrow>* (_Exit_)"
    by(fastforce dest:path_split)+
  with `n \<notin> set(sourcenodes asx)` have "\<not> n postdominates targetnode ax"
    by(fastforce simp:postdominate_def sourcenodes_def)
  from `n \<in> obs n' (PDG_BS S)` `\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)`
  have "n \<notin> set (sourcenodes (a#as''))"
    by(fastforce elim:obs.cases simp:sourcenodes_def)
  from `n' -as\<rightarrow>* n` have "sourcenode a -a#as''\<rightarrow>* n"
    by(fastforce dest:path_split_second)
  with `n postdominates (targetnode a)` `\<not> n postdominates targetnode ax`
    `valid_edge ax` `n \<notin> set (sourcenodes (a#as''))`
  have "sourcenode a controls\<^sub>s n" by(fastforce simp:standard_control_dependence_def)
  with `n \<in> obs n' (PDG_BS S)` have "sourcenode a \<in> (PDG_BS S)"
    by(fastforce intro:cd_closed PDG_cdep_edge elim:obs.cases)
  with `\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)` 
  show False by(simp add:sourcenodes_def)
qed


lemma obs_singleton:"(\<exists>m. obs n (PDG_BS S) = {m}) \<or> obs n (PDG_BS S) = {}"
proof(rule ccontr)
  assume "\<not> ((\<exists>m. obs n (PDG_BS S) = {m}) \<or> obs n (PDG_BS S) = {})"
  hence "\<exists>nx nx'. nx \<in> obs n (PDG_BS S) \<and> nx' \<in> obs n (PDG_BS S) \<and>
    nx \<noteq> nx'" by auto
  then obtain nx nx' where "nx \<in> obs n (PDG_BS S)" and "nx' \<in> obs n (PDG_BS S)"
    and "nx \<noteq> nx'" by auto
  from `nx \<in> obs n (PDG_BS S)` obtain as where "n -as\<rightarrow>* nx" 
    and "\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)" and "nx \<in> (PDG_BS S)" 
    by(erule obsE)
  from `n -as\<rightarrow>* nx` have "valid_node nx" by(fastforce dest:path_valid_node)
  with `nx \<in> (PDG_BS S)` have "obs nx (PDG_BS S) = {nx}" by -(rule n_in_obs)
  with `n -as\<rightarrow>* nx` `nx \<in> obs n (PDG_BS S)` `nx' \<in> obs n (PDG_BS S)` `nx \<noteq> nx'`
  have "as \<noteq> []" by(fastforce elim:path.cases)
  with `n -as\<rightarrow>* nx` `nx \<in> obs n (PDG_BS S)` `nx' \<in> obs n (PDG_BS S)` 
    `nx \<noteq> nx'` `obs nx (PDG_BS S) = {nx}` `\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)`
  have "\<exists>a as' as''. n -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* nx \<and>
                     valid_edge a \<and> as = as'@a#as'' \<and> 
                     obs (targetnode a) (PDG_BS S) = {nx} \<and> 
                    (\<not> (\<exists>m. obs (sourcenode a) (PDG_BS S) = {m} \<or> 
                       obs (sourcenode a) (PDG_BS S) = {}))"
  proof(induct arbitrary:nx' rule:path.induct)
    case (Cons_path n'' as n' a n)
    note [simp] = `sourcenode a = n`[THEN sym] `targetnode a = n''`[THEN sym]
    note more_than_one = `n' \<in> obs n (PDG_BS S)` `nx' \<in> obs n (PDG_BS S)` `n' \<noteq> nx'`
    note IH = `\<And>nx'. \<lbrakk>n' \<in> obs n'' (PDG_BS S); nx' \<in> obs n'' (PDG_BS S); n' \<noteq> nx'; 
      obs n' (PDG_BS S) = {n'}; \<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS S); as \<noteq> []\<rbrakk>
      \<Longrightarrow> \<exists>a as' as''. n'' -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* n' \<and>
      valid_edge a \<and> as = as'@a#as'' \<and> obs (targetnode a) (PDG_BS S) = {n'} \<and>
      (\<not> (\<exists>m. obs (sourcenode a) (PDG_BS S) = {m} \<or> 
      obs (sourcenode a) (PDG_BS S) = {}))`
    from `\<forall>n'\<in>set (sourcenodes (a#as)). n' \<notin> (PDG_BS S)`
    have "\<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS S)" and "sourcenode a \<notin> (PDG_BS S)"
      by(simp_all add:sourcenodes_def)
    show ?case
    proof(cases "as = []")
      case True
      with `n'' -as\<rightarrow>* n'` have [simp]:"n' = n''" by(fastforce elim:path.cases)
      from more_than_one
      have "\<not> (\<exists>m. obs (sourcenode a) (PDG_BS S) = {m} \<or> 
               obs (sourcenode a) (PDG_BS S) = {})"
        by auto
      with `obs n' (PDG_BS S) = {n'}` True `valid_edge a` show ?thesis
        apply(rule_tac x="a" in exI)
        apply(rule_tac x="[]" in exI)
        apply(rule_tac x="[]" in exI)
        by(auto intro!:empty_path)
    next
      case False
      hence "as \<noteq> []" .
      from `n'' -as\<rightarrow>* n'` `\<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS S)` 
      have "obs n' (PDG_BS S) \<subseteq> obs n'' (PDG_BS S)" by(rule path_obs_subset)
      show ?thesis
      proof(cases "obs n' (PDG_BS S) = obs n'' (PDG_BS S)")
        case True
        with `n'' -as\<rightarrow>* n'` `valid_edge a` `obs n' (PDG_BS S) = {n'}` more_than_one
        show ?thesis
          apply(rule_tac x="a" in exI)
          apply(rule_tac x="[]" in exI)
          apply(rule_tac x="as" in exI)
          by(fastforce intro:empty_path)
      next
        case False
        with `obs n' (PDG_BS S) \<subseteq> obs n'' (PDG_BS S)`
        have "obs n' (PDG_BS S) \<subset> obs n'' (PDG_BS S)" by simp
        with `obs n' (PDG_BS S) = {n'}` obtain ni where "n' \<in> obs n'' (PDG_BS S)"
          and "ni \<in> obs n'' (PDG_BS S)" and "n' \<noteq> ni" by auto
        from IH[OF this `obs n' (PDG_BS S) = {n'}` 
          `\<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS S)` `as \<noteq> []`] obtain a' as' as''
          where "n'' -as'\<rightarrow>* sourcenode a'" and "targetnode a' -as''\<rightarrow>* n'"
          and "valid_edge a'" and [simp]:"as = as'@a'#as''" 
          and "obs (targetnode a') (PDG_BS S) = {n'}"
          and more_than_one':"\<not> (\<exists>m. obs (sourcenode a') (PDG_BS S) = {m} \<or> 
          obs (sourcenode a') (PDG_BS S) = {})"
          by blast
        from `n'' -as'\<rightarrow>* sourcenode a'` `valid_edge a`
        have "n -a#as'\<rightarrow>* sourcenode a'" by(fastforce intro:path.Cons_path)
        with `targetnode a' -as''\<rightarrow>* n'` `obs (targetnode a') (PDG_BS S) = {n'}`
          more_than_one' `valid_edge a'` show ?thesis
          apply(rule_tac x="a'" in exI)
          apply(rule_tac x="a#as'" in exI)
          apply(rule_tac x="as''" in exI)
          by fastforce
      qed
    qed
  qed simp
  then obtain a as' as'' where "valid_edge a"
    and "obs (targetnode a) (PDG_BS S) = {nx}"
    and more_than_one:"\<not> (\<exists>m. obs (sourcenode a) (PDG_BS S) = {m} \<or> 
                         obs (sourcenode a) (PDG_BS S) = {})"
    by blast
  have "sourcenode a \<notin> (PDG_BS S)"
  proof(rule ccontr)
    assume "\<not> sourcenode a \<notin> PDG_BS S"
    hence "sourcenode a \<in> PDG_BS S" by simp
    with `valid_edge a` have "obs (sourcenode a) (PDG_BS S) = {sourcenode a}"
      by(fastforce intro!:n_in_obs)
    with more_than_one show False by simp
  qed
  with `valid_edge a` 
  have "obs (targetnode a) (PDG_BS S) \<subseteq> obs (sourcenode a) (PDG_BS S)"
    by(rule edge_obs_subset)
  with `obs (targetnode a) (PDG_BS S) = {nx}` 
  have "nx \<in> obs (sourcenode a) (PDG_BS S)" by simp
  with more_than_one obtain m  where "m \<in> obs (sourcenode a) (PDG_BS S)"
    and "nx \<noteq> m" by auto
  from `m \<in> obs (sourcenode a) (PDG_BS S)` 
  have "valid_node m" by(fastforce dest:in_obs_valid)
  from `obs (targetnode a) (PDG_BS S) = {nx}` have "valid_node nx" 
    by(fastforce dest:in_obs_valid)
  show False
  proof(cases "m postdominates (sourcenode a)")
    case True
    with `nx \<in> obs (sourcenode a) (PDG_BS S)` `m \<in> obs (sourcenode a) (PDG_BS S)`
    have "m postdominates nx"
      by(fastforce intro:postdominate_path_targetnode elim:obs.cases)
    with `nx \<noteq> m` have "\<not> nx postdominates m" by(fastforce dest:postdominate_antisym)
    have "(_Exit_) -[]\<rightarrow>* (_Exit_)" by(fastforce intro:empty_path)
    with `m postdominates nx` have "nx \<noteq> (_Exit_)"
      by(fastforce simp:postdominate_def sourcenodes_def)
    have "\<not> nx postdominates (sourcenode a)"
    proof(rule ccontr)
      assume "\<not> \<not> nx postdominates sourcenode a"
      hence "nx postdominates sourcenode a" by simp
      from `m \<in> obs (sourcenode a) (PDG_BS S)` `nx \<in> obs (sourcenode a) (PDG_BS S)`
      obtain asx' where "sourcenode a -asx'\<rightarrow>* m" and "nx \<notin> set(sourcenodes asx')"
        by(fastforce elim:obs.cases)
      with `nx postdominates sourcenode a` have "nx postdominates m"
        by(rule postdominate_path_targetnode)
      with `\<not> nx postdominates m` show False by simp
    qed
    with `nx \<in> obs (sourcenode a) (PDG_BS S)` `valid_node nx` `nx \<noteq> (_Exit_)` 
    show False by(fastforce dest:obs_postdominate)
  next
    case False
    show False
    proof(cases "m = Exit")
      case True
      from `m \<in> obs (sourcenode a) (PDG_BS S)` `nx \<in> obs (sourcenode a) (PDG_BS S)`
      obtain xs where "sourcenode a -xs\<rightarrow>* m" and "nx \<notin> set(sourcenodes xs)"
        by(fastforce elim:obsE)
      obtain x' xs' where [simp]:"xs = x'#xs'"
      proof(cases xs)
        case Nil
        with `sourcenode a -xs\<rightarrow>* m` have [simp]:"sourcenode a = m" by fastforce
        with `m \<in> obs (sourcenode a) (PDG_BS S)` 
        have "m \<in> (PDG_BS S)" by(metis obsE)
        with `valid_node m` have "obs m (PDG_BS S) = {m}"
          by(rule n_in_obs)
        with `nx \<in> obs (sourcenode a) (PDG_BS S)` `nx \<noteq> m` have False
          by fastforce
        thus ?thesis by simp
      qed blast
      from `sourcenode a -xs\<rightarrow>* m` have "sourcenode a = sourcenode x'" 
        and "valid_edge x'" and "targetnode x' -xs'\<rightarrow>* m"
        by(auto elim:path_split_Cons)
      from `targetnode x' -xs'\<rightarrow>* m` `nx \<notin> set(sourcenodes xs)` `valid_edge x'` 
        `valid_node m` True
      have "\<not> nx postdominates (targetnode x')" 
        by(fastforce simp:postdominate_def sourcenodes_def)
      from `nx \<noteq> m` True have "nx \<noteq> (_Exit_)" by simp
      with `obs (targetnode a) (PDG_BS S) = {nx}`
      have "nx postdominates (targetnode a)"
        by(fastforce intro:obs_postdominate)
      from `obs (targetnode a) (PDG_BS S) = {nx}`
      obtain ys where "targetnode a -ys\<rightarrow>* nx" 
        and "\<forall>nx' \<in> set(sourcenodes ys). nx' \<notin> (PDG_BS S)"
        and "nx \<in> (PDG_BS S)" by(fastforce elim:obsE)
      hence "nx \<notin> set(sourcenodes ys)"by fastforce
      have "sourcenode a \<noteq> nx"
      proof
        assume "sourcenode a = nx"
        from `nx \<in> obs (sourcenode a) (PDG_BS S)`
        have "nx \<in> (PDG_BS S)" by -(erule obsE)
        with `valid_node nx` have "obs nx (PDG_BS S) = {nx}" by -(erule n_in_obs)
        with `sourcenode a = nx` `m \<in> obs (sourcenode a) (PDG_BS S)` 
          `nx \<noteq> m` show False by fastforce
      qed
      with `nx \<notin> set(sourcenodes ys)` have "nx \<notin> set(sourcenodes (a#ys))"
        by(fastforce simp:sourcenodes_def)
      from `valid_edge a` `targetnode a -ys\<rightarrow>* nx`
      have "sourcenode a -a#ys\<rightarrow>* nx" by(fastforce intro:Cons_path)
      from `sourcenode a -a#ys\<rightarrow>* nx` `nx \<notin> set(sourcenodes (a#ys))`
        `nx postdominates (targetnode a)` `valid_edge x'`
        `\<not> nx postdominates (targetnode x')` `sourcenode a = sourcenode x'`
      have "(sourcenode a) controls\<^sub>s nx"
        by(fastforce simp:standard_control_dependence_def)
      with `nx \<in> (PDG_BS S)` have "sourcenode a \<in> (PDG_BS S)"
        by(rule cd_closed)
      with `valid_edge a` have "obs (sourcenode a) (PDG_BS S) = {sourcenode a}"
        by(fastforce intro!:n_in_obs)
      with `m \<in> obs (sourcenode a) (PDG_BS S)`
        `nx \<in> obs (sourcenode a) (PDG_BS S)` `nx \<noteq> m`
      show False by simp
    next
      case False
      with `m \<in> obs (sourcenode a) (PDG_BS S)` `valid_node m`
        `\<not> m postdominates sourcenode a` 
      show False by(fastforce dest:obs_postdominate)
    qed
  qed
qed


lemma PDGBackwardSliceCorrect:
  "BackwardSlice sourcenode targetnode kind valid_edge
        (_Entry_) Def Use state_val PDG_BS"
proof(unfold_locales)
  fix n S assume "n \<in> PDG_BS S"
  thus "valid_node n" by(rule PDG_BS_valid_node)
next
  fix n S assume "valid_node n" and "n \<in> S"
  thus "n \<in> PDG_BS S" by(fastforce intro:PDG_path_Nil simp:PDG_BS_def)
next
  fix n' S n V
  assume "n' \<in> PDG_BS S" and "n influences V in n'"
  thus "n \<in> PDG_BS S"
    by(auto dest:PDG.PDG_path_ddep[OF PDG_scd,OF PDG.PDG_ddep_edge[OF PDG_scd]]
            dest:PDG_path_Append simp:PDG_BS_def split:split_if_asm)
next
  fix n S
  have "(\<exists>m. obs n (PDG_BS S) = {m}) \<or> obs n (PDG_BS S) = {}" 
    by(rule obs_singleton)
  thus "finite (obs n (PDG_BS S))" by fastforce
next
  fix n S
  have "(\<exists>m. obs n (PDG_BS S) = {m}) \<or> obs n (PDG_BS S) = {}" 
    by(rule obs_singleton)
  thus "card (obs n (PDG_BS S)) \<le> 1" by fastforce
qed

end


subsection{* Weak control dependence *}

context WeakControlDependencePDG begin

lemma Exit_in_obs_slice_node:"(_Exit_) \<in> obs n' (PDG_BS S) \<Longrightarrow> (_Exit_) \<in> S"
  by(auto elim:obsE PDG_path_CFG_path simp:PDG_BS_def split:split_if_asm)


lemma cd_closed:
  "\<lbrakk>n' \<in> PDG_BS S; n weakly controls n'\<rbrakk> \<Longrightarrow> n \<in> PDG_BS S"
  by(simp add:PDG_BS_def)(blast dest:PDG_cdep_edge PDG_path_Append PDG_path_cdep)


lemma obs_strong_postdominate:
  assumes "n \<in> obs n' (PDG_BS S)" and "n \<noteq> (_Exit_)" 
  shows "n strongly-postdominates n'"
proof(rule ccontr)
  assume "\<not> n strongly-postdominates n'"
  from `n \<in> obs n' (PDG_BS S)` have "valid_node n" by(fastforce dest:in_obs_valid)
  with `n \<in> obs n' (PDG_BS S)` `n \<noteq> (_Exit_)` have "n strongly-postdominates n"
    by(fastforce intro:strong_postdominate_refl)
  from `n \<in> obs n' (PDG_BS S)` obtain as where "n' -as\<rightarrow>* n"
    and "\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)"
    and "n \<in> (PDG_BS S)" by(erule obsE)
  from `n strongly-postdominates n` `\<not> n strongly-postdominates n'` `n' -as\<rightarrow>* n`
  obtain as' a as'' where [simp]:"as = as'@a#as''" and "valid_edge a"
    and "\<not> n strongly-postdominates (sourcenode a)" and 
    "n strongly-postdominates (targetnode a)"
    by -(erule strong_postdominate_path_branch)
  from `n \<in> obs n' (PDG_BS S)` `\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)` 
  have "n \<notin> set (sourcenodes (a#as''))"
    by(fastforce elim:obs.cases simp:sourcenodes_def)
  from `n' -as\<rightarrow>* n` have "sourcenode a -a#as''\<rightarrow>* n"
    by(fastforce dest:path_split_second)
  from `\<not> n strongly-postdominates (sourcenode a)` `valid_edge a` `valid_node n`
  obtain a' where "sourcenode a' = sourcenode a"
    and "valid_edge a'" and "\<not> n strongly-postdominates (targetnode a')"
    by(fastforce elim:not_strong_postdominate_predecessor_successor)
  with `n strongly-postdominates (targetnode a)` `n \<notin> set (sourcenodes (a#as''))`
    `sourcenode a -a#as''\<rightarrow>* n`
  have "sourcenode a weakly controls n"
    by(fastforce simp:weak_control_dependence_def)
  with `n \<in> obs n' (PDG_BS S)` have "sourcenode a \<in> (PDG_BS S)"
    by(fastforce intro:cd_closed PDG_cdep_edge elim:obs.cases)
  with `\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)`
  show False by(simp add:sourcenodes_def)
qed


lemma obs_singleton:"(\<exists>m. obs n (PDG_BS S) = {m}) \<or> obs n (PDG_BS S) = {}"
proof(rule ccontr)
  assume "\<not> ((\<exists>m. obs n (PDG_BS S) = {m}) \<or> obs n (PDG_BS S) = {})"
  hence "\<exists>nx nx'. nx \<in> obs n (PDG_BS S) \<and> nx' \<in> obs n (PDG_BS S) \<and>
    nx \<noteq> nx'" by auto
  then obtain nx nx' where "nx \<in> obs n (PDG_BS S)" and "nx' \<in> obs n (PDG_BS S)"
    and "nx \<noteq> nx'" by auto
  from `nx \<in> obs n (PDG_BS S)` obtain as where "n -as\<rightarrow>* nx" 
    and "\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)" and "nx \<in> (PDG_BS S)" 
    by(erule obsE)
  from `n -as\<rightarrow>* nx` have "valid_node nx" by(fastforce dest:path_valid_node)
  with `nx \<in> (PDG_BS S)` have "obs nx (PDG_BS S) = {nx}" by -(rule n_in_obs)
  with `n -as\<rightarrow>* nx` `nx \<in> obs n (PDG_BS S)` `nx' \<in> obs n (PDG_BS S)` `nx \<noteq> nx'`
  have "as \<noteq> []" by(fastforce elim:path.cases)
  with `n -as\<rightarrow>* nx` `nx \<in> obs n (PDG_BS S)` `nx' \<in> obs n (PDG_BS S)` 
    `nx \<noteq> nx'` `obs nx (PDG_BS S) = {nx}` `\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)`
  have "\<exists>a as' as''. n -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* nx \<and>
                     valid_edge a \<and> as = as'@a#as'' \<and> 
                     obs (targetnode a) (PDG_BS S) = {nx} \<and> 
                    (\<not> (\<exists>m. obs (sourcenode a) (PDG_BS S) = {m} \<or> 
                       obs (sourcenode a) (PDG_BS S) = {}))"
  proof(induct arbitrary:nx' rule:path.induct)
    case (Cons_path n'' as n' a n)
    note [simp] = `sourcenode a = n`[THEN sym] `targetnode a = n''`[THEN sym]
    note more_than_one = `n' \<in> obs n (PDG_BS S)` `nx' \<in> obs n (PDG_BS S)` `n' \<noteq> nx'`
    note IH = `\<And>nx'. \<lbrakk>n' \<in> obs n'' (PDG_BS S); nx' \<in> obs n'' (PDG_BS S); n' \<noteq> nx'; 
      obs n' (PDG_BS S) = {n'}; \<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS S); as \<noteq> []\<rbrakk>
      \<Longrightarrow> \<exists>a as' as''. n'' -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* n' \<and>
      valid_edge a \<and> as = as'@a#as'' \<and> obs (targetnode a) (PDG_BS S) = {n'} \<and>
      (\<not> (\<exists>m. obs (sourcenode a) (PDG_BS S) = {m} \<or> 
      obs (sourcenode a) (PDG_BS S) = {}))`
    from `\<forall>n'\<in>set (sourcenodes (a#as)). n' \<notin> (PDG_BS S)`
    have "\<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS S)" and "sourcenode a \<notin> (PDG_BS S)"
      by(simp_all add:sourcenodes_def)
    show ?case
    proof(cases "as = []")
      case True
      with `n'' -as\<rightarrow>* n'` have [simp]:"n' = n''" by(fastforce elim:path.cases)
      from more_than_one
      have "\<not> (\<exists>m. obs (sourcenode a) (PDG_BS S) = {m} \<or> 
               obs (sourcenode a) (PDG_BS S) = {})"
        by auto
      with `obs n' (PDG_BS S) = {n'}` True `valid_edge a` show ?thesis
        apply(rule_tac x="a" in exI)
        apply(rule_tac x="[]" in exI)
        apply(rule_tac x="[]" in exI)
        by(auto intro!:empty_path)
    next
      case False
      hence "as \<noteq> []" .
      from `n'' -as\<rightarrow>* n'` `\<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS S)` 
      have "obs n' (PDG_BS S) \<subseteq> obs n'' (PDG_BS S)" by(rule path_obs_subset)
      show ?thesis
      proof(cases "obs n' (PDG_BS S) = obs n'' (PDG_BS S)")
        case True
        with `n'' -as\<rightarrow>* n'` `valid_edge a` `obs n' (PDG_BS S) = {n'}` more_than_one
        show ?thesis
          apply(rule_tac x="a" in exI)
          apply(rule_tac x="[]" in exI)
          apply(rule_tac x="as" in exI)
          by(fastforce intro:empty_path)
      next
        case False
        with `obs n' (PDG_BS S) \<subseteq> obs n'' (PDG_BS S)`
        have "obs n' (PDG_BS S) \<subset> obs n'' (PDG_BS S)" by simp
        with `obs n' (PDG_BS S) = {n'}` obtain ni where "n' \<in> obs n'' (PDG_BS S)"
          and "ni \<in> obs n'' (PDG_BS S)" and "n' \<noteq> ni" by auto
        from IH[OF this `obs n' (PDG_BS S) = {n'}` 
          `\<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS S)` `as \<noteq> []`] obtain a' as' as''
          where "n'' -as'\<rightarrow>* sourcenode a'" and "targetnode a' -as''\<rightarrow>* n'"
          and "valid_edge a'" and [simp]:"as = as'@a'#as''" 
          and "obs (targetnode a') (PDG_BS S) = {n'}"
          and more_than_one':"\<not> (\<exists>m. obs (sourcenode a') (PDG_BS S) = {m} \<or> 
          obs (sourcenode a') (PDG_BS S) = {})"
          by blast
        from `n'' -as'\<rightarrow>* sourcenode a'` `valid_edge a`
        have "n -a#as'\<rightarrow>* sourcenode a'" by(fastforce intro:path.Cons_path)
        with `targetnode a' -as''\<rightarrow>* n'` `obs (targetnode a') (PDG_BS S) = {n'}`
          more_than_one' `valid_edge a'` show ?thesis
          apply(rule_tac x="a'" in exI)
          apply(rule_tac x="a#as'" in exI)
          apply(rule_tac x="as''" in exI)
          by fastforce
      qed
    qed
  qed simp
  then obtain a as' as'' where "valid_edge a"
    and "obs (targetnode a) (PDG_BS S) = {nx}"
    and more_than_one:"\<not> (\<exists>m. obs (sourcenode a) (PDG_BS S) = {m} \<or> 
                         obs (sourcenode a) (PDG_BS S) = {})"
    by blast
  have "sourcenode a \<notin> (PDG_BS S)"
  proof(rule ccontr)
    assume "\<not> sourcenode a \<notin> PDG_BS S"
    hence "sourcenode a \<in> PDG_BS S" by simp
    with `valid_edge a` have "obs (sourcenode a) (PDG_BS S) = {sourcenode a}"
      by(fastforce intro!:n_in_obs)
    with more_than_one show False by simp
  qed
  with `valid_edge a` 
  have "obs (targetnode a) (PDG_BS S) \<subseteq> obs (sourcenode a) (PDG_BS S)"
    by(rule edge_obs_subset)
  with `obs (targetnode a) (PDG_BS S) = {nx}` 
  have "nx \<in> obs (sourcenode a) (PDG_BS S)" by simp
  with more_than_one obtain m  where "m \<in> obs (sourcenode a) (PDG_BS S)"
    and "nx \<noteq> m" by auto
  from `m \<in> obs (sourcenode a) (PDG_BS S)` 
  have "valid_node m" by(fastforce dest:in_obs_valid)
  from `obs (targetnode a) (PDG_BS S) = {nx}` have "valid_node nx" 
    by(fastforce dest:in_obs_valid)
  show False
  proof(cases "m strongly-postdominates (sourcenode a)")
    case True
    with `nx \<in> obs (sourcenode a) (PDG_BS S)` `m \<in> obs (sourcenode a) (PDG_BS S)`
    have "m strongly-postdominates nx"
      by(fastforce intro:strong_postdominate_path_targetnode elim:obs.cases)
    with `nx \<noteq> m` have "\<not> nx strongly-postdominates m" 
      by(fastforce dest:strong_postdominate_antisym)
    have "(_Exit_) -[]\<rightarrow>* (_Exit_)" by(fastforce intro:empty_path)
    with `m strongly-postdominates nx` have "nx \<noteq> (_Exit_)"
      by(fastforce simp:strong_postdominate_def sourcenodes_def postdominate_def)
    have "\<not> nx strongly-postdominates (sourcenode a)"
    proof(rule ccontr)
      assume "\<not> \<not> nx strongly-postdominates sourcenode a"
      hence "nx strongly-postdominates sourcenode a" by simp
      from `m \<in> obs (sourcenode a) (PDG_BS S)` `nx \<in> obs (sourcenode a) (PDG_BS S)`
      obtain asx' where "sourcenode a -asx'\<rightarrow>* m" and "nx \<notin> set(sourcenodes asx')"
        by(fastforce elim:obs.cases)
      with `nx strongly-postdominates sourcenode a` have "nx strongly-postdominates m"
        by(rule strong_postdominate_path_targetnode)
      with `\<not> nx strongly-postdominates m` show False by simp
    qed
    with `nx \<in> obs (sourcenode a) (PDG_BS S)` `valid_node nx` `nx \<noteq> (_Exit_)` 
    show False by(fastforce dest:obs_strong_postdominate)
  next
    case False
    show False
    proof(cases "m = Exit")
      case True
      from `m \<in> obs (sourcenode a) (PDG_BS S)` `nx \<in> obs (sourcenode a) (PDG_BS S)`
      obtain xs where "sourcenode a -xs\<rightarrow>* m" and "nx \<notin> set(sourcenodes xs)"
        by(fastforce elim:obsE)
      obtain x' xs' where [simp]:"xs = x'#xs'"
      proof(cases xs)
        case Nil
        with `sourcenode a -xs\<rightarrow>* m` have [simp]:"sourcenode a = m" by fastforce
        with `m \<in> obs (sourcenode a) (PDG_BS S)` 
        have "m \<in> (PDG_BS S)" by (metis obsE)
        with `valid_node m` have "obs m (PDG_BS S) = {m}"
          by(rule n_in_obs)
        with `nx \<in> obs (sourcenode a) (PDG_BS S)` `nx \<noteq> m` have False
          by fastforce
        thus ?thesis by simp
      qed blast
      from `sourcenode a -xs\<rightarrow>* m` have "sourcenode a = sourcenode x'" 
        and "valid_edge x'" and "targetnode x' -xs'\<rightarrow>* m"
        by(auto elim:path_split_Cons)
      from `targetnode x' -xs'\<rightarrow>* m` `nx \<notin> set(sourcenodes xs)` `valid_edge x'` 
        `valid_node m` True
      have "\<not> nx strongly-postdominates (targetnode x')" 
        by(fastforce simp:strong_postdominate_def postdominate_def sourcenodes_def)
      from `nx \<noteq> m` True have "nx \<noteq> (_Exit_)" by simp
      with `obs (targetnode a) (PDG_BS S) = {nx}`
      have "nx strongly-postdominates (targetnode a)"
        by(fastforce intro:obs_strong_postdominate)
      from `obs (targetnode a) (PDG_BS S) = {nx}`
      obtain ys where "targetnode a -ys\<rightarrow>* nx" 
        and "\<forall>nx' \<in> set(sourcenodes ys). nx' \<notin> (PDG_BS S)"
        and "nx \<in> (PDG_BS S)" by(fastforce elim:obsE)
      hence "nx \<notin> set(sourcenodes ys)"by fastforce
      have "sourcenode a \<noteq> nx"
      proof
        assume "sourcenode a = nx"
        from `nx \<in> obs (sourcenode a) (PDG_BS S)`
        have "nx \<in> (PDG_BS S)" by -(erule obsE)
        with `valid_node nx` have "obs nx (PDG_BS S) = {nx}" by -(erule n_in_obs)
        with `sourcenode a = nx` `m \<in> obs (sourcenode a) (PDG_BS S)` 
          `nx \<noteq> m` show False by fastforce
      qed
      with `nx \<notin> set(sourcenodes ys)` have "nx \<notin> set(sourcenodes (a#ys))"
        by(fastforce simp:sourcenodes_def)
      from `valid_edge a` `targetnode a -ys\<rightarrow>* nx`
      have "sourcenode a -a#ys\<rightarrow>* nx" by(fastforce intro:Cons_path)
      from `sourcenode a -a#ys\<rightarrow>* nx` `nx \<notin> set(sourcenodes (a#ys))`
        `nx strongly-postdominates (targetnode a)` `valid_edge x'`
        `\<not> nx strongly-postdominates (targetnode x')` `sourcenode a = sourcenode x'`
      have "(sourcenode a) weakly controls nx"
        by(fastforce simp:weak_control_dependence_def)
      with `nx \<in> (PDG_BS S)` have "sourcenode a \<in> (PDG_BS S)"
        by(rule cd_closed)
      with `valid_edge a` have "obs (sourcenode a) (PDG_BS S) = {sourcenode a}"
        by(fastforce intro!:n_in_obs)
      with `m \<in> obs (sourcenode a) (PDG_BS S)`
        `nx \<in> obs (sourcenode a) (PDG_BS S)` `nx \<noteq> m`
      show False by simp
    next
      case False
      with `m \<in> obs (sourcenode a) (PDG_BS S)` `valid_node m`
        `\<not> m strongly-postdominates sourcenode a` 
      show False by(fastforce dest:obs_strong_postdominate)
    qed
  qed
qed


lemma WeakPDGBackwardSliceCorrect:
  "BackwardSlice sourcenode targetnode kind valid_edge
        (_Entry_) Def Use state_val PDG_BS"
proof(unfold_locales)
  fix n S assume "n \<in> PDG_BS S"
  thus "valid_node n" by(rule PDG_BS_valid_node)
next
  fix n S assume "valid_node n" and "n \<in> S"
  thus "n \<in> PDG_BS S" by(fastforce intro:PDG_path_Nil simp:PDG_BS_def)
next
  fix n' S n V assume "n' \<in> PDG_BS S" and "n influences V in n'"
  thus "n \<in> PDG_BS S"
    by(auto dest:PDG.PDG_path_ddep[OF PDG_wcd,OF PDG.PDG_ddep_edge[OF PDG_wcd]]
            dest:PDG_path_Append simp:PDG_BS_def split:split_if_asm)
next
  fix n S
  have "(\<exists>m. obs n (PDG_BS S) = {m}) \<or> obs n (PDG_BS S) = {}" 
    by(rule obs_singleton)
  thus "finite (obs n (PDG_BS S))" by fastforce
next
  fix n S
  have "(\<exists>m. obs n (PDG_BS S) = {m}) \<or> obs n (PDG_BS S) = {}" 
    by(rule obs_singleton)
  thus "card (obs n (PDG_BS S)) \<le> 1" by fastforce
qed

end


subsection{* Weak order dependence *}

context CFG_wf begin

lemma obs_singleton: 
  (*assumes valid:"valid_node n"*)
  shows "(\<exists>m. obs n (wod_backward_slice S) = {m}) \<or>
         obs n (wod_backward_slice S) = {}"
proof(rule ccontr)
  let ?WOD_BS = "wod_backward_slice S"
  assume "\<not> ((\<exists>m. obs n ?WOD_BS = {m}) \<or> obs n ?WOD_BS = {})"
  hence "\<exists>nx nx'. nx \<in> obs n ?WOD_BS \<and> nx' \<in> obs n ?WOD_BS \<and>
    nx \<noteq> nx'" by auto
  then obtain nx nx' where "nx \<in> obs n ?WOD_BS" and "nx' \<in> obs n ?WOD_BS"
    and "nx \<noteq> nx'" by auto
  from `nx \<in> obs n ?WOD_BS` obtain as where "n -as\<rightarrow>* nx" 
    and "\<forall>n' \<in> set(sourcenodes as). n' \<notin> ?WOD_BS" and "nx \<in> ?WOD_BS" 
    by(erule obsE)
  from `n -as\<rightarrow>* nx` have "valid_node nx" by(fastforce dest:path_valid_node)
  with `nx \<in> ?WOD_BS` have "obs nx ?WOD_BS = {nx}" by -(rule n_in_obs)
  with `n -as\<rightarrow>* nx` `nx \<in> obs n ?WOD_BS` `nx' \<in> obs n ?WOD_BS` `nx \<noteq> nx'` 
  have "as \<noteq> []" by(fastforce elim:path.cases)
  with `n -as\<rightarrow>* nx` `nx \<in> obs n ?WOD_BS` `nx' \<in> obs n ?WOD_BS` `nx \<noteq> nx'` 
    `obs nx ?WOD_BS = {nx}` `\<forall>n' \<in> set(sourcenodes as). n' \<notin> ?WOD_BS`
  have "\<exists>a as' as''. n -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* nx \<and>
                     valid_edge a \<and> as = as'@a#as'' \<and> 
                     obs (targetnode a) ?WOD_BS = {nx} \<and> 
                    (\<not> (\<exists>m. obs (sourcenode a) ?WOD_BS = {m} \<or> 
                       obs (sourcenode a) ?WOD_BS = {}))"
  proof(induct arbitrary:nx' rule:path.induct)
    case (Cons_path n'' as n' a n)
    note [simp] = `sourcenode a = n`[THEN sym] `targetnode a = n''`[THEN sym]
    note more_than_one = `n' \<in> obs n (?WOD_BS)` `nx' \<in> obs n (?WOD_BS)` `n' \<noteq> nx'`
    note IH = `\<And>nx'. \<lbrakk>n' \<in> obs n'' (?WOD_BS); nx' \<in> obs n'' (?WOD_BS); n' \<noteq> nx'; 
      obs n' (?WOD_BS) = {n'}; \<forall>n'\<in>set (sourcenodes as). n' \<notin> (?WOD_BS); as \<noteq> []\<rbrakk>
      \<Longrightarrow> \<exists>a as' as''. n'' -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* n' \<and>
      valid_edge a \<and> as = as'@a#as'' \<and> obs (targetnode a) (?WOD_BS) = {n'} \<and>
      (\<not> (\<exists>m. obs (sourcenode a) (?WOD_BS) = {m} \<or> 
      obs (sourcenode a) (?WOD_BS) = {}))`
    from `\<forall>n'\<in>set (sourcenodes (a#as)). n' \<notin> (?WOD_BS)`
    have "\<forall>n'\<in>set (sourcenodes as). n' \<notin> (?WOD_BS)" and "sourcenode a \<notin> (?WOD_BS)"
      by(simp_all add:sourcenodes_def)
    show ?case
    proof(cases "as = []")
      case True
      with `n'' -as\<rightarrow>* n'` have [simp]:"n' = n''" by(fastforce elim:path.cases)
      from more_than_one
      have "\<not> (\<exists>m. obs (sourcenode a) (?WOD_BS) = {m} \<or> 
               obs (sourcenode a) (?WOD_BS) = {})"
        by auto
      with `obs n' (?WOD_BS) = {n'}` True `valid_edge a` show ?thesis
        apply(rule_tac x="a" in exI)
        apply(rule_tac x="[]" in exI)
        apply(rule_tac x="[]" in exI)
        by(auto intro!:empty_path)
    next
      case False
      hence "as \<noteq> []" .
      from `n'' -as\<rightarrow>* n'` `\<forall>n'\<in>set (sourcenodes as). n' \<notin> (?WOD_BS)` 
      have "obs n' (?WOD_BS) \<subseteq> obs n'' (?WOD_BS)" by(rule path_obs_subset)
      show ?thesis
      proof(cases "obs n' (?WOD_BS) = obs n'' (?WOD_BS)")
        case True
        with `n'' -as\<rightarrow>* n'` `valid_edge a` `obs n' (?WOD_BS) = {n'}` more_than_one
        show ?thesis
          apply(rule_tac x="a" in exI)
          apply(rule_tac x="[]" in exI)
          apply(rule_tac x="as" in exI)
          by(fastforce intro:empty_path)
      next
        case False
        with `obs n' (?WOD_BS) \<subseteq> obs n'' (?WOD_BS)`
        have "obs n' (?WOD_BS) \<subset> obs n'' (?WOD_BS)" by simp
        with `obs n' (?WOD_BS) = {n'}` obtain ni where "n' \<in> obs n'' (?WOD_BS)"
          and "ni \<in> obs n'' (?WOD_BS)" and "n' \<noteq> ni" by auto
        from IH[OF this `obs n' (?WOD_BS) = {n'}` 
          `\<forall>n'\<in>set (sourcenodes as). n' \<notin> (?WOD_BS)` `as \<noteq> []`] obtain a' as' as''
          where "n'' -as'\<rightarrow>* sourcenode a'" and "targetnode a' -as''\<rightarrow>* n'"
          and "valid_edge a'" and [simp]:"as = as'@a'#as''" 
          and "obs (targetnode a') (?WOD_BS) = {n'}"
          and more_than_one':"\<not> (\<exists>m. obs (sourcenode a') (?WOD_BS) = {m} \<or> 
          obs (sourcenode a') (?WOD_BS) = {})"
          by blast
        from `n'' -as'\<rightarrow>* sourcenode a'` `valid_edge a`
        have "n -a#as'\<rightarrow>* sourcenode a'" by(fastforce intro:path.Cons_path)
        with `targetnode a' -as''\<rightarrow>* n'` `obs (targetnode a') (?WOD_BS) = {n'}`
          more_than_one' `valid_edge a'` show ?thesis
          apply(rule_tac x="a'" in exI)
          apply(rule_tac x="a#as'" in exI)
          apply(rule_tac x="as''" in exI)
          by fastforce
      qed
    qed
  qed simp
  then obtain a as' as'' where "valid_edge a"
    and "obs (targetnode a) (?WOD_BS) = {nx}"
    and more_than_one:"\<not> (\<exists>m. obs (sourcenode a) (?WOD_BS) = {m} \<or> 
                         obs (sourcenode a) (?WOD_BS) = {})"
    by blast
  have "sourcenode a \<notin> (?WOD_BS)"
  proof(rule ccontr)
    assume "\<not> sourcenode a \<notin> ?WOD_BS"
    hence "sourcenode a \<in> ?WOD_BS" by simp
    with `valid_edge a` have "obs (sourcenode a) (?WOD_BS) = {sourcenode a}"
      by(fastforce intro!:n_in_obs)
    with more_than_one show False by simp
  qed
  with `valid_edge a` 
  have "obs (targetnode a) (?WOD_BS) \<subseteq> obs (sourcenode a) (?WOD_BS)"
    by(rule edge_obs_subset)
  with `obs (targetnode a) (?WOD_BS) = {nx}` 
  have "nx \<in> obs (sourcenode a) (?WOD_BS)" by simp
  with more_than_one obtain m  where "m \<in> obs (sourcenode a) (?WOD_BS)"
    and "nx \<noteq> m" by auto
  with `nx \<in> obs (sourcenode a) (?WOD_BS)` obtain as2 
    where "sourcenode a -as2\<rightarrow>* m" and "nx \<notin> set(sourcenodes as2)" 
    by(fastforce elim:obsE)
  from `nx \<in> obs (sourcenode a) (?WOD_BS)` `m \<in> obs (sourcenode a) (?WOD_BS)` 
  obtain as1 where "sourcenode a -as1\<rightarrow>* nx" and "m \<notin> set(sourcenodes as1)"
    by(fastforce elim:obsE)
  from `obs (targetnode a) (?WOD_BS) = {nx}` obtain asx 
    where "targetnode a -asx\<rightarrow>* nx" by(fastforce elim:obsE)
  have "\<forall>asx'. targetnode a -asx'\<rightarrow>* m \<longrightarrow> nx \<in> set(sourcenodes asx')"
  proof(rule ccontr)
    assume "\<not> (\<forall>asx'. targetnode a -asx'\<rightarrow>* m \<longrightarrow> nx \<in> set (sourcenodes asx'))"
    then obtain asx' where "targetnode a -asx'\<rightarrow>* m" and "nx \<notin> set (sourcenodes asx')"
      by blast
    show False
    proof(cases "\<forall>nx \<in> set(sourcenodes asx'). nx \<notin> ?WOD_BS")
      case True
      with `targetnode a -asx'\<rightarrow>* m` `m \<in> obs (sourcenode a) (?WOD_BS)` 
      have "m \<in> obs (targetnode a) ?WOD_BS" by(fastforce intro:obs_elem elim:obsE)
      with `nx \<noteq> m` `obs (targetnode a) (?WOD_BS) = {nx}` show False by simp
    next
      case False
      hence "\<exists>nx \<in> set(sourcenodes asx'). nx \<in> ?WOD_BS" by blast
      then obtain nx' ns ns' where "sourcenodes asx' = ns@nx'#ns'" and "nx' \<in> ?WOD_BS"
        and "\<forall>nx \<in> set ns. nx \<notin> ?WOD_BS" by(fastforce elim!:split_list_first_propE)
      from `sourcenodes asx' = ns@nx'#ns'` obtain ax ai ai' 
        where [simp]:"asx' = ai@ax#ai'" "ns = sourcenodes ai" "nx' = sourcenode ax"
        by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
      from `targetnode a -asx'\<rightarrow>* m` have "targetnode a -ai\<rightarrow>* sourcenode ax"
        by(fastforce dest:path_split)
      with `nx' \<in> ?WOD_BS` `\<forall>nx \<in> set ns. nx \<notin> ?WOD_BS` 
      have "nx' \<in> obs (targetnode a) ?WOD_BS" by(fastforce intro:obs_elem)
      with `obs (targetnode a) (?WOD_BS) = {nx}` have "nx' = nx" by simp
      with `nx \<notin> set (sourcenodes asx')` show False by(simp add:sourcenodes_def)
    qed
  qed
  with `nx \<noteq> m` `sourcenode a -as1\<rightarrow>* nx` `m \<notin> set(sourcenodes as1)` 
    `sourcenode a -as2\<rightarrow>* m` `nx \<notin> set(sourcenodes as2)` `valid_edge a` 
    `targetnode a -asx\<rightarrow>* nx`
  have "sourcenode a \<longrightarrow>\<^bsub>wod\<^esub> nx,m" by(simp add:wod_def,blast)
  with `nx \<in> obs (sourcenode a) (?WOD_BS)` `m \<in> obs (sourcenode a) (?WOD_BS)` 
  have "sourcenode a \<in> ?WOD_BS" by(fastforce elim:cd_closed elim:obsE)
  with `sourcenode a \<notin> ?WOD_BS` show False by simp
qed


lemma WODBackwardSliceCorrect:
  "BackwardSlice sourcenode targetnode kind valid_edge
        (_Entry_) Def Use state_val wod_backward_slice"
proof(unfold_locales)
  fix n S assume "n \<in> wod_backward_slice S"
  thus "valid_node n" by(rule wod_backward_slice_valid_node)
next
  fix n S assume "valid_node n" and "n \<in> S"
  thus "n \<in> wod_backward_slice S" by(rule refl)
next
  fix n' S n V assume "n' \<in> wod_backward_slice S" "n influences V in n'"
  thus "n \<in> wod_backward_slice S"
    by -(rule dd_closed)
next
  fix n S
  have "(\<exists>m. obs n (wod_backward_slice S) = {m}) \<or> 
    obs n (wod_backward_slice S) = {}" 
    by(rule obs_singleton)
  thus "finite (obs n (wod_backward_slice S))" by fastforce
next
  fix n S 
  have "(\<exists>m. obs n (wod_backward_slice S) = {m}) \<or> obs n (wod_backward_slice S) = {}" 
    by(rule obs_singleton)
  thus "card (obs n (wod_backward_slice S)) \<le> 1" by fastforce
qed

end

end