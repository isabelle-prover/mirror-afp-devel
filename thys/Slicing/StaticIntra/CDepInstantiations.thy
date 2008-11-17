header {* \isaheader{Instantiate framework with control dependences} *}

theory CDepInstantiations imports Slice "../Basic/StandardControlDependence"
  "../Basic/WeakControlDependence" "../Basic/WeakOrderDependence" begin

subsection{* Standard control dependence *}

context StandardControlDependencePDG begin

lemma Exit_in_obs_slice_node:"(_Exit_) \<in> obs n' (PDG_BS n\<^isub>c) \<Longrightarrow> n\<^isub>c = (_Exit_)"
  by(auto elim:obsE PDG_path_CFG_path simp:PDG_BS_def split:split_if_asm)


lemma cd_closed:
  assumes isin:"n' \<in> PDG_BS n\<^isub>c" and controls:"n controls\<^isub>s n'"
  shows "n \<in> PDG_BS n\<^isub>c"
proof(cases "valid_node n\<^isub>c")
  case True
  hence valid:"valid_node n\<^isub>c" .
  show ?thesis
  proof(cases "inner_node n\<^isub>c")
    case True
    with valid isin controls show ?thesis
      by(fastsimp dest:PDG_cdep_edge PDG_path_Append PDG_path_cdep simp:PDG_BS_def)
  next
    case False
    with valid isin have eq:"n' = n\<^isub>c" 
      by(fastsimp intro:PDG_path_not_inner simp:PDG_BS_def)
    from False valid have "n\<^isub>c = (_Entry_) \<or> n\<^isub>c = (_Exit_)" by(simp add:inner_node_def)
    thus ?thesis
    proof
      assume "n\<^isub>c = (_Entry_)"
      with eq controls have False by(auto simp:standard_control_dependence_def)
      thus ?thesis by simp
    next
      assume "n\<^isub>c = (_Exit_)"
      with eq controls have False 
	by(fastsimp dest:Exit_not_standard_control_dependent)
      thus ?thesis by simp
    qed
  qed
next
  case False
  with isin have False by(simp add:PDG_BS_def)
  thus ?thesis by simp
qed


lemma obs_postdominate:
  assumes isin:"n \<in> obs n' (PDG_BS n\<^isub>c)" and sliceNotExit:"n\<^isub>c \<noteq> (_Exit_)"
  shows "n postdominates n'"
proof(rule ccontr)
  assume not_pd:"\<not> n postdominates n'" 
  from isin sliceNotExit have notExit:"n \<noteq> (_Exit_)"
    by(fastsimp dest:Exit_in_obs_slice_node)
  from isin have valid:"valid_node n" by(fastsimp dest:in_obs_valid)
  with isin notExit have pd_refl:"n postdominates n"
    by(fastsimp intro:postdominate_refl)
  from isin obtain as where path:"n' -as\<rightarrow>* n"
    and all_notinS:"\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS n\<^isub>c)"
    and "n \<in> (PDG_BS n\<^isub>c)" by(erule obsE)
  from pd_refl not_pd path obtain as' a as'' where as:"as = as'@a#as''"
    and valid_edge:"valid_edge a"
    and not_pd_source:"\<not> n postdominates (sourcenode a)"
    and pd_target:"n postdominates (targetnode a)"
    by -(erule postdominate_path_branch)
  from not_pd_source valid_edge valid obtain asx 
    where path':"sourcenode a -asx\<rightarrow>* (_Exit_)"
    and notin':"n \<notin> set(sourcenodes asx)" by(auto simp:postdominate_def)
  from path' valid_edge obtain ax asx' where asx:"asx = ax#asx'"
    apply - apply(erule path.cases)
    apply(drule_tac s="(_Exit_)" in sym)
    apply simp
    apply(drule Exit_source)
    apply simp_all
    by fastsimp
  with path' have "sourcenode a -[]@ax#asx'\<rightarrow>* (_Exit_)" by simp
  hence valid_edge':"valid_edge ax" and source':"sourcenode a = sourcenode ax"
    and path'':"targetnode ax -asx'\<rightarrow>* (_Exit_)"
    by(fastsimp dest:path_split)+
  from path'' notin' asx have not_pd':"\<not> n postdominates targetnode ax"
    by(fastsimp simp:postdominate_def sourcenodes_def)
  from isin all_notinS as have notin_sources:"n \<notin> set (sourcenodes (a#as''))"
    by(fastsimp elim:obs.cases simp:sourcenodes_def)
  from path as have "sourcenode a -a#as''\<rightarrow>* n"
    by(fastsimp dest:path_split_second)
  with pd_target not_pd' valid_edge' source' notin_sources
  have "sourcenode a controls\<^isub>s n"
    by(fastsimp simp:standard_control_dependence_def)
  with isin have "sourcenode a \<in> (PDG_BS n\<^isub>c)"
    by(fastsimp intro:cd_closed PDG_cdep_edge elim:obs.cases)
  with as all_notinS show False by(simp add:sourcenodes_def)
qed



lemma obs_singleton: 
  assumes valid:"valid_node n"
  shows "(\<exists>m. obs n (PDG_BS n\<^isub>c) = {m}) \<or> obs n (PDG_BS n\<^isub>c) = {}"
proof(rule ccontr)
  assume "\<not> ((\<exists>m. obs n (PDG_BS n\<^isub>c) = {m}) \<or> obs n (PDG_BS n\<^isub>c) = {})"
  hence "\<exists>nx nx'. nx \<in> obs n (PDG_BS n\<^isub>c) \<and> nx' \<in> obs n (PDG_BS n\<^isub>c) \<and>
    nx \<noteq> nx'" by auto
  then obtain nx nx' where isin:"nx \<in> obs n (PDG_BS n\<^isub>c)" 
    and isin':"nx' \<in> obs n (PDG_BS n\<^isub>c)"
    and noteq:"nx \<noteq> nx'" by auto
  hence notExit:"n\<^isub>c \<noteq> (_Exit_)"
    by(fastsimp elim:obsE dest:Exit_PDG_BS)
  from isin obtain as where path:"n -as\<rightarrow>* nx" 
    and all:"\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS n\<^isub>c)" 
    and nx_in_S:"nx \<in> (PDG_BS n\<^isub>c)" 
    by(erule obsE)
  from path have "valid_node nx" by(fastsimp dest:path_valid_node)
  with nx_in_S have obs_nx:"obs nx (PDG_BS n\<^isub>c) = {nx}" by -(rule n_in_obs)
  with path isin isin' noteq have notempty:"as \<noteq> []" by(fastsimp elim:path.cases)
  with path isin isin' noteq obs_nx all
  have "\<exists>a as' as''. n -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* nx \<and>
                     valid_edge a \<and> as = as'@a#as'' \<and> 
                     obs (targetnode a) (PDG_BS n\<^isub>c) = {nx} \<and> 
                    (\<not> (\<exists>m. obs (sourcenode a) (PDG_BS n\<^isub>c) = {m} \<or> 
                       obs (sourcenode a) (PDG_BS n\<^isub>c) = {}))"
  proof(induct arbitrary:nx' rule:path.induct)
    case (Cons_path n'' as n' a n)
    note path = `n'' -as\<rightarrow>* n'`
    note valid_edge = `valid_edge a`
    note source = `sourcenode a = n`
    note target = `targetnode a = n''`
    note singleton = `obs n' (PDG_BS n\<^isub>c) = {n'}`
    note more_than_one = `n' \<in> obs n (PDG_BS n\<^isub>c)` 
      `nx' \<in> obs n (PDG_BS n\<^isub>c)` `n' \<noteq> nx'`
    note IH = `\<And>nx'. \<lbrakk>n' \<in> obs n'' (PDG_BS n\<^isub>c); 
                       nx' \<in> obs n'' (PDG_BS n\<^isub>c); n' \<noteq> nx'; 
                       obs n' (PDG_BS n\<^isub>c) = {n'};
                       \<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS n\<^isub>c); as \<noteq> []\<rbrakk>
      \<Longrightarrow> \<exists>a as' as''. n'' -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* n' \<and>
        valid_edge a \<and> as = as'@a#as'' \<and> 
        obs (targetnode a) (PDG_BS n\<^isub>c) = {n'} \<and>
        (\<not> (\<exists>m. obs (sourcenode a) (PDG_BS n\<^isub>c) = {m} \<or> 
           obs (sourcenode a) (PDG_BS n\<^isub>c) = {}))`
    from `\<forall>n'\<in>set (sourcenodes (a#as)). n' \<notin> (PDG_BS n\<^isub>c)`
    have all:"\<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS n\<^isub>c)"
      and notin:"sourcenode a \<notin> (PDG_BS n\<^isub>c)"
      by(simp_all add:sourcenodes_def)
    show ?case
    proof(cases "as = []")
      case True
      with path have eq:"n'' = n'" by(fastsimp elim:path.cases)
      from more_than_one source
      have "\<not> (\<exists>m. obs (sourcenode a) (PDG_BS n\<^isub>c) = {m} \<or> 
	       obs (sourcenode a) (PDG_BS n\<^isub>c) = {})"
	by auto
      with target eq singleton source True valid_edge show ?thesis
	apply(rule_tac x="a" in exI)
	apply(rule_tac x="[]" in exI)
	apply(rule_tac x="[]" in exI)
	by(auto intro:empty_path)
    next
      case False
      hence notempty:"as \<noteq> []" .
      from path all 
      have subset:"obs n' (PDG_BS n\<^isub>c) \<subseteq> obs n'' (PDG_BS n\<^isub>c)"
	by(rule path_obs_subset)
      thus ?thesis
      proof(cases "obs n' (PDG_BS n\<^isub>c) = obs n'' (PDG_BS n\<^isub>c)")
	case True
	with path valid_edge source target singleton more_than_one
	show ?thesis
	  apply(rule_tac x="a" in exI)
	  apply(rule_tac x="[]" in exI)
	  apply(rule_tac x="as" in exI)
	  by(fastsimp intro:empty_path)
      next
	case False
	with subset 
	have "obs n' (PDG_BS n\<^isub>c) \<subset> obs n'' (PDG_BS n\<^isub>c)" by simp
	with singleton obtain ni where "n' \<in> obs n'' (PDG_BS n\<^isub>c)"
	  and "ni \<in> obs n'' (PDG_BS n\<^isub>c)" and "n' \<noteq> ni" by auto
	from IH[OF this singleton all notempty] obtain a' as' as''
	  where path1:"n'' -as'\<rightarrow>* sourcenode a'"
	  and path2:"targetnode a' -as''\<rightarrow>* n'"
	  and valid_edge':"valid_edge a'"
	  and as:"as = as'@a'#as''" 
	  and singleton':"obs (targetnode a') (PDG_BS n\<^isub>c) = {n'}"
	  and more_than_one':"\<not> (\<exists>m. obs (sourcenode a') (PDG_BS n\<^isub>c) = {m} \<or> 
	                        obs (sourcenode a') (PDG_BS n\<^isub>c) = {})"
	  by blast
	from path1 valid_edge source target have "n -a#as'\<rightarrow>* sourcenode a'"
	  by(fastsimp intro:path.Cons_path)
	with path2 as singleton' more_than_one' valid_edge' show ?thesis
	  apply(rule_tac x="a'" in exI)
	  apply(rule_tac x="a#as'" in exI)
	  apply(rule_tac x="as''" in exI)
	  by fastsimp
      qed
    qed
  qed simp
  then obtain a as' as'' where valid_edge:"valid_edge a"
    and singleton:"obs (targetnode a) (PDG_BS n\<^isub>c) = {nx}"
    and more_than_one:"\<not> (\<exists>m. obs (sourcenode a) (PDG_BS n\<^isub>c) = {m} \<or> 
                         obs (sourcenode a) (PDG_BS n\<^isub>c) = {})"
    by blast
  have "sourcenode a \<notin> (PDG_BS n\<^isub>c)"
  proof(rule ccontr)
    assume "\<not> sourcenode a \<notin> PDG_BS n\<^isub>c"
    hence "sourcenode a \<in> PDG_BS n\<^isub>c" by simp
    with valid_edge have "obs (sourcenode a) (PDG_BS n\<^isub>c) = {sourcenode a}"
      by(fastsimp intro!:n_in_obs)
    with more_than_one show False by simp
  qed
  with valid_edge 
  have "obs (targetnode a) (PDG_BS n\<^isub>c) \<subseteq> obs (sourcenode a) (PDG_BS n\<^isub>c)"
    by(rule edge_obs_subset)
  with singleton have nx_isin:"nx \<in> obs (sourcenode a) (PDG_BS n\<^isub>c)" by simp
  with more_than_one obtain m 
    where m_isin:"m \<in> obs (sourcenode a) (PDG_BS n\<^isub>c)"
    and noteq:"nx \<noteq> m" by auto
  from m_isin have valid_m:"valid_node m" by(fastsimp dest:in_obs_valid)
  from m_isin notExit have m_notExit:"m \<noteq> (_Exit_)"
    by(fastsimp dest:Exit_in_obs_slice_node)
  from singleton have valid_nx:"valid_node nx" by(fastsimp dest:in_obs_valid)
  from singleton notExit have nx_notExit:"nx \<noteq> (_Exit_)"
    by(auto dest:Exit_in_obs_slice_node)
  show False
  proof(cases "m postdominates (sourcenode a)")
    case True
    with nx_isin m_isin have "m postdominates nx"
      by(fastsimp intro:postdominate_path_targetnode elim:obs.cases)
    with noteq have "\<not> nx postdominates m" by(fastsimp dest:postdominate_antisym)
    with valid_nx valid_m obtain asx where path_exit:"m -asx\<rightarrow>* (_Exit_)"
      and notin:"nx \<notin> set(sourcenodes asx)" by(auto simp:postdominate_def)
    have not_pd:"\<not> nx postdominates (sourcenode a)"
    proof(rule ccontr)
      assume "\<not> \<not> nx postdominates sourcenode a"
      hence nx_pd_a:"nx postdominates sourcenode a" by simp
      from m_isin nx_isin obtain asx' where "sourcenode a -asx'\<rightarrow>* m"
	and notin':"nx \<notin> set(sourcenodes asx')"
	by(fastsimp elim:obs.cases)
      with path_exit have "sourcenode a -asx'@asx\<rightarrow>* (_Exit_)" by -(rule path_Append)
      with notin notin' nx_pd_a show False
	by(fastsimp simp:sourcenodes_def postdominate_def)
    qed
    with nx_isin valid_nx nx_notExit cd_closed notExit show False
      by(fastsimp dest:obs_postdominate)
  next
    case False
    with m_isin valid_m m_notExit cd_closed notExit show False
      by(fastsimp dest:obs_postdominate)
  qed
qed

lemma PDGBackwardSliceCorrect:
  "BackwardSlice sourcenode targetnode kind valid_edge
        (_Entry_) Def Use state_val PDG_BS"
proof
  fix n n\<^isub>c assume "n \<in> PDG_BS n\<^isub>c"
  thus "valid_node n" by(rule PDG_BS_valid_node)
next
  fix n assume "valid_node n"
  thus "n \<in> PDG_BS n" by(fastsimp intro:PDG_path_Nil simp:PDG_BS_def)
next
  fix n' n\<^isub>c n V
  assume "n' \<in> PDG_BS n\<^isub>c" and "n influences V in n'"
  thus "n \<in> PDG_BS n\<^isub>c"
    by(auto dest:PDG.PDG_path_ddep[OF PDG_scd,OF PDG.PDG_ddep_edge[OF PDG_scd]]
            dest:PDG_path_Append simp:PDG_BS_def split:split_if_asm)
next
  fix n n\<^isub>c assume "valid_node n"
  hence "(\<exists>m. obs n (PDG_BS n\<^isub>c) = {m}) \<or> obs n (PDG_BS n\<^isub>c) = {}" 
    by(rule obs_singleton)
  thus "finite (obs n (PDG_BS n\<^isub>c))" by fastsimp
next
  fix n n\<^isub>c assume "valid_node n"
  hence "(\<exists>m. obs n (PDG_BS n\<^isub>c) = {m}) \<or> obs n (PDG_BS n\<^isub>c) = {}" 
    by(rule obs_singleton)
  thus "card (obs n (PDG_BS n\<^isub>c)) \<le> 1" by fastsimp
qed

end


subsection{* Weak control dependence *}

context WeakControlDependencePDG begin

lemma Exit_in_obs_slice_node:"(_Exit_) \<in> obs n' (PDG_BS n\<^isub>c) \<Longrightarrow> n\<^isub>c = (_Exit_)"
  by(auto elim:obsE PDG_path_CFG_path simp:PDG_BS_def split:split_if_asm)


lemma cd_closed:
  assumes isin:"n' \<in> PDG_BS n\<^isub>c" and controls:"n weakly controls n'"
  shows "n \<in> PDG_BS n\<^isub>c"
proof(cases "valid_node n\<^isub>c")
  case True
  hence valid:"valid_node n\<^isub>c" .
  show ?thesis
  proof(cases "inner_node n\<^isub>c")
    case True
    with valid isin controls show ?thesis
      by(fastsimp dest:PDG_cdep_edge PDG_path_Append PDG_path_cdep simp:PDG_BS_def)
  next
    case False
    with valid isin have eq:"n' = n\<^isub>c" 
      by(fastsimp intro:PDG_path_not_inner simp:PDG_BS_def)
    from False valid have "n\<^isub>c = (_Entry_) \<or> n\<^isub>c = (_Exit_)" by(simp add:inner_node_def)
    thus ?thesis
    proof
      assume "n\<^isub>c = (_Entry_)"
      with eq controls have False by(auto simp:weak_control_dependence_def)
      thus ?thesis by simp
    next
      assume "n\<^isub>c = (_Exit_)"
      with eq controls have False by(fastsimp dest:Exit_not_weak_control_dependent)
      thus ?thesis by simp
    qed
  qed
next
  case False
  with isin have False by(simp add:PDG_BS_def)
  thus ?thesis by simp
qed


lemma obs_strong_postdominate:
  assumes isin:"n \<in> obs n' (PDG_BS n\<^isub>c)" and sliceNotExit:"n\<^isub>c \<noteq> (_Exit_)"
  shows "n strongly-postdominates n'"
proof(rule ccontr)
  assume not_spd:"\<not> n strongly-postdominates n'" 
  from isin sliceNotExit have notExit:"n \<noteq> (_Exit_)"
    by(fastsimp dest:Exit_in_obs_slice_node)
  from isin have valid:"valid_node n" by(fastsimp dest:in_obs_valid)
  with isin notExit have spd_refl:"n strongly-postdominates n"
    by(fastsimp intro:strong_postdominate_refl)
  from isin obtain as where path:"n' -as\<rightarrow>* n"
    and all_notinS:"\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS n\<^isub>c)"
    and "n \<in> (PDG_BS n\<^isub>c)" by(erule obsE)
  from spd_refl not_spd path obtain as' a as'' where as:"as = as'@a#as''"
    and valid_edge:"valid_edge a"
    and not_spd:"\<not> n strongly-postdominates (sourcenode a)"
    and spd:"n strongly-postdominates (targetnode a)"
    by -(erule strong_postdominate_path_branch)
  from isin all_notinS as have notin_sources:"n \<notin> set (sourcenodes (a#as''))"
    by(fastsimp elim:obs.cases simp:sourcenodes_def)
  from path as have source_path:"sourcenode a -a#as''\<rightarrow>* n"
    by(fastsimp dest:path_split_second)
  from not_spd valid valid_edge obtain a' where "sourcenode a' = sourcenode a"
    and "valid_edge a'" and "\<not> n strongly-postdominates (targetnode a')"
    by(fastsimp elim:not_strong_postdominate_predecessor_successor)
  with spd notin_sources source_path have "sourcenode a weakly controls n"
    by(fastsimp simp:weak_control_dependence_def)
  with isin have "sourcenode a \<in> (PDG_BS n\<^isub>c)"
    by(fastsimp intro:cd_closed PDG_cdep_edge elim:obs.cases)
  with as all_notinS show False by(simp add:sourcenodes_def)
qed



lemma obs_singleton: 
  assumes valid:"valid_node n"
  shows "(\<exists>m. obs n (PDG_BS n\<^isub>c) = {m}) \<or> obs n (PDG_BS n\<^isub>c) = {}"
proof(rule ccontr)
  assume "\<not> ((\<exists>m. obs n (PDG_BS n\<^isub>c) = {m}) \<or> obs n (PDG_BS n\<^isub>c) = {})"
  hence "\<exists>nx nx'. nx \<in> obs n (PDG_BS n\<^isub>c) \<and> nx' \<in> obs n (PDG_BS n\<^isub>c) \<and>
    nx \<noteq> nx'" by auto
  then obtain nx nx' where isin:"nx \<in> obs n (PDG_BS n\<^isub>c)" 
    and isin':"nx' \<in> obs n (PDG_BS n\<^isub>c)"
    and noteq:"nx \<noteq> nx'" by auto
  hence notExit:"n\<^isub>c \<noteq> (_Exit_)" by(fastsimp elim:obsE dest:Exit_PDG_BS)
  from isin obtain as where path:"n -as\<rightarrow>* nx" 
    and all:"\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS n\<^isub>c)" 
    and nx_in_S:"nx \<in> (PDG_BS n\<^isub>c)" 
    by(erule obsE)
  from path have "valid_node nx" by(fastsimp dest:path_valid_node)
  with nx_in_S have obs_nx:"obs nx (PDG_BS n\<^isub>c) = {nx}" by -(rule n_in_obs)
  with path isin isin' noteq have notempty:"as \<noteq> []" by(fastsimp elim:path.cases)
  with path isin isin' noteq obs_nx all
  have "\<exists>a as' as''. n -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* nx \<and>
                     valid_edge a \<and> as = as'@a#as'' \<and> 
                     obs (targetnode a) (PDG_BS n\<^isub>c) = {nx} \<and> 
                    (\<not> (\<exists>m. obs (sourcenode a) (PDG_BS n\<^isub>c) = {m} \<or> 
                       obs (sourcenode a) (PDG_BS n\<^isub>c) = {}))"
  proof(induct arbitrary:nx' rule:path.induct)
    case (Cons_path n'' as n' a n)
    note path = `n'' -as\<rightarrow>* n'`
    note valid_edge = `valid_edge a`
    note source = `sourcenode a = n`
    note target = `targetnode a = n''`
    note singleton = `obs n' (PDG_BS n\<^isub>c) = {n'}`
    note more_than_one = `n' \<in> obs n (PDG_BS n\<^isub>c)` 
      `nx' \<in> obs n (PDG_BS n\<^isub>c)` `n' \<noteq> nx'`
    note IH = `\<And>nx'. \<lbrakk>n' \<in> obs n'' (PDG_BS n\<^isub>c); 
                       nx' \<in> obs n'' (PDG_BS n\<^isub>c); n' \<noteq> nx'; 
                       obs n' (PDG_BS n\<^isub>c) = {n'};
                       \<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS n\<^isub>c); as \<noteq> []\<rbrakk>
      \<Longrightarrow> \<exists>a as' as''. n'' -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* n' \<and>
        valid_edge a \<and> as = as'@a#as'' \<and> 
        obs (targetnode a) (PDG_BS n\<^isub>c) = {n'} \<and>
        (\<not> (\<exists>m. obs (sourcenode a) (PDG_BS n\<^isub>c) = {m} \<or> 
           obs (sourcenode a) (PDG_BS n\<^isub>c) = {}))`
    from `\<forall>n'\<in>set (sourcenodes (a#as)). n' \<notin> (PDG_BS n\<^isub>c)`
    have all:"\<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS n\<^isub>c)"
      and notin:"sourcenode a \<notin> (PDG_BS n\<^isub>c)"
      by(simp_all add:sourcenodes_def)
    show ?case
    proof(cases "as = []")
      case True
      with path have eq:"n'' = n'" by(fastsimp elim:path.cases)
      from more_than_one source
      have "\<not> (\<exists>m. obs (sourcenode a) (PDG_BS n\<^isub>c) = {m} \<or> 
	       obs (sourcenode a) (PDG_BS n\<^isub>c) = {})"
	by auto
      with target eq singleton source True valid_edge show ?thesis
	apply(rule_tac x="a" in exI)
	apply(rule_tac x="[]" in exI)
	apply(rule_tac x="[]" in exI)
	by(auto intro:empty_path)
    next
      case False
      hence notempty:"as \<noteq> []" .
      from path all 
      have subset:"obs n' (PDG_BS n\<^isub>c) \<subseteq> obs n'' (PDG_BS n\<^isub>c)"
	by(rule path_obs_subset)
      thus ?thesis
      proof(cases "obs n' (PDG_BS n\<^isub>c) = obs n'' (PDG_BS n\<^isub>c)")
	case True
	with path valid_edge source target singleton more_than_one
	show ?thesis
	  apply(rule_tac x="a" in exI)
	  apply(rule_tac x="[]" in exI)
	  apply(rule_tac x="as" in exI)
	  by(fastsimp intro:empty_path)
      next
	case False
	with subset 
	have "obs n' (PDG_BS n\<^isub>c) \<subset> obs n'' (PDG_BS n\<^isub>c)" by simp
	with singleton obtain ni where "n' \<in> obs n'' (PDG_BS n\<^isub>c)"
	  and "ni \<in> obs n'' (PDG_BS n\<^isub>c)" and "n' \<noteq> ni" by auto
	from IH[OF this singleton all notempty] obtain a' as' as''
	  where path1:"n'' -as'\<rightarrow>* sourcenode a'"
	  and path2:"targetnode a' -as''\<rightarrow>* n'"
	  and valid_edge':"valid_edge a'"
	  and as:"as = as'@a'#as''" 
	  and singleton':"obs (targetnode a') (PDG_BS n\<^isub>c) = {n'}"
	  and more_than_one':"\<not> (\<exists>m. obs (sourcenode a') (PDG_BS n\<^isub>c) = {m} \<or> 
	                        obs (sourcenode a') (PDG_BS n\<^isub>c) = {})"
	  by blast
	from path1 valid_edge source target have "n -a#as'\<rightarrow>* sourcenode a'"
	  by(fastsimp intro:path.Cons_path)
	with path2 as singleton' more_than_one' valid_edge' show ?thesis
	  apply(rule_tac x="a'" in exI)
	  apply(rule_tac x="a#as'" in exI)
	  apply(rule_tac x="as''" in exI)
	  by fastsimp
      qed
    qed
  qed simp
  then obtain a as' as'' where valid_edge:"valid_edge a"
    and singleton:"obs (targetnode a) (PDG_BS n\<^isub>c) = {nx}"
    and more_than_one:"\<not> (\<exists>m. obs (sourcenode a) (PDG_BS n\<^isub>c) = {m} \<or> 
                         obs (sourcenode a) (PDG_BS n\<^isub>c) = {})"
    by blast
  have "sourcenode a \<notin> (PDG_BS n\<^isub>c)"
  proof(rule ccontr)
    assume "\<not> sourcenode a \<notin> PDG_BS n\<^isub>c"
    hence "sourcenode a \<in> PDG_BS n\<^isub>c" by simp
    with valid_edge have "obs (sourcenode a) (PDG_BS n\<^isub>c) = {sourcenode a}"
      by(fastsimp intro!:n_in_obs)
    with more_than_one show False by simp
  qed
  with valid_edge 
  have "obs (targetnode a) (PDG_BS n\<^isub>c) \<subseteq> obs (sourcenode a) (PDG_BS n\<^isub>c)"
    by(rule edge_obs_subset)
  with singleton have nx_isin:"nx \<in> obs (sourcenode a) (PDG_BS n\<^isub>c)" by simp
  with more_than_one obtain m 
    where m_isin:"m \<in> obs (sourcenode a) (PDG_BS n\<^isub>c)"
    and noteq:"nx \<noteq> m" by auto
  from m_isin notExit have m_notExit:"m \<noteq> (_Exit_)"
    by(fastsimp dest:Exit_in_obs_slice_node)
  from m_isin have valid_m:"valid_node m" by(fastsimp dest:in_obs_valid)
  then obtain xs where m_path:"m -xs\<rightarrow>* (_Exit_)" by(fastsimp dest:Exit_path)
  from singleton notExit have nx_notExit:"nx \<noteq> (_Exit_)"
    by(auto dest:Exit_in_obs_slice_node)
  from singleton have valid_nx:"valid_node nx" by(fastsimp dest:in_obs_valid)
  then obtain xs' where nx_path:"nx -xs'\<rightarrow>* (_Exit_)" by(fastsimp dest:Exit_path)
  show False
  proof(cases "m strongly-postdominates (sourcenode a)")
    case True
    with nx_isin m_isin have "m strongly-postdominates nx"
      by(fastsimp intro:strong_postdominate_path_targetnode elim:obs.cases)
    with noteq m_path nx_path have not_spd:"\<not> nx strongly-postdominates m"
      by(fastsimp dest:strong_postdominate_antisym)
    have not_pd:"\<not> nx strongly-postdominates (sourcenode a)"
    proof(rule ccontr)
      assume "\<not> \<not> nx strongly-postdominates sourcenode a"
      hence spd:"nx strongly-postdominates sourcenode a" by simp
      from nx_isin m_isin obtain asx where "sourcenode a -asx\<rightarrow>* m"
	and "nx \<notin> set(sourcenodes asx)" by(auto elim!:obsE)
      with spd have "nx strongly-postdominates m"
	by(rule strong_postdominate_path_targetnode)
      with not_spd show False by simp
    qed
    with nx_isin valid_nx nx_notExit cd_closed notExit show False
      by(fastsimp dest:obs_strong_postdominate)
  next
    case False
    with m_isin valid_m m_notExit cd_closed notExit show False
      by(fastsimp dest:obs_strong_postdominate)
  qed
qed



lemma WeakPDGBackwardSliceCorrect:
  "BackwardSlice sourcenode targetnode kind valid_edge
        (_Entry_) Def Use state_val PDG_BS"
proof
  fix n n\<^isub>c assume "n \<in> PDG_BS n\<^isub>c"
  thus "valid_node n" by(rule PDG_BS_valid_node)
next
  fix n assume "valid_node n"
  thus "n \<in> PDG_BS n" by(fastsimp intro:PDG_path_Nil simp:PDG_BS_def)
next
  fix n' n\<^isub>c n V assume "n' \<in> PDG_BS n\<^isub>c" and "n influences V in n'"
  thus "n \<in> PDG_BS n\<^isub>c"
    by(auto dest:PDG.PDG_path_ddep[OF PDG_wcd,OF PDG.PDG_ddep_edge[OF PDG_wcd]]
            dest:PDG_path_Append simp:PDG_BS_def split:split_if_asm)
next
  fix n n\<^isub>c assume "valid_node n"
  hence "(\<exists>m. obs n (PDG_BS n\<^isub>c) = {m}) \<or> obs n (PDG_BS n\<^isub>c) = {}" 
    by(rule obs_singleton)
  thus "finite (obs n (PDG_BS n\<^isub>c))" by fastsimp
next
  fix n n\<^isub>c assume "valid_node n"
  hence "(\<exists>m. obs n (PDG_BS n\<^isub>c) = {m}) \<or> obs n (PDG_BS n\<^isub>c) = {}" 
    by(rule obs_singleton)
  thus "card (obs n (PDG_BS n\<^isub>c)) \<le> 1" by fastsimp
qed

end


subsection{* Weak order dependence *}

context CFG_wf begin

lemma obs_singleton: 
  assumes valid:"valid_node n"
  shows "(\<exists>m. obs n (wod_backward_slice n\<^isub>c) = {m}) \<or>
         obs n (wod_backward_slice n\<^isub>c) = {}"
proof(rule ccontr)
  let ?WOD_BS = "wod_backward_slice n\<^isub>c"
  assume "\<not> ((\<exists>m. obs n ?WOD_BS = {m}) \<or> obs n ?WOD_BS = {})"
  hence "\<exists>nx nx'. nx \<in> obs n ?WOD_BS \<and> nx' \<in> obs n ?WOD_BS \<and>
    nx \<noteq> nx'" by auto
  then obtain nx nx' where isin:"nx \<in> obs n ?WOD_BS" 
    and isin':"nx' \<in> obs n ?WOD_BS"
    and noteq:"nx \<noteq> nx'" by auto
  from isin obtain as where path:"n -as\<rightarrow>* nx" 
    and all:"\<forall>n' \<in> set(sourcenodes as). n' \<notin> ?WOD_BS" 
    and nx_in_S:"nx \<in> ?WOD_BS" 
    by(erule obsE)
  from path have "valid_node nx" by(fastsimp dest:path_valid_node)
  with nx_in_S have obs_nx:"obs nx ?WOD_BS = {nx}" by -(rule n_in_obs)
  with path isin isin' noteq have notempty:"as \<noteq> []" by(fastsimp elim:path.cases)
  with path isin isin' noteq obs_nx all
  have "\<exists>a as' as''. n -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* nx \<and>
                     valid_edge a \<and> as = as'@a#as'' \<and> 
                     obs (targetnode a) ?WOD_BS = {nx} \<and> 
                    (\<not> (\<exists>m. obs (sourcenode a) ?WOD_BS = {m} \<or> 
                       obs (sourcenode a) ?WOD_BS = {}))"
  proof(induct arbitrary:nx' rule:path.induct)
    case (Cons_path n'' as n' a n)
    note path = `n'' -as\<rightarrow>* n'`
    note valid_edge = `valid_edge a`
    note source = `sourcenode a = n`
    note target = `targetnode a = n''`
    note singleton = `obs n' ?WOD_BS = {n'}`
    note more_than_one = `n' \<in> obs n ?WOD_BS` 
      `nx' \<in> obs n ?WOD_BS` `n' \<noteq> nx'`
    note IH = `\<And>nx'. \<lbrakk>n' \<in> obs n'' ?WOD_BS; 
                       nx' \<in> obs n'' ?WOD_BS; n' \<noteq> nx'; 
                       obs n' ?WOD_BS = {n'};
                       \<forall>n'\<in>set (sourcenodes as). n' \<notin> ?WOD_BS; as \<noteq> []\<rbrakk>
      \<Longrightarrow> \<exists>a as' as''. n'' -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* n' \<and>
        valid_edge a \<and> as = as'@a#as'' \<and> 
        obs (targetnode a) ?WOD_BS = {n'} \<and>
        (\<not> (\<exists>m. obs (sourcenode a) ?WOD_BS = {m} \<or> 
           obs (sourcenode a) ?WOD_BS = {}))`
    from `\<forall>n'\<in>set (sourcenodes (a#as)). n' \<notin> ?WOD_BS`
    have all:"\<forall>n'\<in>set (sourcenodes as). n' \<notin> ?WOD_BS"
      and notin:"sourcenode a \<notin> ?WOD_BS"
      by(simp_all add:sourcenodes_def)
    show ?case
    proof(cases "as = []")
      case True
      with path have eq:"n'' = n'" by(fastsimp elim:path.cases)
      from more_than_one source
      have "\<not> (\<exists>m. obs (sourcenode a) ?WOD_BS = {m} \<or> 
	       obs (sourcenode a) ?WOD_BS = {})"
	by auto
      with target eq singleton source True valid_edge show ?thesis
	apply(rule_tac x="a" in exI)
	apply(rule_tac x="[]" in exI)
	apply(rule_tac x="[]" in exI)
	by(auto intro:empty_path)
    next
      case False
      hence notempty:"as \<noteq> []" .
      from path all 
      have subset:"obs n' ?WOD_BS \<subseteq> obs n'' ?WOD_BS"
	by(rule path_obs_subset)
      thus ?thesis
      proof(cases "obs n' ?WOD_BS = obs n'' ?WOD_BS")
	case True
	with path valid_edge source target singleton more_than_one
	show ?thesis
	  apply(rule_tac x="a" in exI)
	  apply(rule_tac x="[]" in exI)
	  apply(rule_tac x="as" in exI)
	  by(fastsimp intro:empty_path)
      next
	case False
	with subset 
	have "obs n' ?WOD_BS \<subset> obs n'' ?WOD_BS" by simp
	with singleton obtain ni where "n' \<in> obs n'' ?WOD_BS"
	  and "ni \<in> obs n'' ?WOD_BS" and "n' \<noteq> ni" by auto
	from IH[OF this singleton all notempty] obtain a' as' as''
	  where path1:"n'' -as'\<rightarrow>* sourcenode a'"
	  and path2:"targetnode a' -as''\<rightarrow>* n'"
	  and valid_edge':"valid_edge a'"
	  and as:"as = as'@a'#as''" 
	  and singleton':"obs (targetnode a') ?WOD_BS = {n'}"
	  and more_than_one':"\<not> (\<exists>m. obs (sourcenode a') ?WOD_BS = {m} \<or> 
	                        obs (sourcenode a') ?WOD_BS = {})"
	  by blast
	from path1 valid_edge source target have "n -a#as'\<rightarrow>* sourcenode a'"
	  by(fastsimp intro:path.Cons_path)
	with path2 as singleton' more_than_one' valid_edge' show ?thesis
	  apply(rule_tac x="a'" in exI)
	  apply(rule_tac x="a#as'" in exI)
	  apply(rule_tac x="as''" in exI)
	  by fastsimp
      qed
    qed
  qed simp
  then obtain a as' as'' where valid_edge:"valid_edge a" and as:"as = as'@a#as''"
    and singleton:"obs (targetnode a) ?WOD_BS = {nx}"
    and more_than_one:"\<not> (\<exists>m. obs (sourcenode a) ?WOD_BS = {m} \<or> 
                         obs (sourcenode a) ?WOD_BS = {})"
    by blast
  from all as have notin:"sourcenode a \<notin> ?WOD_BS" by(simp add:sourcenodes_def)
  with valid_edge 
  have "obs (targetnode a) ?WOD_BS \<subseteq> obs (sourcenode a) ?WOD_BS"
    by(rule edge_obs_subset)
  with singleton have nx_isin:"nx \<in> obs (sourcenode a) ?WOD_BS" by simp
  with more_than_one obtain m 
    where m_isin:"m \<in> obs (sourcenode a) ?WOD_BS"
    and noteq:"nx \<noteq> m" by auto
  with nx_isin obtain as2 where path2:"sourcenode a -as2\<rightarrow>* m" 
    and notin2:"nx \<notin> set(sourcenodes as2)" by(fastsimp elim:obsE)
  from nx_isin m_isin obtain as1 where path1:"sourcenode a -as1\<rightarrow>* nx" 
    and notin1:"m \<notin> set(sourcenodes as1)" by(fastsimp elim:obsE)
  from singleton obtain asx where pathx:"targetnode a -asx\<rightarrow>* nx"
    by(fastsimp elim:obsE)
  have "\<forall>asx'. targetnode a -asx'\<rightarrow>* m \<longrightarrow> nx \<in> set(sourcenodes asx')"
  proof(rule ccontr)
    assume "\<not> (\<forall>asx'. targetnode a -asx'\<rightarrow>* m \<longrightarrow> nx \<in> set (sourcenodes asx'))"
    then obtain asx' where path':"targetnode a -asx'\<rightarrow>* m"
      and notin':"nx \<notin> set (sourcenodes asx')" by blast
    show False
    proof(cases "\<forall>nx \<in> set(sourcenodes asx'). nx \<notin> ?WOD_BS")
      case True
      with path' m_isin have "m \<in> obs (targetnode a) ?WOD_BS"
	by(fastsimp intro:obs_elem elim:obsE)
      with noteq singleton show False by simp
    next
      case False
      hence "\<exists>nx \<in> set(sourcenodes asx'). nx \<in> ?WOD_BS" by blast
      then obtain nx' ns ns' where sources:"sourcenodes asx' = ns@nx'#ns'"
	and isin_x:"nx' \<in> ?WOD_BS" and notin:"\<forall>nx \<in> set ns. nx \<notin> ?WOD_BS"
	by(fastsimp elim!:leftmost_element_property)
      from sources obtain ax ai ai' where asx':"asx' = ai@ax#ai'"
	and ns:"sourcenodes ai = ns" and nx':"sourcenode ax = nx'"
	by(fastsimp elim:map_append_append_maps simp:sourcenodes_def)
      from path' asx' have "targetnode a -ai\<rightarrow>* sourcenode ax"
	by(fastsimp dest:path_split)
      with nx' isin_x ns notin have "nx' \<in> obs (targetnode a) ?WOD_BS"
	by(fastsimp intro:obs_elem)
      with singleton have "nx' = nx" by simp
      with notin' asx' nx' show False by(simp add:sourcenodes_def)
    qed
  qed
  with noteq path1 notin1 path2 notin2 valid_edge pathx
  have "sourcenode a \<longrightarrow>\<^bsub>wod\<^esub> nx,m" by(simp add:wod_def,blast)
  with nx_isin m_isin have "sourcenode a \<in> ?WOD_BS"
    by(fastsimp elim:cd_closed elim:obsE)
  with notin show False by simp
qed


lemma "BackwardSlice sourcenode targetnode kind valid_edge
        (_Entry_) Def Use state_val wod_backward_slice"
proof
  fix n n\<^isub>c assume "n \<in> wod_backward_slice n\<^isub>c"
  thus "valid_node n" by(rule wod_backward_slice_valid_node)
next
  fix n assume "valid_node n"
  thus "n \<in> wod_backward_slice n" by(rule refl)
next
  fix n' n\<^isub>c n V assume "n' \<in> wod_backward_slice n\<^isub>c" "n influences V in n'"
  thus "n \<in> wod_backward_slice n\<^isub>c"
    by -(rule dd_closed)
next
  fix n n\<^isub>c assume "valid_node n"
  hence "(\<exists>m. obs n (wod_backward_slice n\<^isub>c) = {m}) \<or> 
    obs n (wod_backward_slice n\<^isub>c) = {}" 
    by(rule obs_singleton)
  thus "finite (obs n (wod_backward_slice n\<^isub>c))" by fastsimp
next
  fix n n\<^isub>c assume "valid_node n"
  hence "(\<exists>m. obs n (wod_backward_slice n\<^isub>c) = {m}) \<or> 
    obs n (wod_backward_slice n\<^isub>c) = {}" 
    by(rule obs_singleton)
  thus "card (obs n (wod_backward_slice n\<^isub>c)) \<le> 1" by fastsimp
qed

end

end