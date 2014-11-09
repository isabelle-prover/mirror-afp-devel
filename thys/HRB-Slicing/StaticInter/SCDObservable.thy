section {* Observable sets w.r.t.\ standard control dependence *}

theory SCDObservable imports Observable HRBSlice begin

context SDG begin

lemma matched_bracket_assms_variant:
  assumes "n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2 \<or> n\<^sub>1 -p:V'\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2" and "matched n\<^sub>2 ns' n\<^sub>3" 
  and "n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4"
  and "call_of_return_node (parent_node n\<^sub>4) (parent_node n\<^sub>1)"
  obtains a a' where "valid_edge a" and "a' \<in> get_return_edges a"
  and "sourcenode a = parent_node n\<^sub>1" and "targetnode a = parent_node n\<^sub>2"
  and "sourcenode a' = parent_node n\<^sub>3" and "targetnode a' = parent_node n\<^sub>4"
proof(atomize_elim)
  from `n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2 \<or> n\<^sub>1 -p:V'\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2` obtain a Q r fs where "valid_edge a" 
    and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "parent_node n\<^sub>1 = sourcenode a"
    and "parent_node n\<^sub>2 = targetnode a"
    by(fastforce elim:SDG_edge.cases)
  from `n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4` obtain a' Q' f'
    where "valid_edge a'" and "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    and "parent_node n\<^sub>3 = sourcenode a'" and "parent_node n\<^sub>4 = targetnode a'"
    by(fastforce elim:SDG_edge.cases)
  from `valid_edge a'` `kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'`
  obtain ax where "valid_edge ax" and "\<exists>Q r fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    and "a' \<in> get_return_edges ax"
    by -(drule return_needs_call,fastforce+)
  from `valid_edge a` `valid_edge ax` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `\<exists>Q r fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
  have "targetnode a = targetnode ax" by(fastforce dest:same_proc_call_unique_target)
  from `valid_edge a'` `a' \<in> get_return_edges ax` `valid_edge ax`
  have "call_of_return_node (targetnode a') (sourcenode ax)"
    by(fastforce simp:return_node_def call_of_return_node_def)
  with `call_of_return_node (parent_node n\<^sub>4) (parent_node n\<^sub>1)` 
    `parent_node n\<^sub>4 = targetnode a'`
  have "sourcenode ax = parent_node n\<^sub>1" by fastforce
  with `valid_edge ax` `a' \<in> get_return_edges ax` `targetnode a = targetnode ax`
    `parent_node n\<^sub>2 = targetnode a` `parent_node n\<^sub>3 = sourcenode a'` 
    `parent_node n\<^sub>4 = targetnode a'`
  show "\<exists>a a'. valid_edge a \<and> a' \<in> get_return_edges a \<and>
    sourcenode a = parent_node n\<^sub>1 \<and> targetnode a = parent_node n\<^sub>2 \<and>
    sourcenode a' = parent_node n\<^sub>3 \<and> targetnode a' = parent_node n\<^sub>4"
    by fastforce
qed

subsection {* Observable set of standard control dependence is at most a singleton *}

definition SDG_to_CFG_set :: "'node SDG_node set \<Rightarrow> 'node set" ("\<lfloor>_\<rfloor>\<^bsub>CFG\<^esub>")
  where "\<lfloor>S\<rfloor>\<^bsub>CFG\<^esub> \<equiv> {m. CFG_node m \<in> S}"


lemma [intro]:"\<forall>n \<in> S. valid_SDG_node n \<Longrightarrow> \<forall>n \<in> \<lfloor>S\<rfloor>\<^bsub>CFG\<^esub>. valid_node n"
  by(fastforce simp:SDG_to_CFG_set_def)


lemma Exit_HRB_Slice:
  assumes "n \<in> \<lfloor>HRB_slice {CFG_node (_Exit_)}\<rfloor>\<^bsub>CFG\<^esub>" shows "n = (_Exit_)"
proof -
  from `n \<in> \<lfloor>HRB_slice {CFG_node (_Exit_)}\<rfloor>\<^bsub>CFG\<^esub>` 
  have "CFG_node n \<in> HRB_slice {CFG_node (_Exit_)}"
    by(simp add:SDG_to_CFG_set_def)
  thus ?thesis
  proof(induct "CFG_node n" rule:HRB_slice_cases)
    case (phase1 nx)
    from `nx \<in> {CFG_node (_Exit_)}` have "nx = CFG_node (_Exit_)" by simp
    with `CFG_node n \<in> sum_SDG_slice1 nx`
    have "CFG_node n = CFG_node (_Exit_) \<or> 
      (\<exists>n Vopt popt b. sum_SDG_edge n Vopt popt b (CFG_node (_Exit_)))"
      by(induct rule:sum_SDG_slice1.induct) auto
    then show ?thesis by(fastforce dest:Exit_no_sum_SDG_edge_target)
  next
    case (phase2 nx n' n'' p)
    from `nx \<in> {CFG_node (_Exit_)}` have "nx = CFG_node (_Exit_)" by simp
    with `n' \<in> sum_SDG_slice1 nx`
    have "n' = CFG_node (_Exit_) \<or> 
      (\<exists>n Vopt popt b. sum_SDG_edge n Vopt popt b (CFG_node (_Exit_)))"
      by(induct rule:sum_SDG_slice1.induct) auto
    hence "n' = CFG_node (_Exit_)" by(fastforce dest:Exit_no_sum_SDG_edge_target)
    with `CFG_node n \<in> sum_SDG_slice2 n'`
    have "CFG_node n = CFG_node (_Exit_) \<or> 
      (\<exists>n Vopt popt b. sum_SDG_edge n Vopt popt b (CFG_node (_Exit_)))"
      by(induct rule:sum_SDG_slice2.induct) auto
    then show ?thesis by(fastforce dest:Exit_no_sum_SDG_edge_target)
  qed
qed


lemma Exit_in_obs_intra_slice_node:
  assumes "(_Exit_) \<in> obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  shows "CFG_node (_Exit_) \<in> S"
proof -
  let ?S' = "\<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  from `(_Exit_) \<in> obs_intra n' ?S'` obtain as where "n' -as\<rightarrow>\<^sub>\<iota>* (_Exit_)"
    and "\<forall>nx \<in> set(sourcenodes as). nx \<notin> ?S'" and "(_Exit_) \<in> ?S'"
    by(erule obs_intraE)
  from `(_Exit_) \<in> ?S'` 
  have "CFG_node (_Exit_) \<in> HRB_slice S" by(simp add:SDG_to_CFG_set_def)
  thus ?thesis
  proof(induct "CFG_node (_Exit_)" rule:HRB_slice_cases)
    case (phase1 nx)
    thus ?case
      by(induct "CFG_node (_Exit_)" rule:sum_SDG_slice1.induct,
        auto dest:Exit_no_sum_SDG_edge_source)
  next
    case (phase2 nx n' n'' p)
    from `CFG_node (_Exit_) \<in> sum_SDG_slice2 n'` `n' \<in> sum_SDG_slice1 nx` `nx \<in> S`
    show ?case
      apply(induct n\<equiv>"CFG_node (_Exit_)" rule:sum_SDG_slice2.induct)
      apply(auto dest:Exit_no_sum_SDG_edge_source)
      apply(hypsubst_thin)
      apply(induct n\<equiv>"CFG_node (_Exit_)" rule:sum_SDG_slice1.induct)
      apply(auto dest:Exit_no_sum_SDG_edge_source)
      done
  qed
qed


lemma obs_intra_postdominate:
  assumes "n \<in> obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "\<not> method_exit n"
  shows "n postdominates n'"
proof(rule ccontr)
  assume "\<not> n postdominates n'"
  from `n \<in> obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` have "valid_node n" 
    by(fastforce dest:in_obs_intra_valid)
  with `n \<in> obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `\<not> method_exit n` have "n postdominates n"
    by(fastforce intro:postdominate_refl)
  from `n \<in> obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` obtain as where "n' -as\<rightarrow>\<^sub>\<iota>* n"
    and all_notinS:"\<forall>n' \<in> set(sourcenodes as). n' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    and "n \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(erule obs_intraE)
  from `n postdominates n` `\<not> n postdominates n'` `n' -as\<rightarrow>\<^sub>\<iota>* n`
  obtain as' a as'' where [simp]:"as = as'@a#as''"
    and "valid_edge a" and "\<not> n postdominates (sourcenode a)"
    and "n postdominates (targetnode a)"  and "intra_kind (kind a)"
    by(fastforce elim!:postdominate_path_branch simp:intra_path_def)
  from `n' -as\<rightarrow>\<^sub>\<iota>* n` have "sourcenode a -a#as''\<rightarrow>\<^sub>\<iota>* n"
    by(fastforce elim:path_split intro:Cons_path simp:intra_path_def)
  with `\<not> n postdominates (sourcenode a)` `valid_edge a` `valid_node n` 
  obtain asx pex where "sourcenode a -asx\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex" 
    and "n \<notin> set(sourcenodes asx)" by(fastforce simp:postdominate_def)
  have "asx \<noteq> []"
  proof
    assume "asx = []"
    with `sourcenode a -asx\<rightarrow>\<^sub>\<iota>* pex` have "sourcenode a = pex" 
      by(fastforce simp:intra_path_def)
    from `method_exit pex` show False
    proof(rule method_exit_cases)
      assume "pex = (_Exit_)"
      with `sourcenode a = pex` have "sourcenode a = (_Exit_)" by simp
      with `valid_edge a` show False by(rule Exit_source)
    next
      fix a' Q f p
      assume "pex = sourcenode a'" and "valid_edge a'" and "kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      from `valid_edge a'` `kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `valid_edge a` `intra_kind (kind a)`
        `sourcenode a = pex` `pex = sourcenode a'`
      show False by(fastforce dest:return_edges_only simp:intra_kind_def)
    qed
  qed
  then obtain ax asx' where [simp]:"asx = ax#asx'" by(cases asx) auto
  with `sourcenode a -asx\<rightarrow>\<^sub>\<iota>* pex` have "sourcenode a -ax#asx'\<rightarrow>* pex"
    by(simp add:intra_path_def)
  hence "valid_edge ax" and [simp]:"sourcenode a = sourcenode ax"
    and "targetnode ax -asx'\<rightarrow>* pex" by(auto elim:path_split_Cons)
  with `sourcenode a -asx\<rightarrow>\<^sub>\<iota>* pex` have "targetnode ax -asx'\<rightarrow>\<^sub>\<iota>* pex"
    by(simp add:intra_path_def)
  with `valid_edge ax` `n \<notin> set(sourcenodes asx)` `method_exit pex`
  have "\<not> n postdominates targetnode ax"
    by(fastforce simp:postdominate_def sourcenodes_def)
  from `n \<in> obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` all_notinS 
  have "n \<notin> set (sourcenodes (a#as''))"
    by(fastforce elim:obs_intra.cases simp:sourcenodes_def)
  from `sourcenode a -asx\<rightarrow>\<^sub>\<iota>* pex` have "intra_kind (kind ax)"
    by(simp add:intra_path_def)
  with `sourcenode a -a#as''\<rightarrow>\<^sub>\<iota>* n` `n postdominates (targetnode a)` 
    `\<not> n postdominates targetnode ax` `valid_edge ax` 
    `n \<notin> set (sourcenodes (a#as''))` `intra_kind (kind a)`
  have "(sourcenode a) controls n"
    by(fastforce simp:control_dependence_def)
  hence "CFG_node (sourcenode a) s\<longrightarrow>\<^bsub>cd\<^esub> CFG_node n"
    by(fastforce intro:sum_SDG_cdep_edge)
  with `n \<in> obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` have "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by(auto elim!:obs_intraE combine_SDG_slices.cases 
            intro:combine_SDG_slices.intros sum_SDG_slice1.intros 
                  sum_SDG_slice2.intros simp:HRB_slice_def SDG_to_CFG_set_def)
  with all_notinS show False by(simp add:sourcenodes_def)
qed



lemma obs_intra_singleton_disj: 
  assumes "valid_node n"
  shows "(\<exists>m. obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m}) \<or> 
         obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}"
proof(rule ccontr)
  assume "\<not> ((\<exists>m. obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m}) \<or> 
             obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {})"
  hence "\<exists>nx nx'. nx \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<and> 
    nx' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<and> nx \<noteq> nx'" by auto
  then obtain nx nx' where "nx \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" 
    and "nx' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "nx \<noteq> nx'" by auto
  from `nx \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` obtain as where "n -as\<rightarrow>\<^sub>\<iota>* nx" 
    and all:"\<forall>n' \<in> set(sourcenodes as). n' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" 
    and "nx \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" 
    by(erule obs_intraE)
  from `n -as\<rightarrow>\<^sub>\<iota>* nx` have "n -as\<rightarrow>* nx" and "\<forall>a \<in> set as. intra_kind (kind a)"
    by(simp_all add:intra_path_def)
  hence "valid_node nx" by(fastforce dest:path_valid_node)
  with `nx \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` have "obs_intra nx \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx}" 
    by -(rule n_in_obs_intra)
  with `n -as\<rightarrow>* nx` `nx \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` 
    `nx' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `nx \<noteq> nx'` have "as \<noteq> []" 
    by(fastforce elim:path.cases simp:intra_path_def)
  with `n -as\<rightarrow>* nx` `nx \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` 
    `nx' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `nx \<noteq> nx'` 
    `obs_intra nx \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx}` `\<forall>a \<in> set as. intra_kind (kind a)` all
  have "\<exists>a as' as''. n -as'\<rightarrow>\<^sub>\<iota>* sourcenode a \<and> targetnode a -as''\<rightarrow>\<^sub>\<iota>* nx \<and>
                     valid_edge a \<and> as = as'@a#as'' \<and> intra_kind (kind a) \<and>
                     obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx} \<and> 
                    (\<not> (\<exists>m. obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m} \<or> 
                       obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}))"
  proof(induct arbitrary:nx' rule:path.induct)
    case (Cons_path n'' as n' a n)
    note IH = `\<And>nx'. \<lbrakk>n' \<in> obs_intra n'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; 
                       nx' \<in> obs_intra n'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; n' \<noteq> nx'; 
                       obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'};
                       \<forall>a\<in>set as. intra_kind (kind a);
                       \<forall>n'\<in>set (sourcenodes as). n' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; as \<noteq> []\<rbrakk>
      \<Longrightarrow> \<exists>a as' as''. n'' -as'\<rightarrow>\<^sub>\<iota>* sourcenode a \<and> targetnode a -as''\<rightarrow>\<^sub>\<iota>* n' \<and>
        valid_edge a \<and> as = as'@a#as'' \<and> intra_kind (kind a) \<and>
        obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'} \<and>
        (\<not> (\<exists>m. obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m} \<or> 
           obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}))`
    note more_than_one = `n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `nx' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `n' \<noteq> nx'`
    from `\<forall>a\<in>set (a#as). intra_kind (kind a)`
    have "\<forall>a\<in>set as. intra_kind (kind a)" and "intra_kind (kind a)" by simp_all
    from `\<forall>n'\<in>set (sourcenodes (a#as)). n' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have all:"\<forall>n'\<in>set (sourcenodes as). n' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(simp add:sourcenodes_def)
    show ?case
    proof(cases "as = []")
      case True
      with `n'' -as\<rightarrow>* n'` have [simp]:"n'' = n'" by(fastforce elim:path.cases)
      from more_than_one `sourcenode a = n`
      have "\<not> (\<exists>m. obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m} \<or> 
               obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {})"
        by auto
      with `targetnode a = n''` `obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'}`
        `sourcenode a = n` True `valid_edge a` `intra_kind (kind a)` 
      show ?thesis
        apply(rule_tac x="a" in exI)
        apply(rule_tac x="[]" in exI)
        apply(rule_tac x="[]" in exI)
        by(auto intro:empty_path simp:intra_path_def)
    next
      case False
      from `n'' -as\<rightarrow>* n'` `\<forall>a\<in>set (a # as). intra_kind (kind a)`
      have "n'' -as\<rightarrow>\<^sub>\<iota>* n'" by(simp add:intra_path_def)
      with all 
      have subset:"obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<subseteq> obs_intra n'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by -(rule path_obs_intra_subset)
      thus ?thesis
      proof(cases "obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs_intra n'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
        case True
        with `n'' -as\<rightarrow>\<^sub>\<iota>* n'` `valid_edge a` `sourcenode a = n` `targetnode a = n''`
          `obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'}` `intra_kind (kind a)` more_than_one
        show ?thesis
          apply(rule_tac x="a" in exI)
          apply(rule_tac x="[]" in exI)
          apply(rule_tac x="as" in exI)
          by(fastforce intro:empty_path simp:intra_path_def)
      next
        case False
        with subset
        have "obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<subset> obs_intra n'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
        with `obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'}` 
        obtain ni where "n' \<in> obs_intra n'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
          and "ni \<in> obs_intra n'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "n' \<noteq> ni" by auto
        from IH[OF this `obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'}` 
          `\<forall>a\<in>set as. intra_kind (kind a)` all `as \<noteq> []`] obtain a' as' as''
          where "n'' -as'\<rightarrow>\<^sub>\<iota>* sourcenode a'" 
          and hyps:"targetnode a' -as''\<rightarrow>\<^sub>\<iota>* n'" "valid_edge a'" "as = as'@a'#as''" 
            "intra_kind (kind a')" "obs_intra (targetnode a') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'}"
            "\<not> (\<exists>m. obs_intra (sourcenode a') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m} \<or> 
                                obs_intra (sourcenode a') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {})"
          by blast
        from `n'' -as'\<rightarrow>\<^sub>\<iota>* sourcenode a'` `valid_edge a` `sourcenode a = n` 
          `targetnode a = n''` `intra_kind (kind a)` `intra_kind (kind a')`
        have "n -a#as'\<rightarrow>\<^sub>\<iota>* sourcenode a'"
          by(fastforce intro:path.Cons_path simp:intra_path_def)
        with hyps show ?thesis
          apply(rule_tac x="a'" in exI)
          apply(rule_tac x="a#as'" in exI)
          apply(rule_tac x="as''" in exI)
          by fastforce
      qed
    qed
  qed simp
  then obtain a as' as'' where "valid_edge a" and "intra_kind (kind a)"
    and "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx}"
    and more_than_one:"\<not> (\<exists>m. obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m} \<or> 
                         obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {})"
    by blast
  have "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  proof(rule ccontr)
    assume "\<not> sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    hence "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    with `valid_edge a`
    have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}"
      by(fastforce intro!:n_in_obs_intra)
    with more_than_one show False by simp
  qed
  with `valid_edge a` `intra_kind (kind a)`
  have "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<subseteq> 
        obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by(rule edge_obs_intra_subset)
  with `obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx}` 
  have "nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
  with more_than_one obtain m 
    where "m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "nx \<noteq> m" by auto
  from `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` have "valid_node m" 
    by(fastforce dest:in_obs_intra_valid)
  from `obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx}` have "valid_node nx"
    by(fastforce dest:in_obs_intra_valid)
  show False
  proof(cases "m postdominates (sourcenode a)")
    case True
    with `nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have "m postdominates nx"
      by(fastforce intro:postdominate_inner_path_targetnode elim:obs_intraE)
    with `nx \<noteq> m` have "\<not> nx postdominates m" by(fastforce dest:postdominate_antisym)
    with `valid_node nx` `valid_node m` obtain asx pex where "m -asx\<rightarrow>\<^sub>\<iota>* pex"
      and "method_exit pex" and "nx \<notin> set(sourcenodes asx)"
      by(fastforce simp:postdominate_def)
    have "\<not> nx postdominates (sourcenode a)"
    proof
      assume "nx postdominates sourcenode a"
      from `nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      obtain asx' where "sourcenode a -asx'\<rightarrow>\<^sub>\<iota>* m" and "nx \<notin> set(sourcenodes asx')"
        by(fastforce elim:obs_intraE)
      with `m -asx\<rightarrow>\<^sub>\<iota>* pex` have "sourcenode a -asx'@asx\<rightarrow>\<^sub>\<iota>* pex"
        by(fastforce intro:path_Append simp:intra_path_def)
      with `nx \<notin> set(sourcenodes asx)` `nx \<notin> set(sourcenodes asx')` 
        `nx postdominates sourcenode a` `method_exit pex` show False
        by(fastforce simp:sourcenodes_def postdominate_def)
    qed
    show False
    proof(cases "method_exit nx")
      case True
      from `m postdominates nx` obtain xs where "nx -xs\<rightarrow>\<^sub>\<iota>* m"
        by -(erule postdominate_implies_inner_path)
      with True have "nx = m"
        by(fastforce dest!:method_exit_inner_path simp:intra_path_def)
      with `nx \<noteq> m` show False by simp
    next
      case False
      with `nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have "nx postdominates sourcenode a" by(rule obs_intra_postdominate)
      with `\<not> nx postdominates (sourcenode a)` show False by simp
    qed
  next
    case False
    show False
    proof(cases "method_exit m")
      case True
      from `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      obtain xs where "sourcenode a -xs\<rightarrow>\<^sub>\<iota>* m" and "nx \<notin> set(sourcenodes xs)"
        by(fastforce elim:obs_intraE)
      obtain x' xs' where [simp]:"xs = x'#xs'"
      proof(cases xs)
        case Nil
        with `sourcenode a -xs\<rightarrow>\<^sub>\<iota>* m` have [simp]:"sourcenode a = m"
          by(fastforce simp:intra_path_def)
        with `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` 
        have "m \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(metis obs_intraE)
        with `valid_node m` have "obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m}"
          by(rule n_in_obs_intra)
        with `nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `nx \<noteq> m` have False
          by fastforce
        thus ?thesis by simp
      qed blast
      from `sourcenode a -xs\<rightarrow>\<^sub>\<iota>* m` have "sourcenode a = sourcenode x'" 
        and "valid_edge x'" and "targetnode x' -xs'\<rightarrow>\<^sub>\<iota>* m"
        and "intra_kind (kind x')"
        by(auto elim:path_split_Cons simp:intra_path_def)
      from `targetnode x' -xs'\<rightarrow>\<^sub>\<iota>* m` `nx \<notin> set(sourcenodes xs)` `valid_edge x'` 
        `valid_node m` True
      have "\<not> nx postdominates (targetnode x')" 
        by(fastforce simp:postdominate_def sourcenodes_def)
      show False
      proof(cases "method_exit nx")
        case True
        from `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
          `nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        have "get_proc m = get_proc nx"
          by(fastforce elim:obs_intraE dest:intra_path_get_procs)
        with `method_exit m` `method_exit nx` have "m = nx"
          by(rule method_exit_unique)
        with `nx \<noteq> m` show False by simp
      next 
        case False
        with `obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx}`
        have "nx postdominates (targetnode a)"
          by(fastforce intro:obs_intra_postdominate)
        from `obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx}`
        obtain ys where "targetnode a -ys\<rightarrow>\<^sub>\<iota>* nx" 
          and "\<forall>nx' \<in> set(sourcenodes ys). nx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
          and "nx \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(fastforce elim:obs_intraE)
        hence "nx \<notin> set(sourcenodes ys)"by fastforce
        have "sourcenode a \<noteq> nx"
        proof
          assume "sourcenode a = nx"
          from `nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
          have "nx \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by -(erule obs_intraE)
          with `valid_node nx`
          have "obs_intra nx \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx}" by -(erule n_in_obs_intra)
          with `sourcenode a = nx` `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` 
            `nx \<noteq> m` show False by fastforce
        qed
        with `nx \<notin> set(sourcenodes ys)` have "nx \<notin> set(sourcenodes (a#ys))"
          by(fastforce simp:sourcenodes_def)
        from `valid_edge a` `targetnode a -ys\<rightarrow>\<^sub>\<iota>* nx` `intra_kind (kind a)`
        have "sourcenode a -a#ys\<rightarrow>\<^sub>\<iota>* nx"
          by(fastforce intro:Cons_path simp:intra_path_def)
        from `sourcenode a -a#ys\<rightarrow>\<^sub>\<iota>* nx` `nx \<notin> set(sourcenodes (a#ys))`
          `intra_kind (kind a)` `nx postdominates (targetnode a)`
          `valid_edge x'` `intra_kind (kind x')` `\<not> nx postdominates (targetnode x')`
          `sourcenode a = sourcenode x'`
        have "(sourcenode a) controls nx"
          by(fastforce simp:control_dependence_def)
        hence "CFG_node (sourcenode a) \<longrightarrow>\<^bsub>cd\<^esub> CFG_node nx" 
          by(fastforce intro:SDG_cdep_edge)
        with `nx \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` have "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
          by(fastforce elim!:combine_SDG_slices.cases
                       dest:SDG_edge_sum_SDG_edge cdep_slice1 cdep_slice2 
                      intro:combine_SDG_slices.intros
                       simp:HRB_slice_def SDG_to_CFG_set_def)
        with `valid_edge a` 
        have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}"
          by(fastforce intro!:n_in_obs_intra)
        with `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
          `nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `nx \<noteq> m`
        show False by simp
      qed
    next
      case False
      with `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have "m postdominates (sourcenode a)" by(rule obs_intra_postdominate)
      with `\<not> m postdominates (sourcenode a)` show False by simp
    qed
  qed
qed



lemma obs_intra_finite:"valid_node n \<Longrightarrow> finite (obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
by(fastforce dest:obs_intra_singleton_disj[of _ S])

lemma obs_intra_singleton:"valid_node n \<Longrightarrow> card (obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<le> 1"
by(fastforce dest:obs_intra_singleton_disj[of _ S])


lemma obs_intra_singleton_element:
  "m \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<Longrightarrow> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m}"
apply -
apply(frule in_obs_intra_valid)
apply(drule obs_intra_singleton_disj) apply auto
done


lemma obs_intra_the_element: 
  "m \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<Longrightarrow> (THE m. m \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) = m"
by(fastforce dest:obs_intra_singleton_element)


lemma obs_singleton_element:
  assumes "ms \<in> obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "\<forall>n \<in> set (tl ns). return_node n"
  shows "obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {ms}"
proof -
  from `ms \<in> obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `\<forall>n \<in> set (tl ns). return_node n`
  obtain nsx n nsx' n' where "ns = nsx@n#nsx'" and "ms = n'#nsx'"
    and split:"n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    "\<forall>nx \<in> set nsx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    "\<forall>xs x xs'. nsx = xs@x#xs' \<and> obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}
    \<longrightarrow> (\<exists>x'' \<in> set (xs'@[n]). \<exists>nx. call_of_return_node x'' nx \<and> 
                                   nx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    by(erule obsE)
  from `n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
  have "obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'}"
    by(fastforce intro!:obs_intra_singleton_element)
  { fix xs assume "xs \<noteq> ms" and "xs \<in> obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    from `xs \<in> obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `\<forall>n \<in> set (tl ns). return_node n`
    obtain zs z zs' z' where "ns = zs@z#zs'" and "xs = z'#zs'"
      and "z' \<in> obs_intra z \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      and "\<forall>z' \<in> set zs'. \<exists>nx'. call_of_return_node z' nx' \<and> nx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      and "\<forall>xs x xs'. zs = xs@x#xs' \<and> obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}
      \<longrightarrow> (\<exists>x'' \<in> set (xs'@[z]). \<exists>nx. call_of_return_node x'' nx \<and> 
                                     nx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
      by(erule obsE)
    with `ns = nsx@n#nsx'` split
    have "nsx = zs \<and> n = z \<and> nsx' = zs'"
      by -(rule obs_split_det[of _ _ _ _ _ _ "\<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"],fastforce+)
    with `obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'}` `z' \<in> obs_intra z \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have "z' = n'" by simp
    with `xs \<noteq> ms` `ms = n'#nsx'` `xs = z'#zs'` `nsx = zs \<and> n = z \<and> nsx' = zs'`
    have False by simp }
  with `ms \<in> obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` show ?thesis by fastforce
qed


lemma obs_finite:"\<forall>n \<in> set (tl ns). return_node n 
  \<Longrightarrow> finite (obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
by(cases "obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}",auto dest:obs_singleton_element[of _ _ S])

lemma obs_singleton:"\<forall>n \<in> set (tl ns). return_node n 
  \<Longrightarrow> card (obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<le> 1"
by(cases "obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}",auto dest:obs_singleton_element[of _ _ S])

lemma obs_the_element: 
  "\<lbrakk>ms \<in> obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; \<forall>n \<in> set (tl ns). return_node n\<rbrakk> 
  \<Longrightarrow> (THE ms. ms \<in> obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) = ms"
by(cases "obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}",auto dest:obs_singleton_element[of _ _ S])
  

end

end